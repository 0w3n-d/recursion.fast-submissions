import json
import subprocess
import unittest

import tests  # noqa: F401  (puts the bot on sys.path)
import attest
import common
import pin
import render
import rfqueue
from decide import decide

PIN = "9eb4ace62922296e9f29dfebb5a6089c184f6086"
OK = {"attested": True, "record_ok": True, "reason": ""}


def E(i, pr, author, status="queued", queued="2026-01-01T00:00:00Z", started=None, **kw):
    e = {"id": f"pr{pr}-{i:012x}", "pr": pr, "sha": f"{i:040x}", "root": "r", "author": author, "status": status,
         "queued": queued, "started": started, "finished": None, "attempts": 0, "reasons": [], "tree": kw.pop("tree", None)}
    e.update(kw)
    return e


def R(verdict="ACCEPT", S=1.0, comparable=True, harness=PIN, **kw):
    r = {"verdict": verdict, "comparable": comparable, "harness_commit": harness, "truncated": False,
         "score": {"S": S, "P_bar": S, "V_bar": 0.0}, "reasons": ["r1"], "cpu_models": ["X"]}
    r.update(kw)
    return r


class Queue(unittest.TestCase):
    def st(self, *es):
        s = rfqueue.empty("o/r", PIN)
        s["submissions"] = list(es)
        return s

    def test_fair_order(self):
        s = self.st(E(1, 1, "spam", queued="2026-01-01T00:00:01Z"), E(2, 2, "spam", queued="2026-01-01T00:00:02Z"),
                    E(3, 3, "spam", queued="2026-01-01T00:00:03Z"), E(4, 4, "bob", queued="2026-01-01T00:00:09Z"),
                    E(5, 5, "carol", queued="2026-01-01T00:00:05Z"),
                    E(6, 9, "carol", status="rejected", started="2026-01-01T00:00:00Z"),
                    E(7, 8, "spam", status="rejected", started="2025-12-01T00:00:00Z"))
        # bob never evaluated first; then spam (last start 2025-12) before carol (2026-01); then round robin
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [4, 1, 5, 2, 3])

    def test_never_evaluated_first_in_queue_order(self):
        s = self.st(E(1, 1, "b", queued="2026-01-01T00:00:02Z"), E(2, 2, "a", queued="2026-01-01T00:00:03Z"))
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [1, 2])

    def test_supersede_withdraw_requeue(self):
        s = self.st()
        a, ch = rfqueue.enqueue(s, E(1, 7, "x"), "t1")
        self.assertTrue(ch)
        b, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t2")
        self.assertEqual(rfqueue.find(s, a["id"])["status"], "superseded")
        self.assertEqual(b["queued"], "t2")
        self.assertEqual(rfqueue.withdraw(s, 7, "t3", "closed"), [b["id"]])
        c, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t4")
        self.assertTrue(ch)
        self.assertEqual((c["status"], c["queued"]), ("queued", "t4"))
        _, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t5")      # idempotent
        self.assertFalse(ch)
        rfqueue.find(s, c["id"])["status"] = "rejected"
        _, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t6")      # an evaluated commit is never re-queued
        self.assertFalse(ch)
        e, ch = rfqueue.add_invalid(s, E(3, 7, "x"), ["bad"], "t7")
        self.assertEqual(e["status"], "invalid")
        self.assertFalse(rfqueue.add_invalid(s, E(3, 7, "x"), ["bad"], "t8")[1])

    def test_reap_and_attempts(self):
        s = self.st(E(1, 1, "x", status="running", attempts=1), E(2, 2, "y", status="running", attempts=2))
        self.assertEqual(len(rfqueue.reap(s, "t")), 2)
        self.assertEqual([e["status"] for e in s["submissions"]], ["queued", "error"])

    def test_duplicates(self):
        s = self.st(E(1, 1, "alice", tree="T", status="withdrawn"), E(2, 2, "bob", tree="U", status="accepted"),
                    E(3, 3, "bob", tree="V", status="queued"), E(4, 4, "eve", tree="W", status="invalid"),
                    E(5, 5, "bob", tree="X", status="error"))
        self.assertIn("another author", rfqueue.duplicate_of(s, "new", 9, "mallory", "T"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "alice", "T"))
        self.assertIn("already evaluated", rfqueue.duplicate_of(s, "new", 2, "bob", "U"))
        self.assertIn("queued in #3", rfqueue.duplicate_of(s, "new", 9, "bob", "V"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 3, "bob", "V"))     # the same PR: superseded instead
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "mallory", "W"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 5, "bob", "X"))     # an organiser ERROR may be retried

    def test_records_per_pin_and_retirement(self):
        s = self.st(E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN),
                    E(2, 2, "b", status="record", finished="2026-01-02", harness_commit="c" * 40))
        self.assertEqual(rfqueue.current_record(s, PIN)["pr"], 1)
        self.assertEqual(rfqueue.current_record(s, "c" * 40)["pr"], 2)
        self.assertIsNone(rfqueue.current_record(s, "d" * 40))
        rfqueue.retire(s["submissions"][0], "t", "x")
        self.assertIsNone(rfqueue.current_record(s, PIN))          # a beaten record never stands again
        self.assertEqual([e["pr"] for e in rfqueue.records(s)], [2, 1])

    def test_dump_names_the_standing_record(self):
        st = rfqueue.empty("o/r", PIN)
        self.assertIsNone(json.loads(rfqueue.dump(st))["record"])
        st["submissions"] += [E(1, 1, "a", "record", harness_commit=PIN, finished="2026-01-01T00:00:01Z"),
                              E(2, 2, "b", "record", harness_commit="1" * 40, finished="2026-01-01T00:00:02Z")]
        self.assertEqual(json.loads(rfqueue.dump(st))["record"], "pr1-000000000001")   # the other pin's never stands
        st["submissions"][0]["status"] = "retired"
        self.assertIsNone(json.loads(rfqueue.dump(st))["record"])

    def test_port(self):
        s = self.st(E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN, tag="rf-source/x"))
        p = rfqueue.port(s, 1, "c" * 40, "now")
        self.assertEqual((p["id"], p["status"], p["port_of"], p["tag"]), (s["submissions"][0]["id"] + "-cccccccc", "queued",
                                                                         s["submissions"][0]["id"], "rf-source/x"))
        self.assertTrue(common.ID_RE.match(p["id"]))
        self.assertIsNone(rfqueue.port(s, 1, "c" * 40, "now"))     # once
        self.assertIsNone(rfqueue.port(s, 1, PIN, "now"))          # the same pin: nothing to port

    def test_compaction_and_large_state(self):
        """Review M1: a flood of pushes keeps the state bounded; a large state loads and orders fast."""
        es = []
        for k in range(3000):
            es.append(E(k + 1, 7, "spam", status="superseded", queued=f"2026-01-01T00:{k // 60:02d}:{k % 60:02d}Z",
                        notes=f"notes/{k}.md", reasons=["r" * 300] * 20, title="t" * 200))
        es.append(E(99999, 7, "spam", status="queued", queued="2026-01-02T00:00:00Z"))
        s = self.st(*es)
        dropped = rfqueue.compact(s)
        self.assertEqual(len(dropped), 3000)
        self.assertEqual(len(rfqueue.of_pr(s, 7)), common.MAX_HEADS_PER_PR + 1)
        self.assertTrue(all(set(e) <= set(rfqueue.COMPACT_KEYS) for e in s["submissions"] if e["status"] == "superseded"))
        big = self.st(*[E(k + 1, k + 1, f"u{k % 500}", status="rejected" if k % 3 else "queued",
                          started="2026-01-01T00:00:00Z" if k % 3 else None, reasons=["x" * 300] * 5)
                        for k in range(20000)])
        raw = rfqueue.dump(big)
        self.assertGreater(len(raw), 30 << 20)
        import time
        t = time.monotonic()
        st = rfqueue.load(raw, "o/r", PIN)
        self.assertEqual(len(rfqueue.order(st)), 6667)
        self.assertLess(time.monotonic() - t, 20)

    def test_load_rejects_foreign_state(self):
        with self.assertRaises(ValueError):
            rfqueue.load(b'{"version": 2, "submissions": []}', "o/r", PIN)
        with self.assertRaises(ValueError):
            rfqueue.load(b'{"version": 1, "submissions": [{"id": "x", "status": "hacked"}]}', "o/r", PIN)


class Decide(unittest.TestCase):
    rec = {"id": "pr1-aaaaaaaaaaaa", "sha": "a" * 40, "root": "r", "score": {"S": 10.0}}

    def duel(self, S=10.0, **kw):
        d = {"sha": "a" * 40, "path": "submissions/r", "certificate_status": "ok", "verdict": "ACCEPT",
             "comparable": True, "truncated": False, "score": {"S": S}, "entry_failed": False, "reasons": []}
        d.update(kw)
        return {"duel": True, "incumbent": d}

    def test_first_record_and_verdicts(self):
        self.assertEqual(decide(R(), OK, PIN, None, 1)["status"], "record")
        self.assertEqual(decide(R("REJECT"), OK, PIN, None, 1)["status"], "rejected")
        self.assertEqual(decide(R("PROVISIONAL"), OK, PIN, None, 1)["status"], "provisional")
        unranked = dict(OK, record_ok=False)      # verify-record.sh is never asked about a non-comparable ACCEPT
        self.assertEqual(decide(R(comparable=False), unranked, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(comparable=False, truncated=True), unranked, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(S=0.0), OK, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(verdict="WIN"), OK, PIN, None, 2)["verdict"], "ERROR")

    def test_error_requeue_once(self):
        d = decide(R("ERROR"), OK, PIN, None, 1)
        self.assertEqual((d["status"], d["requeue"]), ("queued", True))
        d = decide(R("ERROR"), OK, PIN, None, 2)
        self.assertEqual((d["status"], d["requeue"]), ("error", False))
        self.assertEqual(decide(None, {"attested": False}, PIN, None, 2)["status"], "error")

    def test_provenance(self):
        bad = {"attested": False, "record_ok": False, "reason": "nope"}
        self.assertEqual(decide(R(), bad, PIN, None, 1)["status"], "queued")
        self.assertEqual(decide(R(), dict(OK, record_ok=False), PIN, None, 2)["status"], "error")
        self.assertEqual(decide(R(harness="b" * 40), OK, PIN, None, 2)["status"], "error")
        for v in ("REJECT", "PROVISIONAL"):       # review m11: an unattested result is never published as such
            d = decide(R(v), bad, PIN, None, 1)
            self.assertEqual((d["status"], d["verified"]), ("queued", False))
            self.assertTrue(any("not verified" in r for r in d["reasons"]))

    def test_duel(self):
        d = decide(R(S=9.7, **self.duel(10.0)), OK, PIN, self.rec, 1)
        self.assertEqual((d["status"], d["record_of"]), ("record", self.rec["id"]))     # exactly 0.97: a record
        self.assertAlmostEqual(d["duel"]["gain"], 0.03)
        self.assertEqual(decide(R(S=9.71, **self.duel(10.0)), OK, PIN, self.rec, 1)["status"], "accepted")
        # only the same-job measurement counts, not the record's stored S
        self.assertEqual(decide(R(S=5.0, **self.duel(5.1)), OK, PIN, self.rec, 1)["status"], "accepted")
        # organiser side: no duel, another incumbent, its certificate not ok, no comparable score
        for res in (R(S=1.0), R(S=1.0, **self.duel(sha="b" * 40)), R(S=1.0, **self.duel(path="submissions/x")),
                    R(S=1.0, **self.duel(certificate_status="error", verdict=None, score=None)),
                    R(S=1.0, **self.duel(verdict="ERROR", score=None))):
            d = decide(res, OK, PIN, self.rec, 1)
            self.assertEqual((d["status"], d["requeue"]), ("queued", True), res.get("incumbent"))
        d = decide(R(S=1.0, prover_sha256="p" * 64, **self.duel(10.0)), OK, PIN, self.rec, 1, {"p" * 64: "pr0-000000000000"})
        self.assertEqual(d["status"], "accepted")

    def test_incumbent_failed_never_crowns(self):
        """Review M4: the record failing on the duel's runner gives no crown; a retry; two failures retire it."""
        failed = self.duel(None, verdict="ACCEPT", truncated=True, comparable=False, entry_failed=True, reasons=["cap"])
        d = decide(R(S=50.0, **failed), OK, PIN, self.rec, 1)
        self.assertEqual((d["status"], d["requeue"], d["duel_retry"], d["record_failed"], d["retire_record"]),
                         ("queued", True, True, True, False))
        self.assertIsNone(d["record_of"])
        self.assertTrue(any("failed on this runner" in r and "cap" in r for r in d["reasons"]))
        d = decide(R(S=50.0, **failed), OK, PIN, self.rec, 1, duel_retries=1)
        self.assertEqual((d["status"], d["requeue"], d["record_failed"]), ("accepted", False, True))
        d = decide(R(S=50.0, **failed), OK, PIN, self.rec, 1, duel_retries=1, record_failures=1)
        self.assertEqual((d["status"], d["requeue"], d["retire_record"]), ("queued", True, True))

    def test_cache_retry(self):
        from decide import cache_retry
        used = {"certificate": {"record_cache": {"restored": ["M"]}}}
        self.assertTrue(cache_retry(dict(R("REJECT"), **used), {}))
        self.assertFalse(cache_retry(dict(R("REJECT"), **used), {"record_cache": False}))
        self.assertFalse(cache_retry(dict(R("ACCEPT"), **used), {}))
        self.assertTrue(cache_retry(dict(R("REJECT"), incumbent=used), {}))
        self.assertFalse(cache_retry(R("REJECT"), {}))

    def test_untrusted_fields_cleaned(self):
        d = decide(R(reasons=["x" * 1000, "\u202eevil\nline"] * 30, cpu_models=["a`b"] * 9,
                     score={"S": 1.0, "deep": {"a": {"b": {"c": {"d": 1}}}}, "s": "\x00" * 500}), OK, PIN, None, 1)
        self.assertLessEqual(len(d["reasons"]), 20)
        self.assertTrue(all(len(r) <= 300 and r.isprintable() for r in d["reasons"]))
        self.assertEqual(len(d["cpu"]), 4)
        self.assertLessEqual(len(d["score"]["s"]), 200)


class Render(unittest.TestCase):
    def test_sanitisers(self):
        self.assertEqual(common.code_span("a`b @me [x](y) <img>"), "`a'b @me [x](y) <img>`")
        self.assertTrue(all(32 <= ord(c) < 127 for c in common.code_span("é\u202e\x07")))
        self.assertEqual(common.clean("a\u202eb\tc", 10), "a?b c")
        self.assertEqual(len(common.clean("x" * 500, 200)), 200)

    def test_status_description(self):
        e = {"status": "rejected", "verdict": "REJECT", "score": None}
        self.assertEqual(render.status_for(e), ("failure", "REJECT: rejected"))
        e = {"status": "record", "verdict": "ACCEPT", "score": {"S": 1.23456}}
        self.assertEqual(render.status_for(e)[0], "success")
        self.assertLessEqual(len(render.status_for({"status": "x" * 500})[1]), 140)

    def test_comment_has_no_live_markdown_from_reasons(self):
        e = {"id": "pr1-aaaaaaaaaaaa", "status": "rejected", "verdict": "REJECT", "reasons": ["`](http://evil) @owner"],
             "cpu": ["`x`"], "verified": True}
        body = render.publish_comment(e, "https://run")
        self.assertIn("- `'](http://evil) @owner`", body)
        self.assertNotIn("``", body)

    def test_notes_md_fence(self):
        st = rfqueue.empty("o/r", PIN)
        st["submissions"] = [E(1, 1, "a", status="accepted", notes="notes/1.md", finished="2026-01-02"),
                             E(2, 2, "b", status="record", notes="notes/2.md", finished="2026-01-03", score={"S": 2.0}),
                             E(3, 3, "c", status="superseded", notes="notes/3.md")]
        body = {"notes/1.md": "~~~~~~\n## pr9-000000000000 · fake · @owner · record\n".encode(), "notes/2.md": b"two",
                "notes/3.md": b"three"}
        md = render.notes_md(st, body.get, "o/r").decode()
        self.assertLess(md.index("pr2-"), md.index("pr1-"))
        self.assertNotIn("three", md)
        self.assertIn("~~~~~~~markdown", md)       # a fence longer than any in the notes
        lines = md.splitlines()
        self.assertEqual(sum(1 for x in lines if x.startswith("## ")), 3)    # the bot's two and the forged one
        # the forged header is inside the fence
        i = lines.index("## pr9-000000000000 · fake · @owner · record")
        self.assertEqual(lines[i - 2], "~~~~~~~markdown")

    def test_records_json(self):
        st = rfqueue.empty("o/r", PIN)
        st["submissions"] = [E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN),
                             E(2, 2, "b", status="record", finished="2026-01-02", harness_commit=PIN),
                             E(3, 3, "c", status="accepted", harness_commit=PIN)]
        r = json.loads(render.records_json(st, PIN))
        self.assertEqual((r["record"]["pr"], [h["pr"] for h in r["history"]], r["margin"], r["core"]), (2, [1], 0.03, PIN))
        self.assertIsNone(json.loads(render.records_json(rfqueue.empty("o/r", PIN), PIN))["record"])
        r = json.loads(render.records_json(st, "c" * 40))       # another pin: no standing record, the history kept
        self.assertEqual((r["record"], [h["pr"] for h in r["history"]]), (None, [2, 1]))


class Pin(unittest.TestCase):
    W = ("jobs:\n  evaluate:\n    uses: scaraven/recursion.fast/.github/workflows/evaluate.yml@{a}\n"
         "    with:\n      core_ref: {b}\n")

    def test_pins(self):
        self.assertEqual(pin.pins_of(self.W.format(a=PIN, b=PIN), PIN), (PIN, []))
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b="c" * 40), PIN)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN), "c" * 40)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a="main", b="main"), "main")[0])
        two = self.W.format(a=PIN, b=PIN) + "  x:\n    uses: scaraven/recursion.fast/.github/workflows/other.yml@main\n"
        self.assertIsNone(pin.pins_of(two, PIN)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN) + "      core_ref: " + PIN + "\n", PIN)[0])

    def test_repository_files(self):
        import os
        top = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        p, problems = pin.read(top)
        self.assertTrue(p, problems)


class Attest(unittest.TestCase):
    repo, rid = "o/r", "77"

    def fake(self, rc=0, digest=PIN, uri="https://github.com/o/r/actions/runs/77/attempts/1", vr_rc=0):
        def run(cmd, **kw):
            if cmd[0] == "gh":
                out = json.dumps([{"verificationResult": {"signature": {"certificate": {
                    "buildSignerDigest": digest, "buildSignerURI": "u", "runInvocationURI": uri}}}}]).encode()
                return subprocess.CompletedProcess(cmd, rc, out, b"err")
            return subprocess.CompletedProcess(cmd, vr_rc, b"verify-record: OK", b"")
        return run

    def res(self, **kw):
        r = {"verdict": "ACCEPT", "comparable": True, "harness_commit": PIN, "job": "o/r/actions/runs/77/attempts/1"}
        r.update(kw)
        return r

    def test_verify(self):
        v = attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake())
        self.assertEqual((v["attested"], v["record_ok"]), (True, True))
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(rc=1))["attested"])
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(digest="b" * 40))["attested"])
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core",
                                       run=self.fake(uri="https://github.com/o/r/actions/runs/76/attempts/1"))["attested"])
        self.assertFalse(attest.verify("p", self.res(job="o/r/actions/runs/76/attempts/1"), self.repo, self.rid, "core",
                                       run=self.fake())["attested"])
        self.assertFalse(attest.verify("p", self.res(harness_commit=None), self.repo, self.rid, "core", run=self.fake())["attested"])
        v = attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(vr_rc=1))
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        v = attest.verify("p", self.res(verdict="REJECT"), self.repo, self.rid, "core", run=self.fake())
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        # S3 (a): a non-comparable ACCEPT is attested and never asked of verify-record.sh
        v = attest.verify("p", self.res(comparable=False), self.repo, self.rid, "core", run=self.fake(vr_rc=1))
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        # review m2: an earlier attempt than the one that selected the entry is refused
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(), min_attempt=2)["attested"])
        v = attest.verify("p", self.res(job="o/r/actions/runs/77/attempts/2"), self.repo, self.rid, "core",
                          run=self.fake(uri="https://github.com/o/r/actions/runs/77/attempts/2"), min_attempt=2)
        self.assertTrue(v["attested"])


if __name__ == "__main__":
    unittest.main()
