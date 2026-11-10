"""intake → sync → select → publish against a bare repository standing for GitHub (simulate.World)."""
import hashlib
import json
import os
import threading
import unittest

import tests  # noqa: F401  (puts the bot on sys.path)
import flows
import gitdata
import render
import common
import rfqueue
from simulate import PIN, World, commit_tree, git, good_root, make_result


class E2E(unittest.TestCase):
    def setUp(self):
        self.w = World()
        self.g = self.w.gh

    def tearDown(self):
        self.w.cleanup()

    def entry(self, n):
        sha = self.g.prs[n]["head"]["sha"]
        return next(e for e in self.w.state()["submissions"] if e["sha"] == sha)

    def head_status(self, n):
        return self.g.statuses(self.g.prs[n]["head"]["sha"])[0]

    def test_record_progression_and_main(self):
        for n, who in ((1, "alice"), (2, "bob"), (3, "carol")):
            self.g.open_pr(n, who, good_root(f"r{n}", str(n)))
            self.assertEqual(flows.intake(self.w.ctx(), n), "valid")
        self.assertIsNone(self.w.show("data:submissions.json"))          # the intake never writes data
        self.assertEqual([d[0] for d in self.g.dispatches], ["sync.yml"] * 3)
        flows.sync(self.w.ctx())
        for n in (1, 2, 3):
            e = self.entry(n)
            self.assertEqual((e["status"], e["queued"]), ("queued", self.head_status(n)["created_at"]))
            self.assertEqual(git(self.w.bare, "rev-parse", f"refs/tags/{e['tag']}"), e["sha"])
        self.assertEqual(self.g.dispatches[-1][0], "evaluate-next.yml")
        self.assertEqual(flows.sync(self.w.ctx()), 0)                       # idempotent
        man = {"certificate": {"entry_build": {"manifest_sha256": "f" * 64}}}
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, S=10.0, prover="1" * 64), **man))
        self.assertEqual((e["pr"], p["status"], "incumbent" in e, e["record_manifest"]), (1, "record", False, ""))
        rec = json.loads(self.w.show("main:records.json"))["record"]["sum"]
        self.assertEqual(git(self.w.bare, "rev-parse", "main:submissions/r1"), p["tree"])
        # the record rule: S < (1 - MARGIN) * S_record; exactly (1 - MARGIN) * 10 is not a record
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=(1 - common.MARGIN) * 10.0, prover="2" * 64))
        self.assertEqual((p["status"], e["record_manifest"], p["against"]["sum"]["record"]), ("accepted", "f" * 64, rec["id"]))
        self.assertNotIn("incumbent", e)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, prover="3" * 64))
        self.assertEqual((e["pr"], p["status"], p["record_of"]), (3, "record", {"sum": rec["id"], "product": rec["id"]}))
        self.assertAlmostEqual(p["against"]["sum"]["gain"], 0.1)
        self.assertEqual(self.head_status(3)["state"], "success")
        self.assertFalse(any(k in p for k in ("duel", "duels", "duel_with", "cpu")))
        self.assertTrue(any("Against the sum record" in c[1] for c in self.g.comments))
        r2 = json.loads(self.w.show("main:records.json"))
        for t in common.TRACKS:
            self.assertEqual(([r2["record"][t]["pr"]] + [h["pr"] for h in r2["history"][t]], r2["margin"]), ([3, 1], 0.02))
        self.assertEqual(git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split(),
                         ["submissions/README.md", "submissions/example", "submissions/r3"])
        self.assertTrue(self.w.show(f"data:notes/{p['id']}.md").startswith(b"# r3"))
        self.assertIsNotNone(self.w.show(f"data:results/{p['id']}.json"))
        md = self.w.show("data:notes.md").decode()
        self.assertLess(md.index("pr3-"), md.index("pr1-"))
        self.assertEqual(self.entry(3)["builds_on"], [1, 2])
        self.assertTrue(all(c[1].count("`") % 2 == 0 for c in self.g.comments))

    def test_launch_with_no_pull_requests(self):
        self.assertEqual(flows.sync(self.w.ctx()), 0)
        st = json.loads(self.w.show("data:submissions.json"))
        self.assertEqual((st["submissions"], st["core"], st["record"], st["version"]), ([], PIN, {"sum": None, "product": None}, 2))
        self.assertIsNone(flows.select(self.w.ctx()))
        self.assertEqual(self.w.show("main:records.json"), render.records_json(self.w.state(), PIN))
        main0 = git(self.w.bare, "rev-parse", "main")
        self.assertIsNone(flows.select(self.w.ctx()))                     # no churn
        self.assertEqual(git(self.w.bare, "rev-parse", "main"), main0)

    def test_sync_heals_a_missed_intake(self):
        self.g.open_pr(1, "alice", good_root("alpha"))                    # no intake ran at all
        self.g.open_pr(2, "bob", {**good_root("beta"), "records.json": b"{}"})
        flows.sync(self.w.ctx())
        self.assertEqual((self.entry(1)["status"], self.head_status(1)["description"]), ("queued", "queued"))
        e2 = self.entry(2)
        self.assertEqual((e2["status"], e2["tag"]), ("invalid", None))
        self.assertTrue(self.head_status(2)["description"].startswith("invalid"))
        self.assertEqual(len(self.g.comments), 2)
        flows.sync(self.w.ctx())
        self.assertEqual(len(self.g.comments), 2)                          # once

    def test_withdraw_supersede_with_statuses(self):
        self.g.perms["owner"] = "admin"
        self.g.open_pr(1, "owner", {"README.md": b"guidance\n"})
        self.assertEqual(self.w.intake(1), "organiser")
        self.g.open_pr(2, "dave", good_root("delta"), draft=True)
        self.assertEqual(self.w.intake(2), "draft")
        self.assertEqual(json.loads(self.w.show("data:submissions.json"))["submissions"], [])   # created empty
        self.g.prs[2]["draft"] = False
        self.assertEqual(self.w.intake(2), "valid")
        self.g.prs[2]["labels"] = [{"name": "hold"}]
        self.w.intake(2)
        self.assertEqual(self.entry(2)["status"], "withdrawn")
        self.assertEqual(self.head_status(2)["state"], "error")
        self.assertTrue(self.head_status(2)["description"].startswith("withdrawn"))
        self.g.prs[2]["labels"] = []
        self.w.intake(2)
        self.assertEqual((self.entry(2)["status"], self.head_status(2)["description"]), ("queued", "queued"))
        old = self.g.prs[2]["head"]["sha"]
        self.g.push(2, {"submissions/delta/lean/Solution.lean": b"-- v2\n"})
        self.w.intake(2)
        self.assertEqual(self.g.statuses(old)[0]["description"][:10], "superseded")
        self.g.prs[2]["state"] = "closed"
        flows.sync(self.w.ctx())
        self.assertEqual(self.entry(2)["status"], "withdrawn")
        self.g.open_pr(3, "erin", good_root("eps"), base="data")
        self.assertEqual(self.w.intake(3), "ignored")
        self.g.open_pr(4, "frank", {**good_root("zeta"), "submissions/zeta/lean/l": b"/etc"},
                       modes={"submissions/zeta/lean/l": "120000"})
        self.assertEqual(self.w.intake(4), "invalid")
        self.g.open_pr(5, "gina", good_root("example"))                    # a directory the organiser keeps
        self.assertEqual(self.w.intake(5), "invalid")
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])

    def test_copies_and_rerolls_refused(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        self.g.open_pr(2, "mallory", good_root("alpha", "1"))
        self.assertEqual(self.w.intake(2), "invalid")
        self.assertIn("another author", self.entry(2)["reasons"][0])
        self.w.evaluate(lambda e, run: make_result(run, S=5.0))
        self.g.push(1, {})                                                 # an empty commit
        self.assertEqual(self.w.intake(1), "invalid")
        # two intakes raced: both said "queued", sync (the one writer) makes the later one invalid
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        self.g.open_pr(4, "dan", good_root("gamma", "3"))
        self.assertEqual(flows.intake(self.w.ctx(), 3), "valid")
        self.assertEqual(flows.intake(self.w.ctx(), 4), "valid")
        flows.sync(self.w.ctx())
        self.assertEqual((self.entry(3)["status"], self.entry(4)["status"]), ("queued", "invalid"))
        self.assertTrue(self.head_status(4)["description"].startswith("invalid"))
        # the PR moves while queued: select supersedes the stale head
        self.g.push(3, {"submissions/gamma/NOTES.md": b"v2 notes\n"})
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])

    def test_fair_queue_and_compaction(self):
        for n in (1, 2, 3):
            self.g.open_pr(n, "spammer", good_root(f"s{n}", str(n)))
            self.w.intake(n)
        self.g.open_pr(4, "bob", good_root("bob", "b"))
        self.w.intake(4)
        for k in range(60):                                                # a flood of pushes on one PR
            self.g.push(1, {"submissions/s1/NOTES.md": f"v{k}\n".encode()})
            flows.intake(self.w.ctx(), 1)
        flows.sync(self.w.ctx())
        self.assertLessEqual(sum(1 for e in self.w.state()["submissions"] if e["pr"] == 1), 51)
        order = [self.w.evaluate(lambda e, run: make_result(run, "REJECT"))[0]["pr"] for _ in range(4)]
        self.assertEqual(order, [2, 4, 3, 1])       # the pushed PR went to the back of its author's line

    def test_error_requeue_reap_replay_force(self):
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.w.intake(1)
        e, p = self.w.evaluate(lambda e, run: None)                        # no result artifact
        self.assertEqual((p["status"], p["verdict"], p.get("record_cache")), ("queued", "ERROR", False))
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR"))
        self.assertEqual((e["record_cache"], p["status"]), (False, "error"))
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"), force=1)
        self.assertEqual(p["status"], "rejected")
        self.g.open_pr(2, "bob", good_root("beta"))
        self.w.intake(2)
        self.w.run += 1
        dead = flows.select(self.w.ctx(self.w.run))
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=3.0))
        self.assertEqual((e["id"], e["attempts"], p["status"]), (dead["id"], 2, "record"))
        self.assertIsNone(flows.publish(self.w.ctx(dead["run_url"].rsplit("/", 1)[1]), dead["id"], None))
        self.g.open_pr(3, "carol", good_root("gamma"))
        self.w.intake(3)
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, S=0.1), harness_commit="b" * 40))
        self.assertEqual((p["status"], p["verified"]), ("queued", False))

    def test_retirement_and_pin_move(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.assertEqual(rec["record_in"], ["sum", "product"])
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.w.intake(2)
        # the owner retires the record in the sum: no sum record stands, so #2's ACCEPT takes it
        # whatever its S; the product's record still stands and #2 does not beat it
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=99.0, prover="2" * 64), retire=rec["id"], track="sum")
        self.assertEqual((e["pr"], p["status"], p["record_in"], p["record_of"]["sum"], p["against"]["sum"]),
                         (2, "record", ["sum"], None, None))
        self.assertEqual((p["against"]["product"]["record"], p["against"]["product"]["beats"]), (rec["id"], False))
        r0 = next(x for x in self.w.state()["submissions"] if x["id"] == rec["id"])
        self.assertEqual((r0["status"], list(r0["retired_in"])), ("record", ["sum"]))    # the product's crown kept
        r = json.loads(self.w.show("main:records.json"))
        self.assertEqual((r["record"]["sum"]["id"], r["record"]["product"]["id"]), (p["id"], rec["id"]))
        self.assertEqual(git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split(),
                         ["submissions/README.md", "submissions/alpha", "submissions/beta", "submissions/example"])
        # the owner retires records by hand with nothing queued; a wrong track retires nothing, writes
        # nothing, starts nothing and fails the run (also with an entry waiting)
        self.g.open_pr(4, "dave", good_root("delta", "4"))
        self.w.intake(4)
        before = self.w.show("data:submissions.json")
        for rid, t in ((p["id"], "product"), (rec["id"], "sum"), ("pr99-000000000000", "sum")):
            with self.assertRaisesRegex(RuntimeError, "nothing retired, nothing evaluated"):
                self.w.evaluate(lambda e, run: None, retire=rid, track=t)
        self.assertEqual(self.w.show("data:submissions.json"), before)
        self.assertEqual(self.entry(4)["status"], "queued")
        self.g.prs[4]["state"] = "closed"
        flows.sync(self.w.ctx())
        self.w.evaluate(lambda e, run: None, retire=p["id"], track="sum")
        self.w.evaluate(lambda e, run: None, retire=rec["id"], track="product")
        st = self.w.state()
        self.assertEqual([x["status"] for x in st["submissions"]], ["retired", "retired", "withdrawn"])
        self.assertEqual(json.loads(rfqueue.dump(st))["record"], {"sum": None, "product": None})
        # a pin move after a retirement: nothing is ported automatically; the owner's forced port
        # remains, a candidate in every track
        self.w.pin = "c" * 40
        self.assertIsNone(self.w.evaluate(lambda e, run: None)[0])
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=80.0, harness=self.w.pin, prover="2" * 64), force=2)
        self.assertEqual((e["port_of"], e["port_tracks"], p["status"], p["record_in"]), (self.entry(2)["id"], None, "record",
                                                                                        ["sum", "product"]))
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        self.w.intake(3)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=70.0, harness=self.w.pin, prover="3" * 64))
        self.assertEqual((p["status"], p["record_of"]["sum"]), ("record", self.entry(2)["id"] + "-cccccccc"))

    def test_two_tracks_two_records_two_ports(self):
        """A record in one track only; a pin move ports both tracks' records, each by its own port and
        each a candidate only in its own track, before any other entry; then one entry takes both."""
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, a = self.w.evaluate(lambda e, run: make_result(run, S=10.0, Sx=10.0, prover="1" * 64))
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.w.intake(2)
        _, b = self.w.evaluate(lambda e, run: make_result(run, S=12.0, Sx=6.0, prover="2" * 64))
        self.assertEqual((b["status"], b["record_in"], b["record_of"]), ("record", ["product"], {"sum": None, "product": a["id"]}))
        self.assertEqual(self.head_status(2)["description"], "ACCEPT: new record (product), S = 12.0000 s, S_product = 6.0000 s")
        st = json.loads(self.w.show("data:submissions.json"))
        self.assertEqual(st["record"], {"sum": a["id"], "product": b["id"]})
        self.assertEqual(git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split(),
                         ["submissions/README.md", "submissions/alpha", "submissions/beta", "submissions/example"])
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        self.w.intake(3)
        self.w.pin = "c" * 40
        provers = {1: "1" * 64, 2: "2" * 64}
        # the ports' scores are such that each would beat the other's record: neither may take it
        for want, tracks in ((a, ["sum"]), (b, ["product"])):
            e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.0 if e["pr"] == 2 else 11.0, Sx=5.0 if e["pr"] == 1 else 7.0,
                                                              harness=self.w.pin, prover=provers[e["pr"]]), force=3)
            self.assertEqual((e["port_of"], e["port_tracks"], p["status"], p["record_in"]), (want["id"], tracks, "record", tracks))
        st = json.loads(self.w.show("data:submissions.json"))
        self.assertEqual(st["record"], {"sum": a["id"] + "-cccccccc", "product": b["id"] + "-cccccccc"})
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, Sx=5.0, harness=self.w.pin, prover="3" * 64))
        self.assertEqual((e["pr"], p["status"], p["record_in"]), (3, "record", ["sum", "product"]))
        r = json.loads(self.w.show("main:records.json"))
        self.assertEqual({t: x["id"] for t, x in r["record"].items()}, {"sum": p["id"], "product": p["id"]})
        self.assertEqual([h["id"] for h in r["history"]["product"]], [b["id"] + "-cccccccc", b["id"], a["id"]])
        self.assertEqual(git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split(),
                         ["submissions/README.md", "submissions/example", "submissions/gamma"])

    def test_two_records_sharing_a_root_name(self):
        """Two standing records of different entries with one root name: main holds the newer one's tree."""
        self.g.open_pr(1, "alice", good_root("same", "1"))
        self.w.intake(1)
        _, a = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.g.open_pr(2, "bob", good_root("same", "2"))
        self.w.intake(2)
        _, b = self.w.evaluate(lambda e, run: make_result(run, S=12.0, Sx=6.0, prover="2" * 64))
        self.assertEqual(json.loads(self.w.show("data:submissions.json"))["record"], {"sum": a["id"], "product": b["id"]})
        self.assertEqual(git(self.w.bare, "rev-parse", "main:submissions/same"), b["tree"])

    def test_pin_move_ports_the_record_first(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.g.open_pr(2, "mallory", good_root("beta", "2"))            # queued before the pin moves
        self.w.intake(2)
        self.w.pin = "c" * 40
        # even a forced run of #2 evaluates the record's port first, unpaired
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=11.0, harness=self.w.pin, prover="1" * 64), force=2)
        self.assertEqual((e["id"], e["port_of"], "incumbent" in e, p["status"]), (rec["id"] + "-cccccccc", rec["id"], False, "record"))
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=50.0, harness=self.w.pin, prover="2" * 64))
        self.assertEqual((e["pr"], p["against"]["sum"]["record"], p["status"]), (2, rec["id"] + "-cccccccc", "accepted"))
        # the next pin: the port fails, so no record stands; main says so, and the queue proceeds
        self.w.pin = "d" * 40
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT", harness=self.w.pin))
        self.assertEqual((e["port_of"], p["status"]), (rec["id"] + "-cccccccc", "rejected"))
        r = json.loads(self.w.show("main:records.json"))
        self.assertEqual((r["core"], r["record"]), ("d" * 40, {"sum": None, "product": None}))
        self.assertIn("submissions/alpha", git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split())
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        self.w.intake(3)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=40.0, harness=self.w.pin, prover="3" * 64))
        self.assertEqual((e["pr"], p["status"], "incumbent" in e), (3, "record", False))

    def record_at(self, n=1, author="alice", S=10.0, prover="1" * 64):
        self.g.open_pr(n, author, good_root(f"r{n}", str(n)))
        self.w.intake(n)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=S, harness=self.w.pin, prover=prover))
        self.assertEqual(rec["status"], "record")
        return rec

    def win(self, S=9.0, prover="2" * 64):
        return lambda e, run: make_result(run, S=S, harness=self.w.pin, prover=prover)

    def test_requeued_port_stays_first(self):
        """A port re-queued after an ERROR still runs before the queue and a forced run."""
        rec = self.record_at()
        for n, who in ((2, "bob"), (3, "carol")):
            self.g.open_pr(n, who, good_root(f"r{n}", str(n)))
            self.w.intake(n)
        self.w.pin = "c" * 40
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", harness=self.w.pin))
        self.assertEqual((e["port_of"], p["status"]), (rec["id"], "queued"))
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.2, harness=self.w.pin, prover="1" * 64), force=3)
        self.assertEqual((e["port_of"], p["status"]), (rec["id"], "record"))
        e, p = self.w.evaluate(self.win(S=9.0))                       # then the fair order: #2 first
        self.assertEqual((e["pr"], p["against"]["sum"]["record"], p["status"]), (2, rec["id"] + "-cccccccc", "record"))

    def test_ports_of_ports_keep_the_crown(self):
        rec = self.record_at()
        for k, pin in enumerate(("b" * 40, "c" * 40, "d" * 40)):
            self.w.pin = pin
            e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.0 + k, harness=self.w.pin, prover="1" * 64))
            self.assertEqual((e["sha"], p["status"]), (rec["sha"], "record"), p["reasons"])
        # but another commit with that prover binary never takes it
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=1.0, harness=self.w.pin, prover="1" * 64))
        self.assertEqual(p["status"], "accepted")

    def test_truncated_never_a_record(self):
        """A truncated stream (the entry's own condition) is unranked."""
        rec = self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=1.0, comparable=False, harness=self.w.pin, prover="2" * 64))
        self.assertEqual((p["status"], p["record_of"]), ("unranked", {"sum": None, "product": None}))
        self.assertEqual(json.loads(self.w.show("data:submissions.json"))["record"], {"sum": rec["id"], "product": rec["id"]})

    def test_intake_runs_the_workflow_check(self):
        """The intake (main's code) runs wfcheck on every head touching `.github/`."""
        bad = ("on: pull_request_target\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n"
               "      - run: echo \"${{ github.event.pull_request.title }}\"\n").encode()
        good = b"on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: echo ok\n"
        self.g.perms["owner"] = "admin"
        self.g.open_pr(1, "owner", {".github/workflows/x.yml": bad})                # an organiser's PR
        self.assertEqual(self.w.intake(1), "organiser")
        self.assertEqual(self.head_status(1)["state"], "failure")
        self.assertIn("workflow check failed", self.head_status(1)["description"])
        self.assertTrue(any(n == 1 and "workflow check failed" in body and "github.event.pull_request.title" in body
                            for n, body in self.g.comments))
        self.g.open_pr(2, "owner", {".github/workflows/y.yml": good})
        self.assertEqual(self.w.intake(2), "organiser")
        self.assertEqual(self.g.statuses(self.g.prs[2]["head"]["sha"]), [])        # a clean change: no status
        self.g.open_pr(3, "mallory", {**good_root("m3", "3"), ".github/workflows/z.yml": bad})
        self.assertEqual(self.w.intake(3), "invalid")
        self.assertTrue(any(r.startswith("workflow check:") for r in self.entry(3)["reasons"]))

    def test_unverified_results_are_the_organisers(self):
        """A result whose attestation fails is a named organiser error (it never counts against the
        author: no place lost), two in a row pause the queue (nothing an entry runs reaches the attestation),
        and it never clears a pause."""
        self.g.open_pr(1, "ann", good_root("a1", "1"))
        self.w.intake(1)
        unverified = lambda e, run: make_result(run, S=1.0, harness="b" * 40)   # noqa: E731  (fake: not attested)
        _, p = self.w.evaluate(unverified)
        self.assertEqual((p["status"], p["counted_at"]), ("queued", None))
        _, p = self.w.evaluate(unverified)
        self.assertEqual((p["status"], p["counted_at"], p.get("generic_errors", 0)), ("error", None, 0))
        import rfqueue
        self.assertEqual([x for x in self.w.state()["submissions"] if rfqueue.counted_start(x)], [])
        st = self.w.state()
        self.assertEqual(([x["kind"] for x in st["error_streak"]], bool(st.get("paused"))), (["attestation"] * 2, True))
        self.assertEqual(len(self.g.issues), 1)
        # a pause is not lifted by an unverified result
        self.g.open_pr(2, "bob", good_root("b2", "2"))
        self.w.intake(2)
        self.assertIsNone(self.w.evaluate(unverified)[0])                   # paused: nothing runs
        self.w.evaluate(unverified, force=2)
        self.assertTrue(self.w.state().get("paused"))
        self.assertEqual(len(self.g.issues), 1)
        self.w.evaluate(lambda e, run: make_result(run, S=1.0, prover="2" * 64), force=2)
        self.assertIsNone(self.w.state().get("paused"))

    def test_machine_mismatch_is_an_organiser_error_that_keeps_its_place(self):
        """Another machine's fingerprint is the organiser's ERROR: re-queued in its place
        without using up an attempt, never counted; two in a row pause the queue with one owner
        notice; a forced run with a clean result resumes it."""
        rec = self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        self.g.open_pr(3, "carol", good_root("r3", "3"))
        self.w.intake(3)
        off = lambda e, run: make_result(run, S=1.0, harness=self.w.pin, prover="2" * 64, machine_ok=False)  # noqa: E731
        e, p = self.w.evaluate(off)
        self.assertEqual((e["pr"], p["status"], p["verdict"], p["attempts"]), (2, "queued", "ERROR", 0))
        self.assertTrue(any("machine fingerprint is mismatched" in r for r in p["reasons"]))
        import rfqueue
        st = self.w.state()
        self.assertEqual([x["pr"] for x in rfqueue.order(st)], [2, 3])      # bob's ERROR run does not move him back
        self.assertIsNone(rfqueue.counted_start(self.entry(2)))
        self.assertEqual((len(st["error_streak"]), st.get("paused")), (1, None))
        self.assertEqual(self.head_status(2)["state"], "pending")
        e, p = self.w.evaluate(off)
        self.assertEqual((e["pr"], p["status"], p["attempts"]), (2, "queued", 0))     # still no attempt used
        st = self.w.state()
        self.assertEqual(rfqueue.pause_count(st["error_streak"]), 2)
        self.assertTrue(st["paused"]["reason"].startswith("organiser ERROR: the machine fingerprint"))
        self.assertEqual(len(getattr(self.g, "issues", [])), 1)
        self.assertIn("paused", self.g.issues[0][0])
        n = len(self.g.dispatches)
        self.assertIsNone(self.w.evaluate(off)[0])                          # paused: nothing runs
        self.assertEqual(len(self.g.dispatches), n)
        e, p = self.w.evaluate(off, force=3)                                # the owner's test run, still broken
        self.assertEqual((p["status"], len(self.g.issues)), ("queued", 1))  # no second notice
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=5.0, harness=self.w.pin, prover="2" * 64), force=2)
        self.assertEqual((e["pr"], p["status"], p["record_of"]["sum"]), (2, "record", rec["id"]))
        st = self.w.state()
        self.assertEqual((st["error_streak"], st.get("paused")), ([], None))
        e, _ = self.w.evaluate(lambda e, run: make_result(run, "REJECT", harness=self.w.pin))
        self.assertEqual(e["pr"], 3)                                        # resumed

    def test_lengths_error_pauses_like_a_fingerprint_error(self):
        """A stream that did not use the season's fixed chain lengths is the core's named organiser
        ERROR `lengths`: an organiser bug, the same at every retry at one pin. Like a fingerprint
        error it is re-queued in its place without using up an attempt, never counted for the
        author, and two in a row pause the queue with one owner notice; a clean forced run resumes."""
        self.g.open_pr(1, "ann", good_root("a1", "1"))
        self.w.intake(1)
        self.g.open_pr(2, "bob", good_root("b2", "2"))
        self.w.intake(2)
        bad = lambda e, run: make_result(run, "ERROR", harness=self.w.pin, organiser_error="lengths")  # noqa: E731
        e, p = self.w.evaluate(bad)
        self.assertEqual((e["pr"], p["status"], p["attempts"], p["counted_at"]), (1, "queued", 0, None))
        self.assertTrue(any("the season's chain lengths" in r for r in p["reasons"]))
        import rfqueue
        st = self.w.state()
        self.assertEqual([x["pr"] for x in rfqueue.order(st)], [1, 2])      # ann keeps her place
        self.assertIsNone(rfqueue.counted_start(self.entry(1)))
        self.assertEqual((len(st["error_streak"]), st.get("paused")), (1, None))
        e, p = self.w.evaluate(bad)
        self.assertEqual((e["pr"], p["status"], p["attempts"], p.get("generic_errors", 0)), (1, "queued", 0, 0))
        st = self.w.state()
        self.assertEqual([x["kind"] for x in st["error_streak"]], ["lengths", "lengths"])
        self.assertTrue(st["paused"])
        self.assertEqual(len(getattr(self.g, "issues", [])), 1)
        self.assertIn("paused", self.g.issues[0][0])
        self.assertIn("chain lengths", self.g.issues[0][1])
        n = len(self.g.dispatches)
        self.assertIsNone(self.w.evaluate(bad)[0])                          # paused: nothing runs
        self.assertEqual(len(self.g.dispatches), n)
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT", harness=self.w.pin), force=1)
        self.assertEqual((e["pr"], p["status"]), (1, "rejected"))
        st = self.w.state()
        self.assertEqual((st["error_streak"], st.get("paused")), ([], None))

    def test_named_and_unnamed_errors(self):
        """A named organiser error (setup, cache, drift) never counts against the author and uses the
        retry; an unnamed ERROR is not counted the first time, then counts; after two ERRORs the status says the entry is
        waiting on the organiser (pending, not red). Two entry-proof errors in a row (setup, cache)
        pause the queue."""
        self.g.open_pr(1, "ann", good_root("a1", "1"))
        self.w.intake(1)
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", organiser_error="setup"))
        self.assertEqual((p["status"], p["attempts"], p["counted_at"]), ("queued", 1, None))
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", organiser_error="cache"))
        self.assertEqual((p["status"], p["counted_at"]), ("error", None))
        self.assertEqual(self.head_status(1)["state"], "pending")
        self.assertIn("waiting on the organiser", self.head_status(1)["description"])
        self.assertTrue(self.w.state()["paused"])
        self.assertIn(e["id"], self.g.issues[0][1].split("Left in `error`")[1])
        self.g.open_pr(2, "ann", good_root("a2", "2"))
        self.w.intake(2)
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR"), force=2)   # unnamed: not counted the first time
        self.assertEqual((p["status"], p["counted_at"], p["generic_errors"]), ("queued", None, 1))
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR"), force=2)   # the retry's ERROR counts
        self.assertEqual((p["status"], p["generic_errors"]), ("error", 2))
        self.assertIsNotNone(p["counted_at"])
        self.assertEqual((len(self.w.state()["error_streak"]), len(self.g.issues)), (4, 1))

    def test_mixed_organiser_errors_pause_and_resume(self):
        """Every run that ends on the organiser's side joins the error streak. One author's
        entry, whatever it provokes (drift, harness: kinds an entry might cause), counts once, so no
        author can pause the queue alone; the next author's organiser error (setup) pauses it with
        one notice that lists the runs and the entry left in `error`. A REJECT that never reached
        the benchmark (at the certificate) neither counts nor clears the streak, before or during
        the pause. While paused only forced runs run, an ERROR in one keeps the pause, and a clean
        verdict whose stream ran on the season's machine resumes the queue."""
        for n, who in ((1, "alice"), (2, "bob"), (3, "carol"), (4, "dave"), (5, "erin")):
            self.g.open_pr(n, who, good_root(f"m{n}", str(n)))
            self.w.intake(n)
        err = lambda kind: (lambda e, run: make_result(run, "ERROR", organiser_error=kind))  # noqa: E731
        cert_reject = lambda e, run: make_result(run, "REJECT", stream=False)  # noqa: E731
        e, p = self.w.evaluate(err("drift"), force=1)
        self.assertEqual((e["pr"], p["status"], p["attempts"]), (1, "queued", 1))
        e, p = self.w.evaluate(cert_reject, force=3)                          # interleaved: not a reset
        self.assertEqual((e["pr"], p["status"]), (3, "rejected"))
        self.assertEqual([x["kind"] for x in self.w.state()["error_streak"]], ["drift"])
        e, p = self.w.evaluate(err("harness"), force=1)                       # alice's retry: still one author
        self.assertEqual((e["pr"], p["status"]), (1, "error"))
        st = self.w.state()
        self.assertEqual(([x["kind"] for x in st["error_streak"]], rfqueue.pause_count(st["error_streak"]),
                          st.get("paused")), (["drift", "harness"], 1, None))
        self.assertEqual(getattr(self.g, "issues", []), [])
        alice = e["id"]
        e, p = self.w.evaluate(err("setup"), force=2)                         # bob's run: the second author
        self.assertEqual((e["pr"], p["status"], p["attempts"]), (2, "queued", 1))  # his retry is kept
        st = self.w.state()
        self.assertTrue(st["paused"]["reason"])
        self.assertEqual(len(self.g.issues), 1)
        title, body = self.g.issues[0]
        self.assertEqual(title, render.PAUSE_TITLE)
        for k in ("drift", "harness", "setup"):
            self.assertIn(f"`{k}`", body)
        self.assertIn(alice, body.split("Left in `error`")[1])
        self.assertTrue(all(b.count("`") % 2 == 0 for _, b in self.g.issues))
        n = len(self.g.dispatches)
        self.assertIsNone(self.w.evaluate(err("setup"))[0])                  # paused: nothing runs
        self.assertEqual(len(self.g.dispatches), n)
        e, p = self.w.evaluate(cert_reject, force=4)                          # a forced cert-stage REJECT
        self.assertEqual((e["pr"], p["status"], bool(self.w.state().get("paused")), len(self.w.state()["error_streak"])),
                         (4, "rejected", True, 3))                            # does not resume
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR"), force=5)   # an unnamed ERROR keeps it
        self.assertEqual((e["pr"], p["status"], bool(self.w.state().get("paused")), len(self.g.issues)),
                         (5, "queued", True, 1))
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"), force=2)  # a REJECT after the stream
        self.assertEqual((e["pr"], p["status"]), (2, "rejected"))
        st = self.w.state()
        self.assertEqual((st["error_streak"], st.get("paused")), ([], None))
        self.assertEqual(self.g.dispatches[-1][0], "evaluate-next.yml")    # the queue goes on
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"))
        self.assertEqual(e["pr"], 5)
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run, "REJECT"))[0])
        # the entry left in error is the owner's to force
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"), force=1)
        self.assertEqual((e["id"], p["status"]), (alice, "rejected"))

    def test_an_outage_between_certificate_rejects_still_pauses(self):
        """A benchmark-side outage (an evicted service cache, a drifting machine) interleaved with
        certificate-stage REJECTs: those REJECTs never reach the benchmark, so they do not reset
        the streak, and the outage pauses the queue at the second author's entry. A missing result
        (no result artifact) counts once per author. The owner can also clear a pause by hand
        (`resume`)."""
        for n, who in ((1, "alice"), (2, "bob"), (3, "carol"), (4, "dave")):
            self.g.open_pr(n, who, good_root(f"o{n}", str(n)))
            self.w.intake(n)
        cert_reject = lambda e, run: make_result(run, "REJECT", stream=False)  # noqa: E731
        self.w.evaluate(lambda e, run: None, force=1)                         # no result: alice, once
        self.w.evaluate(cert_reject, force=3)
        self.w.evaluate(lambda e, run: None, force=1)                         # alice again: still one
        st = self.w.state()
        self.assertEqual(([x["kind"] for x in st["error_streak"]], rfqueue.pause_count(st["error_streak"]),
                          st.get("paused")), (["noresult", "noresult"], 1, None))
        self.w.evaluate(cert_reject, force=4)
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", organiser_error="drift"), force=2)
        st = self.w.state()
        self.assertEqual((e["pr"], [x["kind"] for x in st["error_streak"]], bool(st.get("paused"))),
                         (2, ["noresult", "noresult", "drift"], True))
        self.assertIn("`noresult`", self.g.issues[0][1])
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run, "REJECT"))[0])   # paused
        # the owner clears the pause by hand; the queue runs bob's retry unforced
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT", stream=False), resume=True)
        self.assertEqual((e["pr"], p["status"]), (2, "rejected"))
        st = self.w.state()
        self.assertEqual((st["error_streak"], st.get("paused")), ([], None))

    def test_a_reaped_run_joins_the_streak_and_select_pauses(self):
        """A run that died (reaped by the next select) is an organiser-side ERROR of the streak; if
        it completes a pause, `select` pauses the queue, opens the notice and starts nothing."""
        self.g.open_pr(1, "alice", good_root("a1", "1"))
        self.w.intake(1)
        self.g.open_pr(2, "bob", good_root("b2", "2"))
        self.w.intake(2)
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", organiser_error="cache"))
        self.assertEqual((e["pr"], p["status"]), (1, "queued"))
        self.w.run += 1
        dead = flows.select(self.w.ctx(self.w.run))                        # alice's retry dies
        self.assertEqual(dead["pr"], 1)
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run, "REJECT"))[0])   # reaped, then paused
        st = self.w.state()
        self.assertEqual(([x["kind"] for x in st["error_streak"]], bool(st.get("paused"))), (["cache", "reaped"], True))
        self.assertEqual(self.entry(1)["status"], "error")
        self.assertEqual(len(self.g.issues), 1)
        self.assertIn("`reaped`", self.g.issues[0][1])
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"), force=2)
        self.assertEqual((e["pr"], p["status"], self.w.state().get("paused")), (2, "rejected", None))

    def test_one_author_runs_back_to_back_with_no_cap(self):
        """There is no cap on an author's evaluations: with nobody else waiting, one author's entries
        run back to back, as many as there are; another author's entry, once queued, goes before that
        author's next (the fair order caps nothing, it only decides who goes next)."""
        for n in range(1, 7):
            self.g.open_pr(n, "carol", good_root(f"c{n}", str(n)))
            self.w.intake(n)
        for n in range(1, 6):
            e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"))
            self.assertEqual((e["pr"], p["status"]), (n, "rejected"))
        self.g.open_pr(7, "dave", good_root("d7", "7"))
        self.w.intake(7)
        e, _ = self.w.evaluate(lambda e, run: make_result(run, "REJECT"))
        self.assertEqual(e["pr"], 7)
        e, _ = self.w.evaluate(lambda e, run: make_result(run, "REJECT"))
        self.assertEqual(e["pr"], 6)
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run, "REJECT"))[0])

    def test_pin_move_refreshes_data_and_main_at_once(self):
        rec = self.record_at()
        self.w.pin = "c" * 40
        n0 = len(self.g.dispatches)
        flows.sync(self.w.ctx())                                        # run by the push that moves the pin
        st = json.loads(self.w.show("data:submissions.json"))
        main = json.loads(self.w.show("main:records.json"))
        none = {"sum": None, "product": None}
        self.assertEqual((st["core"], st["record"], main["core"], main["record"]), ("c" * 40, none, "c" * 40, none))
        self.assertEqual((main["history"]["sum"][0]["id"], main["history"]["product"][0]["id"]), (rec["id"], rec["id"]))
        self.assertIn(("evaluate-next.yml", "main"), self.g.dispatches[n0:])   # for the port

    # what the launch left on the live branches: an earlier pin, another margin and the removed
    # `record_wins`, with no submission evaluated
    LAUNCH_DATA = (b'{\n "version": 1,\n "updated": "2026-11-03T11:25:21Z",\n "repo": "scaraven/recursion.fast-submissions",\n'
                   b' "core": "df1f3448f9ec181ce1fcae43964fd11301f653bf",\n "margin": 0.03,\n "record_wins": 2,\n'
                   b' "submissions": [],\n "record": null\n}\n')
    LAUNCH_RECORDS = (b'{\n "version": 1,\n "core": "df1f3448f9ec181ce1fcae43964fd11301f653bf",\n "margin": 0.03,\n'
                      b' "record_wins": 2,\n "record": null,\n "history": []\n}\n')

    def seed(self, data, records):
        b = self.w.bare
        git(b, "update-ref", "refs/heads/data", commit_tree(b, None, {"submissions.json": data, "notes.md": b"# notes\n"}, "data"))
        git(b, "update-ref", "refs/heads/main", commit_tree(b, git(b, "rev-parse", "main"), {"records.json": records}, "records"))

    def test_launch_state_is_rewritten_for_the_new_pin_and_margin(self):
        """The state of an earlier launch (another pin and margin, `record_wins`) loads without an
        error and is rewritten by the first sync, on `data` and `main`; nothing else is lost."""
        self.seed(self.LAUNCH_DATA, self.LAUNCH_RECORDS)
        self.assertTrue(self.w.state()["_stale"])
        flows.sync(self.w.ctx())
        st = json.loads(self.w.show("data:submissions.json"))
        self.assertEqual((st["version"], st["core"], st["margin"], st["submissions"], st["record"], "record_wins" in st),
                         (2, PIN, common.MARGIN, [], {"sum": None, "product": None}, False))
        self.assertEqual(self.w.show("main:records.json"), render.records_json(rfqueue.empty("o/r", PIN), PIN))
        self.assertFalse(self.w.state()["_stale"])
        self.assertEqual(flows.sync(self.w.ctx()), 0)                       # then idempotent
        self.assertEqual(json.loads(self.w.show("data:submissions.json"))["updated"], st["updated"])
        rec = self.record_at()                                              # the first ACCEPT is the record
        self.assertEqual(json.loads(self.w.show("main:records.json"))["record"]["sum"]["id"], rec["id"])

    def test_margin_change_alone_rewrites_the_state(self):
        """At the same pin, a stored state with another margin is rewritten (the evaluated entries kept)."""
        rec = self.record_at()
        raw = json.loads(self.w.show("data:submissions.json"))
        raw["margin"] = 0.05
        self.seed(json.dumps(raw).encode(), self.w.show("main:records.json").replace(
            b'"margin": %s' % str(common.MARGIN).encode(), b'"margin": 0.05'))
        self.assertIn(b'"margin": 0.05', self.w.show("main:records.json"))
        flows.sync(self.w.ctx())
        st = json.loads(self.w.show("data:submissions.json"))
        self.assertEqual((st["margin"], st["record"]["sum"], [e["id"] for e in st["submissions"]]), (common.MARGIN, rec["id"], [rec["id"]]))
        self.assertEqual(json.loads(self.w.show("main:records.json"))["margin"], common.MARGIN)

    def test_pushes_while_running(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.w.intake(2)
        self.w.run += 1
        dead = flows.select(self.w.ctx(self.w.run))                   # a run that dies with #2 running
        # the author pushes an empty commit (refused: being evaluated), then a real change (queued)
        self.g.push(2, {})
        self.assertEqual(self.w.intake(2), "invalid")
        self.assertIn("being evaluated", self.entry(2)["reasons"][0])
        self.g.push(2, {"submissions/beta/lean/Solution.lean": b"-- v2\n"})
        self.assertEqual(self.w.intake(2), "valid")
        # the next run reaps the dead one; its commit is no longer the head, so it is superseded
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, prover="4" * 64))
        self.assertEqual((e["pr"], e["id"] != dead["id"], p["status"]), (2, True, "record"))
        old = next(x for x in self.w.state()["submissions"] if x["id"] == dead["id"])
        self.assertEqual(old["status"], "superseded")

    def test_record_cache_retry_and_build(self):
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.w.intake(1)
        used = {"certificate": {"record_cache": {"restored": ["AlphaX"]}}}
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, "REJECT"), **used))
        self.assertEqual(p["status"], "queued")
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, "REJECT"), **used))
        self.assertEqual((e["record_cache"], p["status"]), (False, "rejected"))
        d = os.path.join(self.w.dir, "build")
        os.makedirs(d)
        with open(os.path.join(d, "manifest.json"), "wb") as f:
            f.write(b'{"m": 1}')
        h = hashlib.sha256(b'{"m": 1}').hexdigest()
        self.g.cache_keys = [f"rf-record-build-{PIN}-old", "other"]
        ctx = self.w.ctx()
        self.assertEqual(flows.record_build(ctx, {"certificate": {"entry_build": {"manifest_sha256": h}}}, d, PIN, "pr1-x"),
                         f"rf-record-build-{PIN}-pr1-x")
        self.assertEqual(self.g.cache_keys, ["other"])
        self.assertIsNone(flows.record_build(ctx, {"entry_build": {"manifest_sha256": "0" * 64}}, d, PIN, "pr1-x"))
        self.assertIsNone(flows.record_build(ctx, {}, d, PIN, "pr1-x"))

    def test_unreadable_data_fails_closed(self):
        """An oversized or foreign submissions.json stops every step and changes neither `data` nor
        `main`."""
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        self.w.evaluate(lambda e, run: make_result(run, S=10.0))
        main0 = git(self.w.bare, "rev-parse", "main")
        for bad in (b"x" * ((256 << 20) + 1), b'{"version": 7}'):
            ch = gitdata.Changes()
            ch.put("submissions.json", bad)
            gitdata.Repo(self.w.bare).transact("data", lambda s: ch, "pad")
            data0 = git(self.w.bare, "rev-parse", "data")
            self.g.open_pr(2, "mallory", good_root("beta", "2"))
            for step in (lambda: flows.intake(self.w.ctx(), 2), lambda: flows.sync(self.w.ctx()),
                         lambda: self.w.evaluate(lambda e, run: make_result(run, S=50.0, prover="b" * 64))):
                with self.assertRaises((gitdata.GitError, ValueError)):
                    step()
            self.assertEqual((git(self.w.bare, "rev-parse", "data"), git(self.w.bare, "rev-parse", "main")), (data0, main0))

    def test_contention(self):
        """16 concurrent writers, jittered backoff: none loses."""
        res = {}

        def writer(i):
            ch = gitdata.Changes()
            ch.put(f"w{i}.txt", b"x")
            try:
                # 16 writers is a stress test (production has two: sync and evaluate-next), so allow
                # more tries than the default on a slow 2-CPU runner
                gitdata.Repo(self.w.bare).transact("data", lambda s: ch, f"w{i}", tries=40, base=0.05)
                res[i] = True
            except gitdata.GitError:
                res[i] = False
        ts = [threading.Thread(target=writer, args=(i,)) for i in range(16)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        self.assertEqual(sum(res.values()), 16)
        self.assertEqual(len(git(self.w.bare, "ls-tree", "--name-only", "data").split()), 16)
        # a creation-only tag is never moved
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.w.intake(1)
        e = self.entry(1)
        self.assertFalse(gitdata.Repo(self.w.bare).create_tag(git(self.w.bare, "rev-parse", "main"), e["tag"]))
        self.assertEqual(git(self.w.bare, "rev-parse", f"refs/tags/{e['tag']}"), e["sha"])


if __name__ == "__main__":
    unittest.main()
