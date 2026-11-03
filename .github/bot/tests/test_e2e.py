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
from simulate import PIN, World, duel_of, git, good_root, make_result


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

    def test_record_progression_duel_and_main(self):
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
        rec = json.loads(self.w.show("main:records.json"))["record"]
        self.assertEqual(git(self.w.bare, "rev-parse", "main:submissions/r1"), p["tree"])
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.8, prover="2" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual((e["incumbent"]["id"], p["status"], e["record_manifest"]), (rec["id"], "accepted", "f" * 64))
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.5, prover="3" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual((p["status"], p["record_of"], p["duels"][0]["won"]), ("confirming", None, True))
        self.assertEqual(json.loads(self.w.show("main:records.json"))["record"]["id"], rec["id"])   # not yet
        self.assertEqual(self.head_status(3)["state"], "pending")
        self.g.open_pr(4, "dora", good_root("r4", "4"))                   # queued now, but the confirmation goes first
        self.w.intake(4)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.6, prover="3" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual((e["pr"], e["incumbent"]["id"], p["status"], p["record_of"]), (3, rec["id"], "record", rec["id"]))
        self.assertAlmostEqual(p["duel"]["gain"], 0.04)                  # the smaller of 5 % and 4 %
        self.assertEqual([d["won"] for d in p["duels"]], [True, True])
        self.assertIsNotNone(self.w.show(f"data:{p['duels'][0]['result']}"))
        r2 = json.loads(self.w.show("main:records.json"))
        self.assertEqual(([r2["record"]["pr"]] + [h["pr"] for h in r2["history"]], r2["margin"]), ([3, 1], 0.03))
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
        self.assertEqual((st["submissions"], st["core"], st["record"]), ([], PIN, None))
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
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, S=0.1, incumbent=duel_of(e, 3.0)), harness_commit="b" * 40))
        self.assertEqual((p["status"], p["verified"]), ("queued", False))

    def test_incumbent_failure_retirement_and_pin_move(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.w.intake(2)
        fail = lambda e, run: make_result(run, S=99.0, prover="2" * 64, incumbent=duel_of(e, entry_failed=True))  # noqa: E731
        e, p = self.w.evaluate(fail)
        self.assertEqual((p["status"], p["record_of"]), ("queued", None))   # never a crown
        e, p = self.w.evaluate(fail)
        self.assertEqual(p["status"], "queued")
        st = self.w.state()
        self.assertEqual(next(x for x in st["submissions"] if x["id"] == rec["id"])["status"], "retired")
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=99.0, prover="2" * 64))
        self.assertEqual((p["status"], "incumbent" in e), ("record", False))
        self.assertEqual(json.loads(self.w.show("main:records.json"))["record"]["id"], p["id"])
        # the owner retires a record by hand
        e, p2 = self.w.evaluate(lambda e, run: None, retire=p["id"])
        self.assertIsNone(e)
        self.assertEqual(next(x for x in self.w.state()["submissions"] if x["id"] == p["id"])["status"], "retired")
        # a pin move after a retirement: nothing is ported automatically; the owner's forced port remains
        self.w.pin = "c" * 40
        self.assertIsNone(self.w.evaluate(lambda e, run: None)[0])
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=80.0, harness=self.w.pin, prover="2" * 64), force=2)
        self.assertEqual((e["port_of"], p["status"], "incumbent" in e), (self.entry(2)["id"], "record", False))
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        self.w.intake(3)
        win = lambda e, run: make_result(run, S=70.0, harness=self.w.pin, prover="3" * 64, incumbent=duel_of(e, 80.0))  # noqa: E731
        e, p = self.w.evaluate(win)
        self.assertEqual((e["incumbent"]["tag"], p["status"]), (self.entry(2)["tag"], "confirming"))
        e, p = self.w.evaluate(win)
        self.assertEqual(p["status"], "record")

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
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=50.0, harness=self.w.pin, prover="2" * 64,
                                                          incumbent=duel_of(e, 11.0)))
        self.assertEqual((e["pr"], e["incumbent"]["id"], p["status"]), (2, rec["id"] + "-cccccccc", "accepted"))
        # the next pin: the port fails, so no record stands; main says so, and the queue proceeds
        self.w.pin = "d" * 40
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT", harness=self.w.pin))
        self.assertEqual((e["port_of"], p["status"]), (rec["id"] + "-cccccccc", "rejected"))
        r = json.loads(self.w.show("main:records.json"))
        self.assertEqual((r["core"], r["record"]), ("d" * 40, None))
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

    def win(self, S=9.0, S_inc=10.0, prover="2" * 64):
        return lambda e, run: make_result(run, S=S, harness=self.w.pin, prover=prover, incumbent=duel_of(e, S_inc))

    def test_requeued_port_stays_first(self):
        """A port re-queued after an ERROR still runs before a confirmation and a forced run."""
        rec = self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        _, p = self.w.evaluate(self.win())
        self.assertEqual(p["status"], "confirming")
        self.g.open_pr(3, "carol", good_root("r3", "3"))
        self.w.intake(3)
        self.w.pin = "c" * 40
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR", harness=self.w.pin))
        self.assertEqual((e["port_of"], p["status"]), (rec["id"], "queued"))
        self.assertEqual(self.entry(2)["status"], "queued")          # its win was against the old pin's record
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.2, harness=self.w.pin, prover="1" * 64), force=3)
        self.assertEqual((e["port_of"], p["status"]), (rec["id"], "record"))
        e, p = self.w.evaluate(self.win(S=9.0, S_inc=10.2, prover="3" * 64))     # then the fair order: #3 first
        self.assertEqual((e["pr"], e["incumbent"]["id"], p["status"]), (3, rec["id"] + "-cccccccc", "confirming"))

    def test_ports_of_ports_keep_the_crown(self):
        rec = self.record_at()
        for k, pin in enumerate(("b" * 40, "c" * 40, "d" * 40)):
            self.w.pin = pin
            e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.0 + k, harness=self.w.pin, prover="1" * 64))
            self.assertEqual((e["sha"], p["status"]), (rec["sha"], "record"), p["reasons"])
        # but another commit with that prover binary never takes it
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=1.0, harness=self.w.pin, prover="1" * 64,
                                                          incumbent=duel_of(e, 13.0)))
        self.assertEqual(p["status"], "accepted")

    def test_wins_and_retries_are_per_record(self):
        """A duel the old record failed does not use up the retry against the new one; a retirement
        voids a win, and main and data name the new state at once."""
        a = self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        fail = lambda e, run: make_result(run, S=9.0, harness=self.w.pin, prover="2" * 64,  # noqa: E731
                                          incumbent=duel_of(e, entry_failed=True))
        _, p = self.w.evaluate(fail)
        self.assertEqual(p["status"], "queued")
        # the owner retires A: #2 then runs unpaired
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.0, harness=self.w.pin, prover="2" * 64), retire=a["id"])
        self.assertEqual((e["pr"], "incumbent" in e, p["status"]), (2, False, "record"))
        self.g.open_pr(3, "carol", good_root("r3", "3"))
        self.w.intake(3)
        b = p
        self.g.open_pr(4, "dora", good_root("r4", "4"))
        self.w.intake(4)
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, harness=self.w.pin, prover="3" * 64,
                                                          incumbent=duel_of(e, 10.0)))
        self.assertEqual(p["status"], "confirming")
        # B fails in the confirmation: one retry against B (not used up by A), then B fails again: retired
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, harness=self.w.pin, prover="3" * 64,
                                                          incumbent=duel_of(e, entry_failed=True)))
        self.assertEqual((p["pr"], p["status"]), (3, "confirming"))
        _, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, harness=self.w.pin, prover="3" * 64,
                                                          incumbent=duel_of(e, entry_failed=True)))
        self.assertEqual(p["status"], "accepted")                        # B retired: one win is not a record
        st = self.w.state()
        self.assertEqual((st["record"], next(x for x in st["submissions"] if x["id"] == b["id"])["status"]), (None, "retired"))
        self.assertIsNone(json.loads(self.w.show("main:records.json"))["record"])   # main follows at once

    def test_owner_retirement_voids_a_pending_confirmation(self):
        rec = self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        _, p = self.w.evaluate(self.win())
        self.assertEqual(p["status"], "confirming")
        e, _ = self.w.evaluate(lambda e, run: None, retire=rec["id"])
        self.assertIsNone(e)                                            # nothing left to run
        x = self.entry(2)
        self.assertEqual((x["status"], self.head_status(2)["state"]), ("accepted", "success"))
        self.assertIn("one win is not a record", x["reasons"][-1])

    def test_duel_failures_count_in_a_row(self):
        rec = self.record_at()
        for n in (2, 3):
            self.g.open_pr(n, f"u{n}", good_root(f"r{n}", str(n)))
            self.w.intake(n)
        self.w.evaluate(lambda e, run: make_result(run, S=9.9, harness=self.w.pin, prover="2" * 64,
                                                   incumbent=duel_of(e, entry_failed=True)))
        self.w.evaluate(lambda e, run: make_result(run, S=9.9, harness=self.w.pin, prover="3" * 64,
                                                   incumbent=duel_of(e, 10.0)))       # a completed duel
        self.assertEqual(next(x for x in self.w.state()["submissions"] if x["id"] == rec["id"])["duel_failures"], 0)

    def test_noncomparable_confirmation_retried_once(self):
        self.record_at()
        self.g.open_pr(2, "bob", good_root("r2", "2"))
        self.w.intake(2)
        self.w.evaluate(self.win())
        nc = lambda e, run: make_result(run, S=9.0, comparable=False, harness=self.w.pin, prover="2" * 64)  # noqa: E731
        _, p = self.w.evaluate(nc)
        self.assertEqual(p["status"], "confirming")
        _, p = self.w.evaluate(nc)
        self.assertEqual(p["status"], "unranked")

    def test_pin_move_refreshes_data_and_main_at_once(self):
        rec = self.record_at()
        self.w.pin = "c" * 40
        n0 = len(self.g.dispatches)
        flows.sync(self.w.ctx())                                        # run by the push that moves the pin
        st = json.loads(self.w.show("data:submissions.json"))
        main = json.loads(self.w.show("main:records.json"))
        self.assertEqual((st["core"], st["record"], main["core"], main["record"]), ("c" * 40, None, "c" * 40, None))
        self.assertEqual(main["history"][0]["id"], rec["id"])
        self.assertIn(("evaluate-next.yml", "main"), self.g.dispatches[n0:])   # for the port

    def test_confirmation_lost_and_pushes_meanwhile(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.w.intake(1)
        _, rec = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.w.intake(2)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, prover="2" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual(p["status"], "confirming")
        first = p["id"]
        # the author pushes an empty commit (refused: being evaluated), then a real change (queued
        # behind); neither touches the confirmation, nor does a run that dies
        self.g.push(2, {})
        self.assertEqual(self.w.intake(2), "invalid")
        self.assertIn("being evaluated", self.entry(2)["reasons"][0])
        self.g.push(2, {"submissions/beta/lean/Solution.lean": b"-- v2\n"})
        self.assertEqual(self.w.intake(2), "valid")
        self.w.run += 1
        dead = flows.select(self.w.ctx(self.w.run))
        self.assertEqual(dead["id"], first)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.9, prover="2" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual((e["id"], p["status"], [d["won"] for d in p["duels"]]), (first, "accepted", [True, False]))
        self.assertEqual(json.loads(self.w.show("data:submissions.json"))["record"], rec["id"])
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.0, prover="4" * 64, incumbent=duel_of(e, 10.0)))
        self.assertEqual((e["pr"], e["id"] != first, p["status"]), (2, True, "confirming"))

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
                gitdata.Repo(self.w.bare).transact("data", lambda s: ch, f"w{i}", base=0.05)
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
