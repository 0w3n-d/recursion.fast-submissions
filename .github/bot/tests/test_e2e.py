"""intake → select → publish against a bare repository standing for GitHub (simulate.World)."""
import hashlib
import json
import os
import unittest

import tests  # noqa: F401  (puts the bot on sys.path)
import flows
import gitdata
from simulate import PIN, World, git, good_root, make_result

INC = lambda S: {"verdict": "ACCEPT", "comparable": True, "score": {"S": S}, "entry_failed": False}  # noqa: E731


class E2E(unittest.TestCase):
    def setUp(self):
        self.w = World()
        self.g = self.w.gh

    def tearDown(self):
        self.w.cleanup()

    def intake(self, n):
        return flows.intake(self.w.ctx(), n)

    def status(self, eid):
        return next(e for e in self.w.state()["submissions"] if e["id"] == eid)

    def test_record_progression_and_main(self):
        self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.g.open_pr(2, "bob", good_root("beta", "2"))
        self.g.open_pr(3, "carol", good_root("gamma", "3"))
        for n in (1, 2, 3):
            self.assertEqual(self.intake(n), "queued")
        # the retention tags exist at the heads
        for n in (1, 2, 3):
            sha = self.g.prs[n]["head"]["sha"]
            self.assertEqual(git(self.w.bare, "rev-parse", f"refs/tags/rf-source/pr{n}-{sha[:12]}"), sha)
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=10.0, prover="1" * 64))
        self.assertEqual((e["pr"], p["status"], p["record_of"]), (1, "record", None))
        self.assertNotIn("incumbent", e)
        rec = json.loads(self.w.show("main:records.json"))
        self.assertEqual(rec["record"]["id"], p["id"])
        self.assertEqual(git(self.w.bare, "rev-parse", "main:submissions/alpha"), p["tree"])
        # the duel: bob 2 % better than the incumbent in the same job is not a record
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.8, prover="2" * 64, incumbent=INC(10.0)))
        self.assertEqual(e["incumbent"]["id"], rec["record"]["id"])
        self.assertEqual(p["status"], "accepted")
        # carol 5 % better is
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=9.5, prover="3" * 64, incumbent=INC(10.0)))
        self.assertEqual((p["status"], p["record_of"]), ("record", rec["record"]["id"]))
        rec2 = json.loads(self.w.show("main:records.json"))
        self.assertEqual(([rec2["record"]["pr"]] + [h["pr"] for h in rec2["history"]], rec2["margin"]), ([3, 1], 0.03))
        tree = git(self.w.bare, "ls-tree", "--name-only", "main", "submissions/").split()
        self.assertEqual(tree, ["submissions/README.md", "submissions/example", "submissions/gamma"])
        self.assertEqual(self.w.show("main:README.md"), b"# recursion.fast submissions\n")
        # data: results, notes, notes.md
        self.assertIsNotNone(self.w.show(f"data:results/{p['id']}.json"))
        self.assertTrue(self.w.show(f"data:notes/{p['id']}.md").startswith(b"# gamma"))
        md = self.w.show("data:notes.md").decode()
        self.assertLess(md.index("pr3-"), md.index("pr1-"))
        st = self.w.state()
        self.assertEqual(st["margin"], 0.03)
        self.assertEqual(self.status(p["id"])["builds_on"], [1, 2])
        self.assertEqual(self.status(p["id"])["agent"], "Opus 5.5")
        self.assertIsNone(self.w.evaluate(lambda e, run: None)[0])       # the queue is empty
        self.assertTrue(all(c[1].count("`") % 2 == 0 for c in self.g.comments))

    def test_invalid_organiser_draft_hold_closed(self):
        self.g.open_pr(1, "mallory", {**good_root("alpha"), "records.json": b"{}"})
        self.assertEqual(self.intake(1), "invalid")
        self.assertIn("outside", self.g.comments[-1][1])
        self.g.perms["owner"] = "admin"
        self.g.open_pr(2, "owner", {"README.md": b"new guidance\n"})
        self.assertEqual(self.intake(2), "organiser")
        self.assertEqual(len(self.g.comments), 1)
        self.g.open_pr(3, "dave", good_root("delta"), draft=True)
        self.assertEqual(self.intake(3), "draft")
        self.g.prs[3]["draft"] = False
        self.assertEqual(self.intake(3), "queued")
        self.g.prs[3]["labels"] = [{"name": "hold"}]
        self.assertEqual(self.intake(3), "held")
        self.assertEqual(self.w.state()["submissions"][-1]["status"], "withdrawn")
        self.g.prs[3]["labels"] = []
        self.assertEqual(self.intake(3), "queued")
        self.g.prs[3]["state"] = "closed"
        self.assertEqual(self.intake(3), "withdrawn")
        self.g.open_pr(4, "erin", good_root("eps"), base="data")
        self.assertEqual(self.intake(4), "ignored")
        self.g.open_pr(5, "frank", {**good_root("zeta"), "submissions/zeta/lean/l": b"/etc"},
                       modes={"submissions/zeta/lean/l": "120000"})
        self.assertEqual(self.intake(5), "invalid")
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])

    def test_push_supersedes_and_copy_refused(self):
        a1 = self.g.open_pr(1, "alice", good_root("alpha", "1"))
        self.intake(1)
        a2 = self.g.push(1, {"submissions/alpha/lean/Solution.lean": b"-- better\n"})
        self.intake(1)
        st = {e["sha"]: e["status"] for e in self.w.state()["submissions"]}
        self.assertEqual((st[a1], st[a2]), ("superseded", "queued"))
        self.g.open_pr(2, "mallory", {**good_root("alpha", "1"), "submissions/alpha/lean/Solution.lean": b"-- better\n"})
        self.assertEqual(self.intake(2), "invalid")
        self.assertIn("another author", self.w.state()["submissions"][-1]["reasons"][0])
        # an empty commit re-rolling an evaluated root is refused
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=5.0))
        self.g.push(1, {})
        self.assertEqual(self.intake(1), "invalid")
        # the PR moves during evaluation: select supersedes stale queued heads without the intake
        self.g.open_pr(3, "carol", good_root("gamma"))
        self.intake(3)
        self.g.push(3, {"submissions/gamma/NOTES.md": b"v2 notes\n"})
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])
        self.assertEqual(self.w.state()["submissions"][-1]["status"], "superseded")

    def test_fair_queue(self):
        for n in (1, 2, 3):
            self.g.open_pr(n, "spammer", good_root(f"s{n}", str(n)))
            self.intake(n)
        self.g.open_pr(4, "bob", good_root("bob", "b"))
        self.intake(4)
        order = []
        for _ in range(4):
            e, _p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"))
            order.append(e["pr"])
        self.assertEqual(order, [1, 4, 2, 3])

    def test_error_requeue_reap_and_replay(self):
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.intake(1)
        e, p = self.w.evaluate(lambda e, run: None)                    # no result artifact
        self.assertEqual((p["status"], p["verdict"]), ("queued", "ERROR"))
        e, p = self.w.evaluate(lambda e, run: make_result(run, "ERROR"))
        self.assertEqual(p["status"], "error")
        self.assertIsNone(self.w.evaluate(lambda e, run: make_result(run))[0])
        # the owner forces it once more
        e, p = self.w.evaluate(lambda e, run: make_result(run, "REJECT"), force=1)
        self.assertEqual(p["status"], "rejected")
        # a run that dies after select: the next select reaps it
        self.g.open_pr(2, "bob", good_root("beta"))
        self.intake(2)
        self.w.run += 1
        dead = flows.select(self.w.ctx(self.w.run))
        e, p = self.w.evaluate(lambda e, run: make_result(run, S=3.0))
        self.assertEqual(e["id"], dead["id"])
        self.assertEqual(e["attempts"], 2)
        self.assertEqual(p["status"], "record")
        # a stale publish of the dead run changes nothing
        self.assertIsNone(flows.publish(self.w.ctx(dead["run_url"].rsplit("/", 1)[1]), dead["id"], None))
        # a genuine ACCEPT of another run, replayed as this run's result: not verified, never a record
        self.g.open_pr(3, "carol", good_root("gamma"))
        self.intake(3)
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, S=0.1, incumbent=INC(3.0)), harness_commit="b" * 40))
        self.assertEqual((p["status"], p["verified"]), ("queued", False))

    def test_record_cache_retry_and_build(self):
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.intake(1)
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, "REJECT"), record_cache={"reused": ["x"]}))
        self.assertEqual(p["status"], "queued")
        e, p = self.w.evaluate(lambda e, run: dict(make_result(run, "REJECT"), record_cache={"reused": ["x"]}))
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
        self.assertIsNotNone(flows.record_build(ctx, {"entry_build": {"manifest_sha256": h}}, d, PIN, "pr1-x"))
        self.assertIsNone(flows.record_build(ctx, {}, d, PIN, "pr1-x"))

    def test_optimistic_retry(self):
        """A concurrent writer pushes to `data` between our fetch and push: the transaction re-applies."""
        self.g.open_pr(1, "alice", good_root("alpha"))
        self.intake(1)
        repo = gitdata.Repo(self.w.bare)
        calls = []

        def mutate(snap):
            calls.append(1)
            if len(calls) == 1:     # someone else wins the race
                other = gitdata.Repo(self.w.bare)
                other.transact("data", lambda s: _put(s, "race.txt", b"x"), "race")
            return _put(snap, "mine.txt", b"y")
        repo.transact("data", mutate, "mine")
        self.assertEqual(len(calls), 2)
        self.assertEqual((self.w.show("data:race.txt"), self.w.show("data:mine.txt")), (b"x", b"y"))
        self.assertIsNotNone(self.w.show("data:submissions.json"))
        # a creation-only tag is never moved
        sha = self.g.prs[1]["head"]["sha"]
        self.assertFalse(repo.create_tag(git(self.w.bare, "rev-parse", "main"), f"rf-source/pr1-{sha[:12]}"))
        self.assertEqual(git(self.w.bare, "rev-parse", f"refs/tags/rf-source/pr1-{sha[:12]}"), sha)


def _put(snap, path, data):
    ch = gitdata.Changes()
    ch.put(path, data)
    return ch


if __name__ == "__main__":
    unittest.main()
