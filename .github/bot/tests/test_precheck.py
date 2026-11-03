import os
import shutil
import tempfile
import unittest
from unittest import mock

import tests  # noqa: F401  (puts the bot on sys.path)
import common
import precheck
from gitdata import Repo
from simulate import commit_tree, git, good_root


class Tree(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.mkdtemp()
        self.bare = os.path.join(self.d, "g.git")
        os.makedirs(self.bare)
        git(self.bare, "init", "-q", "--bare")
        self.repo = Repo(self.bare, workdir=self.bare)

    def tearDown(self):
        shutil.rmtree(self.d)

    def check(self, files, root="alpha", modes=None):
        sha = commit_tree(self.bare, None, files, "t", modes)
        return precheck.tree_rule(self.repo, sha, root)

    def test_valid(self):
        reasons, info = self.check(good_root("alpha"))
        self.assertEqual(reasons, [])
        self.assertTrue(info["notes"].startswith(b"# alpha"))
        self.assertEqual(info["readme"], b"# alpha\n")
        self.assertRegex(info["tree"], r"^[0-9a-f]{40}$")

    def test_missing_files(self):
        f = good_root("alpha")
        for k in ("claim.json", "lean/Solution.lean", "prover/prover.s", "NOTES.md"):
            g = dict(f)
            del g[f"submissions/alpha/{k}"]
            reasons, _ = self.check(g)
            self.assertTrue(reasons, k)
        reasons, _ = self.check({**{k: v for k, v in f.items() if not k.endswith("prover.s")},
                                 "submissions/alpha/prover/sub/x.s": b"x", "submissions/alpha/prover/x.S": b"x"})
        self.assertIn("prover/ holds no .s file", reasons)
        reasons, _ = self.check(f, root="beta")
        self.assertIn("does not exist", reasons[0])

    def test_claim_and_notes_content(self):
        f = good_root("alpha")
        for bad in (b"[1, 2]", b"{not json", b"\xff\xfe", b"[" * 60000):
            reasons, _ = self.check({**f, "submissions/alpha/claim.json": bad})
            self.assertIn("claim.json is not a JSON object", reasons)
        reasons, _ = self.check({**f, "submissions/alpha/claim.json": b" " * 70000})
        self.assertTrue(any("claim_bytes" in r for r in reasons))
        reasons, _ = self.check({**f, "submissions/alpha/NOTES.md": b"x" * (common.MAX_TEXT_BYTES + 1)})
        self.assertTrue(any("NOTES.md has" in r for r in reasons))
        reasons, _ = self.check({**f, "submissions/alpha/NOTES.md": b"  \n"})
        self.assertIn("NOTES.md is empty", reasons)
        reasons, _ = self.check({**f, "submissions/alpha/NOTES.md": b"\xff bad"})
        self.assertIn("NOTES.md is not UTF-8", reasons)
        reasons, info = self.check({**f, "submissions/alpha/README.md": b"y" * (common.MAX_TEXT_BYTES + 1)})
        self.assertEqual(reasons, [])
        self.assertIsNone(info["readme"])

    def test_modes_and_names(self):
        f = good_root("alpha")
        reasons, _ = self.check({**f, "submissions/alpha/lean/link": b"/etc/passwd"}, modes={"submissions/alpha/lean/link": "120000"})
        self.assertTrue(any("symbolic link" in r for r in reasons))
        reasons, _ = self.check({**f, "submissions/alpha/dep": b"c0dec0dec0dec0dec0dec0dec0dec0dec0dec0de"},
                                modes={"submissions/alpha/dep": "160000"})
        self.assertTrue(any("gitlink" in r for r in reasons))
        for name in (".gitattributes", "a b.txt", "x/.GITmodules", "naïve.md", "a`b"):
            reasons, _ = self.check({**f, f"submissions/alpha/{name}": b"x"})
            self.assertTrue(any("file name" in r for r in reasons), name)
        reasons, _ = self.check({**f, "submissions/alpha/prover/build.sh": b"#!/bin/sh\n"},
                                modes={"submissions/alpha/prover/build.sh": "100755"})
        self.assertEqual(reasons, [])

    def test_caps(self):
        f = good_root("alpha")
        caps = dict(common.ENTRY_CAPS)
        with mock.patch.dict(precheck.ENTRY_CAPS, files=5):
            reasons, _ = self.check({**f, "submissions/alpha/extra.txt": b"x"})
            self.assertTrue(any("6 files, above the cap files" in r for r in reasons))
        with mock.patch.dict(precheck.ENTRY_CAPS, file_bytes=10, bytes=50):
            reasons, _ = self.check(f)
            self.assertTrue(any("file_bytes = 10" in r for r in reasons))
            self.assertTrue(any("cap bytes = 50" in r for r in reasons))
        with mock.patch.dict(precheck.ENTRY_CAPS, lean_files=1, lean_bytes=5, prover_files=1, prover_bytes=5, claim_bytes=10):
            reasons, _ = self.check({**f, "submissions/alpha/lean/deep/X.lean": b"x", "submissions/alpha/prover/b.s": b"y"})
            for k in ("lean_files", "lean_bytes", "prover_files", "prover_bytes", "claim_bytes"):
                self.assertTrue(any(f"cap {k} =" in r for r in reasons), k)
        self.assertEqual(precheck.ENTRY_CAPS, caps)
        # the season's values (core harness/season.toml [entry])
        self.assertEqual(caps, {"files": 2048, "bytes": 536870912, "file_bytes": 134217728, "lean_files": 1024,
                                "lean_bytes": 33554432, "prover_files": 256, "prover_bytes": 268435456,
                                "claim_bytes": 65536})


class Paths(unittest.TestCase):
    def test_rules(self):
        F = lambda *names: [{"filename": n} for n in names]  # noqa: E731
        self.assertEqual(precheck.paths_rule(F("submissions/a/x", "submissions/a/lean/y")), ("a", [], False))
        root, reasons, outside = precheck.paths_rule(F("submissions/a/x", ".github/workflows/intake.yml"))
        self.assertTrue(outside and reasons)
        root, reasons, outside = precheck.paths_rule(F("submissions/a/x", "submissions/b/x"))
        self.assertIsNone(root)
        self.assertIn("2 roots", reasons[0])
        root, reasons, outside = precheck.paths_rule([{"filename": "submissions/a/x", "previous_filename": "records.json"}])
        self.assertTrue(outside)
        for bad in ("A", "1x", "a" * 41, "a_b", ".git"):
            root, reasons, _ = precheck.paths_rule(F(f"submissions/{bad}/x"))
            self.assertIsNone(root, bad)
        self.assertTrue(precheck.paths_rule(F("submissions/README.md"))[2])
        self.assertEqual(precheck.paths_rule(None)[1][0], "the pull request changes more than 3000 files")
        self.assertTrue(precheck.paths_rule([])[1])

    def test_notes_header(self):
        notes = b"# X\n\n**Agent:** Claude `Opus` @x <b>\n- Builds on: #12, #4 and #12, #7 (#99999999)\nBuilds on: #1\n"
        agent, builds = precheck.notes_header(notes, own_pr=7)
        self.assertEqual(builds, [12, 4])
        self.assertTrue(agent.startswith("Claude"))
        self.assertEqual(precheck.notes_header(b"\n" * 50 + b"Agent: late\n", 1), (None, []))
        self.assertEqual(precheck.notes_header(b"Agent: \x1b[31m\xe2\x80\xaeevil\n", 1)[0], "?[31m?evil")


if __name__ == "__main__":
    unittest.main()
