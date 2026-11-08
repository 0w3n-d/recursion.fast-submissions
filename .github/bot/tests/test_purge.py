"""purge-caches.sh, the pin move's cache purge, with a stub `gh` (no network, no GitHub): it refuses
while an evaluation runs; it deletes, by key, exactly the caches whose key starts with one of the
core's keys for the new pin, `rf-kernels-nanoda-` included (and only lists them with --dry-run),
through the API's key filter with pagination, so that no number of other caches can hide one; it
checks that none remains; it rejects a SHA that is not a full one. And pin-core.sh refuses the
current pin before anything (re-pinning it would purge the live caches).

  python3 -I -m unittest discover -s .github/bot/tests -t .github/bot
"""
import json
import os
import shutil
import subprocess
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(os.path.dirname(HERE), "purge-caches.sh")
NEW = "c0dec0dec0dec0dec0dec0dec0dec0dec0dec0de"   # fictional
OLD = "0123456789abcdef0123456789abcdef01234567"

# the stub: answers `gh run list` and `gh cache list` from files, records every call, and deletes
# a cache from its store on `gh cache delete` (unless STUB_KEEP is set: a delete that did not land)
STUB = r'''#!/usr/bin/env python3
import json, os, sys
d = os.environ["STUB_DIR"]
open(os.path.join(d, "calls"), "a").write(" ".join(sys.argv[1:]) + "\n")
a = sys.argv[1:]
if a[:2] == ["run", "list"]:
    print(open(os.path.join(d, "runs.json")).read())
elif a[0] == "api":
    from urllib.parse import urlparse, parse_qs
    url = a[-1]
    q = parse_qs(urlparse(url).query)
    key = q["key"][0]
    p = os.path.join(d, "caches.json")
    cs = json.load(open(p))
    if "-X" in a and a[a.index("-X") + 1] == "DELETE":    # every cache with exactly this key
        if not os.environ.get("STUB_KEEP"):
            json.dump([c for c in cs if c["key"] != key], open(p, "w"))
    else:                                                   # a prefix filter, in pages of 100
        m = [c for c in cs if c["key"].startswith(key)]
        assert "--paginate" in a, "a listing must paginate"
        for i in range(0, max(len(m), 1), 100):
            print(json.dumps({"total_count": len(m), "actions_caches": m[i:i + 100]}))
else:
    sys.exit("stub gh: unexpected " + " ".join(a))
'''


class Purge(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.mkdtemp()
        bin_ = os.path.join(self.d, "bin")
        os.makedirs(bin_)
        with open(os.path.join(bin_, "gh"), "w") as f:
            f.write(STUB)
        os.chmod(os.path.join(bin_, "gh"), 0o755)
        self.env = {**os.environ, "PATH": bin_ + os.pathsep + os.environ["PATH"], "STUB_DIR": self.d}
        self.caches([{"id": 1, "key": f"rf-org-{NEW}"}, {"id": 2, "key": f"rf-svc-{NEW}"},
                     {"id": 3, "key": f"rf-kernels-lean-{NEW}"}, {"id": 4, "key": f"rf-record-build-{NEW}-r7"},
                     {"id": 5, "key": f"rf-org-{OLD}"}, {"id": 6, "key": "rf-pages-cache"},
                     {"id": 7, "key": f"rf-kernels-nanoda-{NEW}"}, {"id": 8, "key": f"rf-org-{NEW}"},
                     {"id": 9, "key": f"something-else-{NEW}"}])
        self.runs([{"databaseId": 11, "status": "completed"}])

    def tearDown(self):
        shutil.rmtree(self.d, ignore_errors=True)

    def _load(self, name):
        with open(os.path.join(self.d, name)) as f:
            return f.read()

    def _dump(self, name, obj):
        with open(os.path.join(self.d, name), "w") as f:
            json.dump(obj, f)

    def caches(self, cs):
        self._dump("caches.json", cs)

    def runs(self, rs):
        self._dump("runs.json", rs)

    def run_(self, *args, **env):
        p = subprocess.run(["bash", SCRIPT, *args], env={**self.env, **env}, capture_output=True, text=True)
        calls = self._load("calls").splitlines() if os.path.exists(os.path.join(self.d, "calls")) else []
        left = {c["id"] for c in json.loads(self._load("caches.json"))}
        return p, calls, left

    def test_dry_run_lists_and_deletes_nothing(self):
        p, calls, left = self.run_(NEW, "--dry-run")
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(left, set(range(1, 10)))
        self.assertFalse([c for c in calls if "DELETE" in c])
        for k in (f"rf-org-{NEW}", f"rf-svc-{NEW}", f"rf-kernels-lean-{NEW}", f"rf-kernels-nanoda-{NEW}",
                  f"rf-record-build-{NEW}-r7"):
            self.assertIn(f"would delete every cache with the key {k}\n", p.stdout + "\n")
        self.assertNotIn(OLD, p.stdout)

    def test_deletes_exactly_the_new_pins_caches(self):
        p, calls, left = self.run_(NEW)
        self.assertEqual(p.returncode, 0, p.stderr)
        # the core's keys for the new pin are gone (two caches shared one key: both), the old pin's
        # and unrelated keys stay (a key that merely contains the SHA elsewhere is not the core's)
        self.assertEqual(left, {5, 6, 9})
        deleted = sorted(c.split("key=")[1] for c in calls if "DELETE" in c)
        self.assertEqual(deleted, sorted([f"rf-org-{NEW}", f"rf-svc-{NEW}", f"rf-kernels-lean-{NEW}",
                                          f"rf-kernels-nanoda-{NEW}", f"rf-record-build-{NEW}-r7"]))
        self.assertTrue(all("repos/scaraven/recursion.fast-submissions/" in c for c in calls if c.startswith("api")))
        self.assertIn("no cache names", p.stdout)

    def test_no_window_hides_a_key(self):
        # 2,000 other caches and 250 record-build keys of the new pin: all found (pages), all deleted
        cs = [{"id": 1000 + i, "key": f"junk-{i}"} for i in range(2000)]
        cs += [{"id": 5000 + i, "key": f"rf-record-build-{NEW}-x{i}"} for i in range(250)]
        cs += [{"id": 1, "key": f"rf-org-{NEW}"}]
        self.caches(cs)
        p, calls, left = self.run_(NEW)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(len(left), 2000)
        self.assertEqual(len([c for c in calls if "DELETE" in c]), 251)

    def test_refuses_while_an_evaluation_runs(self):
        for status in ("in_progress", "queued", "waiting", "pending", "requested"):
            self.runs([{"databaseId": 12, "status": status}, {"databaseId": 11, "status": "completed"}])
            if os.path.exists(os.path.join(self.d, "calls")):
                os.unlink(os.path.join(self.d, "calls"))
            p, calls, left = self.run_(NEW)
            self.assertEqual(p.returncode, 1, status)
            self.assertIn("an evaluation is running", p.stderr)
            self.assertEqual(left, set(range(1, 10)))
            self.assertFalse([c for c in calls if c.startswith("api")], status)

    def test_a_delete_that_did_not_land_fails(self):
        p, calls, left = self.run_(NEW, STUB_KEEP="1")
        self.assertEqual(p.returncode, 1)
        self.assertIn("remain", p.stderr)

    def test_nothing_to_purge(self):
        self.caches([{"id": 5, "key": f"rf-org-{OLD}"}])
        p, calls, left = self.run_(NEW)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn("no cache names", p.stdout)

    def test_pin_core_refuses_the_current_pin(self):
        # before any network or gh call, and without changing a file
        top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=HERE, capture_output=True, text=True).stdout.strip()
        cur = subprocess.run(["git", "ls-files", "-s", ".contract"], cwd=top, capture_output=True, text=True).stdout.split()
        if not cur:
            self.skipTest("no .contract gitlink in this checkout")
        before = subprocess.run(["git", "status", "--porcelain"], cwd=top, capture_output=True, text=True).stdout
        p = subprocess.run(["bash", os.path.join(os.path.dirname(HERE), "pin-core.sh"), cur[1]], cwd=top,
                           env=self.env, capture_output=True, text=True)
        self.assertEqual(p.returncode, 1, p.stderr)
        self.assertIn("is already the pin", p.stderr)
        self.assertFalse(os.path.exists(os.path.join(self.d, "calls")))
        after = subprocess.run(["git", "status", "--porcelain"], cwd=top, capture_output=True, text=True).stdout
        self.assertEqual(before, after)

    def test_rejects_a_short_or_uppercase_sha(self):
        for bad in (NEW[:12], NEW.upper(), "x" * 40):
            p, calls, left = self.run_(bad)
            self.assertEqual(p.returncode, 2, bad)
            self.assertEqual(calls, [])


if __name__ == "__main__":
    unittest.main()
