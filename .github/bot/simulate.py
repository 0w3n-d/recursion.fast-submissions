#!/usr/bin/env python3
"""A local end-to-end run of the bot (untrusted by nothing: a test tool). A temporary bare git
repository stands for GitHub's (with `main`, `refs/pull/N/head` and the bot's `data` branch and
tags), `FakeGitHub` for the REST API, and fixture result.json files for the core's evaluation.

  python3 -I .github/bot/simulate.py         runs the scenario and prints what the bot did

The tests (`tests/test_e2e.py`) drive the same pieces."""
import json
import os
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flows  # noqa: E402
import rfqueue  # noqa: E402

REPO = "scaraven/recursion.fast-submissions"
PIN = "9eb4ace62922296e9f29dfebb5a6089c184f6086"
GENV = {"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t", "GIT_AUTHOR_DATE": "2026-11-03T00:00:00Z",
        "GIT_COMMITTER_DATE": "2026-11-03T00:00:00Z"}


def git(d, *args, input=None):
    env = dict(os.environ, **GENV)
    r = subprocess.run(["git", "-C", d, *args], input=input, capture_output=True, env=env)
    if r.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.decode()}")
    return r.stdout.decode().strip()


def commit_tree(bare, parent, files, message, modes=None):
    """A commit on `parent` with `files` ({path: bytes | None}) changed; `modes` overrides a path's
    mode (120000, 160000) with its content as the target."""
    idx = os.path.join(bare, "sim-index")
    if os.path.exists(idx):
        os.remove(idx)
    env = dict(os.environ, **GENV, GIT_INDEX_FILE=idx)
    run = lambda *a, input=None: subprocess.run(["git", "-C", bare, *a], input=input, capture_output=True,  # noqa: E731
                                                env=env, check=True).stdout.decode().strip()
    if parent:
        run("read-tree", parent)
    for path, data in files.items():
        mode = (modes or {}).get(path, "100644")
        if data is None:
            run("update-index", "-z", "--index-info", input=b"0 " + b"0" * 40 + b"\t" + path.encode() + b"\0")
        elif mode == "160000":
            run("update-index", "--add", "--cacheinfo", f"160000,{data.decode()},{path}")
        else:
            oid = run("hash-object", "-w", "--stdin", input=data)
            run("update-index", "--add", "--cacheinfo", f"{mode},{oid},{path}")
    tree = run("write-tree")
    return run("commit-tree", tree, "-m", message, *(["-p", parent] if parent else []))


def good_root(name, salt="", notes=None):
    p = f"submissions/{name}/"
    return {p + "claim.json": b'{"error": "1/2", "completeness_error": "0", "qV": 1, "fuel_base": 0, "fuel_per_word": 8}',
            p + "lean/Solution.lean": f"-- solution {salt}\n".encode(),
            p + "prover/prover.s": f"# prover {salt}\n".encode(),
            p + "NOTES.md": (notes if notes is not None else f"# {name}\n\nAgent: Opus 5.5\nBuilds on: #1, #2\n\nidea {salt}\n").encode(),
            p + "README.md": f"# {name}\n".encode()}


class FakeGitHub:
    """The REST calls the bot makes, against the bare repository."""

    def __init__(self, bare):
        self.bare, self.prs, self.perms = bare, {}, {}
        self.comments, self.statuses, self.dispatches = [], [], []

    def main(self):
        return git(self.bare, "rev-parse", "refs/heads/main")

    def open_pr(self, n, author, files, title="entry", draft=False, labels=(), modes=None, base="main"):
        sha = commit_tree(self.bare, self.main(), files, f"PR {n}", modes)
        git(self.bare, "update-ref", f"refs/pull/{n}/head", sha)
        self.prs[n] = {"number": n, "state": "open", "draft": draft, "title": title, "user": {"login": author},
                       "head": {"sha": sha}, "base": {"ref": base}, "labels": [{"name": x} for x in labels],
                       "created_at": "2026-11-03T00:00:00Z", "_base_sha": self.main()}
        return sha

    def push(self, n, files, modes=None):
        p = self.prs[n]
        sha = commit_tree(self.bare, p["head"]["sha"], files, f"PR {n} push", modes)
        git(self.bare, "update-ref", f"refs/pull/{n}/head", sha)
        p["head"]["sha"] = sha
        return sha

    def pr(self, n):
        p = dict(self.prs[n])
        p["changed_files"] = len(self.pr_files(n) or [])
        return json.loads(json.dumps(p))

    def pr_files(self, n, limit=3000):
        p = self.prs[n]
        out = git(self.bare, "diff", "--name-status", "-M", p["_base_sha"], p["head"]["sha"])
        files = []
        for line in out.splitlines():
            parts = line.split("\t")
            if parts[0].startswith("R"):
                files.append({"filename": parts[2], "previous_filename": parts[1], "status": "renamed"})
            else:
                files.append({"filename": parts[1], "status": parts[0]})
        return None if len(files) > limit else files

    def permission(self, login):
        return self.perms.get(login, "read")

    def comment(self, n, body):
        self.comments.append((n, body))

    def set_status(self, sha, state, description, target_url=None):
        self.statuses.append((sha, state, description))

    def dispatch(self, workflow, ref, inputs=None):
        self.dispatches.append((workflow, ref))

    def caches(self, prefix):
        return [{"key": k} for k in getattr(self, "cache_keys", []) if k.startswith(prefix)]

    def delete_cache(self, key):
        self.cache_keys.remove(key)


def make_result(run_id, verdict="ACCEPT", S=1.0, comparable=True, harness=PIN, incumbent=None, prover="a" * 64):
    r = {"schema": "recursion.fast/v4/result-1", "verdict": verdict, "comparable": comparable, "truncated": False,
         "harness_commit": harness, "job": f"{REPO}/actions/runs/{run_id}/attempts/1", "cpu_models": ["AMD EPYC 9V74"],
         "reasons": [] if verdict == "ACCEPT" else ["the entry failed: `boom` @someone"], "prover_sha256": prover}
    if verdict in ("ACCEPT", "PROVISIONAL"):
        r["score"] = {"S": S, "P_bar": S * 0.8, "V_bar": S * 0.2, "M": 96, "c_P": 1.0, "fit": {"a": 1e-6}}
    if incumbent is not None:
        r["incumbent"] = incumbent
    return r


def fake_verify(pin):
    def verify(path, result):
        ok = result.get("harness_commit") == pin and "/actions/runs/" in str(result.get("job"))
        return {"attested": ok, "record_ok": ok and result.get("verdict") == "ACCEPT" and result.get("comparable") is True,
                "reason": "" if ok else "fake: not attested"}
    return verify


class World:
    """A bare 'GitHub' repository with a `main`, a fake API, and a clock."""

    def __init__(self, root=None):
        self.dir = root or tempfile.mkdtemp(prefix="rf-sim-")
        self.bare = os.path.join(self.dir, "github.git")
        os.makedirs(self.bare)
        git(self.bare, "init", "-q", "--bare")
        main = commit_tree(self.bare, None, {"README.md": b"# recursion.fast submissions\n",
                                             "records.json": b'{"version": 1, "records": {}}\n',
                                             "submissions/README.md": b"roots\n", ".contract": PIN.encode(),
                                             "submissions/example/NOTES.md": b"kept\n"},
                           "main", modes={".contract": "160000"})
        git(self.bare, "update-ref", "refs/heads/main", main)
        self.gh = FakeGitHub(self.bare)
        self.t, self.run = 0, 100
        self.logs = []

    def clock(self):
        import datetime
        self.t += 1
        return datetime.datetime(2026, 11, 3, tzinfo=datetime.timezone.utc) + datetime.timedelta(seconds=self.t)

    def ctx(self, run_id=None):
        return flows.Ctx(self.gh, REPO, self.bare, PIN, run_id=run_id or self.run, clock=self.clock,
                         sleep=lambda s: None, verify=fake_verify(PIN), log=self.logs.append)

    def state(self):
        raw = subprocess.run(["git", "-C", self.bare, "show", "data:submissions.json"], capture_output=True).stdout
        return rfqueue.load(raw or None, REPO, PIN)

    def show(self, ref_path):
        r = subprocess.run(["git", "-C", self.bare, "show", ref_path], capture_output=True)
        return r.stdout if r.returncode == 0 else None

    def evaluate(self, result=None, force=None):
        """select → (the core's evaluation, replaced by `result(entry, run_id)`) → publish."""
        self.run += 1
        ctx = self.ctx(self.run)
        e = flows.select(ctx, force)
        if e is None:
            return None, None
        path = None
        if result is not None:
            r = result(e, self.run)
            if r is not None:
                path = os.path.join(self.dir, f"result-{self.run}.json")
                with open(path, "w") as f:
                    json.dump(r, f)
        return e, flows.publish(ctx, e["id"], path)

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)


def main():
    w = World()
    try:
        g = w.gh
        g.open_pr(1, "alice", good_root("alpha", "1"))
        g.open_pr(2, "bob", good_root("beta", "2"))
        g.open_pr(3, "mallory", {**good_root("gamma", "3"), ".github/workflows/x.yml": b"evil"})
        for n in (1, 2, 3):
            print(f"intake #{n}:", flows.intake(w.ctx(), n))
        e, p = w.evaluate(lambda e, run: make_result(run, S=10.0))
        print("evaluated", e["id"], "->", p["status"])
        e, p = w.evaluate(lambda e, run: make_result(run, S=9.5, prover="b" * 64,
                                                     incumbent={"verdict": "ACCEPT", "comparable": True,
                                                                "score": {"S": 10.2}, "entry_failed": False}))
        print("evaluated", e["id"], "->", p["status"], p["reasons"][-1])
        print("main records.json:", json.loads(w.show("main:records.json"))["record"]["id"])
        print("main tree:", git(w.bare, "ls-tree", "--name-only", "main", "submissions/").split())
        print("comments:", len(g.comments), "statuses:", len(g.statuses), "dispatches:", len(g.dispatches))
        print("queue:", [(x["id"], x["status"]) for x in w.state()["submissions"]])
    finally:
        w.cleanup()


if __name__ == "__main__":
    sys.exit(main())
