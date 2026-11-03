"""Git plumbing against the repository on GitHub (TRUSTED): fetch a commit as data, create a
creation-only tag, and change a branch by optimistic transaction (fetch, apply the mutation to the
fresh state, push without force, retry on a lost race). Nothing is checked out: blobs are read
with `git cat-file`, trees are built in a private index, so no file of an entry ever lands in a
working tree and no hook or filter runs.

The token, if any, goes to git as an HTTP header through `GIT_CONFIG_*` variables (never argv, a
config file or a URL)."""
import base64
import os
import subprocess
import tempfile

BOT_NAME = "github-actions[bot]"
BOT_EMAIL = "41898282+github-actions[bot]@users.noreply.github.com"


class GitError(Exception):
    pass


class Repo:
    """A private bare repository standing for the remote `url` (GitHub, or a path in the tests)."""

    def __init__(self, url, token=None, workdir=None):
        self.url = url
        self.dir = workdir or tempfile.mkdtemp(prefix="rf-git-")
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.env.update({"GIT_TERMINAL_PROMPT": "0", "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                         "GIT_AUTHOR_NAME": BOT_NAME, "GIT_AUTHOR_EMAIL": BOT_EMAIL,
                         "GIT_COMMITTER_NAME": BOT_NAME, "GIT_COMMITTER_EMAIL": BOT_EMAIL})
        cfg = [("core.hooksPath", os.devnull), ("protocol.version", "2"), ("fetch.fsckObjects", "true")]
        if token:
            b64 = base64.b64encode(f"x-access-token:{token}".encode()).decode()
            cfg.append(("http.https://github.com/.extraheader", f"AUTHORIZATION: basic {b64}"))
        self.env["GIT_CONFIG_COUNT"] = str(len(cfg))
        for i, (k, v) in enumerate(cfg):
            self.env[f"GIT_CONFIG_KEY_{i}"], self.env[f"GIT_CONFIG_VALUE_{i}"] = k, v
        if not os.path.exists(os.path.join(self.dir, "HEAD")):
            self.git("init", "-q", "--bare")

    def git(self, *args, input=None, check=True, env=None):
        e = dict(self.env, **(env or {}))
        r = subprocess.run(["git", "-C", self.dir, *args], input=input, capture_output=True, env=e, timeout=600)
        if check and r.returncode:
            raise GitError(f"git {args[0]} failed ({r.returncode}): {r.stderr.decode('utf-8', 'replace')[-800:]}")
        return r

    def out(self, *args, env=None):
        return self.git(*args, env=env).stdout.decode().strip()

    # -- reading -----------------------------------------------------------------------------
    def fetch(self, ref, local=None, depth=1):
        """Fetches `ref` of the remote; returns its commit (None if the ref does not exist)."""
        dst = local or "refs/rf/fetched"
        r = self.git("fetch", "-q", "--no-tags", f"--depth={depth}", self.url, f"+{ref}:{dst}", check=False)
        if r.returncode:
            if b"couldn't find remote ref" in r.stderr or b"not found" in r.stderr.lower():
                return None
            raise GitError(f"git fetch {ref} failed: {r.stderr.decode('utf-8', 'replace')[-800:]}")
        return self.out("rev-parse", f"{dst}^{{commit}}")

    def blob(self, commit, path, cap):
        """The bytes of `path` at `commit` if it is a blob of at most `cap` bytes, else None."""
        r = self.git("cat-file", "-s", f"{commit}:{path}", check=False)
        if r.returncode or int(r.stdout) > cap:
            return None
        if self.out("cat-file", "-t", f"{commit}:{path}") != "blob":
            return None
        return self.git("cat-file", "blob", f"{commit}:{path}").stdout

    def tree_of(self, commit, path):
        """The object id of the tree `path` at `commit`, or None."""
        r = self.git("rev-parse", "--verify", "-q", f"{commit}:{path}", check=False)
        oid = r.stdout.decode().strip() if r.returncode == 0 else None
        return oid if oid and self.out("cat-file", "-t", oid) == "tree" else None

    def ls_tree(self, commit, path):
        """[(mode, type, size or None, path)] of everything under `path` at `commit`, trees included."""
        raw = self.git("ls-tree", "-r", "-t", "-l", "-z", "--full-tree", commit, "--", path).stdout
        out = []
        for rec in raw.split(b"\0"):
            if not rec:
                continue
            meta, name = rec.split(b"\t", 1)
            mode, typ, _oid, size = meta.decode().split()
            out.append((mode, typ, None if size == "-" else int(size), name.decode("utf-8", "surrogateescape")))
        return out

    def remote_ref(self, ref):
        r = self.git("ls-remote", self.url, ref)
        line = r.stdout.decode().split("\n")[0].split()
        return line[0] if line else None

    # -- writing -----------------------------------------------------------------------------
    def create_tag(self, sha, name):
        """Creates the lightweight tag `refs/tags/<name>` at `sha` on the remote, never moving an
        existing one. Returns True if the tag now points at `sha`."""
        self.git("push", "-q", self.url, f"{sha}:refs/tags/{name}", check=False)
        return self.remote_ref(f"refs/tags/{name}") == sha

    def snapshot(self, branch):
        """A read-only view of the remote's `branch` now."""
        return Snapshot(self, self.fetch(f"refs/heads/{branch}", local=f"refs/rf/{branch}"))

    def transact(self, branch, mutate, message, tries=5):
        """Applies `mutate(Snapshot) -> Changes | None` to the fresh head of `branch` and pushes the
        result as one commit, without force; on a lost race fetches again and re-applies (at most
        `tries` times). An absent branch is created as an orphan. Returns the new commit, or None if
        the mutation changed nothing."""
        last = None
        for _ in range(tries):
            head = self.fetch(f"refs/heads/{branch}", local=f"refs/rf/{branch}")
            ch = mutate(Snapshot(self, head))
            if ch is None or ch.empty():
                return None
            commit = self._commit(head, ch, message)
            if commit is None:
                return None
            r = self.git("push", "-q", self.url, f"{commit}:refs/heads/{branch}", check=False)
            if r.returncode == 0:
                return commit
            last = r.stderr.decode("utf-8", "replace")[-800:]
        raise GitError(f"push to {branch} failed {tries} times: {last}")

    def _commit(self, head, ch, message):
        idx = os.path.join(self.dir, "rf-index")
        if os.path.exists(idx):
            os.remove(idx)
        env = {"GIT_INDEX_FILE": idx}
        if head:
            self.git("read-tree", head, env=env)
        for prefix in ch.drop:
            paths = self.git("ls-files", "-z", "--", prefix.rstrip("/") + "/", env=env).stdout.split(b"\0")
            paths = [p for p in paths if p]
            if paths:   # mode 0 in --index-info removes the path (works in a bare repository)
                self.git("update-index", "-z", "--index-info", env=env,
                         input=b"".join(b"0 " + b"0" * 40 + b"\t" + p + b"\0" for p in paths))
        for prefix, tree in ch.trees:
            # every blob of `tree` at `prefix/…` (update-index --index-info: "mode oid\tpath")
            raw = self.git("ls-tree", "-r", "-z", "--full-tree", tree).stdout
            recs = []
            for rec in raw.split(b"\0"):
                if rec:
                    meta, name = rec.split(b"\t", 1)
                    mode, _typ, oid = meta.split()
                    recs.append(mode + b" " + oid + b"\t" + prefix.rstrip("/").encode() + b"/" + name)
            if recs:
                self.git("update-index", "-z", "--index-info", input=b"\0".join(recs) + b"\0", env=env)
        for path, data in ch.blobs.items():
            if data is None:
                self.git("update-index", "-z", "--index-info", env=env, input=b"0 " + b"0" * 40 + b"\t" + path.encode() + b"\0")
                continue
            oid = self.git("hash-object", "-w", "--stdin", input=data).stdout.decode().strip()
            self.git("update-index", "--add", "--cacheinfo", f"100644,{oid},{path}", env=env)
        tree = self.out("write-tree", env=env)
        if head and tree == self.out("rev-parse", f"{head}^{{tree}}"):
            return None
        args = ["commit-tree", tree, "-m", message] + (["-p", head] if head else [])
        return self.git(*args, env=env).stdout.decode().strip()


class Snapshot:
    """A read-only view of one commit of a branch (or of an absent branch: everything is None)."""

    def __init__(self, repo, head):
        self.repo, self.head = repo, head

    def read(self, path, cap=64 << 20):
        return self.repo.blob(self.head, path, cap) if self.head else None


class Changes:
    """What a transaction writes: blobs (None deletes), whole directories dropped, and subtrees
    grafted at a prefix (an existing tree object, e.g. an entry's root at its retained commit)."""

    def __init__(self):
        self.blobs, self.drop, self.trees = {}, [], []

    def put(self, path, data):
        self.blobs[path] = data if isinstance(data, bytes) or data is None else data.encode()

    def drop_dir(self, prefix):
        self.drop.append(prefix)

    def graft(self, prefix, tree):
        self.trees.append((prefix, tree))

    def empty(self):
        return not (self.blobs or self.drop or self.trees)
