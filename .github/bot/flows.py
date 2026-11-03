"""The bot's three steps (TRUSTED): intake, select, publish, and the sync of `main` to the record.
Each reads GitHub through `ctx.gh` and git through `gitdata.Repo(ctx.git_url)`, so the tests and
`simulate.py` drive them against a local bare repository and a fake API.

No step runs entry code or checks an entry out: a pull request is read as git objects and API
JSON. Every write to `data` and `main` is an optimistic transaction (`gitdata.Repo.transact`)."""
import copy
import json
import time

import precheck
import render
import rfqueue
from common import (ID_RE, LOGIN_RE, MAX_TEXT_BYTES, ROOT_RE, SHA_RE, clean, entry_id, now_iso)
from decide import cache_retry, decide
from gitdata import Changes, Repo

DATA, NOTES_MD = "data", "notes.md"
ORGANISER = ("admin", "maintain", "write")


class Ctx:
    """Everything a step needs from its environment."""

    def __init__(self, gh, repo, git_url, pin, token=None, run_id="0", server="https://github.com",
                 default_branch="main", clock=None, sleep=time.sleep, verify=None, log=print):
        self.gh, self.repo, self.git_url, self.pin, self.token = gh, repo, git_url, pin, token
        self.run_id, self.server, self.default_branch = str(run_id), server, default_branch
        self.run_url = f"{server}/{repo}/actions/runs/{self.run_id}"
        self.clock, self.sleep, self.verify, self.log = clock, sleep, verify, log

    def git(self):
        return Repo(self.git_url, self.token)

    def now(self):
        return now_iso(self.clock)


def _state(ctx, snap):
    return rfqueue.load(snap.read("submissions.json"), ctx.repo, ctx.pin)


def _write_state(ctx, ch, snap, st, extra_reads=None):
    """Puts submissions.json and the regenerated notes.md into `ch`."""
    extra = extra_reads or {}
    ch.put("submissions.json", rfqueue.dump(st, ctx.clock))
    ch.put(NOTES_MD, render.notes_md(st, lambda p: extra[p] if p in extra else snap.read(p, MAX_TEXT_BYTES), ctx.repo))


def _labels(pr):
    return {(lab.get("name") or "").lower() for lab in pr.get("labels") or []}


def _withdraw(ctx, pr_n, reason):
    def mutate(snap):
        st = _state(ctx, snap)
        if not rfqueue.withdraw(st, pr_n, ctx.now(), reason):
            return None
        ch = Changes()
        _write_state(ctx, ch, snap, st)
        return ch
    ctx.git().transact(DATA, mutate, f"withdraw #{pr_n}: {reason}")


# ---- intake -------------------------------------------------------------------------------------
def intake(ctx, pr_n):
    """Prechecks the pull request's current head and queues it (or records it invalid, or
    withdraws its queued entry). Returns what it did."""
    pr = ctx.gh.pr(pr_n)
    author = pr["user"]["login"]
    if pr["base"]["ref"] != ctx.default_branch:
        ctx.log(f"intake: #{pr_n} targets {clean(pr['base']['ref'], 60)!r}, not {ctx.default_branch}: ignored")
        return "ignored"
    files = ctx.gh.pr_files(pr_n) if (pr.get("changed_files") or 0) <= 3000 else None
    root, reasons, outside = precheck.paths_rule(files)
    if outside and ctx.gh.permission(author) in ORGANISER:
        ctx.log(f"intake: #{pr_n} is an organiser pull request: ignored")
        _withdraw(ctx, pr_n, "an organiser pull request")
        return "organiser"
    if pr["state"] != "open":
        _withdraw(ctx, pr_n, "the pull request was closed before its evaluation")
        return "withdrawn"
    if pr.get("draft"):
        _withdraw(ctx, pr_n, "the pull request is a draft")
        return "draft"
    if "hold" in _labels(pr):
        _withdraw(ctx, pr_n, "the pull request is on hold (label `hold`)")
        return "held"
    sha = pr["head"]["sha"]
    if not SHA_RE.match(sha or ""):
        raise ValueError("the pull request's head is not a full SHA")
    git = ctx.git()
    got = None
    for k in range(4):
        got = git.fetch(f"refs/pull/{pr_n}/head")
        if got == sha:
            break
        ctx.sleep(5 * (k + 1))
    if got != sha:
        if ctx.gh.pr(pr_n)["head"]["sha"] != sha:
            ctx.log(f"intake: #{pr_n} moved while it was read; the newer event's run handles it")
            return "moved"
        raise RuntimeError(f"refs/pull/{pr_n}/head is {got}, the API says {sha}")
    eid = entry_id(pr_n, sha)
    info = {}
    if root:
        more, info = precheck.tree_rule(git, sha, root)
        reasons = reasons + more
    agent, builds = precheck.notes_header(info["notes"], pr_n) if info.get("notes") else (None, [])
    entry = {"id": eid, "pr": pr_n, "sha": sha, "root": root or "",
             "author": author if LOGIN_RE.match(author or "") else clean(author, 40),
             "title": clean(pr.get("title"), 200), "agent": agent, "builds_on": builds,
             "opened": pr.get("created_at"), "queued": None, "started": None, "finished": None, "attempts": 0,
             "status": "queued", "verdict": None, "score": None, "comparable": False, "truncated": False,
             "reasons": [], "cpu": [], "run_url": None, "tag": f"rf-source/{eid}",
             "notes": f"notes/{eid}.md" if info.get("notes") else None,
             "readme": f"readme/{eid}.md" if info.get("readme") else None,
             "record_of": None, "tree": info.get("tree"), "verified": False, "harness_commit": None,
             "prover_sha256": None}
    if not reasons:
        dup = rfqueue.duplicate_of(_state(ctx, git.snapshot(DATA)), eid, pr_n, author, entry["tree"])
        if dup:
            reasons.append(dup)
    if not reasons and not git.create_tag(sha, entry["tag"]):
        reasons.append(f"the retention tag {entry['tag']} exists at another commit")
    valid = not reasons
    reasons = [clean(r, 300) for r in reasons[:20]]
    done = {}

    def mutate(snap):
        st = _state(ctx, snap)
        now = ctx.now()
        e = copy.deepcopy(entry)
        if valid:
            dup = rfqueue.duplicate_of(st, eid, pr_n, author, e["tree"])
            if dup:
                e, changed = rfqueue.add_invalid(st, e, [dup], now)
            else:
                e, changed = rfqueue.enqueue(st, e, now)
        else:
            e, changed = rfqueue.add_invalid(st, e, reasons, now)
        done.clear()
        if not changed:
            return None
        ch = Changes()
        extra = {}
        if e["status"] == "queued":
            if info.get("notes"):
                ch.put(e["notes"], info["notes"])
                extra[e["notes"]] = info["notes"]
            if info.get("readme"):
                ch.put(e["readme"], info["readme"])
        _write_state(ctx, ch, snap, st, extra)
        done.update(entry=copy.deepcopy(e), pos=rfqueue.position(st, eid))
        return ch
    git.transact(DATA, mutate, f"intake #{pr_n}: {eid}")
    if not done:
        ctx.log(f"intake: #{pr_n} {eid} unchanged")
        return "unchanged"
    e = done["entry"]
    state, desc = render.status_for(e)
    ctx.gh.set_status(sha, state, desc, f"{ctx.server}/{ctx.repo}/pull/{pr_n}")
    ctx.gh.comment(pr_n, render.intake_comment(e, *done["pos"]))
    if e["status"] == "queued":
        ctx.gh.dispatch("evaluate-next.yml", ctx.default_branch)
    return e["status"]


# ---- select -------------------------------------------------------------------------------------
def select(ctx, force_pr=None):
    """Picks the next entry (brief §4; `force_pr`: that pull request's queued or errored entry),
    marks it running, and returns a copy of it (None: nothing to evaluate). Entries a previous run
    left running are reaped first (runs are serialised by the `rf-eval` concurrency group)."""
    live, picked, notify, final = {}, {}, {}, {}

    def live_pr(n):
        if n not in live:
            try:
                live[n] = ctx.gh.pr(n)
            except Exception as ex:  # noqa: BLE001 - one unreadable pull request must not stop the queue
                ctx.log(f"select: #{n} unreadable ({ex.__class__.__name__}); skipped")
                live[n] = None
        return live[n]

    def mutate(snap):
        st = _state(ctx, snap)
        now = ctx.now()
        picked.clear()
        notify.clear()
        reaped = rfqueue.reap(st, now)
        notify.update({i: copy.deepcopy(rfqueue.find(st, i)) for i in reaped})
        changed = bool(reaped)
        cands = rfqueue.order(st)
        if force_pr is not None:
            cands = [e for e in cands if e["pr"] == force_pr]
            if not cands:
                errs = [e for e in rfqueue.of_pr(st, force_pr) if e["status"] == "error"]
                if errs:
                    e = max(errs, key=lambda e: e.get("finished") or "")
                    e.update(status="queued", finished=None, attempts=0)
                    cands, changed = [e], True
        for e in cands[:25]:
            p = live_pr(e["pr"])
            if p is None:
                continue
            if p.get("state") != "open":
                e.update(status="withdrawn", finished=now, reasons=["the pull request was closed before its evaluation"])
                changed = True
                continue
            if (p.get("head") or {}).get("sha") != e["sha"]:
                e.update(status="superseded", finished=now,
                         reasons=["the pull request moved before this commit was evaluated"])
                changed = True
                continue
            if force_pr is None and (p.get("draft") or "hold" in _labels(p)):
                continue
            rfqueue.mark_running(e, now, ctx.run_url)
            rec = rfqueue.current_record(st)
            e["duel_with"] = rec["id"] if rec else None      # the incumbent this run measures (brief §2a)
            picked.update(copy.deepcopy(e))
            picked["record_cache"] = e.get("record_cache") is not False
            if rec:
                picked["incumbent"] = {k: rec[k] for k in ("id", "sha", "root", "tag")}
            changed = True
            break
        final.update(state=copy.deepcopy(st))
        if not changed:
            return None
        ch = Changes()
        _write_state(ctx, ch, snap, st)
        return ch
    ctx.git().transact(DATA, mutate, "select")
    try:
        sync_main(ctx, final["state"])    # heals a record a failed publish left off main
    except Exception as ex:  # noqa: BLE001 - never block the queue on it; publish raises it
        ctx.log(f"select: main is not synced to the record: {ex}")
    for e in notify.values():
        st_, desc = render.status_for(e)
        ctx.gh.set_status(e["sha"], st_, desc, e.get("run_url"))
    if not picked:
        ctx.log("select: nothing to evaluate")
        return None
    e = picked
    if not (ID_RE.match(e["id"]) and SHA_RE.match(e["sha"]) and ROOT_RE.match(e["root"])):
        raise ValueError(f"select: a malformed entry {e['id']!r}")
    git = ctx.git()
    if git.remote_ref(f"refs/tags/{e['tag']}") != e["sha"]:
        if git.fetch(f"refs/pull/{e['pr']}/head") != e["sha"] or not git.create_tag(e["sha"], e["tag"]):
            raise RuntimeError(f"select: the retention tag {e['tag']} is missing and cannot be created")
    ctx.gh.set_status(e["sha"], "pending", "evaluating", ctx.run_url)
    return e


# ---- publish ------------------------------------------------------------------------------------
def load_result(path, cap=16 << 20):
    """(raw bytes, parsed dict) of result.json, or (None, None)."""
    try:
        with open(path, "rb") as f:
            raw = f.read(cap + 1)
        if len(raw) > cap:
            return None, None
        r = json.loads(raw)
        return (raw, r) if isinstance(r, dict) else (None, None)
    except (OSError, ValueError, RecursionError):
        return None, None


def publish(ctx, eid, result_path):
    """Publishes the verdict of the running entry `eid` (this run's): its status, the result on
    `data`, the record on `main`, the comment and the commit status; then dispatches the next
    evaluation if anything is queued. Returns the entry (None if this run does not own it)."""
    raw, result = load_result(result_path) if result_path else (None, None)
    if result is None:
        ver = {"attested": False, "record_ok": False, "reason": "no result"}
    else:
        ver = ctx.verify(result_path, result)
    done = {}

    def mutate(snap):
        st = _state(ctx, snap)
        done.clear()
        e = rfqueue.find(st, eid)
        if e is None or e["status"] != "running" or e.get("run_url") != ctx.run_url:
            return None
        rec = rfqueue.current_record(st)
        provers = {r["prover_sha256"]: r["id"] for r in rfqueue.records(st) if r.get("prover_sha256")}
        res = result
        if isinstance(result, dict) and (rec or {}).get("id") != e.get("duel_with"):
            res = dict(result, incumbent=None)    # measured against another record than the standing one
        d = decide(res, ver, ctx.pin, rec, e.get("attempts", 1), provers)
        now = ctx.now()
        ps = result.get("prover_sha256") if isinstance(result, dict) else None
        e.update({k: d[k] for k in ("verdict", "score", "comparable", "truncated", "cpu", "harness_commit",
                                    "verified", "record_of", "duel", "reasons")},
                 prover_sha256=ps if isinstance(ps, str) and len(ps) == 64 and ps.isalnum() else None)
        if d["status"] != "queued" and cache_retry(result, e):
            d["requeue"] = True
            e["record_cache"] = False         # the next evaluation runs without the record build cache
            e["reasons"] = e["reasons"][:19] + ["the record build cache was reused: evaluated once more without it"]
        if d["requeue"]:
            e.update(status="queued", finished=None)
        else:
            e.update(status=d["status"], finished=now)
        ch = Changes()
        if raw is not None and len(raw) <= 4 << 20:
            ch.put(f"results/{eid}.json", raw)
            e["result"] = f"results/{eid}.json"
        _write_state(ctx, ch, snap, st)
        done.update(entry=copy.deepcopy(e), state=copy.deepcopy(st))
        return ch
    ctx.git().transact(DATA, mutate, f"publish {eid}")
    if not done:
        ctx.log(f"publish: {eid} is not running under this run; nothing published")
        return None
    e, st = done["entry"], done["state"]
    try:
        state, desc = render.status_for(e)
        ctx.gh.set_status(e["sha"], state, desc, ctx.run_url)
        ctx.gh.comment(e["pr"], render.publish_comment(e, ctx.run_url))
        if e["status"] == "record":
            sync_main(ctx, st)
    finally:
        if rfqueue.any_queued(st):
            ctx.gh.dispatch("evaluate-next.yml", ctx.default_branch)
    return e


def sync_main(ctx, st):
    """Makes `main` hold the current record: its checked root (the tree at its retained commit,
    replacing the previous record's root) and `records.json`. A no-op if `main` already does, or
    if there is no record."""
    rec = rfqueue.current_record(st)
    if rec is None:
        return None
    want = render.records_json(st, ctx.pin)
    git = ctx.git()
    commit = git.fetch(f"refs/tags/{rec['tag']}", local="refs/rf/record")
    if commit != rec["sha"]:
        raise RuntimeError(f"sync_main: the tag {rec['tag']} is at {commit}, the record is {rec['sha']}")
    tree = git.tree_of(commit, f"submissions/{rec['root']}")
    if tree is None or (rec.get("tree") and tree != rec["tree"]):
        raise RuntimeError(f"sync_main: the root of {rec['id']} at its tag is not the root that was checked")

    def mutate(snap):
        cur = snap.read("records.json", 16 << 20)
        if cur == want:
            return None
        old = None
        try:
            old = (json.loads(cur or b"null") or {}).get("record") or {}
            old = old.get("root") if isinstance(old, dict) else None
        except (ValueError, AttributeError):
            old = None
        ch = Changes()
        if isinstance(old, str) and ROOT_RE.match(old) and old != rec["root"]:
            ch.drop_dir(f"submissions/{old}")
        ch.drop_dir(f"submissions/{rec['root']}")
        ch.graft(f"submissions/{rec['root']}", tree)
        ch.put("records.json", want)
        return ch
    s = (rec.get("score") or {}).get("S")
    return git.transact(ctx.default_branch, mutate,
                        f"record: {rec['root']} ({rec['id']}, S = {render.num(s)} s) by {rec['author']}, "
                        f"evaluated in {rec.get('run_url')}")


def record_build(ctx, result, build_dir, pin, eid):
    """Whether the downloaded `entry-build` artifact of a new record may be cached: its
    manifest.json's sha256 is the attested `entry_build.manifest_sha256`. If so, deletes the older
    `rf-record-build-<pin>-*` caches (the new one is saved by the workflow under the returned key)."""
    import hashlib
    import os
    from decide import build_manifest_sha
    want = build_manifest_sha(result)
    try:
        with open(os.path.join(build_dir, "manifest.json"), "rb") as f:
            got = hashlib.sha256(f.read()).hexdigest()
    except OSError:
        got = None
    if not want or got != want:
        ctx.log(f"record-build: not cached (manifest {got}, attested {want})")
        return None
    key = f"rf-record-build-{pin}-{eid}"
    for c in ctx.gh.caches(f"rf-record-build-{pin}-"):
        if c.get("key") != key and str(c.get("key", "")).startswith(f"rf-record-build-{pin}-"):
            ctx.gh.delete_cache(c["key"])
    return key
