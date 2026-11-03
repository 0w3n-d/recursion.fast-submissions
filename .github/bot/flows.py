"""The bot's steps (TRUSTED): intake, sync, select, publish, and the sync of `main` to the record.
Each reads GitHub through `ctx.gh` and git through `gitdata.Repo(ctx.git_url)`, so the tests and
`simulate.py` drive them against a local bare repository and a fake API.

Writers of `data` (two, so that racing intakes cannot lose entries): `sync` (workflow sync.yml, concurrency `rf-data`) is the only writer
of new queue entries; `select` and `publish` (evaluate-next.yml, `rf-eval`) mark entries running and
evaluated. The intake writes nothing on `data`: it prechecks, creates the retention tag, and sets
the commit status `recursion.fast/evaluation` to pending "queued", whose `created_at` is the queue
timestamp (only the base repository's token can set it); then it dispatches `sync`, which rescans
every open pull request and is idempotent, so coalesced runs lose nothing.

No step runs entry code or checks an entry out: a pull request is read as git objects and API
JSON. Every write to `data` and `main` is an optimistic transaction (`gitdata.Repo.transact`), and a
`data` that cannot be read aborts the step (nothing is reset)."""
import copy
import json
import time

import precheck
import render
import rfqueue
from common import CONFIRMING, ID_RE, LOGIN_RE, MAX_TEXT_BYTES, ROOT_RE, SHA_RE, STATUS_CONTEXT, clean, entry_id, now_iso
from decide import build_manifest_sha, cache_retry, decide
from gitdata import Changes, Repo

DATA, NOTES_MD = "data", "notes.md"
ORGANISER = ("admin", "maintain", "write")
BOT_LOGIN = "github-actions[bot]"
# descriptions of the bot's statuses after which a head may be admitted again
READMIT = ("withdrawn", "superseded", "intake failed")


class Ctx:
    """Everything a step needs from its environment."""

    def __init__(self, gh, repo, git_url, pin, token=None, run_id="0", run_attempt=1, server="https://github.com",
                 default_branch="main", clock=None, sleep=time.sleep, verify=None, log=print, bot_login=BOT_LOGIN):
        self.gh, self.repo, self.git_url, self.pin, self.token = gh, repo, git_url, pin, token
        self.run_id, self.run_attempt, self.server, self.default_branch = str(run_id), int(run_attempt), server, default_branch
        self.run_url = f"{server}/{repo}/actions/runs/{self.run_id}"
        self.clock, self.sleep, self.verify, self.log, self.bot_login = clock, sleep, verify, log, bot_login

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


def _try(ctx, what, fn, *a):
    """One side effect (a status, a comment, a dispatch): logged, never stopping the others.
    Returns False on failure."""
    try:
        fn(*a)
        return True
    except Exception as ex:  # noqa: BLE001
        ctx.log(f"{what} failed: {ex.__class__.__name__}: {str(ex)[:200]}")
        return False


def bot_statuses(ctx, sha):
    """The bot's statuses of the context on `sha`, newest first."""
    return [s for s in ctx.gh.statuses(sha) if s.get("context") == STATUS_CONTEXT
            and (s.get("creator") or {}).get("login") == ctx.bot_login]


def main_roots(git, branch="main"):
    """The directory names under `submissions/` on `main`."""
    head = git.fetch(f"refs/heads/{branch}", local="refs/rf/main-roots")
    if not head:
        return set()
    return {p.split("/", 1)[1] for mode, typ, _s, p in git.ls_tree(head, "submissions")
            if typ == "tree" and p.count("/") == 1}


# ---- examine: what the bot makes of a pull request's head (reads only) ----------------------------
def examine(ctx, git, pr, st, reserved=()):
    """{kind, entry, info, reasons}: kind is ignored (not into main), organiser, closed, draft, held,
    moved (the head changed while it was read), invalid or valid."""
    n = pr["number"]
    author = (pr.get("user") or {}).get("login") or "ghost"
    if (pr.get("base") or {}).get("ref") != ctx.default_branch:
        return {"kind": "ignored"}
    files = ctx.gh.pr_files(n) if (pr.get("changed_files") or 0) <= 3000 else None
    root, reasons, outside = precheck.paths_rule(files)
    if outside and ctx.gh.permission(author) in ORGANISER:
        return {"kind": "organiser"}
    if pr.get("state") != "open":
        return {"kind": "closed"}
    if pr.get("draft"):
        return {"kind": "draft"}
    if "hold" in _labels(pr):
        return {"kind": "held"}
    sha = (pr.get("head") or {}).get("sha") or ""
    if not SHA_RE.match(sha):
        raise ValueError("the pull request's head is not a full SHA")
    got = None
    for k in range(4):
        got = git.fetch(f"refs/pull/{n}/head")
        if got == sha:
            break
        ctx.sleep(5 * (k + 1))
    if got != sha:
        if ctx.gh.pr(n)["head"]["sha"] != sha:
            return {"kind": "moved"}
        raise RuntimeError(f"refs/pull/{n}/head is {got}, the API says {sha}")
    eid = entry_id(n, sha)
    info = {}
    if root:
        if root in reserved:
            reasons.append(f"submissions/{root}/ is a directory the organiser keeps on main; choose another root name")
        more, info = precheck.tree_rule(git, sha, root)
        reasons = reasons + more
    agent, builds = precheck.notes_header(info["notes"], n) if info.get("notes") else (None, [])
    entry = {"id": eid, "pr": n, "sha": sha, "root": root or "",
             "author": author if LOGIN_RE.match(author) else clean(author, 40),
             "title": clean(pr.get("title"), 200), "agent": agent, "builds_on": builds,
             "opened": pr.get("created_at"), "queued": None, "started": None, "finished": None, "attempts": 0,
             "status": "queued", "verdict": None, "score": None, "comparable": False, "truncated": False,
             "reasons": [], "cpu": [], "run_url": None, "tag": f"rf-source/{eid}",
             "notes": f"notes/{eid}.md" if info.get("notes") else None,
             "readme": f"readme/{eid}.md" if info.get("readme") else None,
             "record_of": None, "tree": info.get("tree"), "verified": False, "harness_commit": None,
             "prover_sha256": None}
    if not reasons:
        dup = rfqueue.duplicate_of(st, eid, n, entry["author"], entry["tree"])
        if dup:
            reasons.append(dup)
    reasons = [clean(r, 300) for r in reasons[:20]]
    if reasons:
        entry.update(tag=None, notes=None, readme=None)
    return {"kind": "invalid" if reasons else "valid", "entry": entry, "info": info, "reasons": reasons}


def admit(ctx, git, x, force=False):
    """The intake's writes for an examined head (none on `data`): the retention tag and the pending
    "queued" status (valid), or the failure status (invalid), and one comment. A head the bot has
    already admitted is left alone unless `force` (the owner's re-intake). Returns the head's queue
    timestamp (the status's time) or None."""
    e = x["entry"]
    prior = bot_statuses(ctx, e["sha"])
    if prior and not force and not prior[0].get("description", "").startswith(READMIT):
        return None
    if x["kind"] == "valid" and not git.create_tag(e["sha"], e["tag"]):
        x["kind"], x["reasons"] = "invalid", [f"the retention tag {e['tag']} exists at another commit"]
        e.update(tag=None, notes=None, readme=None)
    if x["kind"] == "valid":
        ctx.gh.set_status(e["sha"], "pending", "queued", f"{ctx.server}/{ctx.repo}/pull/{e['pr']}")
        if not prior:
            _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(dict(e, status="queued"), None, None))
    else:
        e2 = dict(e, status="invalid", reasons=x["reasons"])
        ctx.gh.set_status(e["sha"], *render.status_for(e2), f"{ctx.server}/{ctx.repo}/pull/{e['pr']}")
        _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(e2, None, None))
    return ctx.now()


# ---- intake -------------------------------------------------------------------------------------
def intake(ctx, pr_n, force=False):
    """Prechecks the pull request's current head and admits it (tag, status, comment), then
    dispatches `sync`. Writes nothing on `data`. Returns what it found."""
    pr = ctx.gh.pr(pr_n)
    git = ctx.git()
    st = _state(ctx, git.snapshot(DATA))       # fails closed: an unreadable `data` stops the intake
    x = examine(ctx, git, pr, st, _reserved(git, st))
    if x["kind"] in ("valid", "invalid"):
        admit(ctx, git, x, force)
    if x["kind"] not in ("ignored", "organiser"):
        _try(ctx, "dispatch sync", ctx.gh.dispatch, "sync.yml", ctx.default_branch)
    ctx.log(f"intake: #{pr_n}: {x['kind']}")
    return x["kind"]


def intake_failed(ctx, pr_n):
    """After an exception in the intake: the head's status says so (sync retries it)."""
    try:
        sha = ctx.gh.pr(pr_n)["head"]["sha"]
        ctx.gh.set_status(sha, "error", "intake failed; the bot retries it", ctx.run_url)
    except Exception as ex:  # noqa: BLE001
        ctx.log(f"intake_failed: {ex}")


def _reserved(git, st):
    roots = {e["root"] for e in rfqueue.records(st)}
    return main_roots(git) - roots


# ---- sync: the single writer of new queue entries ------------------------------------------------
def sync(ctx):
    """Brings `data` up to date with GitHub: every open pull request's head is queued (with its
    NOTES/README copied from the retention tag) or invalid; older heads are superseded; closed,
    draft, held and organiser pull requests' queued entries are withdrawn; superseded and withdrawn
    heads get their commit status. Idempotent. Returns the number of entries changed."""
    git = ctx.git()
    st0 = _state(ctx, git.snapshot(DATA))
    reserved = _reserved(git, st0)
    prs = {p["number"]: p for p in ctx.gh.open_prs()}
    looks, admitted = {}, {}
    for n, pr in sorted(prs.items()):
        if (pr.get("base") or {}).get("ref") != ctx.default_branch or pr.get("draft") or "hold" in _labels(pr):
            continue
        sha = pr["head"]["sha"]
        old = rfqueue.find(st0, entry_id(n, sha)) if SHA_RE.match(sha or "") else None
        if old and old["status"] not in ("withdrawn", "superseded", "invalid"):
            continue
        prior = bot_statuses(ctx, sha)
        if old and old["status"] == "invalid" and not (prior and prior[0].get("description") == "queued"):
            continue                       # an invalid head stays invalid unless re-admitted
        try:
            full = ctx.gh.pr(n)            # changed_files is only in the single-PR payload
            x = examine(ctx, git, full, st0, reserved)
        except Exception as ex:  # noqa: BLE001 - one unreadable pull request must not stop the others
            ctx.log(f"sync: #{n} not examined ({ex.__class__.__name__}: {str(ex)[:120]}); next sync retries")
            continue
        if x["kind"] not in ("valid", "invalid"):
            looks[n] = x
            continue
        # the head's status must say what the bot found: a valid head "queued" (whose time is the
        # queue time), an invalid one "invalid…"; otherwise (no intake ran, it failed, or the fresh
        # state disagrees with it) sync admits the head itself
        want = "queued" if x["kind"] == "valid" else "invalid"
        top = prior[0].get("description", "") if prior else ""
        if (top == "queued") if want == "queued" else top.startswith("invalid"):
            q = prior[0]["created_at"]
        else:
            try:
                q = admit(ctx, git, x, force=True)
            except Exception as ex:  # noqa: BLE001
                ctx.log(f"sync: #{n} not admitted ({ex.__class__.__name__}: {str(ex)[:120]}); next sync retries")
                continue
        admitted[n] = (x, q)
    closed = {}
    for e in st0["submissions"]:
        if e["status"] == "queued" and e["pr"] not in prs and e["pr"] not in closed:
            try:
                closed[e["pr"]] = ctx.gh.pr(e["pr"])
            except Exception as ex:  # noqa: BLE001
                ctx.log(f"sync: #{e['pr']} unreadable ({ex.__class__.__name__}); kept")
    effects, changed = [], []

    def mutate(snap):
        st = _state(ctx, snap)
        now = ctx.now()
        effects.clear()
        changed.clear()
        before = {e["id"]: e["status"] for e in st["submissions"]}
        ch, extra = Changes(), {}
        for n, (x, q) in sorted(admitted.items(), key=lambda kv: (kv[1][1], kv[0])):
            e = copy.deepcopy(x["entry"])
            e["builds_on"] = [b for b in e.get("builds_on") or [] if rfqueue.of_pr(st, b)]
            if x["kind"] == "valid":
                dup = rfqueue.duplicate_of(st, e["id"], n, e["author"], e["tree"])
                if dup:
                    e.update(tag=None, notes=None, readme=None)
                    e, _c = rfqueue.add_invalid(st, e, [dup], q)
                    effects.append(("invalid", copy.deepcopy(e)))
                    continue
                e, _c = rfqueue.enqueue(st, e, q)
                if e["status"] == "queued":
                    for k, src in (("notes", "notes"), ("readme", "readme")):
                        if e.get(k) and x["info"].get(src):
                            ch.put(e[k], x["info"][src])
                            extra[e[k]] = x["info"][src]
            else:
                rfqueue.add_invalid(st, e, x["reasons"], q)
        for n, pr in prs.items():
            sha = (pr.get("head") or {}).get("sha") or ""
            if (pr.get("base") or {}).get("ref") != ctx.default_branch:
                continue
            kind = (looks.get(n) or {}).get("kind")
            if pr.get("draft") or kind == "draft":
                rfqueue.withdraw(st, n, now, "the pull request is a draft")
                continue
            if "hold" in _labels(pr) or kind == "held":
                rfqueue.withdraw(st, n, now, "the pull request is on hold (label hold)")
                continue
            if kind == "organiser":
                rfqueue.withdraw(st, n, now, "an organiser pull request")
                continue
            for e in rfqueue.of_pr(st, n):
                if e["status"] == "queued" and e["sha"] != sha:
                    e.update(status="superseded", finished=now,
                             reasons=["the pull request moved before this commit was evaluated"])
        for n, pr in closed.items():
            if pr.get("state") != "open":
                rfqueue.withdraw(st, n, now, "the pull request was closed before its evaluation")
        for path in rfqueue.compact(st):
            ch.put(path, None)
        for e in st["submissions"]:
            if before.get(e["id"]) != e["status"]:
                changed.append(e["id"])
                if e["status"] in ("superseded", "withdrawn") and before.get(e["id"]) is not None:
                    effects.append(("status", copy.deepcopy(e)))
        stale = bool(st.get("_stale"))
        if not changed and ch.empty() and snap.head and not stale:
            return None                    # (an absent `data` is created, with an empty state)
        _write_state(ctx, ch, snap, st, extra)
        effects.append(("queued?", rfqueue.any_queued(st) or rfqueue.due_port(st, ctx.pin) is not None))
        if stale:
            effects.append(("main", copy.deepcopy(st)))
        return ch
    git.transact(DATA, mutate, "sync")
    for kind, e in effects:
        if kind == "status":
            st_, desc = render.status_for(e)
            _try(ctx, "status", ctx.gh.set_status, e["sha"], st_, desc, None)
        elif kind == "invalid":
            _try(ctx, "status", ctx.gh.set_status, e["sha"], *render.status_for(e), None)
            _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(e, None, None))
        elif kind == "queued?" and e:
            _try(ctx, "dispatch", ctx.gh.dispatch, "evaluate-next.yml", ctx.default_branch)
        elif kind == "main":
            _try(ctx, "sync main", sync_main, ctx, e)
    ctx.log(f"sync: {len(changed)} entries changed")
    return len(changed)


# ---- select -------------------------------------------------------------------------------------
def select(ctx, force_pr=None, retire_id=None):
    """Picks the next entry (`rfqueue.order`; `force_pr`: that pull request's waiting or errored
    entry), marks it running, and returns a copy of it with the standing record as `incumbent`
    (None: nothing to evaluate). Entries a previous run left running are reaped first (runs are
    serialised by `rf-eval`). `retire_id`: the owner retires that record first. When no record
    stands at the pin and the last record is of an earlier pin, its port to this pin is created
    and evaluated before anything else, forced runs included, so no other entry can take the
    record unpaired before it."""
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
        changed = False
        changed = bool(st.get("_stale"))      # a pin move: rewrite the pin and its record at once
        if retire_id:
            r = rfqueue.find(st, retire_id)
            if r is not None and r["status"] == "record":
                rfqueue.retire(r, now, "retired by the owner")
                for i in rfqueue.void_confirmations(st, r["id"], now):
                    notify[i] = copy.deepcopy(rfqueue.find(st, i))
                changed = True
        rec0 = rfqueue.current_record(st, ctx.pin)
        reaped = rfqueue.reap(st, now, rec0["id"] if rec0 else None)
        notify.update({i: copy.deepcopy(rfqueue.find(st, i)) for i in reaped})
        settled = rfqueue.settle(st, ctx.pin, now)
        changed = changed or bool(reaped) or bool(settled)
        cands = rfqueue.order(st)
        due = rfqueue.due_port(st, ctx.pin)
        ports = [e for e in cands if e.get("port_of") and e["status"] == "queued"]
        if due is not None:
            cands, changed = [rfqueue.port(st, due["pr"], ctx.pin, now, o=due)], True
        elif ports:
            cands = ports[:1]                  # a waiting port (re-queued after an ERROR) is still first
        elif force_pr is not None:
            cands = [e for e in cands if e["pr"] == force_pr]
            if not cands:
                errs = [e for e in rfqueue.of_pr(st, force_pr) if e["status"] == "error"]
                if errs:
                    e = max(errs, key=lambda e: e.get("finished") or "")
                    e.update(status=rfqueue.waiting(e, rec0["id"] if rec0 else None), finished=None, attempts=0)
                    cands, changed = [e], True
                else:
                    port = rfqueue.port(st, force_pr, ctx.pin, now)
                    if port:
                        cands, changed = [port], True
        for e in cands:                      # every candidate, so one unreadable PR blocks nothing
            p = live_pr(e["pr"]) if not e.get("port_of") else {"state": "open", "head": {"sha": e["sha"]}}
            if p is None:
                continue
            if e["status"] == CONFIRMING:
                # mid-evaluation: its retained commit is confirmed whatever the PR did since; only
                # the owner's `hold` keeps it waiting
                if force_pr is None and "hold" in _labels(p):
                    continue
            else:
                if p.get("state") != "open":
                    e.update(status="withdrawn", finished=now, reasons=["the pull request was closed before its evaluation"])
                    notify[e["id"]] = copy.deepcopy(e)
                    changed = True
                    continue
                if (p.get("head") or {}).get("sha") != e["sha"]:
                    e.update(status="superseded", finished=now,
                             reasons=["the pull request moved before this commit was evaluated"])
                    notify[e["id"]] = copy.deepcopy(e)
                    changed = True
                    continue
                if force_pr is None and (p.get("draft") or "hold" in _labels(p)):
                    continue
            rfqueue.mark_running(e, now, ctx.run_url)
            e["run_attempt"] = ctx.run_attempt
            rec = rfqueue.current_record(st, ctx.pin)
            e["duel_with"] = rec["id"] if rec else None      # the incumbent this run measures
            picked.update(copy.deepcopy(e))
            picked["record_cache"] = e.get("record_cache") is not False
            if rec:
                picked["incumbent"] = {k: rec[k] for k in ("id", "sha", "root", "tag")}
            # the record build cache may only be restored with the standing record's attested manifest
            picked["record_manifest"] = (rec or {}).get("build_manifest") or ""
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
        _try(ctx, "status", ctx.gh.set_status, e["sha"], st_, desc, e.get("run_url"))
    if not picked:
        ctx.log("select: nothing to evaluate")
        return None
    e = picked
    if not (ID_RE.match(e["id"]) and SHA_RE.match(e["sha"]) and ROOT_RE.match(e["root"])):
        raise ValueError(f"select: a malformed entry {e['id']!r}")
    git = ctx.git()
    for t, s in [(e["tag"], e["sha"])] + ([(e["incumbent"]["tag"], e["incumbent"]["sha"])] if e.get("incumbent") else []):
        if git.remote_ref(f"refs/tags/{t}") != s:
            raise RuntimeError(f"select: the retention tag {t} is not at {s}")
    _try(ctx, "status", ctx.gh.set_status, e["sha"], "pending", "evaluating", ctx.run_url)
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
    st0 = _state(ctx, ctx.git().snapshot(DATA))
    e0 = rfqueue.find(st0, eid) or {}
    if result is None:
        ver = {"attested": False, "record_ok": False, "reason": "no result"}
    else:
        ver = ctx.verify(result_path, result, e0.get("run_attempt") or 1)
    done = {}

    def mutate(snap):
        st = _state(ctx, snap)
        done.clear()
        e = rfqueue.find(st, eid)
        if e is None or e["status"] != "running" or e.get("run_url") != ctx.run_url:
            return None
        rec = rfqueue.current_record(st, ctx.pin)
        # the records of other commits: every port of a record shares its commit, and keeps its crown
        provers = {r["prover_sha256"]: r["id"] for r in rfqueue.records(st)
                   if r.get("prover_sha256") and r.get("sha") != e.get("sha")}
        res = result
        if isinstance(result, dict) and (rec or {}).get("id") != e.get("duel_with"):
            res = dict(result, duel=None, incumbent=None)     # measured against another record
        rid = rec["id"] if rec else None
        d = decide(res, ver, ctx.pin, rec, e.get("attempts", 1), provers,
                   duel_retries=len(rfqueue.failed_duels(e, rid)) if rec else 0,
                   record_failures=(rec or {}).get("duel_failures", 0),
                   wins=rfqueue.won_duels(e, rid) if rec else (), confirm_retries=e.get("confirm_retries", 0))
        now = ctx.now()
        ps = result.get("prover_sha256") if isinstance(result, dict) else None
        e["build_manifest"] = build_manifest_sha(result) if d["verified"] else None
        e.update({k: d[k] for k in ("verdict", "score", "comparable", "truncated", "cpu", "harness_commit",
                                    "verified", "record_of", "duel", "reasons")},
                 prover_sha256=ps if isinstance(ps, str) and len(ps) == 64 and ps.isalnum() else None)
        if d["record_failed"] and rec is not None:
            rec["duel_failures"] = rec.get("duel_failures", 0) + 1
            if d["retire_record"]:
                rfqueue.retire(rec, now, f"its own run failed in {rec['duel_failures']} duels in a row")
                done["voided"] = rfqueue.void_confirmations(st, rec["id"], now)
        elif rec is not None and d["duel_now"]:
            rec["duel_failures"] = 0           # the record completed a duel: failures count in a row
        if d["confirm_retry"]:
            e["confirm_retries"] = e.get("confirm_retries", 0) + 1
        elif (d["duel_now"] or {}).get("won"):
            e["confirm_retries"] = 0
        ch = Changes()
        keep_raw = raw is not None and len(raw) <= 4 << 20
        if d["duel_now"]:                      # every duel is kept, with its own copy of the result
            e["duels"] = (e.get("duels") or [])[-9:] + [dict(d["duel_now"], run_url=ctx.run_url)]
            if keep_raw:
                e["duels"][-1]["result"] = f"results/{eid}.duel{len(e['duels'])}.json"
                ch.put(e["duels"][-1]["result"], raw)
            if d["duel_now"].get("won") and d["status"] == CONFIRMING:
                e["attempts"] = 0              # the confirmation has its own organiser-error retry
        if d["status"] not in ("queued", CONFIRMING) and cache_retry(result, e):
            d["requeue"] = True
            e["reasons"] = e["reasons"][:19] + ["the record build cache was used: evaluated once more without it"]
        if d["requeue"] or d["status"] == CONFIRMING:
            if d["verdict"] in ("ERROR", "REJECT") or not d["verified"]:
                e["record_cache"] = False      # the retry builds clean: a sabotaged cache cannot fail it
            cur = rfqueue.current_record(st, ctx.pin)
            e.update(status=d["status"] if d["status"] in ("queued", CONFIRMING) else rfqueue.waiting(e, cur and cur["id"]),
                     finished=None)
        else:
            e.update(status=d["status"], finished=now)
        rfqueue.settle(st, ctx.pin, now)       # wins against a record that no longer stands are void
        cur = rfqueue.current_record(st, ctx.pin)
        done["record_changed"] = (cur or {}).get("id") != rid
        if keep_raw:
            ch.put(f"results/{eid}.json", raw)
            e["result"] = f"results/{eid}.json"
        _write_state(ctx, ch, snap, st)
        done.update(entry=copy.deepcopy(e), state=copy.deepcopy(st))
        return ch
    ctx.git().transact(DATA, mutate, f"publish {eid}")
    changed_record, voided = done.pop("record_changed", False), done.pop("voided", [])
    if not done:
        ctx.log(f"publish: {eid} is not running under this run; nothing published")
        return None
    e, st = done["entry"], done["state"]
    failed = []
    if not _try(ctx, "status", ctx.gh.set_status, e["sha"], *render.status_for(e), ctx.run_url):
        failed.append("status")
    if not _try(ctx, "comment", ctx.gh.comment, e["pr"], render.publish_comment(e, ctx.run_url)):
        failed.append("comment")
    for i in voided:                           # confirmations voided by this retirement
        v = rfqueue.find(st, i)
        _try(ctx, "status", ctx.gh.set_status, v["sha"], *render.status_for(v), v.get("run_url"))
    if (e["status"] == "record" or changed_record) and not _try(ctx, "sync main", sync_main, ctx, st):
        failed.append("main")
    if rfqueue.any_queued(st) and not _try(ctx, "dispatch", ctx.gh.dispatch, "evaluate-next.yml", ctx.default_branch):
        failed.append("dispatch")
    if failed:
        raise RuntimeError(f"publish: {eid} is published on data, but these failed: {', '.join(failed)}")
    return e


def sync_main(ctx, st):
    """Makes `main` hold the standing record: its checked root (the tree at its retained commit,
    replacing the roots of earlier records) and `records.json`, which names the pin and the standing
    record whatever happens. With no record at this pin, only `records.json` changes (`record:
    null`) and the last record's root stays until a new record replaces it. A no-op if `main`
    already says so."""
    rec = rfqueue.current_record(st, ctx.pin)
    want = render.records_json(st, ctx.pin)
    git = ctx.git()
    if rec is None:
        def mutate_none(snap):
            if snap.read("records.json", 16 << 20) == want:
                return None
            ch = Changes()
            ch.put("records.json", want)
            return ch
        return git.transact(ctx.default_branch, mutate_none, f"records: no record stands at the pin {ctx.pin[:12]}")
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
        olds = set()
        try:
            j = json.loads(cur or b"null") or {}
            for r in [j.get("record")] + list(j.get("history") or []):
                if isinstance(r, dict) and isinstance(r.get("root"), str) and ROOT_RE.match(r["root"]):
                    olds.add(r["root"])
        except (ValueError, AttributeError, TypeError):
            pass
        ch = Changes()
        for old in sorted(olds - {rec["root"]}):
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
