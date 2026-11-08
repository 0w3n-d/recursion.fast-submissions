"""The queue in `submissions.json` (TRUSTED; pure functions on the parsed state).

Order: first a waiting port of the record to a new pin (oldest first); then, among the other
queued entries, the author whose most recent evaluation started earliest (never-evaluated authors
first), then that author's oldest queued entry. `queued` is the bot's timestamp, so a push goes to
the back of its author's line. There is no cap on an author's evaluations: the order only decides
who goes next."""
import datetime
import json

from common import (ENTRY_PROOF_ERRORS, UNCOUNTED_ERRORS, FINAL, MARGIN, MAX_ATTEMPTS, MAX_HEADS_PER_PR,
                    PAUSE_AFTER, QUEUED, RUNNING, STATUSES, STREAK_CAP, STREAK_WINDOW_S, now_iso)

EVALUATED = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error")


def empty(repo, pin):
    return {"version": 1, "updated": None, "repo": repo, "core": pin, "margin": MARGIN, "submissions": []}


def load(raw, repo, pin):
    """The state from the bytes of `submissions.json` (None: a fresh state). A state that is not
    the bot's format fails loudly rather than being silently replaced."""
    if raw is None:
        return empty(repo, pin)
    st = json.loads(raw)
    if not isinstance(st, dict) or st.get("version") != 1 or not isinstance(st.get("submissions"), list):
        raise ValueError("submissions.json is not version 1 of the bot's format")
    for e in st["submissions"]:
        if not isinstance(e, dict) or e.get("status") not in STATUSES or not isinstance(e.get("id"), str):
            raise ValueError(f"submissions.json holds a malformed entry: {str(e)[:200]}")
    # `stale`: the stored pin or parameters are not the current ones (a pin move); the next writer
    # rewrites the file even if no entry changed, so readers see the pin and its record at once
    stale = (st.get("core"), st.get("margin")) != (pin, MARGIN) or "record_wins" in st
    st.pop("record_wins", None)
    st.pop("fingerprint_errors", None)          # an older state's counter: `error_streak` replaces it
    st["core"], st["margin"] = pin, MARGIN
    st["_stale"] = stale
    return st


def dump(st, clock=None):
    st.pop("_stale", None)
    st["updated"] = now_iso(clock)
    rec = current_record(st, st.get("core"))
    st["record"] = rec["id"] if rec else None      # the standing record at the pin, for readers (the site)
    return (json.dumps(st, indent=1, ensure_ascii=False, sort_keys=False) + "\n").encode()


def find(st, eid):
    return next((e for e in st["submissions"] if e["id"] == eid), None)


def of_pr(st, pr):
    return [e for e in st["submissions"] if e["pr"] == pr]


def _close(e, status, now, reason=None):
    e["status"], e["finished"] = status, now
    if reason:
        e["reasons"] = [reason]


def withdraw(st, pr, now, reason):
    """Queued entries of the pull request become `withdrawn` (closed, draft or held before their
    evaluation). Returns the ids changed."""
    out = []
    for e in of_pr(st, pr):
        if e["status"] == QUEUED:
            _close(e, "withdrawn", now, reason)
            out.append(e["id"])
    return out


def enqueue(st, entry, now):
    """Queues `entry` (a fresh dict for the pull request's head) and supersedes the pull request's
    other queued entries. An existing id is re-queued only if it was superseded, withdrawn or
    invalid (the same commit, back in line); an id that is queued, running or evaluated is kept.
    Returns (entry in the state, changed: bool)."""
    changed = False
    for e in of_pr(st, entry["pr"]):
        if e["status"] == QUEUED and e["id"] != entry["id"]:
            _close(e, "superseded", now, "the pull request moved before this commit was evaluated")
            changed = True
    old = find(st, entry["id"])
    if old is None:
        entry.update(status=QUEUED, queued=now, started=None, finished=None, attempts=0, reasons=[])
        st["submissions"].append(entry)
        return entry, True
    if old["status"] in ("superseded", "withdrawn", "invalid"):
        keep = {k: old.get(k) for k in ("started", "counted_at", "generic_errors")}
        old.update(entry)
        old.update(status=QUEUED, queued=now, finished=None, attempts=0, reasons=[], verdict=None, **keep)
        return old, True
    return old, changed


def add_invalid(st, entry, reasons, now):
    """Records a head that failed the precheck (and supersedes the pull request's queued ones).
    Returns (entry, changed)."""
    for e in of_pr(st, entry["pr"]):
        if e["status"] == QUEUED and e["id"] != entry["id"]:
            _close(e, "superseded", now, "the pull request moved before this commit was evaluated")
    old = find(st, entry["id"])
    if old is not None and old["status"] not in ("superseded", "withdrawn", "invalid"):
        return old, False
    if old is not None and old["status"] == "invalid" and old.get("reasons") == reasons:
        return old, False
    tgt = old if old is not None else entry
    if old is not None:
        old.update(entry)
    else:
        st["submissions"].append(entry)
    tgt.update(status="invalid", queued=now, started=tgt.get("started"), finished=now, attempts=tgt.get("attempts", 0),
               reasons=reasons, verdict=None)
    return tgt, True


def duplicate_of(st, eid, pr, author, tree):
    """Why a root with this tree is not queued, or None. Another author's entry with the same tree
    came first (a copied root: the earliest wins, whatever became of it), or one of the author's
    own entries with the same tree was evaluated, is being evaluated, or is queued in another pull
    request (an identical re-run, e.g. an empty commit, would only re-draw the measurement noise).
    Invalid entries never count, nor do the author's own organiser-side errors (a retry)."""
    if not tree:
        return None
    for e in st["submissions"]:
        if e.get("tree") != tree or e["id"] == eid or e["status"] == "invalid":
            continue
        if e["author"] != author:
            return f"the same root as {e['id']} (#{e['pr']}, by another author), submitted earlier"
        if e["status"] in EVALUATED and e["status"] != "error":
            return f"the same root as {e['id']} (#{e['pr']}), already evaluated ({e['status']})"
        if e["status"] == RUNNING:
            return f"the same root as {e['id']} (#{e['pr']}), being evaluated"
        if e["pr"] != pr and e["status"] == QUEUED:
            return f"the same root as {e['id']}, queued in #{e['pr']}"
    return None


def order(st):
    """The waiting entries in evaluation order: waiting ports (oldest first), then the other queued
    entries in the fair order."""
    last = {}
    for e in st["submissions"]:
        t = counted_start(e)
        if t:
            a = e["author"]
            last[a] = max(last.get(a, ""), t)
    key = lambda e: (e["queued"] or "", e["id"])  # noqa: E731
    front = sorted((e for e in st["submissions"] if e["status"] == QUEUED and e.get("port_of")), key=key)
    queued = sorted((e for e in st["submissions"] if e["status"] == QUEUED and not e.get("port_of")), key=key)
    by = {}
    for e in queued:
        by.setdefault(e["author"], []).append(e)
    # authors by (never evaluated first, earliest last start, their oldest queued entry)
    authors = sorted(by, key=lambda a: (a in last, last.get(a, ""), by[a][0]["queued"], a))
    # round robin in that order: an author's second entry comes after every other author's first,
    # since starting the first makes that author the most recent
    out = front
    for k in range(max((len(v) for v in by.values()), default=0)):
        out += [by[a][k] for a in authors if len(by[a]) > k]
    return out


def _ts(iso):
    return datetime.datetime.strptime(iso, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=datetime.timezone.utc).timestamp()


def counted_start(e):
    """When an entry's evaluation counts as started, for the fair order (AGENTS.md §9):
    `counted_at`, the start of its first run that counted (a retry never refreshes it), or the start
    of the run in progress. A run does not count when it ended in a named organiser error
    (`UNCOUNTED_ERRORS`: fingerprint, lengths, drift, setup, cache, attestation), nor the first
    unnamed ERROR of an entry (a catch-all harness error or a reaped run); a later one does
    (`settle_run`). Ports (the organiser's), superseded and withdrawn entries never count."""
    if e.get("port_of") or e.get("status") in ("superseded", "withdrawn", "invalid"):
        return None
    if e.get("status") == RUNNING:
        return e.get("counted_at") or e.get("started")
    if "counted_at" in e:
        return e["counted_at"]
    # an entry written before `counted_at` existed: its start unless its last run was an ERROR
    return e.get("started") if e.get("started") and e.get("verdict") != "ERROR" else None


def settle_run(e, organiser_error=None, error=False):
    """Whether the run that just ended counts as the author's start in the fair order, recorded in
    `counted_at`: not after a named organiser error, not after the entry's first unnamed ERROR
    (`generic_errors`), otherwise yes (from the run's start, once)."""
    if organiser_error in UNCOUNTED_ERRORS:
        counts = False
    elif error:
        e["generic_errors"] = e.get("generic_errors", 0) + 1
        counts = e["generic_errors"] > 1
    else:
        counts = True
    if counts and not e.get("counted_at"):
        e["counted_at"] = e.get("started")
    e.setdefault("counted_at", None)
    return counts


def _noted(x):
    """When a streak entry was noted (its `at`), or None if it has no readable time."""
    try:
        return _ts(x["at"])
    except (KeyError, TypeError, ValueError):
        return None


def pause_count(streak):
    """The errors of the streak that count toward a pause (common.py): every ENTRY_PROOF one, and of
    the others one per author; an error noted more than STREAK_WINDOW_S before the newest one does
    not count (one with no readable time does)."""
    times = [t for t in map(_noted, streak) if t is not None]
    newest = max(times, default=None)
    n, seen = 0, set()
    for x in streak:
        t = _noted(x)
        if newest is not None and t is not None and newest - t > STREAK_WINDOW_S:
            continue
        if x.get("kind") in ENTRY_PROOF_ERRORS:
            n += 1
        elif x.get("author") not in seen:
            seen.add(x.get("author"))
            n += 1
    return n


def note_error(st, e, kind, now, reason, run_url):
    """Adds a run of `e` that ended on the organiser's side (`kind`: a named organiser error,
    `unnamed` or `reaped`) to the error streak, and pauses the queue when `pause_count` reaches
    PAUSE_AFTER. Returns True if this run paused it (an already paused queue stays paused)."""
    s = st.setdefault("error_streak", [])
    s.append({"id": e["id"], "author": e.get("author"), "kind": kind, "at": now, "reason": str(reason or kind)[:300]})
    del s[:-STREAK_CAP]
    if st.get("paused") or pause_count(s) < PAUSE_AFTER:
        return False
    st["paused"] = {"since": now, "reason": str(reason or kind)[:300], "run_url": run_url}
    return True


def clear_errors(st):
    """A clean verdict: the error streak is empty and the queue is not paused. Returns True if it
    was paused."""
    st["error_streak"] = []
    return st.pop("paused", None) is not None


def reap(st, now):
    """Entries still `running` when a new evaluation run selects (runs are serialised by the
    concurrency group, so their run ended without publishing): an organiser-side ERROR, waiting
    once more or left as `error`, and a `reaped` run in the error streak. Returns (the ids, whether
    the queue paused)."""
    out, paused = [], False
    for e in st["submissions"]:
        if e["status"] == RUNNING:
            why = "harness error: the evaluation run ended without publishing a verdict"
            e["verdict"] = "ERROR"
            settle_run(e, error=True)             # a reaped run: not counted the first time, then it counts
            paused = note_error(st, e, "reaped", now, why, e.get("run_url")) or paused
            if e.get("attempts", 0) < MAX_ATTEMPTS:
                e["status"], e["reasons"] = QUEUED, [why + " (queued again)"]
            else:
                _close(e, "error", now, why)
            out.append(e["id"])
    return out, paused


def mark_running(e, now, run_url):
    e.update(status=RUNNING, started=now, finished=None, run_url=run_url)
    e["attempts"] = e.get("attempts", 0) + 1


def records(st):
    """Every record ever taken (status `record` or `retired`), newest first."""
    rs = [e for e in st["submissions"] if e["status"] in ("record", "retired")]
    return sorted(rs, key=lambda e: (e.get("finished") or "", e["id"]), reverse=True)


def current_record(st, pin):
    """The standing record: the newest record taken at this pin (`harness_commit == pin`), unless it
    was retired (a retired record never stands again). A record of an earlier pin stays in the
    history; with none standing, the first comparable attested ACCEPT at the pin is the record."""
    newest = next((e for e in records(st) if e.get("harness_commit") == pin), None)
    return newest if newest is not None and newest["status"] == "record" else None


def retire(e, now, why):
    """The record leaves the throne (it stays in the history as `retired`)."""
    e["status"], e["retired"] = "retired", now
    e["reasons"] = (e.get("reasons") or [])[:19] + [why]


COMPACT_KEYS = ("id", "pr", "sha", "root", "author", "status", "queued", "finished", "tree", "attempts", "verdict",
                "started", "counted_at")


def compact(st):
    """Bounds the state against a flood of pushes: an entry that never was evaluated (superseded, withdrawn,
    invalid) and is not its pull request's newest entry keeps only `COMPACT_KEYS` (the tree for the
    duplicate rule, `started` for fairness); a pull request keeps at most `MAX_HEADS_PER_PR` such
    entries (the oldest are dropped). Evaluated entries are kept whole. Returns the paths of copied
    NOTES/README files that are no longer referenced."""
    newest, drop_files, keep = {}, [], []
    for e in st["submissions"]:
        if e["pr"] not in newest or (e.get("queued") or "") >= (newest[e["pr"]].get("queued") or ""):
            newest[e["pr"]] = e
    per_pr = {}
    for e in sorted(st["submissions"], key=lambda e: (e.get("queued") or "", e["id"]), reverse=True):
        if e["status"] in ("superseded", "withdrawn", "invalid") and e is not newest[e["pr"]]:
            per_pr[e["pr"]] = per_pr.get(e["pr"], 0) + 1
            drop_files += [e[k] for k in ("notes", "readme") if e.get(k)]
            if per_pr[e["pr"]] > MAX_HEADS_PER_PR:
                continue
            for k in list(e):
                if k not in COMPACT_KEYS:
                    del e[k]
        keep.append(e)
    keep_ids = {id(e) for e in keep}
    st["submissions"] = [e for e in st["submissions"] if id(e) in keep_ids]
    return drop_files


def port_id(o, pin):
    """`pr<N>-<sha12>-<pin8>`: the entry `o` re-evaluated at the pin `pin`."""
    return f"{o['id'][:len('pr') + len(str(o['pr'])) + 13]}-{pin[:8]}"


def due_port(st, pin):
    """The record to port to this pin first, or None: when no record stands at the pin, the newest
    record of all is of an earlier pin and was not retired, and it has not been ported here yet
    (a port evaluated once, whatever its verdict, is not repeated)."""
    if current_record(st, pin) is not None:
        return None
    rs = records(st)
    o = rs[0] if rs else None
    if o is None or o["status"] != "record" or o.get("harness_commit") == pin or not o.get("tag"):
        return None
    return o if find(st, port_id(o, pin)) is None else None


def port(st, pr, pin, now, o=None):
    """A re-evaluation at a new pin: the record `o` (by default the pull request's newest record or
    other evaluated ACCEPT of an earlier pin), queued again as `<id>-<pin8>` on the same retained
    commit, so the old record can keep the crown at the new pin. None if there is none
    or it exists."""
    if o is None:
        olds = [e for e in of_pr(st, pr) if e["status"] in ("record", "retired", "accepted", "unranked")
                and e.get("harness_commit") != pin and e.get("tag")]
        if not olds:
            return None
        o = max(olds, key=lambda e: e.get("finished") or "")
    nid = port_id(o, pin)
    if find(st, nid) is not None:
        return None
    keep = ("pr", "sha", "root", "author", "title", "agent", "builds_on", "opened", "tag", "notes", "readme", "tree")
    e = {k: o.get(k) for k in keep}
    e.update(id=nid, port_of=o["id"], status=QUEUED, queued=now, started=None, finished=None, attempts=0,
             verdict=None, score=None, comparable=False, truncated=False, reasons=[], run_url=None,
             record_of=None, verified=False, harness_commit=None, prover_sha256=None)
    st["submissions"].append(e)
    return e


def any_queued(st):
    return any(e["status"] == QUEUED for e in st["submissions"])


def position(st, eid):
    ids = [e["id"] for e in order(st)]
    return (ids.index(eid) + 1, len(ids)) if eid in ids else (None, len(ids))


assert set(EVALUATED) <= set(FINAL)
