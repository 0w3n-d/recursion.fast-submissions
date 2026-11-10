"""The queue in `submissions.json` (TRUSTED; pure functions on the parsed state).

Order: first a waiting port of the record to a new pin (oldest first); then, among the other
queued entries, the author whose most recent evaluation started earliest (never-evaluated authors
first), then that author's oldest queued entry. `queued` is the bot's timestamp, so a push goes to
the back of its author's line. There is no cap on an author's evaluations: the order only decides
who goes next."""
import datetime
import json

from common import (ENTRY_PROOF_ERRORS, UNCOUNTED_ERRORS, FINAL, MARGIN, MAX_ATTEMPTS, MAX_HEADS_PER_PR,
                    PAUSE_AFTER, QUEUED, RUNNING, STATUSES, STREAK_CAP, STREAK_WINDOW_S, TRACK_RE, TRACKS, now_iso)

EVALUATED = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error")


VERSION = 2


def empty(repo, pin):
    return {"version": VERSION, "updated": None, "repo": repo, "core": pin, "margin": MARGIN, "submissions": []}


def migrate_v1(st):
    """Version 1 (one record, the sum's) as version 2, once: a record or retired entry took the sum's
    record (`record_in`), retired in it if `retired`; `record_of` and `against` become per track."""
    for e in st["submissions"]:
        if e.get("status") in ("record", "retired"):
            e["record_in"] = ["sum"]
            if e["status"] == "retired":
                e["retired_in"] = {"sum": e.get("retired") or e.get("finished")}
        if "record_of" in e and not isinstance(e["record_of"], dict):
            e["record_of"] = {"sum": e["record_of"] if isinstance(e["record_of"], str) else None}
        if "against" in e:
            e["against"] = {"sum": e["against"] if isinstance(e["against"], dict) else None}
    st["version"] = VERSION
    return st


def load(raw, repo, pin):
    """The state from the bytes of `submissions.json` (None: a fresh state). A state that is not
    the bot's format fails loudly rather than being silently replaced. Version 1 (one record, no tracks)
    is migrated once (`migrate_v1`) and rewritten by the next writer."""
    if raw is None:
        return empty(repo, pin)
    st = json.loads(raw)
    if not isinstance(st, dict) or st.get("version") not in (1, VERSION) or not isinstance(st.get("submissions"), list):
        raise ValueError(f"submissions.json is not version {VERSION} (or 1) of the bot's format")
    for e in st["submissions"]:
        if not isinstance(e, dict) or e.get("status") not in STATUSES or not isinstance(e.get("id"), str):
            raise ValueError(f"submissions.json holds a malformed entry: {str(e)[:200]}")
    old = st["version"] == 1
    if old:
        migrate_v1(st)
    # `stale`: the stored pin, parameters or format are not the current ones (a pin move); the next
    # writer rewrites the file even if no entry changed, so readers see the pin and its records at once
    stale = (st.get("core"), st.get("margin")) != (pin, MARGIN) or "record_wins" in st or old
    st.pop("record_wins", None)
    st.pop("fingerprint_errors", None)          # an older state's counter: `error_streak` replaces it
    st["core"], st["margin"] = pin, MARGIN
    st["_stale"] = stale
    return st


def dump(st, clock=None):
    st.pop("_stale", None)
    st["updated"] = now_iso(clock)
    # the standing record of each track at the pin, for readers (the site)
    st["record"] = {t: (r["id"] if r else None) for t, r in standing(st, st.get("core")).items()}
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


def tracks(st):
    """The tracks of the state: TRACKS, then any other track an entry took a record in."""
    extra = {t for e in st["submissions"] for t in e.get("record_in") or [] if isinstance(t, str) and TRACK_RE.match(t)}
    return list(TRACKS) + sorted(extra - set(TRACKS))


def records(st, track=None):
    """Every record ever taken in `track` (None: in any track), newest first: an entry with status
    `record` or `retired` whose `record_in` names the track."""
    rs = [e for e in st["submissions"] if e["status"] in ("record", "retired")
          and (e.get("record_in") if track is None else track in (e.get("record_in") or []))]
    return sorted(rs, key=lambda e: (e.get("finished") or "", e["id"]), reverse=True)


def current_record(st, pin, track):
    """The standing record of `track`: the newest record of the track taken at this pin
    (`harness_commit == pin`), unless it was retired in that track (a retired record never stands
    again). A record of an earlier pin stays in the history; with none standing, the first
    comparable attested ACCEPT at the pin is the track's record."""
    newest = next((e for e in records(st, track) if e.get("harness_commit") == pin), None)
    return newest if newest is not None and not retired_in(newest, track) else None


def retired_in(e, track):
    """Whether the record `e` was retired in `track` (status `retired`: in every track it took)."""
    return e["status"] == "retired" or track in (e.get("retired_in") or {})


def standing(st, pin):
    """{track: its standing record at the pin, or None} for every track of the state."""
    return {t: current_record(st, pin, t) for t in tracks(st)}


def retire(e, track, now, why):
    """The record leaves the throne of `track` (it stays in that track's history); once it is
    retired in every track it took, its status is `retired`. Returns False if it is not a record of
    that track, or already retired in it."""
    if e["status"] != "record" or track not in (e.get("record_in") or []) or retired_in(e, track):
        return False
    e.setdefault("retired_in", {})[track] = now
    e["reasons"] = (e.get("reasons") or [])[:19] + [f"{why} ({track})"]
    if all(t in e["retired_in"] for t in e["record_in"]):
        e["status"], e["retired"] = "retired", now
    return True


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


def due_ports(st, pin):
    """{track: the record to port to this pin}, for each track with no record standing at the pin
    whose newest record is of an earlier pin, was not retired in that track, and has not been ported
    here yet (a port evaluated once, whatever its verdict, is not repeated)."""
    out = {}
    for t, cur in standing(st, pin).items():
        rs = records(st, t)
        o = rs[0] if rs else None
        if cur is not None or o is None or retired_in(o, t) or o.get("harness_commit") == pin \
                or not o.get("tag") or find(st, port_id(o, pin)) is not None:
            continue
        out[t] = o
    return out


def due_port(st, pin):
    """The record to port to this pin first (the first track's, in `tracks` order), or None. One
    port serves every track whose record is that entry."""
    return next(iter(due_ports(st, pin).values()), None)


def port(st, pr, pin, now, o=None):
    """A re-evaluation at a new pin: the record `o` (by default the pull request's newest record or
    other evaluated ACCEPT of an earlier pin), queued again as `<id>-<pin8>` on the same retained
    commit, so the old record can keep its crowns at the new pin. A due port (`due_ports`) is a
    candidate only in the tracks whose record it carries (`port_tracks`), so that two tracks'
    records of different entries are each kept by their own port whatever the order the ports run
    in; the owner's re-evaluation of another entry is a candidate in every track. None if there is
    none or it exists."""
    if o is None:
        olds = [e for e in of_pr(st, pr) if e["status"] in ("record", "retired", "accepted", "unranked")
                and e.get("harness_commit") != pin and e.get("tag")]
        if not olds:
            return None
        o = max(olds, key=lambda e: e.get("finished") or "")
    nid = port_id(o, pin)
    if find(st, nid) is not None:
        return None
    carried = [t for t, x in due_ports(st, pin).items() if x["id"] == o["id"]]
    keep = ("pr", "sha", "root", "author", "title", "agent", "builds_on", "opened", "tag", "notes", "readme", "tree")
    e = {k: o.get(k) for k in keep}
    e.update(id=nid, port_of=o["id"], port_tracks=carried or None, status=QUEUED, queued=now, started=None,
             finished=None, attempts=0, verdict=None, score=None, comparable=False, truncated=False, reasons=[],
             run_url=None, record_of=None, record_in=[], against=None, verified=False, harness_commit=None,
             prover_sha256=None)
    st["submissions"].append(e)
    return e


def any_queued(st):
    return any(e["status"] == QUEUED for e in st["submissions"])


def position(st, eid):
    ids = [e["id"] for e in order(st)]
    return (ids.index(eid) + 1, len(ids)) if eid in ids else (None, len(ids))


assert set(EVALUATED) <= set(FINAL)
