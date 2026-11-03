"""The queue in `submissions.json` (TRUSTED; pure functions on the parsed state).

Order: first a waiting port of the record to a new pin, then the entries waiting for a
confirmation duel (`confirming`), each oldest first; then, among the other queued entries, the
author whose most recent evaluation started earliest (never-evaluated authors first), then that
author's oldest queued entry. `queued` is the bot's timestamp, so a push goes to the back of its
author's line."""
import json

from common import (CONFIRMING, FINAL, MARGIN, MAX_ATTEMPTS, MAX_HEADS_PER_PR, QUEUED, RECORD_WINS, RUNNING, STATUSES,
                    WAITING, now_iso)

EVALUATED = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error")


def empty(repo, pin):
    return {"version": 1, "updated": None, "repo": repo, "core": pin, "margin": MARGIN, "record_wins": RECORD_WINS,
            "submissions": []}


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
    stale = (st.get("core"), st.get("margin"), st.get("record_wins")) != (pin, MARGIN, RECORD_WINS)
    st["core"], st["margin"], st["record_wins"] = pin, MARGIN, RECORD_WINS
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
        keep = {k: old.get(k) for k in ("started",)}
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
        if e["status"] in (RUNNING, CONFIRMING):
            return f"the same root as {e['id']} (#{e['pr']}), being evaluated"
        if e["pr"] != pr and e["status"] == QUEUED:
            return f"the same root as {e['id']}, queued in #{e['pr']}"
    return None


def order(st):
    """The waiting entries in evaluation order: waiting ports, then confirmations (each oldest
    first), then the other queued entries in the fair order."""
    last = {}
    for e in st["submissions"]:
        if e.get("started"):
            a = e["author"]
            last[a] = max(last.get(a, ""), e["started"])
    key = lambda e: (e["status"] != QUEUED, e["queued"] or "", e["id"])  # noqa: E731  (ports first)
    front = sorted((e for e in st["submissions"] if e["status"] == CONFIRMING
                    or (e["status"] == QUEUED and e.get("port_of"))), key=key)
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


def won_duels(e, record_id):
    """The duels `e` won against the record `record_id` (a confirmation counts only against the
    record the first win was against)."""
    return [d for d in e.get("duels") or [] if isinstance(d, dict) and d.get("won") and d.get("incumbent") == record_id]


def failed_duels(e, record_id):
    """The duels of `e` in which the record `record_id` failed on the runner (no comparison)."""
    return [d for d in e.get("duels") or [] if isinstance(d, dict) and d.get("incumbent_failed")
            and d.get("incumbent") == record_id]


def waiting(e, record_id):
    """The status an entry waits in: `confirming` if it won a duel against the standing record
    `record_id`, else `queued`."""
    return CONFIRMING if record_id and won_duels(e, record_id) else QUEUED


def settle(st, pin, now):
    """Wins count only against the record they were won against. When that record no longer stands
    (beaten, retired, or a pin move), a `confirming` entry goes back to `queued`, keeping its queue
    time, for a fresh duel against whatever stands next: no win carries over, and none crowns an
    entry. Returns the ids changed."""
    rec = current_record(st, pin)
    out = []
    for e in st["submissions"]:
        if e["status"] == CONFIRMING and waiting(e, rec["id"] if rec else None) == QUEUED:
            e["status"] = QUEUED
            e["reasons"] = (e.get("reasons") or [])[:19] + [
                "the record it won its duel against no longer stands: queued for a fresh evaluation"]
            out.append(e["id"])
    return out


def void_confirmations(st, record_id, now):
    """A retired record's pending confirmations: each entry `confirming` on a win against it is
    `accepted`, since a retirement must not crown a candidate on one win. Returns the ids."""
    out = []
    for e in st["submissions"]:
        if e["status"] == CONFIRMING and won_duels(e, record_id):
            _close(e, "accepted", now)
            e["reasons"] = (e.get("reasons") or [])[:19] + [
                f"the record {record_id} was retired before this entry's confirmation duel: one win is not a record"]
            out.append(e["id"])
    return out


def reap(st, now, record_id=None):
    """Entries still `running` when a new evaluation run selects (runs are serialised by the
    concurrency group, so their run ended without publishing): an organiser-side ERROR, waiting
    once more or left as `error`. Returns the ids."""
    out = []
    for e in st["submissions"]:
        if e["status"] == RUNNING:
            why = "harness error: the evaluation run ended without publishing a verdict"
            e["verdict"] = "ERROR"
            if e.get("attempts", 0) < MAX_ATTEMPTS:
                e["status"], e["reasons"] = waiting(e, record_id), [why + " (queued again)"]
            else:
                _close(e, "error", now, why)
            out.append(e["id"])
    return out


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
    history; with none standing there is no duel, and the first comparable attested ACCEPT at the pin
    is the record."""
    newest = next((e for e in records(st) if e.get("harness_commit") == pin), None)
    return newest if newest is not None and newest["status"] == "record" else None


def retire(e, now, why):
    """The record leaves the throne (it stays in the history as `retired`)."""
    e["status"], e["retired"] = "retired", now
    e["reasons"] = (e.get("reasons") or [])[:19] + [why]


COMPACT_KEYS = ("id", "pr", "sha", "root", "author", "status", "queued", "finished", "tree", "attempts", "verdict",
                "started")


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
    commit, so the old record can keep the crown at the new pin (unpaired). None if there is none
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
             verdict=None, score=None, comparable=False, truncated=False, reasons=[], cpu=[], run_url=None,
             record_of=None, verified=False, harness_commit=None, prover_sha256=None)
    st["submissions"].append(e)
    return e


def any_queued(st):
    return any(e["status"] in WAITING for e in st["submissions"])


def position(st, eid):
    ids = [e["id"] for e in order(st)]
    return (ids.index(eid) + 1, len(ids)) if eid in ids else (None, len(ids))


assert set(EVALUATED) <= set(FINAL)
