"""The queue in `submissions.json` (TRUSTED; pure functions on the parsed state).

Order (brief §4): among queued entries, the author whose most recent evaluation started earliest
(never-evaluated authors first), then that author's oldest queued entry; `queued` is the bot's
timestamp, so a push goes to the back of its author's line."""
import json

from common import FINAL, MARGIN, MAX_ATTEMPTS, MAX_HEADS_PER_PR, QUEUED, RUNNING, STATUSES, now_iso

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
    st["core"], st["margin"] = pin, MARGIN
    return st


def dump(st, clock=None):
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
    """Why a root with this tree is not queued, or None: another author's entry had the same tree
    first (a copied root; the earliest wins), or an entry with the same tree was already evaluated
    (an identical re-run, e.g. an empty commit, would only re-draw the measurement noise), or is
    queued in another pull request. An
    invalid entry, or one whose evaluation was an organiser-side error, does not count."""
    if not tree:
        return None
    for e in st["submissions"]:
        if e.get("tree") != tree or e["id"] == eid or e["status"] == "invalid":
            continue
        if e["author"] != author:
            return f"the same root as {e['id']} (#{e['pr']}, by another author), submitted earlier"
        if e["status"] in EVALUATED and e["status"] != "error":
            return f"the same root as {e['id']} (#{e['pr']}), already evaluated ({e['status']})"
        if e["pr"] != pr and e["status"] in (QUEUED, RUNNING):
            return f"the same root as {e['id']}, queued in #{e['pr']}"
    return None


def order(st):
    """The queued entries in the fair order of brief §4."""
    last = {}
    for e in st["submissions"]:
        if e.get("started"):
            a = e["author"]
            last[a] = max(last.get(a, ""), e["started"])
    queued = sorted((e for e in st["submissions"] if e["status"] == QUEUED), key=lambda e: (e["queued"], e["id"]))
    by = {}
    for e in queued:
        by.setdefault(e["author"], []).append(e)
    # authors by (never evaluated first, earliest last start, their oldest queued entry)
    authors = sorted(by, key=lambda a: (a in last, last.get(a, ""), by[a][0]["queued"], a))
    # round robin in that order: an author's second entry comes after every other author's first,
    # since starting the first makes that author the most recent
    out = []
    for k in range(max((len(v) for v in by.values()), default=0)):
        out += [by[a][k] for a in authors if len(by[a]) > k]
    return out


def reap(st, now):
    """Entries still `running` when a new evaluation run selects (runs are serialised by the
    concurrency group, so their run ended without publishing): an organiser-side ERROR, queued
    once more or left as `error`. Returns the ids."""
    out = []
    for e in st["submissions"]:
        if e["status"] == RUNNING:
            why = "harness error: the evaluation run ended without publishing a verdict"
            e["verdict"] = "ERROR"
            if e.get("attempts", 0) < MAX_ATTEMPTS:
                e["status"], e["reasons"] = QUEUED, [why + " (queued again)"]
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
    was retired (a beaten record never stands again). A record of an earlier pin stays in the
    history; with none standing there is no duel, and the first comparable attested ACCEPT at the pin
    is the record (brief §2a, review M4, M5)."""
    newest = next((e for e in records(st) if e.get("harness_commit") == pin), None)
    return newest if newest is not None and newest["status"] == "record" else None


def retire(e, now, why):
    """The record leaves the throne (it stays in the history as `retired`)."""
    e["status"], e["retired"] = "retired", now
    e["reasons"] = (e.get("reasons") or [])[:19] + [why]


COMPACT_KEYS = ("id", "pr", "sha", "root", "author", "status", "queued", "finished", "tree", "attempts", "verdict",
                "started")


def compact(st):
    """Bounds the state (review M1): an entry that never was evaluated (superseded, withdrawn,
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


def port(st, pr, pin, now):
    """The owner's re-evaluation at a new pin (after a pin move): the pull request's newest record
    (or other evaluated ACCEPT) of an earlier pin, queued again as `<id>-<pin8>` on the same retained
    commit, so the old record can keep the crown at the new pin. None if there is none."""
    olds = [e for e in of_pr(st, pr) if e["status"] in ("record", "retired", "accepted", "unranked")
            and e.get("harness_commit") != pin and e.get("tag")]
    if not olds:
        return None
    o = max(olds, key=lambda e: e.get("finished") or "")
    nid = f"{o['id'][:len('pr') + len(str(pr)) + 13]}-{pin[:8]}"
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
    return any(e["status"] == QUEUED for e in st["submissions"])


def position(st, eid):
    ids = [e["id"] for e in order(st)]
    return (ids.index(eid) + 1, len(ids)) if eid in ids else (None, len(ids))


assert set(EVALUATED) <= set(FINAL)
