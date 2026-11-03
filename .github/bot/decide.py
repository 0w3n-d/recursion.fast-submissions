"""The status of an evaluated entry and the record rule (TRUSTED; pure).

A result can become the record only if its verdict is ACCEPT, it is comparable, its attestation
verifies (the core's signer workflow at the pin, on a GitHub-hosted runner, bound to this run), the
core's `harness/verify-record.sh` accepts it, and `harness_commit` is the pin. Then:

- with no record, it is the record (the only unpaired path, needing no confirmation);
- with a standing record (the newest record at this pin), the evaluation was a duel (the record
  re-run in the same benchmark job, same drawn chain lengths), and `duel` decides: the candidate
  wins iff `S_cand <= (1 - MARGIN) * S_inc`. One win is not enough, since the runner's noise can
  give it to a copy: a candidate with fewer than `RECORD_WINS` wins against this record is
  `confirming` (one more duel of the same commit, first in the queue); with `RECORD_WINS` wins it
  is the record, and a lost confirmation makes it `accepted`. If the record fails on that runner
  (`entry_failed`), there is no comparison: no crown, the candidate is evaluated once more, and a
  record that fails in two duels is retired. An organiser-side failure is an ERROR.

A prover binary that an earlier record already had never takes the record (a resubmitted copy)."""
from common import CONFIRMING, MARGIN, MAX_ATTEMPTS, RECORD_WINS, SHA_RE, VERDICTS, clean, clean_reasons, is_num


def clean_value(v, depth=0):
    if is_num(v) or isinstance(v, bool) or v is None:
        return v
    if isinstance(v, str):
        return clean(v, 200)
    if depth >= 3:
        return None
    if isinstance(v, list):
        return [clean_value(x, depth + 1) for x in v[:16]]
    if isinstance(v, dict):
        return {clean(k, 40): clean_value(x, depth + 1) for k, x in list(v.items())[:48]}
    return None


DUEL_RETRIES = 1        # a candidate whose duel the record failed is evaluated once more (per record)
RECORD_FAILURES = 2     # a record whose own run fails in this many duels in a row is retired
CONFIRM_RETRIES = 1     # a confirmation whose result is not comparable is run once more


def duel(result, S, record, margin=MARGIN):
    """(outcome, reason, duel record) of a comparable, attested ACCEPT with score `S` against the
    standing `record`, from the core's duel fields (`harness/aggregate.py pair()`): `duel: true` and
    `incumbent: {sha, path, certificate_status, verdict, comparable, truncated, score: {S, ...},
    entry_failed, reasons}`. outcome is `won`, `accepted`, `incumbent_failed` (the record failed on
    this runner: never a crown) or `error` (the organiser's)."""
    rid = record["id"]
    inc = result.get("incumbent")
    if result.get("duel") is not True or not isinstance(inc, dict):
        return "error", f"harness error: no duel with the record {rid} in this evaluation", None
    if inc.get("sha") != record["sha"] or inc.get("path") != f"submissions/{record['root']}":
        return "error", (f"harness error: the duel measured {clean(inc.get('sha'), 40)}:{clean(inc.get('path'), 60)}, "
                         f"not the record {rid}"), None
    why = "; ".join(clean(r, 120) for r in (inc.get("reasons") or [])[:3] if isinstance(inc.get("reasons"), list))
    if inc.get("certificate_status") != "ok":
        return "error", (f"harness error: the record {rid}'s certificate is {clean(inc.get('certificate_status'), 20)} "
                         f"in the duel" + (f" ({why})" if why else "")), None
    if inc.get("entry_failed") is True:
        return "incumbent_failed", (f"the record {rid} failed on this runner ({clean(inc.get('verdict'), 20)}"
                                    + (", truncated" if inc.get("truncated") else "") + (f": {why}" if why else "")
                                    + "): no comparison"), {"incumbent": rid, "S": S, "S_inc": None, "gain": None,
                                                            "incumbent_failed": True, "won": False}
    sc = inc.get("score") if isinstance(inc.get("score"), dict) else {}
    s_inc = sc.get("S")
    if inc.get("verdict") != "ACCEPT" or inc.get("comparable") is not True or not is_num(s_inc) or s_inc <= 0:
        return "error", (f"harness error: the record {rid}'s run in the duel gave no comparable score "
                         f"(verdict {clean(inc.get('verdict'), 20)}) and no entry failure"), None
    d = {"incumbent": rid, "S": S, "S_inc": s_inc, "gain": 1 - S / s_inc, "incumbent_failed": False}
    d["won"] = S <= (1 - margin) * s_inc
    if d["won"]:
        return "won", f"S = {S:.4f} beats the record {rid} (S = {s_inc:.4f} in the same job) by {d['gain']:.1%}", d
    return "accepted", (f"S = {S:.4f} against the record {rid}'s S = {s_inc:.4f} in the same job "
                        f"({d['gain']:+.1%}; a win needs {margin:.0%})"), d


def decide(result, verification, pin, record, attempts, record_provers=(), margin=MARGIN, duel_retries=0,
           record_failures=0, wins=(), record_wins=RECORD_WINS, confirm_retries=0):
    """The fields an evaluation sets on its entry, with `requeue` (evaluate it once more) and
    `retire_record` / `record_failed` (what happens to the standing record).

    result: the parsed result.json or None; verification: {"attested": bool, "record_ok": bool,
    "reason": str}; record: the standing record's entry (at this pin) or None; attempts: this entry's
    evaluations so far in this round, this one included; record_provers: {prover_sha256: id} of
    every record (but this commit's own); duel_retries: the candidate's duels against `record` that
    the record failed; record_failures: the record's consecutive duel failures so far; wins: the
    duels this entry already won against `record`; confirm_retries: its confirmations already
    re-run for a non-comparable result. `status` is `confirming` (not `queued`) when the entry
    waits with a win."""
    if not isinstance(result, dict):
        result = {"verdict": "ERROR", "reasons": ["harness error: the evaluation produced no readable result "
                                                  "(no `result` artifact: a job failed before the attest job)"]}
    verdict = result.get("verdict") if result.get("verdict") in VERDICTS else "ERROR"
    score = clean_value(result.get("score")) if isinstance(result.get("score"), dict) else None
    S = (score or {}).get("S")
    hc = result.get("harness_commit") if isinstance(result.get("harness_commit"), str) and SHA_RE.match(result["harness_commit"]) else None
    out = {"verdict": verdict, "score": score, "comparable": result.get("comparable") is True,
           "truncated": result.get("truncated") is True,
           "cpu": [clean(m, 100) for m in (result.get("cpu_models") or [])[:4]] if isinstance(result.get("cpu_models"), list) else [],
           "harness_commit": hc, "verified": bool(verification.get("attested")),
           "record_of": None, "duel": None, "duel_now": None, "requeue": False, "confirm_retry": False, "duel_retry": False, "record_failed": False,
           "retire_record": False}
    reasons = clean_reasons(result.get("reasons"))
    extra = []

    def error(why=None):
        if why:
            extra.append(why)
        if attempts < MAX_ATTEMPTS:
            out["requeue"] = True
            extra.append(f"organiser-side ERROR; queued again (attempt {attempts} of {MAX_ATTEMPTS})")
            return "queued"
        return "error"

    if not out["verified"]:
        # any result whose provenance fails is the organiser's problem, whatever it says
        status = error("attestation not verified: " + clean(verification.get("reason") or "no attestation", 240))
    elif verdict == "ERROR":
        status = error()
    elif verdict == "REJECT":
        status = "rejected"
    elif verdict == "PROVISIONAL":
        status = "provisional"
    elif hc != pin:
        status = error(f"the result's harness_commit {hc} is not the pin {pin}")
    elif not out["comparable"] and wins and record is not None and confirm_retries < CONFIRM_RETRIES:
        # a confirmation the runner made incomparable is not a lost duel: run it once more
        status, out["requeue"], out["confirm_retry"] = CONFIRMING, True, True
        extra.append("ACCEPT, not comparable (" + ("truncated stream" if out["truncated"] else "mixed CPU models or plan")
                     + ") in the confirmation duel: queued once more for it")
    elif not out["comparable"]:
        status = "unranked"
        extra.append("ACCEPT, not comparable (" + ("truncated stream" if out["truncated"] else "mixed CPU models or plan")
                     + "): not ranked")
    elif not verification.get("record_ok"):
        status = error("harness/verify-record.sh refused the ACCEPT: " + clean(verification.get("reason"), 240))
    elif not is_num(S) or S <= 0:
        status = "unranked"
        extra.append("ACCEPT without a positive score S: not ranked")
    elif isinstance(result.get("prover_sha256"), str) and result["prover_sha256"] in record_provers:
        status = "accepted"
        extra.append(f"the same prover binary as the record {record_provers[result['prover_sha256']]}: never a new record")
    elif record is None:
        status = "record"
    else:
        outcome, why, out["duel"] = duel(result, S, record, margin)
        out["duel_now"] = out["duel"]
        extra.append(why)
        won = list(wins) + ([out["duel"]] if outcome == "won" else [])
        if outcome == "won" and len(won) >= record_wins:
            status, out["record_of"] = "record", record["id"]
            out["duel"] = min(won, key=lambda d: d["gain"])       # the gain it is credited with: the smallest
            if len(won) > 1:
                extra.append(f"{len(won)} duels won against the record {record['id']}: the new record")
        elif outcome == "won":
            status = CONFIRMING
            extra.append(f"duel {len(won)} of {record_wins} won: one more duel of this commit against the record "
                         f"{record['id']} runs next, first in the queue")
        elif outcome == "error":
            status = error()
        elif outcome == "incumbent_failed":
            out["record_failed"] = True
            status = "accepted"
            if record_failures + 1 >= RECORD_FAILURES and wins:
                # a retirement never crowns a candidate on one win: its confirmation is void
                out["retire_record"] = True
                extra.append(f"the record {record['id']} failed in {record_failures + 1} duels in a row and is "
                             "retired during this confirmation: one win is not a record")
                status = "accepted"
            elif record_failures + 1 >= RECORD_FAILURES:
                out["retire_record"] = True
                out["requeue"] = out["duel_retry"] = True
                extra.append(f"the record {record['id']} failed in {record_failures + 1} duels in a row and is retired; "
                             "this entry is evaluated once more with no standing record")
                status = "queued"
            elif duel_retries < DUEL_RETRIES:
                out["requeue"] = out["duel_retry"] = True
                extra.append("queued once more for another duel")
                status = "queued"
        else:
            status = "accepted"
            if wins:
                extra.append("the confirmation duel was lost: not the record")
    if status == "queued" and wins and not out["retire_record"]:
        status = CONFIRMING                    # a retry keeps the win and its place at the front
    out["status"] = status
    out["reasons"] = reasons[:max(0, 20 - len(extra))] + extra[:20]
    return out


def cache_retry(result, entry):
    """True if a REJECT used the record build cache (its certificate, or the incumbent's, restored
    modules from it) and this entry was not yet evaluated without it: it is queued once more with
    `record_cache: false`, so a sabotaged cache cannot fail a candidate. An ERROR's retry runs
    without the cache anyway (flows.publish)."""
    if not isinstance(result, dict) or result.get("verdict") != "REJECT" or entry.get("record_cache") is False:
        return False

    def restored(r):
        c = (r or {}).get("certificate") if isinstance(r, dict) else None
        rc = (c or {}).get("record_cache") if isinstance(c, dict) else None
        return isinstance(rc, dict) and bool(rc.get("restored"))
    legacy = result.get("record_cache")
    return restored(result) or restored(result.get("incumbent")) or (isinstance(legacy, dict) and bool(legacy.get("reused")))


def build_manifest_sha(result):
    """The attested sha256 of the entry build's manifest.json (certificate.entry_build first, then a
    top-level entry_build), or None."""
    if not isinstance(result, dict):
        return None
    for holder in (result.get("certificate"), result):
        eb = holder.get("entry_build") if isinstance(holder, dict) else None
        h = eb.get("manifest_sha256") if isinstance(eb, dict) else None
        if isinstance(h, str) and len(h) == 64 and all(c in "0123456789abcdef" for c in h):
            return h
    return None
