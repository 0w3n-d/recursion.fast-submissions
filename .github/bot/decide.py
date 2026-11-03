"""The status of an evaluated entry and the record rule (TRUSTED; pure).

A result can become the record only if its verdict is ACCEPT, it is comparable, its attestation
verifies (the core's signer workflow at the pin, on a GitHub-hosted runner, bound to this run), the
core's `harness/verify-record.sh` accepts it, and `harness_commit` is the pin. Then (brief §2a):

- with no record, it is the record (the only unpaired path);
- with a record, the evaluation was a duel (the record re-run in the same benchmark job, same
  drawn chain lengths), and `duel` decides: the candidate is the record iff
  `S_cand <= (1 - margin) * S_inc` (margin 0.03), or the incumbent failed for an entry reason on
  that runner; an incumbent that failed for the organiser's reason is an ERROR. A result with no
  incumbent measurement never takes a record from a standing one.

A prover binary that an earlier record already had never takes the record (a resubmitted copy)."""
from common import MARGIN, MAX_ATTEMPTS, SHA_RE, VERDICTS, clean, clean_reasons, is_num


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


def duel(inc, S, record, margin=MARGIN):
    """(status, reason, duel record) of a comparable, attested ACCEPT with score `S` against the
    standing `record`, from the result's incumbent measurement (the interface assumed of the core
    until its duel exists: `incumbent: {verdict, comparable, score: {S, ...}, entry_failed}`).
    status is `record`, `accepted` or `error` (the organiser's: queued again once)."""
    rid = record["id"]
    if not isinstance(inc, dict):
        return "accepted", (f"no head-to-head run with the record {rid} in this evaluation: "
                            "an unpaired score never takes a standing record"), None
    if inc.get("entry_failed") is True:
        return "record", f"the record {rid} failed for an entry reason on this runner", \
            {"incumbent": rid, "S_inc": None, "gain": None, "incumbent_failed": True}
    s_inc = (inc.get("score") or {}).get("S") if isinstance(inc.get("score"), dict) else None
    if inc.get("verdict") != "ACCEPT" or inc.get("comparable") is not True or not is_num(s_inc) or s_inc <= 0:
        return "error", (f"harness error: the record {rid}'s run in the duel gave no comparable score "
                         f"(verdict {clean(inc.get('verdict'), 20)}) and no entry failure"), None
    d = {"incumbent": rid, "S_inc": s_inc, "gain": 1 - S / s_inc, "incumbent_failed": False}
    if S <= (1 - margin) * s_inc:
        return "record", f"S = {S:.4f} beats the record {rid} (S = {s_inc:.4f} in the same job) by {d['gain']:.1%}", d
    return "accepted", (f"S = {S:.4f} against the record {rid}'s S = {s_inc:.4f} in the same job "
                        f"({d['gain']:+.1%}; a record needs {margin:.0%})"), d


def decide(result, verification, pin, record, attempts, record_provers=(), margin=MARGIN):
    """The fields an evaluation sets on its entry, and `requeue` (an ERROR with attempts left).

    result: the parsed result.json or None; verification: {"attested": bool, "record_ok": bool,
    "reason": str}; record: the current record's entry or None; attempts: this entry's evaluations
    so far, this one included; record_provers: {prover_sha256: id} of every record so far."""
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
           "record_of": None, "duel": None, "requeue": False}
    reasons = clean_reasons(result.get("reasons"))
    extra = []
    if not out["verified"]:
        extra.append("attestation not verified: " + clean(verification.get("reason") or "no attestation", 240))

    def error(why=None):
        if why:
            extra.append(why)
        if attempts < MAX_ATTEMPTS:
            out["requeue"] = True
            extra.append(f"organiser-side ERROR; queued again (attempt {attempts} of {MAX_ATTEMPTS})")
            return "queued"
        return "error"

    if verdict == "ERROR":
        status = error()
    elif verdict == "REJECT":
        status = "rejected"
    elif verdict == "PROVISIONAL":
        status = "provisional"
    elif not out["verified"] or not verification.get("record_ok"):
        status = error(None if not out["verified"] else
                       "harness/verify-record.sh refused the ACCEPT: " + clean(verification.get("reason"), 240))
    elif hc != pin:
        status = error(f"the result's harness_commit {hc} is not the pin {pin}")
    elif not out["comparable"]:
        status = "unranked"
        extra.append("ACCEPT, not comparable (" + ("truncated stream" if out["truncated"] else "mixed CPU models or plan")
                     + "): not ranked")
    elif not is_num(S) or S <= 0:
        status = "unranked"
        extra.append("ACCEPT without a positive score S: not ranked")
    elif isinstance(result.get("prover_sha256"), str) and result["prover_sha256"] in record_provers:
        status = "accepted"
        extra.append(f"the same prover binary as the record {record_provers[result['prover_sha256']]}: never a new record")
    elif record is None:
        status = "record"
    else:
        status, why, out["duel"] = duel(result.get("incumbent"), S, record, margin)
        if status == "record":
            out["record_of"] = record["id"]
        elif status == "error":
            status = error()
        extra.append(why)
    out["status"] = status
    out["reasons"] = reasons[:max(0, 20 - len(extra))] + extra[:20]
    return out


def cache_retry(result, entry):
    """True if a REJECT or ERROR used the record build cache (`record_cache.reused` non-empty) and
    this entry was not yet evaluated without it: it is queued once more with `record_cache: false`,
    so a sabotaged cache cannot fail a candidate (S5)."""
    if not isinstance(result, dict) or result.get("verdict") not in ("REJECT", "ERROR"):
        return False
    rc = result.get("record_cache")
    return isinstance(rc, dict) and bool(rc.get("reused")) and entry.get("record_cache") is not False


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
