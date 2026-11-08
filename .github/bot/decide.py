"""The status of an evaluated entry and the record rule (TRUSTED; pure).

A result can become the record only if its verdict is ACCEPT, it is comparable (the stream not
truncated; a run off the season's machine is the core's ERROR, never an ACCEPT), its attestation verifies (the core's signer workflow
at the pin, on the organiser's self-hosted runner, bound to this run), the core's
`harness/verify-record.sh` accepts it, and `harness_commit` is the pin. Then (AGENTS.md §10):

- with no record standing at the pin, it is the record;
- with a standing record, it is the record iff `S < (1 - MARGIN) * S_record`, `S_record` the
  record's own score at the pin (both measured on the same machine, as comparability requires).

A prover binary that an earlier record already had never takes the record (a resubmitted copy)."""
from common import MARGIN, MAX_ATTEMPTS, ORGANISER_ERRORS, PAUSING_ERRORS, SHA_RE, VERDICTS, clean, clean_reasons, is_num


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


def against(S, record, margin=MARGIN):
    """(beats, reason, comparison) of a comparable, attested ACCEPT with score `S` against the
    standing `record` (AGENTS.md §10): beats iff `S < (1 - margin) * S_record`."""
    rid, s_rec = record["id"], (record.get("score") or {}).get("S")
    if not is_num(s_rec) or s_rec <= 0:
        return False, f"the record {rid} has no positive score: no comparison", None
    d = {"record": rid, "S": S, "S_record": s_rec, "gain": 1 - S / s_rec, "beats": S < (1 - margin) * s_rec}
    if d["beats"]:
        return True, f"S = {S:.4f} beats the record {rid} (S = {s_rec:.4f}) by {d['gain']:.1%}", d
    return False, (f"S = {S:.4f} against the record {rid}'s S = {s_rec:.4f} ({d['gain']:+.1%}; a record needs "
                   f"more than {margin:.0%})"), d


def decide(result, verification, pin, record, attempts, record_provers=(), margin=MARGIN):
    """The fields an evaluation sets on its entry, with `requeue` (evaluate it once more) and
    `organiser_side` (the run ended on the organiser's side, not in a clean verdict) and
    `benchmarked` (the result records a stream on the season's machine: the run got past every
    benchmark-side check, so its clean verdict shows the machine and the harness work).

    result: the parsed result.json or None; verification: {"attested": bool, "record_ok": bool,
    "reason": str}; record: the standing record's entry (at this pin) or None; attempts: this entry's
    evaluations so far in this round, this one included; record_provers: {prover_sha256: id} of
    every record (but this commit's own)."""
    benchmarked = (isinstance(result, dict) and isinstance(result.get("stream"), dict)
                   and isinstance(result.get("machine"), dict) and result["machine"].get("matches") is True)
    if not isinstance(result, dict):
        result = {"verdict": "ERROR", "reasons": ["harness error: the evaluation produced no readable result "
                                                  "(no `result` artifact: a job failed before the attest job)"]}
    verdict = result.get("verdict") if result.get("verdict") in VERDICTS else "ERROR"
    score = clean_value(result.get("score")) if isinstance(result.get("score"), dict) else None
    S = (score or {}).get("S")
    hc = result.get("harness_commit") if isinstance(result.get("harness_commit"), str) and SHA_RE.match(result["harness_commit"]) else None
    out = {"verdict": verdict, "score": score, "comparable": result.get("comparable") is True,
           "truncated": result.get("truncated") is True, "harness_commit": hc,
           "verified": bool(verification.get("attested")), "record_of": None, "against": None, "requeue": False,
           "organiser_error": None, "organiser_side": False, "error_reason": None,
           "benchmarked": benchmarked}
    if out["verified"] and verdict == "ERROR" and result.get("organiser_error") in ORGANISER_ERRORS:
        out["organiser_error"] = result["organiser_error"]      # named by the core (attested)
    elif not out["verified"]:
        out["organiser_error"] = "attestation"                  # the provenance failed: the organiser's side
    reasons = clean_reasons(result.get("reasons"))
    extra = []

    def error(why=None):
        out["organiser_side"] = True                    # not a clean verdict: it joins the error streak
        out["error_reason"] = why or (reasons[0] if reasons else None)
        if why:
            extra.append(why)
        if out["organiser_error"] in PAUSING_ERRORS:    # the organiser's, not the entry's: never uses up the retry
            out["requeue"] = True
            what = "machine fingerprint" if out["organiser_error"] == "fingerprint" else "the season's chain lengths"
            extra.append(f"organiser ERROR ({what}): queued again; this run does not count as an attempt")
            return "queued"
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
    elif not out["comparable"]:
        status = "unranked"
        extra.append("ACCEPT, not comparable (" + ("truncated stream" if out["truncated"]
                                                    else "the job plan") + "): not ranked")
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
        beats, why, out["against"] = against(S, record, margin)
        extra.append(why)
        status = "record" if beats else "accepted"
        if beats:
            out["record_of"] = record["id"]
    out["status"] = status
    out["reasons"] = reasons[:max(0, 20 - len(extra))] + extra[:20]
    return out


def cache_retry(result, entry):
    """True if a REJECT used the record build cache (its certificate restored modules from it) and this entry was not yet evaluated without it: it is queued once more with
    `record_cache: false`, so a sabotaged cache cannot fail a candidate. An ERROR's retry runs
    without the cache anyway (flows.publish)."""
    if not isinstance(result, dict) or result.get("verdict") != "REJECT" or entry.get("record_cache") is False:
        return False

    def restored(r):
        c = (r or {}).get("certificate") if isinstance(r, dict) else None
        rc = (c or {}).get("record_cache") if isinstance(c, dict) else None
        return isinstance(rc, dict) and bool(rc.get("restored"))
    legacy = result.get("record_cache")
    return restored(result) or (isinstance(legacy, dict) and bool(legacy.get("reused")))


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
