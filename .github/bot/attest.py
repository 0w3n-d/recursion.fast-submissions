"""Provenance of a result (TRUSTED): the checks of the core's `harness/verify-record.sh`, bound to
this run, and that script itself for an ACCEPT.

1. `gh attestation verify RESULT --repo THIS_REPO --signer-workflow
   scaraven/recursion.fast/.github/workflows/evaluate.yml`: attested by the core's reusable
   workflow, in this repository, on a self-hosted runner (the certificate's `runnerEnvironment`:
   the organiser's server is the trust anchor, the core's AGENTS.md §8; GitHub attests the
   workflow and commit);
2. every attestation's signer digest (the commit the reusable workflow ran at) is the result's
   `harness_commit` (as verify-record.sh);
3. the attestation was made by this workflow run (`runInvocationURI`) and the result names this
   run (`job`): a genuine result of another evaluation, replayed as this run's artifact, fails;
4. for a comparable ACCEPT, the core's `harness/verify-record.sh` at the pin must pass as well (it
   also requires the result to record the organiser's runner: name `rf-…`, the one label
   `rf-bench`; the server's runners carry exactly one label, `rf-bench` or `rf-light`).

`attested` is 1-3; `record_ok` is 4."""
import json
import os
import re
import subprocess

from common import SHA_RE, SIGNER_WORKFLOW


def _attempt(s, run_id):
    m = re.search(rf"/actions/runs/{run_id}/attempts/([0-9]+)", s or "")
    return int(m.group(1)) if m else None


def verify(path, result, repo, run_id, core_dir=None, run=subprocess.run, min_attempt=1):
    """`attested` (provenance, 1-3, for every verdict) and `record_ok` (4, only for a comparable
    ACCEPT: verify-record.sh refuses anything else, so it is never asked about an unranked one). The
    attempt that produced the result must not precede the attempt whose `select` chose the entry
    (`min_attempt`): after "re-run all jobs", an older attempt's artifact is refused."""
    out = {"attested": False, "record_ok": False, "reason": ""}
    hc = result.get("harness_commit") if isinstance(result, dict) else None
    if not isinstance(hc, str) or not SHA_RE.match(hc):
        out["reason"] = "the result has no full harness_commit"
        return out
    job = result.get("job")
    if not isinstance(job, str) or not job.startswith(f"{repo}/actions/runs/{run_id}/"):
        out["reason"] = f"the result names another run ({str(job)[:120]})"
        return out
    if (_attempt("/" + job, run_id) or 0) < min_attempt:
        out["reason"] = f"the result is from an attempt before the one that selected this entry ({min_attempt})"
        return out
    try:
        r = run(["gh", "attestation", "verify", path, "--repo", repo, "--signer-workflow", SIGNER_WORKFLOW,
                 "--format", "json"], capture_output=True, timeout=300)
    except (OSError, subprocess.TimeoutExpired) as e:
        out["reason"] = f"gh attestation verify did not run: {e.__class__.__name__}"
        return out
    if r.returncode:
        out["reason"] = "gh attestation verify failed: " + r.stderr.decode("utf-8", "replace").strip()[-200:]
        return out
    try:
        att = json.loads(r.stdout)
        certs = [a["verificationResult"]["signature"]["certificate"] for a in att]
    except (ValueError, KeyError, TypeError):
        out["reason"] = "gh attestation verify printed no attestation"
        return out
    digests = {c.get("buildSignerDigest") for c in certs}
    if not certs or digests != {hc}:
        out["reason"] = f"the attesting workflow ran at {sorted(map(str, digests))}, the result says {hc}"
        return out
    envs = {c.get("runnerEnvironment") for c in certs}
    if envs != {"self-hosted"}:
        out["reason"] = f"attested on {sorted(map(str, envs))}, not the organiser's self-hosted runner"
        return out
    runs = {c.get("runInvocationURI") or "" for c in certs}
    if not all(f"/{repo}/actions/runs/{run_id}/" in u and (_attempt(u, run_id) or 0) >= min_attempt for u in runs):
        out["reason"] = "the attestation was made by another workflow run or an earlier attempt"
        return out
    out["attested"] = True
    if result.get("verdict") == "ACCEPT" and result.get("comparable") is True and core_dir:
        script = os.path.join(core_dir, "harness", "verify-record.sh")
        try:
            r = run(["bash", script, path], capture_output=True, timeout=300)
            ok, msg = r.returncode == 0, (r.stdout + r.stderr).decode("utf-8", "replace").strip()[-240:]
        except (OSError, subprocess.TimeoutExpired) as e:
            ok, msg = False, f"verify-record.sh did not run: {e.__class__.__name__}"
        out["record_ok"], out["reason"] = ok, msg
    return out
