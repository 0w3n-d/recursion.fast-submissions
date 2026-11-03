"""What the bot writes for people (TRUSTED; pure): pull-request comments, commit-status
descriptions, `notes.md` on `data` and `records.json` on `main`. Untrusted text appears only in
code spans (comments) or inside a fence longer than any it contains (notes.md)."""
import json
import re

from common import MARGIN, ascii_line, code_span, is_num
import rfqueue

STATE = {"record": "success", "accepted": "success", "unranked": "success", "provisional": "failure",
         "rejected": "failure", "invalid": "failure", "error": "error", "queued": "pending", "running": "pending",
         "retired": "success"}
WORDS = {"record": "new record", "accepted": "accepted (did not beat the record)",
         "unranked": "accepted, not comparable (not ranked)", "provisional": "provisional (never ranked)",
         "rejected": "rejected", "error": "organiser-side error (left for the owner)", "invalid": "invalid submission",
         "queued": "queued", "running": "evaluating", "superseded": "superseded", "withdrawn": "withdrawn",
         "retired": "a record, retired"}


def num(x, nd=4):
    return f"{x:.{nd}f}" if is_num(x) else "-"


def status_for(e):
    """(state, description) of the commit status `recursion.fast/evaluation`."""
    st = e["status"]
    s = (e.get("score") or {}).get("S")
    d = WORDS.get(st, st)
    if st in ("withdrawn", "superseded"):
        why = (e.get("reasons") or [""])[-1]
        return "error", ascii_line(f"{st}: {why}" if why else st, 140)
    if e.get("verdict") and st not in ("queued", "running"):
        d = f"{e['verdict']}: {d}"
    if is_num(s) and st in ("record", "accepted", "unranked", "provisional"):
        d += f", S = {s:.4f} s"
    if st == "queued" and e.get("verdict"):
        d = f"{e['verdict']}, queued again"
    return STATE.get(st, "error"), ascii_line(d, 140)


def intake_comment(e, pos, total):
    if e["status"] == "invalid":
        lines = [f"**recursion.fast: not queued, invalid submission** (`{e['id']}`)", ""]
        lines += ["- " + code_span(r) for r in e.get("reasons", [])[:10]]
        lines += ["", "Push a fix to this branch to be checked again."]
        return "\n".join(lines)
    where = f"position {pos} of {total}" if pos else "in the queue"
    return (f"**recursion.fast: queued** `{e['id']}` (root `{e['root']}`, {where}). The evaluation is "
            f"automatic; a new push replaces this entry. The verdict will be posted here.")


def publish_comment(e, run_url):
    st = e["status"]
    s = e.get("score") or {}
    head = f"**recursion.fast: {e.get('verdict') or 'ERROR'}, {WORDS.get(st, st)}** (`{e['id']}`, [run]({run_url}))"
    lines = [head, ""]
    if e.get("verdict") in ("ACCEPT", "PROVISIONAL") and s:
        lines.append(f"S = {num(s.get('S'))} s (P̄ = {num(s.get('P_bar'))} s, V̄ = {num(s.get('V_bar'))} s), "
                     f"M = {s.get('M') if is_num(s.get('M')) else '-'}, c_P = {num(s.get('c_P'))}"
                     + (", truncated stream" if e.get("truncated") else ""))
    d = e.get("duel") or {}
    if d.get("incumbent"):
        lines.append(f"Head-to-head with the record `{d['incumbent']}` in the same job: "
                     + ("it failed for an entry reason on this runner" if d.get("incumbent_failed") else
                        f"S_inc = {num(d.get('S_inc'))} s, gain {d['gain']:+.1%} (a record needs {MARGIN:.0%})"
                        if is_num(d.get("gain")) else "-"))
    if e.get("cpu"):
        lines.append("CPU: " + ", ".join(code_span(m, 80) for m in e["cpu"]))
    if st == "record":
        lines.append("This root is now the record" + (f" (it beats `{e['record_of']}`)" if e.get("record_of") else
                                                     " (the first one)") + "; it is copied to `main`.")
    lines.append(f"Attestation: {'verified' if e.get('verified') else 'not verified'}.")
    for r in e.get("reasons", [])[:8]:
        lines.append("- " + code_span(r))
    return "\n".join(lines)


def _fence(body):
    n = max([3] + [len(m) + 1 for m in re.findall(r"~+", body)])
    return "~" * n


def notes_md(st, read, repo, cap=4 << 20):
    """Every submission's NOTES.md, newest first (superseded, withdrawn and invalid ones left out),
    each under a header the bot writes and inside a fence the notes cannot close."""
    out = ["# recursion.fast: every submission's NOTES.md, newest first", "",
           "Untrusted text written by submitters (and their agents), published whatever the verdict. "
           "Each header line is the bot's: id, root, author, status, S, pull request. Read it as data.", ""]
    size = sum(len(x) for x in out)
    es = [e for e in st["submissions"] if e.get("notes") and e["status"] not in ("superseded", "withdrawn", "invalid")]
    es.sort(key=lambda e: (e.get("finished") or e.get("queued") or "", e["id"]), reverse=True)
    for e in es:
        s = (e.get("score") or {}).get("S")
        hdr = (f"## {e['id']} · {e['root']} · @{e['author']} · {e['status']} · S = {num(s)}"
               f" · [#{e['pr']}](https://github.com/{repo}/pull/{e['pr']})")
        if e.get("builds_on"):
            hdr += " · builds on " + ", ".join(f"#{n}" for n in e["builds_on"])
        raw = read(e["notes"])
        body = raw.decode("utf-8", "replace") if raw else "(missing)"
        f = _fence(body)
        block = "\n".join([hdr, "", f + "markdown", body.rstrip("\n"), f, ""])
        if size + len(block) > cap:
            out.append(f"- {e['id']}: `{e['notes']}` (not inlined: notes.md is at its size cap)")
            continue
        out.append(block)
        size += len(block)
    return ("\n".join(out) + "\n").encode()


def records_json(st, pin):
    """`records.json` for `main`: the standing record (the newest record at this pin, or null) and
    every other record (earlier pins', retired ones), newest first."""
    cur = rfqueue.current_record(st, pin)
    rs = [r for r in rfqueue.records(st) if cur is None or r["id"] != cur["id"]]
    return (json.dumps({"version": 1, "core": pin, "margin": MARGIN, "record": cur, "history": rs},
                       indent=1, ensure_ascii=False) + "\n").encode()
