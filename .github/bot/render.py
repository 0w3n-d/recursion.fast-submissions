"""What the bot writes for people (TRUSTED; pure): pull-request comments, commit-status
descriptions, `notes.md` on `data` and `records.json` on `main`. Untrusted text appears only in
code spans (comments) or inside a fence longer than any it contains (notes.md)."""
import json
import re

from common import MARGIN, STREAK_WINDOW_S, TRACKS, ascii_line, code_span, is_num, score_fields
import rfqueue

STATE = {"record": "success", "accepted": "success", "unranked": "success", "provisional": "failure",
         "rejected": "failure", "invalid": "failure", "error": "pending", "queued": "pending", "running": "pending",
         "retired": "success"}
WORDS = {"record": "new record", "accepted": "accepted (did not beat the record)",
         "unranked": "accepted, not comparable (not ranked)", "provisional": "provisional (never ranked)",
         "rejected": "rejected", "error": "waiting on the organiser (an organiser-side error)", "invalid": "invalid submission",
         "queued": "queued", "running": "evaluating", "superseded": "superseded", "withdrawn": "withdrawn",
         "retired": "a record, retired"}


def num(x, nd=4):
    return f"{x:.{nd}f}" if is_num(x) else "-"


def scores_text(score):
    """Each track's score of a result: `S = 1.2345 s, S_product = 1.5000 s` (the fields it names)."""
    return ", ".join(f"{f} = {v:.4f} s" for _t, f, v in score_fields(score)) or "no score"


def took_text(e):
    """The tracks whose record the entry took, e.g. ` (sum, product)`."""
    return f" ({', '.join(e['record_in'])})" if e.get("record_in") else ""


def status_for(e):
    """(state, description) of the commit status `recursion.fast/evaluation`."""
    st = e["status"]
    fields = score_fields(e.get("score"))
    d = WORDS.get(st, st) + (took_text(e) if st == "record" else "")
    if st in ("withdrawn", "superseded"):
        why = (e.get("reasons") or [""])[-1]
        return "error", ascii_line(f"{st}: {why}" if why else st, 140)
    if e.get("verdict") and st not in ("queued", "running"):
        d = f"{e['verdict']}: {d}"
    if fields and st in ("record", "accepted", "unranked", "provisional"):
        d += ", " + scores_text(e.get("score"))
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
        x = lambda k: num(s.get(k))  # noqa: E731
        m = s.get("M") if is_num(s.get("M")) else "-"
        trunc = ", truncated stream" if e.get("truncated") else ""
        lines.append(f"Sum: S = {x('S')} s (P̄ = {x('P_bar')} s, V̄ = {x('V_bar')} s, x̄ = {x('x_bar')}), M = {m}{trunc}")
        if is_num(s.get("S_product")):
            lines.append(f"Product: S_product = {x('S_product')} s (P̄ = {x('P_bar')} s, mean V = {x('V_mean_s')} s, "
                         f"g = {x('g')}; mean proof size {num(s.get('pi_mean_bytes'), 0)} bytes, not scored)")
    order = lambda kv: (TRACKS.index(kv[0]) if kv[0] in TRACKS else len(TRACKS), kv[0])  # noqa: E731
    for t, d in sorted((e.get("against") or {}).items(), key=order):
        if isinstance(d, dict) and d.get("record") and is_num(d.get("gain")):
            lines.append(f"Against the {t} record `{d['record']}`: {num(d.get('S'))} s against {num(d.get('S_record'))} s, "
                         f"gain {d['gain']:+.1%} (a new record needs more than {MARGIN:.0%})")
    if st == "record":
        rof = e.get("record_of") or {}
        took = [f"{t} (it beats `{rof[t]}`)" if rof.get(t) else f"{t} (no record stood in it at the pin)"
                for t in e.get("record_in") or []]
        lines.append("This root is now the record of " + " and ".join(took) + "; it is copied to `main`.")
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
           "Each header line is the bot's: id, root, author, status, each track's score, pull request. Read it as data.", ""]
    size = sum(len(x) for x in out)
    es = [e for e in st["submissions"] if e.get("notes") and e["status"] not in ("superseded", "withdrawn", "invalid")]
    es.sort(key=lambda e: (e.get("finished") or e.get("queued") or "", e["id"]), reverse=True)
    for e in es:
        sc = " · ".join(f"{f} = {num(v)}" for _t, f, v in score_fields(e.get("score"))) or "S = -"
        hdr = (f"## {e['id']} · {e['root']} · @{e['author']} · {e['status']} · {sc}"
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
    """`records.json` for `main` (version 2): per track, the standing record (the newest record of
    the track at this pin, or null) and every other record of that track (earlier pins', retired
    ones), newest first. An entry that took both tracks' records appears under both."""
    cur = rfqueue.standing(st, pin)
    hist = {t: [r for r in rfqueue.records(st, t) if cur[t] is None or r["id"] != cur[t]["id"]] for t in cur}
    return (json.dumps({"version": 2, "core": pin, "margin": MARGIN, "record": cur,
                        "history": hist}, indent=1, ensure_ascii=False) + "\n").encode()


def workflow_comment(sha, problems):
    """The workflow check's refusal of a pull request's head (organiser text; problems in code spans)."""
    return "\n".join([f"**recursion.fast: workflow check failed** on `{sha[:12]}` (`.github/bot/wfcheck.py`, main's code)", ""]
                     + ["- " + code_span(p, 300) for p in problems[:10]]
                     + ["", "No workflow may run on the organiser's runners for a fork-controlled event, nor give a "
                        "`pull_request_target` job the pull request's head as code. Fix the workflows and push again."])


PAUSE_TITLE = "recursion.fast: evaluation paused (organiser errors since the last completed benchmark)"
ERROR_KINDS = {"fingerprint": "the machine fingerprint is not the season's",
               "lengths": "the stream did not use the season's chain lengths",
               "drift": "c_P drifted beyond c_P_drift", "setup": "a setup job did not complete",
               "cache": "an organiser cache was missing", "attestation": "the result's provenance did not verify",
               "harness": "the certificate job ended without a certificate", "unnamed": "an unnamed harness ERROR",
               "noresult": "no readable result (the attest job did not finish, or its result.json could not be read)",
               "reaped": "the run ended without publishing a verdict"}


def pause_notice(st, run_url):
    """The one owner-facing notice when the queue pauses (organiser text; reasons in code spans)."""
    streak = st.get("error_streak") or []
    left = [e["id"] for e in st["submissions"] if e["status"] == "error"
            and any(x.get("id") == e["id"] for x in streak)]
    lines = [f"The evaluation queue is **paused**: {rfqueue.pause_count(streak)} organiser errors counted since the last "
             f"run that completed its benchmark on the season's machine (the last: [run]({run_url})); {len(streak)} runs "
             "ended on the organiser's side in that time. One author's repeated errors of a kind an entry might provoke "
             f"count once, and an error more than {STREAK_WINDOW_S // 86400} days before the newest does not count. "
             "Nothing runs until you force a run.", "", "The runs, oldest first:", ""]
    lines += [f"- {code_span(x.get('at') or '', 20)} {code_span(x.get('id'), 60)} ({code_span(x.get('kind'), 40)}, "
              f"{ERROR_KINDS.get(x.get('kind'), 'an organiser-side ERROR')}): {code_span(x.get('reason'), 300)}"
              for x in streak[-10:]]
    lines += ["", "No entry was charged for these runs (a fingerprint or lengths ERROR uses up no attempt; the "
              "others use the entry's one retry). Fix the cause: the machine or the image (then the season's "
              "`[machine] fingerprint` in the core, and the pin), the harness at the pin, the setup or a cache. "
              "Then run `evaluate-next` with `pr` = a queued pull request (a port of the record due at the pin runs "
              "first). Its clean verdict resumes the queue only if its stream ran to the end on the season's "
              "machine (an ACCEPT, a PROVISIONAL, or a REJECT after the stream): a REJECT at the certificate or "
              "inside the stream does not, so pick an entry likely to get that far (the record's port, or one "
              "whose earlier commit was ACCEPTed). With none, run `evaluate-next` with `resume` = true. The bot "
              "README's \"Owner setup\" has the procedure for a changed image or machine."]
    if left:
        lines += ["", "Left in `error` (force each with `evaluate-next`, `pr` = its pull request): "
                  + ", ".join(code_span(i, 60) for i in left[:20])]
    return "\n".join(lines)
