"""Constants and the sanitisers every module uses (TRUSTED; the bot of recursion.fast-submissions).

Every string that reaches `data`, a comment or a commit status from a pull request (its title, the
NOTES header, file names, the result's reasons) goes through `clean` or `code_span` first.
"""
import datetime
import re

CORE_REPO = "scaraven/recursion.fast"
SIGNER_WORKFLOW = "scaraven/recursion.fast/.github/workflows/evaluate.yml"
STATUS_CONTEXT = "recursion.fast/evaluation"
# The record rule (AGENTS.md §10), per track t: a comparable, attested ACCEPT at the pin is a new
# record of t iff S_t < (1 - MARGIN) * S_t,record, S_t,record the standing record's score in t at the pin.
# MARGIN is the owner's choice (2 %), not derived from the noise. For reference: σ, the relative
# run-to-run spread of S for one entry on the evaluation machine with the fixed chain lengths, was
# measured at 1.75 % over 10 runs at the smoke shape (the core's harness/smoke.toml; mostly per-step
# process overhead, likely smaller at the season shape). S and S_record are two independent runs, so
# two runs of one entry differ by about √2·σ ≈ 2.5 %: a near-copy of the record can beat it by noise
# alone (at σ = 1.75 %, in roughly one attempt in five). A noise-proof margin would be 3·√2·σ ≈ 7.4 %.
# The defences are elsewhere: a byte copy of an evaluated root is invalid, a record's prover binary
# never takes the record again, and the owner retires a record won by noise (`retire`). The owner may
# change MARGIN between seasons (a stored state with another margin is rewritten at once,
# rfqueue.load; README.md, "Changing the margin", lists every place that states it).
MARGIN = 0.02
# The tracks (the core's AGENTS.md §7, §8): two scores from the one evaluation, each with its own
# records. A result's `score.tracks` names, per track, the field of `score` that is its score
# ({"sum": "S", "product": "S_product"}); a score without `tracks` (an older result) has the sum
# alone, `S`. The record rule runs once per track that the result names, with the one MARGIN.
# TRACKS is the order the bot lists them in and the tracks `record` always names; a track a result
# names that is not here is decided the same way, so a later track needs no bot change.
TRACKS = ("sum", "product")
LEGACY_TRACKS = {"sum": "S"}
TRACK_RE = re.compile(r"[a-z][a-z0-9_]{0,15}\Z")
MAX_ATTEMPTS = 2          # an organiser-side ERROR is evaluated once more, then left for the owner
# Organiser errors the core names in a result (`organiser_error`), and `attestation`, which the bot
# gives a result whose provenance does not verify (nothing an entry runs can reach the attest job).
# `drift` is among them although c_P is sampled during the entry's stream: the sandbox leaves no
# entry process alive, so only a thermal effect could carry over (accepted and documented). These are
# the organiser's alone: a run that ends in one never counts against the author (it does not move
# the author back in the fair order). A `fingerprint` error (the machine is not the season's) or a
# `lengths` error (the stream did not use the season's fixed chain lengths: an organiser bug, the
# same at every retry at one pin) does not even use up the entry's retry; the others are retried
# once (MAX_ATTEMPTS). `attestation`: an unverified result (the bot's).
UNCOUNTED_ERRORS = ("fingerprint", "lengths", "drift", "setup", "cache", "attestation")
ORGANISER_ERRORS = UNCOUNTED_ERRORS + ("harness",)
PAUSING_ERRORS = ("fingerprint", "lengths")     # a retry cannot clear them: re-queued in place without an attempt
# The pause (AGENTS.md §9): every run that ends on the organiser's side (any ERROR, named or not, a
# result whose provenance fails, no result at all, a run reaped after it died) joins the error
# streak. Only a clean verdict (a verified ACCEPT, PROVISIONAL or REJECT) whose stream ran on the
# season's machine clears it; a REJECT at the certificate or inside the stream never reached the
# benchmark-side checks and leaves it as it is. When PAUSE_AFTER errors of the streak count, the
# queue pauses and one issue is opened for the owner. An entry cannot cause an ENTRY_PROOF error
# (decided before any entry code runs, or by jobs that never fetch the entry; `attestation` here is a
# result that exists but whose provenance fails), so each one counts. The others (drift, measured
# during the entry's stream; harness, the certificate job, which builds the entry, ended without a
# certificate; no result at all; an unnamed ERROR; a reaped run) might be provoked by an entry, so
# they count once per author in the streak: no author can pause the queue alone, and an outage still
# pauses it at the second author's entry. An error more than STREAK_WINDOW_S before the streak's
# newest no longer counts, so unrelated errors weeks apart do not add up to a pause.
ENTRY_PROOF_ERRORS = ("fingerprint", "lengths", "setup", "cache", "attestation")
PAUSE_AFTER = 2
STREAK_CAP = 32           # the streak's newest runs kept in the state
STREAK_WINDOW_S = 7 * 24 * 3600

ROOT_RE = re.compile(r"[a-z][a-z0-9-]{0,39}\Z")
SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
ID_RE = re.compile(r"pr[1-9][0-9]{0,8}-[0-9a-f]{12}(?:-[0-9a-f]{8})?\Z")   # -<pin8>: a port to a new pin
LOGIN_RE = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?\Z")

QUEUED, RUNNING = "queued", "running"
FINAL = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error", "invalid",
         "superseded", "withdrawn")
STATUSES = (QUEUED, RUNNING) + FINAL
VERDICTS = ("ACCEPT", "PROVISIONAL", "REJECT", "ERROR")

# The entry caps: exactly the `[entry]` section of the core's harness/season.toml at the pin (the
# harness is authoritative; pin-core.sh warns when a new pin's values differ). A breach is invalid.
ENTRY_CAPS = {"files": 2048, "bytes": 512 << 20, "file_bytes": 128 << 20, "lean_files": 1024,
              "lean_bytes": 32 << 20, "prover_files": 256, "prover_bytes": 256 << 20, "claim_bytes": 64 << 10}
MAX_PR_FILES = 3000       # the pull-request files API lists at most 3000
MAX_TEXT_BYTES = 64 << 10   # NOTES.md, README.md (the bot's own cap)
MAX_HEADS_PER_PR = 50       # compact entries kept per pull request (older ones are dropped)
MAX_PATH = 512            # bytes of the whole path, `submissions/<root>/` included


def entry_id(pr, sha):
    """The id of one evaluated commit of one pull request: `pr<N>-<first 12 hex of the sha>`."""
    return f"pr{int(pr)}-{sha[:12]}"


def now_iso(clock=None):
    t = clock() if clock else datetime.datetime.now(datetime.timezone.utc)
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def clean(s, cap):
    """Untrusted text as one printable line of at most `cap` characters (Unicode letters kept;
    control, format (bidi) and separator characters other than space become `?`)."""
    s = " ".join(str(s if s is not None else "").split())
    out = "".join(c if c.isprintable() else "?" for c in s)
    return out if len(out) <= cap else out[: max(cap - 1, 0)] + "…"


def ascii_line(s, cap):
    """Untrusted text as printable ASCII, at most `cap` characters, with no backtick."""
    s = " ".join(str(s if s is not None else "").split())
    out = "".join(c if 32 <= ord(c) < 127 else "?" for c in s).replace("`", "'")
    return out if len(out) <= cap else out[: max(cap - 3, 0)] + "..."


def code_span(s, cap=300):
    """Untrusted text for a comment: printable ASCII in a code span, so no markdown, link, HTML or
    @-mention in it is rendered."""
    return "`" + (ascii_line(s, cap) or " ") + "`"


def clean_reasons(rs, n=20, cap=300):
    if not isinstance(rs, list):
        rs = [rs] if rs else []
    return [clean(r, cap) for r in rs[:n]]


def is_num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and x == x and abs(x) != float("inf")


def score_fields(score):
    """[(track, field, value)] of a result's `score` object, in TRACKS order: the field
    `score.tracks[track]` names and its value, for each track whose score is a positive number (a
    score without `tracks`: the sum's `S` only). At most 8 tracks."""
    if not isinstance(score, dict):
        return []
    names = score.get("tracks") if isinstance(score.get("tracks"), dict) else LEGACY_TRACKS
    out = []
    for t, f in list(names.items())[:8]:
        v = score.get(f) if isinstance(f, str) and f != "tracks" else None
        if isinstance(t, str) and TRACK_RE.match(t) and is_num(v) and v > 0:
            out.append((t, f, v))
    return sorted(out, key=lambda x: (TRACKS.index(x[0]) if x[0] in TRACKS else len(TRACKS), x[0]))


def track_scores(score):
    """{track: the positive score in that track} of a result's `score` object (`score_fields`)."""
    return {t: v for t, _f, v in score_fields(score)}
