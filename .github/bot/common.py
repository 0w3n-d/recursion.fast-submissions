"""Constants and the sanitisers every module uses (TRUSTED; the bot of recursion.fast-submissions).

Every string that reaches `data`, a comment or a commit status from a pull request (its title, the
NOTES header, file names, the result's reasons) goes through `clean` or `code_span` first.
"""
import datetime
import re

CORE_REPO = "scaraven/recursion.fast"
SIGNER_WORKFLOW = "scaraven/recursion.fast/.github/workflows/evaluate.yml"
STATUS_CONTEXT = "recursion.fast/evaluation"
# The record rule's two parameters (the owner may tune them after calibrating with self-duels):
MARGIN = 0.03             # a duel is won iff S_cand <= (1 - MARGIN) * S_inc, both measured in one job
RECORD_WINS = 2           # duels a candidate must win against the same standing record to take it
MAX_ATTEMPTS = 2          # an organiser-side ERROR is evaluated once more, then left for the owner

ROOT_RE = re.compile(r"[a-z][a-z0-9-]{0,39}\Z")
SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
ID_RE = re.compile(r"pr[1-9][0-9]{0,8}-[0-9a-f]{12}(?:-[0-9a-f]{8})?\Z")   # -<pin8>: a port to a new pin
LOGIN_RE = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?\Z")

# confirming: won a duel, waiting at the front of the queue for the next one against the same record
QUEUED, RUNNING, CONFIRMING = "queued", "running", "confirming"
WAITING = (QUEUED, CONFIRMING)
FINAL = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error", "invalid",
         "superseded", "withdrawn")
STATUSES = (QUEUED, RUNNING, CONFIRMING) + FINAL
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
