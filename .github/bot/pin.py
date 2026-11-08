"""The one core pin (TRUSTED): the `.contract` gitlink, the `uses: …/evaluate.yml@<PIN>` and the
`core_ref: <PIN>` of `.github/workflows/evaluate-next.yml` must be one full SHA.

  python3 -I .github/bot/pin.py [REPO_DIR]          the checkout (its index); prints the pin or exits 1
  python3 -I .github/bot/pin.py --git GIT_DIR REV   a commit read as data (a pull request's head)
  --core (with either)                              also: the core's evaluate.yml at the pin takes every
                                                    input the bot passes, the bot passes every input the
                                                    core requires, and it pins every action by full
                                                    commit SHA, and its season's [entry] caps are the
                                                    bot's (fetches the pin, read-only)
  python3 -I .github/bot/pin.py --records FILE PIN  prints records.json re-pinned to PIN (no record stands
                                                    at a new pin: the record moves to the history)"""
import json
import os
import re
import subprocess
import sys

WORKFLOW = ".github/workflows/evaluate-next.yml"
USES_RE = re.compile(r"^\s*uses:\s*scaraven/recursion\.fast/\.github/workflows/evaluate\.yml@(\S+)", re.M)
CORE_REF_RE = re.compile(r"^\s*core_ref:\s*[\"']?([^\s\"'#]+)", re.M)
CHECKOUT_PIN_RE = re.compile(r"^\s*ref:\s*([^\s#]+)\s*# THE PIN\b", re.M)
ANY_CORE_RE = re.compile(r"^\s*uses:\s*['\"]?scaraven/recursion\.fast/", re.M)
SHA = re.compile(r"[0-9a-f]{40}\Z")


def pins_of(text, gitlink):
    """(pin or None, problems) from the workflow's text and the gitlink's SHA."""
    problems = []
    uses, refs, cos = USES_RE.findall(text), CORE_REF_RE.findall(text), CHECKOUT_PIN_RE.findall(text)
    if len(cos) != 1:
        problems.append(f"{WORKFLOW} must have exactly one core checkout `ref: <PIN>  # THE PIN`")
    if len(uses) != 1 or len(ANY_CORE_RE.findall(text)) != 1:
        problems.append(f"{WORKFLOW} must name scaraven/recursion.fast exactly once, in `uses: …/evaluate.yml@<PIN>`")
    if len(refs) != 1:
        problems.append(f"{WORKFLOW} must have exactly one `core_ref:`")
    vals = {"gitlink .contract": gitlink, "uses @": uses[0] if uses else None, "core_ref": refs[0] if refs else None,
            "core checkout ref": cos[0] if cos else None}
    for k, v in vals.items():
        if not isinstance(v, str) or not SHA.match(v):
            problems.append(f"{k} is not a full lowercase SHA: {v}")
    if len(set(vals.values())) != 1:
        problems.append("the pins disagree: " + ", ".join(f"{k} = {v}" for k, v in vals.items()))
    return (None if problems else gitlink), problems


def gitlink(repo_dir):
    """The `.contract` gitlink in the index (a fresh checkout's index is its commit's tree)."""
    r = subprocess.run(["git", "-C", repo_dir, "ls-files", "-s", "--", ".contract"], capture_output=True, text=True)
    parts = r.stdout.split()
    if r.returncode == 0 and len(parts) >= 2 and parts[0] == "160000":
        return parts[1]
    r = subprocess.run(["git", "-C", repo_dir, "ls-tree", "HEAD", ".contract"], capture_output=True, text=True)
    parts = r.stdout.split()
    return parts[2] if r.returncode == 0 and len(parts) >= 3 and parts[0] == "160000" else None


def read(repo_dir):
    with open(os.path.join(repo_dir, WORKFLOW), encoding="utf-8") as f:
        return pins_of(f.read(), gitlink(repo_dir))


def read_git(git_dir, rev):
    """The pins of commit `rev` of the repository `git_dir`, read as data (git show / ls-tree)."""
    r = subprocess.run(["git", "--git-dir", git_dir, "show", f"{rev}:{WORKFLOW}"], capture_output=True)
    text = r.stdout.decode("utf-8", "replace") if r.returncode == 0 else ""
    t = subprocess.run(["git", "--git-dir", git_dir, "ls-tree", rev, ".contract"], capture_output=True, text=True)
    parts = t.stdout.split()
    link = parts[2] if t.returncode == 0 and len(parts) >= 3 and parts[0] == "160000" else None
    return pins_of(text, link)


WITH_RE = re.compile(r"^    uses: scaraven/recursion\.fast/[^\n]*\n(?:    (?!with:).*\n)*    with:\n((?:      .*\n|\s*\n)*)", re.M)
INPUTS_RE = re.compile(r"^\s{6}([a-z_]+):\s*\{\s*type:", re.M)
REQUIRED_RE = re.compile(r"^\s{6}([a-z_]+):\s*\{[^}\n]*\brequired:\s*true\b", re.M)
# the inputs the bot passes (none names an incumbent)
OUR_INPUTS = ("entry_repo", "entry_sha", "entry_path", "pr_ref", "core_ref", "record_cache", "record_manifest_sha256")


def inputs_problems(ours, core):
    """The `with:` keys of our `evaluate` job that the core's evaluate.yml (at the pin) does not take,
    the core's required inputs we do not pass, and any key outside `OUR_INPUTS`."""
    m = WITH_RE.search(ours)
    keys = set(re.findall(r"^      ([a-z_]+):", m.group(1), re.M)) if m else set()
    head = core.split("outputs:", 1)[0]
    core_inputs, required = set(INPUTS_RE.findall(head)), set(REQUIRED_RE.findall(head))
    if not keys:
        return ["no `with:` block found in the evaluate job"]
    return ([f"the core's evaluate.yml at the pin has no input {k}" for k in sorted(keys - core_inputs)]
            + [f"the core's evaluate.yml at the pin requires the input {k}, which the bot does not pass"
               for k in sorted(required - keys)]
            + [f"the evaluate job passes {k}, not an input of the bot's" for k in sorted(keys - set(OUR_INPUTS))])


ACTION_RE = re.compile(r"^\s*(?:-\s*)?uses:\s*[\"']?([^\s\"'#]+)", re.M)


def tag_problems(core_wf):
    """Actions of the core's evaluate.yml not pinned by a full commit SHA. The submissions repository
    requires SHA pins (`sha_pinning_required`), and that reaches into a called reusable workflow, so
    one tag there fails every evaluation before it starts. Only evaluate.yml itself is scanned: a
    local action (`./…`) or a further reusable workflow it calls is not (the launch core has none)."""
    out = []
    for ref in ACTION_RE.findall(core_wf):
        if ref.startswith(("./", "docker://")):
            continue
        name, _, at = ref.partition("@")
        if not SHA.match(at):
            out.append(f"the core's evaluate.yml at the pin uses {name} at {at or 'no ref'}, not a full commit SHA")
    return list(dict.fromkeys(out))


def caps_problems(season_text):
    """Differences between the season's [entry] caps and the bot's (common.ENTRY_CAPS)."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from common import ENTRY_CAPS
    sec = re.search(r"^\[entry\][^\n]*\n(.*?)(?=^\[|\Z)", season_text, re.M | re.S)
    vals = dict((k, int(v)) for k, v in re.findall(r"^([a-z_]+)\s*=\s*([0-9]+)", sec.group(1), re.M)) if sec else {}
    return [f"[entry] {k}: the season says {vals.get(k)}, the bot {v}" for k, v in sorted(ENTRY_CAPS.items())
            if vals.get(k) != v] + [f"[entry] {k} is new in the season" for k in sorted(set(vals) - set(ENTRY_CAPS))]


def core_problems(ours, pin):
    """What the core at `pin` lacks for our workflow text `ours`: inputs, SHA pins, the caps."""
    import shutil
    import tempfile
    d = tempfile.mkdtemp(prefix="rf-core-")
    try:
        g = lambda *a: subprocess.run(["git", "--git-dir", d, *a], capture_output=True)  # noqa: E731
        g("init", "-q", "--bare")
        if g("fetch", "-q", "--depth=1", "--no-tags", "https://github.com/scaraven/recursion.fast.git", pin).returncode:
            return [f"cannot fetch the core at {pin}"]
        core_wf = g("show", f"{pin}:.github/workflows/evaluate.yml").stdout.decode("utf-8", "replace")
        season = g("show", f"{pin}:harness/season.toml").stdout.decode("utf-8", "replace")
    finally:
        shutil.rmtree(d, ignore_errors=True)
    return inputs_problems(ours, core_wf) + tag_problems(core_wf) + caps_problems(season)


def repin_records(raw, pin):
    """records.json at a new pin, as the bot writes it there before any evaluation: `core` is the
    pin, `margin` the bot's (common.MARGIN), no record stands (`record: null`), and the old record
    heads the history."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from common import MARGIN
    j = json.loads(raw)
    if not isinstance(j, dict) or j.get("version") != 1:
        raise ValueError("records.json is not version 1 of the bot's format")
    rec, hist = j.get("record"), [h for h in j.get("history") or [] if isinstance(h, dict)]
    if isinstance(rec, dict) and j.get("core") != pin:
        hist = [rec] + [h for h in hist if h.get("id") != rec.get("id")]
        rec = None
    j.pop("record_wins", None)      # not a parameter of the record rule
    j.update(core=pin, margin=MARGIN, record=rec, history=hist)
    return (json.dumps(j, indent=1, ensure_ascii=False) + "\n").encode()


def workflow_text(repo_dir=None, git_dir=None, rev=None):
    if git_dir:
        r = subprocess.run(["git", "--git-dir", git_dir, "show", f"{rev}:{WORKFLOW}"], capture_output=True)
        return r.stdout.decode("utf-8", "replace")
    with open(os.path.join(repo_dir, WORKFLOW), encoding="utf-8") as f:
        return f.read()


def main():
    a = sys.argv[1:]
    if a[:1] == ["--records"]:
        with open(a[1], "rb") as f:
            sys.stdout.buffer.write(repin_records(f.read(), a[2]))
        return 0
    core = "--core" in a
    a = [x for x in a if x != "--core"]
    if a[:1] == ["--git"]:
        pin, problems = read_git(a[1], a[2])
        text = (lambda: workflow_text(git_dir=a[1], rev=a[2]))
    else:
        pin, problems = read(a[0] if a else ".")
        text = (lambda: workflow_text(a[0] if a else "."))
    if pin and core:
        problems += core_problems(text(), pin)
        pin = None if problems else pin
    for p in problems:
        print(f"pin-check: {p}")
    if pin:
        print(pin)
    return 0 if pin else 1


if __name__ == "__main__":
    sys.exit(main())
