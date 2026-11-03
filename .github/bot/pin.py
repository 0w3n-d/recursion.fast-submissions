"""The one core pin (TRUSTED): the `.contract` gitlink, the `uses: …/evaluate.yml@<PIN>` and the
`core_ref: <PIN>` of `.github/workflows/evaluate-next.yml` must be one full SHA.

  python3 -I .github/bot/pin.py [REPO_DIR]          the checkout (its index); prints the pin or exits 1
  python3 -I .github/bot/pin.py --git GIT_DIR REV   a commit read as data (a pull request's head)
  python3 -I .github/bot/pin.py --core [REPO_DIR]   also: the core's evaluate.yml at the pin takes every
                                                    input the bot passes, and its season's [entry]
                                                    caps are the bot's (fetches the pin, read-only)"""
import os
import re
import subprocess
import sys

WORKFLOW = ".github/workflows/evaluate-next.yml"
USES_RE = re.compile(r"^\s*uses:\s*scaraven/recursion\.fast/\.github/workflows/evaluate\.yml@(\S+)", re.M)
CORE_REF_RE = re.compile(r"^\s*core_ref:\s*[\"']?([^\s\"'#]+)", re.M)
ANY_CORE_RE = re.compile(r"^\s*uses:\s*['\"]?scaraven/recursion\.fast/", re.M)
SHA = re.compile(r"[0-9a-f]{40}\Z")


def pins_of(text, gitlink):
    """(pin or None, problems) from the workflow's text and the gitlink's SHA."""
    problems = []
    uses, refs = USES_RE.findall(text), CORE_REF_RE.findall(text)
    if len(uses) != 1 or len(ANY_CORE_RE.findall(text)) != 1:
        problems.append(f"{WORKFLOW} must name scaraven/recursion.fast exactly once, in `uses: …/evaluate.yml@<PIN>`")
    if len(refs) != 1:
        problems.append(f"{WORKFLOW} must have exactly one `core_ref:`")
    vals = {"gitlink .contract": gitlink, "uses @": uses[0] if uses else None, "core_ref": refs[0] if refs else None}
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


def inputs_problems(ours, core):
    """The `with:` keys of our `evaluate` job that the core's evaluate.yml (at the pin) does not take."""
    m = WITH_RE.search(ours)
    keys = set(re.findall(r"^      ([a-z_]+):", m.group(1), re.M)) if m else set()
    core_inputs = set(INPUTS_RE.findall(core.split("outputs:", 1)[0]))
    if not keys:
        return ["no `with:` block found in the evaluate job"]
    missing = sorted(keys - core_inputs)
    return [f"the core's evaluate.yml at the pin has no input {k}" for k in missing]


def caps_problems(season_text):
    """Differences between the season's [entry] caps and the bot's (common.ENTRY_CAPS)."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from common import ENTRY_CAPS
    sec = re.search(r"^\[entry\][^\n]*\n(.*?)(?=^\[|\Z)", season_text, re.M | re.S)
    vals = dict((k, int(v)) for k, v in re.findall(r"^([a-z_]+)\s*=\s*([0-9]+)", sec.group(1), re.M)) if sec else {}
    return [f"[entry] {k}: the season says {vals.get(k)}, the bot {v}" for k, v in sorted(ENTRY_CAPS.items())
            if vals.get(k) != v] + [f"[entry] {k} is new in the season" for k in sorted(set(vals) - set(ENTRY_CAPS))]


def core_problems(repo_dir, pin):
    import tempfile
    d = tempfile.mkdtemp(prefix="rf-core-")
    g = lambda *a: subprocess.run(["git", "--git-dir", d, *a], capture_output=True)  # noqa: E731
    g("init", "-q", "--bare")
    if g("fetch", "-q", "--depth=1", "--no-tags", "https://github.com/scaraven/recursion.fast.git", pin).returncode:
        return [f"cannot fetch the core at {pin}"]
    core_wf = g("show", f"{pin}:.github/workflows/evaluate.yml").stdout.decode("utf-8", "replace")
    season = g("show", f"{pin}:harness/season.toml").stdout.decode("utf-8", "replace")
    with open(os.path.join(repo_dir, WORKFLOW), encoding="utf-8") as f:
        ours = f.read()
    return inputs_problems(ours, core_wf) + caps_problems(season)


def main():
    a = sys.argv[1:]
    core = "--core" in a
    a = [x for x in a if x != "--core"]
    if a[:1] == ["--git"]:
        pin, problems = read_git(a[1], a[2])
    else:
        pin, problems = read(a[0] if a else ".")
        if pin and core:
            problems += core_problems(a[0] if a else ".", pin)
            pin = None if problems else pin
    for p in problems:
        print(f"pin-check: {p}")
    if pin:
        print(pin)
    return 0 if pin else 1


if __name__ == "__main__":
    sys.exit(main())
