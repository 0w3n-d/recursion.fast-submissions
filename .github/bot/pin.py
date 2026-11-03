"""The one core pin (TRUSTED): the `.contract` gitlink, the `uses: …/evaluate.yml@<PIN>` and the
`core_ref: <PIN>` of `.github/workflows/evaluate-next.yml` must be one full SHA.

  python3 -I .github/bot/pin.py [REPO_DIR]     prints the pin, or the disagreement (exit 1)"""
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


def main():
    pin, problems = read(sys.argv[1] if len(sys.argv) > 1 else ".")
    for p in problems:
        print(f"pin-check: {p}")
    if pin:
        print(pin)
    return 0 if pin else 1


if __name__ == "__main__":
    sys.exit(main())
