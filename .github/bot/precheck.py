"""The intake's precheck of a submission pull request (TRUSTED; reads the pull request as data).

Two rules. `paths_rule` reads the pull request's changed files (the files API, renames' old names
included): they must all lie under one `submissions/<root>/`. `tree_rule` reads the root at the
head commit with `git ls-tree` and `git cat-file`: the required files, regular files and
directories only, safe names, and the entry caps of the core's season (`common.ENTRY_CAPS`, counted
as `harness/evaluate.py entry_caps` counts them)."""
import json
import re

from common import ENTRY_CAPS, MAX_PATH, MAX_PR_FILES, MAX_TEXT_BYTES, ROOT_RE, clean

COMPONENT_RE = re.compile(r"[A-Za-z0-9._+-]{1,255}\Z")
MODES = {"100644": "blob", "100755": "blob", "040000": "tree"}
HEADER_RE = re.compile(r"^\s*(?:[-*]\s+)?(?:\*\*|__)?\s*(builds on|agent)\s*(?:\*\*|__)?\s*:\s*(?:\*\*|__)?(.*)$",
                       re.IGNORECASE)
HEADER_LINES = 40


def paths_rule(files):
    """(root or None, reasons, outside): the one root the pull request changes, the reasons it is
    not a submission, and whether it touches anything outside `submissions/<name>/`."""
    if files is None:
        return None, [f"the pull request changes more than {MAX_PR_FILES} files"], True
    if not files:
        return None, ["the pull request changes no file"], False
    roots, outside = set(), []
    for f in files:
        for name in (f.get("filename"), f.get("previous_filename")):
            if not name:
                continue
            parts = name.split("/")
            if len(parts) >= 3 and parts[0] == "submissions":
                roots.add(parts[1])
            else:
                outside.append(name)
    reasons = []
    if outside:
        reasons.append("changes files outside one submissions/<root>/: " + ", ".join(clean(n, 80) for n in outside[:5])
                       + (f" and {len(outside) - 5} more" if len(outside) > 5 else ""))
    if len(roots) != 1:
        reasons.append(f"changes {len(roots)} roots under submissions/ (exactly one is allowed)"
                       + (": " + ", ".join(clean(r, 45) for r in sorted(roots)[:5]) if roots else ""))
    root = next(iter(roots)) if len(roots) == 1 else None
    if root is not None and not ROOT_RE.match(root):
        reasons.append(f"root name {clean(root, 45)!r} is not [a-z][a-z0-9-]{{0,39}}")
        root = None
    return root, reasons, bool(outside)


def _utf8(b):
    try:
        return b.decode("utf-8")
    except (UnicodeDecodeError, AttributeError):
        return None


def tree_rule(repo, sha, root):
    """(reasons, info) for `submissions/<root>` at `sha`. info: tree, notes, readme (bytes or None),
    files, bytes."""
    base = f"submissions/{root}"
    info = {"tree": repo.tree_of(sha, base), "notes": None, "readme": None, "files": 0, "bytes": 0}
    if info["tree"] is None:
        return [f"{base}/ does not exist at the head commit"], info
    reasons, blobs = [], {}
    caps = ENTRY_CAPS
    count, total = {"lean": 0, "prover": 0}, {"lean": 0, "prover": 0}
    for mode, typ, size, path in repo.ls_tree(sha, base):
        if not path.startswith(base + "/"):
            continue
        rel = path[len(base) + 1:]
        shown = clean(rel, 120)
        if MODES.get(mode) != typ:
            what = {"120000": "a symbolic link", "160000": "a submodule (gitlink)"}.get(mode, f"mode {mode}")
            reasons.append(f"{shown} is {what}; only regular files and directories are allowed")
            continue
        comps = rel.split("/")
        too_long = len(path.encode("utf-8", "surrogateescape")) > MAX_PATH
        if too_long or any(not COMPONENT_RE.match(c) or c in (".", "..") or c.lower().startswith(".git") for c in comps):
            reasons.append(f"file name {shown!r}: each part must match [A-Za-z0-9._+-]{{1,255}}, not start "
                           f"with .git, and the path be at most {MAX_PATH} bytes")
        if typ == "blob":
            info["files"] += 1
            info["bytes"] += size
            blobs[rel] = size
            top = comps[0] if len(comps) > 1 else ""
            if top in count:
                count[top] += 1
                total[top] += size
            if size > caps["file_bytes"]:
                reasons.append(f"{shown} has {size} bytes, above the cap file_bytes = {caps['file_bytes']}")
    count[""], total[""] = info["files"], info["bytes"]
    for k, name in (("", ""), ("lean", "lean_"), ("prover", "prover_")):
        where = f"{k}/" if k else "the root"
        if count[k] > caps[f"{name}files"]:
            reasons.append(f"{where} holds {count[k]} files, above the cap {name}files = {caps[name + 'files']}")
        if total[k] > caps[f"{name}bytes"]:
            reasons.append(f"{where} holds {total[k]} bytes, above the cap {name}bytes = {caps[name + 'bytes']}")
    if blobs.get("claim.json", 0) > caps["claim_bytes"]:
        reasons.append(f"claim.json has {blobs['claim.json']} bytes, above the cap claim_bytes = {caps['claim_bytes']}")

    def text(rel, required, cap=MAX_TEXT_BYTES):
        if rel not in blobs:
            if required:
                reasons.append(f"{rel} is missing")
            return None
        if blobs[rel] > cap:
            if required and rel != "claim.json":
                reasons.append(f"{rel} has {blobs[rel]} bytes (at most {cap})")
            return None
        return repo.blob(sha, f"{base}/{rel}", cap)

    claim = text("claim.json", True, caps["claim_bytes"])
    if claim is not None:
        try:
            ok = isinstance(json.loads(claim.decode("utf-8")), dict)
        except (ValueError, UnicodeDecodeError, RecursionError):
            ok = False
        if not ok:
            reasons.append("claim.json is not a JSON object")
    if "lean/Solution.lean" not in blobs:
        reasons.append("lean/Solution.lean is missing")
    if not any(r.startswith("prover/") and r.endswith(".s") and r.count("/") == 1 for r in blobs):
        reasons.append("prover/ holds no .s file")
    notes = text("NOTES.md", True)
    if notes is not None:
        if _utf8(notes) is None:
            reasons.append("NOTES.md is not UTF-8")
        elif not notes.strip():
            reasons.append("NOTES.md is empty")
        else:
            info["notes"] = notes
    readme = text("README.md", False)
    if readme is not None and _utf8(readme) is not None:
        info["readme"] = readme
    return reasons[:20], info


def notes_header(notes, own_pr):
    """(agent or None, builds_on) from the header lines `Agent: …` and `Builds on: #a, #b` among
    the first lines of NOTES.md (the first of each counts)."""
    agent, builds = None, None
    text = _utf8(notes) or ""
    for line in text.splitlines()[:HEADER_LINES]:
        m = HEADER_RE.match(line)
        if not m:
            continue
        key, val = m.group(1).lower(), m.group(2).strip().strip("*_").strip()
        if key == "agent" and agent is None:
            agent = clean(val, 100) or None
        elif key == "builds on" and builds is None:
            builds = []
            for n in re.findall(r"#([0-9]{1,7})\b", val):
                n = int(n)
                if 0 < n != own_pr and n not in builds:
                    builds.append(n)
            builds = builds[:20]
    return agent, builds or []
