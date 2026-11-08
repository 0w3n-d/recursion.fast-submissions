"""The workflow safety lint (advisory; standard library only; fail-closed in what it parses).

The hard guarantee is not here: the server's runner image has a job-started hook that refuses any
job whose GitHub-supplied event or workflow ref is not one of this repository's workflows on `main`
(or the core's `evaluate.yml` called from them), so a fork's `pull_request` workflow never runs on
the organiser's machine. This lint helps the owner spot a dangerous workflow before approving or
merging it; its known gaps (a variable holding `git`, an allowlist that rejects some harmless
fields) are accepted. Its aim: no workflow may run a job on the organiser's machine (an `rf-*` runner, or any runner that is not
an allowlisted GitHub-hosted label) for an event a fork or any GitHub user controls, and no
`pull_request_target` job may check out or name the pull request's head as code.

  python3 -I .github/bot/wfcheck.py [REPO_DIR]          the checkout's .github/workflows
  python3 -I .github/bot/wfcheck.py --git GIT_DIR REV   a commit's workflows, read as data
                                                        (a pull request's head, in pin-check)

Rules, for every `*.yml` and `*.yaml` directly under `.github/workflows`:

1. The file must parse with this module's YAML subset (block mappings and sequences at any
   consistent indentation, one-line flow collections, quoted and plain scalars, `|`/`>` block
   scalars); anything else (anchors, aliases, tags, multi-line flow or plain scalars, duplicate
   keys, tabs) is a failure, and so is a file without `on` or `jobs`.
2. Allowlisted triggers (`SAFE`): `pull_request_target`, `workflow_dispatch`, `schedule`, and
   `push` to `main` only (`branches: [main]`, no tags, no `branches-ignore`). Any other trigger is
   treated as fork-controlled.
3. A job is reachable from a fork-controlled trigger unless its `if:` is exactly
   `github.event_name == '<safe event>'`. A reachable job must have `runs-on` equal to one literal
   of `GITHUB_HOSTED`; any expression, list, mapping (runner group), `vars.` or label outside the
   allowlist is a failure. A reachable job-level `uses:` (a reusable workflow) is a failure unless
   it is in `ALLOWED_REUSABLE` (empty).
4. Every job that can run for an event other than `pull_request` (`main`'s workflow file with a
   write token: `pull_request_target`, `issue_comment`, dispatch, schedule, push, …) is held to an
   allowlist: every `${{ … }}` in `run:`, a step's `with:` and a `uses:` job's `with:` is one of
   `EXPR_ANY` (or literals joined by `||`, `&&`, `==`, `!=`), and in `env:` one of `EXPR_ENV`, which
   adds the pull request's fields as data; context names as written (mixed case, index syntax and
   functions fail). `actions/checkout` takes no `ref` but `${{ github.sha }}` (or a fixed
   `repository` at a fixed commit or a step's output), a literal `path`, nothing else; another
   action gets no `ref`, `repository` or `token` by expression; under `pull_request_target` a job
   may not be a reusable workflow; no `secrets: inherit`. A `run:` script may not make a working
   tree of, or run, fetched code (`git checkout`, `clone`, `switch`, `worktree`, …: a conservative
   textual check). Fetching `refs/pull/N/head` into a repository as data stays allowed: the intake
   reads pull requests that way.

Rule 4 also scans `runs-on` (no expression at all), `container` and `services` (refused),
`shell`, `working-directory` and `defaults`, and the workflow's own `env:`/`defaults:`; in code
positions (`run:`, a script action's `script:`, those fields) only constants are allowed, never
`env.`, `steps.` or `needs.` (they launder pull-request data); `actions/checkout` of another
repository only at a literal 40-hex commit; a double-quoted scalar with a backslash escape is
refused; files above 64 KiB each or 512 KiB in all are refused before parsing.

Threat model: workflows on `main` are written only by the owner, and submissions are never merged.
This lint guards against the organiser's own mistake and against a pull request that edits
workflows (pin-check's PR job, and the intake on any head touching `.github/`, `flows.intake`). It is
not a sandbox against a malicious organiser, and human review of every workflow change stays
required.
"""
import os
import re
import subprocess
import sys

SAFE = ("pull_request_target", "workflow_dispatch", "schedule", "push")
GITHUB_HOSTED = ("ubuntu-24.04", "ubuntu-latest", "ubuntu-22.04")
ALLOWED_REUSABLE = ()
ID = r"[A-Za-z0-9_-]+"
# rule 4: the `${{ … }}` shapes allowed in `run:`, `with:`, `env:` and a `uses:` job's `with:` of a job
# that can run for any event other than `pull_request`; context names exactly as written (lower case,
# dotted: `Github.event` or `github['event']` fail)
EXPR_ANY = (r"github\.(?:repository|run_id|run_attempt|sha|token|workspace|event_name)", r"secrets\.GITHUB_TOKEN",
            rf"inputs\.{ID}", rf"needs\.{ID}\.outputs\.{ID}", rf"steps\.{ID}\.outputs\.{ID}", r"runner\.temp",
            r"env\.[A-Za-z0-9_]+")
# in code (`run:`, a script action's `script:`, `runs-on`, `container`, `services`, `shell`,
# `working-directory`): constants only, never `env.`, `steps.` or `needs.` (they can carry pull-request
# data back in: pass data through `env:` and read shell variables)
EXPR_CODE = (r"github\.(?:repository|run_id|run_attempt|sha|token|workspace|event_name)", r"secrets\.GITHUB_TOKEN",
             rf"inputs\.{ID}", r"runner\.temp")
# the pull request's fields: only inside `env:`, where they reach a step as data
EXPR_ENV = EXPR_ANY + (r"github\.event\.pull_request(?:\.[a-z0-9_]+)+", r"github\.event\.number",
                       r"github\.(?:head_ref|base_ref)")
EXPR_RE = re.compile(r"\$\{\{(.*?)\}\}", re.S)
LITERAL_RE = re.compile(r"'[^']*'|true|false|null|[0-9]+")
# a conservative textual check on `run:` (not a decision procedure: human review of every workflow
# change stays required): no command that makes a working tree of, or runs, fetched code. Fetching
# `refs/pull/N/head` into a bare repository as data stays allowed (the intake reads pull requests so).
RUN_CODE_RE = re.compile(r"\bgit\b[^\n;&|]*?\s(?:checkout|switch|clone|worktree|restore|reset|archive|read-tree|"
                         r"checkout-index|stash|merge|am|apply|submodule|pull|show|cat-file|rebase|cherry-pick|revert)\b"
                         r"|\bgh\s+(?:pr\s+(?:checkout|diff)|repo\s+clone|api)\b|\|\s*(?:ba|z|k|da)?sh\b|\beval\b"
                         r"|\bsource\b|\bpatch\b|\bbase64\s+-d")
CHECKOUT_KEYS = {"ref", "repository", "path", "persist-credentials", "sparse-checkout", "fetch-depth"}
GUARD_RE = re.compile(r"github\.event_name == '([a-z_]+)'")


class Unparsed(Exception):
    pass


# ---- a fail-closed YAML subset -------------------------------------------------------------------
def _strip_comment(line):
    """The line without a trailing comment (a `#` at the start or after whitespace, outside quotes)."""
    q, out = None, []
    for k, c in enumerate(line):
        if q:
            if c == q:
                q = None
        elif c in "'\"" and (k == 0 or line[k - 1] in " \t:[{,-"):
            q = c
        elif c == "#" and (k == 0 or line[k - 1] in " \t"):
            break
        out.append(c)
    if q:
        raise Unparsed(f"an unterminated quoted scalar: {line.strip()[:80]}")
    return "".join(out).rstrip()


def _scalar(t):
    t = t.strip()
    if not t:
        return None
    if t[0] in "&*!|>@`%" or t.startswith(("? ", "--- ", "...")) or t in ("---", "?"):
        raise Unparsed(f"an unsupported construct: {t[:80]}")
    if t[0] == "'":
        if len(t) < 2 or t[-1] != "'":
            raise Unparsed(f"a quoted scalar does not end on its line: {t[:80]}")
        return t[1:-1].replace("''", "'")
    if t[0] == '"':
        if len(t) < 2 or t[-1] != '"':
            raise Unparsed(f"a quoted scalar does not end on its line: {t[:80]}")
        if "\\" in t:          # no YAML escapes (`\x24{{` would hide an expression)
            raise Unparsed(f"a backslash escape in a double-quoted scalar: {t[:80]}")
        return t[1:-1]
    if t[0] in "[{":
        v, rest = _flow(t, 0)
        if t[rest:].strip():
            raise Unparsed(f"text after a flow collection: {t[:80]}")
        return v
    if t[0] in "]}":
        raise Unparsed(f"an unbalanced flow collection: {t[:80]}")
    return t


def _flow(t, i):
    """A one-line flow collection from t[i]; (value, next index). `${{ … }}` is atomic."""
    close = "]" if t[i] == "[" else "}"
    out = [] if close == "]" else {}
    i += 1
    while True:
        while i < len(t) and t[i] == " ":
            i += 1
        if i >= len(t):
            raise Unparsed(f"a flow collection does not end on its line: {t[:80]}")
        if t[i] == close:
            return out, i + 1
        if t[i] in "[{":
            v, i = _flow(t, i)
            key = None
        else:
            j, depth, q = i, 0, None
            while j < len(t):
                c = t[j]
                if q:
                    if c == q:
                        q = None
                elif c in "'\"" and (j == i or t[j - 1] in " :"):
                    q = c
                elif t.startswith("${{", j):
                    depth += 1
                    j += 2
                elif t.startswith("}}", j) and depth:
                    depth -= 1
                    j += 1
                elif depth == 0 and c in ",]}":
                    break
                elif depth == 0 and c in "[{":
                    raise Unparsed(f"a nested flow collection inside a scalar: {t[:80]}")
                j += 1
            item = t[i:j].strip()
            i = j
            key = None
            if close == "}":
                m = re.match(r"^((?:\"[^\"]*\"|'[^']*'|[^:]+?))\s*:(?:\s+(.*))?$", item, re.S)
                if not m:
                    raise Unparsed(f"a flow mapping entry without a key: {item[:80]}")
                key, item = _scalar(m.group(1)), (m.group(2) or "")
                if item.startswith(("[", "{")):
                    raise Unparsed(f"a nested flow collection after a key: {t[:80]}")
            v = _scalar(item)
        if close == "]":
            out.append(v)
        else:
            if key is None or key in out:
                raise Unparsed(f"a flow mapping entry without a key, or a duplicate key: {t[:80]}")
            out[key] = v
        while i < len(t) and t[i] == " ":
            i += 1
        if i < len(t) and t[i] == ",":
            i += 1
        elif i < len(t) and t[i] == close:
            continue
        elif i >= len(t):
            raise Unparsed(f"a flow collection does not end on its line: {t[:80]}")
        else:
            raise Unparsed(f"an unexpected character in a flow collection: {t[:80]}")


KEY_RE = re.compile(r"^((?:\"[^\"]*\"|'[^']*'|[^\s\"'#\-?:\[\]{}][^:#]*?|-[^\s:#][^:#]*?))\s*:(?:\s+(.*)|)$")


def parse(text):
    """The document of `text` in the supported subset, or raises Unparsed."""
    raw = text.split("\n")
    lines = []
    for n, line in enumerate(raw, 1):
        if "\t" in line[:len(line) - len(line.lstrip())]:
            raise Unparsed(f"line {n}: a tab in the indentation")
        lines.append((n, line))
    pos = [0]

    def skip_blank():
        while pos[0] < len(lines) and not _strip_comment(lines[pos[0]][1]).strip():
            pos[0] += 1

    def indent(line):
        return len(line) - len(line.lstrip(" "))

    def block_scalar(parent_indent):
        out = []
        while pos[0] < len(lines):
            n, line = lines[pos[0]]
            if line.strip() and indent(line) <= parent_indent:
                break
            out.append(line.strip())
            pos[0] += 1
        return "\n".join(out)

    def value_after(rest, ind, n):
        """The value of a `key:` whose text after the colon is `rest`, at indentation `ind`."""
        rest = rest.strip() if rest else ""
        if rest in ("|", "|-", "|+", ">", ">-", ">+"):
            pos[0] += 1
            return block_scalar(ind)
        if rest:
            pos[0] += 1
            v = _scalar(rest)
            skip_blank()
            if pos[0] < len(lines) and indent(lines[pos[0]][1]) > ind:
                raise Unparsed(f"line {lines[pos[0]][0]}: a continued plain scalar or misplaced block")
            return v
        pos[0] += 1
        skip_blank()
        if pos[0] >= len(lines):
            return None
        nl = lines[pos[0]][1]
        ni = indent(nl)
        if ni > ind or (ni == ind and _strip_comment(nl).lstrip().startswith("- ")):
            return node(ni)
        return None

    def node(ind):
        skip_blank()
        n, line = lines[pos[0]]
        body = _strip_comment(line)
        if body.lstrip().startswith("- ") or body.strip() == "-":
            return seq(ind)
        return mapping(ind)

    def seq(ind):
        out = []
        while True:
            skip_blank()
            if pos[0] >= len(lines):
                return out
            n, line = lines[pos[0]]
            body = _strip_comment(line)
            if indent(line) != ind or not (body.lstrip().startswith("- ") or body.strip() == "-"):
                if indent(line) > ind:
                    raise Unparsed(f"line {n}: a misplaced line in a sequence")
                return out
            item = body.lstrip()[2:] if body.strip() != "-" else ""
            sub = ind + 2 + (len(item) - len(item.lstrip(" ")))
            item = item.strip()
            if not item:
                out.append(value_after("", ind, n))
            elif KEY_RE.match(item):
                # a mapping that starts on the dash's line: re-read it as a line at the item's column
                lines[pos[0]] = (n, " " * sub + item)
                out.append(mapping(sub))
            else:
                pos[0] += 1
                v = _scalar(item)
                skip_blank()
                if pos[0] < len(lines) and indent(lines[pos[0]][1]) > ind:
                    raise Unparsed(f"line {lines[pos[0]][0]}: a continued plain scalar in a sequence")
                out.append(v)

    def mapping(ind):
        out = {}
        while True:
            skip_blank()
            if pos[0] >= len(lines):
                return out
            n, line = lines[pos[0]]
            if indent(line) < ind:
                return out
            if indent(line) > ind:
                raise Unparsed(f"line {n}: unexpected indentation")
            body = _strip_comment(line).strip()
            if body.startswith("- "):
                return out
            m = KEY_RE.match(body)
            if not m:
                raise Unparsed(f"line {n}: not a `key: value` line: {body[:80]}")
            key = _scalar(m.group(1))
            if not isinstance(key, str) or key in out:
                raise Unparsed(f"line {n}: a duplicate or non-string key {m.group(1)[:40]}")
            out[key] = value_after(m.group(2), ind, n)

    skip_blank()
    if pos[0] >= len(lines):
        raise Unparsed("an empty file")
    first = lines[pos[0]][1]
    if indent(first) != 0:
        raise Unparsed("the document does not start at column 0")
    doc = node(0)
    skip_blank()
    if pos[0] < len(lines):
        raise Unparsed(f"line {lines[pos[0]][0]}: text after the document")
    return doc


# ---- the rules ------------------------------------------------------------------------------------
def triggers(doc):
    """{event: config} of the workflow, or raises Unparsed."""
    on = doc.get("on", doc.get(True)) if isinstance(doc, dict) else None
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list) and all(isinstance(x, str) for x in on):
        return {x: None for x in on}
    if isinstance(on, dict):
        return on
    raise Unparsed("no `on:` triggers")


def push_is_main_only(cfg):
    return (isinstance(cfg, dict) and cfg.get("branches") == ["main"]
            and set(cfg) <= {"branches", "paths", "paths-ignore"})


def expr_ok(expr, atoms):
    """True if `expr` (inside `${{ }}`) is allowed atoms and literals joined by `||`, `&&`, `==`, `!=`."""
    toks = re.split(r"\s*(\|\||&&|==|!=)\s*", expr.strip())
    return len(toks) % 2 == 1 and all(LITERAL_RE.fullmatch(t) or any(re.fullmatch(a, t) for a in atoms)
                                      for t in toks[::2])


def bad_exprs(value, atoms):
    """The `${{ … }}` in `value` (a string, or a mapping or list of them) that are not allowed."""
    if isinstance(value, dict):
        return [x for v in value.values() for x in bad_exprs(v, atoms)]
    if isinstance(value, list):
        return [x for v in value for x in bad_exprs(v, atoms)]
    t = "" if value is None else str(value)
    found = EXPR_RE.findall(t)
    if t.count("${{") != len(found):
        return [t[:60]]
    return [e.strip()[:80] for e in found if not expr_ok(e, atoms)]


def rule4(where, j, prt):
    """Rule 4 for a job that can run for an event other than `pull_request` (`main`'s workflow, a
    write token): the expression allowlist, the checkout of the base commit only, no reusable
    workflow under `pull_request_target`, no command that runs fetched code."""
    out = []
    if "${{" in repr(j.get("runs-on")):
        out.append(f"{where}: runs-on holds an expression")
    for key in ("container", "services"):
        if key in j:            # none is used: refused outright
            out.append(f"{where}: {key} is not allowed")
    for e in bad_exprs((j.get("defaults") or {}) if isinstance(j.get("defaults"), dict) else j.get("defaults"), EXPR_CODE):
        out.append(f"{where}: defaults expression `{e}` is not allowed")
    for e in bad_exprs(j.get("env"), EXPR_ENV):
        out.append(f"{where}: env expression `{e}` is not allowed")
    if "uses" in j:
        if prt:
            out.append(f"{where}: a reusable workflow under pull_request_target")
        for e in bad_exprs(j.get("with"), EXPR_ANY) + bad_exprs(j.get("secrets"), EXPR_ANY):
            out.append(f"{where}: with expression `{e}` is not allowed")
        if j.get("secrets") == "inherit":
            out.append(f"{where}: secrets: inherit")
    for k, st in enumerate(j.get("steps") or []):
        if not isinstance(st, dict):
            out.append(f"{where}: step {k} is not a mapping")
            continue
        w = st.get("with")
        if w is not None and not isinstance(w, dict):
            out.append(f"{where}: step {k}: with is not a mapping")
            w = {}
        w = w or {}
        for e in bad_exprs(st.get("env"), EXPR_ENV):
            out.append(f"{where}: step {k}: env expression `{e}` is not allowed")
        code = {x: w[x] for x in ("script",) if x in w}
        for e in (bad_exprs(st.get("run"), EXPR_CODE) + bad_exprs(code, EXPR_CODE)
                  + bad_exprs({x: v for x, v in w.items() if x not in code}, EXPR_ANY)
                  + bad_exprs({x: st.get(x) for x in ("shell", "working-directory")}, EXPR_CODE)):
            out.append(f"{where}: step {k}: expression `{e}` is not allowed (pass the value through env: and read a "
                       "shell variable)")
        if isinstance(st.get("run"), str) and RUN_CODE_RE.search(st["run"]):
            out.append(f"{where}: step {k}: run: makes a working tree of, or runs, fetched code")
        uses = st.get("uses") if isinstance(st.get("uses"), str) else ""
        if uses.lower().startswith("actions/checkout@"):
            repo, ref, path = w.get("repository"), w.get("ref"), w.get("path")
            if set(w) - CHECKOUT_KEYS:
                out.append(f"{where}: step {k}: checkout inputs {sorted(set(w) - CHECKOUT_KEYS)}")
            if not (path is None or (isinstance(path, str) and "${{" not in path and ".." not in path)):
                out.append(f"{where}: step {k}: checkout path {path!r}")
            if repo is None:
                if not (ref is None or (isinstance(ref, str) and ref.strip() == "${{ github.sha }}")):
                    out.append(f"{where}: step {k}: checkout of a ref other than the base commit ({str(ref)[:60]})")
            elif not (isinstance(repo, str) and "${{" not in repo and re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo)
                      and isinstance(ref, str) and re.fullmatch(r"[0-9a-f]{40}", ref.strip())):
                out.append(f"{where}: step {k}: checkout of {str(repo)[:60]} at {str(ref)[:60]}: only a fixed "
                           "repository at a literal 40-hex commit")
        elif uses and any(isinstance(w.get(x), str) and "${{" in w[x] for x in ("ref", "repository", "token")):
            out.append(f"{where}: step {k}: an action given a ref, repository or token by expression")
    return out


def check_doc(name, doc):
    problems = []
    if not isinstance(doc, dict) or not isinstance(doc.get("jobs"), dict) or not doc["jobs"]:
        return [f"{name}: no `jobs:` mapping"]
    on = triggers(doc)
    unsafe = sorted(e for e, cfg in on.items() if e not in SAFE or (e == "push" and not push_is_main_only(cfg)))
    for job, j in doc["jobs"].items():
        where = f"{name}: job {job}"
        if not isinstance(j, dict):
            problems.append(f"{where}: not a mapping")
            continue
        cond = j.get("if")
        m = GUARD_RE.fullmatch(cond.strip()) if isinstance(cond, str) else None
        guarded = m.group(1) if m and m.group(1) in on and m.group(1) not in unsafe else None
        if unsafe and not guarded:
            ro = j.get("runs-on")
            if "uses" in j:
                if j["uses"] not in ALLOWED_REUSABLE:
                    problems.append(f"{where}: a reusable workflow ({j['uses']}) for the fork-controlled event(s) {unsafe}")
            elif not (isinstance(ro, str) and ro in GITHUB_HOSTED):
                problems.append(f"{where}: runs-on {ro!r} is not a GitHub-hosted literal {list(GITHUB_HOSTED)}, "
                                f"and the job can run for the fork-controlled event(s) {unsafe}")
        # rule 4 applies wherever the job can run for an event other than `pull_request` (whose
        # token is read-only); a job guarded to `pull_request` alone is exempt from it
        ev4 = [m.group(1)] if m and m.group(1) in on else list(on)
        if any(e != "pull_request" for e in ev4):
            problems += rule4(where, j, "pull_request_target" in ev4)
    if any(e != "pull_request" for e in on):     # the workflow's own env: and defaults: reach those jobs
        problems += [f"{name}: workflow env expression `{e}` is not allowed" for e in bad_exprs(doc.get("env"), EXPR_ENV)]
        problems += [f"{name}: workflow defaults expression `{e}` is not allowed" for e in bad_exprs(doc.get("defaults"), EXPR_CODE)]
    return problems


def check_text(name, text):
    """The problems of one workflow file (a file that does not parse is one)."""
    try:
        return check_doc(name, parse(text))
    except Unparsed as e:
        return [f"{name}: not checkable ({e}): a workflow must be written in the checked subset"]
    except RecursionError:
        return [f"{name}: not checkable (nested too deeply)"]


def is_workflow(fn):
    """A workflow file name, matched case-insensitively and ignoring surrounding whitespace (`bad.YML`,
    `bad.yml `): fail-closed, without guessing which of them GitHub runs."""
    return fn.strip().lower().endswith((".yml", ".yaml"))


MAX_FILE, MAX_TOTAL = 64 << 10, 512 << 10      # a workflow larger than this is refused unparsed


def check_dir(repo_dir):
    d = os.path.join(repo_dir, ".github", "workflows")
    files = sorted(f for f in os.listdir(d) if is_workflow(f) and os.path.isfile(os.path.join(d, f))) if os.path.isdir(d) else []
    if not files:
        return ["no workflow files found"]
    sizes = {f: os.path.getsize(os.path.join(d, f)) for f in files}
    if sum(sizes.values()) > MAX_TOTAL or max(sizes.values()) > MAX_FILE:
        return [f"the workflows are too large to check ({sum(sizes.values())} bytes; at most {MAX_FILE} per file, "
                f"{MAX_TOTAL} in all)"]
    out = []
    for f in files:
        with open(os.path.join(d, f), encoding="utf-8", errors="replace") as fh:
            out += check_text(f, fh.read())
    return out


def check_git(git_dir, rev):
    """The workflows of commit `rev`, read as data (`git ls-tree` / `git cat-file`)."""
    r = subprocess.run(["git", "--git-dir", git_dir, "ls-tree", "-z", rev, ".github/workflows/"], capture_output=True)
    if r.returncode:
        return [f"cannot list the workflows of {rev}"]
    out, n, blobs = [], 0, []
    for ent in r.stdout.split(b"\0"):
        if not ent:
            continue
        meta, _, path = ent.partition(b"\t")
        mode, typ, oid = meta.decode().split()
        fn = os.path.basename(path.decode("utf-8", "replace"))
        if not is_workflow(fn):
            continue
        n += 1
        if typ != "blob" or mode not in ("100644", "100755"):
            out.append(f"{fn}: not a regular file ({mode})")
            continue
        size = subprocess.run(["git", "--git-dir", git_dir, "cat-file", "-s", oid], capture_output=True, text=True)
        blobs.append((fn, oid, int(size.stdout.strip()) if size.returncode == 0 and size.stdout.strip().isdigit() else -1))
    if any(sz < 0 for _, _, sz in blobs):
        return out + [f"{fn}: unreadable" for fn, _, sz in blobs if sz < 0]
    total = sum(sz for _, _, sz in blobs)
    if blobs and (total > MAX_TOTAL or max(sz for _, _, sz in blobs) > MAX_FILE):
        # sized before any parse: an outsider's huge workflow costs the intake nothing
        return out + [f"the workflows are too large to check ({total} bytes; at most {MAX_FILE} per file, {MAX_TOTAL} in all)"]
    for fn, oid, _ in blobs:
        blob = subprocess.run(["git", "--git-dir", git_dir, "cat-file", "blob", oid], capture_output=True)
        out += check_text(fn, blob.stdout.decode("utf-8", "replace")) if blob.returncode == 0 else [f"{fn}: unreadable"]
    return out if n else ["no workflow files found"]


def main():
    a = sys.argv[1:]
    problems = check_git(a[1], a[2]) if a[:1] == ["--git"] else check_dir(a[0] if a else ".")
    for p in problems:
        print(f"wfcheck: {p}")
    if not problems:
        print("wfcheck: OK, no job reaches the organiser's runners from a fork-controlled event")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
