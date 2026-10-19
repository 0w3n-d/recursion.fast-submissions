#!/usr/bin/env bash
# Build-effort measurement of the spartan-chain entry (proof-effort / build-time report).
#
# On a FRESH scratch copy of the core clone (committed tree of its branch, plus its working
# lakefile with the SpartanChain library) and a snapshot of this root's *.lean files:
#   1. builds the core libraries the entry imports (untimed warm-up, logged);
#   2. cold full build of the entry: `lake build SpartanChain` (default -j), wall time + peak RSS;
#   3. every module alone, in dependency order: `lake env lean <M>.lean` (its imports already
#      built by step 2), wall time + peak RSS (`/usr/bin/time -v`);
#   4. code lines per file (`.contract/scripts/loc.py`), components, copied-vs-fresh lines;
# and writes docs/snark-baseline/reports/measurements.md and raw logs under
# logs/spartan-chain/measure/<stamp>/.
#
# The shared package tree is only symlinked (read-only); nothing in the core clone or this root
# is written. Every Lean command runs under a memory-capped systemd scope and a timeout.
#
# Environment overrides: CORE (core clone), PKGS (prebuilt packages), SCRATCH (scratch dir),
# MEM (memory cap, default 16G), TMO (per-command timeout in seconds, default 7200).
set -u
ROOT=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$ROOT/../.." && pwd)
# `measure.sh --report <logdir>` regenerates the report from an existing run's logs.
if [ "${1:-}" = "--report" ]; then REPORT_ONLY=1; LOG=$(cd "$2" && pwd); else REPORT_ONLY=0; fi
CORE=${CORE:-/home/devops/Verified-zkEVM/rf-core-sc}
PKGS=${PKGS:-/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages}
STAMP=$(date +%Y%m%d-%H%M%S)
[ "$REPORT_ONLY" = 1 ] || LOG=$REPO/logs/spartan-chain/measure/$STAMP
SCR=${SCRATCH:-/tmp/spartan-measure-$STAMP}
MEM=${MEM:-16G}
TMO=${TMO:-7200}
LIMIT=(systemd-run --user --scope -p "MemoryMax=$MEM" --quiet --)
mkdir -p "$LOG"

machine() {  # $1: label
  { echo "== $1 $(date -Is)"; uptime; } >> "$LOG/machine.txt"
}

if [ "$REPORT_ONLY" = 0 ]; then
mkdir -p "$SCR"
# ---- 0. Machine and snapshot -------------------------------------------------------------
{
  echo "date: $(date -Is)"; echo "host: $(hostname)"; echo "nproc: $(nproc)"
  grep -m1 'model name' /proc/cpuinfo; free -g | head -2
  echo "core: $CORE @ $(git -C "$CORE" rev-parse HEAD) ($(git -C "$CORE" branch --show-current))"
  echo "toolchain: $(cat "$CORE/lean-toolchain")"; echo "mem cap: $MEM, timeout: ${TMO}s"
} > "$LOG/env.txt"
machine start

git -C "$CORE" archive HEAD | tar -x -C "$SCR"
cp "$CORE/lakefile.toml" "$SCR/lakefile.toml"
mkdir -p "$SCR/.lake" "$SCR/SpartanChainRoot"
ln -s "$PKGS" "$SCR/.lake/packages"
cp "$ROOT"/SpartanChain*.lean "$SCR/SpartanChainRoot/"
(cd "$SCR/SpartanChainRoot" && sha256sum SpartanChain*.lean) > "$LOG/snapshot.sha256"
mkdir -p "$LOG/snapshot" && cp "$SCR"/SpartanChainRoot/SpartanChain*.lean "$LOG/snapshot/"
mods=$(ls "$SCR/SpartanChainRoot" | sed -n 's/^\(SpartanChain[A-Za-z0-9]*\)\.lean$/"\1"/p' | paste -sd, -)
python3 - "$SCR/lakefile.toml" "$mods" <<'PY'
import re, sys
p, mods = sys.argv[1], sys.argv[2]
s = open(p).read()
s = re.sub(r'(name = "SpartanChain"\nsrcDir = "SpartanChainRoot"\nroots = )\[[^\]]*\]',
           lambda m: m.group(1) + '[' + mods + ']', s)
open(p, 'w').write(s)
PY

cd "$SCR" || exit 1

# ---- 1. Core libraries (warm-up, not the entry) ------------------------------------------
machine core-build
/usr/bin/time -v -o "$LOG/core.time" timeout "$TMO" "${LIMIT[@]}" \
  lake build RecursionFastContract RecursionFastLibrary > "$LOG/core.log" 2>&1
echo "core build exit $?" >> "$LOG/env.txt"

# ---- 2. Cold full build of the entry -----------------------------------------------------
machine full-build
/usr/bin/time -v -o "$LOG/full.time" timeout "$TMO" "${LIMIT[@]}" \
  lake build SpartanChain > "$LOG/full.log" 2>&1
echo "full build exit $?" >> "$LOG/env.txt"

# ---- 3. Every module alone, in dependency order ------------------------------------------
python3 - "$SCR/SpartanChainRoot" > "$LOG/order.txt" <<'PY'
import os, re, sys
d = sys.argv[1]
mods = sorted(f[:-5] for f in os.listdir(d) if re.fullmatch(r'SpartanChain[A-Za-z0-9]*\.lean', f))
deps = {}
for m in mods:
    deps[m] = {i for i in re.findall(r'^import\s+(\S+)', open(os.path.join(d, m + '.lean')).read(), re.M)
               if i in mods}
done, order = set(), []
while len(order) < len(mods):
    ready = [m for m in mods if m not in done and deps[m] <= done]
    if not ready:  # a cycle: emit the rest as is
        ready = [m for m in mods if m not in done]
    for m in ready:
        done.add(m); order.append(m)
print('\n'.join(order))
PY
machine modules
mkdir -p "$LOG/modules"
while read -r m; do
  /usr/bin/time -v -o "$LOG/modules/$m.time" timeout "$TMO" "${LIMIT[@]}" \
    lake env lean "SpartanChainRoot/$m.lean" > "$LOG/modules/$m.log" 2>&1
  echo "$m $?" >> "$LOG/modules/status.txt"
done < "$LOG/order.txt"
machine end
fi

# ---- 4. Lines, components, copied lines, report ------------------------------------------
(cd "$LOG/snapshot" && python3 "$REPO/.contract/scripts/loc.py" SpartanChain*.lean) > "$LOG/loc.txt"
python3 - "$LOG" "$LOG/snapshot" "$REPO/docs/snark-baseline/reports/measurements.md" <<'PY'
import os, re, sys, json
log, src, out = sys.argv[1:4]

def tparse(path):
    wall = rss = None
    try:
        for line in open(path):
            if 'Elapsed (wall clock)' in line:
                v = line.rsplit(': ', 1)[1].strip().split(':')
                wall = sum(float(x) * 60 ** i for i, x in enumerate(reversed(v)))
            elif 'Maximum resident set size' in line:
                rss = int(line.rsplit(': ', 1)[1]) / 1024
    except FileNotFoundError:
        pass
    return wall, rss

loc = {}
for line in open(os.path.join(log, 'loc.txt')):
    p = line.split()
    if p and p[0].endswith('.lean'):
        loc[os.path.basename(p[0])[:-5]] = int(p[4])

def code_lines(lines):
    """loc.py's rule on a list of lines: code lines (outside comments)."""
    depth = code = 0
    for line in lines:
        s = line.strip(); has = False; i = 0
        while i < len(s):
            if depth > 0:
                if s.startswith('-/', i): depth -= 1; i += 2
                elif s.startswith('/-', i): depth += 1; i += 2
                else: i += 1
            else:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('--', i): break
                else:
                    if not s[i].isspace(): has = True
                    i += 1
        code += has
    return code

copied = {}
for m in loc:
    text = open(os.path.join(src, m + '.lean')).read().splitlines()
    head = '\n'.join(text[:40])
    if re.search(r'Provenance:\s*copied from leanerVM', head):
        copied[m] = ('leanerVM, whole file (modified)', code_lines(text))
    elif re.search(r'Provenance:\s*copied from `submissions/baseline', head):
        copied[m] = ('S2a baseline entry', code_lines(text))
    else:
        sec, inside, n = [], False, 0
        for line in text:
            if re.match(r'\s*section Copied', line): inside = True; continue
            if re.match(r'\s*end Copied', line): inside = False; continue
            if inside: sec.append(line)
        if sec:
            copied[m] = ('leanerVM, `section Copied*`', code_lines(sec))

def component(m):
    n = m[len('SpartanChain'):]
    if n.endswith('Controls') or n in ('', 'Kat', 'Run', 'Submission', 'Solution', 'Bench', 'Final'):
        return 'submission / controls / KAT / run'
    if n.startswith('Soundness'):
        return 'soundness (Defs/KS/Final/Spartan/PCS/Log/Chain)'
    if n.startswith('Field'):
        return 'field'
    if n.startswith(('MLE', 'Sumcheck', 'RingSwitch')):
        return 'algebra / sumcheck / ring switching'
    if n.startswith(('RS', 'Proximity', 'PCSBounds')):
        return 'RS / proximity / PCS bounds'
    if n.startswith(('Blake2s', 'Chain')):
        return 'BLAKE2s circuit + chain'
    if n.startswith(('Oracle', 'Merkle', 'Transcript')):
        return 'Merkle / transcript / oracle'
    if n.startswith(('Ligero', 'Spartan', 'Verifier', 'Prover', 'Decode', 'Completeness')):
        return 'protocol (Ligero/Spartan/Verifier/Prover/Decode)'
    return 'other'

status = {}
for line in open(os.path.join(log, 'modules', 'status.txt')):
    m, c = line.split(); status[m] = int(c)
order = [l.strip() for l in open(os.path.join(log, 'order.txt')) if l.strip()]
rows = []
for m in order:
    w, r = tparse(os.path.join(log, 'modules', m + '.time'))
    rows.append(dict(module=m, component=component(m), wall=w, rss=r, code=loc.get(m, 0),
                     ok=status.get(m) == 0, copied=copied.get(m, (None, 0))))
full_w, full_r = tparse(os.path.join(log, 'full.time'))
core_w, core_r = tparse(os.path.join(log, 'core.time'))
env = open(os.path.join(log, 'env.txt')).read()
full_log = open(os.path.join(log, 'full.log'), errors='replace').read()
full_exit = re.search(r'full build exit (\d+)', env)
full_ok = full_exit is not None and full_exit.group(1) == '0'
full_fail = sorted(set(re.findall(r'✖ \[\d+/\d+\] Building (\S+)', full_log)))
mach = open(os.path.join(log, 'machine.txt')).read()
json.dump(dict(rows=rows, full=[full_w, full_r], core=[core_w, core_r]),
          open(os.path.join(log, 'summary.json'), 'w'), indent=1)

f = lambda x, d=1: '—' if x is None else f'{x:.{d}f}'
L = []
L.append('# Measurements: build effort of the `spartan-chain` entry\n')
L.append('Generated by `submissions/spartan-chain/measure.sh`; raw logs: `logs/spartan-chain/measure/'
         + os.path.basename(log) + '/`.\n')
L.append('**The machine is shared.** Every time and memory figure is an upper bound: other jobs ran at '
         'the same time (load averages below). Lean runs under `systemd-run --user --scope -p MemoryMax=…`.\n')
L.append('```\n' + env.strip() + '\n```\n')
L.append('Load during the run (`uptime` at each phase):\n\n```\n' + mach.strip() + '\n```\n')
L.append('## Totals\n')
tot_code = sum(r['code'] for r in rows)
tot_copy = sum(r['copied'][1] for r in rows)
sum_w = sum(r['wall'] or 0 for r in rows)
max_r = max((r['rss'] or 0) for r in rows) if rows else 0
L.append('| quantity | value |\n|---|---|')
L.append(f'| modules | {len(rows)} ({sum(not r["ok"] for r in rows)} failed to check) |')
L.append(f'| code lines (`loc.py`) | {tot_code} |')
L.append(f'| of which copied (provenance) | {tot_copy} |')
L.append(f'| written fresh | {tot_code - tot_copy} |')
L.append(f'| core libraries warm-up (not the entry), wall | {f(core_w)} s |')
L.append(f'| **cold full build of the entry** (`lake build SpartanChain`, default `-j`), wall | **{f(full_w)} s** |')
L.append(f'| full build status | {"complete" if full_ok else "INCOMPLETE (exit " + (full_exit.group(1) if full_exit else "?") + "; failed: " + ", ".join(full_fail) + ")"} |')
L.append(f'| peak RSS of the full build (largest single process) | {f(full_r, 0)} MiB |')
L.append(f'| sum of per-module check times (sequential) | {f(sum_w)} s |')
L.append(f'| largest per-module peak RSS | {f(max_r, 0)} MiB |')
floor = min((r['wall'] for r in rows if r['wall']), default=None)
L.append(f'| per-module floor (import loading; the smallest module time) | {f(floor)} s |\n')
L.append('## By component\n')
L.append('| component | modules | code lines | copied | check time (s, sum) | peak RSS (MiB, max) |\n|---|---|---|---|---|---|')
comps = {}
for r in rows:
    c = comps.setdefault(r['component'], dict(n=0, code=0, copy=0, w=0.0, rss=0.0))
    c['n'] += 1; c['code'] += r['code']; c['copy'] += r['copied'][1]
    c['w'] += r['wall'] or 0; c['rss'] = max(c['rss'], r['rss'] or 0)
for k in sorted(comps, key=lambda k: -comps[k]['w']):
    c = comps[k]
    L.append(f"| {k} | {c['n']} | {c['code']} | {c['copy']} | {c['w']:.1f} | {c['rss']:.0f} |")
L.append('\n## By module (dependency order)\n')
L.append('| module | component | code lines | copied | check time (s) | peak RSS (MiB) | status |\n|---|---|---|---|---|---|---|')
for r in rows:
    cp = f"{r['copied'][1]} ({r['copied'][0]})" if r['copied'][0] else '0'
    L.append(f"| `{r['module']}` | {r['component']} | {r['code']} | {cp} | {f(r['wall'])} | "
             f"{f(r['rss'], 0)} | {'ok' if r['ok'] else 'FAILED'} |")
L.append('\n## Method\n')
L.append('- Per-module time is `lake env lean <M>.lean` with every import already built (step 2), so it is the '
         'module\'s own elaboration and kernel check, not its dependencies. The full build is the parallel '
         'cold build of all entry modules (the core libraries and the shared packages are prebuilt).')
L.append('- Every per-module time includes loading the imported `.olean` files (a few seconds; the floor '
         'row above), so small modules are dominated by it.')
L.append('- A FAILED module (the entry is still changing) is timed up to its error; modules that import it '
         'were checked against the previous build products of step 2 only if those exist.')
L.append('- Peak RSS is `/usr/bin/time -v`\'s maximum resident set size (the largest single process).')
L.append('- Copied lines: whole files whose header says "Provenance: copied from leanerVM" (modified copies) '
         'or from the S2a baseline entry, and `section Copied*` blocks; counted with `loc.py`\'s code-line rule. '
         'Everything else is written for this entry.')
notes = os.path.join(log, 'notes.md')
if os.path.exists(notes):
    L.append('\n## Notes on this run\n')
    L.append(open(notes).read().strip())
open(out, 'w').write('\n'.join(L) + '\n')
print('wrote', out)
PY
echo "logs: $LOG"
