#!/usr/bin/env bash
# The baseline entry's end-to-end check (BASELINE-TASK §7, §9; the v2 baseline's scripts/check.sh is
# the model). Nothing is built or written in `.contract`, and the organiser-side material (the v3
# challenge stub, its renderer, the local proof-half harness, the scratch setup) is not in this
# root: it comes from a clone of the core at the pin plus the interim branch CORE_BRANCH of
# CORE_REPO (scripts/render-challenge.py, RecursionFast/Challenge/V3.lean.in,
# scripts/harness-local.sh, scripts/setup-scratch.sh), until stage S3 provides them.
#
#   submissions/baseline/check.sh            image, hygiene, source rule, build, render, solution,
#                                            challenge, axioms, leanchecker, negative claims, smoke,
#                                            line counts
#   HARNESS=1 submissions/baseline/check.sh  also the proof half of the harness
#                                            (scripts/harness-local.sh of a clean organiser clone,
#                                            with an allowlist and olean manifest generated from it)
#
# CORE, ORG: the scratch clones (defaults logs/V3-S2/core-interim, logs/V3-S2/org-interim), cloned
# from CORE_REPO (default /home/devops/Verified-zkEVM/rf-core-s2a) at CORE_BRANCH (default
# v3/s2-interim-harness) when absent; they may differ from the pin only in the interim files.
# LOGDIR: where the logs go (default logs/V3-S2/check-<UTC time>, never overwritten). TIMEOUT:
# seconds per build or Lean run (default 3600).
set -euo pipefail
B=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$B/../.." && pwd); C=$REPO/.contract
L=${LOGDIR:-$REPO/logs/V3-S2/check-$(date -u +%Y%m%dT%H%M%SZ)}
[[ ! -e "$L" ]] || { echo "check: $L exists; logs are never overwritten" >&2; exit 2; }
mkdir -p "$L"; L=$(cd "$L" && pwd); echo "logs: $L"
CORE=${CORE:-$REPO/logs/V3-S2/core-interim}; ORG=${ORG:-$REPO/logs/V3-S2/org-interim}
CORE_REPO=${CORE_REPO:-/home/devops/Verified-zkEVM/rf-core-s2a}; CORE_BRANCH=${CORE_BRANCH:-v3/s2-interim-harness}
TIMEOUT=${TIMEOUT:-3600}; export TIMEOUT
PIN=$(git -C "$REPO" ls-tree HEAD .contract | awk '{print $3}'); export PIN
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
TIME=(/usr/bin/time -f "%e s wall, %M KB max")
# A clone of the core at CORE_BRANCH (created if absent); it must contain the pin.
clone() {
  [[ -d "$1/.git" ]] || git clone -q -b "$CORE_BRANCH" "$CORE_REPO" "$1"
  git -C "$1" merge-base --is-ancestor "$PIN" HEAD || { echo "check: $1 does not contain the pin $PIN" >&2; exit 1; }
}
STUB=RecursionFast/Challenge/V3.lean.in

echo "== 1. extractor image"
if command -v riscv64-unknown-elf-as > /dev/null; then
  "$B/build-extractor.sh" "$T"
  cmp "$T/extractor.bin" "$B/extractor.bin" && cmp "$T/extractor.data" "$B/extractor.data"
  cmp "$B/extractor.bin" "$C/tests/asm/proofwords.bin"
  echo "extractor.bin reassembled byte-identically; equal to the core's tests/asm/proofwords.bin"
else
  echo "riscv64-unknown-elf-as not installed: image not reassembled"
fi | tee "$L/image.log"

echo "== 2. hygiene"
python3 -I - "$B"/*.lean <<'PY' | tee "$L/hygiene.log"
import re, sys
bad = re.compile(r'\b(sorry|admit|native_decide|implemented_by|extern|csimp|axiom|unsafe|partial|opaque)\b'
                 r'|set_option\s+(maxRecDepth|maxHeartbeats)')
hits = []
for p in sys.argv[1:]:
    s = re.sub(r'/-.*?-/', '', open(p).read(), flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    hits += [f"{p}: {l.strip()}" for l in s.split('\n') if bad.search(l)]
print("\n".join(hits) if hits else "hygiene OK: no sorry/admit/native_decide/implemented_by/extern/csimp/axiom/"
      "unsafe/partial/opaque/local limits")
sys.exit(1 if hits else 0)
PY

echo "== 3. source rule (the core's scripts/source-rule.py on the root)"
python3 -I "$C/scripts/source-rule.py" "$B" 2>&1 | tee "$L/source-rule.log"

echo "== 4. build (scratch core at the pin, then a clean rebuild of the entry)"
clone "$CORE"
"${TIME[@]}" "$CORE/scripts/setup-scratch.sh" entry "$B" BaselineV3Run 2>&1 | tee "$L/setup-core.log"
rm -f "$CORE"/.lake/build/lib/lean/BaselineV3*.* "$CORE"/.lake/build/ir/BaselineV3*.* "$CORE/.lake/build/bin/entry-run"
(cd "$CORE" && "${TIME[@]}" timeout "$TIMEOUT" lake build EntryScratch entry-run) 2>&1 \
  | grep -E "BaselineV3|error|warning|s wall|Build completed" | tee "$L/build-entry.log"
grep -q "Build completed successfully" "$L/build-entry.log" || { echo "entry build FAILED"; exit 1; }
! grep -qE "warning: .*BaselineV3" "$L/build-entry.log" || { echo "the entry's modules have warnings"; exit 1; }

echo "== 5. render the organiser's challenge stub with claim.json; make the solution; it equals the committed one"
python3 -I "$CORE/scripts/render-challenge.py" "$CORE/$STUB" "$B/claim.json" "$L/BaselineV3Challenge.lean"
python3 -I "$B/make-solution.py" "$L/BaselineV3Challenge.lean" "$T/BaselineV3Solution.lean"
cmp "$T/BaselineV3Solution.lean" "$B/BaselineV3Solution.lean" \
  && echo "BaselineV3Solution.lean = make-solution.py(render(V3.lean.in, claim.json))" | tee "$L/solution.log"

echo "== 6. the challenge elaborates with exactly its two sorry placeholders"
(cd "$CORE" && timeout "$TIMEOUT" lake env lean "$L/BaselineV3Challenge.lean") > "$L/challenge.log" 2>&1 || true
cat "$L/challenge.log"
[ "$(grep -c "declaration uses \`sorry\`" "$L/challenge.log")" = 2 ] && [ "$(grep -c "error" "$L/challenge.log" || true)" = 0 ] \
  || { echo "challenge: expected exactly the two sorry placeholders"; exit 1; }

echo "== 7. axiom audit of every declaration of the entry"
{
  printf 'import BaselineV3Solution\nimport BaselineV3Controls\nimport BaselineV3Run\n'
  echo "#print axioms RecursionFast.Challenge.certified"
  echo "#print axioms RecursionFast.Challenge.submission"
  for f in BaselineV3 BaselineV3Controls BaselineV3Run; do
    ns=$(grep -m1 "^namespace" "$B/$f.lean" | awk '{print $2}')
    grep -E "^(theorem|def|abbrev) " "$B/$f.lean" | awk '{print $2}' \
      | while read -r n; do echo "#print axioms $ns.$n"; done
  done
  echo "#print axioms main"
} | awk '!seen[$0]++' > "$T/Axioms.lean"
(cd "$CORE" && timeout "$TIMEOUT" lake env lean "$T/Axioms.lean") 2>&1 | tee "$L/axioms.log"
n=$(grep -c "axioms" "$T/Axioms.lean"); m=$(grep -cE "depends on axioms|does not depend on any axioms" "$L/axioms.log" || true)
[ "$n" = "$m" ] || { echo "axiom audit: $m answers for $n declarations"; exit 1; }
if grep -vE "depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$|does not depend on any axioms$" "$L/axioms.log"; then
  echo "axiom audit FAILED"; exit 1; fi
echo "axiom audit OK: $n declarations, only propext, Classical.choice, Quot.sound" | tee -a "$L/axioms.log"

echo "== 8. leanchecker on the solution's closure"
(cd "$CORE" && "${TIME[@]}" timeout "$TIMEOUT" lake env leanchecker BaselineV3Solution) 2>&1 | tee "$L/leanchecker.log"
[ "${PIPESTATUS[0]}" = 0 ] || { echo "leanchecker FAILED"; exit 1; }

echo "== 9. negative claims: each must fail to certify"
for v in img fuel7 fuelbig; do
  mkdir -p "$T/$v"; cp "$B/extractor.bin" "$B/extractor.data" "$B/claim.json" "$T/$v/"
  python3 -I - "$T/$v" "$v" <<'PY'
import json, sys
d, v = sys.argv[1:]
if v == "img":
    b = bytearray(open(f"{d}/extractor.bin", "rb").read()); b[8] ^= 1     # bit 0 of the third word
    open(f"{d}/extractor.bin", "wb").write(bytes(b))
c = json.load(open(f"{d}/claim.json"))
if v == "fuel7": c["fuel_base"] = 7                                      # below the image's 8 steps
if v == "fuelbig": c["fuel_base"] = 2 ** 41                              # above the budget B
json.dump(c, open(f"{d}/claim.json", "w"))
PY
  python3 -I "$CORE/scripts/render-challenge.py" "$CORE/$STUB" "$T/$v/claim.json" "$T/$v/Ch.lean"
  python3 -I "$B/make-solution.py" "$T/$v/Ch.lean" "$T/$v/Sol.lean"
  if (cd "$CORE" && timeout "$TIMEOUT" lake env lean "$T/$v/Sol.lean") > "$T/$v/out.log" 2>&1; then
    echo "negative claim $v ACCEPTED (bad)"; exit 1; fi
  echo "negative claim $v rejected: $(grep -m1 error "$T/$v/out.log")"
done | tee "$L/negative-claims.log"
[ "$(grep -c "rejected" "$L/negative-claims.log")" = 3 ] || exit 1

echo "== 10. smoke (r = 2, n = 16): native prover, compiled Vb, canaries, node mode, DoS sample"
"${TIME[@]}" python3 -I "$B/smoke.py" --run "$CORE/.lake/build/bin/entry-run" 2>&1 | tee "$L/smoke.log"
grep -q "^SMOKE: OK" "$L/smoke.log" || exit 1

echo "== 11. line counts (the core's scripts/loc.py)"
python3 -I "$C/scripts/loc.py" "$B"/*.lean | tee "$L/loc.log"

if [ "${HARNESS:-0}" = 1 ]; then
  echo "== 12. harness, proof half (the organiser clone's scripts/harness-local.sh)"
  clone "$ORG"
  "${TIME[@]}" "$ORG/scripts/setup-scratch.sh" org 2>&1 | tee "$L/setup-org.log"
  (cd "$ORG" && timeout "$TIMEOUT" lake exe gate --closure Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls \
    "$L/import-allowlist.txt") 2>&1 | tail -1
  (cd "$ORG" && python3 -I scripts/olean-manifest.py gen "$L/olean-manifest.sha256" --org "$ORG" \
    --closure "$L/import-allowlist.txt") 2>&1 | tail -1
  "${TIME[@]}" "$ORG/scripts/harness-local.sh" --org "$ORG" --manifest "$L/olean-manifest.sha256" \
    --allowed-imports "$L/import-allowlist.txt" --work "$L/harness-work" \
    "$B/claim.json" "$B" "$B/comparator-nanoda.json" 2>&1 | tee "$L/harness.log"
  grep -q "^HARNESS: ACCEPT" "$L/harness.log" || { echo "harness REJECTED"; exit 1; }
  cmp "$L/harness-work/claim/BaselineV3Challenge.lean" "$L/BaselineV3Challenge.lean" \
    && echo "the harness's rendering = step 5's" | tee -a "$L/harness.log"
fi
echo "CHECK OK"
