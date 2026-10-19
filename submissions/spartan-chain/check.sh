#!/usr/bin/env bash
# The entry's end-to-end check (adapted from submissions/baseline/check.sh at 91b3a56). Nothing is
# built or written in `.contract` or in the shared development clone: the core is cloned from the
# interim branch CORE_BRANCH (default v3/ks-interim-harness: the amended contract v3/ks-potential
# 05fde28 plus the interim organiser files RecursionFast/Challenge/V3.lean.in,
# scripts/render-challenge.py, scripts/harness-local.sh, scripts/setup-scratch.sh) of CORE_REPO
# (default /home/devops/Verified-zkEVM/rf-core-s2a) into CORE.
#
#   submissions/spartan-chain/check.sh             image, hygiene, source rule, build, challenge,
#                                                  solution (or its preview), axioms, negative
#                                                  claims, smoke, line counts
#   HARNESS=1 submissions/spartan-chain/check.sh   also the proof half of the harness
#                                                  (scripts/harness-local.sh of a clean organiser
#                                                  clone ORG), once the solution exists
#
# Until the module SpartanChainFinal.lean (leafVerifier, proveLeafR1, facts) exists, the solution
# steps run as a PREVIEW: the solution is generated against a stand-in SpartanChainFinal whose
# `facts` is `sorry`, elaborated, and must produce no error and exactly that one `sorry`.
# CORE, ORG: the scratch clones (defaults logs/spartan-chain/infra/core, …/org). BASE: the commit
# the interim branch is based on (default 05fde28). LOGDIR: the logs (default
# logs/spartan-chain/infra/check-<UTC>, never overwritten). TIMEOUT: seconds per Lean step (3600).
set -euo pipefail
B=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$B/../.." && pwd)
L=${LOGDIR:-$REPO/logs/spartan-chain/infra/check-$(date -u +%Y%m%dT%H%M%SZ)}
[[ ! -e "$L" ]] || { echo "check: $L exists; logs are never overwritten" >&2; exit 2; }
mkdir -p "$L"; L=$(cd "$L" && pwd); echo "logs: $L"
CORE=${CORE:-$REPO/logs/spartan-chain/infra/core}; ORG=${ORG:-$REPO/logs/spartan-chain/infra/org}
CORE_REPO=${CORE_REPO:-/home/devops/Verified-zkEVM/rf-core-s2a}; CORE_BRANCH=${CORE_BRANCH:-v3/ks-interim-harness}
BASE=${BASE:-05fde28}
TIMEOUT=${TIMEOUT:-3600}; export TIMEOUT
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
TIME=(/usr/bin/time -f "%e s wall, %M KB max")
clone() {
  [[ -d "$1/.git" ]] || git clone -q -b "$CORE_BRANCH" "$CORE_REPO" "$1"
  git -C "$1" merge-base --is-ancestor "$BASE" HEAD || { echo "check: $1 does not contain $BASE" >&2; exit 1; }
}
clone "$CORE"; PIN=$(git -C "$CORE" rev-parse "$BASE"); export PIN
STUB=RecursionFast/Challenge/V3.lean.in
FINAL=0; [[ -f "$B/SpartanChainFinal.lean" ]] && FINAL=1

echo "== 1. extractor image"
if command -v riscv64-unknown-elf-as > /dev/null; then
  "$B/build-extractor.sh" "$T"
  cmp "$T/extractor.bin" "$B/extractor.bin" && cmp "$T/extractor.data" "$B/extractor.data"
  cmp "$B/extractor.bin" "$CORE/tests/asm/proofwords.bin"
  echo "extractor.bin reassembled byte-identically; equal to the core's tests/asm/proofwords.bin"
else
  echo "riscv64-unknown-elf-as not installed: image not reassembled"
fi | tee "$L/image.log"

echo "== 2. hygiene (sorry, admit, native_decide, code attributes, axioms, unsafe/partial/opaque)"
python3 -I - "$B"/*.lean <<'PY' | tee "$L/hygiene.log"
import re, sys
bad = re.compile(r'\b(sorry|admit|native_decide|implemented_by|extern|csimp|axiom|unsafe|partial|opaque)\b'
                 r'|set_option\s+(maxRecDepth|maxHeartbeats)')
hits = []
for p in sys.argv[1:]:
    s = re.sub(r'/-.*?-/', '', open(p).read(), flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    hits += [f"{p}: {l.strip()}" for l in s.split('\n') if bad.search(l)]
print("\n".join(hits) if hits else "hygiene OK")
print(f"hygiene: {len(hits)} finding(s)")
PY
[[ $FINAL == 0 ]] || grep -q "^hygiene OK" "$L/hygiene.log" || { echo "hygiene FAILED (final mode)"; exit 1; }

echo "== 3. source rule (the core's scripts/source-rule.py on the root)"
python3 -I "$CORE/scripts/source-rule.py" "$B" > "$L/source-rule.log" 2>&1 && sr=0 || sr=1
cat "$L/source-rule.log"
if [[ $sr == 1 ]]; then
  [[ $FINAL == 0 ]] || { echo "source rule FAILED"; exit 1; }
  echo "source rule: findings (reported only until SpartanChainFinal.lean exists)"
fi

echo "== 4. build (scratch core clone; the infrastructure modules, the runner$( [[ $FINAL == 1 ]] && echo ', the final module'))"
targets="RecursionFastContract SpartanChainSubmission SpartanChainRun"
[[ $FINAL == 1 ]] && targets="$targets SpartanChainFinal"
ENTRY_TARGETS=$targets "${TIME[@]}" "$CORE/scripts/setup-scratch.sh" entry "$B" 2>&1 | tee "$L/build.log"
grep -q "setup-scratch: entry" "$L/build.log" || { echo "build FAILED"; exit 1; }
! grep -qE "warning: .*SpartanChain(VerifierTop|Submission|Decode)\.lean" "$L/build.log" || { echo "warnings in the infrastructure modules"; exit 1; }
# The local runner `entry-verify` (outside the root: a `main` is not entry code): the compiled
# `Run.verifyProof`, the submission's `Vb` (`Run.verifyProof_eq`), for smoke.py.
mkdir -p "$CORE/entrymain"
cat > "$CORE/entrymain/EntryVerify.lean" <<'EOF'
import SpartanChainRun

/-! Local runner (outside the entry root): the compiled instantiated verifier `Run.verifyProof`
(the submission's `Vb`, `Run.verifyProof_eq`) on a statement and a proof. -/

open SpartanChain RecursionFast

def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: r => do
    let x ← hexDigit a
    let y ← hexDigit b
    let t ← parseHex r
    pure ((x * 16 + y) :: t)
  | [_] => none

def readDigest (path : String) : IO Digest := do
  let raw ← IO.FS.readBinFile path
  if h : raw.data.size = 32 then return ⟨raw.data, h⟩
  let some l := parseHex (String.fromUTF8! raw).trimAscii.toString.toList
    | throw (IO.userError s!"{path}: not a statement")
  if h : l.toArray.size = 32 then return ⟨l.toArray, h⟩
  throw (IO.userError s!"{path}: not a statement")

def verify (stmt proof : String) : IO UInt32 := do
  let c ← readDigest stmt
  let π ← IO.FS.readBinFile proof
  let t₀ ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => Run.verifyProof c π
  let t₁ ← IO.monoNanosNow
  let verdict := if b then "accept" else "reject"
  IO.eprintln s!"Vb: {verdict} in {(t₁ - t₀) / 1000} us ({π.size} bytes)"
  pure (if b then 0 else 1)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["verify", stmt, proof] => verify stmt proof
    | _ => IO.eprintln "usage: entry-verify verify STMT.hex PROOF.bin"; pure 2
  catch e => IO.eprintln s!"entry-verify: {e}"; pure 2
EOF
grep -q '^name = "entry-verify"' "$CORE/lakefile.toml" \
  || printf '\n[[lean_exe]]\nname = "entry-verify"\nsrcDir = "entrymain"\nroot = "EntryVerify"\n' >> "$CORE/lakefile.toml"
(cd "$CORE" && "${TIME[@]}" timeout "$TIMEOUT" lake build entry-verify) 2>&1 | grep -E "error|s wall|Build completed" | tee -a "$L/build.log"
[[ -x "$CORE/.lake/build/bin/entry-verify" ]] || { echo "runner build FAILED"; exit 1; }

echo "== 5. render the organiser's challenge stub with claim.json"
python3 -I "$CORE/scripts/render-challenge.py" "$CORE/$STUB" "$B/claim.json" "$L/SpartanChainChallenge.lean"
(cd "$CORE" && timeout "$TIMEOUT" lake env lean "$L/SpartanChainChallenge.lean") > "$L/challenge.log" 2>&1 || true
cat "$L/challenge.log"
[ "$(grep -c "declaration uses \`sorry\`" "$L/challenge.log")" = 2 ] && [ "$(grep -c "error" "$L/challenge.log" || true)" = 0 ] \
  || { echo "challenge: expected exactly the two sorry placeholders"; exit 1; }

echo "== 6. the solution"
python3 -I "$B/make-solution.py" "$L/SpartanChainChallenge.lean" "$T/SpartanChainSolution.lean"
if [[ $FINAL == 1 ]]; then
  cmp "$T/SpartanChainSolution.lean" "$B/SpartanChainSolution.lean" \
    && echo "SpartanChainSolution.lean = make-solution.py(render(V3.lean.in, claim.json))" | tee "$L/solution.log"
  (cd "$CORE" && "${TIME[@]}" timeout "$TIMEOUT" lake build SpartanChainSolution) 2>&1 | tail -3 | tee -a "$L/solution.log"
else
  echo "PREVIEW: no SpartanChainFinal.lean yet; elaborating against a stand-in whose facts are sorry" | tee "$L/solution.log"
  mkdir -p "$T/pv"
  cat > "$T/pv/SpartanChainFinal.lean" <<'EOF'
import SpartanChainSubmission
import SpartanChainVerifier
import SpartanChainChainEval
namespace SpartanChain
open RecursionFast
/-- Stand-in: the real leaf verifier. -/
def leafVerifier : LeafVerifier := Leaf.leafVerifier chainEvals
/-- Stand-in prover: an empty SNARK. -/
def proveLeafR1 (_ : Digest) (_ : ℕ) (_ : Digest) : OProg ByteArray := .ret ByteArray.empty
/-- Stand-in facts (PREVIEW only). -/
theorem facts : Facts leafVerifier proveLeafR1 := sorry
end SpartanChain
EOF
  LP="$(cd "$CORE" && lake env printenv LEAN_PATH):$T/pv"
  (cd "$CORE" && LEAN_PATH=$LP timeout "$TIMEOUT" lake env lean --root="$T/pv" -o "$T/pv/SpartanChainFinal.olean" "$T/pv/SpartanChainFinal.lean") > "$L/preview-final.log" 2>&1 || true
  (cd "$CORE" && LEAN_PATH=$LP timeout "$TIMEOUT" lake env lean "$T/SpartanChainSolution.lean") > "$L/preview-solution.log" 2>&1 || true
  cat "$L/preview-final.log" "$L/preview-solution.log" | tee -a "$L/solution.log"
  [ "$(grep -c "declaration uses \`sorry\`" "$L/preview-final.log")" = 1 ] && ! grep -q "error" "$L/preview-final.log" "$L/preview-solution.log" \
    || { echo "preview FAILED"; exit 1; }
  echo "PREVIEW OK: the solution elaborates against the stand-in (its only gap: the stand-in's facts)" | tee -a "$L/solution.log"
fi

echo "== 7. axiom audit of the infrastructure modules"
{
  printf 'import SpartanChainSubmission\n'
  for f in SpartanChainDecode SpartanChainVerifierTop SpartanChainSubmission; do
    ns=$(grep -m1 "^namespace" "$B/$f.lean" | awk '{print $2}')
    grep -E "^(noncomputable )?(theorem|def|abbrev) " "$B/$f.lean" | sed 's/^noncomputable //' | awk '{print $2}' \
      | grep -vx main | while read -r n; do echo "#print axioms $ns.$n"; done
  done
} > "$T/Axioms.lean"
(cd "$CORE" && timeout "$TIMEOUT" lake env lean "$T/Axioms.lean") 2>&1 | tee "$L/axioms.log"
n=$(grep -c "axioms" "$T/Axioms.lean"); m=$(grep -cE "depends on axioms|does not depend on any axioms" "$L/axioms.log" || true)
[ "$n" = "$m" ] || { echo "axiom audit: $m answers for $n declarations"; exit 1; }
if grep -vE "depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$|does not depend on any axioms$" "$L/axioms.log"; then
  echo "axiom audit FAILED"; exit 1; fi
echo "axiom audit OK: $n declarations, only propext, Classical.choice, Quot.sound" | tee -a "$L/axioms.log"

echo "== 8. negative claims"
if [[ $FINAL == 1 ]]; then
  for v in img fuel7 qv; do
    mkdir -p "$T/$v"; cp "$B/extractor.bin" "$B/extractor.data" "$B/claim.json" "$T/$v/"
    python3 -I - "$T/$v" "$v" <<'PY'
import json, sys
d, v = sys.argv[1:]
if v == "img":
    b = bytearray(open(f"{d}/extractor.bin", "rb").read()); b[8] ^= 1
    open(f"{d}/extractor.bin", "wb").write(bytes(b))
c = json.load(open(f"{d}/claim.json"))
if v == "fuel7": c["fuel_base"] = 7
if v == "qv": c["qV"] = 16383
json.dump(c, open(f"{d}/claim.json", "w"))
PY
    python3 -I "$CORE/scripts/render-challenge.py" "$CORE/$STUB" "$T/$v/claim.json" "$T/$v/Ch.lean"
    python3 -I "$B/make-solution.py" "$T/$v/Ch.lean" "$T/$v/Sol.lean"
    if (cd "$CORE" && timeout "$TIMEOUT" lake env lean "$T/$v/Sol.lean") > "$T/$v/out.log" 2>&1; then
      echo "negative claim $v ACCEPTED (bad)"; exit 1; fi
    echo "negative claim $v rejected: $(grep -m1 error "$T/$v/out.log")"
  done | tee "$L/negative-claims.log"
else
  echo "PENDING: negative claims need SpartanChainFinal.lean" | tee "$L/negative-claims.log"
fi

echo "== 9. smoke: the Rust prover, the native and the compiled Lean verifiers, the canaries"
"${TIME[@]}" python3 -I "$B/smoke.py" --run "$CORE/.lake/build/bin/entry-verify" 2>&1 | tee "$L/smoke.log"
grep -q "^SMOKE: OK" "$L/smoke.log" || exit 1

echo "== 10. line counts (the core's scripts/loc.py)"
python3 -I "$CORE/scripts/loc.py" "$B"/*.lean | tee "$L/loc.log"

if [ "${HARNESS:-0}" = 1 ]; then
  if [[ $FINAL == 0 ]]; then echo "== 11. harness: PENDING (no SpartanChainFinal.lean)"; else
  echo "== 11. harness, proof half (the organiser clone's scripts/harness-local.sh)"
  clone "$ORG"
  "${TIME[@]}" "$ORG/scripts/setup-scratch.sh" org 2>&1 | tee "$L/setup-org.log"
  # the allowlist and the manifest of the clean organiser build, with CompPoly's BF64/Ext3 closure
  # (the interim branch's scripts/org-closure.sh; DESIGN-v3 §7.4, AGENTS.md §10)
  "$ORG/scripts/org-closure.sh" "$L"
  "${TIME[@]}" "$ORG/scripts/harness-local.sh" --org "$ORG" --manifest "$L/olean-manifest.sha256" \
    --allowed-imports "$L/import-allowlist.txt" --work "$L/harness-work" \
    "$B/claim.json" "$B" "$B/comparator-nanoda.json" 2>&1 | tee "$L/harness.log"
  grep -q "^HARNESS: ACCEPT" "$L/harness.log" || { echo "harness REJECTED"; exit 1; }
  fi
fi
echo "CHECK OK$( [[ $FINAL == 0 ]] && echo ' (PREVIEW: the solution, the negative claims and the harness wait for SpartanChainFinal.lean)')"
