#!/usr/bin/env bash
# All the offline tests of this entry (no harness, no network), from whichever root holds this src/:
#   1. regen.sh --check: the generated kernels and prover/prover.s are reproduced from the sources;
#   2. test_keccak: every kernel this CPU runs against the baseline's portable Keccak (the permutation on
#      random states, chains of 0 to 1.5e5 steps, two chains per call), then test_vectors.py (an
#      independent Python Keccak) on chain ends, leaf and node statements and keccak256("");
#   3. test_prover.py: the prover, built from prover/*.s with the evaluation's command, against
#      src/ref_prover.c (the witness-baseline prover) through a strict fake service, for every kernel this
#      CPU runs, forced, and for each way a request chooses its kernel;
#   4. test_mutants.py: planted bugs that 2. must catch;
#   5. with qemu-x86_64: on CPUs without AVX-512 (Haswell) and without BMI (qemu64), which kernels are
#      offered, and 2. and 3. on them, shortened.
# A kernel this CPU cannot run is reported as NOT TESTED; REQUIRE="NAME ..." makes that a failure.
#   src/test.sh [--quick]     --quick skips 4 and 5
#   src/test.sh --bench       also prints ns per permutation (pin it yourself: taskset -c N)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
T=$(mktemp -d "${TMPDIR:-/tmp}/rft.XXXXXX"); trap 'rm -rf "$T"' EXIT
cd "$ROOT/src"
if gcc --version | head -1 | grep -qF '(Ubuntu 15.2.0-16ubuntu1) 15.2.0'; then
  ./regen.sh --check
else
  echo "test: regen --check skipped (another gcc than the one prover.s was made with)"
fi
gcc -O2 -Wall -Wno-unused-function -o "$T/test_keccak" test_keccak.c
"$T/test_keccak" all
python3 -I test_vectors.py "$T/test_keccak"
KERNELS=$("$T/test_keccak" available)
for k in ${REQUIRE:-}; do
  [[ " $KERNELS " == *" $k "* ]] || { echo "test: REQUIRE names $k, which this CPU cannot run" >&2; exit 1; }
done
mkdir "$T/build" && cp "$ROOT"/prover/*.s "$T/build/"
gcc -static -O2 -pthread "$T"/build/*.s -o "$T/build/prover" -lm
gcc -O2 -o "$T/ref" ref_prover.c
TMPDIR="$T" python3 -I test_prover.py "$T/ref" "$T/build/prover" "$KERNELS"
if [[ "${1:-}" != --quick ]]; then
  python3 -I test_mutants.py "$ROOT/src"
  if command -v qemu-x86_64 >/dev/null; then
    for cpu in Haswell qemu64; do
      want=$([[ $cpu == Haswell ]] && echo "scalar bmi" || echo "scalar")
      got=$(qemu-x86_64 -cpu $cpu "$T/test_keccak" available | xargs)
      [[ "$got" == "$want" ]] || { echo "test: qemu $cpu offers \"$got\", expected \"$want\"" >&2; exit 1; }
      echo "qemu $cpu: kernels offered: $got"
      TK_QUICK=1 qemu-x86_64 -cpu $cpu "$T/test_keccak" all
      TMPDIR="$T" TP_QUICK=1 python3 -I test_prover.py "$T/ref" "qemu-x86_64 -cpu $cpu $T/build/prover" "$got" | tail -1
    done
  else
    echo "test: qemu-x86_64 not found; the CPUs without AVX-512 or BMI are NOT TESTED"
  fi
fi
[[ "${1:-}" == --bench ]] && "$T/test_keccak" bench
exit 0
