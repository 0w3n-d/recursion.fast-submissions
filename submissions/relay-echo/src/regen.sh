#!/usr/bin/env bash
# Regenerates the generated kernels and prover/prover.s from the sources, byte for byte:
#   gen_scalar.py, gen_lanes.py and gen_vlasm.py write keccak_scalar.inc, keccak_lanes.inc and
#   keccak_vlasm.inc; then gcc -S -O2 src/prover.c, then src/asm-compat.py (a copy of the core's
#   harness/tools/asm-compat.py, which rewrites directives that the evaluation VM's binutils 2.42 rejects).
# The committed prover.s was made with GCC "(Ubuntu 15.2.0-16ubuntu1) 15.2.0" (its .ident line); another
# GCC gives other, equally valid assembly, so the script refuses to overwrite with one unless FORCE=1.
#   src/regen.sh            regenerate (run from anywhere)
#   src/regen.sh --check    only check that the committed files are reproduced
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WANT="GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
CHECK=0; [[ "${1:-}" == --check ]] && CHECK=1
bad=0
for g in scalar lanes vlasm; do
  python3 -I "$ROOT/src/gen_$g.py" > "$T/keccak_$g.inc"
  if (( CHECK )); then
    cmp -s "$T/keccak_$g.inc" "$ROOT/src/keccak_$g.inc" || { echo "regen: src/keccak_$g.inc is not what gen_$g.py writes" >&2; bad=1; }
  else
    cmp -s "$T/keccak_$g.inc" "$ROOT/src/keccak_$g.inc" || cp "$T/keccak_$g.inc" "$ROOT/src/keccak_$g.inc"
  fi
done
(cd "$ROOT/src" && gcc -S -O2 -o "$T/raw.s" prover.c)   # from src/, so that .file is "prover.c"
python3 -I "$ROOT/src/asm-compat.py" "$T/raw.s" "$T/prover.s" >/dev/null
if ! grep -qF ".ident	\"$WANT\"" "$T/prover.s" && [[ "${FORCE:-0}" != 1 ]]; then
  echo "regen: this gcc is not $WANT; the output would differ from the committed file (FORCE=1 to write it anyway)" >&2
  exit 1
fi
if (( CHECK )); then
  cmp "$T/prover.s" "$ROOT/prover/prover.s" || bad=1
  (( bad )) && exit 1
  echo "regen: the generated kernels and prover/prover.s are reproduced byte for byte"
else
  cp "$T/prover.s" "$ROOT/prover/prover.s" && echo "regen: wrote the generated kernels and prover/prover.s"
fi
