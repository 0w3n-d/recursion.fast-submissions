#!/usr/bin/env bash
# Regenerates prover/prover.s from src/prover.c byte for byte:
#   gcc -S -O2 src/prover.c, then src/asm-compat.py (a copy of the core's harness/tools/asm-compat.py,
#   which rewrites directives that the evaluation VM's binutils 2.42 rejects).
# The committed file was made with GCC "(Ubuntu 15.2.0-16ubuntu1) 15.2.0" (its .ident line); another
# GCC gives other, equally valid assembly, so the script refuses to overwrite with one unless FORCE=1.
#   src/regen.sh            regenerate prover/prover.s (run from anywhere)
#   src/regen.sh --check    only check that the committed file is reproduced
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WANT="GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
gcc -S -O2 -o "$T/raw.s" "$ROOT/src/prover.c"
python3 -I "$ROOT/src/asm-compat.py" "$T/raw.s" "$T/prover.s" >/dev/null
if ! grep -qF ".ident	\"$WANT\"" "$T/prover.s" && [[ "${FORCE:-0}" != 1 ]]; then
  echo "regen: this gcc is not $WANT; the output would differ from the committed file (FORCE=1 to write it anyway)" >&2
  exit 1
fi
if [[ "${1:-}" == --check ]]; then
  cmp "$T/prover.s" "$ROOT/prover/prover.s" && echo "regen: prover/prover.s is reproduced byte for byte"
else
  cp "$T/prover.s" "$ROOT/prover/prover.s" && echo "regen: wrote prover/prover.s"
fi
