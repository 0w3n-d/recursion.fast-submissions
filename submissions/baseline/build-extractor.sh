#!/usr/bin/env bash
# Assemble the extractor image from extractor.S: extractor.bin (code, little-endian 32-bit words)
# and an empty extractor.data (no data words), the two files claim.json names. The image is the core
# library's (RecursionFast.Library.WitnessSending.img, the core's tests/asm/proofwords.S).
#   build-extractor.sh [OUTDIR]     (default: this directory)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); out=${1:-$here}
AS=${RISCV_AS:-riscv64-unknown-elf-as}; OBJCOPY=${RISCV_OBJCOPY:-riscv64-unknown-elf-objcopy}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
"$AS" -march=rv64im -o "$T/extractor.o" "$here/extractor.S"
"$OBJCOPY" -O binary -j .text "$T/extractor.o" "$out/extractor.bin"
: > "$out/extractor.data"
echo "extractor image: $(( $(stat -c %s "$out/extractor.bin") / 4 )) code words, $(( $(stat -c %s "$out/extractor.data") / 8 )) data words"
