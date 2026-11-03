# ligero-chain-v2

Basefold nodes over binary towers and register-resident BLAKE2s lanes.

## What is certified

Knowledge soundness with ε = 2^-128 per fresh query, completeness with δ = 0, and the
extractor's fuel `8 · t` steps. See `lean/Solution.lean`.

## Building the prover

`prover/gen.sh` regenerates `prover/prover.s` from the Rust sources in `prover/src/` with the
runner image's toolchain.
