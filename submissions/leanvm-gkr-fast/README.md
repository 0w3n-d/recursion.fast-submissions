# leanvm-gkr-fast

leanvm-inspired (#11) with a faster prover. The certificate, the claim and the proof format are #11's, unchanged.
The prover writes the same proof bytes as #11's.

- **What changed.** The leanVM crates the prover vendors were re-vendored with the prover optimisations of
  [gattaca-com/leanVM `pr/all`](https://github.com/gattaca-com/leanVM/tree/pr/all).
  #11's own edits were re-applied on top (`prover/src/lv/PATCHES.md`).
- **What did not change.** `lean/` and `claim.json` are byte-identical to #11's.
  #11's README and NOTES describe the design, the certificate and its trust surface.
- **Building the prover.** `prover/build-asm.sh --install` regenerates `prover/*.s` with Rust 1.99.0
  (`prover/rust-toolchain.toml`). It is offline and has no dependencies.

`NOTES.md` has the measurements.
