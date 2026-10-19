# `spartan-chain`: the honest succinct entry (R1, stage S2b)

A Spartan-style SNARK for the BLAKE2s hash chain at the leaves, and witness-sending nodes. The
normative specification is `docs/snark-baseline/BLUEPRINT-R1.md`. The rules an implementer follows
are in `docs/snark-baseline/IMPLEMENTERS.md`, and the per-module reports are in
`docs/snark-baseline/reports/`. This entry targets the proposed amendment of the core's
knowledge-soundness definition (core issue #5, branch `v3/ks-potential`), not the contract at the
pin.

## Checks

`check.sh` runs the end-to-end check (`docs/snark-baseline/reports/submission-infra.md`). It
covers the image, hygiene, the source rule, the build, the challenge, the solution (or its
preview), the axiom audit, the negative claims, `smoke.py`, and the line counts. With `HARNESS=1`
it also runs the harness. The Rust native prover is built with
`CARGO_TARGET_DIR=<outside this root> cargo build --release --offline`.

## Licences and provenance

- **leanerVM, Apache-2.0.** Code copied or transcribed from leanerVM
  (https://github.com/Verified-zkEVM/leanerVM) is used under the Apache License, Version 2.0. Its
  text is in **`LICENSE-leanerVM`** in this directory, a copy of leanerVM's `LICENSE` at commit
  `532ebb4`. That code is in:
  - `SpartanChainBlake2sCircuit.lean`, `SpartanChainBlake2sWords.lean`,
    `SpartanChainBlake2sCompress.lean`, `SpartanChainRingSwitch.lean`;
  - `circuit.rs`.

  Each file's header names the source path, the commit and the modifications made.
- **The core library.** `SpartanChainDecode.lean`'s list codec is copied from this repository's
  `submissions/baseline/BaselineV3.lean` (commit `91b3a56`). The extractor files come from
  `submissions/baseline`, and they are the core's `tests/asm/proofwords.S`.
