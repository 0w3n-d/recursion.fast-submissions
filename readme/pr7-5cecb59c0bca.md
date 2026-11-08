# witness-baseline

The simplest certified entry there is, published by the organiser as the reference point for
season 1. It is honest and complete, and it is not competitive: it shows the floor that any real
construction must beat, and it puts every part of the pipeline to work (claim, Lean certificate,
assembly prover, oracle service, checks, score).

## What it is

- **The proof is the witness.** A leaf proof is the chain's start and length (48 bytes). A node
  proof is its two children's statements and their signed proofs `(π, tr, σ)`, copied whole. There
  is no commitment, no sumcheck and no Fiat–Shamir.
- **The verifier recomputes everything.** `V` decodes the proof and checks it against the relation
  directly: for a leaf it recomputes the Keccak-256 chain from the start and compares the leaf
  statement; for a node it hashes the node statement and runs `acc` on both children (signature
  and verifier), recursively, down to the first step. `V` asks the oracle nothing (`qV = 0`), so
  every trace is empty and every signature is over the empty trace.
- **The certificate is the core library's.** `lean/Solution.lean` is the rendered challenge filled
  with `RecursionFast.Library.WitnessSending`: knowledge error 0 (an accepted proof *is* a
  witness, so the extractor just copies it), completeness error 0, fuel `8 · t`. The claim:
  `{"error": "0", "completeness_error": "0", "qV": 0, "fuel_base": 0, "fuel_per_word": 8}`.
- **The prover** (`prover/prover.s`, generated from `src/prover.c`) computes the new chain with a
  portable, single-threaded Keccak-256, writes the witness encoding, and makes one empty `SIGN`.

## Why it is slow, and how it scores

The stream is pure IVC: step `i` proves `nodeStmt prev (leaf C_i)`. Here the step-`i` proof
contains every earlier proof, so checking it means recomputing **every chain of the stream so
far**, about `Σ_{j≤i} n_j` permutations: about 0.3 M per step on average, 32 M by step 96.

Measured locally (development VM, not the evaluation machine, see `NOTES.md`): the compiled `acc`
costs about 2–3 µs per permutation on one core, so `V_i` grows linearly with `i`, and there it
passed the per-check cap `verify_s = 10 s` at about 4.3 M permutations of history. On the
evaluation machine its check exceeds `verify_s` from about step 31 of the season's fixed lengths.
At the season shape the evaluation therefore ends in **REJECT** ("a check took … s, above verify_s"). Before that point the score's verifier
term dominates: `x_i = V_i / v_ref + |π_i| / s_ref` grows with `i`, and `V̄` charges it cubically.
`P̄` (about 1 s per `2^18` permutations with this prover) is irrelevant in comparison.

The proof also grows, by about 9.7 KB per step (two signatures of 4.8 KB each per level), which
is harmless next to `s_ref = 2 MiB`.

## Files

| Path | What |
|---|---|
| `claim.json` | the declared numbers |
| `lean/Solution.lean` | the certificate (imports only the core library) |
| `prover/prover.s` | the prover, GNU assembly as built by the harness |
| `src/prover.c` | its C source (the core's toy prover without the smoke's broken variants) |
| `src/regen.sh` | regenerates `prover/prover.s` byte for byte (`--check` to verify) |
| `src/asm-compat.py` | the core's filter for binutils 2.42, used by `regen.sh` |
| `NOTES.md` | idea, result, what failed, and what to try first |
| `LICENSE` | Apache-2.0 (the C, Lean and Python here derive from the core) |
