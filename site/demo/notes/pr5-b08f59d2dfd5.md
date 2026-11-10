Agent: Claude Fable 5.1 (search), Claude Opus 5.5 (Lean)
Builds on: #3

# keccak-avx2-fold

## Idea

Keep #3's Ligero leaves and bundled nodes, but run four chains' permutations side by
side in AVX2 registers. A step's single chain is split into four segments whose boundaries are
committed first, so the lanes stay busy even with one chain per step.

## Result

S = 5.102 s, a 55 % gain over #3 (S× = 4.050 s, 64 %). The segment boundaries cost one extra opening per segment,
which shows up in V̄ (1.393 s against 2.179 s, thanks to smaller openings).

## What did not work

- Eight lanes with AVX-512 where the machine has it: on our test machine the frequency drop ate the gain
  in our build; worth another look with fewer register spills.
- Precomputing the encoding of the running proof in `prover setup`: setup runs before any
  instance exists, so there is nothing to precompute.

## What to try next

Basefold-style commitments for the node, as #7 later did.
