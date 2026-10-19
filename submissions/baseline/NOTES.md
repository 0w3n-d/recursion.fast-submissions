# NOTES: the witness-sending baseline (journal)

Untrusted text for the next solver (DESIGN-v3 §7.7). Measurements are quoted with their logs in
`README.md` §6 and in `docs/stages/V3-S2a-RESULT.md`.

## The idea

Send the witness. A leaf proof is the chain's start and length; a node proof is the two child
digests and the two child proofs. The verifier recomputes everything: every chain of the tree,
every leaf and node statement. No oracle query, error `0`, the extractor is the identity on the
proof's words. It is certified, complete and sound, and it is the reference point that calibrates
the succinctness cap `T_V` (§6.5): on an honest tree its root check is dominated by the chain
work, which is linear in the total chain length.

## The result

- Certified against the rendered v3 claim (`BaselineV3Solution.certified`), axioms `propext`,
  `Classical.choice`, `Quot.sound` only.
- Smoke tree (r = 2, n = 16): every proof accepted against independently computed digests, every
  canary rejected.
- Calibration (r = 8, n = 2^14) on the development VM: the compiled root check takes about 21 s,
  so the entry is listed, unranked (`T_V = 2 s`). The native prover takes well under a second for
  the whole tree, which is irrelevant: the entry is excluded by its verifier, not its prover.

## What did not work, and why

- **The core library's verifier as it is.** `RecursionFast.Library.WitnessSending.check` checks
  canonicity only for node proofs. A leaf proof is accepted whenever its packed words decode to the
  leaf, and `decodeWit` ignores the words after the sixth, so a leaf proof with one byte appended
  is accepted, and so is one with the last byte removed (the top byte of the length word, always
  zero up to `chainCap`). Those are two of the four canaries of §6.3 step 7, so the library's
  submission would fail the benchmark. The kernel-checked evidence is in `BaselineV3Controls`
  (`lib_check_appended`, `lib_check_truncated`). This entry's `check` requires the canonical
  encoding for leaves too. Because the relation is about the instantiated verifier, the strict
  check must be used recursively for the children as well, so `check` and its soundness and
  completeness proofs are the entry's own; `encode`, `decode`, `P`, `E`, `img` and `computes` are
  the library's.
- **The library's decoder in compiled code.** The contract's `packBytes` takes 8 bytes after a
  `drop (8 * j)` for every word `j`, and `bytesAt` walks the word list for every byte, so their
  compiled code is quadratic. A verifier that calls `decode` took 563 s to reject a uniformly
  random 1 MiB proof (log in the RESULT), which fails the DoS column (`verify_s = 60 s`). A first fix, a
  filter on the tag word, made random proofs cheap but left a proof with tag word 1 slow. The fix
  that stayed: `packFast`, `bytesAtF`, `decodeF`, `encodeF`, linear in the proof they read, proved
  equal to the library's functions. Random proofs now reject within 0.25 s and adversarially
  shaped 1 MiB proofs under the root digest within 1.3 s (`smoke.log`).
- **Not fixed: the whole verifier is not linear.** Each node decodes, re-encodes and compares its
  whole subproof before recursing, so the decoding costs `O(|π| · depth)`. The review measured
  valid lopsided ("caterpillar") proofs with no chain work: 212.6 s at depth 2,000 (272 KB),
  ×4 per doubling (`logs/V3-S2/review/caterpillar.log`). Under the runner's root digest such a
  proof needs a hash preimage, so the benchmark's DoS column (random proofs) is unaffected. A
  linear verifier would check the proof over byte offsets into one buffer, without copying the
  children, and prove that equal to `check`; not worth it for an unranked baseline.

## Known properties

- **Verifier time** is the chain work plus `O(|π| · depth)` decoding (above). A valid proof may
  declare up to `chainCap = 2^20` steps per leaf and as many leaves as fit in `proofCap`. Such a
  proof is accepted, after as many compressions as its prover computed. The cap of `2^20` steps per leaf
  bounds the work spent on one leaf before a wrong leaf is rejected (about 5 s at the measured
  ~5 µs per compiled compression).
- **The image is the library's 8-instruction in-place extractor**: it outputs the proof's words as
  they are, and `decodeWit` reads them leniently (V3-S1-A22). The canonicity of the proof is the
  verifier's business, not the extractor's.
- **The native prover is Python.** It is never proved; `smoke.py` checks that it writes the same
  bytes as the compiled Lean prover `P` and as the kernel-checked known answers.

## What to try next

- Nothing for this entry: it exists to be beaten. A competitive entry needs a verifier whose root
  check does not recompute the chains: a SNARK or an accumulation scheme over the chain steps.
- For the organiser: make the library's `check` strict on leaves (one line: the leaf branch also
  requires `encode (.leaf s n) = π`), so that the library's own submission passes the canaries,
  and consider linear-time `packBytes`/`bytesAt` in the library (proved equal), so that every entry
  that reuses `decode` gets a cheap verifier.
