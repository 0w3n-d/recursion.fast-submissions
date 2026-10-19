# Report: `Decode.lean`, the linear-time decoder (BLUEPRINT-R1 §1.2.1, group A)

## What was built

`submissions/spartan-chain/SpartanChainDecode.lean`, `namespace SpartanChain`, added to the umbrella
`SpartanChain.lean`. It is a copy, with a provenance line, of S2a's linear twins from
`submissions/baseline/BaselineV3.lean` at commit `91b3a56`. The definitions and proofs are
unchanged; only the namespace differs.

| Definition | Theorem (against the library or contract) |
|---|---|
| `packFast` | `packFast_eq : packFast b = packBytes b` |
| `bytesAtF` | `bytesAtF_eq : bytesAtF o k n = bytesAt o k n` (helper `wordByte_eq`, private) |
| `decodeWitF` | `decodeWitF_eq : decodeWitF o = decodeWit o` |
| `decodeF π := decodeWitF (packFast π.data.toList)` | `decodeF_eq : decodeF π = WitnessSending.decode π` |
| `witWordsF`, `encodeF` | `encodeF_eq : encodeF w = WitnessSending.encode w` |

Controls added here:

- `decodeF_encodeF` (positive): the round trip on every `w` with `w.Fits`.
- `decodeF_bad_tag` (negative, kernel): an unknown tag word decodes to nothing.

## What is proved and checked

- Everything above is proved. There is no `sorry`.
- `#print axioms` on all seven theorems gives only `propext`, `Classical.choice` and `Quot.sound`.
  The axiom file was a scratch file outside the root, `rf-core-sc/scratch/DecodeAxioms.lean`.
- The build is `cd rf-core-sc && timeout 3600 lake build +SpartanChainDecode`: green in 14.7 s.
  It was run on the branch `v3/ks-potential`. `encode`, `decode`, `packBytes`, `bytesAt` and
  `decodeWit` are unchanged there from the pin.
- The source rule on the root reports 26 files and 0 findings.
- `loc.py`: 54 code lines, 96 lines in total, 8 theorems.

## Lemmas the node check will need (S2a's pattern)

These are for `SpartanChainVerifier` and `SpartanChainSubmission` (group C). S2a's `check` has the
same node branch, so each item below has a proved model in `submissions/baseline/BaselineV3.lean`.

1. **`check_eq`.** It restates `check` and `checkNode` with the library's `decode` and `encode`.
   Prove it with `rw [check, decodeF_eq]; simp only [encodeF_eq, dite_eq_ite]`. Every later proof
   goes through it, and never through `decodeF` or `encodeF` directly. The node `if` becomes an
   `ite` once `encodeF` is rewritten, which is why `dite_eq_ite` is in the `simp only` list.
2. **Termination.** In `decreasing_by`, rewrite with `rw [← _h, encodeF_eq, size_encode]`, then
   `simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
   ← size_eq_length]` and `omega`. A canonical node encoding is longer than each child.
3. **Strictness (`check_canonical`).** If an accepted node proof decodes to `w`, then
   `encode w = π`.
   - This is the fact that rejects the two byte canaries for nodes: one byte appended, and the last
     byte removed. Both change the size, and every encoding has a size that is a multiple of 8.
   - For leaves, R1's `leafSize n` size check does the same job (§1.1). The library's `check` lacks
     this in its leaf branch (S2a finding).
4. **Soundness (`checkNode_sound`).** From `checkNode c π = true`:
   - `decode π = some (.node c₁ c₂ π₁ π₂)`,
   - `c = nodeStmt c₁ c₂`,
   - and `submission.Vb cᵢ πᵢ = true` for both children, through `Vb_eq`, from the
     `πᵢ.size ≤ proofCap ∧ check cᵢ πᵢ` conjuncts.

   This is `final` for node proofs, with no oracle involved. Model: S2a's `check_sound`.
5. **Completeness (`check_encode` for nodes).** For `Rel submission.Vb c (.node …)`:
   - `fits_of_rel` gives the children's sizes from `size_le_of_Vb`;
   - `decode_encode` gives the round trip;
   - `Vb_eq` turns each child's `Vb` into the `check` conjunct.
6. **Statement binding (canaries 3 and 4).** An accepted proof binds one statement. S2a's
   `stmt_unique` derives this from soundness: `Rel` fixes `c = nodeStmt c₁ c₂`, so a flipped bit or
   swapped children is rejected unless BLAKE2s collides. For R1's leaf branch, the same follows
   from `c = leafStmt h n` being checked first (§1.3 step 1).
7. **`Vb_iff` (optional, summary).** `Vb c π = true ↔ π.size ≤ proofCap ∧ ∃ w, decode π = some w ∧
   encode w = π ∧ Rel submission.Vb c w`, restricted to node proofs for R1. S2a's proof combines
   items 3–5.
8. **Kernel controls.** `check` is defined by well-founded recursion, so the kernel cannot reduce
   it. Rewrite with `check_eq` (and with `decodeF_eq` for `decodeF`) before `decide +kernel`; S2a's
   controls use `rw [check_eq]; decide +kernel`.

## Open, and deviations

- **Nothing open in this module.**
- **No deviation from the blueprint.** The two controls are additions.
- **Cost of the node check.** The whole recursive check is `O(|π| · depth)`, because each node
  decodes and re-encodes its whole subproof. S2a measured 212.6 s at depth 2,000
  (`logs/V3-S2/review/caterpillar.log`). For the honest shape (depth `r`) the decoding is linear
  per node; the blueprint's §12 decode row should quote this entry's own measurement.
