# Report: `SpartanChainVerifierTop.lean`, the top level of `V` and the node branch

BLUEPRINT-R1 §1.1–§1.3 and the §14 "Verifier.lean" items. This is the part of `Verifier.lean`
that does not depend on the SNARK. The SNARK is a parameter, so the module builds now and is
instantiated later.

## What was built

`submissions/spartan-chain/SpartanChainVerifierTop.lean`, in `namespace SpartanChain`. It imports
only `SpartanChainDecode`, and it is added to the umbrella `SpartanChain.lean`.

**The parameter.** `structure LeafVerifier` has three fields:

- `size : ℕ → ℕ`, which is `leafSize n` (§7);
- `size_ge : ∀ n, 80 ≤ size n`;
- `prog : (s n h snark) → OProg Bool`, the SNARK verifier of §1.3 step 3, run when `n ≥ 1`.

`Verifier.lean` builds a `LeafVerifier` from `leafSize` and the Spartan/Ligero verifier, then
uses `V LV`, `check LV` and `vb LV`.

**Parsing (§1.1).**

| Field | Bytes | Definition |
|---|---|---|
| `tagWord` | 0–7 | `ofLE` of the bytes, little-endian |
| `leafS` | 8–39 | `digestFrom π 8`, an `Array.getD` read |
| `leafN` | 40–47 | `ofLE` of the bytes, little-endian |
| `leafH` | 48–79 | `digestFrom π 48` |
| `leafSnark` | 80 to the end | `π.extract 80 π.size` |

Every read is an array operation. No list of the whole proof is built in compiled code.

**The leaf branch (§1.3).** `leafHeaderOK` checks, with no oracle, in this order:

1. `n ≤ chainCap`;
2. `π.size = leafSize n`;
3. `c = leafStmt h n`.

`leafProg` then accepts iff `h = s` when `n = 0`, and otherwise runs `LV.prog s n h π_S`.

**The decision and the verifier (§1.2).**

- `check` returns `false` when `π.size < 8`. It runs `(leafProg c π).run blake2sOracle` for tag 0
  and the node branch for tag 1, and returns `false` otherwise. It recurses on `π.size`, with S2a's
  `decreasing_by`.
- The node branch is canonical over `decodeF` and `encodeF`. It checks `c = nodeStmt c₁ c₂`, and
  that each child is at most `proofCap` bytes and passes `check`.
- `checkNode` is the node branch as a separate definition.
- `V` takes the same branches: `leafProg` for leaves and `.ret` for everything else.
- `vb c π := decide (π.size ≤ proofCap) && check c π`.

## What is proved (no `sorry`; axioms within `propext`, `Classical.choice`, `Quot.sound`)

Every result below holds for every `LeafVerifier`.

- **Unfolding.**
  - `check_eq` restates `check` with `checkNode`.
  - `checkNode_eq` restates `checkNode` with the library's `decode` and `encode`.
  - `V_run : (V LV c π).run blake2sOracle = check LV c π`.
  - `Vb_eq_vb : S.V = V LV → S.Vb = vb LV`. This is the bridge to `Rel S.Vb`.
- **Node soundness and completeness.**
  - `checkNode_sound`: an accepted node is `decode π = some (.node c₁ c₂ π₁ π₂)`, with
    `encode … = π`, `c = nodeStmt c₁ c₂` and both children accepted by `vb`.
  - `checkNode_rel` packages that as `∃ w, decode π = some w ∧ Rel (vb LV) c w`.
  - `check_encode_node`: if `Rel (vb LV) c (.node …)`, then `check` accepts `encode (.node …)`.
- **Statement binding.**
  - `check_stmt_unique`: a proof is accepted under at most one statement.
  - `leafProg_stmt`: an accepted leaf proof binds `leafStmt h n`, for every oracle.
  - `checkNode_stmt_unique`: the same for node proofs.
  - So a flipped statement bit and swapped children are rejected. This is stated as uniqueness:
    the inequality `nodeStmt c₂ c₁ ≠ nodeStmt c₁ c₂` is a hash fact, and is not claimed.
- **Canaries (one byte appended, the last byte removed).**
  - Leaf proofs: `leaf_push_rejected` and `leaf_pop_rejected`, from the exact-size header check
    (`check_leaf_size`).
  - Node proofs: `node_push_rejected` and `node_pop_rejected`, from canonicity
    (`check_node_size`: an accepted node proof has `8 ∣ size` and `88 ≤ size`).
  - Each is rejected under every statement.
  - Helpers: `leaf_resized_rejected`, `parse48_congr` (the tag and the length read only bytes
    0–47), `parse_congr` (the whole header reads only bytes 0–79), `take_push`, `take_dropLast`.
- **The extractor's view.**
  - `decode_leaf : 48 ≤ π.size → tagWord π = 0 → decode π = some (.leaf (leafS π) (leafN π))`.
    The library's `decode` reads exactly `(s, n)` from a leaf proof, whatever follows byte 48.
  - So `E := WitnessSending.E`, `img := WitnessSending.img`, `fuel := WitnessSending.fuel` and
    `computes := WitnessSending.computes` are reused as they are. That is how the S2a entry does
    it: its `certificate` sets `computes := WitnessSending.computes`, because `E`, `img` and `fuel`
    are the library's.
- **What `final` gets** (for `Soundness/KS.lean`).
  - `final_of_not_leaf`: off the leaf branch, a proof accepted on any log decodes to a witness of
    `Rel (vb LV)`, with no oracle answer used.
  - `final_of_leaf`: on the leaf branch, an accepted proof gives five facts:
    1. `decode π = some (.leaf s n)`;
    2. `n ≤ chainCap`;
    3. `c = leafStmt h n`;
    4. `n = 0 → h = s`;
    5. `n ≠ 0 →` `LV.prog s n h π_S` accepted on the same log.

    The SNARK's soundness must then supply `h = chainEnd s n`.
  - `leafProg_zero_rel`: the zero-step leaf alone gives `Rel`.
- **Query counts.**
  - `V_eq_ret`: off the leaf branch, `V = .ret (check …)`.
  - `V_queries_of_not_leaf`: off the leaf branch, `queries = []`.
  - `leafProg_queries`: the only queries are `LV.prog`'s, and only when the header holds and
    `n ≠ 0`.
- **Controls** (§10.1, top level).
  - Setting: `zeroLeaf` is an 80-byte leaf with `n = 0` and `h = s = 01…01`. `zeroLeaf_parse` is a
    kernel `decide`.
  - Positive:
    - `zeroLeaf_accepted`, assuming `LV.size 0 = 80`, as §7 says;
    - `zeroNode_accepted`, for the node over two zero leaves.
  - Negative:
    - `zeroLeaf_canaries` and `zeroNode_canaries` (one byte appended or removed);
    - `zeroLeaf_other_stmt` (any other statement);
    - `bad_tag_rejected` (tag 2, and a 1-byte proof).

## Checks

- `cd rf-core-sc && ./refresh-roots.sh && timeout 3600 lake build +SpartanChainVerifierTop`: green
  in 22.7 s, with no warnings.
- `#print axioms` on all 60 public definitions and theorems: every axiom set is a subset of `propext`,
  `Classical.choice` and `Quot.sound`. The scratch file is `rf-core-sc/scratch/VTAx.lean`.
- The source rule on the root: 37 files, 0 findings.
- `loc.py`: 375 code lines, 559 lines in total, 49 theorems.

## Open, and deviations

- **Left to other modules.**
  - The instance `LeafVerifier` (`leafSize`, which must satisfy `size_ge`, and the SNARK `prog`)
    belongs to `Verifier.lean`.
  - `submission`, `Vb_eq` (from `Vb_eq_vb`) and `fits_of_rel` belong to `Submission.lean`.
  - The leaf case of `final` belongs to the SNARK soundness modules, from `final_of_leaf`.
- **Signature.** The blueprint writes `leafProg c π`. Here `LV.prog` takes the parsed
  `(s, n, h, π_S)`, and `leafProg` does the parsing and the header checks, which are §1.3 steps 1
  and 2. `LV.size` is a parameter, and only `size_ge` is assumed. The control assumes
  `size 0 = 80` (§7: `leafSize 0 = 80`).
- **`check` and `checkNode`.** `check` inlines the node branch so that the recursion is one
  function. `checkNode` is the same code, stated separately, and `check_eq` connects the two.
- **Cost.** The node branch decodes and re-encodes each subproof, so a whole check costs
  `O(|π| · depth)`. This is S2a's measured property: 212.6 s at depth 2,000,
  `logs/V3-S2/review/caterpillar.log`. For the honest shape the depth is `r`.
- **Not claimed: hash inequalities.** The flipped-bit and swapped-children canaries need
  `nodeStmt c₂ c₁ ≠ nodeStmt c₁ c₂` or a statement inequality. Binding is proved instead.
