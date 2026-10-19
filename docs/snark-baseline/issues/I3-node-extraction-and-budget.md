Node extraction is decoding, not log lookup, and `extractorBudget` is sized for the proof rather than the committed word: no honest recursive extractor fits

## Summary

Child proofs of a recursive node cannot be read off the query log. `Rel` requires the children to be
accepted by `Vb`, which runs **concrete BLAKE2s**, while the log holds answers of the **random**
oracle. The only object a proof can tie to `Vb c₁ π₁ = true` is the node circuit's witness, so a
node extractor must decode the committed codeword in the log. That word is about `2^29` symbols at
node size, and a quasi-linear decoder needs about `2^43` RV64 steps (estimate), against
`B t = 2^40 + 2^8·t`. The header of `Extractor.lean` sizes `2^40` for "a `2^20`-byte proof", but
the decoder's input is the log, not the proof. A verified quasi-linear Reed–Solomon decoder in
RV64 assembly is a project in its own right, not a baseline component. The node extraction rule
needs a decision.

## The problem

For readers new to the contract. The certificate's knowledge clause is a named extractor `E` that
returns a witness from (statement, proof, query log), together with a RISC-V image that provably
computes `E` within a step budget (`ImageComputes`, decision Q1). The relation (`Relation.lean:87-89`):

```lean
def Rel (Vb : Digest → Proof → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true
```

`Certificate.secure` is `KS (Rel S.Vb) S.V S.E …` (`Certificate.lean:62`), with
`S.Vb c π = (S.V c π).run blake2sOracle` (`:56-57`). `final` must produce `π₁` with
`Vb c₁ π₁ = true` from `(c, π, L)` for every good log `L`, whose answers are arbitrary digests.

1. **Lookup is unprovable** (F1 §3.1). Suppose the prover queried `H(π₁)` and `E` finds the entry
   whose answer the node proof carries. The SNARK attests, through an in-circuit BLAKE2s, that
   *some* `π₁'` with `BLAKE2s(π₁') = h₁` is accepted. The log's `H`-preimage of `h₁` is unrelated.
   Rebuilding the child's Merkle paths from `L` fails the same way: they are `H`-valid, while `Vb`
   needs them BLAKE2s-valid.
2. **Decoding is forced.** The only provable route is a circuit-correctness lemma
   `R1CS_node(c, c₁, c₂, z) → ∃ π₁' π₂', z encodes them ∧ Vb c₁ π₁' ∧ Vb c₂ π₂'`, where `z` is the
   committed witness. `E` must find the tree under the root in `L`, read the codeword and **decode**
   it. Reading the systematic part is not enough: a word corrupted in one unopened systematic
   position is accepted with probability about `1 − t/n`.
3. **The budget** (`Extractor.lean:92`): `def extractorBudget (t : ℕ) : ℕ := 2 ^ 40 + 2 ^ 8 * t`.
   Its header (`:34-38`) says "`2^40` covers a quasi-linear decoder of a `2^20`-byte proof with a
   large constant". The word to decode lives in the **log**, not in the proof (finding F1-3).

Leaves are fine. A leaf witness is 40 bytes. Put it in the clear at the head of the leaf proof and
`E` parses it with the existing 8-instruction image. The leaf SNARK then needs only soundness for a
public computation (F1 §3.2).

## Why it matters

The first certified *recursive* entry is blocked whatever proof system it uses. Every Merkle-
committed code-based node extractor must decode, and none fits the budget. Even an
in-budget decoder must be RV64 assembly proved against `Machine.run`, with
`Library/Machine.lean`'s symbolic execution as the only tooling. CompPoly has a Lean-level Gao
decoder (`CompPoly.Univariate.ReedSolomon.GaoDecoder`, `GaoCorrectness`), but it is not
allowlisted and it is not an image. Decision Q1 assumed that extraction is cheap for straight-line
extractors. That assumption holds for leaves and fails for nodes.

## Evidence (paper sizing; every number here is an estimate)

From F1 §3.3, after R7 §2.2 and §5.3 and WHIR Table 5 (UD column). BLAKE2s in R1CS over `BF64`
with bits as variables costs about `2^14` constraints per compression (320 32-bit additions at
about 50 constraints each).

| Quantity | Value |
|---|---|
| compressions to verify one UD-provable 128-bit PCS proof at `2^24`–`2^28` | 10k–14k |
| node circuit (two children) | `≈ 2·10^4 · 2^14 ≈ 2^28.3` constraints |
| committed word at rate 1/2 | `≈ 2^29` symbols, about 4 GiB of log |
| tape `t` | `2^29`–`2^30` words, so `B t ≈ 2^40.1`–`2^40.3` |
| quasi-linear RS decoding (fast Euclid over the additive NTT) | `≈ 2^38.7` field ops, `≈ 2^43` RV64 steps with Zbc |
| quadratic (Gao/Euclid, schoolbook) | `≈ 2^58` |

ADV-M7 reaches the same conclusion independently: Berlekamp–Welch on a `2^23` word is `≈ 2^46`.

## Options

| Option | Trust cost | Who pays | Assessment |
|---|---|---|---|
| **Raise `B`** to `2^48 + 2^16·t` | none: `2^48` still excludes `2^128` enumeration, and `Rel` has no 64-bit secret | one constant (O-21 is open anyway) | do it regardless; a quasi-linear decoder then fits |
| **Organiser decoder image** (O-15(2)), with a calling convention and composition lemmas in `Library/Machine.lean` | none (kernel-checked) | the organiser: a verified decoder | the right long-term answer; large; O-15(2) becomes a precondition of board T |
| **Lean-level cost model for `E`**: a first-order extractor language (log, word and field primitives, bounded loops) with a step-counting interpreter in the contract, about 60–100 lines | the interpreter's semantics, and that each primitive is `O(1)` machine work (must exclude bignum `Nat` and one-step list-length gaps) | the organiser once; submitters then reason about structured programs, not assembly | viable; moderate growth of the trusted base; this is ADV1's "relax Q1" |
| Measured extractor time (like `T_V`) | the knowledge content drops to soundness plus a liveness test | — | reject |
| `E` noncomputable, `ImageComputes` dropped | same | — | reject |

Proposal: raise `B` in the same contract change as the KS amendment. Put the choice between the
organiser decoder and the cost model to the user, noting that the first recursive certification is
blocked on it either way. Meanwhile the honest baseline (S2b, R1) uses parsing leaves and
witness-sending nodes, so it needs no decoder.

Side effects of raising `B` are mechanical. Three proof terms mention `8 ≤ 2 ^ 40`
(`Library/WitnessSending.lean:264`, `Controls/Certificate.lean:54`, `Controls/Backdoor.lean:155`)
and change to `2 ^ 48`. The negative control `fuel_over_budget_claim` (`Controls/Certificate.lean:69-71`,
declared fuel `2 ^ 41`) and the S2a entry's negative claim `fuel_base = 2^41` need a constant above
the new budget.

## Cross-references

F1 §3, §6, F1-3; ADV-M7; DESIGN-v3 §4.4, §5.4 (ROM-recursion heuristic), §6.6 (extractor row);
O-15(2), O-21; decision Q1 (`docs/design/DISCUSSION.md`); KS amendment issue (the `logCap` domain
`≤ 2^60`-word tape, ADV-m7).
