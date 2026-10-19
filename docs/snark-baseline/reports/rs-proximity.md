# Report: RS + Proximity (`SpartanChainRS`, `SpartanChainProximity`, `SpartanChainRSControls`)

Blueprint: `BLUEPRINT-R1.md` §5.1, §5.4, §5.5, §9.4 L-RS1…L-RS5, §10 rows `RS.lean` and
`Proximity.lean`, §10.1. Everything is in namespace `SpartanChain.RS` (controls in
`SpartanChain.RS.Controls`). **No `sorry`.** Every theorem listed below depends only on `propext`,
`Classical.choice` and `Quot.sound` (see `logs/spartan-chain/rs-proximity/axioms.log`). The source
rule reports `20 files, 0 finding(s)` on the root.

## What was built

The development is generic. `K` is a field, `E` is a field with `[Algebra K E]`, `ι` is a
`Fintype` of positions, and the points are `ω : ι → K`, which must be injective. The protocol sets
`K := F`, `E := EF`, `ι := Fin N`, `ω c := F.ofUInt64 c`, and passes `Fintype EF` (for example
`Fintype.ofFinite`). The proximity results hold for any linear code `C : Submodule E (ι → E)` that
satisfies `MinDist C d`.

### `SpartanChainRS.lean` (L-RS1, L-RS5)

| item | name |
|---|---|
| `W_i` (polynomial, unnormalised); `W_i(a)` by the value recursion | `W`, `wVal`, `wVal_eq` |
| `W_i` monic of degree `2^i` **for every** `κ` | `W_monic` |
| §5.1's constants `κ_i = W_i(pt i)` (pass `pt i = ω_{2^i}`) | `kappaArr` |
| `X_j = ∏_{i<ℓ} W_i^{bit_i j}`, value form | `basisPoly`, `basisVal`, `basisVal_eq` |
| **`basis_deg`**: `X_j` monic, `natDegree = j` for `j < 2^ℓ` | `basis_deg` |
| `Enc(msg)_c = Σ_j X_j(ω_c)·msg_j`, as a function and as an `E`-linear map; `C = range` | `enc`, `encL`, `rsCode` |
| C is the RS code: `c ∈ C ↔ ∃ p, natDegree p < 2^ℓ ∧ c = (p(ω_x))_x` | `mem_rsCode_iff` |
| **L-RS1 `code_dist`**: `MinDist (rsCode κ ℓ ω) (|ι| − 2^ℓ + 1)` given `Injective ω`; the two-codeword form is `MinDist.le_dist` | `code_dist`, `MinDist`, `MinDist.le_dist`, `MinDist.eq_of_agree` |
| `Enc` injective when `2^ℓ ≤ |ι|` | `enc_injective` |
| **L-RS5** linearity `Enc(Σ r_i Q_i) = Σ r_i Enc(Q_i)` | `encode_complete` |
| K rows encode to K rows; K-linear maps commute with `Enc` | `enc_algebraMap`, `enc_linearMap` |
| `C` is defined over `K` | `KRational`, `rsCode_kRational` |
| a K-valued codeword has a K-valued message | `msg_in_K` |
| verifier evaluation: `tensor` (`2^ℓ − 1` multiplications, `Array`), `encAt` (`Fin.foldl` dot product with `•`) | `tensorAux`, `tensor`, `encAt` |
| **L-RS5** tensor evaluation equals `Enc(·)_c` | `encAt_eq`, `tensor_getD`, `tensor_size` |

### `SpartanChainProximity.lean` (L-RS2, L-RS3, L-RS4)

| item | name |
|---|---|
| `Δ(w, C) ≤ e` | `Close`, `close_iff_agree` |
| `eClose U e` (§5.5), and its witness `(S, c)` | `eClose`, `IsDecomp` |
| affine-line lemma: more than `e+1` close points on `u + αv` and `3e < d` imply that `u`, `v` agree with codewords off one set of `≤ e` positions | `line_close` |
| far direction in the row span (AHIV22 Lemma 4.3 in the journal numbering) | `exists_far_comb` |
| **L-RS2** sharp: `≤ (e+1)·|E|^{m−1}` | `far_bad_card` |
| **L-RS2 `far_bad_le`**, as the blueprint states it | `far_bad_le` |
| **L-RS3** exact `(|ι| − |D|)^t`; `miss_le` with `a ≤ |D|`; rational form `(1−δ)^t·N^t` | `miss_card`, `miss_le`, `miss_le_rat` |
| **L-RS4** `close_unique` (`2e < d`), `close_in_K` (`KRational`, `e < d`) | `close_unique`, `close_in_K` |
| helpers for the close case of §5.5: a combination of a decomposition, and `d ≤ Δ(c, w) + |S|` | `IsDecomp.comb`, `dist_ge_of_agree` |

Exact statement of the main theorem:

```lean
theorem far_bad_le [Fintype E] (hC : MinDist C d) (h3 : 3 * e < d)
    (hdE : d < Fintype.card E) {m : ℕ} (U : Fin m → ι → E) (hfar : ¬ eClose C U e) :
    Nat.card {r : Fin m → E // Close C e (∑ i, r i • U i)} ≤ d * Fintype.card E ^ (m - 1)
```

How it is proved:

1. `line_close` takes two decoded points `α₁ ≠ α₂` and forms the line of codewords `u' + αv'`
   through them. Every other decoded point is on that line, because two codewords that agree off
   `≤ 3e < d` positions are equal. A double count (`Finset.card_mul_le_card_mul`) then gives
   `|D|(|A|−1) ≤ |A|e`, where `D = {(u, v) ≠ (u', v')}`. At each position of `D`,
   `a + αb = a' + αb'` holds for at most one `α` (`affine_eq_unique`). Hence `|D| ≤ e` as soon
   as `|A| ≥ e + 2`.
2. `exists_far_comb` assumes that every row-span word is close and inducts on the rows. The
   invariant is: there are codewords `c`, and a row-span word `u` with a codeword `ĉ`, such that
   `{u ≠ ĉ}` equals the joint disagreement set `S_j` of the first `j` rows, with `|S_j| ≤ e`. In
   the step, `line_close` is applied on the whole line `u + αU_j`. Uniqueness (`2e < d`) then
   puts `S_j` inside the new `D`. A scalar `α` that keeps every disagreement visible exists
   because at most `|S_{j+1}| ≤ e < |E|` scalars are bad. ArkLib proves this lemma with a
   maximal-support argument instead.
3. `far_bad_card` double counts with ArkLib's translation trick:
   `#bad·|E| = Σ_α #{r : P(r + αs)} = Σ_r #{α : P(r + αs)} ≤ |E|^m (e+1)`.

### `SpartanChainRSControls.lean` (§10.1)

- `enc_four`: `Enc` at `k = 4` is `m₀ + m₁X + m₂X(X+κ₀) + m₃X·X(X+κ₀)`, over any field.
- `kappa_toy`: over `ZMod 7` with `pt i = 2^i`, `kappaArr = #[1, 6]`.
- `enc_toy`, `encAt_toy`: `Enc(1,2,3,4)` equals the naive polynomial `1 + 5X + 4X³` at all 7
  points, both for the specification and for the verifier's `Array` code (`decide +kernel`).
- Negative controls for `Enc`: `enc_toy_ne_zero` (a nonzero message has a nonzero codeword) and
  `enc_toy_not_monomial` (`X_2 ≠ X²`).
- `eClose` on a `2×8` matrix over `ZMod 11` (`k = 2`, `d = 7`, `e = 2`):
  - `close_toy` is a positive instance.
  - `far_toy` is a negative instance whose two rows are each 2-close (`far_toy_rows_close`) but
    need 4 distinct columns together.
  - `far_toy_bound` instantiates `far_bad_le` on it, which shows the hypotheses can be satisfied.
- Tightness, `tight_toy`: for the repetition code over `ZMod 3` with `e = 0`, exactly
  `1 = (e+1)·|E|^{m−1}` coefficient makes the far row `(0,1)` close. So `far_bad_card` is tight.
  `far_bad_le`'s `d = 2` is attained up to the factor `d/(e+1)`.

## Is the blueprint's statement correct?

Yes, L-RS2 is true as written. It even holds with `(e+1)` in place of `d` and with
`e + 1 < |E|` in place of `d < |E|`; that stronger form is `far_bad_card`.

## Deviations

1. **Generic statements.** All results are generic, as the task asked: `MinDist` is a hypothesis,
   and `code_dist` discharges it for the RS code. `U` is `E`-valued; the protocol maps its `K`
   matrix through `algebraMap`. `close_in_K` and `msg_in_K` bring the decoded codewords and
   messages back into `K`.
2. **Any `κ`.** The code and every soundness property hold for every `κ`. `kappaArr` is provided
   for the honest prover and the NTT; the soundness results never mention it.
3. **Message type.** Messages are `Fin (2^ℓ) → E` in the specification. `encAt` takes an
   `Array E`, read with default `0`.
4. **Namespace and files.** Both modules use the namespace `SpartanChain.RS`, so that generic
   names (`enc`, `Close`) cannot collide in the umbrella. The controls are in their own module,
   not in `Controls.lean`, which belongs to group D.
5. **Counting form.** L-RS2 and L-RS3 are stated with `Nat.card` of subtypes, so no decidability
   instances appear in the statements. The `Finset.card` form follows from
   `Fintype.card_subtype`.

## What remains open

- Nothing in this group. The numeric bounds of §5.5 and R0/R7 at the protocol's parameters are
  now in `SpartanChainPCSBounds.lean`; see `ligero.md`.
- §14 asks for `Proximity.lean` to be "a port with provenance" of ArkLib's `AHIV22.lean`.
  - The statement of L-RS2 is unchanged.
  - The proof is independent, with ArkLib `7653a90` as the guide, cited in the module docstring.
- Build: the earlier `lake` problem is fixed by the orchestrator's `refresh-roots.sh`.
  `lake build +SpartanChainRSControls` is green.

## Measurements

| file | code lines (`loc.py`) | theorems | compile time (`lake env lean`, wall) |
|---|---|---|---|
| `SpartanChainRS.lean` | 313 | 31 | 7.3 s |
| `SpartanChainProximity.lean` | 274 | 13 | 8.3 s |
| `SpartanChainRSControls.lean` | 101 | 17 | 6.5 s |
| total | 688 | 61 | |

The logs are in `logs/spartan-chain/rs-proximity/`: `loc.log`, `axioms.log`, and one `<module>.log`
per module.

Imports are narrow:

- `SpartanChainRS`: `Polynomial.Roots`, `InformationTheory.Hamming`,
  `LinearAlgebra.Basis.VectorSpace` and `LinearAlgebra.Projection`.
- `SpartanChainProximity` adds `Combinatorics.Enumerative.DoubleCounting`,
  `Tactic.LinearCombination` and `Tactic.FieldSimp`.
- The controls add `Algebra.Field.ZMod` and `Tactic.NormNum.Prime`.

Nothing is copied from ArkLib. ArkLib's `ProximityGap/AHIV22.lean` (`7653a90`, which has no
`sorry`) was used as a guide only.
