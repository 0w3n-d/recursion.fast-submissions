# Report: MLE + Sumcheck + RingSwitch (`SpartanChainMLE`, `SpartanChainSumcheck`, `SpartanChainRingSwitch`, `SpartanChainMLEControls`)

Blueprint: `BLUEPRINT-R1.md` §3, §4, §9.2–§9.4 (L-E1…L-E4, L-S1…L-S4, L-R1…L-R5), §10 rows
`MLE.lean`, `Sumcheck.lean` and `RingSwitch.lean`, and §10.1. Review: BP-m4 is handled (see
"Sumcheck"). Everything is in namespace `SpartanChain`.

- **No `sorry`.** Every listed theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`. The controls run by `decide` and use only `propext` and `Quot.sound`. Log:
  `logs/spartan-chain/mle-sumcheck-ringswitch/build.log`.
- The source rule reports `21 files, 0 finding(s)` on the root.
- The modules are **generic**. They import Mathlib only, never `SpartanChainField`.
  - `MLE` and `Sumcheck` work over `[CommRing R]`. The counting lemmas add
    `[IsDomain R] [Fintype R] [DecidableEq R]`.
  - `RingSwitch` works over `[CharP R 2]` and `[Field K] [Field E] [Algebra K E]`.
  - To plug in the word-level field, set `K := F` and `E := EF`. The `Algebra F EF`,
    `CharP` and `Field` instances already exist in `SpartanChainFieldExtCorrect`.

## What was built

Conventions:

- An index `u < 2^ℓ` stands for the Boolean point whose coordinate `l` is bit `l` of `u`
  (little-endian). Variable `0` is the low bit, and it is the variable bound first.
- The specification uses tables `Fin (2^ℓ) → R` and points `Fin ℓ → R`.
- The computable code uses tables `Array R` and points `List R` (points have at most 35
  coordinates). The two are bridged by:
  - `tbl ℓ t u = t.getD u 0`;
  - `pt r l = r[l]`;
  - `ptOf ℓ r l = r.getD l 0`.
- No computable definition builds a `List` of `2^k` elements or uses `Fin n → α` as data. Loops
  use `Nat.fold`, `Array.ofFn` and `Array.map`.

### `SpartanChainMLE.lean`

| item | name |
|---|---|
| Boolean point; `eq(a,b)=∏(a_l b_l+(1−a_l)(1−b_l))`; `f̃(r)=Σ_u eq(r,u)f(u)`; fixing variable 0 | `cube`, `eq`, `mle`, `fix0` |
| indices `2u+b`, `u₁+2^a u₂` and their equivalences | `dbl`, `join`, `dblEquiv`, `joinEquiv` |
| sum of a product of per-bit factors over the cube | `sum_cube_prod`, `sum_cube_succ` |
| **L-E1** `Σ_u eq(r,u) = 1` | `eq_sum_one` |
| **L-E2** `Σ_u eq(a,u)eq(u,b) = eq(a,b)` | `eq_mle` |
| **L-E3** tensor split, slice form `f̃(r₁,r₂) = Σ_{u₁} eq(r₁,u₁)·f(u₁,·)~(r₂)` | `mle_split` (with `eq_append_join`) |
| **L-E4** `eq(r,u)^{2^k} = eq(r^{2^k},u)` (char 2) | `eq_frob` |
| `f̃` on the cube is `f`; a zero extension means a zero table; fixing var 0 is evaluating it | `mle_cube`, `eq_zero_of_mle`, `mle_fix0` |
| computable `eq` table (one pass per variable, `2^{ℓ+1}` mults) | `eqTable`, `tbl_eqTable`, `tbl_eqTable'` |
| computable `f̃(r)`; bind variable 0; `eq` on two points | `mleEval`/`mleEval_eq(')`, `bind0`/`tbl_bind0`, `eqPts`/`eqPts_eq` |

### `SpartanChainSumcheck.lean`

| item | name |
|---|---|
| coefficient arrays: Horner, `+`, `×`, `toPoly` | `peval`, `pAdd`, `pMul`, `toPoly` (+ `peval_eq_sum`, `peval_pMul`, `coeff_toPoly`, …) |
| summand expressions (`var`/`add`/`mul`), value, degree, coefficient arithmetic | `Expr`, `Expr.eval`, `Expr.deg`, `Expr.evalPoly`, `Expr.evalPoly_size` |
| honest round polynomial (products of linear factors, no interpolation or inversion), all rounds | `linAt`, `roundPoly`, `honest`, `peval_roundPoly` |
| verifier rounds over an abstract claim: size `d+1`, `g(0)+g(1) = claim`, then claim `← g(r)` | `verifyRounds` |
| **L-S1** | `round_bad_le` (`Polynomial.card_roots'`), `round_bad_le_arr`, `round_bad_le_of_check` |
| **L-S2** | `zerocheck_bad_le` |
| **L-S3** | `batch_bad_le` |
| **L-S4** | `sumcheck_complete` |
| BP-m4: the check in characteristic two | `peval_zero_add_one` |

- **L-S4.** For tables of size `2^|rs|` and the true sum as the claim, `verifyRounds` on the
  honest polynomials returns `some (e.eval (i ↦ t̃_i(rs)))` for every list of challenges `rs`.
- **BP-m4.** The check is stated literally as `peval g 0 + peval g 1 = claim`.
  - `peval_zero_add_one` proves that in characteristic two this equals `Σ_{1≤i≤d} c_i`. So `c_0`
    is not constrained by the check and enters only the next claim `g(r)`. The control
    `check_char_two` exhibits this.
  - `round_bad_le_of_check` is L-S1 in the form the verifier's check gives. If `g` passes and the
    true `g*` does not, then `#{r : g(r) = g*(r)} ≤ d`.
  - The Rust prover and the verifier must agree that all `d+1` coefficients are sent.

### `SpartanChainRingSwitch.lean`

- **Copied** with a provenance block from leanerVM `532ebb457a6b…`,
  `LeanerVM/Protocol/ToArkLib/Flock/FrobeniusMap.lean` (Apache-2.0). Only the namespace and the
  `module`/`public` header changed. The copied declarations are `frobMap`, `frobTerms`,
  `frobMap_eq_sum` (**L-R5**), `frobMap_append`, `frobMap_add`, `frobMap_zero`, `frobMapHom`,
  `frobPair`, `frobPair_stage`, `card_frob_root_le_one` and `card_stage_zero_le_one`
  (**L-R2**, copied form).
- **Stages.** `stages s' fs`: stage `p` is `(2^{s'−p}, f_p)`. Lemmas: `stages_cons`,
  `stages_append`.
- **`Φ`.** `Phi fs` applies all stages. `frobMap_stages_zeros` proves that `Φ` with every
  coefficient zero is the identity.
- **Computable code** (squarings, no `npow`):
  - `sqIter`, `frobMapC`, `phiApply` (`phiApply_eq`);
  - `phiTable`, the `c_k` table, built by concatenation stage by stage;
  - **L-R5 dense form** `Phi_eq_table`: `Φ(a) = Σ_{k<2^|fs|} c_k a^{2^k}`;
  - `target` (`T = Σ_i x^i Φ(s_i)`, Horner, `target_eq`);
  - `weightTable` (the prover's `W(u') = Φ(eq(r,u'))`);
  - `weightEval` (`W̃(r'') = Σ_k c_k eq(r^{2^k}, r'')`, with the point squared once per `k`;
    `weightEval_eq`).
- **L-R1 `ring_inj`.** If `δ ∈ E^n` and `δ ≠ 0`, then `∃ k < n, Σ_i x^i δ_i^{2^k} ≠ 0`.
  - The proof follows Annex A §A.3. It splits each `δ_i` into `K`-coordinates on `1, y, y²`, uses
    the `K`-independence of `1, y^{2^k}, y^{2^{k+1}}`, and then applies a Vandermonde argument in
    the conjugates (`frob_sums_eq_zero`).
  - Hypotheses, which are the field facts:
    - `hconj`: `((List.range n).map (x^2^·)).Nodup`, verbatim `F.conj_distinct` with `n = 64`;
    - `hK`: `a^{2^n} = a` on `K`, from `nat_card_F` and `FiniteField.pow_card`;
    - `hspan`: `E = K + Ky + Ky²`;
    - `hbasis`: the `ybasis` facts, in independence form.
- **`ybasis_of_period`.** `hbasis` follows from the period `e^{2^N} = e` of `E` (`N = 192`) and the
  independence of `1, y, y²` alone. The 64 kernel determinants are therefore not needed (compare
  review BP-m10).
- **L-R2 `stage_bad_le_one`** (protocol form). Suppose that after `p ≤ s'` coefficients some
  `π_k ≠ 0` with `k < 2^{s'+1−p}`. Then for all but at most one next `f`, some `π_k ≠ 0` with
  `k < 2^{s'−p}`.
- **L-R3 `ring_complete`.** For any additive `Φ`:
  `Σ_u Φ(eq(r,u))·q(u) = Σ_i x^i Φ(Q̃_i(r))` with `q = Σ_i Q_i x^i` and `Q_i` Boolean.
- **`ring_final`.** `T − Σ_u W(u)q(u) = π_0` of `Φ(s_i − Q̃_i(r))`. This is the "after R5"
  link of §9.2.
- **L-R4 `weight_mle`.** `W̃(r'') = Σ_k c_k eq(r^{2^k}, r'')`. Its computable form is
  `mleEval_weightTable`: the verifier's `weightEval` equals the extension of the prover's
  `weightTable`.

### `SpartanChainMLEControls.lean` (§10.1)

Positive and negative controls, run by `decide` (`decide +kernel` for two of them):

- `eqTable`, including a negative control for the wrong bit order;
- `mleEval` at Boolean points, `bind0` and `eqPts`;
- the sumcheck: an honest run with its exact final value, a false claim rejected, a wrong size
  rejected, and the char-2 `c_0` behaviour;
- `Φ`: the identity when all `f = 0`, and not the identity when `f = [1]` over `ZMod 2`;
- `phiTable`, both ways, and `weightEval` against `mleEval ∘ weightTable`.

Tightness controls show that the L-S1, L-S2 and L-S3 bounds are attained, at 2, 1 and 2.

## Line counts (`loc.py`)

```
file                                                          total  blank comment   code  thm
submissions/spartan-chain/SpartanChainMLE.lean                  380     64      63    253   33
submissions/spartan-chain/SpartanChainSumcheck.lean             395     59      66    270   27
submissions/spartan-chain/SpartanChainRingSwitch.lean           459     65      82    312   28
submissions/spartan-chain/SpartanChainMLEControls.lean          103     30      30     43   20
TOTAL                                                          1337    218     241    878  108
```

Each module compiles in 6–8 s wall (`build.log`).

## Build note

The scratch lakefile is fixed (`rf-core-sc/refresh-roots.sh`). `lake build +SpartanChainMLE …
+SpartanChainMLEControls` succeeds (`logs/spartan-chain/mle-sumcheck-ringswitch/lake-build-2.log`).
The follow-up work is in `soundness-spartan.md`: L-R1 at `F`/`EF`, the R1–R6 lemmas, and the
sumcheck lemmas `trueSum`, `round_escape_le` and `bindAll`.

## Deviations from the blueprint

1. **Generic, no `Field` import.** The modules do not depend on the field module, which the
   blueprint lists as a dependency. They are generic, so the word-level field plugs in by
   instantiation. The `F`/`EF` instantiation of L-R1's hypotheses is an integration step that has
   not been done (see "Open").
2. **L-S1 drops the hypothesis `g(0)+g(1) = g*(0)+g*(1)`.** The bound does not use it, so the
   statement is stronger. `round_bad_le_of_check` adds the verifier-check form.
3. **L-R1's `ybasis` is a hypothesis in independence form**, not the `Matrix.det ≠ 0` form of
   `EF.ybasis`. It is also derivable through `ybasis_of_period`, so the integration may skip the
   determinants.
4. **L-S2 is stated on tables** (`fix0 f c = 0` for a nonzero table `f`). The polynomial reading
   in §9.2 (`P_l ≢ 0`) is equivalent by `mle_cube` and `eq_zero_of_mle`.
5. **The `c_k` table is built by concatenation** (later stages first: `t ++ t·f^{2^e}`), not by
   §4.3's `T_{p+1}` recursion. The values are identical, and `Phi_eq_table` proves them. Building
   it costs about 650 squarings instead of 192, which is negligible.
6. **`Expr` has no subtraction.** In characteristic two, write `A·B − C` as `A·B + C`.

## Open

- **Instantiate L-R1 at `K = F`, `E = EF`, `y = EF.y`, `n = 64`.** Now done, as `ring_inj_EF`;
  see `soundness-spartan.md`. The pieces:
  - `hconj := F.conj_distinct`;
  - `hK` from `nat_card_F`;
  - `hspan` from the `EF.mk` coordinates;
  - `hbasis` by `ybasis_of_period` with `N = 192` (`nat_card_EF`) and the independence of
    `1, y, y²`.

  This also gives L-R1 its non-vacuity control. It needs coordinate lemmas for `EF`, such as
  `x = ofF c₀ + ofF c₁·y + ofF c₂·y²`, from the field module.
- **The per-round state functions (R1–R6) belong to `Soundness/Spartan.lean`.** The lemmas here
  have the shapes §9.2 needs: `zerocheck_bad_le`, `round_bad_le_of_check`, `batch_bad_le`,
  `stage_bad_le_one`, `ring_inj` (the state at `p = 0`) and `ring_final` (the state after R5).
