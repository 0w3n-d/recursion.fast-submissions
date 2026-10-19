# Report: L-R1 at the word-level field, and the algebraic rounds R1–R6 (`SpartanChainRingSwitchField`, `SpartanChainSoundnessSpartan`)

Blueprint: `BLUEPRINT-R1.md` §3, §4, §9.2 (the revised table, after review), §9.4 and §14.
Everything is in namespace `SpartanChain`.

**Status**

- **No `sorry`.**
- All six of my modules build with `lake build +SpartanChain…` in `rf-core-sc`, after
  `./refresh-roots.sh` (log: `logs/spartan-chain/mle-sumcheck-ringswitch/lake-build-2.log`).
- Axioms (`axioms-2.log`):
  - Every theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
  - The `decide` controls use only `propext` and `Quot.sound`.
  - `rs_start` uses no axioms.
- The source rule reports `30 files, 0 finding(s)`.

## 1. L-R1 at `F`/`EF` (`SpartanChainRingSwitchField.lean`)

| item | name |
|---|---|
| Frobenius periods from `card_F`, `card_EF` | `F.pow_two_pow_64`, `EF.pow_two_pow_192` |
| coordinates: `⟨a, b, c⟩ = a + b·y + c·y²` (through `ringEquivExt3`, `toExt3_eq`) | `EF.mk_eq` |
| `EF = F + F y + F y²`; `1, y, y²` independent | `EF.span`, `EF.indep` |
| **L-R1 at the protocol's fields** (`n = 64`, `x = F.x`, `y = EF.y`) | `ring_inj_EF` |
| positive control: a wrong first slice is detected | `ring_inj_EF_single` |
| negative controls: `hconj` fails for `x = 1`; independence fails for `y = 1` | `conj_distinct_one_false`, `indep_one_false` |

- The bases `1, y^{2^k}, y^{2^{k+1}}` come from `ybasis_of_period`, using the period and
  `EF.indep`. `EF.ybasis`, with its determinants, is not used.
- Nothing in the field files needs to change. The coordinate lemmas are in my module.
- `ring_inj_EF` is unconditional, so L-R1's hypotheses are shown to be satisfiable: it is not
  vacuous.

## 2. The algebraic rounds (`SpartanChainSoundnessSpartan.lean`)

**Setting.**

- The R1CS is abstract:
  - matrices `A B C : Fin (2^a) → Fin (2^b) → E` on the cube;
  - their extensions `matMle` (`M̃(r_x, r_y) = Σ eq·eq·M`);
  - `matVec`, `Sat` and `residual` (`F = Az·Bz + Cz`).
- The extended witness is any `z : Fin (2^b) → E` (the close-mode `z_dec`).
- `E` is a field of characteristic 2; `K` with `[Algebra K E]` is used for ring switching.
- The chain circuit plugs in through `matrix_mle_eq` (Chain.lean), which states that the
  verifier's formulas equal `matMle`.
- Tables are `Array`s viewed through `tbl` (`Array.ofFn` of a function, `tbl_ofFn`).
- `trueSum e ts m` is `Σ_u e(tables at u)`. `bindAll` and `bindT` bind challenges in order,
  variable 0 first.

**Lemma shape.** Each round's lemma has the form the potential needs. From a doomed state
(stated as hypotheses), the number of challenge values in `E` that give a non-doomed next state
is at most the bound. Rows without a challenge are "after" lemmas, which carry doom by equality,
with no division (BP-m13).

| §9.2 row | doom | lemma | bound |
|---|---|---|---|
| start | `¬Sat` ⇒ residual table `≠ 0` (`P_0 ≢ 0`) | `zc_start` | — |
| R1 `τ_l` | `tbl (m+1) t ≠ 0` (bound residual, i.e. `P_l ≢ 0` by `mle_cube`/`eq_zero_of_mle`) → `tbl m (bind0 t τ_l) = 0` | `zc_escape_le` | **1** |
| R1 end | `tbl 0 (bindT t τ) ≠ 0` ⇒ `F̃(τ) ≠ 0` ⇒ outer claim `0` false | `zc_end`, `outer_trueSum`, `outer_start` | — |
| R2 `r_{x,l}` | `claim ≠ trueSum outerExpr ts (m+1)`; escape: check passes ∧ `g(r) = trueSum (ts bound at r)` | `round_escape_le` (`outerExpr_deg = 3`) | **3** |
| after R2 | final value `eq(τ,r_x)·(t_A t_B + t_C)` (`outer_final`); passing check ⇒ wrong triple | `outer_final`, `triple_wrong` | — |
| R3 `ρ` | wrong triple; escape: `v_A + ρv_B + ρ²v_C = trueSum innerExpr (innerTables r_x ρ …)` | `batch_escape_le` (with `inner_trueSum`) | **2** |
| R4 `r_{y,l}` | as R2, `innerExpr` | `round_escape_le` | **2** |
| after R4 | final value `M̃_ρ(r_x,r_y)·z̃(r_y)` (`inner_final`); `z̃` from slices (`z_mle_slices`); passing check ⇒ wrong slices | `inner_final`, `z_mle_slices`, `ne_of_claim` | — |
| R5 `f_p` | `rsDoom w δ s' fs` (`∃ k < 2^{s'+1−p}, π_k(Φ_p δ) ≠ 0`); start from L-R1 | `rs_start` (+ `ring_inj_EF`), `rs_escape_le` | **1** |
| after R5 | `rsDoom` after `s'+1` stages ⇒ `T ≠ Σ_u Φ(eq(r,u))·q(u)` | `rs_end` | — |
| R6 `r''_l` | as R2, tables `#[W, q]` (`prod_trueSum`) | `round_escape_le` | **2** |
| after R6 | `claim ≠ W̃·q̃` ∧ `claim = W̃·v'` ⇒ `v' ≠ q̃` | `ne_of_claim` | — |

Sumcheck additions (in `SpartanChainSumcheck.lean`):

- `trueSum`, `tbl_map_bind0`, `roundPoly_check`, `roundPoly_next`, `bindAll`,
  `trueSum_bindAll` and `verifyRounds_honest`.
- **`round_escape_le`**, the generic R2/R4/R6 lemma. It holds for any `g`: a `g` of the wrong
  size or failing the check has an empty escape set.
- `sumcheck_complete` (L-S4) has an unchanged statement and is re-proved through these lemmas.

Controls (`SpartanChainMLEControls.lean`, added):

- `bindT` both ways;
- `sat_neg` and `sat_pos` (a one-row R1CS, unsatisfied and satisfied), so `zc_start`'s
  hypothesis is reachable;
- the tightness controls of L-S1/L-S2/L-S3 from before, which still apply.

## Line counts (`loc.py`)

```
file                                                          total  blank comment   code  thm
submissions/spartan-chain/SpartanChainMLE.lean                  382     64      64    254   33
submissions/spartan-chain/SpartanChainSumcheck.lean             448     68      78    302   34
submissions/spartan-chain/SpartanChainRingSwitch.lean           461     65      82    314   28
submissions/spartan-chain/SpartanChainRingSwitchField.lean       88     16      27     45    9
submissions/spartan-chain/SpartanChainSoundnessSpartan.lean     325     58      74    193   28
submissions/spartan-chain/SpartanChainMLEControls.lean          121     35      35     51   24
TOTAL                                                          1825    306     360   1159  156
```

## Deviations

1. **Module name.** It is `SpartanChainSoundnessSpartan.lean`, which is the flat form of
   `Soundness/Spartan.lean`.
2. **`FarDoom` is not here.**
   - In far mode §9.2 makes every escape set empty. That case analysis belongs to the potential,
     `Soundness/KS.lean`.
   - The lemmas here are the close-mode algebra, for a fixed `z_dec`/`q_dec`.
3. **R1 doom is stated on the bound residual table**, not on the polynomial `P_l`.
   - `mle_cube` and `eq_zero_of_mle` make the two equivalent.
   - The table form is what `zerocheck_bad_le` counts.
4. **The witness split is a hypothesis.** `z_mle_slices` takes `z = (w ‖ pub)` as `hz` on `join`,
   with the top variable selecting `pub`.
   - The chain's actual layout (`pub` positions, `pub̃` by 513 lookups) is Chain.lean's job.
   - The statement uses `1 − r_top`, which is `1 + r_top` in characteristic 2.

## Open

1. **`Soundness/KS.lean` must assemble the doom predicates.** The pieces are:
   - per chain, the table states of each round (`bindT`/`bindAll` of the prefix of challenges);
   - the transitions after each absorb (`triple_wrong`, `ne_of_claim`, `rs_end`);
   - the far case.

   The counting lemmas above are the per-answer bounds `1, 3, 2, 2, 1, 2` (over `|E|`).
2. **Chain.lean needs to connect its formulas to the abstract R1CS:**
   - `matrix_mle_eq` must yield `matMle`;
   - the R1CS must be `Sat`, matching L-C2.
