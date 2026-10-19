# Report: the knowledge state of the leaf SNARK (`SoundnessDefs`, `SoundnessKSBase`, `SoundnessKS`, `SoundnessKState`)

BLUEPRINT-R1 §9.2–§9.4: `Rej`, `Alg`, `Doom`, `EscAt`, `Esc`, `ext`, `ext1`, `condCount`,
`pRound`, `μ`, the `step` law, and L-K5 `kstate`, L-K6 `ks`. The `final` law (`doom_of_not_esc`,
L-K3 `accept_not_doomed`, `mu_final`) is the log/PCS agents' (`SpartanChainSoundnessFinal`,
`SpartanChainSoundnessChain`, `SpartanChainSoundnessKSFinal`); it is plugged in here.

- **Status.** No `sorry` in the four modules. All build (`lake build +SpartanChainSoundnessKState`).
- **Axioms.** `ks`, `kstate`, `mu_step`, `chainEvals_ok`: `propext`, `Classical.choice`,
  `Quot.sound` only (`logs/spartan-chain/soundness-ks/axioms.log`).
- **Source rule.** `source-rule: 59 files, 0 finding(s)`.

## The result

```lean
-- SpartanChainSoundnessKState.lean, namespace SpartanChain.KS
noncomputable def kstate : KState (Rel (vb LV)) (V LV) WitnessSending.E εKS
theorem ks : RecursionFast.KS (Rel (vb LV)) (V LV) WitnessSending.E εKS (2 ^ 14)
-- LV := Leaf.leafVerifier chainEvals (SoundnessKSFinal.LV), εKS := (2 : ℝ≥0)⁻¹ ^ 129
```

`kstate` is `⟨μ chainEvals, mu_empty, mu_step_chain, SoundnessKSFinal.final_law⟩`; `ks` adds
`V_queries_le` (L-Q1: `Leaf.queries_le` on the leaf branch, no query elsewhere).

## Modules

| module | content |
|---|---|
| `SpartanChainSoundnessDefs` | all §9.2–§9.3 definitions (below) |
| `SpartanChainSoundnessKSBase` | the generic step law, positions, locality, `rej_mono`, `doom_mid`, the R0/R7 round bounds |
| `SpartanChainSoundnessKS` | `doom_absorb`, `esc_single_le`, `chainEvals_ok`, `mu_step`, `mu_step_chain`, `mu_empty` |
| `SpartanChainSoundnessKState` | L-K5 `kstate`, L-K6 `ks`, `V_queries_le` |

**Definitions** (`SoundnessDefs`, namespace `SpartanChain.KS`). Generic in a doom predicate
`D L₀ es` and a charge `φ L₀ es`: `EscAtG`, `EscG`, `termG`, `sumG`, `muG` (§9.3's `μ`). Rounds:
`pre8`, `rnd κ p` (R0 `(1, rows κ)`, R7 `(pV κ, J)`), `lastAns`, `ext1`, `ext` (a fold of `ext1`),
`stmtOf`, `kapOf`, `condCount D L₀ es₀ r pre`, `pRoundG`. The leaf view: positions `pU pTau pG
pTri pGi pS pF pGr pV`; data `rootOf rVec ubarOf tauOf gOut rxOf triOf rhoOf gIn ryOf slicesOf
fsOf gRs rrOf vOf bOf rhiOf aOf`; claims `clOut clIn clRs`; `RoundOK`; **`Rej ev es`** (checks
(a)–(f), literally the verifier's tests); `FS`, `Far`, `FarDoom`, `qPack`, `qPlane`, `deltaOf`,
`wX`, `zOfU` (`= zDec`), `matA/B/C` (the chain matrices), `fTbl oTbls iTbls wTbls`, `SumWrong`,
`Dof`, `VWrong`; `PosClass`, `posClass`, `stepOf`; **`AlgRow`/`Alg`** (§9.2's table, one row per
class); `Uof`; **`Doom ev L₀ es := Rej ev es ∨ Alg (kapOf es) (Uof L₀ es) es`**; `EscAt`, `Esc`,
`pRound`, **`μ ev := muG (Doom ev) (pRound ev)`**.

## What is proved (blueprint name → Lean)

| blueprint | Lean | where |
|---|---|---|
| `empty` | `muG_empty`, `mu_empty` | KSBase, KS |
| `mu_le`, `step_bad`, `step_split`, §9.3 steps 1–5 | `muG_step` (helpers `termG_append`, `sumG_append`, `escG_append`, `L₀_new`, `new_seed`, `card_bad_le`) | KSBase |
| §9.3 step 4 by position | `hloc_of` (from `habs`, `hmid`, `hsingle`, `hround`), `muG_step_of` | KSBase |
| `eps_budget` + `2^-256` | `eps_le` (`B/2^256 + (4/5)·2^-129 ≤ 2^-129`), `single_le_δ` | KSBase |
| `condCount_split`, `condCount_last` | same names (from `extCount_split`) | KSBase |
| `rej_mono` | `rej_mono`, `rej_of_agree`, `rej_append_iff_full`, `not_rej_early` | KSBase |
| `doom_mid` | `doom_mid` | KSBase |
| `r0_esc_le`/`r7_esc_le` instantiated | `round_r0_le`, `round_r7_le`, `round_le` | KSBase |
| `doom_absorb` | `doom_absorb`, with `absorb_g0` (`zc_end`, `outer_start`), `absorb_tri` (`outer_final`, check (b), `eqPts_eq`, `triple_wrong`), `absorb_sl` (`inner_final`, check (d), `ne_of_claim`, `zV_eq_of_delta` = `z_mle_slices` in `zOf`'s layout + `pub_mle`), `absorb_gR0` (`rs_end`, `prod_trueSum`, `qPack_eq_sum`), `absorb_v` (check (f), `weightEval_mle` = L-R4, `ne_of_claim`, `mle_pack` = L-E3 with `eval_of_correct`'s order) | KS |
| `esc_single_le` | `esc_single_le` (`esc_tau0` via `ftbl_ne_zero` = L-C2 `chain_sound` + `wDec_bool` + `zc_start` (S2b-M4); `esc_tauS` `zc_escape_le`; `esc_rx`/`esc_ry`/`esc_rr` `round_escape_le` + `bindAll_snoc`; `esc_rho` `batch_escape_le`; `esc_f0` `ring_inj_EF` + `rs_start`; `esc_fS` `rs_escape_le`; `esc_card` `card_chE_mem`) | KS |
| `mu_step` | `mu_step ev (hev : EvalsOK ev)`, `mu_step_chain` | KS |
| evaluator correctness (S2b-m1) | `chainEvals_ok : EvalsOK chainEvals` (`chainMats_eq`, `matMle_cast`, `chainPub_eq`) | KS |
| L-K5, L-K6 | `kstate`, `ks` | KState |

## Deviations from the blueprint

1. **Module split.** `SoundnessDefs` (asked by the orchestrator), `SoundnessKSBase` (the stable,
   generic part, split off for build time), `SoundnessKS`, and `SoundnessKState` (needs
   `SoundnessKSFinal`, so `kstate`/`ks` are not in `SoundnessKS`).
2. **Generic layer.** `EscAt`, `Esc`, `μ`, `pRound` are instances of `EscAtG`, `EscG`, `muG`,
   `pRoundG` for `D := Doom ev`. `mu_le`, `step_bad`, `step_split` are steps inside `muG_step`, not
   separate theorems.
3. **`condCount` takes the round length `r` explicitly** (`condCount D L₀ es₀ r pre`); `ext` is a
   fold of `ext1`.
4. **`Alg` by `PosClass`.** One class per §6.2 step (`r0 j`, `r7 j` carry the answer count).
5. **`δ_i` uses the bit planes** `Q_i(u') = w_dec(i + 64u')` (`qPlane`). The blueprint's
   "`Q^{dec}_i := EF.ofF ∘ qDec κ U i`" indexes a row, not a bit plane.
6. **`EvalsOK ev`** is the hypothesis of `doom_absorb`/`mu_step` (check (d) is false for arbitrary
   `ev`, S2b-m1). It is discharged for `chainEvals` (`chainEvals_ok`); `kstate` uses `chainEvals`.
7. **Checks are the verifier's.** Check (b) uses `eqPts τ r_x`, (f) uses `weightEval` and
   `dot (eqTable r''_lo) v`; `RoundOK d g c := g.size = d + 1 ∧ g(0) + g(1) = c`.
8. **`chainEvals_ok`** rewrites `(chainEvals κ n s h).pub` by `simp only [chainEvals]`: the definitional unfolding by `rfl` exceeds the recursion limit.
   instance); no axiom or `native_decide` is involved.

## Open, or for others

- Nothing open in these modules. `controls.md` should now cite `KS.esc_single_le` (it exists).
- The packing identity is `SoundnessPack.qPack_eq_sum` (PCS agent); `final_law` is
  `SoundnessKSFinal` (log agent).

## Measurements

Lines (`loc.py`): Defs 257, KSBase 1654, KS 841, KState 23 code lines (2775 total, 228 theorems).
Check time (`lake env lean`, wall): Defs 42.0 s, KSBase 38.3 s, KS 11.7 s, KState 6.6 s
(`logs/spartan-chain/soundness-ks/*.log`).
