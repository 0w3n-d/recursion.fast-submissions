# Report: non-vacuity controls of the `spartan-chain` entry (blueprint §10.1, §14 Controls)

This report lists every definition the certificate relies on, together with its positive and
negative control.

- **What a control is.** Each control is a kernel-checked theorem: either `decide` /
  `decide +kernel` on reduced objects, or a theorem about every instance.
- **No kernel BLAKE2s, except one file.** No control evaluates BLAKE2s in the kernel, except the
  existing transcript and Merkle KATs (`SpartanChainTranscriptControls`, 71 s, measured by their
  author).
- **New module.** `SpartanChainControls.lean` (this audit) holds the controls that were missing.
- **Checks.** All its theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`
  (`logs/spartan-chain/rs-proximity/axioms-controls.log`). `lake build +SpartanChainControls` is
  green, and the source rule reports `51 files, 0 finding(s)`.

File abbreviations:

- `C` = `SpartanChainControls`
- `FC` = `FieldControls`
- `MC` = `MLEControls`
- `RC` = `RSControls`
- `LC` = `LigeroControls`
- `PC` = `SoundnessPCSControls`
- `TC` = `TranscriptControls`
- `SLC` = `SoundnessLogControls`
- `VT` = `VerifierTop`

Every file name is prefixed `SpartanChain`.

## Inventory

| definition | positive control | negative control |
|---|---|---|
| `F` arithmetic (`*`, `sq`, `⁻¹`) | `FC:mul_x_x`, `FC:mul_wraps`, `FC:sq_top`, `FC:mul_inv_x` | `FC:mul_x_x_ne`, `FC:mul_wraps_ne`, `FC:inv_x_ne` |
| `EF` arithmetic | `FC:y_cube`, `FC:mul_inv_y` | `FC:y_cube_ne` |
| byte codecs `F.toBytes`/`EF.toBytes` | `FC:toBytes_le`, `FC:toBytes_bf64` | `FC:toBytes_not_be` |
| `eqTable`, `mleEval`, `bind0`, `bindT`, `eqPts` | `MC:eqTable_pos`, `MC:mleEval_pos`, `MC:bind0_pos`, `MC:bindT_pos`, `MC:eqPts_pos` | `MC:eqTable_neg` (bit order), `MC:mleEval_neg`, `MC:bind0_neg`, `MC:bindT_neg`, `MC:eqPts_neg` |
| `verifyRounds` (sumcheck verifier) | `MC:sumcheck_pos`; L-S4 `Sumcheck.sumcheck_complete` | `MC:sumcheck_neg`, `MC:sumcheck_neg_size` (wrong size), `MC:check_char_two` |
| sumcheck error bounds (L-S1/2/3) | tightness `MC:round_bad_tight`, `MC:zerocheck_tight`, `MC:batch_tight` | — (a tightness control is both: the bound is attained) |
| `Phi` / stages / `phiTable` | `MC:phi_zeros_pos` (all `f_p = 0`: the identity), `MC:phiTable_pos` | `MC:phi_neg` (one `f_p ≠ 0`: not the identity), `MC:phiTable_neg` |
| `weightEval` | `MC:weightEval_pos` | fixed exactly by L-R4 `weight_mle` |
| L-R1 over `F ⊂ EF` | `RingSwitchField:ring_inj_EF_single` | `RingSwitchField:conj_distinct_one_false`, `RingSwitchField:indep_one_false` |
| abstract `Sat` (R1CS) | `MC:sat_pos` | `MC:sat_neg` |
| chain block R1CS (`chainBlock`, L-C1) | `Blake2sR1CS:chainTrace_zero_kat` (KAT from the RFC/`hashlib`; `decide +kernel` on the contract's BLAKE2s step only) | `Blake2sR1CS:not_holds_flip` (any output bit flipped breaks `Holds`) |
| chain R1CS `ChainSat` (L-C2/L-C3) | `ChainSound:chain_complete` (honest witness, every `n ≤ 2^κ`) | **`C:chainSat_wrong_end`** (no Boolean witness for a wrong end) |
| RS encoding `enc`/`encAt`, `kappaArr` | `RC:enc_four`, `RC:enc_toy`, `RC:encAt_toy`, `RC:kappa_toy` | `RC:enc_toy_ne_zero`, `RC:enc_toy_not_monomial` |
| `eClose`, `Close`, `far_bad_le` | `RC:close_toy`, `RC:far_toy_rows_close`, `RC:far_toy_bound`, `RC:tight_toy` | `RC:far_toy`, `RC:U3_far` |
| `Dset`, far mode | `PC:toy_not_close`, `PC:toy_Dset_card` (`far_Dset_card`'s hypothesis is reachable) | `PC:zero_Dset` |
| `Decodes`/`qDec` | `SoundnessPCS:decodes_honest` | `SoundnessPCS:decode_unique` (no second decoding) |
| Ligero column check `colCheck` | `Ligero:colCheck_honest`; `Ligero:verify2_complete` | `LC:colCheck_tampered` |
| `Ligero.verify1` | `Ligero:prove1_verify1` | — (no checks of its own; it only runs the transcript) |
| `Ligero.verify2` | `Ligero:verify2_complete` (every oracle) | **`C:verify2_rejects_col`** (one failing opening rejects) |
| `snarkProg` (leaf SNARK) | `Prover:snark_complete` (honest proof accepted, every oracle, under `HonestOps`) | **`C:snarkProg_verify2`** + `C:verify2_rejects_col` + `LC:colCheck_tampered` (a tampered Ligero column is rejected); `SpartanProtocol:check_wrong_size` (63 slices rejected) |
| Spartan verifier (`Spartan.verify`) | `SpartanProtocol:complete`, `SpartanProtocol:check_honest` | `SpartanProtocol:check_wrong_size` |
| Merkle `verify`, `build` | `TC:kat_merkle_root`, `TC:kat_verify`; `Merkle:path_complete` | `TC:kat_verify_flip`, `TC:kat_verify_index` |
| `colL` / filled matrix | `TC:colL_log4` | `TC:colL_log4_missing` |
| transcript (`seed`, `absorb`, `squeeze`) | `TC:kat_transcript` | `TC:kat_transcript_root_ne` |
| `chE` | `TC:kat_chE` | `TC:chE_not_be` |
| `indices` | `TC:kat_indices` | covered by `TC:kat_indices` (exact value) |
| `Bad` | `TC:bad_stateHit` | `TC:not_bad_one` |
| `pathOf`, `IsChain`, `Matches` | `TC:pathOf_linked`, `SLC:honest1_chain` | `TC:pathOf_orphan`, `SLC:broken_not_chain`, `SLC:short_not_chain` |
| `OnFrontier` | `SLC:honest1_frontier` | `SLC:honest1_not_frontier` |
| `Rej` (checks (a)–(f)) | **`C:not_rej_short`** (no check applies before the first round polynomial) | **`C:rej_bad_size`** (a first outer round polynomial of the wrong size rejects) |
| `Alg` / `Doom` | **`C:doom_seed_false`** (a false statement is doomed at its seed) | **`C:not_doom_seed_true`** (a true one is not) |
| `EscAt` / `Esc` | **`C:escAtG_pos`** (the escape shape is reachable) | **`C:not_escAt_single`** (no escape at a one-entry chain) |
| `μ` | **`C:mu_empty`** (`μ [] = 0`) | **`C:mu_repeat`** (`μ = 1` on a log with a repeated query) |
| decoder `decodeF`/`encodeF` | `Decode:decodeF_encodeF` | `Decode:decodeF_bad_tag` |
| `leafProg`/`check`/`V` (top level) | `VT:zeroLeaf_accepted`, `VT:zeroNode_accepted`, `VT:check_encode_node` | `VT:zeroLeaf_canaries`, `VT:zeroNode_canaries`, `VT:zeroLeaf_other_stmt`, `VT:bad_tag_rejected`, `VT:leaf_push_rejected`, `VT:leaf_pop_rejected`, `VT:node_push_rejected`, `VT:node_pop_rejected` |
| claim / certificate numbers | `Submission:certificateR_claim` | `Submission:claim_negatives` (image, fuel, `qV`); **`C:claim_eps_negative`** (`ε = 2^-130` declared: not certified) |
| booleanity of `w` (packing, `wDec_bool`) | `C:and_gadget_bool` (Boolean witnesses of the AND row are `(1, 1)`) | **`C:and_gadget_nonbool`** (non-Boolean `(y, y⁻¹)` satisfies it: the R1CS has no booleanity rows, so `chain_sound`'s `0/1` hypothesis is load-bearing) |
| PCS parameters (`t = 260`) | `PCSBounds:pow17_le`, `PCSBounds:shape_table` | `PCSBounds:pow17_259` (`t = 259` is not enough) |

**Bold** marks the controls added in `SpartanChainControls.lean` by this audit.

## Notes and gaps

- **Tampered column.** "A leaf proof with a tampered Ligero column is rejected by `snarkProg`" is a
  chain of three theorems:
  1. an accepting `snarkProg` passes `verify2` on its arguments (`snarkProg_verify2`);
  2. `verify2` rejects when any opening fails its column check (`verify2_rejects_col`);
  3. a column with one entry changed fails the check (`colCheck_tampered`).

  A concrete run would need BLAKE2s in the kernel, which the brief rules out.
- **`Rej` has no positive control on honest messages.** A tiny-instance control showing that
  `Rej` accepts the honest messages needs a full honest chain (BLAKE2s-chained states). The
  substitute is `not_rej_short`, which shows `Rej` is not trivially true; `snark_complete` covers
  the honest run of the verifier itself. The completeness module (group D) is the place for a
  theorem-level "honest chain ⇒ ¬Rej".
- **No reachable `Esc` control.** A positive `Esc` control on a real chain would need an actual
  escape (for example an R0 answer tuple making a far `U` close), so the positive control is on
  the generic shape (`escAtG_pos`). The escape bounds themselves are proved: `r0_esc_le`,
  `r7_esc_le`, and the KS module's `esc_single_le`.
- **Code-level change.** While writing this audit I adapted `SpartanChainSoundnessFinal` to the
  KS agent's latest `SoundnessDefs` (`PosClass.r7`, `AlgRow`, `stmtOf` through `entAt`). It builds
  green again, and `posClass_last` now takes `0 < nJ κ`, proved for every chain by `kapOf_le` and
  `nJ_pos`.
