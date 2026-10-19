# Report: PCS-level soundness (`SpartanChainSoundnessPCS`) and Ligero controls (`SpartanChainLigeroControls`)

These modules cover blueprint §9.1–§9.2 (the filled matrix, R0, the close and far modes,
decoding, R7, and the "after `v`" link) and §10.1 (the Ligero negative control).

- **Status.** There is no `sorry`, and both modules build with `lake build +…`.
- **Axioms.** Every theorem uses only `propext`, `Classical.choice` and `Quot.sound`
  (`logs/spartan-chain/rs-proximity/axioms-soundness-pcs.log`).
- **Source rule.** The rule reports no findings for these files. The 2 findings on the root are
  in another agent's `SpartanChainKat.lean`.

The facts concern a committed matrix `U : Fin m → Fin N → F` and the raw 32-byte answers. They
do not depend on how `μ` is assembled. Everything assumes `κ ≤ 20`. The namespace is
`SpartanChain.SoundnessPCS`.

## What is proved

| blueprint item | Lean |
|---|---|
| filled matrix `U_L(root)` (§9.1; a missing column reads as empty bytes) | `filled`; `filled_of_colL` (a column read off the log is the filled column) |
| **R0, far mode, in answers**. If `U` is not `e`-close, then `#{a ∈ Digest^m : Σ chE(a_i)·U_i is e-close} · 2^169 ≤ 2^{256m}` | `r0_answers`: `r0_far_bad` composed with the exact `2^64`-to-one `chE` (`card_chE_fiber`, through `card_chE_vec`) |
| **close mode**: unique decoding to a matrix over `F` (L-RS4) | `Decodes κ U Q S`; `decode_exists` (`close_in_K` + `msg_in_K`); `decode_unique`; `qDec` (non-constructive, `0` when far); `qDec_spec`; `qDec_eq`; non-vacuity `decodes_honest` |
| difference sets `D_far`, `D_close` | `Dset κ U w msg`; `far_Dset_card` (`> e` for every `ū` when `Σ r_i U_i` is not close); `close_Dset_card` (`≥ d − e` when `v ≠ Σ_i a_i q_dec[i]`) |
| an accepted opening of `U`'s column lies outside both sets | `accept_not_mem` (from `colCheck_iff`); `opened_not_mem` (on the log, through `Merkle.open_binding_prefix`: the opened column is `filled L₀ root`'s) |
| `verify2` accepting on a log | `verify2_runLog`: every opening's `Merkle.verify` runs to `some true` on the log, and both column equations hold |
| **R7**, exact count | `r7_count`: `#{b ∈ Digest^J : all t indices miss D} · N^t = (N − \|D\|)^t · 2^{256J}`, from `card_idx_fiber` per answer, `card_idxAll_fiber`, `card_avoid`, `miss_iff` (the indices of `Transcript.indices` are `idxVec` of answer `j / cnt` at `j mod cnt`) |
| R7 bounds | `r7_far`: `\|D\| ≥ e+1 ⇒ # · 2^129 · 5 ≤ 4 · 2^{256J}`. `r7_close`: `\|D\| ≥ d−e ⇒ # · 2^328 ≤ 2^{256J}`. Both use `layout_ok`, which `decide` checks for all `κ ≤ 20` |
| "after `v`": a correct `v` gives the decoded tensor evaluation | `eval_of_correct`: `Σ_j b_j (Σ_i a_i q_dec[i][j]) = Σ_{i,j} a_i b_j q_dec[i][j]` |
| §10.1 Ligero negative control | `Ligero.Controls.colCheck_tampered`: one column entry changed by `δ ≠ 0`, in a row with a nonzero coefficient, fails the column check. `comb_tamper` is its helper. The positive controls are `colCheck_honest` and `verify2_complete` |

How the KS module uses these (the current §9.2 wording):

1. **Mode.** `far(U) := ¬ eClose (code κ) (UE κ U) (radius κ)`, with `U := filled κ L₀(T) root_T`.
2. **R0.** `r0_answers` bounds `Pr[Esc]` over the whole block of `m` answers. The conditional
   counts `p_T` (L-K2a/b/c) are sums over the rest of the block and belong to KS.
3. **Far mode, R7.** `FarDoom` with `far_Dset_card` gives `|D_far| > e`. Acceptance gives, via
   `verify2_runLog` and `opened_not_mem`, that every index lies outside `D_far`, i.e.
   `Miss … D_far b`. `r7_far` bounds the number of such answer tuples.
4. **Close mode, R7.** The doom row "after `v`" says `v ≠ Σ_i a_i q_dec[i]`. With
   `close_Dset_card` this gives `|D_close| ≥ d − e`, and `r7_close` bounds the misses.
5. **Correct `v`.** `eval_of_correct` gives `v' = q̃_dec(r'')`. The row-weight and `eq` split is
   L-E3 in the MLE module.

## Notes, deviations and open items

- **§9 rewrite.** The rewrite after `BLUEPRINT-R1-S9-review.md` (`Rej` in `Doom`, `μ` over frontier
  entries, the cut at `absorb(root)`) had not landed in `BLUEPRINT-R1.md` when I finished. The
  statements here do not depend on it: the review keeps the R0 and R7 bounds and uses them only
  under `¬Rej`. The names are the current §9.2 ones (`D_far`, `D_close`, `q_dec`, `U_T`). Renaming
  to `Doom`/`Esc`/`Rej` is left for when the new text is in.
- **R7 closed form.** The review's optional closed form for R7 is exactly `r7_count`. Its
  per-answer form is `card_idx_mem` in `SpartanChainTranscript`.
- **Index type.** `D` in `r7_far` and `r7_close` is a `Finset (Fin (2 ^ lN κ))`. That type is
  definitionally `Fin (cols κ)`, so a `Dset` passes directly. The miss predicate `Miss` uses the
  same `Transcript.indices … (List.ofFn b)` as `verify2`.
- **Filled-matrix fill.** `filled` fills a missing column with `readFs` of the empty byte string,
  i.e. `F.ofBytes` of eight zero bytes in every entry. The blueprint says "the zero column"; I did
  not prove that the two agree. Nothing here uses the fill value, because every lemma is about
  opened (present) columns.
- **No conditional counts.** The conditional R0 counts `p_T`, given the first `j` answers, are
  not here. They are KS's (L-K2).

## Measurements

| file | code lines | theorems | check time (wall) |
|---|---|---|---|
| `SpartanChainSoundnessPCS.lean` | 361 | 25 | 8.0 s |
| `SpartanChainLigeroControls.lean` | 28 | 4 | 6.6 s |

The logs are in `logs/spartan-chain/rs-proximity/`: `loc.log`, `axioms-soundness-pcs.log` and
one `<module>.log` per module.

## Additions for the new §9 (second review)

- **`wDec κ U : Fin 2^{14+κ} → F`.** This is §4.1's packing: position `i + 64u'` is bit `i` of
  `qDec κ U (u'/k) (u' mod k)`.
  - `wDec_bool` proves every value is `0` or `1`.
  - `zDec κ U s h := zOf (EF.ofF ∘ wDec κ U) s h` uses `SpartanChainChain.zOf`, so the §2.3
    layout is shared with the chain module and needs no bridge.
- **`r0_esc_le` and `r7_esc_le` are stated at the `extCount` level.** `condCount` and `EscAt`
  live in `SoundnessKS`, which imports this module, so these two lemmas cannot mention them. The
  KS module instantiates `P := P es` (§9.2), using `condCount U es [] = extCount (P es) [] r / 2^(256 r)`.
  - `r0_esc_le`: if every `P (List.ofFn a)` implies `far ∧ Close (Σ chE(a_i)•U_i)`, then
    `extCount P [] m / 2^(256m) ≤ 1/2^169`.
  - `r7_esc_le`: if `|D| ≥ e+1` and every `P (List.ofFn b)` implies `Miss … D b`, then
    `extCount P [] J / 2^(256J) ≤ (4/5)/2^129`.
  - This covers both modes. Far mode gets `|D| ≥ e+1` from `far_Dset_card`. Close mode gets it
    from `close_Dset_card` together with `radius_succ_le` (`e+1 ≤ d−e`).
- **`PCS.eps_budget`** now includes `+ 1/2^256`.
- **Controls** (`SpartanChainSoundnessPCSControls`, §14's `Dset` item):
  - `not_close_of_weight` is the general fact behind the toy example.
  - At `κ = 0`, the word `1` on columns `0…299` is not `298`-close (`toy_not_close`), so
    `far_Dset_card`'s hypothesis can be met and `299 ≤ |Dset|` holds for every `ū`
    (`toy_Dset_card`).
  - Negative control: `zero_Dset` shows the difference set is empty for consistent data.
- **Checks.** All of this uses only the axioms `propext`, `Classical.choice` and `Quot.sound`
  (`logs/spartan-chain/rs-proximity/axioms-soundness-pcs-2.log`). The source rule reports `44
  files, 0 finding(s)`. Code lines: `SoundnessPCS` 434, `SoundnessPCSControls` 49.
