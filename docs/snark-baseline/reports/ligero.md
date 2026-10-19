# Report: PCS bounds and Ligero (`SpartanChainPCSBounds`, `SpartanChainLigero`)

Blueprint: §5.2–§5.5, §6.2 steps 2–4 and 11–13, §7 fields 1–2 and 8–9, §9.2 rows R0 and R7,
§14 (review response). There is **no `sorry`**. Axioms are `propext`, `Classical.choice` and
`Quot.sound` only (`logs/spartan-chain/rs-proximity/axioms-pcs-ligero.log`). The source rule
reports `31 files, 0 finding(s)`. Both modules build with `lake build +SpartanChainLigero`, after
`./refresh-roots.sh`. The RS and proximity layer is reported in `rs-proximity.md`.

## `SpartanChainPCSBounds.lean` (namespace `SpartanChain.PCS`)

- **Shape (§5.2).** `muR`, `lk`, `lN`, `rows`, `msgLen`, `cols`, `dist`, `radius`, and
  `tQ = 260`.
  - Arithmetic: `cols_eq` (`N = 8k`), `dist_eq` (`d = 7k+1`), `radius_eq` (`e = ⌊7k/3⌋`),
    `three_radius_lt`, `rows_mul` (`m·k = 2^{8+κ}`).
  - `shape_table` reproduces §5.2's table by `decide`.
- **The protocol's code.** `dom N c` is the `F` element whose word is `c`. `pt i = ω_{2^i}`, and
  `kap ℓ` holds §5.1's constants. `code κ := rsCode (kap (lk κ)) (lk κ) (dom (cols κ))` over `EF`.
  - `dom_injective` requires `N ≤ 2^64`.
  - `code_minDist`: for `κ ≤ 20`, `MinDist (code κ) (dist κ)`.
- **R0, `r0_far_bad`.** This is `far_bad_le` at the protocol's code with `|EF| = 2^192`
  (`EF.card_EF`). If `U` is not `e`-close, then
  `#{r ∈ EF^m : Σ r_i U_i e-close} · 2^169 ≤ (2^192)^m`, so `d/|E| ≤ 2^-169`. Its hypothesis is
  `κ ≤ 20`, which gives `dist_mul_le : d·2^169 ≤ 2^192`.
- **R7.** These are L-RS3 at the blueprint's parameters, in exact `ℕ` form:
  - `far_miss`: if `|D| ≥ e+1`, then `#{c ∈ [N]^260 missing D} · 2^129 · 5 ≤ 4 · N^260`. So the
    escape probability is at most `(4/5)·2^-129 < 2^-129.32`.
  - `close_miss`: if `|D| ≥ d−e`, then `# · 2^328 ≤ N^260`.
  - Building blocks: `far_ratio` (`24(N−e−1) ≤ 17N`), `close_ratio` (`12(N−(d−e)) ≤ 5N`),
    `miss_pow`, and the kernel-decided `pow17_le` (`17^260·2^129·5 ≤ 24^260·4`) and `pow5_le`.
  - Negative control `pow17_259`: `t = 259` columns do not reach `2^-129`.
- **Budget.** `eps_budget` states
  `(4/5)·2^-129 + 3·2^-152 + 2^-160 ≤ 2^-129`, which is R7 plus the `Bad` terms at
  `logCap = 2^96` (BP-m1, BP-M2). `single_round_le` gives `3/2^192 ≤ 2^-169 ≤ 2^-129`.
- **Cost.** The large-number inequalities are kernel `Nat` comparisons (GMP) and the whole file
  checks in 6.5 s (wall). `set_option exponentiation.threshold 600` silences the elaborator's
  warning; it is not elaboration-time code.

## `SpartanChainLigero.lean` (namespace `SpartanChain.Ligero`)

All compiled code is monomorphic in `F`/`EF`, and `EF`×`F` products use `EF.smulBase`.

| item | names |
|---|---|
| field kernels: tensor `(X_j(a))_j`, `Σ t_j·msg_j`, `Enc(msg)_a`, column of `U`, `Σ w_i·col_i`, `Σ w_i·Q[i]` | `tensorF`, `dotE`, `encAtE`, `columnAt`, `comb`, `combRows`; `kapArr`, `kapFn`, `ptOf` |
| equal to the spec | `tensorF_eq`, `encAtE_eq` (`= RS.enc … c`), `columnAt_getD` (entry `i` = `Enc_F(Q[i])_c`), `comb_eq` |
| the two column equations of §5.4 (one shared tensor per column, §12) | `colCheck`, `colCheck_eq`, **`colCheck_iff`** (as `RS.enc` equalities) |
| L-RS5 at a column; honest columns pass for every `r`, `a` | `enc_combRows`, **`colCheck_honest`** |
| bytes of §7 | `efBytes`, `fBytes`, `labelsBytes`, `readEF(s)`, `readF(s)`, `readLabel`, `readCol`, `readPath`; round trips `readEFs_efBytes`, `readFs_fBytes`, `readCol_openings`, `readPath_openings` |
| sizes | `openW κ = 8m + 31ℓ_N`, `size1 κ = 31 + 24k` (fields 1–2), `size2 κ = 24k + 260·openW` (fields 8–9); `size_table` checks §7 (`113 360`, `84 760`) |
| verifier steps 2–4 (`absorb(root)` kind `0x01`, `m` squeezes for `r`, `absorb(ū)` kind `0x02`) | `rootAndCoeffs`, `verify1` |
| verifier steps 11–13 (`absorb(v)` kind `0x08`, `squeezeIdx (lN κ) 260`, then for each opening `Merkle.verify` and `colCheck`) | `openOne`, `verify2`, **`run_verify2`** (acceptance ⇔ every opening's path verifies and both equations hold, under any oracle) |
| prover | `matrixRows` (`q(j+k·i) = Q[i][j]`), `Commitment`, `commit` (columns by `columnAt`, `fBytes`, `Merkle.build`), `Commitment.root`, `prove1`, `openingBytes`, `prove2` |
| completeness | **`prove1_verify1`** (same transcript for steps 2–4); **`verify2_complete`** (for every oracle, packed witness, `r` and `a`, the verifier accepts the honest `v` and openings with the honest `ū`, via `Merkle.path_complete`) |

How the verifier is cut. The Ligero messages sit at both ends of the transcript, so the
verifier has two phases:

- `verify1` runs right after the seed. It returns the state and `r`.
- `verify2` runs after the ring-switching sumcheck. It takes the root label, `r`, the row weights
  `a_i = eq(r''_hi, i)` (computed by the caller with the MLE module), the decoded `ū`, the bytes
  of `v`, and the openings.

Two things stay with `Verifier.lean`:

- the evaluation claim `v' = Σ_j b_j v_j`, read with `readEFs` (field 8);
- the overall size check, `π.size = leafSize n`.

`Merkle.verify` performs every Merkle query of all 260 openings; there is no early exit.

## Deviations and notes

1. **Openings are absorbed nowhere.** This follows §6.2, which absorbs no opening bytes. The
   openings are bound by the Merkle paths only.
2. **Size of the prover's commit.** `commit` computes `N` tensors and `N·m` dot products of
   length `k`, i.e. `N·k·(m+1)` `F` products. That is about 19M at `n = 16`, but about 9·10^9 at
   `n = 1024`, so the Lean `P` is practical only for small `n`. The Rust prover uses the additive
   NTT. `kap` is §5.1's choice, so the two produce the same `U`; a byte-identical check is §11.3's
   KAT and is not run here.
3. **`Proximity.lean` is not a port.** §14 asks for "a port with provenance of ArkLib's
   `AHIV22.lean`". The statement is unchanged, but the proof is independent: ArkLib `7653a90` was
   the guide and is cited in the module docstring. The row-span step uses a row-by-row induction
   instead of ArkLib's maximal-support argument, and the double count is ArkLib's translation
   trick over `E^m`.
4. **No kernel KAT for the verifier.** Ligero has no kernel-evaluated test (BP-m12 asks to
   measure KATs before relying on them). Its non-vacuity rests on two things. First,
   `colCheck_iff` and `run_verify2` state exactly what acceptance means. Second,
   `verify2_complete` shows that the accepting set is nonempty for every oracle. A
   tampered-column negative control belongs in `Controls.lean` (group D).
5. **Build note.** Another agent's `lake build` sometimes removed `SpartanChainLigero.olean` while
   this module was failing mid-edit. That was transient; the final `lake build +SpartanChainLigero`
   is green.

## Measurements

The logs are in `logs/spartan-chain/rs-proximity/`: `loc.log`, the per-module `.log` files and
`axioms-pcs-ligero.log`.

| file | code lines | theorems | check time (`lake env lean`, wall) |
|---|---|---|---|
| `SpartanChainPCSBounds.lean` | 108 | 22 | 6.5 s |
| `SpartanChainLigero.lean` | 392 | 39 | 7.7 s |

## For other modules

- **`Verifier.lean`** calls `verify1` after the seed. Before `verify2` it computes `a`, `b` and
  `v'` with the MLE module. It passes `readEFs ubarB 0 (msgLen κ)` as `ū`.
- **`Soundness/PCS.lean`** uses `run_verify2` with `colCheck_iff` to turn acceptance into `RS.enc`
  equations, then applies `r0_far_bad`, `far_miss` and `close_miss`. Under BP-M1, the columns of
  `U` are `Merkle.colOr` decoded with `readFs` and mapped into `EF` by `EF.ofF`.
- **`Completeness.lean`** uses `prove1_verify1` and `verify2_complete`.
