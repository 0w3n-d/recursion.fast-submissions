# Report: the algebraic protocol layer (`SpartanChainSpartanProtocol.lean`)

Blueprint: §3, §4, §6.2 steps 5–10, §7 fields 3–7 and §8. Namespace `SpartanChain.Spartan`.
Imports: `SpartanChainTranscript`, `SpartanChainSoundnessSpartan` and `SpartanChainRingSwitchField`.
It does not depend on `SpartanChainLigero`, which does not build at the moment.

**Status**

- **No `sorry`.**
- `lake build +SpartanChainSpartanProtocol` succeeds (`logs/spartan-chain/mle-sumcheck-ringswitch/lake-build-3.log`).
- Axioms are `propext`, `Classical.choice` and `Quot.sound` only (`axioms-3.log`).
- The source rule reports `38 files, 0 finding(s)`.
- Code: 525 lines, 30 theorems (`loc.py`).

## Sizes

| quantity | definition | value |
|---|---|---|
| `ℓ_x = ℓ_y` | `ly κ := lu κ + 1` | `15 + κ` |
| `ℓ_u` | `lu κ := 6 + lq κ` | `14 + κ` |
| `ℓ_q` | `lq κ := 8 + κ` | `8 + κ` |

The sizes are written as nested definitions so that the point splits are definitional:
`r_y = (r_lo ‖ r_hi ‖ r_top)`, with `r_lo` of 6 coordinates and `r_hi` of `ℓ_q`.

## (a) Verifier

**Messages and bytes.**

- **`Msgs`**: the outer polynomials (4 coefficients each), `v_A, v_B, v_C`, the inner
  polynomials (3 each), the 64 slices and the ring-switching polynomials (3 each).
- **`encodeMsgs`**: §7 fields 3–7. Every `EF` element is written as its 24 bytes (`EF.toBytes`),
  in field order, with no padding.
- **`parseMsgs κ b off`**: total; the caller checks the size.
- **`msgsBytes κ`**: `24·(7ℓ_y + 3 + 64 + 3ℓ_q)`.

**`verify κ ev m st`**, starting from the state after `absorb(ū)`, replays the transcript:

1. Squeeze `τ` (`ℓ_x` answers).
2. Outer rounds, kind `0x03`: absorb `g_l`, then squeeze. The squeeze answer is the new state.
3. Absorb `v_A‖v_B‖v_C` (kind `0x04`); squeeze `ρ`.
4. Inner rounds, kind `0x05`.
5. Absorb the slices (kind `0x06`); squeeze `f_0 … f_5`.
6. Ring-switching rounds, kind `0x07`.

It then runs `check`:

- The shapes are right.
- The three sumchecks pass (`verifyRounds`), with claims `0`, `v_A + ρv_B + ρ²v_C` and
  `T = target xE fs s`.
- The outer final check holds: `c₁ = eqPts τ r_x · (v_A v_B + v_C)`.
- The inner final check holds: `c₂ = M̃_ρ(r_x, r_y) · z̃_V`, where
  `z̃_V = (1 − r_top)·dot(eqTable r_lo, s) + r_top·p̃ub(r_u)`.

`Ã, B̃, C̃` and `p̃ub` are the `Evals` argument, which Chain.lean supplies.

**Output:** `some (state, ⟨r'', W̃(r''), c₃⟩)`, or `none`.

- The **PCS claim** is `PcsClaim`, meaning `q̃(point)·weight = value`.
- `Verifier.lean` checks it after Ligero's `verify2` as `value = weight · v'`, with
  `v' = Σ_j eq(r''_lo, j)·v_j`. There is no division (BP-m13).
- The returned state is the one before step 11 (absorb `v`).

**Negative control:** `check_wrong_size` (63 slices are rejected for every challenge).

## (b) Prover

`prove κ w st` runs the same transcript and returns the final state and the messages.

- **Round polynomials.** `proveRounds` computes the honest polynomials with `roundPoly`, using
  coefficient arithmetic and binding the tables after each challenge (`bind0`).
- **`v_M`** are the entries of the bound tables.
- **Slices.** `sliceVals` builds one `eqTable(r_hi)` and takes 64 strided dot products.
- **Ring switching.** It uses `weightTable fs r_hi` and `q` mapped to `EF`.

`Witness` holds:

- `az, bz, cz : Array EF`;
- `z : Array F` (Boolean);
- `q : Array F` (packed);
- `innerTab` (the table `M̃_ρ(r_x, ·)` on the cube, which Chain.lean computes from the sparse
  matrices).

**Efficiency.**

- Everything is `Array`, `Nat.fold` or `Array.ofFn`.
- The generic kernels in MLE/Sumcheck/RingSwitch (`eqTable`, `bind0`, `sumTo`, `dot`,
  `mleEval`, `peval`, `pAdd`, `pMul`, `Expr.evalPoly`, `roundPoly`, `sqIter`, `frobMapC`,
  `phiApply`, `phiTable`, `target`, `weightTable`, `weightEval`) are now `@[specialize]`, so they
  compile to `EF`-monomorphic code. In the IR, `roundPoly._at_.SpartanChain.Spartan.proveRounds.spec_0`
  is the `EF` specialisation called by `proveRounds`.
- **Not benchmarked.** There is no executable target yet.

## (c) Completeness

**`complete`** holds for every oracle `H`, given `Honest κ w ev A B C`. The verifier, run on
`(prove κ w st).run H`, returns `some (prover's final state, c)` with:

- `c.point.length = ℓ_q`;
- **`c.value = c.weight · q̃(c.point)`** (`mleEval` of `q` in `EF`).

No challenge value is excluded.

**What `Honest` assumes**, relating the tables to the abstract R1CS `A, B, C` of
`SoundnessSpartan`:

- `z` is Boolean and of size `2^ℓ_y`;
- `tbl az = matVec A z`, and the same for `bz`, `cz`;
- `Sat A B C z` (L-C3);
- `innerTab` is `M̃_ρ(r_x, ·)` on the cube;
- `ev.mats` gives `matMle` at `(r_x, r_y)`;
- `ev.pub` is the extension of the top half of `z`;
- `q(u') = Σ_i z(i + 64u')·x^i`.

**Proof parts:**

| what | lemma |
|---|---|
| the verifier and prover loops agree; the honest polynomials are `honest e ts rs`; the tables end as `bindAll ts rs` | `run_proveRounds` |
| the outer claim `0` is true (`Sat`) | `outer_claim` |
| the inner claim is true | `inner_claim` |
| `z̃_V` is `z̃(r_y)` for honest slices | `zV_eq`, via `z_mle_slices` |
| `T` equals the ring-switching true sum (L-R3) | `ring_claim` |
| the sumchecks pass | L-S4 three times (`verifyRounds_honest`, `trueSum_bindAll`) |
| `W̃` is the extension of `W` (L-R4) | `mleEval_weightTable` |
| all together, for any challenges | `check_honest` |

**Shapes and bytes.**

- `prove_wellSized`: the honest messages have §7's shape.
- `parseMsgs_encodeMsgs`: the messages are read back from `pre ++ encodeMsgs m ++ post` at
  offset `pre.size`.
- `encodeMsgs_size`: the encoding is `msgsBytes κ` bytes.

## Deviations and notes

1. **`verify` takes parsed `Msgs`, not raw bytes.**
   - It absorbs the re-encoding of each parsed message.
   - For honest proofs these are exactly the proof bytes (`parseMsgs_encodeMsgs`).
   - For any proof the re-encoding is an injective function of the parsed messages
     (`EF.ofBytes_toBytes`), which is all the Fiat–Shamir binding needs.
2. **The byte helpers duplicate Ligero's.** `encE`/`decE` duplicate Ligero's `efBytes`/`readEFs`,
   because Ligero does not build yet. They can be de-duplicated later.
3. **The check is `g(0) + g(1)`.** It equals §3's `c_1 + … + c_d` in characteristic 2
   (`peval_zero_add_one`).

## Open (for `Verifier.lean` / `Prover.lean` / `Chain.lean`)

1. **Wiring.** Wire `Ligero.verify1 → Spartan.verify κ ev (parseMsgs κ proof (31 + 24k)) st →
   Ligero.verify2`, then check the PCS claim against `v'`.
2. **Chain.lean must supply:**
   - `Evals` (§2.4 formulas and `p̃ub`);
   - `innerTab`;
   - the `Honest` facts (`matrix_mle_eq`, L-C3).
3. **Measure the Lean prover** once an executable exists.
