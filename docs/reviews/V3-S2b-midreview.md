# V3-S2b mid-stage adversarial review: `submissions/spartan-chain/`

Reviewed: checkpoint `bbe37e6` plus the working tree of 2026-10-19 ~20:45 (uncommitted
`SpartanChainSoundnessChain.lean`, untracked `SpartanChainChainCols.lean`), against
`docs/snark-baseline/BLUEPRINT-R1.md` (normative, with §14), `IMPLEMENTERS.md`, `PLAN.md`,
`reports/*.md` and the amended contract `rf-core-sc` `v3/ks-potential` @ `05fde28`. Read-only; no
entry file edited. Probes and logs: `logs/s2b-review-probes/` (`main/`, `arith/`, `build/`,
`FactsQueriesFalse.*`, `axioms.log`). Builds in `rf-core-sc` under
`systemd-run … MemoryMax=8G timeout 1200`.

**Verdict.** The protocol as implemented is faithful to the blueprint and to the Rust prover, and
it is an honest succinct argument. As of this checkpoint it is **not certifiable**:

- the certificate's `Facts` structure is uninhabited for the real verifier (S2b-M1, kernel-checked);
- the smoke root misses `T_V` (S2b-M2);
- the `step` law, the `.ubar → τ` link to `chain_sound`, and the final instantiation (`WitFor`,
  `HonestOps`, `SpartanChainFinal`) are still missing (S2b-M3 to M5).

No hypothesis was found that is circular or false apart from M1 and m1. Each missing lemma was
checked on paper against the lemmas that exist, and each is dischargeable as stated.

---

## Major findings

### S2b-M1. `Facts.queries` is false, so `certificate` is vacuous for the real verifier

**Location.** `SpartanChainSubmission.lean:131`, field `queries : ∀ H s n h sn,
((LV.prog s n h sn).queries H).length ≤ qVR1`. No bound on `n`.

**Evidence.** For `LV = Leaf.leafVerifier ev`, the call `snarkProg` always asks at least
`1 + (2 + rows (kap n))` queries: `seed`, then `len_verify1` (an equality).

- At `n = 2^40`: `kap = 40` and `rows 40 = 2^21 > 2^14`.
- At `n = 2^26`: `rows 26 = 2^14`, so the bound already fails there.

Two independent kernel-checked probes prove `¬ Facts (leafVerifier ev) pl` for every `ev` and
`pl`, using only `propext`, `Classical.choice` and `Quot.sound`:

- `logs/s2b-review-probes/main/FactsQueries.lean` and its `.log` (`facts_uninhabited`);
- `logs/s2b-review-probes/FactsQueriesFalse.lean` (`facts_false`).

So `certificate` and `certificateR_claim` currently say nothing about the entry.

**Fix.** Guard the field: `queries : ∀ H s n h sn, n ≤ chainCap → … ≤ qVR1`. It is then
`Leaf.queries_le` (`chainCap = 2^20`). In `V_queries`, the branch that calls `F.queries` sits under
`leafHeaderOK LV c π = true`, which gives `leafN π ≤ chainCap` through `leafHeaderOK_iff`. Add a
control: `Facts (leafVerifier chainEvals) proveLeafR1` is inhabited once the final module exists.

### S2b-M2. The smoke root check exceeds `T_V = 2 s`

**Location.** `SpartanChainVerifierTop.lean:95–125` (`check`, `checkNode`) and
`SpartanChainDecode.lean` (`packFast`, `bytesAtF`, `decodeWitF`, `encodeF`).

**Evidence.** `logs/spartan-chain/leaf-snark/verify-tree.log`, compiled Lean `vb`:

| proof | bytes | time |
|---|---|---|
| root | 575 112 | 2 245–2 496 ms over 4 runs (process wall 3.45 s) |
| level-1 node | 287 512 | 1.01–1.06 s |
| its two leaves | | about 0.5 s together |
| leaf `n = 16` | | 0.23–0.29 s |

About 1.2 s of the root is the node codec (the entry's own `reports/leaf-snark.md`). A flipped
byte inside a leaf still costs 0.99 s before rejection. The causes:

- `decodeF` and `encodeF` run on `List UInt8` and `List Word`, with boxed `BitVec 64` words;
- `bytesAtF o 10 _` unpacks every word after π₁'s offset, so π₂ is unpacked twice;
- `c = nodeStmt c₁ c₂` is tested only after the full decode and re-encode.

**Fix.**
1. Test `c = nodeStmt c₁ c₂` on bytes 8–71, and both length words, before any decode.
2. Replace the list codec with a `ByteArray`-offset decoder: `extract` for the children and a
   zero-padding check for canonicity. Prove it equal to `decodeF` (hence `decode`) and to the
   test `encodeF … = π`.
3. Re-measure the root.

This also removes the inherited `O(|π|·depth)` behaviour (m4).

### S2b-M3. The `step` law is only generic; the per-position facts for `Doom ev` are missing

**Location.** `SpartanChainSoundnessKS.lean`.

**What exists.** `muG_step` and `muG_step_of` turn four per-position facts (`habs`, `hmid`,
`hsingle`, `hround`) into the contract's `step` with `ε = 2^-129`. The budget arithmetic is
kernel-checked: `eps_le` gives `B/2^256 + (4/5)·2^-129 ≤ 2^-129` with `B = 2^96(3·2^8+1)+1`.
`muG_step_of` matches `KState.step` exactly (fresh `q`, `L.length < logCap`, `μ L < 1`).

**What is missing.** For `Doom ev`, only `hmid` (`doom_mid`) is proved. Not yet built:

- `doom_absorb` (`habs`);
- `esc_single_le` (`hsingle`);
- the R0 instance of `hround`, `round_r0_le` (`KS.lean:~1762`, unfinished at reading time);
- the R7 instance of `hround`;
- `kstate` (L-K5), `ks` (L-K6);
- the full `mu_final`: node branch plus `decode`, of which only `mu_final_leaf` exists;
- the instantiated `certified`.

`docs/snark-baseline/reports/controls.md:91` claims `esc_single_le` is proved. No such theorem
exists.

**Fix.** Build the listed lemmas from what exists: `round_escape_le`, `batch_escape_le`,
`rs_escape_le`, `r0_esc_le`, and `r7_esc_le` through `far_Dset_card`, or `close_Dset_card` with
`radius_succ_le`. All of their hypotheses are reachable (`RSControls`,
`SoundnessPCSControls.toy_not_close`). Correct `controls.md`.

### S2b-M4. `chain_sound` (L-C2) has no consumer: the `.ubar → τ_0` doom transition is unproved

**Location.** `SpartanChainSoundnessDefs.lean:432–437` (the `.ubar` and `.tau 0` rows of `Alg`).
Nothing in `SoundnessKS` refers to `chain_sound`.

**Evidence.** The step from `FS ∧ (FarDoom ∨ ¬far)` to `fTbl ≠ 0` needs a lemma. It says: in close
mode, a false statement gives a nonzero residual table for `zDec U`. That lemma is `zc_start` fed by
`chain_sound`, `wDec_bool` and `zDec = zOf`. `ChainSat` is literally
`Sat chainA chainB chainC (zOf …)`, so no extra bridge is needed. Without it, `habs` (M3) cannot be
closed at that position, and `doom_of_not_esc` is only as good as its `Esc` definition.

**Fix.** Add `ubar_tau_doom : FS es → ¬far → tbl … (Ftbl) ≠ 0` (name free), from
`chain_sound` and `wDec_bool`. Add the bit-plane lemma `qPack u = Σ_i x^i · Q_i(u)`, which is needed
by the `f_5 → absorb(g''_0)` transition (`rs_end` with `prod_trueSum`). It relies on bit `i` of the
`BF64` word being the coefficient of `X^i` (FIELD.md convention; prove it, don't assume it).

### S2b-M5. The final instantiation does not exist, so neither completeness nor P's compiled path can be discharged

**Location.**

- `SpartanChainProver.lean:149` (`HonestOps ev wf`), `Leaf.WitFor`;
- `check.sh` (expects `SpartanChainFinal.lean`);
- `SpartanChainChainCols.lean` (untracked, `sorry` at 176).

**Evidence.**

- `HonestOps chainEvals wf` needs a **computable** `WitFor`: `az`, `bz`, `cz`, `z`, `q`,
  `innerTab`, with theorems for `q_pack` and `inner`. Its `mats` and `pub` fields are covered
  (`chainMats_eq`, `chainPub_eq`).
- The in-progress `bsum` and `colA` in `ChainCols` are noncomputable (through `blockA`) and
  quadratic (16 384 terms per column), so as written they cannot be `P`'s code path.
- Without `WitFor`:
  - `Facts.leaf_complete` cannot be discharged;
  - the Lean `P` cannot run;
  - the prover byte-identity KAT (§11.3, the "strongest known-answer test") has not been run
    (`reports/leaf-snark.md`, "not run yet").

**Fix.**

1. Port Rust `Circuit::transpose` as a computable sparse column walk, proved equal to `bsum`.
2. Prove `HonestOps chainEvals wf`.
3. Write `SpartanChainFinal.lean` with:
   - `LV := leafVerifier chainEvals`;
   - `proveLeafR1 := fun s n _ => proveSnark wf s n`;
   - `facts : Facts LV proveLeafR1`.
4. Run the `n ∈ {1, 2, 16}` byte-identity KAT against `scratch/leaf/data/l*.bin`.

---

## Minor findings

**S2b-m1. `habs` is false for an arbitrary `ev`; `kstate` must fix `ev := chainEvals`.**
`SoundnessKS` carries `ev` free (lines ~1380, 1620, 1713, 1951).

- **Counterexample.** `ev.mats = 0`, `ev.pub = 0`. Check (d) then passes whenever the inner claim
  is `0`. A prover who sends the true slices makes `δ = 0` and undooms `absorb(slices)`.
- **Fix.** State `doom_absorb`, `kstate` and `ks` for `chainEvals` only, using:
  - `chainMats_eq` (needs `1 ≤ n ≤ 2^κ`, true for `κ = clog 2 n`) and `matMle_cast`;
  - `chainPub_eq`;
  - `eqPts_eq` for check (b);
  - a `weightEval = W̃` lemma from `weight_mle` for check (f).

  The verifier's `Leaf.EvalsFor` argument order `(κ, n, s, h)` must be the one `μ` uses.

**S2b-m2. The certified prover and the compiled prover are two definitions with no equality
theorem.**

- The two paths:
  - `Submission.P` builds a leaf as `leafBytes s n h πS` (`encodeF (.leaf s n) ++ h ++ πS`).
  - `Run.proveLeafBytes` runs `Leaf.proveLeaf`, which uses `leafHeader` (`enc64 0 ‖ s ‖ enc64 n
    ‖ h`) (`SpartanChainProver.lean:252–260`).
- They agree on paper, but nothing proves it. A KAT run through `Run` would therefore not test the
  certified `P`.
- **Fix.** Prove `(submission LV proveLeafR1).P c (.leaf s n) |>.run H = (Leaf.proveLeaf wf s n).run H`
  (`leafHeader s n h = encodeF (.leaf s n) ++ ⟨h.toArray⟩`). Alternatively, make `Run` call
  `submission.P`.

**S2b-m3. `check.sh` and `smoke.py` are stale.** `check.sh:97` and `smoke.py:18` use
`Run.runLV`, which `SpartanChainRun.lean` no longer defines (`Run` now takes `Ops`). Preview step 6
will fail. The last green run (`logs/spartan-chain/infra/check-5`) predates the rewrite. Fix:
update both and re-run.

**S2b-m4. Inherited `O(|π|·depth)` node checking.** S2a's "caterpillar" behaviour (V3-S2a-M2,
212 s at depth 2000) carries over unchanged. Every level re-decodes and re-encodes its subtree. On
prover-chosen statements this risks `verify_s = 60 s`. The fix of M2 addresses it.

**S2b-m5. Apache-2.0 licence copy missing.** The code copied from leanerVM
(`Blake2sCircuit`, `Blake2sWords`, `Blake2sCompress`, `RingSwitch`) carries correct provenance
lines (repository, path, commit, modifications). `Compress` was diffed against leanerVM `9595721`
(`logs/s2b-review-probes/{src,dst}-compress.lean`), and its differences match the declared ones.
The root ships no copy of the licence, which Apache-2.0 §4(a) requires. Fix: add
`LICENSE-leanerVM` or a NOTICE.

**S2b-m6. Allowlist provenance pending.** All imports are in `docs/core/import-allowlist.txt` (v2):
Mathlib, Batteries, and the 29-module CompPoly `BF64.Bytes`/`BF64.Ext3` closure. The exceptions are
`RecursionFast.Library.{Oracle,Security,WitnessSending}`, v3 organiser modules not yet in any
allowlist file. They are legal once S3 regenerates the allowlist. Record this in the RESULT.

**S2b-m7. No control shows booleanity is load-bearing.** The chain R1CS has no booleanity rows by
design: booleanity comes from `wDec`, the bit-planes of the decoded `q` (`wDec_bool`). Nothing
exhibits a non-Boolean `w` with `ChainSat` for a false chain end (`SpartanChainControls.lean:131`
only has the wrong-end negative). Fix: add that control on a reduced object, so that the reliance
on packing is pinned.

**S2b-m8. Start-up closed terms are unmeasured.** `constPositions`, `initW` and `constGates` are
computable module-level terms evaluated at program start (`blake2s-r1cs.md`, deviation 4).
`chainMats` recomputes `eqv` products and reads points through `List.getD`. Both are harmless at the
measured scale (about 80 ms of `chainMats` inside a 138–227 ms leaf), but the start-up cost should
be measured and quoted.

**S2b-m9. A stale olean.** The built `SpartanChainSoundnessKS.olean` (20:14) predates the split
into `SoundnessDefs`. Importing it together with `SoundnessFinal` fails with a duplicate `stmtOf`.
Rebuild before the next review or `check.sh`.

**S2b-m10. Lint noise.** `SoundnessKS` produces 229 linter warnings (197 unused simp arguments,
13 unused tactics). `SoundnessChain` has 13 and `ChainMle` 5. For the golf pass.

**S2b-m11. Stale documentation.**

- `SpartanChainChain.lean:33–36` lists `chain_sound` and `chain_complete`, which live in
  `SpartanChainChainSound.lean`.
- The "Open" section of `reports/blake2s-r1cs.md` lists two items that are done: the walk merge and
  the circuit KAT.
- `controls.md:91` is wrong (M3).

**S2b-m12. The KAT uses its own copy of the outer expression.** `SpartanChainKat.lean:195`
redefines `Kat.outerExpr`, textually equal to `SpartanChain.outerExpr`
(`SoundnessSpartan.lean:197`). A KAT should exercise the definition the prover and the proofs use.
Import and use `SpartanChain.outerExpr`.

---

## Checked, no finding

**(1) Faithfulness of the verifier.** `snarkProg`, `Spartan.verify` and `check`, `Ligero.verify1`
and `verify2`, `finalCheck`, `Merkle.verify`, `Transcript.*` and `VerifierTop` were checked
against the blueprint and the Rust prover.

- **Transcript bytes** (`Oracle.lean` `seedQ`, `absorbQ`, `squeezeQ`, `leafQ`, `nodeQ`):
  - first bytes `0x10`, `0x20`, `0x30`, `0x00`, `0x01`, pairwise distinct;
  - kind bytes `0x01`–`0x08` in §6.2 order;
  - Rust `transcript.rs`/`prover.rs` identical;
  - `0x52` added only by `blake2sOracle`.
- **Every proof byte of fields 1–8 is absorbed**, each before the challenge that depends on it:
  root → `r` → ū → τ → `g_l` → `v_A‖v_B‖v_C` → ρ → `g'_l` → slices → `f_0..5` → `g''_l` → `v` →
  indices. Field 9 is bound by Merkle paths to the absorbed root.
- **Challenges and indices.** `chE` reads bytes 0–23. Index bits are read little-endian (Rust
  identical). There are `nAns` index squeezes and `t = 260` openings with repetition.
- **Spartan checks (a)–(f)** are literal:
  - round sizes `d+1`;
  - `peval g 0 + peval g 1 = claim`;
  - (b) `eqPts τ r_x·(v_A v_B + v_C)`;
  - (d) `(1 + r_top)·Σ eq(r_lo,i)s_i + r_top·p̃ub`;
  - ring target `Σ x^i Φ(s_i)`;
  - (f) `W̃(r'')·Σ_j eq(r''_lo,j)v_j`.

  All `zip` and `zipWith` lengths are equal by construction.
- **Column checks.** Both Ligero equations are checked, with `a = eqTable(r''_hi)` and
  `b = eqTable(r''_lo)`, consistent with `u' = j + k·i`.
- **Sizes and offsets.** `leafSize` is checked exactly before any query, so every `b[o+i]!` read is
  in range. `snarkSize` matches §7, and `leafSize_table` agrees with the Rust file sizes. Decoders
  are total bijections (`EF.ofBytes`, `F.ofBytes`), so there are no non-canonical encodings.
- **Node branch.** It is the canonical encoding (`decodeF`/`encodeF` with `_eq` theorems), with
  `c = nodeStmt`, children `≤ proofCap` and `check` recursive. It makes no query.
- **Empirical.** Lean `vb` accepts the Rust proofs for `n ∈ {1, 2, 16}` and the smoke tree. The
  canaries are rejected (`logs/spartan-chain/leaf-snark/`).

**(1, arithmetisation).** One compression per chain step (`chainStep_eq`: counter 33, final flag).

- `block_sound`, `block_complete`, `chain_sound` and `chain_complete` are proved in both
  directions, including padding blocks, the wiring at block 0 to `s`, and the tail binding block
  `n−1` to `h`.
- `chainMats_eq` and `chainPub_eq` tie the verifier's evaluators to `matMle`. The walk skips row
  512.
- Packing and Φ stage order agree across the Lean verifier, the Lean prover and Rust: the walk,
  circuit, phi and leaf KATs all report SAME (`logs/s2b-review-probes/arith/`).

**(2) Shapes.**

- `μ ev L` is a function of the log alone; `ev` is fixed, which m1 requires.
- `runLog`'s first-entry semantics is handled: `Repeated ⊂ Bad`, and `entry_unique` applies.
- No KS lemma quantifies over a fixed oracle: `runLog_chain'` uses `logOracle L`.
- The final direction (`doom_of_not_esc`, `accept_not_doomed`, `leaf_final`, `mu_final_leaf`) is
  proved with the standard axioms. Its L-K4 hypothesis `RunChain` is delivered by the uncommitted
  `runLog_chain'` (`SoundnessChain.lean:~1243`), whose preconditions follow from `leafProg`'s
  header check.
- `HonestOps` is completeness-only. With `ev = chainEvals`, its `mats` field pins `A, B, C`.

**(3) Compiled code.**

- The harness runs `Submission.Vb`, which is `(V LV c π).run blake2sOracle`, the same object as
  the theorems (`V_run`, `Vb_eq_vb`).
- The fast codec has `_eq` theorems.
- `F` and `EF` carry word-level compiled arithmetic. Their `Field` instances are built on those
  same operations and proved equal to CompPoly (`ringEquivBF64`, `ringEquivExt3`).
- There is no `implemented_by`.
- The one gap is the prover (m2, M5).

**(4) Trust.**

- `source-rule.py` reports `51 files, 0 finding(s)` (`.contract` and `rf-core-sc` copies are
  identical).
- There is no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `partial`, `unsafe` or
  heartbeat option in the committed modules.
- `#print axioms` gives only the standard three for `certificate`, `complete`, `muG_step`,
  `leaf_final`, `doom_of_not_esc`, `chain_sound`, `bad_step_le`, `Run.verifyProof` and
  `Run.proveLeafBytes` (`logs/s2b-review-probes/axioms.log`).
- There are no large closed terms on the badge path (`blake2sCircuit` and `chainBlock` are
  noncomputable; the `Fintype` instances are noncomputable).

**(5) Build.** Every module is under 2 min and 4 GB (`logs/s2b-review-probes/build/times.txt`):

| module | time | peak memory |
|---|---|---|
| SoundnessLog | 48 s | 2.7 GB |
| Blake2sCompress | 38 s | 2.0 GB |
| FieldBaseCorrect | 38 s | 2.8 GB |
| SoundnessKS | 37 s | 3.0 GB |

No kernel evaluation of the `2^14` block. A leaf asks 3 533 queries against `qV = 2^14`
(`qBound 20 = 7 774`).

**(6) Honesty.** It is a genuine succinct argument: a Ligero PCS over the packed witness, Spartan
sumchecks, ring switching, and `t = 260` Merkle-opened columns. `V` never computes BLAKE2s on an
oracle input and never compares a local hash with an oracle answer. Its only local BLAKE2s calls
are:

- `leafStmt h n` on proof bytes, compared with `c`;
- the node branch's `check` of the children under `blake2sOracle`. That branch has no oracle
  answers to compare against: it decides `Rel (vb LV)`, which the contract defines through `Vb`
  (S2a's pattern).

There is no CGH-style oracle recognition.
