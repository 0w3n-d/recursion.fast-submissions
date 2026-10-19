# V3-S2b final adversarial review: `submissions/spartan-chain/`

Reviewed: commit `3171790` ("S2b: the honest entry spartan-chain is certified"), code frozen,
against `docs/snark-baseline/BLUEPRINT-R1.md` (normative, with §14), `PLAN.md`, the reports in
`docs/snark-baseline/reports/`, the reviews `BLUEPRINT-R1-review.md`, `BLUEPRINT-R1-S9-review.md`
and `V3-S2b-midreview.md`, the amended contract (`rf-core-sc` at `05fde28`, branch
`v3/ks-potential`: potential `KState`, `logCap = 2^96`), and the interim harness branch
`v3/ks-interim-harness` (`9d5b26a`) of `rf-core-s2a`. Read-only; nothing in the entry was edited.
Probes and logs are under `logs/s2b-final-review-probes/`. Builds ran in `rf-core-sc` under
`systemd-run --user --scope -p MemoryMax=8G timeout 1800`. Skills: `adversarial-review`,
`lean4:review`.

**Verdict.** The mathematics is sound and the statement is the contract's:
`Challenge.certified : CertificateR declared submission` is kernel-checked against the
organiser's stub, rendered from `claim.json`, with the three standard axioms and no hypothesis.
The comparator's Lean kernel accepts it. No weakening and no vacuity was found, and the
midreview's five majors are fixed.

**The stage is not done.** Its definition of done requires `HARNESS: ACCEPT`, and
`HARNESS=1 check.sh` on the committed tree ends in **`HARNESS: REJECT`**:

- the second kernel, nanoda, was killed (exit 137) after a 1 797 s comparator run, at 53 GB or
  more of resident memory (V3-S2b-M1);
- the gate, which the harness never reached and this review ran by hand on the comparator's
  tree, rejects for two reasons in the interim organiser tooling (V3-S2b-M2).

There are 2 majors and 7 minors. The code is honest: a real leaf SNARK, with no CGH-style
recognition. Its succinctness is at the leaves only (m7).

---

## 1. The certified statement (focus 1)

**Checked, no finding.**

- **The stub is the organiser's, verbatim.** The rendered challenge
  (`logs/spartan-chain/infra/harness-final/SpartanChainChallenge.lean`) differs from
  `SpartanChainSolution.lean` in exactly three places: the added `import SpartanChainFinal`, the
  body of `submission`, and the body of `certified` (`diff`, this review). Everything else
  (`image`, `declared`, the docstrings) is byte-identical. `RecursionFast/Challenge/V3.lean.in` on
  `v3/ks-interim-harness` adds only organiser files to `05fde28`
  (`git diff --stat 05fde28 v3/ks-interim-harness`: the stub, `harness-local.sh`,
  `render-challenge.py`, `setup-scratch.sh`). `RecursionFast/Contract/` is unchanged in the
  shared clone and in the check's core clone.
- **The statement.** `#check` gives `Challenge.certified : CertificateR Challenge.declared
  Challenge.submission`, and `#print` gives `declared = { img := Challenge.image,
  ε := 1 / 340282366920938463463374607431768211456, qV := 16384, fuel := fun t => 8 + 0 * t }`
  (`logs/s2b-final-review-probes/Axioms.log`). These are `claim.json`'s numbers. `2^128` is the
  denominator, so the declared error is `errorCap`.
- **The fields of the certified submission are the entry's objects.** Each of the following is
  closed by `rfl` in `Axioms.lean`:
  - `submission.ε = 2⁻¹ ^ 129`;
  - `submission.qV = 2 ^ 14`;
  - `submission.E = WitnessSending.E`;
  - `submission.img = WitnessSending.img`;
  - `submission.V = SpartanChain.V leafVerifier`;
  - `submission.Vb c π = Run.verifyProof c π`, the function the smoke runner `entry-verify`
    executes.
- **Image binding.** `certified` closes the image binding by `rfl` against the rendered literal.
  `check.sh` reassembles `extractor.bin` byte-identically and finds it equal to the core's
  `tests/asm/proofwords.bin` (`harness-final/image.log`). `claim_negatives` (kernel) rejects a
  flipped image bit, a declared fuel of 7 and a declared query bound of `2^14 − 1`.
- **Axioms.** `certified`, `facts`, `KS.kstate`, `KS.ks`, `mu_final`, `mu_step_chain`,
  `Run.verifyProof_eq` and `Run.proveLeafBytes_eq` use only `propext`, `Classical.choice` and
  `Quot.sound` (`Axioms.log`). The hygiene scan and the source rule (`61 files, 0 finding(s)`,
  with both the core's and `.contract`'s `source-rule.py`) are clean. There are no `instance`
  declarations on contract types: all of them are on the entry's `F`, `EF` and circuit types.
- **No weakening.** `Facts.ks : Nonempty (KState (Rel (vb LV)) (V LV) WitnessSending.E εR1)`
  is the contract's own structure. `Vb_eq : (submission LV pl).Vb = vb LV` moves it to
  `Rel S.Vb`. `KS.kstate` fills `μ`, `empty`, `step` and `final` with the contract's binders, and
  `final_law` takes only the contract's hypotheses: nothing is assumed beyond `L.length ≤ logCap`,
  `μ L < 1` and acceptance. `εR1 ≤ errorCap`, `qVR1 ≤ 2^16`, the fuel `8 ≤ 2^40 + 2^8 t`, and
  `img.byteSize ≤ imageCap` are closed by `decide` or `norm_num`.

## 2. Vacuity (focus 2)

**Checked, no finding** beyond m6.

- **Hypothesis-free.** `facts : Facts leafVerifier proveLeafR1` is a closed theorem, so the
  parametrised `certificateR_of` is instantiated, not assumed. Midreview S2b-M1 is fixed:
  - `Facts.queries` is guarded by `n ≤ chainCap`;
  - `V_queries` discharges the guard from `leafHeaderOK_iff`;
  - the kernel-checked uninhabitation probe of the midreview no longer applies.
- **No degenerate verifier.** `Complete` is proved for every oracle, and
  `Facts.leaf_complete` covers every `1 ≤ n ≤ chainCap`. Since `Rel` has a leaf witness for every
  `(s, n)`, the verifier accepts the honest proof of every chain under every oracle, BLAKE2s
  included. Measured in compiled code (`harness-final/smoke.log`): the compiled `Vb`
  (`Run.verifyProof`, `rfl`-equal to `Submission.Vb`) accepts every proof of the `r = 2`,
  `n = 16` tree from the Rust prover, including the root (575 112 B, 1.221 s), against
  independently computed digests. It rejects all 28 canaries and 16 random 1 MiB proofs (at most
  0.093 s each).
- **No degenerate `μ`.** The contract makes a degenerate potential impossible:
  - `step` at the empty log forces `Σ_a μ [(q, a)] ≤ ε · 2^256`, so `μ` cannot be `1` on most
    logs;
  - `final` must hold wherever `μ < 1`.

  The entry's `μ` is §9.3's definition. `Bad ∨ Esc` gives `1`; otherwise `μ` is the sum of the
  frontier `pRound` charges. `Doom = Rej ∨ Alg`, and `Alg` is §9.2's table, one row per
  `PosClass`.
- **A non-vacuous extractor.** `E = decode π` returns the leaf `(s, n)` sent in the clear. The
  knowledge content is therefore not in `E`. It is in `Rel`, which requires
  `chainEnd s n = h` for the sent `s`. That equation holds only through the SNARK's soundness
  (`chainEnd_of_runChain`), which needs the full potential argument. A verifier that skipped the
  SNARK would make `final` false at any false chain end.
- **The ε negative is not a theorem in the entry.** See m6. Probe:
  `logs/s2b-final-review-probes/EpsNegative.lean` (kernel-checked, standard axioms).

## 3. Integrity of the soundness proof (focus 3)

These steps were spot-checked against the blueprint. All of them are kernel-checked and reached
from `certified`.

- **`τ_0` after `absorb(ū)`, through `chain_sound` and the packing lemma** (`esc_tau0`,
  `ftbl_ne_zero`, `SoundnessKS.lean:500–552`). The "doom before" is the `.ubar` row,
  `FS ∧ (FarDoom ∨ ¬Far)`.
  - **Far branch.** `FarDoom` is on both sides, so nothing escapes.
  - **Close branch.** `ftbl_ne_zero` applies `zc_start` to `¬ Sat`. That comes from `chain_sound`
    on the Boolean witness `EF.ofF ∘ wDec κ U` (`wDec_bool`), with `zOfU = zOf` and
    `matA = chainA n κ`. `zc_escape_le` then bounds the escaping `τ_0` to at most one value.

  Midreview S2b-M4 is fixed. `absorb_gR0` uses `qPack_eq_sum`, the bit-plane identity
  (`SoundnessPack`, via `qDec_bitplanes`), not an assumption.
- **`doom_absorb`** (`SoundnessKS.lean:375–486`). It covers every absorb class:
  - `absorb_g0`: `zc_end`, `outer_start`;
  - `absorb_tri`: `outer_final` and check (b), with `eqPts_eq`;
  - `absorb_sl`: `inner_final`, check (d) through `EvalsOK`, `zV_eq_of_delta`;
  - `absorb_gR0`;
  - `absorb_v`: check (f), `weightEval_mle`, `mle_pack`.

  Every other absorb class carries the same row across. `chainEvals_ok : EvalsOK chainEvals` is
  proved from `chainMats_eq` and `chainPub_eq`, and `kstate` is stated for `chainEvals` only
  (midreview m1 fixed).
- **R0 and R7 counts.**
  - `round_r0_le` gives `condCount ≤ δKS` from `r0_esc_le` (`r0_answers`, `2^-169`).
  - `round_r7_le` handles both modes. In far mode it uses `r7_esc_le` with `far_Dset_card` and
    `r7_far`, `(4/5)·2^-129`. In close mode it uses `close_Dset_card` and `radius_succ_le`
    (`KSBase.lean:1834–1890`).
  - The budget is `eps_le : (2^96(3·2^8+1)+1)/2^256 + δKS ≤ 2^-129`, by `norm_num`.
  - `layout_ok` and `kapOf_le` (`κ ≤ 20` from `n ≤ chainCap`) feed the numeric bounds, so the
    bounds hold at every admissible shape.
- **L-K4 `runLog_chain` and its extra hypotheses.** `mu_final_leaf_closed` (`SoundnessChain`)
  discharges both of `runLog_chain`'s extra hypotheses from an accepting `leafProg`
  (`hchain_of_leafProg`):
  - `n ≤ chainCap`, from the header check;
  - `off₃ κ ≤ |π_S|`, from `π.size = leafSize n`.

  `SoundnessKSFinal.mu_final` has no hypothesis beyond the contract's.
- **The node branch of `final`** (`final_of_not_leaf`). The node branch asks no query, and
  `checkNode_rel` decides `Rel (vb LV)` with `vb` on the children. Every other tag returns
  `ret false`.
- **The definitions are the blueprint's.** `Doom`, `EscAtG`, `EscG`, `muG`, `pRoundG`,
  `condCount`, the `Alg` rows and `posClass` were read against §9.2–§9.3 row by row. The
  documented deviations are the bit-plane `δ_i` (a correction to the blueprint) and the explicit
  round length `r` of `condCount` (`reports/soundness-ks.md`, "Deviations"). Neither weakens the
  argument, and the contract's laws are what is proved in any case.

## 4. Honesty (focus 4)

**Checked, no finding.** The scope statement, though, belongs in the RESULT (m7).

- **The leaf branch never recomputes the chain.** `leafProg` hashes only the proof's header,
  `c = leafStmt h n` (`VerifierTop.lean:79–89`). For `n = 0` it compares `h = s`. For `n ≥ 1` it
  runs the SNARK.
  - The verifier modules make no BLAKE2s call besides `leafStmt` and `nodeStmt`:
    `Verifier`, `SpartanProtocol`, `Ligero`, `Merkle`, `Transcript`, `Oracle`, `ChainEval` (grep).
  - `chainEvals` walks the one `2^14`-position block circuit (`walkAB`) and a closed form in `κ`.
    Its cost does not grow with `n`.
- **No CGH-style recognition.** No path computes `blake2sOracle` and compares the result with an
  oracle answer. The node branch does evaluate `blake2sOracle`, in `check` on the children, under
  any oracle. That is `Rel`'s self-application (`Rel` is defined through `Vb`), the S2a pattern.
  It accepts exactly when `Rel` holds, never on a magic proof.
- **Succinct at the leaves only.** The argument is honest: Spartan sumchecks, ring switching,
  a Ligero PCS with `t = 260` Merkle-opened columns, and Fiat–Shamir over the oracle. It is
  succinct **at the leaves**. The nodes are witness-sending ([D-3]), so a root proof grows
  linearly in the number of leaves:
  - `r = 8` cannot fit `proofCap` (BLUEPRINT §0, fact 1);
  - the entry runs only the `r = 2`, `n = 16` smoke tree.

## 5. Trust, hygiene, performance (focus 5)

- **Source rule.** 61 files, 0 findings. Hygiene is clean.
- **Code attributes.** There are none:
  - `@[inline]` 13, `@[specialize]` 21, `@[irreducible]` 3;
  - `@[never_extract]` 1, on `chainBlockAt`, to keep the `2^14`-row circuit out of start-up
    closed-term extraction. It is not on the gate's list and it changes no code.
- **Imports.** Mathlib, Batteries, `CompPoly.Fields.Binary.BF64.{Bytes,Ext3}`,
  `RecursionFast.Contract.*`, and `RecursionFast.Library.{Blake2s,Oracle,Security,WitnessSending}`
  (see M2 for the allowlist and the pinning).
- **Provenance and licence.**
  - Lean files copied from leanerVM name the repository, path, commit and modifications:
    `Blake2sCircuit`, `Blake2sWords`, `Blake2sCompress`, `RingSwitch`.
  - `circuit.rs` names its leanerVM/leanVM source.
  - `LICENSE-leanerVM` (Apache-2.0) is present, so midreview m5 is fixed.
  - `Decode` names its S2a source.
- **Compiled code is the certified code.**
  - `Run.verifyProof` is `rfl`-equal to `Challenge.submission.Vb` (probe).
  - `Run.proveLeafBytes` is `rfl`-equal to the submission's `P` (midreview m2 fixed).
  - Start-up of `entry-verify` is 0.08 s process wall (caterpillar probe, depth 1), so start-up
    closed terms cost nothing measurable (midreview m8).
- **Module times** (`lake env lean`, imports prebuilt,
  `logs/s2b-final-review-probes/module-times.log`):

  | module | wall | peak RSS |
  |---|---:|---:|
  | TranscriptControls | 70.98 s | **4.16 GB** |
  | SoundnessKSBase | 35.39 s | 3.11 GB |
  | SoundnessKS | 12.09 s | 2.90 GB |
  | SoundnessChain | 10.86 s | 2.90 GB |
  | Chain | 8.75 s | 2.47 GB |
  | ChainInner | 8.30 s | 2.78 GB |
  | SoundnessLogControls | 8.09 s | 2.82 GB |
  | ChainTables | 8.20 s | 2.78 GB |
  | Final | 6.39 s | 2.77 GB |

  Every module is under 2 min. TranscriptControls is at the 4 GB line of the IMPLEMENTERS
  budget: it is the kernel's BLAKE2s known-answer test, not on the certificate's path.
- **Verify time (`T_V`).** The smoke root takes 1.221 s in the final smoke run. The fix-m2 logs
  give 0.99–1.71 s, and 1.06–1.45 s through `Run.verifyProof`, at load 5–7. That is under 2 s
  with little margin, so midreview S2b-M2 is fixed.
- **The harness.** `HARNESS: REJECT (comparator, exit 1)`
  (`logs/spartan-chain/infra/harness-final.log`, `…/harness-final/harness-work/comparator.log`).
  - Stage 0 (manifest) and the source rule pass, and the fresh tree builds.
  - "nanoda kernel rejected the solution … Lean default kernel accepts the solution … nanoda
    exited with 137".
  - `TIME comparator 1797.01 s`.

  The gate was not reached. This review ran it by hand on the comparator's tree
  (`logs/s2b-final-review-probes/gate.log`), and it rejects (M2). Steps 1–10 of `check.sh` pass
  on the committed tree: image, hygiene, source rule, build, challenge, solution, axioms (111
  declarations), negative claims, smoke, line counts.

## 6. What is kernel-checked, measured, and claimed (focus 6; for the RESULT)

| kind | fact | evidence |
|---|---|---|
| kernel | `Challenge.certified : CertificateR declared submission` for the rendered `claim.json` (`ε ≤ 2^-128`, `qV ≤ 16384`, `fuel = 8`, the image of `extractor.bin`), standard axioms | `Axioms.log`; `harness-final/solution.log` |
| kernel | `KState` with `ε = 2^-129` for `Rel (vb LV)` (`kstate`), and `KS … (2^14)` (`ks`) | same |
| kernel | perfect completeness for every oracle (`complete`, `snark_complete`, `chainHonest`) | `facts` |
| kernel | the compiled verifier and prover are the certified ones (`verifyProof_eq`, `proveLeafBytes_eq`, `rfl`) | `Axioms.log` |
| kernel | negative claims: image bit, fuel 7, `qV = 2^14 − 1` (`claim_negatives`); ε below `2^-129` (this review's probe only) | `EpsNegative.log` |
| measured | the compiled `Vb` accepts the Rust `r = 2`, `n = 16` tree (root 575 112 B, 1.221 s) and rejects 28 canaries and 16 random 1 MiB proofs | `harness-final/smoke.log` |
| measured | root `Vb` 0.99–1.71 s over 9 runs; through `Run.verifyProof` 1.06–1.45 s | `fix-m2/after-root*.log` |
| measured | the Rust prover: `n = 16` 0.18 s, 143 711 B; `n = 1024` 0.71 s; smoke tree 0.72 s | `rust/`, `smoke.log` |
| measured | the Lean prover's tables at `κ = 4`: 8.6 s for `z, az, bz, cz, q`, plus 15.9 s for `innerTab` | `blake2s-r1cs/bench-wit.log` |
| measured | the Lean `P` is byte-identical to Rust at `n ∈ {1, 2, 16}`, **with the tables before the last `ChainInner` change, through a copy** (m2) | `leaf-snark/prove-kat.log` (21:03) |
| measured | valid caterpillar proofs: depth 3000, 504 080 B, 64.0 s; depth 6000, 1 008 080 B, **275.0 s** (m1) | `caterpillar/caterpillar.log` |
| measured | module times and memory (§5) | `module-times.log` |
| measured | `HARNESS: REJECT`: nanoda exit 137 after 1 797 s, at least 53.5 GB; Lean's kernel accepts (M1) | `harness-final.log`, `nanoda-rss.log` |
| measured | the gate, run by hand, rejects: CompPoly not pinned (`csimp`); rule 4's v2 fields (M2) | `gate.log` |
| claimed, not backed | "check.sh (final mode) printed CHECK OK" for the committed tree (commit message) | m3 |
| claimed, false | caterpillar proofs "now at memcpy cost" (`reports/submission-infra.md:204`); the M2 fix "also removes" the `O(|π|·depth)` behaviour (midreview M2 fix text) | m1 |
| claimed, stale | REPORT §1 item 3, §3.2, §3.4 ("not yet done", `TBD (final run)`), module times, the `T_V` range | m4 |

---

## Major findings

### V3-S2b-M1. The second kernel does not finish: `HARNESS: REJECT` at the comparator

- **Location.** `comparator-nanoda.json` (`enable_nanoda: true`). The certificate's closure is
  32 457 constants by this review's count (`logs/s2b-final-review-probes/Closure.log`); the gate
  counts 32 932.
- **Evidence.** In `harness-final/harness-work/comparator.log`, the export succeeds and then
  "Running nanoda kernel on solution / nanoda kernel rejected the solution / Running Lean default
  kernel on solution / Lean default kernel accepts the solution / uncaught exception: nanoda
  exited with 137". `TIME comparator 1797.01 s wall`.
  - This review sampled nanoda's resident memory every 30 s
    (`logs/s2b-final-review-probes/nanoda-rss.log`). It rose steadily from 38.1 GB at 17:18
    elapsed to 53.5 GB at 22:49 elapsed, on a 62 GB machine, until the process was killed.
  - For comparison, S2a's comparator, both kernels included, ran in 71 s at 0.98 GB
    (`logs/V3-S2/`).
  - The comparator's checked statement is the right one, and Lean's kernel accepts it. The
    failure is resources: memory or time, killed by `SIGKILL`.
- **Why it matters.** The stage's definition of done (CLAUDE.md, "What done means") requires
  `HARNESS: ACCEPT`. The design's two-kernel check is part of the trusted path, so a certificate
  that only one kernel can check is not certified by the harness.
- **Fix.**
  1. Bisect with the comparator and nanoda on sub-statements: `KS.ks`,
     `Facts.leaf_complete` (via `chainHonest`), `Leaf.queries_le`, `WitnessSending.computes`. A
     scratch challenge per theorem is enough.
  2. Find the declarations nanoda cannot check in bounded memory, and rewrite those proofs. They
     are likely kernel reductions of large closed terms. Candidates, not confirmed: the
     `unfold …; rfl` of `chainBlockAt_eq`, which is in the closure (`Closure.log`) and relates
     two constructions of the `2^14`-row circuit; and any `decide` on large `Nat` or array data.
  3. Alternatively, take the nanoda memory and time budget to the organiser as an S3 question.

  Until one of these is done, the RESULT can claim kernel-checked by Lean, not `HARNESS: ACCEPT`.

### V3-S2b-M2. The interim gate rejects the solution (two causes, both in the organiser's tooling)

- **Location.** `rf-core-s2a` `v3/ks-interim-harness:scripts/Gate.lean` (rules 3, 4, 6), the
  manifest and allowlist generated by `check.sh` step 11, and `make-solution.py`'s
  `noncomputable def submission`.
- **Evidence.** This review ran the gate on the comparator's tree with the harness's own
  arguments (`--manifest`, `--computable RecursionFast.Challenge.submission`,
  `--allowed-imports`). The output is in `logs/s2b-final-review-probes/gate.log`:

  ```
  gate: rule 4: RecursionFast.Challenge.submission: no compiled code as a whole …; checking its badge-path fields [P, cfg]
  gate: 3812 modules, 3727 trusted and 0 pinned by hash
  gate: REJECT module CompPoly.Fields.Extension.Arithmetic: registers @[csimp] lemmas
  gate: REJECT RecursionFast.Challenge.submission: structure RecursionFast.Submission has no field cfg
  ```

  1. **CompPoly is not pinned.** "0 pinned by hash", so CompPoly's modules count as untrusted,
     and a `@[csimp]` lemma in `CompPoly.Fields.Extension.Arithmetic` (reached through `BF64.Ext3`)
     rejects them under rule 3. The generated allowlist
     (`harness-final/import-allowlist.txt`, 10 779 modules) also lists no `CompPoly.*` module,
     so rule 6 would reject the direct imports of `CompPoly.Fields.Binary.BF64.{Bytes,Ext3}`.
     Design §7.4 allows those imports.
  2. **Rule 4 still checks v2's badge-path fields.** The solution's `submission` is
     `noncomputable`, because `εR1` is a power in `ℝ≥0`. Unlike S2a's, it has no compiled code as
     a whole, so the gate falls back to v2's field list `[P, cfg]` and fails on the missing field
     `cfg`. v3's `Submission` has `V`, `P`, `E` and `img`. S2a passed only because its
     `submission` (`ε := 0`) was computable as a whole.
- **Scope.** Neither cause is a defect of the entry's mathematics. Both block `HARNESS: ACCEPT`.
- **Fix.**
  - Organiser (S3):
    - pin CompPoly in the manifest (its `BF64`/`Ext3` closure, design §7.4) and include it in the
      allowlist;
    - change rule 4's badge-path fields to v3's `V`, `P`, `E`, `img`.
  - Entry, optional: a `submission` that is computable as a whole would avoid the field path, if
    a computable `ℝ≥0` literal for `2^-129` can be had.
  - Record in the RESULT that the compiled verifier is `Run.verifyProof`
    (`rfl`-equal to `Challenge.submission.Vb`).
  - Then re-run `HARNESS=1 check.sh`.

## Minor findings

### V3-S2b-m1. Valid caterpillar proofs take 275 s; the "memcpy cost" claim is false

- **Location.** `SpartanChainVerifierTop.lean` `check` (each level runs `nodeParse`:
  `extract` of both children and `encodeNodeB … = π` over the whole proof);
  `reports/submission-infra.md:204`; the midreview's M2 fix text ("This also removes the
  inherited `O(|π|·depth)` behaviour").
- **Evidence.** Measured with the compiled `entry-verify` of the final check
  (`logs/s2b-final-review-probes/caterpillar/`, generator `gen.py`). The proofs are valid: each
  node has a deeper left child and a zero-step leaf on the right, and every one is accepted.

  | depth | bytes | `Vb` |
  |---:|---:|---:|
  | 1 | 248 | 0.25 ms |
  | 1000 | 168 080 | 6.8 s |
  | 3000 | 504 080 | 64.0 s |
  | 6000 | 1 008 080 | 275.0 s |

  That is about 80 ns per byte re-processed, not memcpy speed, and 4.6 times `verify_s = 60 s`.
- **Scope.** As in V3-S2a-M2, the benchmark is not affected. The root and sample checks run under
  the runner's digests, which force the honest shape. The defect is the claim, and the DoS
  property for anyone who runs `verify` on a statement the prover chose.
- **Fix.** Correct `submission-infra.md`, and state the measured property in the RESULT. This
  review records the decision that, under the code freeze, the code stays. A linear check is
  possible but optional: parse the children in place by offsets (canonical length words and
  zero padding checked on the bytes), recurse on `(offset, length)` views, and never re-encode.

### V3-S2b-m2. The prover byte-identity KAT ran on a copy of the tables, before the last change

- **Location.** `reports/leaf-snark.md:14` ("The Lean prover is byte-identical to Rust") and
  :144–155; `rf-core-sc/scratch/leaf/LeafMain.lean` (`chainWitCopy`).
- **Evidence.** `prove-kat.log` (21:03) ran `Run.proveLeafBytes` with `chainWitCopy`, a textual
  copy of `chainWit` made "because that module did not build yet". Commit `3171790` then changed
  the helpers the copy calls (`ChainInner` +96/−31, `ChainTables`, "a per-bit retrace bug
  fixed"). The certified `proveLeafR1 = proveSnark chainWf` has never been compared with the Rust
  bytes. Completeness is kernel-checked, so this is a test gap, not a soundness gap.
- **Fix.** Re-run the KAT with `SpartanChain.chainWf` imported from `SpartanChainChainHonest`
  (no copy) at `n ∈ {1, 2, 16}`, quote the new log, and drop the copy.

### V3-S2b-m3. The commit's "check.sh (final mode) printed CHECK OK" has no log for the committed tree

- **Evidence.**
  - The final-mode runs that passed, `check-20261019T213908Z` and `…214048Z` (21:39 and 21:40),
    predate the last edits.
  - `check-final-1.log` (21:49) and `check-final-2.log` (21:52) **fail** with
    `SpartanChainChainTables.lean:64:2: dsimp made no progress`.
  - `check-…214048Z`'s harness rejected at the comparator for the same module.
  - The commit is at 21:57:53. The first check of the committed tree is `harness-final`, started
    at 21:57:58. Its steps 1–10 pass: build, solution, axioms (111 declarations), negative claims,
    smoke OK, line counts.
- **Fix.** In the RESULT, quote `logs/spartan-chain/infra/harness-final.log` and its directory,
  not the earlier runs.

### V3-S2b-m4. `REPORT.md` and the reports are stale against the commit

- **`REPORT.md`.**
  - §1 item 3 and §3.4 list as "not yet done" or "`TBD (final run)`" the `KState`, `Facts`,
    `SpartanChainFinal`, the solution, the negative claims and the harness, all of which are now
    done.
  - §3.2 has byte identity as TBD.
  - §3.1's module times are stale. `SpartanChainChain` is 134.9 s there and 8.75 s now.
    `SoundnessLogControls` is "≥ 133.9 s (killed)" there and 8.09 s now.
  - §3.3 quotes the root as "0.99–1.21 s over 8 runs". `fix-m2/after-root.log` also has a
    1.71 s run, and the `Run.verifyProof` runs are 1.06–1.45 s.
  - The module count is 58 there and 61 now.
- **`reports/soundness-ks.md`.** Deviation 8 ends in a broken sentence ("… recursion limit.
  instance); …").
- **`SpartanChainRun.lean`.** The docstring says the tables are "an argument until
  `SpartanChainChain` supplies them", but `chainWf` exists.
- **Fix.** Update them in the fix pass. The RESULT supersedes the REPORT's status lines.

### V3-S2b-m5. Four midreview minors have no disposition

- **Still open.**
  - **S2b-m7.** No control shows that booleanity is load-bearing: a non-Boolean `w` with
    `ChainSat` for a wrong end. `SpartanChainControls.lean:131` covers the Boolean case only.
  - **S2b-m10.** 279 linter warnings, 227 of them in `SoundnessKSBase`.
  - **S2b-m11.** `SpartanChainChain.lean:33–36` still lists `chain_sound` and `chain_complete`.
    They live in `ChainSound`.
  - **S2b-m12.** `SpartanChainKat.lean:195` still redefines `outerExpr`.
- **Fix.** Fix each one, or argue it in the RESULT's disposition table. m10 is the golf pass's.

### V3-S2b-m6. No kernel-checked negative for the declared error

- **Evidence.**
  - `claim_negatives` covers the image, the fuel and `qV`, but not `ε`.
  - `check.sh` step 8's negatives are script-level: they show that make-solution's own proof
    term fails, not that no proof exists.
  - This review's probe proves `¬ CertificateR {claimR1 with ε := 2⁻¹ ^ 130} (submission LV pl)`
    for every `LV`, `pl` (`logs/s2b-final-review-probes/EpsNegative.lean`, standard axioms).
- **Fix.** Add the ε variant to `claim_negatives`, and an `error` variant to `check.sh` step 8.

### V3-S2b-m7. The RESULT must state the entry's scope

This is an observation for the RESULT, not a defect of the code.

- The argument is succinct at the leaves only. The nodes are witness-sending, so the root proof
  is linear in the leaf count. `r = 8` is impossible under `proofCap`, and only the `r = 2` smoke
  tree runs.
- The node branch evaluates `blake2sOracle` itself, to decide `Rel` through `Vb`. It compares no
  oracle answer, which is the S2a pattern, and the O-25 intake review should be told so.
- The `T_V` margin on the smoke root is 0.3–1.0 s on this VM, under load.
- TranscriptControls peaks at 4.16 GB.

---

## Midreview majors: disposition checked

| finding | status | evidence |
|---|---|---|
| S2b-M1 `Facts.queries` false | **fixed** | the field is guarded by `n ≤ chainCap`; `facts` is a closed theorem |
| S2b-M2 root over `T_V` | **fixed** | `nodeParse` by offsets; root 1.22 s (`harness-final/smoke.log`), 0.99–1.71 s (`fix-m2`) |
| S2b-M3 `step` generic only | **fixed** | `doom_absorb`, `esc_single_le`, `round_r0_le`, `round_r7_le`, `mu_step_chain`, `kstate`, `ks` |
| S2b-M4 `chain_sound` unused | **fixed** | `ftbl_ne_zero` (`chain_sound`, `wDec_bool`, `zc_start`); `qPack_eq_sum` |
| S2b-M5 final instantiation missing | **fixed**, with m2 | `SpartanChainFinal.facts`, `chainHonest`; the KAT ran on a pre-change copy |

Midreview minors: m1, m2, m3, m5, m6 (to S3, see M2), m8 and m9 are fixed. m4 is not fixed,
and its claimed fix is false (m1 here). m7, m10, m11 and m12 are open (m5 here).
