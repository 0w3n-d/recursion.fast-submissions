# V3-S2a review: the witness-sending baseline entry

Adversarial review of stage S2a, the entry half of S2 (design §7.3, §11 S2, V3-9; brief
`docs/baseline/BASELINE-TASK.md`; RESULT `docs/stages/V3-S2a-RESULT.md`). Reviewed on 2026-10-19
against the pin `15e4ae5`. Scope: every file of `submissions/baseline/`, the RESULT, the contract
(`.contract/RecursionFast/Contract/*.lean`), `Library/WitnessSending.lean` and `Library/Security.lean`,
`Controls/Certificate.lean` and `Controls/Extractor.lean` (for the cited controls), and the logs under
`logs/V3-S2/`.

The golf pass ran in parallel and rewrote proofs in `BaselineV3.lean` at 17:57 (240 lines; it was 252
in the RESULT). Line numbers below are the post-golf file. The definitions (`packFast`, `bytesAtF`,
`decodeWitF`, `decodeF`, `witWordsF`, `encodeF`, `check`, `V`, `submission`, `kstate`) and every
theorem statement are unchanged.

## Verdict

**Changes required: two majors (M1, M2) and nine minors.** The certificate is sound and states
what it should. `certified : CertificateR declared submission` is the contract's own structure
against a `declared` that faithfully renders `claim.json`, and the proof uses no gap. The strict
verifier is the right call, and the library finding (§4 of the RESULT) holds. Both majors concern
where organiser material lives and what the documents claim, not the theorem. After the fix pass,
re-run `HARNESS=1 check.sh` on the golfed sources (m7).

## What was checked, and how

| Check | Result |
|---|---|
| `certified` states `CertificateR` for this submission | Yes. The stub's statement is `CertificateR declared submission` (`Contract/Certificate.lean`), with `submission := BaselineV3.submission`. The comparator log exports exactly `certified` and `submission` and accepts under both kernels (`logs/V3-S2/check/harness-work/comparator.log`; comparator `d03acab`, nanoda `3a24072`, both confirmed by `git rev-parse` in the tool trees). |
| The stub is faithful to the contract, not weaker | Yes. The only organiser data is `declared`. Its `image_code_0` unpacks to the 8 words of `extractor.bin`, which equal `WitnessSending.img` and the core's `tests/asm/proofwords.bin` (`image.log`). `ε := ((0 : ℝ≥0) / 1)`, `qV := 0`, and the fuel is `8 + 0 * t`. An affine declared fuel only narrows what a claim can say; `CertificateR.bounds` still requires `D.fuel t ≤ extractorBudget t`. Nothing in the contract's `CertificateR` is dropped or restated. |
| Soundness argument | `check_sound` → `kstate.final`, `Bounded 0` by `bounded_of_not_bad`, and `qV = 0` because `V` is `.ret`. `E` is the library's `decode`, which `check_sound` returns. Rel's node clause is about `submission.Vb`, the strict verifier, and `check_sound` gives exactly that. Correct. |
| Completeness | `check_encode` and `fits_of_rel`. Rel is inhabited without hashing (`leaf s 0` under `leafStmt (chainEnd s 0) 0`), so the theorem is not vacuous. |
| Library finding (RESULT §4) | Confirmed. `decodeWit` reads words 0 to 5 of a leaf and ignores the rest. `lib_check_appended` and `lib_check_truncated` are kernel-checked, and the library's `check` only requires canonicity in the node branch (`Library/WitnessSending.lean`, `check`). |
| Canaries really exercise rejection | Yes. The smoke log has 28 canary lines, each with the verifier's own `Vb: reject` line. They include the 49-byte and 47-byte leaf proofs that the library's verifier would accept. Reproduced independently: `logs/V3-S2/review/smoke.log` (`SMOKE: OK`, 63 `ok` lines, against a copy of the post-golf `baseline-run`). |
| `check.sh` green on the golfed sources | Yes, with `CHECK OK` (`logs/V3-S2/golf-check.log`, the golf agent's run at 17:58, without `HARNESS=1`). |
| Trust policy | The entry imports only `RecursionFast.Library.WitnessSending`, plus `RecursionFast.Contract` in the solution. Nothing imports `Controls`. Axioms are the three (55 declarations, `axioms.log`). The source rule finds 0 issues, and hygiene is OK. No `partial`, `opaque` or `unsafe`, and no code attributes. See M1 for the copies. |
| Measurements | Each number in the RESULT has a log, but several logs were overwritten after the RESULT quoted them (m7). |

## Majors

### V3-S2a-M1: organiser material (the challenge stub, the renderer, the harness) lives in the entry root

- **Where:** `submissions/baseline/Challenge.lean.in`, `render-challenge.py` and `harness-local.sh`.
  `check.sh` steps 5, 9 and 12 use them. RESULT deviation 8; README §1 row "interim organiser
  material".
- **Evidence:**
  - `render-challenge.py` is "the v2 renderer (the core's `scripts/render-challenge.py` at the tag
    `v2-archive`) cut down" (its own docstring). `harness-local.sh` is v2's `scripts/harness.sh`
    order, re-implemented. `CLAUDE.md` hard rule: "Never copy, edit or shadow a contract, library,
    harness or challenge file here. A change to any of them is a pull request to the core."
  - `AGENTS.md` and the brief require an entry pull request to touch only its own root. A root that
    carries its own stub and renderer makes the entry the author of the statement it is certified
    against.
  - **Concrete failure.** The harness input `logs/V3-S2/check/BaselineV3Challenge.lean` is produced
    by `submissions/baseline/render-challenge.py` from `submissions/baseline/Challenge.lean.in`
    (`check.sh` lines 60 and 133). A submitter who follows this worked example and edits the stub,
    for example replacing `CertificateR declared submission` with `Certificate submission`, or
    dropping the image binding, gets `HARNESS: ACCEPT` from `harness-local.sh`. Nothing in the
    pipeline compares the stub against an organiser copy.
  - For this entry the stub is faithful (see the table above). The defect is that nothing enforces
    it, and the baseline teaches the pattern.
- **Fix:**
  - Move `Challenge.lean.in` and `render-challenge.py` to the core-side half of S2. The brief §1
    says the stub goes "in the core-side pull request". Move `harness-local.sh` to the core-side
    half too, or to S3. Until they land, keep them outside the entry root, for example in the core
    scratch clone.
  - Make `check.sh` take the stub, the renderer and the harness from there (`STUB=`, `RENDER=`
    variables), not from `$B`.
  - The README's worked example should then say that the organiser renders the challenge.
  - If the orchestrator keeps them in the root for S2a, record that decision in the RESULT as a
    deviation from the hard rule, and add a check to `check.sh` that the stub's `certified` line is
    byte-equal to `theorem certified : CertificateR declared submission := sorry`.

### V3-S2a-M2: the verifier is quadratic on valid unbalanced proofs; the "linear" claims are false

- **Where:** `BaselineV3.lean` 108–125 (`check`: every level runs `decodeF π` and `encodeF w = π`
  over the whole of `π`, and `bytesAtF` copies each child before recursing). The claims are in
  RESULT §6 ("Linear-time decoding"), RESULT line 67, README line 150 ("The verifier's time is
  linear in the chain length the proof declares"), NOTES lines 12 and 47 ("linear in the witnessed
  chain length"), and the docstrings at `BaselineV3.lean` 84 and 97.
- **Evidence:** measured. Valid "caterpillar" proofs: each node has a deeper left child and a leaf
  right child, every leaf has `n = 0`, so there is no chain work. All were accepted by the post-golf
  `baseline-run` (`logs/V3-S2/review/caterpillar.log`; generator `logs/V3-S2/review/caterpillar.py`).

  | Depth | Proof | `Vb` time |
  |---:|---:|---:|
  | 250 | 34,048 B | 2.68 s |
  | 500 | 68,048 B | 11.63 s |
  | 1,000 | 136,048 B | 49.56 s |
  | 2,000 | 272,048 B | 212.64 s |

  - The time grows ×4 per doubling, so it is `O(|π| · depth)`. A 272 KB valid proof with about 2,000
    hashes in total takes 213 s, more than `verify_s = 60 s` and 10 times the ranked root check.
    Extrapolated, not measured: about 3,200 s for a 1 MiB proof.
  - The per-level constant is about 0.8 µs per byte, consistent with the 1.1 s of the "consistent
    lengths" shape in `smoke.log`.
- **Scope:** this does **not** affect the benchmark as designed. Under the runner's root digest,
  preimage resistance forces the honest shape (depth `r = 8`). The DoS column draws random proofs
  against that digest (design §6.3 steps 4 and 10). The defect is in what the RESULT, README and
  NOTES assert, which is a claim not backed by a log and contradicted by one. It also matters for
  anyone who runs `verify` on a statement the prover chose.
- **Fix:**
  - Correct the claims: the decoding of one level is linear, and the verifier is
    `O(Σ over nodes of the subtree size)`, which is `O(|π| · depth)`. Add the measurement to the
    README's "Known properties" and NOTES, and add an open question.
  - Optional code fix, for the orchestrator to weigh: a verifier over byte offsets into one buffer
    with no child copies, proved equal to `check`, would be linear. Not needed for an unranked
    baseline.

## Minors

### V3-S2a-m1: the Controls header names theorems that do not exist

- **Where:** `BaselineV3Controls.lean` lines 18–21.
- **Evidence:** the header lists `node_wrong_stmt` and `child_over_proofCap`. The file has
  `stmt_unique` and `node_children_capped` instead, as the RESULT §3 table correctly says.
- **Fix:** rename the bullets.
  - `node_children_capped` is the general form of the brief's "child above `proofCap`" negative
    control. Say also that `decodeWit` already returns `none` for such a child (the core's
    `decodeWit_long_child`).

### V3-S2a-m2: "under a second" contradicts the entry's own measurement

- **Where:** README line 152 and NOTES line 43.
- **Evidence:** the README §6 table and `smoke.log` give 1.19 s, and the review run gives 1.21 s,
  for the "tag 1, consistent lengths" proof.
- **Fix:** write "within 1.2 s (`smoke.log`)".

### V3-S2a-m3: the negative claims fail a hard-coded proof script, not the claim itself

- **Where:** `check.sh` step 9; `make-solution.py` lines 22–24.
- **Evidence:**
  - `negative-claims.log` shows `fuel7` and `fuelbig` rejected by "Type mismatch" at the
    `show 8 ≤ 8 + 0 * t` and `show 8 + 0 * t ≤ …` of the fixed solution text. That shows that this
    proof fails, not that no certificate exists.
  - The general facts are kernel-checked only for `WitnessSending.submission`
    (`Controls/Certificate.lean` `flipped_image`, `fuel_7_claim`, `fuel_over_budget_claim`), not for
    `BaselineV3.submission`. The two submissions share `img` and `fuel`, so the facts transfer, but
    only by argument.
- **Fix:** add to `BaselineV3Controls`, which needs no import of the core's controls:
  - `¬ CertificateR {img := flipped, …} BaselineV3.submission`, with a `Declared` literal as in the
    core's control;
  - fuel 7;
  - fuel `2^41`.

  Or make the bounds proof in `make-solution.py` generic (`by simp [declared, submission, …]`), so
  that a rejection reflects a false claim.

### V3-S2a-m4: no concrete positive kernel control of acceptance, and the key lemma is split three ways

- **Where:** `BaselineV3Controls.lean`; `BaselineV3.lean` `check_canonical`, `check_sound` and
  `check_encode` (RESULT deviation 5).
- **Evidence:**
  - Every kernel control of `check` is a rejection. Acceptance is only the general `check_encode`,
    plus the compiled smoke run.
  - The brief's key lemma (`Vb … ↔ …`) is false for a strict verifier, as the RESULT rightly says.
    Its corrected form is never stated as one theorem. The reader has to combine three theorems.
- **Fix:**
  1. Add `check (leafStmt (chainEnd s 0) 0) (encode (.leaf s 0)) = true`, from `check_encode` and
     `⟨Nat.zero_le _, rfl⟩`, with no hash evaluation.
  2. State the key lemma as one theorem:
     `Vb_iff : submission.Vb c π = true ↔ π.size ≤ proofCap ∧ ∃ w, decode π = some w ∧ encode w = π ∧ Rel submission.Vb c w`.
     This is the audience's one-line summary of what the verifier decides.

### V3-S2a-m5: RESULT §4 states a general fact that is kernel-checked only at `n = 16`

- **Where:** RESULT line 124 ("for every `n ≤ chainCap`").
- **Evidence:** `lib_leaf_truncated` is about `w₀ = leaf (dg 1) 16` only.
- **Fix:** either prove `∀ s n, n < 2^56 → decode (dropLast (encode (.leaf s n))) = some (.leaf s n)`,
  or write "for example at `n = 16` (`lib_leaf_truncated`); the argument holds for every `n < 2^56`".

### V3-S2a-m6: `smoke.py` counts any exit code 1 as a rejection

- **Where:** `smoke.py` lines 82–84; `BaselineV3Run.lean` lines 42–46 and 64–77.
- **Evidence:** an uncaught `IO` error in `baseline-run` exits with code 1, the same code as reject.
  That covers an unreadable file and a malformed statement (`readDigest` throws). So a canary or DoS
  check can pass on a crash. It did not happen here: every one of the 28 canary lines carries
  `Vb: reject`.
- **Fix:** do one of the following.
  - In `Verifier.__call__`, require `"Vb: reject"` in stderr for a rejection.
  - Catch exceptions in `main` and return 2.

### V3-S2a-m7: the cited logs were overwritten, and `HARNESS: ACCEPT` predates the golfed sources

- **Where:** RESULT §2, the headline, and `logs/V3-S2/check/`.
- **Evidence:**
  - The golf agent's `check.sh` at 17:58 rewrote `leanchecker.log` (now 24.77 s; the RESULT quotes
    22.7 s), `build-entry.log`, `smoke.log`, `axioms.log` and `loc.log`.
  - `harness.log` (17:50) and the comparator run predate `BaselineV3.lean` (17:57). The ACCEPT is
    therefore for the pre-golf proofs.
- **Fix:**
  - In the fix pass, re-run `HARNESS=1 check.sh` and re-quote every number from the new logs.
  - Consider a per-run log directory, for example `logs/V3-S2/check-<UTC>`, so that a quoted log is
    never overwritten.

### V3-S2a-m8: the local gate does not enforce "no `Controls` imports"; the manifest is self-generated

- **Where:** `check.sh` lines 126–129.
- **Evidence:**
  - The allowlist is `gate --closure Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls`,
    so `Controls` modules are importable. This is v2's policy too (`v2-archive:scripts/org-build.sh`
    line 72).
  - The olean manifest is generated from the same organiser build that stage 0 checks. It therefore
    detects only changes during the run, not a mismatch with a reference build.
  - The brief's §1 note allows both. The entry does not import `Controls`.
- **Fix:** add a sentence to the RESULT's harness description stating both limits. Raise the
  allowlist scope as an open question for the core and S3: drop `RecursionFast.Controls` from the
  closure if the convention is meant to be enforced.

### V3-S2a-m9: README and RESULT overstate gate rule 4

- **Where:** README §3.1, the "Checked by" column; RESULT open question 3.
- **Evidence:** the README says that gate rule 4 checks `V`, `P` and `E` as compiled. The gate log
  says "rule 4: RecursionFast.Challenge.submission: compiled code": it checks the whole constant,
  because its `badgeFields` are v2's (RESULT open question 3).
- **Fix:** write "gate rule 4 (`submission` compiled as a whole, which covers every field)".

## Deviations from the brief (RESULT §5), assessed

| # | Deviation | Assessment |
|---|---|---|
| 1 | The library's `encode`, not LEB128 | Justified. S1 caps `n ≤ chainCap` and children at `proofCap`, so a 64-bit word is complete (`fits_of_rel`), and the image can output the proof's words in place. |
| 2 | `fuel t`, constant 8 | Justified (contract). |
| 3 | No validating copy loop | Justified by `decodeWit`'s leniency (V3-S1-A22). `ImageComputes` is the library's theorem, and `E` is the same `decode`. |
| 4 | Well-founded recursion, no fuel | Justified. The termination measure is `π.size`, with no fuel to make independent. |
| 5 | The key lemma's shape | Justified. The corrected iff should be one theorem (m4). |
| 6 | Strict leaves, linear-time decoding | Strict leaves are correct and needed. The "linear-time" claim is overstated (M2). |
| 7 | One module; no committed `Axioms.lean` or `check-hygiene.sh` | Acceptable. The generated audit covers every `theorem`, `def` and `abbrev`. The inline hygiene regex is a superset of the core's `check-hygiene.sh`. |
| 8 | Stub and renderer in the entry root | **Not acceptable as is** (M1). |
| 9 | `harness-local.sh` instead of `harness.sh` | Within the brief's §1 note. Its location falls under M1. |
| 10 | Own `KState`, library lemma imported | Justified. The library is importable. |
| 11 | Prover file formats | Match design §6.3's interface; S3 fixes them. |

## Observations (no action required)

- `BaselineV3Run` is the entry's own runner, not the organiser's badge executable. Its compiled
  `Vb` is built in the scratch core, not from the comparator-verified artifacts. This is acceptable
  until S3, and README §4 says so.
- `bytesAtF` begins with a `let`, but every argument is explicit, so the eta-expansion trap of the
  brief's §10 does not apply.
- The leaf branch checks canonicity, then `n ≤ chainCap`, then the hash. So a non-canonical or
  over-cap leaf costs no hash (`leaf_over_chainCap` reduces without evaluating BLAKE2s). Under the
  root digest, the worst rejected proof costs one honest-shape decode plus at most one `2^20`-step
  chain (about 5 s at about 5 µs per compression), within `verify_s`.
- Readability for the target audience is good. The module headers say what is the library's and
  what is the entry's, and README §3 is a usable field-by-field worked example. With m1 and m4
  fixed, the controls file reads as a checklist.
