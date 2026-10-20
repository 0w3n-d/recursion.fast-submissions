# Handoff: fixing the rules of recursion.fast in the trusted core

Written 2026-10-20 for the agent that will change the core repository `scaraven/recursion.fast`.
It lists every rule problem found while two entries were built against the v3 contract
(S2a `submissions/baseline/`, the witness-sending argument; S2b/R1 `submissions/spartan-chain/`,
an honest leaf SNARK). It also records the user's decisions of 2026-10-20 and says what is already
implemented, and where. **Nothing listed here is fixed on the core's `main`.**

Each claim cites its source: an issue number, a file and section, a commit, or a log under
`logs/` (gitignored, local to the development VM). Paths are relative to the submissions
repository `/home/devops/Verified-zkEVM/recursion.fast-submissions` unless they are absolute.
Finding ids are quoted exactly as the sources give them. Where two sources disagree, the item says
so.

Reading order:
- §0 orients you and gives the hard rules.
- §1 is the status table.
- §2 has the per-item sections, by priority.
- §3 cross-references `REPORT.md` §4 and §6 and the roadmap #1.
- §4 gives an order of work (dependencies only).
- §5 says what not to do.
- §6 lists what could not be verified.

---

## 0. Orientation

### 0.1 What the core is, and where things are

- **The core** is `scaraven/recursion.fast`, the trusted half: the Lean 4 contract
  (`RecursionFast/Contract/*.lean`, a budget of 500 code lines by `scripts/loc.py`), the vendored
  RV64 model, the untrusted library and controls, the harness tools and the design. Read its
  `CLAUDE.md` first (copy: `docs/core/core-CLAUDE.md`). The design in force is
  `docs/DESIGN-v3.md` (copy here: `docs/design/DESIGN-v3.md`, identical to the core's apart from a
  provenance line). Agreed changes go into the ledger `docs/DESIGN-AMENDMENTS.md`. The master of
  the design is in the user's design workspace, which you must not edit (§0.2).
- **The submissions repository** (this one) holds entries, `records.json`, `AGENTS.md` (the
  submitter's rules) and the `.contract` submodule.
- **The pin.** `.contract` is at `15e4ae5`, "Merge pull request #3 from scaraven/v3/remove-v2".
  `git ls-remote` on 2026-10-20 shows the core's `refs/heads/main` still at `15e4ae5`. The contract
  is 328 code lines at the pin (`loc.py`, run here).
- **Local checkouts:**

  | path | what | state |
  |---|---|---|
  | `/home/devops/Verified-zkEVM/recursion.fast` | the core's own checkout | **read-only; never build or edit there** |
  | `/home/devops/Verified-zkEVM/rf-core-ks` | scratch clone; branch `v3/ks-potential` = the KS amendment (§2.1) | head `05fde28`; **pushed** to origin (reflog: "update by push", 2026-10-20 09:07:59 UTC); **PR #11 open** |
  | `/home/devops/Verified-zkEVM/rf-core-s2a` | scratch clone (origin = this repository's `.contract`); branches `v3/s2-interim-harness` (`2a4588b`) and `v3/ks-interim-harness` (`4a1a1ed`, on top of `05fde28`) | **local only, never pushed** |
  | `/home/devops/Verified-zkEVM/rf-core-sc` | shared development clone, on `v3/ks-potential` `05fde28`, with uncommitted entry scaffolding | the entry agents' workspace; do not reuse it |
  | `/home/devops/CambridgePQ/recursion.fast` | the user's design workspace, the master of DESIGN-v3 and `DISCUSSION.md` (Q1–Q6) | **read-only** |
  | `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` | the prebuilt shared package tree | **read-only**: never `lake update`, never `lake exe cache get` against it |

- **Issues:** #1 (roadmap), #4 (O-25; one comment from this work), #5 (one comment), #6, #7, #8,
  #9, #10, all open. **PR #11** "V3/ks potential" (`v3/ks-potential` → `main`) was opened by
  `scaraven` at 2026-10-20T09:09:28Z. It is open and mergeable, has an empty body, no review and
  no comment.
  - **Sources disagree.** `REPORT.md` §5 and §6 Q1, `PLAN.md` D-8 and D-12, `V3-S2b-RESULT.md`
    §8 and §9 and the #5 comment say the branch "was not pushed". That was true when they were
    written. The push and the PR came later (reflog and `gh pr view 11`).

### 0.2 Hard rules when you edit the core

Copied from the core's `CLAUDE.md` (`docs/core/core-CLAUDE.md`) and this repository's
`CLAUDE.md`. They are not negotiable.

- **Work in a fresh clone or a new worktree** of the core, on a new branch. Never edit, build in
  or commit to `/home/devops/Verified-zkEVM/recursion.fast` (another agent may be working there)
  or `/home/devops/CambridgePQ/recursion.fast`. To get packages, symlink the shared tree:
  `mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages`.
  The shared tree is read-only.
- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`.
- **No code-changing attributes:** `implemented_by`, `extern`, `export`, `init`, `csimp`,
  `cpass`, `computed_field`. No `unsafe`, `partial` or `opaque`. No elaboration-time code
  (`#eval`, `run_cmd`, `elab`, `macro`, `initialize`, `import Lean`, …), comments included (the
  source rule scans them).
- **Contract:** it imports Lean core, Mathlib and the vendored Rv64 only, never
  ArkLib/CompPoly/VCVio/PolyFun. It has no field (V3-1). The budget is ≤ 500 code lines for
  `Contract.lean`, `Contract/*.lean` and `Hash/Blake2s.lean` (`scripts/loc.py`). Every definition
  has a docstring that says what it means.
- **Statements are non-vacuous:** every definition has a positive and a negative control.
  **A proof never changes the statement it proves.**
- **Stage protocol**, one stage at a time, each on a branch merged by pull request:
  1. implement, keep `lake build` green, write `docs/stages/V3-S<n>-RESULT.md` (files with
     `loc.py` counts, build times, controls, deviations, open questions);
  2. adversarial review (`docs/reviews/V3-S<n>-review.md`, findings `M<i>`/`m<i>`, a verdict),
     in parallel with 3;
  3. golf, with no statement changed (`docs/reviews/V3-S<n>-golf.md`);
  4. fix every major finding and answer every minor one, then append `## Fix pass` to the
     RESULT;
  5. the orchestrator records the ledger entries and commits.

  **Subagents do not commit.** Skills: `lean-spec-authoring` for definitions and statements;
  `adversarial-review` and `lean4:review` for reviewing; `lean4:golf`; `lean4:lean4`.
- **No pushing** and no creating remotes, PRs or issues unless the user asks.
- **No estimates** of human work. Durations quoted here are measurements with their logs.
- **Long builds:** give every background or locked Lean build a `timeout`, and tell sub-agents to
  do the same. If a module runs for minutes, inspect it with `ps` and its log; do not wait.
- **The pin moves only with a contract change, in its own commit**, before any entry is
  certified against the new commit. Never pin a commit that is not on the core's remote (§5).

### 0.3 Vocabulary (one line each)

- `OProg α`: a query program, a tree that asks the oracle `ByteArray → Digest` and branches on the
  32-byte answer (`Contract/Oracle.lean`).
- `Log`: a list of (query, answer) pairs.
- `runLog L`: run a program with its answers read from `L`.
- `KS`: knowledge soundness in the ROM, in a local counting form over logs (`Contract/Security.lean`).
- `Complete`: perfect completeness over every oracle function.
- `Rel Vb`: the relation over digests.
  - Leaf: `c = leafStmt (chainEnd s n) n`, `n ≤ chainCap`.
  - Node: `c = nodeStmt c₁ c₂` with both child proofs accepted by the deployed `Vb`, which is
    `V` run under concrete BLAKE2s (`blake2sOracle q = BLAKE2s(0x52 ‖ q)`), with proofs above
    `proofCap = 2^20` rejected.
- `ImageComputes img E fuel`: a RISC-V image provably computes `E` on the contract machine
  within `fuel t ≤ B t = 2^40 + 2^8·t` steps (`Contract/Extractor.lean`).

---

## 1. Status table

Severity classes:
- **exploit**: an entry can score or certify without doing the intended work.
- **blocks**: honest entries cannot be certified or accepted.
- **hygiene**: wrong text, a missing control, a stale document.
- **perf**: a cost an entry inherits.

| # | Id(s) | One-line problem | Severity | Fix exists? | Decision needed |
|---|---|---|---|---|---|
| 2.1 | #5; F1-1, F1-2; ADV-M2, ADV-M3; D-2, D-8, D-9; V3-S2-KS-M1 … m6 | `KS` at `errorCap` is unsatisfiable for every Merkle/BCS verifier | **blocks** (every succinct entry) | **yes**: `v3/ks-potential` `05fde28`, PR #11 open, unmerged | merge PR #11; `logCap` `2^96` or `2^58` (REPORT §6 Q2) |
| 2.2 | #4 and its comment; O-25; V3-S1-M1; ADV-M5 | a certified `V` may recognise BLAKE2s and accept a magic proof | **exploit** | direction settled (§2.2): contract-owned verifier template over first-order data, INV′, A1–A4; not implemented | **user**: reverse Q6? T, MG1 (recommended) or review-only ranking |
| 2.3 | #6(a); ADV-M1; O-18, O-9 | `T_V = 2 s` wall time does not exclude witness-sending (threads, fast BLAKE2s) | **exploit** (wins board T while proving nothing) | design only | CPU time / one core / step count (REPORT §6 Q7) |
| 2.4 | #6(b); ADV-M4 | board T rewards avoiding recursion (witness-sending below level `j`) | **exploit** (incentive) | design only | cap at every level, or rank column R |
| 2.5 | #7; F1-3; ADV-M7; D-3; O-15(2), O-21; Q1 | node extraction is decoding; the RISC-V image and the budget make it infeasible | **blocks** (every recursive entry) | none; **decided 2026-10-20**: `E` in Lean with a proved step bound | the step-unit budget value |
| 2.6 | O-23; #8(2); #9 item 10; ADV-m2; V3-S1-m10, V3-S1-A9 | perfect completeness over every `H` forbids grinding and challenge-dependent cases | **blocks** (designs) | none; **decided 2026-10-20**: `CompleteWithError δ` | `completenessCap` `2^-128` (recommended) or `2^-96` |
| 2.7 | D-11; V3-S2b-M1; REPORT §2.7 | nanoda (the second kernel) has no stated budget; an ordinary lemma took it to 52 GB | **blocks** (`HARNESS: REJECT` for a sound entry) | entry-side rewrite only; **not filed** | nanoda memory and time caps (REPORT §6 Q4) |
| 2.8 | V3-S2b-M2; #9 item 4; ADV-m5; V3-S2a OQ 3, 4, 7, 8 | interim harness: the CompPoly closure is not allowlisted or pinned; gate rule 4 checks v2 fields | **blocks** (`HARNESS: REJECT`) | **yes, local**: `rf-core-s2a` `09668b5`, `4a1a1ed` (+ `2464e97`, `26c3b23`, `9d5b26a`) | adopt in S3 (REPORT §6 Q8) |
| 2.9a | #8(1); F1-4; V3-5, V3-6; O-14, O-22 | `proofCap`, BLAKE2s-only, R1CS and UD-only leave just WHIR-class sizes for recursion | **blocks** (ranked recursion) | none | one of four options (REPORT §6 Q6) |
| 2.9b | #8(3); ADV-M6 | preprocessing SNARKs cannot meet `Complete ∀H` within `qV ≤ 2^16` | **blocks** (designs); sharpens O-25 review | design only (an indexer) | adopt the indexer? |
| 2.9c | #8(4); ADV-M8 | hash-based accumulation (named in §1) is not expressible | hygiene (a design claim) or a design change | none | correct §1, or an accumulation relation |
| 2.10 | #10; V3-S2a findings (S2a OQ 1, 2) | library `check` accepts malleated leaves (fails the canaries); `packBytes`/`bytesAt` are quadratic (563 s) | perf / hygiene | **yes, in the S2a entry** (`submissions/baseline/BaselineV3.lean`), to port | none |
| 2.11 | #9 items 1–10; ADV-m1, m3, m4, m6, m7 | minor rules: fallback completeness; repeated runs; `AGENTS.md` drift; trust statement; theorem domain; `Fintype`; ArkLib; field speed | hygiene; item 1 is an exploit of liveness | `AGENTS.md` drift fixed here (`5cb89d8`); the rest none | ArkLib policy (item 8) |
| 2.12 | V3-S2a-M2; V3-S2b-m1; S2b-m4 | valid unbalanced ("caterpillar") proofs: 275 s at 1 MiB; not covered by the DoS column | perf | none (an offset parser was sketched) | acceptable? (REPORT §6 Q10) |
| 2.13 | V3-S2-KS-m1, m2, m4, m5; ledger gap for `05fde28` | housekeeping of the amendment: no `V31` control; stale design text; the noncomputable instance not recorded in the RESULT or the ledger | hygiene | partly | `V31` in S4, or accept the paper argument (REPORT §6 Q11) |
| 2.14 | user decision 3 (2026-10-20); REPORT §2.4(1) | proof size: Ligero is √-size, 1,464,107 B at `n = 2^14`; R1′ with folding | open design direction, no rule change yet | none | the rule-side asks in §2.14 |
| 2.15 | REPORT §4 item 2 | the organiser library: upstream the entry's reusable layers (about 10,500 lines) | perf (submitter cost) | the code exists in the entry | adopt as S4? (REPORT §6 Q8) |
| 2.16 | #1 | the roadmap is stale (S1 shown "in review"; links to the `v3/s1-contract` branch); every v3 stage and open item is unticked | hygiene | none | none |

---

## 2. Items, by priority

### 2.1 KS amendment: the potential form with a log-length guard (#5) — **merge PR #11, then move the pin**

**Intuition.** The S1 rule asks the submitter to name, for every log and every fresh query, a set
of "bad" answers of density at most `2^-128`. Two standard parts of every hash-based SNARK cannot
be charged that way:
- the Merkle collision term grows with the log length;
- a query phase spreads one challenge over several 32-byte answers.

So no honest succinct entry can be certified. The fix replaces the bad sets by a potential that
rises by `ε` on average, and covers only logs of up to `logCap` entries.

**Precise problem** (#5; F1 §1–§2; ADV-M2, ADV-M3). At the pin, `KState.Bounded` is
`∀ L q, Nat.card {a // bad L q a} ≤ ε·2^256` with `ε ≤ errorCap = 2^-128`:
- (a) Over logs longer than `2^128`, collision and late-preimage sets exceed the cap.
- (b) The boolean form charges a `k`-answer query phase `(1−δ)^{t/k}` at its last answer.

Kernel-checked (`logs/adv-probes/CountingForm.lean`, standard axioms, 6.4 s):
- `collision_not_capped`;
- `product16_not_capped`: a 16-query verifier with ROM error `2^-128` has no state below `2^-8`;
- `eps_ge_density`: spreading the event over more answers never helps.

Under the pin, the only certifiable entries are the witness-sending argument and the O-25
backdoor (REPORT §2.1).

**The fix, already implemented.** Branch `v3/ks-potential` in `rf-core-ks`. Three commits on
`15e4ae5`:
- `ecdcbd5`: the potential form, V3-KS-A1 … A5;
- `c3f6380`: the fix pass, with `logCap = 2^96`, the literal `2^256` and the paper theorem;
- `05fde28`: `noncomputable instance`.

`git diff --stat 15e4ae5 v3/ks-potential` lists 12 files (+1578/−148):

| file | change |
|---|---|
| `RecursionFast/Contract/Security.lean` (**TRUSTED**) | `noncomputable instance : Fintype Digest` (by `Fintype.ofSurjective` from `Fin 32 → Fin 256`); `def logCap : ℕ := 2 ^ 96`; `KState R V E ε` with `μ`, `empty`, `step`, `final`; `KState.Bounded` removed; `KS` with `Nonempty`; header rewritten. Imports `Mathlib.Data.Fintype.Pi` and `Mathlib.Algebra.BigOperators.Group.Finset.Defs` in place of `Mathlib.SetTheory.Cardinal.Finite`. 23 → 26 code lines; contract 331 of 500 |
| `RecursionFast/Library/Security.lean` | `BoolKState` (S1's structure verbatim), `Bounded`, `BoundedBelow`, `KState.ofBool`, `KState.zero`, `KState.mono`, `step_of_hits`, `one_le_of_jump`, `final_unguarded`, `step_unstopped`, `@[simp] fintype_card_digest` |
| `RecursionFast/Library/PaperTheorem.lean` (new, 113 code lines) | `paper`: for a lazily sampled oracle and a game of `n ≤ logCap` queries, P[accepted and unextractable] `≤ n·ε`, kernel-checked |
| `RecursionFast/Library/WitnessSending.lean` | `kstate := KState.zero 0 …` |
| `RecursionFast/Controls/Security.lean` | S1 controls ported; `jump`, `mono_control`, boolean-form controls (`bool_bounded_ge_one`, …) |
| `RecursionFast/Controls/Potential.lean` (new) | `twoLucky` (a potential at `2^-192`, no boolean state below `2^-96`); `Vcol` (`collision_no_bool_kstate`, `collision_ks`); `V24` (`v24_no_bool_kstate`, `v24_ks`) |
| `RecursionFast/Controls/Backdoor.lean` | `boolState` (S1's state), `kstate := KState.ofBool …`; O-25 unchanged |
| `RecursionFast/Controls/Certificate.lean`, `Controls.lean`, `Library.lean` | one line each |
| `docs/DESIGN-AMENDMENTS.md` | V3-KS-A1 … A7, "Answered, not changed" |
| `docs/stages/V3-S2-KS-RESULT.md` | RESULT and fix pass |

The trusted text after the fix (from `git diff`, docstrings omitted):

```lean
noncomputable instance : Fintype Digest :=
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i))
    fun d => ⟨fun i => d[i].toFin, by ext i hi; simp⟩
def logCap : ℕ := 2 ^ 96
structure KState (R) (V) (E) (ε : ℝ≥0) where
  μ : Log → ℝ≥0
  empty : μ [] = 0
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w
def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV
```

Why each detail is the way it is:
- **`logCap = 2^96`, not F1's `2^64`.** V3-S2-KS-M1 showed that `2^64` certifies a verifier that
  compares digests on 24 bytes (96-bit generic security) at the 128-bit cap. The probe is
  `Probe.v24_ks`; the control is `v24_no_bool_kstate`. At `2^96` an honest Merkle verifier pays
  about `2^-145` per query (#5 comment item 1; KS review §3).
- **The literal `2^256`.** With `Fintype.card Digest` in its place, failing unifications try to
  evaluate the instance (V3-S2-KS-m2).
- **`noncomputable`.** As a computable closed term, the instance made every compiled binary that
  imports the contract enumerate `256^32` functions at start-up. A hello-world reached 22.9 GB in
  20 s without printing (`logs/spartan-chain/oracle-merkle-transcript/init-blowup.log`; D-9; #5
  comment item 4). With `noncomputable`, a binary starts in 0.20 s with 86 MB.

**Measured.** The amended core: `lake build` 2 min 00 s cold with a 4.16 GB peak, 2.8 s warm;
axiom audit PASS on 811 declarations; `ci.sh` passed; line budget 331/500
(`logs/ks-amendment/fix/`). The honest entry is certified against it: `Challenge.certified`,
`HARNESS: ACCEPT` (`logs/spartan-chain/infra/harness-final3/`, `harness-final4/`). Its potential
pays `(2^96(3·2^8+1)+1)/2^256` per fresh query plus `(4/5)·2^-129` (REPORT §2.1).

**Controls.**
- Already present: every S1 control is ported with its meaning (KS review, Pass B table).
- Separating controls: `twoLucky` (the potential is needed) and `Vcol` (the guard is needed for
  boolean states).
- `V24`: the `logCap` value is load-bearing.
- **Missing:** a control showing that the guard is needed for a *potential*. `V31` was proposed
  (V3-S2-KS-m1), not built; for `Vcol` alone it is borderline false (§2.13).

**What remains to do for this item:**
1. **The PR description.** PR #11 has an empty body. With the user's permission, give it one:
   link #5, the RESULT, the review (copy `docs/reviews/V3-S2-KS-review.md` from here into the
   core's `docs/reviews/`, as the stage protocol expects), the controls, the measurements and the
   noncomputable fix. Issue #5 still says "Nothing has been pushed yet".
2. **The ledger gap** (§2.13). `V3-S2-KS-RESULT.md` quotes the instance as computable, both in
   the first text and in the fix-pass verbatim block. Neither the RESULT nor `DESIGN-AMENDMENTS.md`
   records `05fde28`. Add a ledger entry (for example V3-KS-A8) and a RESULT note before the merge.
3. **The design text.** DESIGN-v3 §1.1 (figure), §4.1, §4.2, §4.5, §6.6 and §8 contradict the
   amended contract (V3-S2-KS-m5). The ledger (V3-KS-A1, A2, A6) carries the replacement wording.
   The core's `docs/DESIGN-v3.md` and its master in the design workspace must be patched together;
   the master is the user's, so ask.
4. **The `logCap` decision** (REPORT §6 Q2). Keep `2^96` (the review's recommendation), or use
   `2^58` to sit under the extractor's `2^60`-word tape (ADV-m7; #9 item 6)? With decision 2.5
   (no RISC-V tape), the `2^60` argument may disappear; re-check.
5. **After the merge,** move this repository's pin in its own commit
   (`git -C .contract fetch origin main && git -C .contract checkout <merge commit> && git add .contract && git commit`).
   Then:
   - re-certify S2a against the new contract (the core's `WitnessSending` is already ported;
     S2a's own `kstate` must become `μ := 0`);
   - update `AGENTS.md` §4, `docs/baseline/BASELINE-TASK.md` §0, §5 (V3-KS-A5) and `AGENTS.md`
     §15;
   - add the `Fintype Digest` tactic note to `AGENTS.md` (V3-S2-KS-m2: avoid `positivity`, `gcongr`,
     `rfl`/`decide` on `Fintype.card Digest`; rewrite with `fintype_card_digest`).

**Not in this PR, although #5 and #7 proposed it:** raising `extractorBudget`.
`Contract/Extractor.lean` is not in the diff. It is subsumed by §2.5.

**Acceptance.**
- PR #11 is merged with a review on record.
- The ledger records all of `05fde28`.
- DESIGN-v3 is patched from the ledger.
- `ci.sh` passes and the contract is ≤ 500 lines.
- The submissions pin is at the merge commit, and S2a and R1 print `HARNESS: ACCEPT` against it.

**Dependencies.** None upstream. 2.5, 2.6 and the O-25 fix all rebase on it.

---

### 2.2 O-25 (CGH) — direction settled; the reversal of Q6 awaits the user

**Settled direction (2026-10-20, after two design rounds and two independent adversarial
reviews).**

Sources:
- the design memo `notes/F2-o25-uninstantiability.md`: round 1 (Candidate E) and round 2
  (Candidate T, §R2.0–R2.11);
- the reviews `docs/reviews/F2-o25-review.md` (round 1: E broken, O25-M1…M6) and
  `docs/reviews/F2-o25-review-r2.md` (round 2: T's core holds, O25T-M1…M6, m1…m9, middle ground
  MG1).

1. **Rejected: making `V` parametric (Candidate E and #4's own proposal).** Opaque digests with
   equality only are sound; kernel probes closed every Lean escape hatch tried. But every other
   channel a real SNARK verifier needs reopens the one-line backdoor:
   - an index map whose width `V` chooses (`idx a 256 0` is the whole answer; kernel-checked);
   - `CommRing` with `DecidableEq` over the one deployed field, which names every element;
   - decoding proof bytes into the field;
   - degree-1 recognition `x − τ`.

   **Post-hoc challenge verification** also defeats every design in which submission-written
   checks see a challenge as a value. After `c₁`, the prover sends BLAKE2s wires over the prefix,
   and low-degree checks confirm `c₁` equals their output. No fixed point stops it.
2. **Adopted: the core of Candidate T.** Every part of the verifier that touches the oracle is
   contract-owned: the transcript, the sumcheck/zerocheck checks and the PCS/Merkle/proximity
   checks. Submissions supply only **first-order data that is fixed and bound into the seed before
   any challenge**, plus `P` and the extractor. The invariant, as corrected by O25T-M1 (**INV′**):
   no submission-authored code ever produces or consumes an operand of an acceptance check that
   depends on the oracle. Concretely:
   - the seed query is made by the contract;
   - the public input `x` is a contract-fixed map of the statement, not a submission function;
   - the seed binds the statement, `csDigest` (over the *expanded* instance) and `paramsDigest`.
3. **Admissibility rules A1–A4** (O25T-M2) go into the contract header and the rulebook. Without
   them, one constructor with a challenge term reopens the backdoor as data. Data-defined
   functions are:
   - (A1) evaluated only at challenges and at PCS-bound evaluations of pre-challenge commitments,
     with a degree bound;
   - (A2) never given a challenge as a coefficient or variable, and the witness is committed in a
     single phase;
   - (A3) multi-round sub-protocols (lookup, permutation, grand product, GKR, memory checking) are
     template gadgets only;
   - (A4) no datatype is an interpreter.
4. **Templates are short reference specifications, with a kernel theorem `impl = spec`.** A spec
   is reviewed once, against an enumerable checklist, with an embargo on whoever proposed it
   (O25T-M5). That review is the one remaining human-trust item.
5. **Breadth: recommended MG1, which is the user's decision.**
   - Agents choose the constraint format (uniform R1CS, CCS, AIR or Plonkish with bounded-degree
     custom gates).
   - They choose a compiler (Spartan-like sumcheck, HyperPlonk-like zerocheck or STARK-AIR
     quotient), a PCS (Ligero, WHIR, Basefold or FRI) and a field (`GF(2^64)`/`EF`, Goldilocks²
     or BabyBear⁴), each from a contract-owned menu that satisfies A1–A4.
   - New menu items arrive by core pull request.
   - Free-form `V` stays as an **unranked research track**. It is enforced by type and by a tier
     field in `records.json`, not by policy (O25T-m6).

   **This reverses Q6** ("No organiser compiler"; "the submitted object is the non-interactive
   argument itself"; field-agnostic). The user must choose: T as specified, MG1, or review-only
   ranking.

**Open blockers to fix before implementation:**
- O25T-M3: spartan-chain cannot be expressed. Its matrices depend on `n` and `κ`, and T has no
  node branch.
- O25T-M4: the ranked board is empty at launch. The Ligero leaf exceeds `proofCap`, and a generic
  evaluator inside a self-verifying node costs `nnz(cs)`. It needs a WHIR-class template and a
  node design under A3.
- O25T-m2: T-3 predates `4b3356a`. Use `ext`/`Computes`, `δ`/`CompleteWithError` and the 288-line
  contract.
- O25T-m4: the generic `Template.ks` is a new extraction proof, not a generalisation of
  spartan-chain's.
- O25T-m7: the contract grows by about 100–130 lines, to roughly 390–420 of 500.

**Strength, stated precisely:**
- KS remains a kernel theorem.
- By the contract's definitions (structural, no meta-theorem), no submission-authored code can
  express the `Backdoor.lean`, ADV-M5 or post-hoc mechanism.
- That the template itself never recognises BLAKE2s rests on reviewing a short spec against A1–A4.
- The irreducible residual is BLAKE2s-Fiat–Shamir soundness of the template for every admissible
  instance. No ROM theorem can remove it (CGH98; GK03 and BBHMR19 for this protocol family).
  Removing it would need correlation intractability of BLAKE2s, which is unproven.
- A clever adversary needs a new Fiat–Shamir attack beyond KRS25/Fenzi26, delivered through
  first-order data, or a subverted template review.
- The cheap future risk is a menu item that violates A2. A1–A4 must therefore be checked for every
  new template.

**Status.** The user decided on 2026-10-20 that **the ROM-uninstantiability gap O-25 / #4 must
be closed**. A separate design track is working on the fix; its notes will be
`docs/snark-baseline/notes/F2-o25-*.md` (none existed when this was written). This section
summarises the problem and the candidates on record. **Do not design or implement a fix from it.**
Replace the placeholder line above with the decision when it is made.

**Intuition.** The certificate proves security for a *random* oracle. The harness runs the
verifier with *one* oracle, BLAKE2s, which anyone can compute. A verifier can therefore test "is
my oracle BLAKE2s?" by comparing an answer with a locally computed hash, and accept a magic proof
when it is. Over a random oracle that test succeeds with probability `2^-256`, so the theorems
hold. In deployment it always succeeds. This is Canetti–Goldreich–Halevi.

**Precise problem** (#4 §1; DESIGN-v3 §5.4, §6.7, §12 O-25; V3-S1-M1).
`Controls/Backdoor.lean` is kernel-checked:
`theorem backdoor : Certificate S ∧ ∀ c, S.Vb c (magic c) = true`. Its `V` asks the empty query,
compares the answer with `blake2sOracle ""` computed locally, and on a match accepts the 32-byte
magic proof of every statement. The bad set is one answer in `2^256`, so `KS` holds at `errorCap`
with one query. The honest branch is untouched, so `Complete` holds. Every harness check passes.
Today board T rests on a rule (§6.7: "`V`'s local computation must not evaluate the oracle's
instantiation") and on intake review (S7).

**The candidate fix stated in #4 §2–§7: a parametric `V`.**
`V : ∀ (D : Type) [DecidableEq D], D → Tape D → OProg D Bool`:
- every oracle answer, the statement and every digest slot of the proof are values of an abstract
  `D`;
- `Tape D := List (ByteArray ⊕ D)` is a contract proof grammar; queries are structured,
  `List (ByteArray ⊕ D)`;
- the contract's wrapper instantiates `D := Digest`, parses the proof, serialises each query, and
  passes `DigestOps D` (`chainStep`, `leafStmt`, `nodeStmt`);
- the gate checks `V`'s type literally;
- the argument is parametricity, a meta-theorem: with only `DecidableEq D`, `V` can compare an
  answer only with other `D`-values, never with a `Digest` constant it computed.

#4 lists the required design changes (§3.1–§3.4, §2, §5.4, §6.7, §7.6, §8 with about thirty
trusted lines, §11, §12). It also lists the residual channels, each with its closure: ambiguous
serialisation (needs `serialise_injective`, `serialise_inl_ne_inr`, `parse_serialise`), extra
`D` operations, grammar overlap, and Lean escape hatches. Finally it lists the controls to ship
(#4 §7). The residual boundary is a real BLAKE2s collision.

**Evasions and objections in our comment on #4** (ADV-M5 items 1–5; draft
`issues/I5-comment-on-4.md`):
1. **Literal trigger, kernel-checked** (`logs/adv-probes/LiteralTrigger.lean`, `backdoor_lit`,
   standard axioms). The trigger is replaced by a 32-byte literal computed offline. Its constant
   closure contains no `blake2sOracle`, `tagRO` or `Submission.Vb`. Its remaining BLAKE2s
   footprint (`blake2s256`, `Blake2s.compress`, reached through `Rel`'s chain check) is identical
   to the honest `WitnessSending.V`'s. The S1 review's proposed closure test cannot tell the two
   apart.
2. **Trace-check trigger (paper).** A debug branch checks a proof-supplied concrete trace of the
   in-circuit BLAKE2s gadget whose output equals the oracle's answer. It recognises the
   instantiation while evaluating no hash.
3. **The §6.7 rule is over-broad.** It also bans concatenation nodes (which §6.7 allows),
   hard-coded verification keys, and "consistency fast paths". R1's node branch evaluates
   `blake2sOracle` on the children to decide `Rel` and compares no oracle answer
   (`V3-S2b-RESULT.md` §7), yet a syntactic rule would flag it.
4. **The parametric-`D` fix cannot support Fiat–Shamir.** If answers stay opaque, no challenge
   can be derived. If a challenge interface yields `b` bits per answer, `V` can compare those bits
   with local BLAKE2s bits, which certifies recognition at `2^-b`; that needs `b ≥ 128`, which is
   certified at `errorCap`. Under the potential `μ` of §2.1, `k` answers of `b` bits each are
   priced at `2^-bk`, exactly like a spread challenge. Parametricity protects commitment answers,
   not challenge answers. Keying or salting does not help (V3-S1-M1's two-query argument).
5. **`AGENTS.md` does not state the rule** (no hits for "O-25", "recogni", "magic"). That is
   still true of this repository's `AGENTS.md` today.

ADV1's recommendations (the #4 comment):
- state the rule semantically in `AGENTS.md`;
- require `NOTES.md` to list every comparison of an oracle answer with anything else;
- make intake review mandatory, with a challenge period;
- drop or narrow the parametric-`D` candidate;
- adopt the indexer (§2.9b).

**Links to other items.**
- §2.6: dropping `Complete ∀H` removes the theorem that honest proofs verify under BLAKE2s, which
  is a liveness analogue of O-25 (see there).
- §2.9b: the indexer removes the one legitimate hard-coded constant compared with an oracle
  answer.
- §2.1: the potential prices spread recognition.

**Decision needed (user).** Pending; see the design track.

---

### 2.3 The succinctness cap `T_V` does not exclude witness-sending (#6 (a))

**Intuition.** The cap is meant to separate a SNARK verifier, with polylogarithmic work, from the
trivial verifier, which recomputes every chain. But it measures wall time. Wall time rewards
threads, and the trivial check with a fast BLAKE2s fits under 2 s.

**Precise problem and evidence** (#6; ADV-M1; DESIGN-v3 §6.3 step 4, §6.5 "22–29 s … margin
10×"). The whole ranked tree (`r = 8`, `n = 2^14`, `2^22` compressions), on a QEMU 32-vCPU VM with
no `pclmulqdq`/`gfni`, which is not the reference machine:

| root check | time | log |
|---|---|---|
| certified S2a `Vb`, reference BLAKE2s, sequential | 20.87 / 21.23 / 21.16 s (#6); 20.69 / 21.11 / 20.93 s (REPORT §2.2) | `logs/V3-S2/calibration-r8-n16384.log`; `logs/V3-S2/fix/calibration-r8-n16384.log` |
| reference BLAKE2s + `Task.spawn`, chains only | 1.17–1.31 s | `logs/adv-probes/refchain.log` |
| unrolled BLAKE2s, sequential | 0.64–0.69 s | `logs/adv-probes/fastchain.log` |
| unrolled BLAKE2s + `Task.spawn` | 37–43 ms | `fastchain.log` |

(The two S2a rows are different runs; the sources quote different triples.)
`Task.spawn` is kernel-transparent: `(Task.spawn f).get = f ()` by `rfl`, and `all_par` uses
`propext` only (`logs/adv-probes/TaskRfl.lean`). A threaded check is therefore provably equal to
the sequential one, and the source rule accepts it. Two caveats: no threaded `Vb` was built as an
entry, and the unrolled hash was not proved equal to `chainStep`. Raising `n` does not close the
gap: at `n = chainCap` the threaded unrolled check is about 2.6 s, against the required
`5·T_V = 10 s`.

**Proposed change** (#6; ADV1 says all three parts are needed):
1. measure CPU time (user + system), or pin the check to one core;
2. calibrate against the best linear verifier the organiser can write: `T_V ≤ T_triv,best/10`,
   about 65 ms of CPU on this VM, or change the benchmark shape (for example `r = 4`,
   `n = 2^20`);
3. better, O-18: a deterministic step count.

**A new option opened by §2.5.** If the extractor's step-counting language is adopted, the same
cost model could price `Vb` (a step-count `T_V` without a Lean-to-RISC-V compiler, which
O-18/O-12 assumed). That would need `V` in that language, which is a much larger change. Record
it; do not assume it.

**Controls / acceptance.**
- With the chosen measuring rule, the threaded and unrolled witness-sending probes
  (`RefChain.lean`, `FastChain.lean`) are measured and exceed the cap by the stated margin.
- §6.5's numbers and margin are corrected.
- `T_V` is set after the benchmark shape and the measuring rule are fixed (REPORT §4 item 9).
- Trust cost: none (the harness and the text).

**Dependencies.** O-6 (the reference machine), O-9 (compiled field speed; §2.11 item 9), O-18.

---

### 2.4 Board T does not reward recursion (#6 (b))

**Intuition.** Witness-sending proofs cost nothing to produce. A prover can therefore send
witnesses below some level `j` and run one SNARK over all chains above it, which saves node
proofs. In the limit (`j = 8`) there is one flat SNARK and no recursion at all.

**Precise problem** (#6 (b); ADV-M4). §6.7's row "pays in `T_tree`" and §5.3's "a prover cannot
flatten the tree" are false: the level-`j` nodes do the chain work an honest leaf proof would do
anyway, and `2^{8−j} − 1` node proofs replace 255. The sample checks pass: a level-7
witness-sending proof is `2^21` compressions, about 12 s, inside `verify_s = 60 s`. Only memory
(96 GB) and parallel efficiency bound `j`.

**Proposed change.**
- Apply the CPU-time cap of §2.3 to sampled proofs **at every level**. A level-`j` witness-sending
  proof costs `2^{j+14}·160 ns`: about 42 ms at `j = 4` and 84 ms at `j = 5`. A 65 ms cap forces
  recursion from level 5 up; every level needs `n ≈ 2^20`.
- Or rank column R beside T.
- Either way, correct §5.3 and §6.7.

**Acceptance.** The chosen rule makes a level-`j` flattening strategy either non-admissible or
priced; the design text is corrected. Trust cost: none.

**Dependencies.** §2.3's measuring rule.

---

### 2.5 The extractor: a Lean function with a proved step bound (#7; **user decision 2026-10-20**)

**Intuition.**
- Knowledge soundness needs an extractor that is *efficient*: otherwise "the extractor finds a
  witness" collapses to "a witness exists", which is only soundness.
- Today efficiency is expressed by a RISC-V image proved to compute `E` within a step budget.
- For recursive nodes, `E` must decode a Reed–Solomon codeword of about `2^29` symbols. Writing
  and proving that in RV64 assembly is a project of its own, and it does not fit the budget.
- The user decided to replace the image by a Lean extractor written in a small step-counting
  language, with a proved step bound.

**Precise problem** (#7; F1 §3; ADV-M7; DESIGN-v3 §4.4; decision Q1 in `docs/design/DISCUSSION.md`):
1. **A log lookup is unprovable.** `Rel`'s node clause demands `Vb c₁ π₁ = true` under concrete
   BLAKE2s, while the log holds random-oracle answers. The only provable route is circuit
   correctness: the extractor must find the committed word in the log and decode it.
2. **The budget.** `extractorBudget t = 2^40 + 2^8·t` (`Extractor.lean:92`). Its header sizes
   `2^40` for "a quasi-linear decoder of a `2^20`-byte proof", but the decoder's input is the word
   in the log, not the proof (F1-3).
3. **The sizing (paper estimates, F1 §3.3).** The node circuit is about `2^28.3` constraints and
   the word about `2^29` symbols. Quasi-linear decoding is about `2^38.7` field operations, about
   `2^43` RV64 steps; quadratic decoding is about `2^58`. ADV-M7 independently gives `2^46` for
   Berlekamp–Welch on a `2^23` word.
4. **Leaves are fine.** The witness goes in the clear and the 8-instruction parsing image extracts
   it. R1 does this (D-3).

**The decision (2026-10-20, from the user).**
- `E` is a computable Lean 4 function written in a small step-counting monad whose primitives are
  word-sized operations. Each primitive charges a step; there is no arbitrary-size `Nat`
  arithmetic hidden in one step.
- The certificate proves `steps(E, c, π, L) ≤ B(|input|)` for every input.
- Benchmarks of the honest extractor on generated proofs and logs are a sanity and liveness check,
  and they calibrate step costs. They are not the security bound.
- **Rationale.** A measured-only bound is gameable. A brute-force fallback branch reachable only
  on accepted-but-undecodable proofs is never exercised by honestly generated proofs, so fuzzing
  never finds it, and knowledge soundness collapses to soundness. This is also why `REPORT.md`
  §2.3, F1 §6.2 and #7 reject "measured extractor time" and "noncomputable `E`".
- This unblocks #7, since a decoder becomes ordinary Lean. CompPoly's decoders become usable as
  specifications and templates: Gao (`CompPoly.Univariate.ReedSolomon.GaoDecoder`, #7) and
  Guruswami–Sudan (`CompPoly.Bivariate.GuruswamiSudan.*`, noted by the user under Q1). They are not
  allowlisted today (§2.11 item 8) and would have to be re-expressed in the language with a
  refinement proof.
- The budget must be raised for decoding. REPORT §2.3 suggests `2^48 + 2^16·t` in RV64 steps;
  re-derive it in the new step units.
- Trusted cost: the step monad and its primitive list, about 60–100 lines (REPORT §2.3, "Lean-level
  cost model"; F1 §6.2, #7 options table).

**Requirements the implementation must meet.** These are not new decisions; they follow from
"each primitive charges a step, nothing hidden" and from F1 §6.2's "must exclude `Nat`-bignum and
list-length-in-one-step gaps (A3 C2)":
1. **Every computation must be charged.** If the monad's bind takes an arbitrary Lean
   continuation (`Word → M α`), the continuation can do unbounded uncharged work before it emits
   its next primitive, for example a brute-force search computed in pure Lean, and the step bound
   would mean nothing. The representation must make uncharged computation impossible by
   construction: a deep embedding (programs as syntax over words and bounded arrays, interpreted
   by a contract function that counts steps), or an equivalent the reviewer cannot get around.
   **The adversarial review must attack exactly this point.** The RISC-V image has this property
   for free; the replacement must keep it.
2. **Primitives are `O(1)` machine work.** Word arithmetic and logic on `UInt64`, comparisons,
   shifts, a bounded array read and write, reading word `i` of the input, writing an output word,
   a branch, and a loop. No `Nat`/`BitVec` bignum (`BitVec 64` compiles to `Nat`; §2.11 item 9), no
   `List.length` or `List.getD` in one step.
   - To decide: whether carry-less multiply is a primitive (the reference machine exposes it under
     V3-1; with it, `GF(2^64)` multiplication is a few steps);
   - and whether a BLAKE2s compression is a primitive with a stated cost (it would be for a Merkle
     rebuild).
3. **A program-size cap**, analogous to `imageCap = 2^20` bytes, so that the extractor cannot be a
   huge table.
4. **The input** can stay the normative tape `extractorInput c π L` (words), read through a
   primitive, with the output still denoting a witness through `decodeWit`. That keeps
   `Extractor.lean`'s codec, `outCap` and the leniency of V3-S1-A7/A22, and the size measure `t`
   stays the tape length. Alternatively `E` reads `(c, π, L)` directly with a defined size measure.
   Choose one and state it.
5. **The budget `B t`.** Re-derive it in the new units, for a quasi-linear RS decoder of the
   largest word a node extractor must decode (F1 §3.3), plus log indexing (`≤ 2^8` per word
   today). `2^48` still excludes `2^128` enumeration (#7). Show the derivation in the RESULT.
6. **Computability.** `E` (the program) is on the badge path: gate rule 4 lists `E` (§2.8), and
   the liveness check runs it.

**What changes in the core.**
- `Contract/Extractor.lean`: `ImageComputes` is replaced by the step-bounded statement, and
  `extractorBudget` is re-derived.
- `Contract/Machine.lean` (113 code lines at the pin) and the vendored RV64 (205 declarations,
  DESIGN-v3 §8 item 3, "serves the extractor only") leave the trusted base. O-16 becomes moot.
- `Contract/Certificate.lean`: `Submission.img`, the `computes` clause, the cap
  `S.img.byteSize ≤ imageCap`, `Declared.img` and `CertificateR.img` change.
- The renderer's `image` kind and the stub (§2.8).
- DESIGN-v3 §4.4, §6.3 step 8 (liveness: run the compiled `E` and check the step count, in place
  of the riscv-zkvm emulator), §6.6 (the extractor rows), §8 (items 2, 3, 8), §12 (O-15(2)
  reframed, O-16, O-21); `AGENTS.md` §4.
- Q1 in `DISCUSSION.md` is the user's record, so ask before the design text says it is superseded.
- Net trusted lines must be measured with `loc.py`. Removing `Machine.lean` may offset the new
  language.

**Controls (each kernel-checked).**
- Positive:
  - the library's witness-sending `E` (parse) in the new language, with `steps ≤ B`;
  - R1's parsing leaf extractor ported;
  - a log-indexing extractor (find an entry by answer) within the linear term;
  - a toy decoder (for example Berlekamp–Welch on a tiny code) within a stated bound.
- Negative:
  - a program that loops `k` times has `steps ≥ k`;
  - an extractor that enumerates `2^64` candidates has no certificate at `B`;
  - a certificate with fuel above `B` is rejected (the analogue of `fuel_over_budget_claim`).
- Meta, for the review: there is no way to express unbounded computation without steps
  (requirement 1).

**Acceptance.**
- The new statement is in the contract, with the controls above.
- S2a and R1 re-certify; the core library's `WitnessSending.computes` is ported.
- The trusted budget is ≤ 500.
- The liveness check of §6.3 step 8 is restated.
- A review verdict addresses requirement 1.

**Dependencies.** §2.1 (rebase on it). §2.8: gate rule 4 lists `E`, and the stub drops the image
literal. §2.3 (optional reuse for `T_V`). O-21 (the budget).

---

### 2.6 Completeness with a small error: drop `Complete ∀ H` (O-23; **user decision 2026-10-20**)

**Intuition.** Today the honest proof must be accepted for every oracle function, including
adversarial ones. That forbids:
- proof-of-work grinding, since an adversarial oracle defeats any bounded nonce search;
- rejection sampling of challenges;
- every `2^-170`-type exceptional case, such as an out-of-domain point landing in the domain.

The user decided to allow a small completeness error `δ` over a uniformly random oracle.

**Precise problem.** `Contract/Security.lean:74-76` at the pin (unchanged by the amendment):

```lean
def Complete (R) (P : Digest → Wit → OProg Proof) (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true
```

`OProg` is inductive, so no unbounded search exists, and an adversarial `H` defeats every bounded
one (#8 (2); ADV-m2). Sources:
- The design already promises a counted form: DESIGN-v3 §4.3 "`CompleteWithError` … `δ ≤ 2^-64`",
  §6.6 (the `δ` row), §6.7 ("Grinding / proof of work: allowed through the counted completeness
  form").
- The contract has none (V3-S1-A9).
- V3-S1-m10 asked for both rows to be marked "after O-23". That was **not applied** in DESIGN-v3
  or `AGENTS.md` (ADV-m2; #9 item 10).
- Honest designs pay for it. R1 needed design care in every round to meet `∀ H`: no division, no
  distinctness requirement, `snark_complete` holds even for a constant oracle (REPORT §2.4(2);
  BLUEPRINT-R1 §8).

**The decision (user, 2026-10-20).** Drop perfect completeness over every oracle and allow a small
error `δ`, with `δ ≤ completenessCap`, a contract constant. The user suggests `2^-128` or `2^-96`;
the design's `2^-64` (§4.3, §6.6) is superseded.

**Statement shape to propose** (to be written with `lean-spec-authoring`; a sketch, not compiled).
The probability is over a uniformly random oracle, lazily sampled, so that the queries of `P` and
`V` are consistent and **`P`'s queries are counted**:

```lean
/-- The probability that the program returns `false` when every query not yet in the log is
answered uniformly at random and recorded (a lazily sampled random oracle). -/
noncomputable def failProb : Log → OProg Bool → ℝ≥0
  | _, .ret b => if b then 0 else 1
  | L, .query q k => match L.find? (·.1 = q) with
    | some e => failProb L (k e.2)
    | none => (∑ a : Digest, failProb (L ++ [(q, a)]) (k a)) / 2 ^ 256
/-- Completeness with error `δ`: on every statement and witness in `R`, the honest prover's proof,
produced and then verified under the same uniformly random oracle, is rejected with probability at
most `δ`. -/
def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop :=
  ∀ c w, R c w → failProb [] ((P c w).bind fun π => V c π) ≤ δ
def completenessCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128   -- or ^ 96: the user's choice
```

- `OProg.bind` is not in the contract today (`Oracle.lean` has `ret`, `query`, `run`, `runLog`,
  `queries`). Add it, or state the sum over the composed tree directly.
- The sum uses the amendment's `noncomputable instance : Fintype Digest` (§2.1). Use the literal
  `2^256` for the same reason as there.
- `Library/PaperTheorem.lean` already has a lazily sampled oracle. Reuse its formulation, or prove
  the two agree, so that "uniform random `H` over the contract's `Digest`" is one notion in the
  repository.
- `Certificate.complete` becomes `CompleteWithError (Rel S.Vb) S.P S.V S.δ`. `Submission` gains a
  `δ` field. `Certificate.cap` gains `S.δ ≤ completenessCap`. `Declared`/`CertificateR` gain a
  declared `δ`, and the renderer and stub follow (§2.8).

**Why the cap is close to free.** A grinding prover with fuel for `T` attempts at difficulty `2^g`
fails with probability `(1 − 2^-g)^T ≈ e^{−T/2^g}`:
- `δ = 2^-128` needs `T ≈ 128·ln 2·2^g ≈ 89·2^g`;
- `δ = 2^-96` needs `T ≈ 96·ln 2·2^g ≈ 67·2^g`.

The expected prover work (`2^g`) is the same; only the worst-case fuel of the certified `P`
differs, by a constant factor. Recommendation: `2^-128`, which matches `errorCap`'s scale, unless a
design needs more. **The choice is the user's**; record both numbers.

**Controls.**
- Positive, embedding: `Complete R P V → CompleteWithError R P V 0`, so every existing entry ports
  (S2a, R1, the library's `WitnessSending.complete`).
- Positive, grinding, kernel-checkable exactly: a `V` that accepts iff the answer to
  `(c, nonce)` has its first bit `0`, with a `P` that tries 128 nonces. Then
  `failProb = 2^-128` exactly; it is certified at `completenessCap = 2^-128`.
- Negative:
  - the same with 127 nonces (`2^-127`) is rejected at the cap;
  - a `V` that accepts iff the first bit of `H(c)` is `0` (`δ = 1/2`) has no certificate;
  - reject-all still fails for every `δ < 1` (port `rejectAll_not_complete`, used in
    `Controls/Certificate.lean:75`).
- Port `ws_complete` (`Controls/Security.lean:58`) and `Backdoor.complete`
  (`Controls/Backdoor.lean:151`).

**Keep a deterministic check under the deployed oracle.**
- Under `∀ H`, it is a *theorem* that honest proofs verify under BLAKE2s, since BLAKE2s is one of
  the `H`. A probabilistic statement over random `H` says nothing about the one deployed `H`.
- A `V` could therefore reject every honest proof exactly when the oracle is BLAKE2s, and the
  certificate would still hold. This is a liveness analogue of O-25 (§2.2); flag it to the O-25
  track.
- The harness's concrete checks must stay, as the only guarantee: the root check, the sample
  checks, the smoke tree, and the liveness check of §6.3 step 8, which runs the Lean `P` under
  concrete BLAKE2s and requires `Vb` to accept.
- Say in DESIGN §5.4 that this is no longer implied by the certificate.

**Interaction with recursion.**
- `Rel`'s node clause demands children accepted by `Vb` under concrete BLAKE2s. The honest
  native prover can check its own proofs concretely and retry (for example extend the nonce
  search), so tree completeness is fine in practice.
- The runner treats a prover that fails to produce an accepted proof as a failed evaluation, as
  today. With `δ ≤ 2^-128` that is negligible. State this in §6.3, and say that the native prover
  is not bound by the Lean `P`'s fuel.
- The Lean `P`'s `T` bounds only the certified prover.

**Interaction with the KS amendment.** None found.
- `KS` and `KState` do not mention `P` or `Complete`.
- `git grep Complete` on `v3/ks-potential` finds no use in `Library/PaperTheorem.lean` or
  `Controls/Potential.lean`.
- The only uses are `Certificate.lean:64`, `Library/WitnessSending.lean:171,258`,
  `Controls/Security.lean:58,81`, `Controls/Certificate.lean:75` and `Controls/Backdoor.lean:151,159`.
  All are ports, not dependencies.

**Design text.**
- §4.3: the definition, and `δ` with the cap.
- §6.6: the `δ` row, with the new cap.
- §6.7: the grinding row becomes operative.
- §5.4: the deployed-oracle point above.
- §12: O-23 resolved.
- `AGENTS.md` §4, and the §6 caps table.
- V3-S1-m10's "mark after O-23" becomes moot once this lands.

**Acceptance.** The definition, cap and controls above are in the contract. S2a, R1 and the
library re-certify through the embedding. The grinding positive control is certified. The harness
keeps its concrete acceptance checks. The design text is patched.

**Dependencies.** §2.1 (the `Fintype Digest` instance and rebase). §2.8 (stub, renderer,
`Declared`). It is orthogonal to §2.5, but both touch `Certificate.lean`: land them in one stage,
or sequence them.

---

### 2.7 The second kernel (nanoda) has no stated budget (D-11; **not yet filed on #9**)

**Intuition.** The harness checks the certificate with two kernels, Lean's and nanoda. A lemma
that Lean's kernel checks in seconds made nanoda run out of memory, so a sound entry was rejected,
and the submitter had no way to find this out before intake.

**Evidence (measured).**
- **The whole entry.** The comparator printed "nanoda kernel rejected the solution … Lean default
  kernel accepts the solution … nanoda exited with 137", `TIME comparator 1797.01 s`
  (`logs/spartan-chain/infra/harness-final/harness-work/comparator.log`; V3-S2b-M1).
  - nanoda's RSS sampled every 30 s reached 53,456,308 KB
    (`logs/s2b-final-review-probes/nanoda-rss.log`).
  - nanoda alone on the 236 MB export (22,745 theorems, 7,978 definitions, 4.27 M expressions)
    grew about 2 GB per minute and was stopped by the OOM killer at **52.0 GB** after 23 min
    (`reports/submission-infra.md`, "Harness decisions applied", item 3;
    `logs/spartan-chain/infra/harness-final2/nanoda/nanoda-run.log`).
  - A second run inside a 50 G scope was killed at 51.3 GB (item 5 there).
  - The sources round differently ("52 GB": REPORT §2.7, PLAN D-11; "53.5 GB": V3-S2b-review
    M1); they are different runs and samplers.
- **Bisection** (`logs/spartan-chain/infra/harness-final2/nanoda/bisect/`: `suspects.log`,
  `spread-nanoda.log`, `compoly.log`; 4 GB cap and 300 s per module closure).
  - One private field lemma, `SpartanChain.F.spread_getLsbD`, proved by a **64-way
    `interval_cases j <;> simp`** over `BitVec` positions.
  - Its closure alone (3,441 declarations, 20.5 MB of export) took nanoda to **41.9 GB** before
    the kill (`reports/submission-infra.md`; `logs/field/nanoda.log` records "> 40 GB (killed)",
    exit 143, under a 40 G cap).
  - Every closure without it checks in ≤ 8 s.
  - CompPoly's `BF64` closures check in about 70 s and 2.3 GB (`cp-Impl` 74.73 s / 2,292,144 KB;
    `cp-Ext3` 69.95 s / 2,272,920 KB, `compoly.log`).
- **After the rewrite** (five mask-and-shift stage lemmas with `omega`, statement unchanged):
  - the lemma checks in **0.76 s / 32,668 KB (33 MB)** (`logs/field/nanoda.log`);
  - the whole solution checks under nanoda in **70 s, peak 2,412,072 KB (2.41 GB)**
    (`logs/spartan-chain/infra/harness-final3/nanoda-rss.log`), and `HARNESS: ACCEPT` followed
    (`harness-final3/`, `harness-final4/`).
  - The orchestrator also replaced `SoundnessPCS.x_pow_word`'s `decide +kernel` (V3-S2b-RESULT,
    fix pass; it passed nanoda in 21–25 s / 0.6 GB before).
- For comparison, S2a's comparator took 71 s and 0.98 GB with both kernels.
- A precedent: v0.3's nanoda was OOM-killed at 60 GB on a diverging declaration
  (`notes/E4-clean-riscv-tooling.md` §3).

**Gap in the rules.** DESIGN-v3 §6.6 caps the harness at 2 h and the build at 48 GB, but sets no
memory or time cap per kernel. Nothing tells a submitter that `interval_cases`- or `decide`-style
case splits over concrete words can be fatal for nanoda.

**Proposed change** (REPORT §2.7, §4 item 4):
1. State a nanoda budget per entry (memory and wall time) in `AGENTS.md` §6 and in the harness,
   measured on the reference machine, and enforce it with a cgroup and a timeout.
2. Ship the comparator and nanoda pins in the entry-side tooling. `tools.env` is absent at the pin
   (E4 §3); v2's has comparator `d03acab`, lean4export `076e8e5`, nanoda `3a24072` (#1 "Pins").
   Then a submitter can run a "nanoda budget" check before submission.
3. Count the organiser library's `BF64` closure (about 70 s, 2.3 GB) once, not per entry, if the
   harness design allows it.
4. **File this on #9** (not done; D-11 says it "goes to … core issue #9").

**Controls / acceptance.** S3's harness kills nanoda at the stated cap with a clear verdict. A
fixture entry with the old `spread_getLsbD` proof is rejected with "nanoda budget exceeded"; the
rewritten one is accepted. The budget appears in `AGENTS.md`. Trust cost: none.

**Decision needed.** The memory and time values, on which machine, and whether the pre-submission
check is organiser-provided (REPORT §6 Q4).

---

### 2.8 Interim harness fixes that must land in S3 (V3-S2b-M2; #9 item 4; S2a open questions)

**Intuition.** The core at the pin has no v3 harness: no stub, renderer, allowlist, manifest or
driver (E4 §3). To get `HARNESS: ACCEPT`, the entries ran organiser tooling written on scratch
branches. Two of the fixes are rule-level: without them a sound entry is rejected.

**What exists** (`rf-core-s2a`, verified with `git show --stat`; local only):

| commit | branch | content |
|---|---|---|
| `2a4588b` | `v3/s2-interim-harness` (on `15e4ae5`) | `RecursionFast/Challenge/V3.lean.in` (the v3 stub: rendered `Declared`, `submission` and `certified` as the only `sorry` placeholders), `scripts/render-challenge.py` (the nat, rat and image kinds), `scripts/harness-local.sh` (v2 order: render, manifest, source rule, comparator with both kernels, build binding, gate), `scripts/setup-scratch.sh`; 402 lines, no Lean source change |
| `2464e97` | `v3/ks-interim-harness` (on `05fde28`) | the same four files (`git diff 2a4588b 2464e97 -- scripts RecursionFast/Challenge` is empty) |
| `26c3b23` | same | the stub notes the amended contract |
| `9d5b26a` | same | `setup-scratch.sh` `ENTRY_TARGETS` |
| **`09668b5`** | same | `scripts/org-closure.sh`: allowlist roots = Mathlib, Contract, Library, Controls, plus `CompPoly.Fields.Binary.BF64{,.Basic,.Bytes,.Ext3,.Impl,.Reduce,.BaseCertificate}`; generated `scripts/import-allowlist.txt` (10,808 modules) and `scripts/olean-manifest.sha256` (34,392 entries); CompPoly pinned by hash, so its `@[csimp]` lemma (`CompPoly.Fields.Extension.Arithmetic`) is reported, not rejected |
| **`4a1a1ed`** | same | `scripts/Gate.lean` `badgeFields`: `(RecursionFast.Submission, [V, P, E, img])` in place of v2's `[P, cfg]`; header and docstring updated; fixtures in `logs/spartan-chain/infra/harness-final2/gate-fixtures/` (all computable: PASS; a noncomputable `V` or `E`: REJECT) |

**The two rule-level defects they fix** (`logs/s2b-final-review-probes/gate.log`):
- **CompPoly is not pinned or allowlisted.** "0 pinned by hash" and "REJECT module
  CompPoly.Fields.Extension.Arithmetic: registers @[csimp] lemmas" (rule 3). Rule 6 would also
  reject the direct imports of `BF64.{Bytes,Ext3}`, which DESIGN-v3 §7.4 (V3-9) and `AGENTS.md`
  §10 allow. **Not filed** on any issue: #9 item 8 covers ArkLib, not this.
- **Gate rule 4 lists v2's fields** (#9 item 4; ADV-m5). A v3 `submission` that is
  noncomputable as a whole (every entry with a real-valued `ε`) fails on "no field cfg" and `V`,
  `E`, `img` are never checked. S2a passed only because `ε := 0` made it computable.

**Other interim limits S3 must remove** (from the tools' headers and S2a's open questions):
- `harness-local.sh` generates the manifest and allowlist from the organiser tree itself, so
  stage 0 detects changes during a run, not a mismatch with a reference build (V3-S2a-m8;
  `harness-local.sh` header).
- The allowlist includes `RecursionFast.Controls`, so "entries import no Controls" is not
  enforced (S2a OQ 7).
- `olean-manifest.py`'s `PINNED_PKGS` still lists Clean (E4 §3).
- The stub and claim schema: an `ℝ≥0` rational makes `declared` noncomputable, and the declared
  fuel shape is open (S2a OQ 4).
- The library's v3 modules (`Library.{Oracle,Security,WitnessSending}`) are not in any committed
  allowlist (S2b-m6).
- The `Fintype (Vector UInt8 n)` instances in CompPoly `Data/Bytes/Bias.lean`, VCVio and ArkLib
  are a diamond with the contract's instance. It is harmless (a subsingleton), but record it at
  allowlist regeneration (V3-S2-KS-m4).

**Proposed change.** Stage S3 (and the S2 core half, `BASELINE-TASK.md` §2.2) adopts or replaces
these, rebased on the merged §2.1. Changes:
- `badgeFields` = `V`, `P`, `E`, `img`, or `E`'s program after §2.5;
- the CompPoly `BF64`/`Ext3` closure allowlisted and pinned;
- a reference organiser build for the manifest;
- Controls dropped from the closure if the convention is meant to bind;
- the stub and renderer with `δ` (§2.6) and without the image literal if §2.5 lands;
- the nanoda budget (§2.7);
- CI.

**Acceptance.** On the core's `main`, the harness prints `HARNESS: ACCEPT` for S2a and for R1
with no scratch branch. The fixtures above pass and fail as stated. A v3 submission with a
noncomputable `ε` and computable `V`, `P`, `E` passes rule 4.

**Dependencies.** §2.1. §2.5 and §2.6 change the stub and rule 4's list; sequence them or update
the tooling in the same stage.

---

### 2.9 Honest recursion under the caps (#8 items 1, 3, 4; item 2 is §2.6)

#### 2.9a `proofCap`, BLAKE2s-only hashing, R1CS and unique decoding (#8 (1); F1-4)

**Intuition.** Under unique decoding a provable query phase gains at most one bit per query. Each
Merkle level in a recursion circuit is a BLAKE2s gadget of about `2^14` R1CS constraints. Proofs
of the node circuit are then too big for `proofCap = 1 MiB` unless the PCS is WHIR-class.

**Evidence.**
- Paper sizing from WHIR Table 5 (UD column) and ZCF24 (F1 §5.2), for the node circuit of about
  `2^28.3` constraints: WHIR-class 621–770 KiB ("yes, barely"); FRI about 1 MiB (no); Basefold
  7.95 MiB (no); Ligero/Brakedown `≥ 25 MiB` (no).
- Measured: the BLAKE2s circuit is leanerVM's, 14,720 gates + 256 output rows per compression
  (REPORT §2.4; `rows_digest_matches_leanervm`). R1's Ligero leaf at `n = 2^14` is 1,464,107 B,
  above `proofCap` (`reports/rust-prover.md`; `logs/spartan-chain/rust/`).
- With a plonkish/AIR BLAKE2s (`2^10`–`2^11` cells) the node circuit is about `2^24` and every
  row but Ligero fits.

**Options (user decision, REPORT §4 item 8, §6 Q6):**
1. document that recursion closes only with WHIR-class sizes (§6.6);
2. raise `proofCap` for node proofs;
3. an arithmetisation-friendly hash entry in a menu (O-14; a second trusted hash specification);
4. admit a named proximity-gap hypothesis (not under V3-5; the comparator must track it).

Options 3 and 4 change the trusted base. This interacts with O-18 and §2.14.

#### 2.9b Preprocessing: an indexer (#8 (3); ADV-M6)

**Intuition.** A preprocessing SNARK hard-codes a verification key computed with the hash.
Under a random `H` that key has no opening, so `Complete ∀H` fails. Recomputing it inside `V`
costs about `2^20` queries, above `qV ≤ 2^16`.

**Proposed change.**
- Add an indexer to the submission: `I : OProg Key` and `V : Key → Digest → Proof → OProg Bool`.
- `KS` counts `I`'s queries in the log, as made honestly before the adversary.
- `Complete` uses `I.run H` (after §2.6, run `I` inside the `failProb` game).
- `Vb` uses `I.run blake2sOracle`, computed once at badge build and untimed.
- `qV` excludes `I`'s queries.

This costs a handful of trusted lines. It also removes the only legitimate reason for `V` to
compare an oracle answer with a hard-coded 32-byte constant, which sharpens the O-25 review
(§2.2). Controls: a Spartan-with-SPARK-shaped toy that needs the key is certified with the
indexer; without it, it is not. This depends on §2.1 and §2.6, and on the O-25 decision (the
parametric-`V` shape, if adopted, must accommodate `Key`).

#### 2.9c Accumulation (#8 (4); ADV-M8)

The node clause `Vb c₁ π₁ = true` demands full verification of each child, so ARC/WARP-style
accumulation is not expressible. There are three obstacles:
- the accumulator witness is above `proofCap`;
- a decider outside the circuit gives no transfer from random-`H` to concrete BLAKE2s;
- the extractor has no source for the child proof.

Decision: correct DESIGN-v3 §1, which names accumulation as a reason for v3 (full recursion only),
or change the node clause to an accumulation-shaped relation, which is a design change.

---

### 2.10 Library: canaries and quadratic decoding (#10)

**Intuition.**
- The organiser's own witness-sending verifier accepts a leaf proof with a byte appended or
  removed, so it fails the benchmark's canaries.
- The contract's byte-packing functions, run as code, are quadratic. Any verifier that decodes
  through them takes minutes on a 1 MiB proof.

**Evidence.**
- Kernel-checked (`submissions/baseline/BaselineV3Controls.lean`; `logs/V3-S2/check/axioms.log`):
  `lib_leaf_appended`, `lib_leaf_truncated`, `lib_check_appended`, `lib_check_truncated`.
- The leaf branch of `Library/WitnessSending.check` lacks `encode … = π` (`:64-72`), and
  `decodeWit` ignores trailing words.
- Measured: a strict `check` over the library's codec took **563.26 s** (128 MB) to reject a random
  `2^20`-byte proof (`logs/V3-S2/dos-unfiltered/run.log`). With linear twins: ≤ 0.25 s for random
  proofs, ≤ 1.19 s for adversarial shapes (`logs/V3-S2/check/smoke.log`).

**Proposed change** (library only; #10):
1. A strict leaf branch, with `check_sound` and `complete` adapted, and controls for the four
   canaries (S2a's `leaf_appended_rejected`, `leaf_truncated_rejected`, `node_appended_rejected`,
   `node_truncated_rejected`).
2. Linear twins in `Library/Words.lean`: `packFast`, `bytesAtF`, `decodeWitF`, `decodeF`,
   `encodeF`, with `*_eq` theorems, from S2a's `BaselineV3.lean` (about 70 code lines); the
   library's `check` runs them.
3. Optionally, a header remark in `Extractor.lean` that `packBytes`/`bytesAt` are specifications.

If §2.5 removes the tape, item 3 is moot but items 1–2 stand. Trust cost: none.

**Acceptance.** The library verifier rejects the four canaries (kernel); a random 1 MiB proof is
rejected within `verify_s` (measured); S2a can drop its own `check` (S2a OQ 1).

---

### 2.11 Minor rules and hygiene (#9), item by item

Source: #9 (ADV-m1 … m7; F1 §7.3). Status today: open on the core.
1. **Completeness through a fallback branch is vacuous, and liveness tests only the fallback
   (ADV-m1).** With `V = SNARK ∨ witness-sending` and `P` the witness-sending prover, nothing about
   the scored SNARK path is proved complete. The liveness check (§6.3 step 8) then runs only `P`
   with an empty log.
   - *Fix:* run liveness on the **native prover's** proofs, with a query log the native prover
     must emit. The harness checks the log's hashes and that it contains `V`'s queries, then runs
     the extractor (an image today, the §2.5 program later). The output is decidable: `Rel` for a
     leaf, `Vb` on the extracted children for a node.
   - This is the one minor item with an exploit flavour. It interacts with §2.5 and §2.6.
2. **Repeated runs reuse instances (ADV-m3).** §6.3 step 9 repeats steps 3–6 "on the same
   instances" without a fresh `DIR`, so a prover can cache. *Fix:* v2's rule, a fresh step
   directory that is the only writable path, for every repetition (`docs/core/harness-README.md:295-300`).
3. **`AGENTS.md` misstated the contract (ADV-m4).** The seven rows of #9's table: `Digest`, the
   chain tag, `n ≤ chainCap`, `fuel`'s type, the `2^24` log bound, where `img` is bound, the
   separation claim. **Fixed in this repository** (commit `5cb89d8`, per REPORT §2.8; `AGENTS.md`
   §15). Still to fix in the core's text: DESIGN-v3 §2.1 (`Fin 32 → UInt8`), and §6.5 / §6.7 (see
   §2.3, §2.4).
4. **Gate rule 4 lists v2 fields (ADV-m5).** See §2.8 (fixed locally in `4a1a1ed`).
5. **The trust statement should name core `extern`s (ADV-m6).** These are `Task.spawn`/`Task.get`
   (kernel-transparent) and the `Array`/`ByteArray` primitives; the badge `verify` may be
   multi-threaded. *Fix:* name them in DESIGN §8 item 6, or restrict them on the badge path (with
   §2.3).
6. **Restate the paper theorem's domain (ADV-m7).** After `logCap`, the theorem holds for
   `Q + qV ≤ min(logCap, ≈2^57)`; the second bound comes from the `2^60`-word tape at ≥ 5 words
   per entry. §4.5 and `AGENTS.md` §5 quote `2^64` without the domain. The amended header now
   says "Nothing is claimed for `Q + qV > logCap`". Re-check the tape bound after §2.5.
7. **No `Fintype Digest` at the pin.** `#synth Fintype (Vector UInt8 32)` fails with Mathlib
   v4.34.1 (`logs/issue-probes/FintypeDigest.log`). Supplied by the amendment (§2.1).
8. **ArkLib is not allowlisted.** Entries must re-prove (R1 re-proved AHIV22's lemma), copy a
   Mathlib-only closure, or wait for S4. *Ask:* state the policy in DESIGN §9 and `AGENTS.md` §10.
   The measured closures (E2 §1) show that only CompPoly's modules are cheap: `Multilinear.Basic`
   is 3 modules, while ArkLib's AHIV22 lemma is a 102-module, 24.7 k-line closure (REPORT §3.5).
   After §2.5, the CompPoly RS decoders become relevant.
9. **Compiled field speed decides `T_V` (O-9 reframed).** Measured, compiled CompPoly
   (`logs/probes/e2/bfbench.log`): `BF64` mul+add 29.7 µs, `Ext3` mul+add 415 µs, `BF64` inverse
   1.72 ms. Rust GF(2^64) is 22 ns (`logs/probes/fieldbench.log`). The cause is that `BitVec`
   compiles to `Nat` bignums.
   - R1's word-level field, proved equal to CompPoly's: `F` mul 87 ns, `EF` mul 535 ns
     (`logs/field/bench-20261019-185727.log`; `ringEquivBF64`, `ringEquivExt3`).
   - *Fix (library):* host that field (§2.15).
10. **Perfect completeness ∀H and the counted form (ADV-m2, V3-S1-m10).** Superseded by §2.6.

---

### 2.12 The caterpillar DoS: valid unbalanced proofs (V3-S2a-M2, V3-S2b-m1)

**Intuition.** A witness-sending node check re-parses its whole subtree at every level. A valid
but deeply unbalanced proof on a statement the prover chose takes minutes to verify.

**Evidence (measured).**
- R1: valid caterpillar proofs take 6.8 s at depth 1,000, 64.0 s at 3,000 and **275.0 s at depth
  6,000 (1,008,080 B)**, about 80 ns per byte re-processed
  (`logs/s2b-final-review-probes/caterpillar/caterpillar.log`).
- S2a: 212.64 s at depth 2,000 (`logs/V3-S2/review/caterpillar.log`).

**Is it a rule matter?** Partly.
- The benchmark is unaffected, because the runner's digests force depth `r`.
- `verify_s = 60 s` applies to "one `Vb` run (root, sample, DoS)" (§6.6), but the DoS column runs
  random proofs on the root digest (§6.3 step 10). An adversarially shaped valid proof on a
  prover-chosen statement is in no harness check.
- The organiser's library `WitnessSending.check` has the same per-level structure (its node branch
  re-encodes, `:64-72`), so every entry that reuses it inherits this.

**Decision.** Is it acceptable for unranked entries (REPORT §6 Q10)? Should the DoS column add
valid adversarial shapes? Should the library get an offset-recursive node check (parse children by
offsets, check canonical lengths and padding on the bytes, never re-encode; V3-S2b-m1's sketch)?

---

### 2.13 Housekeeping of the amendment and the design text

- **The ledger gap for `05fde28`** (§2.1). Not recorded in `V3-S2-KS-RESULT.md` (whose verbatim
  blocks show a computable instance) or in `DESIGN-AMENDMENTS.md`.
- **V3-S2-KS-m1: no control that the guard is needed for a potential.** `V31` (equal answers on
  31 bytes) was proposed and not built. The fix pass records that for `Vcol` a potential without
  the guard is borderline feasible at exactly `2^-128`. Build it in S4, or accept F1 §4.1 (paper)
  (REPORT §6 Q11).
- **V3-S2-KS-m2:** done in the core (literal, `@[simp]`); the `AGENTS.md` note is pending in this
  repository (§2.1 step 5).
- **V3-S2-KS-m3:** kept and annotated (`final_unguarded`, `step_unstopped`); no action.
- **V3-S2-KS-m4:** the allowlist note (§2.8).
- **V3-S2-KS-m5:** the design text (§2.1 step 3).
- **V3-S2-KS-m6:** controls added; no action.
- **V3-S1-m11** (optional): restrict `final` to `π.size ≤ proofCap`. Not required; listed for
  completeness.
- **REPORT §4 counts.** The prompt for this handoff speaks of "ten recommended rule changes";
  REPORT §4 lists 11 numbered items (§3.1 below maps all 11). `PLAN.md` has no D-7 (it jumps from
  D-6 to D-8).

---

### 2.14 Proof size: an open design direction (user decision 3, 2026-10-20; not a rule change yet)

**Facts.** R1's Ligero leaf is √-size: 1,464,107 B at `n = 2^14` (measured,
`reports/rust-prover.md`). The byte layout (BLUEPRINT-R1 §7, `leafSize`, at `k = 2^14`,
`m = 256`, `ℓ_N = 17`):

| part | bytes | share |
|---|---:|---:|
| the two combined rows `ū`, `v` (`48k`) | 786,432 | about 54 % |
| the 260 opened columns (`260·8m`) | 532,480 | about 36 % |
| their Merkle paths (`260·31·ℓ_N`) | 137,020 | about 9 % |

(The shares are computed from the blueprint formula; the total is the measured size.)

**Direction (user).**
- An R1′ with WHIR/Ligerito-style folding in the unique-decoding regime, using BCHKS25's
  half-distance mutual correlated agreement in place of AHIV22's `d/3`, is the route under
  `proofCap`.
- The Johnson regime comes later.
- Grinding needs O-23's counted completeness (§2.6).

**Rule-side asks from this** (not yet decisions):
- `proofCap` versus node proofs (§2.9a);
- grinding through `CompleteWithError` (§2.6);
- admissibility of proximity-gap results under V3-5: proved theorems (BCHKS25-type, formalised
  by the entry or the library) are admissible as theorems; named conjectures are not (§2.9a
  option 4).

---

### 2.15 The organiser library (REPORT §4 item 2)

The protocol-independent layers of R1 (16,766 code lines in total, `reports/measurements.md`)
could be upstreamed to `Library/`. Trust cost: none (untrusted, kernel-checked). The allowlist
gains a Mathlib+CompPoly closure. About 10,500 of the 16,766 lines are in these layers (REPORT
§3.1, §4 item 2):
- the word-level `BF64`/`Ext3` with its CompPoly ring isomorphism (1,031 lines; this makes `T_V`
  reachable at all);
- the BLAKE2s R1CS gadget against the contract's hash (4,622 lines including the leanerVM copy,
  Apache-2.0 provenance);
- the Merkle/transcript-on-the-log lemmas (993);
- the generic potential with `muG_step` and `extCount_split` (part of the 2,250 lines of potential
  and log forest);
- the AHIV22 proximity lemma (696 with RS);
- the MLE/sumcheck counting lemmas (936);
- the linear codec twins (§2.10).

This is S4 work. Decision: adopt it as a core stage (REPORT §6 Q8). It depends on §2.1, and on
§2.5 for any extractor helpers.

---

### 2.16 Roadmap #1 is stale

Issue #1 still shows S1 as "in review" (PR #2), with links to the branch `v3/s1-contract`, although
`main` is at `15e4ae5` after PRs #2 and #3. Every box is unticked:
- S1–S7;
- O-6, O-7, O-8, O-9, O-12, O-14, O-15, O-16, O-18, O-19, O-20, O-21, O-22, O-23, O-24, O-25;
- the six "carried over" items;
- the seven intake items.

The body should be edited (it changes "by an edit of this body, never by a comment"):
- tick S1;
- add #5 … #11 against the items they touch: S2 core half and S3 ← §2.8; O-21 ← §2.1, §2.5;
  O-23 ← §2.6; O-25 ← §2.2; O-18 ← §2.3; O-15(2), O-16 ← §2.5; O-9 ← §2.11 item 9;
  O-14 ← §2.9a;
- note PR #11.

Edit only with the user's permission (it is a GitHub write).

---

## 3. Cross-references

### 3.1 REPORT §4 recommendations → sections here

| REPORT §4 | recommendation | here |
|---|---|---|
| 1 | potential `KS`, `logCap = 2^96` | §2.1 |
| 2 | organiser library of verified gadgets | §2.15 |
| 3 | node extraction rule; raise `B` | §2.5 (decided: Lean step-counted `E`) |
| 4 | per-kernel harness budgets, pre-submission nanoda check | §2.7 |
| 5 | succinctness measurement; fresh directories | §2.3; §2.11 item 2 |
| 6 | recursion incentive | §2.4 |
| 7 | allowlist and gate policy (`org-closure.sh`, rule 4, ArkLib/CompPoly policy) | §2.8; §2.11 item 8 |
| 8 | `proofCap` and the hash menu | §2.9a; §2.14 |
| 9 | `T_V` calibration after the shape and rule are fixed | §2.3 |
| 10 | counted completeness (O-23) and an indexer | §2.6 (decided); §2.9b |
| 11 | library fixes (#10); trust statement naming core `extern`s | §2.10; §2.11 item 5 |

### 3.2 REPORT §6 open questions → sections here

| REPORT §6 | question | status | here |
|---|---|---|---|
| Q1 | push and merge the amendment; move the pin; re-certify S2a | pushed, PR #11 open; merge and pin move pending | §2.1 |
| Q2 | `logCap` `2^96` or `2^58` | open | §2.1 step 4 |
| Q3 | extraction rule for nodes | **decided 2026-10-20** | §2.5 |
| Q4 | nanoda budget | open | §2.7 |
| Q5 | R1's acceptance run (smoke tree, unranked) or a hashing node | open (an entry question) | §2.9a |
| Q6 | `proofCap` / hash menu / proximity hypothesis | open | §2.9a, §2.14 |
| Q7 | succinctness measurement; rank column R | open | §2.3, §2.4 |
| Q8 | organiser library as S4; library fixes; interim harness in S3 | open | §2.15, §2.10, §2.8 |
| Q9 | O-25: semantic rule, intake review, indexer | **must be closed (decided)**; how: pending | §2.2, §2.9b |
| Q10 | the caterpillar DoS | open | §2.12 |
| Q11 | S2a open items; the `Fintype` note; `V31` | open | §2.13, §2.8, §2.10 |

### 3.3 Roadmap #1 open items touched by this work

S2 (core half: allowlist, manifest, v3 stub, `BASELINE-TASK.md` §2.2) and S3 ← §2.7, §2.8, §2.3.
S4 ← §2.15, §2.13 (`V31`). S5 ← every design-text patch. S7 ← §2.2 (mandatory intake review is a
candidate). O-9 ← §2.11 item 9. O-12 (unchanged). O-14 ← §2.9a. O-15(2) and O-16 ← §2.5.
O-18 ← §2.3. O-21 ← §2.1, §2.5. O-22 ← §2.11 item 8. O-23 ← §2.6. O-25 ← §2.2. O-6, O-7,
O-8, O-19, O-20, O-24: not touched by these findings.

---

## 4. Suggested order of work (dependencies only)

1. **§2.1: merge PR #11** (after the ledger note for `05fde28` and a PR description, with the
   user's permission). Then move the submissions pin, re-certify S2a, and update `AGENTS.md`. Every
   later contract change rebases on it.
2. **The user's pending choices**, which gate the contract stage of step 3:
   - `completenessCap` (`2^-128` recommended);
   - the extractor budget value in step units;
   - `logCap` (`2^96` or `2^58`).

   The O-25 decision runs in its own track and gates nothing below, except §2.9b's interface shape.
3. **One contract stage for §2.6 and §2.5**, or two in sequence. Both touch `Certificate.lean`,
   `Declared` and `CertificateR`:
   - `CompleteWithError` with its controls;
   - the step-counted extractor language, the re-derived `B`, `Machine.lean`/Rv64 out of the
     trusted base, and the ported controls (S2a, `WitnessSending`, R1's parsing extractor).

   The stage protocol applies, with the review specifically attacking §2.5 requirement 1.
4. **§2.8 with §2.7 (S3 harness and the S2 core half):** rebase or replace the interim tooling on
   the result of step 3. That covers the stub with `δ` and without the image literal, the renderer,
   rule 4's fields, the CompPoly closure pinned, a reference organiser build for the manifest, and
   the nanoda cap with fixtures; then CI, then `HARNESS: ACCEPT` for S2a and R1 on `main`. File
   D-11 on #9 when the user allows GitHub writes.
5. **§2.3 and §2.4** (measuring rule, calibration, recursion incentive): harness and design text.
   They need the reference machine (O-6) for the numbers, not for the rule.
6. **§2.10, §2.11 items 1, 2, 5, 6, 8, §2.12, §2.15** (library, harness and text): independent
   of each other once step 1 is done. Item 1 (liveness on the native prover's log) needs step 3's
   extractor form.
7. **§2.9b (indexer):** after step 3, and after the O-25 decision fixes `V`'s type.
8. **§2.9a, §2.9c, §2.14:** after the user's decisions; they change the design (and possibly the
   trusted base, for a hash menu or a named hypothesis).
9. **§2.16 and the design-text sync:** with each merge, not at the end.

---

## 5. What NOT to do

- **Do not move the submissions pin to a commit that is not on the core's `main`.** `05fde28` is
  now on the remote as PR #11's branch, but it is unmerged. Pin the merge commit, in its own
  commit, before any entry is certified against it. Never pin a local-only commit (the
  `rf-core-s2a` branches are local only).
- **Do not weaken a statement to make an entry pass,** and do not change a statement inside a
  proof. A fix that relaxes the contract (the potential, `CompleteWithError`, the extractor
  language) is a contract stage with controls showing what is still excluded.
- **No measured-only extractor bounds**, and no noncomputable `E`: a measured bound is gameable by
  an unreachable brute-force branch (§2.5). The step count is the proved bound; benchmarks only
  calibrate it.
- **No step monad in which computation can escape the count** (uncharged continuations, bignum
  `Nat`, one-step list traversals).
- **Do not design or implement the O-25 fix from §2.2.** Wait for the design track
  (`notes/F2-o25-*.md`) and the user's decision. Do not adopt the §6.7 syntactic rule or the
  closure test as a defence: the literal trigger evades it (kernel-checked).
- **Do not drop the concrete acceptance checks** (root, samples, smoke, liveness under BLAKE2s)
  when `Complete ∀H` goes: they become the only guarantee that honest proofs verify under the
  deployed oracle.
- **Do not make `Fintype Digest` computable**, and do not mark it irreducible (an attribute in the
  trusted base; the KS review declined it). Keep the literal `2^256` in trusted statements.
- **Do not edit, build in or commit to** `/home/devops/Verified-zkEVM/recursion.fast` or
  `/home/devops/CambridgePQ/recursion.fast`. Do not run `lake update` or `lake exe cache get`
  against the shared package tree.
- **Do not push, open PRs, comment on issues or edit #1** without the user's explicit permission.
- **Do not copy contract, harness or library files into the submissions repository,** and do not
  shadow them there. A change to any of them is a core PR.
- **Do not edit the design workspace master.** Record agreed design changes in the core's
  `docs/DESIGN-AMENDMENTS.md`, and ask the user to sync the master.
- **No time estimates** in RESULTs or issues; quote measured durations with their logs.
- **Do not trust stale status lines.** `REPORT.md`, `PLAN.md`, `V3-S2b-RESULT.md` and the #5
  comment say the branch was not pushed (§0.1). Check `git ls-remote` and `gh pr list` first.

---

## 6. What could not be verified here

- **The O-25 design track.** No `docs/snark-baseline/notes/F2-o25-*.md` existed at writing time;
  §2.2 summarises only #4 and its comment.
- **The proposed Lean in §2.6 (`failProb`, `CompleteWithError`) is a sketch, not compiled.** The
  same holds for every requirement of §2.5. The controls named there are proposals.
- **Who pushed `v3/ks-potential` and opened PR #11.** The reflog of `rf-core-ks` shows a push on
  2026-10-20 at 09:07:59 UTC, and GitHub shows the PR authored by `scaraven` at 09:09:28Z. Which
  session or person did it is not recorded locally.
- **Paper estimates stay estimates:** the node-circuit size, the decoder step counts, the WHIR/FRI/
  Basefold sizes, the `2^48` budget, and the 65 ms best-linear-verifier figure. No measurement
  backs them.
- **The measured times come from a QEMU 32-vCPU VM without `pclmulqdq`/`gfni`,** not the
  reference machine (O-6). Every `T_V` margin must be re-measured there.
- **The sampled nanoda peak** differs between sources (52.0 GB, 51.3 GB, 53.5 GB; §2.7); they
  are different runs and samplers. The "0.76 s / 33 MB" and "70 s / 2.41 GB" figures were checked
  against `logs/field/nanoda.log` and `harness-final3/nanoda-rss.log`.
- (Checked, not a gap: the two S2a root-check triples are the first run,
  `logs/V3-S2/calibration-r8-n16384.log`, 20.871/21.234/21.164 s, and the fix-pass re-run,
  `logs/V3-S2/fix/calibration-r8-n16384.log`, 20.693/21.111/20.926 s.)
- **The live state of the issues** was compared with the snapshots on 2026-10-20 (same comment
  counts and update times); later changes are not covered.
