# Review of the v3 ideation design documents (core PR `v3/ideation-design-docs`)

## 0. Scope, method and summary

**Reviewed** (worktree `/home/devops/Verified-zkEVM/recursion.fast-design`, branch
`v3/ideation-design-docs` on `059812f`, uncommitted, as of 2026-10-22):

- `docs/README.md` (50 lines);
- the design, `docs/v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md`
  (1,596 lines, cited **Design §n**);
- the lessons, `docs/v3-lessons-from-building-a-witness-sending-entry-and-an-honest-Spartan-Ligero-SNARK-entry.md`
  (656 lines, **Lessons §n**);
- the open problem, `docs/v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md`
  (910 lines, **O-25 §n**);
- the skeleton: `README.md`, `CLAUDE.md`, `RecursionFast.lean`, `lakefile.toml`, `.gitignore`,
  `docs/reference/` (one edited paragraph in `neighbouring-competitions.md`), checked against
  `git status` and `ls`.

**Sources read** (all read-only):

- the archived core `recursion.fast-rules` at `6202402` (= `origin/v3/contract-archive`):
  `docs/DESIGN-v3.md`, `docs/DESIGN-AMENDMENTS.md` (every entry), `docs/stages/*`,
  `docs/reviews/*`, `RecursionFast/Contract/*.lean` in full, the control and library theorem names,
  `scripts/loc.py` re-run on the contract;
- the submissions repository: `docs/design/DISCUSSION.md`, `docs/snark-baseline/` (REPORT, PLAN,
  CORE-HANDOFF, `notes/ADV1`, `notes/E2`, `notes/E3`, `notes/F2`, `reports/measurements.md`,
  `reports/rust-prover.md`), `docs/reviews/*`, `docs/stages/*`, and the logs under `logs/`;
- the S1 logs in `/home/devops/Verified-zkEVM/recursion.fast/logs/V3-S1/`, the S2R logs in
  `recursion.fast-rules/logs/`, the scratch clones `rf-core-s2a` and `rf-core-sc/scratch/`;
- the issue snapshots `issue-{1,4,5,6,7,8,9,10}.json` (bodies and comments);
- the user's messages of 2026-10-20 and 2026-10-22 as logged in the orchestrator's job timeline
  (`~/.claude/jobs/e2d4aee0/timeline.jsonl`);
- **outside the given source list**, because it bears directly on O-25 and is on the core's
  remote: the branch `origin/explore/relativized-nark` (head `043bcb3`) and the untracked draft
  `docs/DESIGN-relativized-recursion.md` in the worktree `recursion.fast-reldesign` (branch
  `docs/relativized-recursion-design`).

Nothing was built and nothing was edited except this file. The method follows the
`adversarial-review` skill, adapted to documents: pass A (do the statements say what the sources
support, and nothing stronger), pass B (fidelity: numbers, names, definitions, commits and logs
checked against the sources independently of how the documents phrase them), pass C (hygiene:
links, commands, the tree, readability).

**Summary.** The documents are, in bulk, accurate and unusually well sourced: 47 concrete
claims were checked (§4), 35 match their sources exactly, and the trusted definitions quoted in
Design §4–§6 match the archived Lean text line for line. The ledger index (§12) is complete. The
problems are of four kinds:

1. **A whole O-25 exploration is missing** (DOC-M1): the relativized-NARK exploration on
   `origin/explore/relativized-nark`, which starts from the user's own idea and recommends an
   attested-oracle closure of O-25. Its absence makes three statements of the record false
   ("none is on record", N1–N5 "not proposed anywhere", "every reviewed direction fails C11").
2. **Strength statements are stronger than the evidence** (DOC-M2, DOC-M3): the "only invariant"
   and "in no weaker form" claims about O-25, several "kernel" labels on paper arguments and on
   definitions or `#eval`s, A9's justification, and the second wall ("no recursive entry fits"),
   which contradicts the documents' own WHIR estimate.
3. **The user's decisions are not all recorded as the user made them** (DOC-M4): T and review-only
   ranking are recorded as rejected by the user, which the user did not say; the 2026-10-19
   decisions (a)–(d) were the orchestrator's; one rationale is invented.
4. **Record gaps** (DOC-M5, DOC-M6): four of the fifteen S2R open questions are not carried
   over, and the evidence for the decisive kernel claims (the O-25 probes, the counting-form
   probes, the interim harness that produced both `HARNESS: ACCEPT` verdicts) is local to the VM
   while Lessons §9 says it is committed.

Six majors and twenty-seven minors. **Verdict (§8): changes required before the PR.**

## 1. Major findings

### DOC-M1. The relativized-NARK exploration of O-25 is missing, and three statements of the record are false without it

**Where.** All three documents and `docs/README.md`. In particular:

- O-25 §0 (line 51): "a mechanism that closes the mechanism without narrowing the design space,
  without a human review surface, and without manual intervention. **None is on record.**"
- O-25 §10.2 (line 818): "Whether any mechanism meets the three criteria of §11. **Nothing on
  record does.**"
- Design §17 (line 1500) and §17.2 (lines 1520–1521): N1–N5 "were not proposed anywhere in the v3
  record. They are listed because they aim at C11 directly, **which every reviewed direction
  fails**".
- O-25 §1.4 (line 127), Design §6.7 and §13.2: "a secret-keyed oracle is impossible because the
  recursion evaluates the oracle", stated without qualification.
- `docs/README.md` "Where the code went" lists every branch and tag except this one.

**Source.** The core's remote has the branch `origin/explore/relativized-nark` (head `043bcb3`,
commits of 2026-10-20 to 2026-10-22, 49 files, 11,696 lines). It contains:

- `docs/explore/BRIEF.md`, which quotes **the user's own idea verbatim**: a verifier
  knowledge-sound for a *relativized* recursion relation (the node clause accepts the children
  "with the same oracle" as the game, instead of under BLAKE2s);
- `docs/explore/REPORT.md`, 12 notes (T1 impossibility, W1 workarounds, W2 attested oracle,
  A1–A3 attacks, C1 cost, L1 literature, P1–P4 Lean probes) and 21 Lean probe modules under
  `RecursionFast/Explore/`;
- an adversarial review with a fix pass, `docs/reviews/EXPLORE-report-review.md` (M1–M6).

Its conclusion bears on every one of the statements above. Relativization removes the premise
"the recursion evaluates the oracle", because nobody arithmetises the oracle. The oracle can
therefore be a secret harness service, and O-25 closes **by the deployment**. The relation alone
does not close it: the backdoor stays certified, which is kernel-checked. The cost in the pure ROM
is that parents must re-ask their children's queries, and there "recursion never beats
concatenation". The workaround is **D4, the attested oracle**: the harness attests the answers a
child used, and the report claims that O-25 closes by construction and that whole-tree composition
becomes a theorem. Variants are W5 (a channel split, with an extractability heuristic) and D4+
(an oracle-chain leaf, for #6 (a)). A compiled proposal, `docs/DESIGN-relativized-recursion.md`
(1,086 lines, untracked, worktree `recursion.fast-reldesign`, branch
`docs/relativized-recursion-design`), says "Issue #4 (O-25) closes at stage R2".

Whatever its merits, this is an on-record O-25 direction that keeps a submitter-written `V`, has
no per-entry review and no menu, and has had an adversarial review. It is not mentioned anywhere,
so:

- "None is on record" and "Nothing on record does" are false as written;
- N3 (a harness-sampled keyed oracle, with the circuit's key separated from the outer `Vb`'s) and
  N5 (rank leaves, keep recursion unranked) overlap D2/D4 and D1 of that report, so "not proposed
  anywhere in the v3 record" is false;
- "every reviewed direction fails C11" is false or at least unargued for D4;
- the next ideation round, whose stated input is these documents, would rediscover the
  exploration.

**Fix.**

1. Add an "on record" row to Design §17.1, for example **D-L. Relativized node clause plus
   attested oracle (D4; variants W5 and D4+)**. Give its source (branch and head `043bcb3`, REPORT
   §1, §7, §9, the review), its known pros (O-25 closed by the deployment; composition a theorem),
   its known cons (a trusted harness service; records certify the attested deployment and are
   checkable only by the organiser until key release; the re-ask law in the pure ROM; #6 (b), #7
   and #8 unchanged; trusted-line growth of about 50 lines), and its review status.
2. In O-25 §10.2 and §10.3, and in §0, replace "None is on record" by a sentence that names D4
   and says what its review established and left open. In §1.4 and §5 (Candidate B), add one
   line: "the relativized exploration removes this premise by changing the node clause"
   (O-25 §1.4 cross-reference).
3. In Design §17.2, delete "were not proposed anywhere in the v3 record". Mark N3 and N5 as
   overlapping D-L, and replace "which every reviewed direction fails" by a per-row statement.
4. Add a bullet to `docs/README.md` "Where the code went": `explore/relativized-nark` (`043bcb3`),
   not merged, not archived elsewhere. If the orchestrator decides the exploration is out of scope
   for v3, say that explicitly with the reason, rather than omitting it.

### DOC-M2. O-25 strength statements and "kernel" labels are stronger than the evidence

**Where and why**, item by item:

1. **"Known for certain" and "in no weaker form" (O-25 §0 lines 46–50, §10.1 item 3 line 790,
   the "precise statement" lines 804–807; Design §15.1 heading line 1360; `docs/README.md` line 8,
   "can be closed only by taking the verifier away from the submitter").** "The only invariant
   that removes the submission-authored mechanism is INV′" and "achievable by construction exactly
   when the submission authors no check that sees an oracle-derived value, **and in no weaker
   form**" are universal claims. The evidence is attacks on the enumerated candidates (E, driver-E,
   MG2, MG3, opaque handles): round 2 R2.3 and R2.9, and review r2 §5. O-25 §10.3 Q2 contradicts
   them: whether a restricted composition language (a conjunction with a mandatory final binding,
   no disjunction, no data-dependent selection of checks) "is both expressive and safe **was not
   examined**". DOC-M1's D4 is a further counterexample to "only by taking the verifier away".
   *Fix:* "No weaker invariant found; every weaker candidate examined (list) was broken. Not a
   theorem: §10.3 Q2 is unexamined." Rename Design §15.1 to "…, and no submission-authored
   verifier examined could be made safe". In `docs/README.md`, write "could be closed, among the
   designs examined, only by taking the verifier away from the submitter".
2. **"Every narrower fix was broken by kernel probes" (Design §1 line 64) and "every mechanical fix
   … was broken by a kernel probe" (O-25 §0 line 28).** Several breaks are kernel-checked:
   ADV-M5.1 (`backdoor_lit`), O25-M1 (`idxOf_full`), O25T-M1 and M2 (`pubTau_eq_challenge`,
   `postHoc_iff`). Others are paper arguments in their own sources:
   - ADV-M5.4, the parametric `D` cannot support Fiat–Shamir (an argument in the #4 comment);
   - O25-M3 to M6;
   - the post-hoc attack, which Design §15.1 itself files under "Known (argument)";
   - the salting argument (V3-S1-M1).

   *Fix:* "was broken, by kernel probes (…) or by paper arguments (…)".
3. **"Known (kernel)" lists definitions and an `#eval` (Design §15.1 lines 1362–1369; the
   "Theorems" column of the O-25 §12 probe table).** In `rf-core-sc/scratch/o25/P1_interface.lean`,
   `cmpNat`, `encodeF` and `cmpF` are **definitions** that elaborate at the parametric type, and
   `pinned` is a definition exercised by `#eval O25P1.pinned (F := ZMod 7) 2`, which is compiled
   evaluation, not a kernel proof. The only `#print axioms` in the file is for `idxOf_full`. O25-M2's
   "for a 1 − 2^-96 fraction of elements {1, β, …, β^191} is an F₂-basis" is paper. *Fix:* "kernel:
   `idxOf_full`, `idxOf_all_bits`; elaborated definitions: `cmpNat`, `encodeF`/`cmpF`, `pinned`
   (with an `#eval` on `ZMod 7`); paper: the basis-density bound."
4. **T's guarantees are stated as structural facts (O-25 §0 line 38, "its review confirmed the
   mechanism cannot be authored by a submission"; §6.5 "Structural, definitional in the contract").**
   T was never implemented. Review r2 §8.1 argues the structural property for a design sketch, with
   one probe that found the breaks. *Fix:* prefix §6.5 with "For T as specified on paper (never
   implemented)", and in §0 replace "confirmed" by "argued, and found no acceptance backdoor in".
5. **A9's justification is not marked as a paper argument (Design §6.5 lines 555–560).** "Two logs
   with different answers have one tape, and no program could extract from both; without it no
   log-reading extractor could be certified" is, per the S2R RESULT fix pass, "A9 gives the
   construction; argued on paper, not kernel-checked". The orchestrator told the user the same on
   2026-10-20. *Fix:* append "(paper argument; the ledger gives the construction; not
   kernel-checked; the log-scan proof could not be closed without the bound)". Also add S2R Q14
   (DOC-M5).
6. **"About 500× between implementations of the same certified function" (Design §8.5 line 770,
   §15.3 line 1411).** The 37–43 ms row is a chain-only microbenchmark (`FastChain.lean`). Its
   unrolled BLAKE2s "still has to be proved equal to `chainStep` … this probe does not do" it, and
   "no threaded `Vb` was built as a certified entry" (#6, Evidence). The conclusion "a certified
   entry that proves nothing could win board T" stands as a strong paper argument; the factor is
   between a certified verifier and an unproved microbenchmark. *Fix:* say so in the table's
   caption and in §15.3.
7. **C4 (Design §16): "with a concrete-hash `Vb` in the clause, only decoding works and lookup is
   unprovable (#7)".** Both halves are F1 §3.1–§3.2 paper arguments (#7 "Evidence (paper sizing;
   every number here is an estimate)"). *Fix:* "(paper, F1 §3.1)".
8. **The liveness mirror reads as kernel-checked (O-25 §10.1 item 1, line 780).** "The backdoor
   is such a verifier (`Backdoor.lean`, kernel-checked), and so is its liveness mirror." No control
   at `6202402` certifies a verifier that rejects honest proofs only under BLAKE2s (no `Controls/`
   file mentions it). It is the paper observation V3-S2R-H-M4. *Fix:* "…; its liveness mirror is
   the same construction on paper (H-M4), not a control".

### DOC-M3. The second wall is overstated, and contradicts the documents' own sizing

**Where.**

- `docs/README.md` lines 9–10: "the honest entry **showed** that **no recursive entry fits** the
  caps without decisions that change the trusted base";
- Design §15.2 heading: "Honest recursion does not fit the caps, and **every way out changes the
  trusted base**";
- Design §16 C5: "At v3's values **nothing fits** (#8)".

**Contradicted by.**

- Design §1 wall 2: "only WHIR-class proof sizes close the recursion, and only just (paper
  estimate, #8)".
- Design §13.6 and Lessons §5.2, which give WHIR-class at 621–770 KiB, "yes, barely".
- Issue #8's option (i), "accept that recursion closes only with WHIR-class sizes and say so",
  which changes no trusted base.
- The honest entry measured only a **Ligero leaf** (1,464,107 B). It showed that Ligero cannot
  fit. It did not show anything about recursion.

**Fix.** Use one precise statement in all three places: "By paper estimate (#8), only a WHIR-class
PCS fits `proofCap` at node size, and only just. No such PCS has a Lean knowledge-soundness proof.
Node extraction needs a `2^29`-symbol decoder that was not written (#7). Every other route (a hash
menu, a larger `proofCap`, a proximity hypothesis, an accumulation-shaped relation) changes the
trusted base or the relation. The honest entry measured only that Ligero does not fit." Drop
"showed" from `docs/README.md`.

### DOC-M4. Several of "the user's decisions" are not the user's, or not as recorded

Design §14 calls its table "the fixed points a next design inherits unless the user reopens
them", so errors here propagate. Checked against `DISCUSSION.md`, the ledger and the user's logged
messages:

1. **T and review-only ranking are recorded as rejected by the user.** This appears in Design §1
   (lines 60–64, "which the user rejected on 2026-10-22 together with its wider menu form MG1"),
   §14 ("T, being narrower, is rejected with it"), §17.1 D-B ("**rejected by the user**"), and
   O-25 §8 ("T is narrower than MG1, so it is rejected with it … With all three options
   refused"). The user's message of 2026-10-22 09:38 reads: "I'm not happy with MG1, this severely
   restricts the design space …". CORE-HANDOFF §2.2 put three options (T, MG1, review-only ranking);
   the user answered about MG1 only. Review-only ranking was not refused either; it is excluded by
   the 2026-10-20 "O-25 must be closed" plus ADV-M5. *Fix:* record "MG1 rejected (the user's
   words)". Then add, as the author's inference: "T, being strictly narrower, falls under the same
   objection; review-only ranking does not close O-25, which the user required on 2026-10-20".
   In D-B, write "rejected by implication".
2. **§14 row "2026-10-19 (a)–(d), S1 fix pass" sits in the user's table.** The ledger heading reads
   "after the review … and **the orchestrator's decisions**, 2026-10-19", and the S1 RESULT calls
   them "The four decisions" of the fix pass. *Fix:* move the row to a separate "orchestrator's
   decisions" list, or label it.
3. **Q4 row: "(the user accepted it in Q6 because it is 25 lines)".** No source gives this
   reason. DISCUSSION Q6 states no such rationale, and the relation was then estimated at "about
   35 code lines" (DESIGN-v3 §2.1). *Fix:* delete the parenthesis, or reword it as the author's
   observation.
4. **Q6 row includes "two repositories".** DISCUSSION Q6 lists decisions V3-1 … V3-11; the
   two-repository model is V3-12 (same date, a separate decision). The row also omits Q6's "the
   extractor as a RISC-V image with a budget (Q1 stands)". *Fix:* move "two repositories" to a
   V3-12 note, and add the Q1 clause.
5. **2026-10-20 (a) and (b).** For (b), the user recommended `2^-128` with `2^-96` as the
   alternative; §14 and §6.4 present the two as neutral ("`2^-128` was chosen to match
   `errorCap`'s scale"). For (a), the user's first proposal (09:12) was an extractor "executed …
   on generated traces/proofs … if it runs within a reasonable amount of time (this needs to be
   benchmarked)". The proved bound was the orchestrator's recommendation, which the user accepted
   at 15:19 ("I'm happy with the extractor as a lean 4 function and a proved cost bound"). The
   rationale "measured-only bounds are rejected, because … never found by fuzzing" is the
   orchestrator's. *Fix:* state both. The user's first preference matters for an ideation round
   that wants a wider design space.
6. **C11 (Design §16) and O-25 §11 criterion 1 present an interpretation as the user's
   constraint.** "A rule may restrict *what the verifier is given*, not *which proof system it may
   be*" is the author's reading of the user's three objections; so is O-25 §8's "rules out … any
   fixed menu … however it is extended". *Fix:* label C11's last sentence and O-25 §8's
   "read as requirements" paragraph as the author's reading, to be confirmed by the user.
7. **Design §2 (line 89): "`DISCUSSION.md`, Q1–Q5".** `DISCUSSION.md` has Q1, Q2, Q3, Q4,
   "Q2 (revisited)" and Q6; no Q5 exists (Q2 says "revisited after Q3–Q5"). *Fix:* "Q1–Q4 and Q2
   revisited (no Q5 was held)".

### DOC-M5. Open decisions from the stages are not all carried over

**Where.** Design §14, last paragraph ("Decisions the stages asked for and never received, each
listed where it is used"), and §13.5.

**Missing** (S2R RESULT §7):

- **Q7**: the compiled interpreter's per-step cost was never measured; `Word := UInt64` is a
  mechanical port if liveness needs it.
- **Q8**: the primitive set (`clmul`, `clmulh`, `mulhu` in; no BLAKE2s compression in the
  language). Confirm.
- **Q12**: keep the RISC-V machine deleted (git has it at `05fde28`), or keep it for O-18.
- **Q14**: the `Computes` domain change (A9) is an unrequested contract change awaiting the
  user's confirmation; the alternative is a tape of at most `2^61` words. This is the only trusted
  change of the stage that nobody confirmed, and the documents present it as settled.
- **Q1** (`completenessCap` 2^-128 or 2^-96) and **Q10** (the GitHub writes) appear only in
  passing; neither is in the §14 list.
- **Q11**: both entries must be ported before any pin move. Neither entry is certified against
  the archived head `6202402`: S2a is certified against `15e4ae5`, S2b against `05fde28`, and both
  use `img`, `Complete` and `Declared.img`. This appears only in Lessons §1. Design §9.1 mixes the
  S2a entry's facts (comparator, harness, 20.9 s) with the library verifier at `6202402` ("strict
  … linear"), so a reader takes the baseline as certified against the archived contract.

Also missing from the list: REPORT §6 Q8 (adopt the organiser library as S4, and the interim
harness pieces in S3) and Q11's `V31`/`AGENTS.md` items. The §14 list cites REPORT Q5 and Q10 but
not Q8.

**Fix.** Add the six S2R ids and REPORT Q8 to the §14 list, each with one line. In Design §1 and
§9.1, add: "Neither entry is certified against the archived head `6202402`; porting (S2R Q11)
never happened."

### DOC-M6. The evidence for the decisive kernel claims is not archived, and Lessons §9 says it is

**Where.** Lessons §9, last paragraph: "**Kernel facts cited by name live in the committed
sources**: the core's `RecursionFast/Controls/` and `RecursionFast/Library/` at
`v3/contract-archive` `6202402`, and the entries' …". O-25's header (line 9) and §12 correctly say
the probes "are not committed anywhere", so the two documents contradict each other.

**What is actually local-only** (checked on disk; every path is under a gitignored `logs/` or the
untracked `scratch/` of the shared clone):

| Kernel claim cited in the documents | File |
|---|---|
| `backdoor_lit`, `lit_eq`, `Vlit_eq` (ADV-M5.1) | submissions `logs/adv-probes/LiteralTrigger.lean` |
| `collision_not_capped`, `product16_not_capped`, `eps_ge_density` (#5) | `logs/adv-probes/CountingForm.lean` |
| `spawn_get`, `all_par` (#6) | `logs/adv-probes/TaskRfl.lean` |
| `Probe.v24_ks`, `Probe.paper` (adopted), `Redundant`, `Snag` | `logs/ks-review-probes/*.lean` |
| `facts_false` / `facts_uninhabited` (S2b-M1) | `logs/s2b-review-probes/` |
| `bruteForce_steps` (H-M1, the reason the extractor is a deep program) | core `logs/s2r/probes/Shallow.lean` |
| `mem_le` (V3-S2R-M1) | core `logs/review/probes/Review.lean` |
| `idxOf_full`, `idxOf_all_bits`, `cmpNat`, `encodeF`/`cmpF`, `pinned` (O25-M1, M2); H1–H8 (O25-m1) | `rf-core-sc/scratch/o25/P1_interface.lean`, `P2_hatches.lean` (untracked) |
| `pubTau_eq_challenge`, `evil_Vb`, `postHoc_iff` (O25T-M1, M2) | `rf-core-sc/scratch/o25t/T1_pub_sees.lean` (untracked) |

Likewise, **the interim harness** that produced both `HARNESS: ACCEPT` verdicts is on local
branches of `rf-core-s2a` only:

- `v3/s2-interim-harness`, `2a4588b`, for S2a: the v3 stub, the renderer, `harness-local.sh` and
  `setup-scratch.sh`;
- `v3/ks-interim-harness`, `2464e97` … `4a1a1ed`, for S2b: the same plus `org-closure.sh` and the
  interim gate rule 4.

The remote branches seen from the core worktree (`git branch -r`, last fetch) are
`explore/relativized-nark`, `main`, `master`, `v3/contract-archive`, `v3/ks-potential`,
`v3/remove-v2` and `v3/s1-contract`, with no interim branch. The user asked on 2026-10-22 to keep
the contract work on remote, and the documents present these probes as the decisive evidence for
O-25, #5, #6 and the extractor's shape.

**Fix.** Either the PR's owner pushes the probe files, with their logs, to an archive location
(for example `v3/contract-archive` under `probes/v3/`, or the submissions repository under
`docs/probes/`), pushes the two interim branches as archive branches, and the documents cite the
pushed paths; or, at minimum:

- correct Lessons §9's last paragraph;
- add to `docs/README.md` "Where the code went" a bullet listing these files and branches as **not
  archived** (local to `leanervm-dev`);
- mark every such kernel claim in the three documents "(local probe, not archived)".

## 2. Minor findings

Each item gives the document and place, the source, and the fix.

**Attribution and citation errors**

- **DOC-m1. Who filed #4.** Design §13 intro: "Seven of them (#4–#10) were filed on 2026-10-19
  by the orchestrating agent from the honest-baseline work". Only #5–#10 and **the comment on #4**
  were filed that way (PLAN D-6; the #5–#10 bodies carry the "Filed by the orchestrating agent"
  banner and #4's does not). #4 is the O-25 tracking issue from the S1 review. Lessons §1 has it
  right. *Fix:* "#5–#10 and the comment on #4 were filed …; #4 was opened from the S1 review."
- **DOC-m2. "Five additions, two kernel-checked"** (Design §13.2). Only addition (1), the literal
  trigger, is kernel-checked. ADV1's table gives ADV-M5's evidence as "kernel, `LiteralTrigger.lean`",
  and the #4 comment marks (2) "(paper)". *Fix:* "one kernel-checked".
- **DOC-m3. V24 attributed to V3-KS-A4** (Design §12.2: "A4 the controls (`twoLucky`, `Vcol`,
  `V24`)"). V24 is V3-KS-A6, from the fix pass after review M1. *Fix:* move V24 to A6.
- **DOC-m4. `leaf_at_chainCap` listed as a negative control** (Design §4, "Controls").
  `Controls/Relation.lean:99` proves `Rel Vb (leafStmt (chainEnd s chainCap) chainCap) (.leaf s
  chainCap)`, a positive control (the S1 RESULT: "`leaf_at_chainCap` (in)"). *Fix:* move it to
  "Positive".
- **DOC-m5. The interim branches are conflated** (Design §9.3: "the interim scratch branch
  `v3/ks-interim-harness` (commits `2a4588b` … `4a1a1ed`)"). `2a4588b` is on
  `v3/s2-interim-harness`, which is based on `15e4ae5` and served S2a. `v3/ks-interim-harness` is
  `2464e97` … `4a1a1ed`, based on `05fde28`, and served S2b (both branches in `rf-core-s2a`).
  Lessons §3 and §4.7 have it right. *Fix:* name both branches with their commits.
- **DOC-m6. ArkLib policy cited to the wrong question** (Design §13.7 item 8: "the user's
  (REPORT §6 Q8)"). REPORT §6 Q8 asks whether to adopt the organiser library (S4) and the interim
  harness (S3). The ArkLib policy is REPORT §4 item 7, #9 item 8 and CORE-HANDOFF §2.11. *Fix:*
  cite those.
- **DOC-m7. Non-existent section** (Design §11.2: "REPORT §4 item 2; S2R RESULT §2.15"). The S2R
  RESULT has no §2.15. The section is CORE-HANDOFF §2.15. *Fix:* "CORE-HANDOFF §2.15".
- **DOC-m8. Non-existent section** (Lessons §3 line 170: "failed the §6.3 canaries"). Lessons has
  no §6.3. It means DESIGN-v3 §6.3 step 7, which is Design §8.3 step 7. *Fix:* "the canaries of
  Design §8.3 step 7".
- **DOC-m9. PLAN has no D-7.** Lessons §4.1 cites "PLAN D-3, D-4, D-5, D-7", and Design §18 cites
  "`PLAN.md` D-1 … D-12". `PLAN.md` jumps from D-6 to D-8 (CORE-HANDOFF §2.13 notes this). D-7
  (ring switching) is BLUEPRINT-R1's. BLUEPRINT-R1 numbers **[D-7] … [D-11]** "continuing PLAN",
  which collides with PLAN's own D-8 … D-11. *Fix:* "BLUEPRINT-R1 D-7". Note the collision once
  in Lessons §1 or §8.3, since the documents cite D-9 and D-11 (PLAN's) elsewhere.
- **DOC-m10. Log citations that do not resolve.**
  - Lessons §8.1, first trap row, cites `logs/spartan-chain/rust/kat.log`. There is no such file:
    `rust/kat/` is a directory, and `kat/kat.log` has no start-up figure. The "6.8 GB in 7 s" and
    "0.20 s and 86 MB" figures are not in `init-blowup.log` either; they appear only as text in
    REPORT, PLAN D-9 and CORE-HANDOFF.
  - The Lessons §9 index lists `field/` under `logs/spartan-chain/`; it is `logs/field/` (§4.4 and
    §4.5 cite it correctly).
  - Lessons §9 lists `logs/review/Review.log`; the file is `logs/review/probes/Review.log`.
  - The S1 logs are in `/home/devops/Verified-zkEVM/recursion.fast/logs/V3-S1/`, the main
    checkout; §9 calls this "core (S1 clone)".
  - `docs/README.md` claims the lessons document's "every number names its log or its kernel
    theorem".

  *Fix:* correct the paths, give absolute roots for the three log locations, and mark the
  start-up figures "(REPORT, no log)".

**Number inconsistencies**

- **DOC-m11. The smoke-root verification time understates the maximum.** Lessons §4.4 gives
  "0.99–1.45 s", and Design §8.5 and §15.3 give "1.0–1.45 s". `logs/spartan-chain/fix-m2/after-root.log`
  contains a 1.707 s run. The S2b final review gives "0.99–1.71 s over 9 runs; through
  `Run.verifyProof` 1.06–1.45 s". The 2 s cap's margin is therefore 0.29 s, not 0.3–1.0 s. The
  "before" range is 2.25–2.8 s in REPORT §3.3, against 2.25–2.51 s here. *Fix:* quote both
  series with their logs.
- **DOC-m12. Two different DoS numbers.** Design §13.8 gives "rejected in at most 0.25 s,
  adversarially shaped ones in at most 1.19 s", issue #10's earlier run. Lessons §3 gives
  "≤ 0.28 s; ≤ 1.25 s", the S2a RESULT's final run (`logs/V3-S2/fix/check/smoke.log`). *Fix:* use
  the final run in both, with the log.
- **DOC-m13. The theorem column of Lessons §4.2 mixes groupings.** The rows are `measure.sh`'s
  components, but the theorem counts come from the S2b RESULT §1, which groups modules
  differently. For example, "protocol" is 6 modules and 1,917 lines in `measure.sh`, while the
  RESULT's 102 theorems belong to its 4-module, 1,284-line protocol row; "field" is 5 modules here
  and 6 in the RESULT. Only the total, 1,561, is exact. The error is inherited from REPORT §3.1.
  *Fix:* add a note, or drop the per-row theorem counts.
- **DOC-m14. "Certified against nothing the public core had"** (Design §9.4). From 2026-10-20
  09:09 the branch `v3/ks-potential` (`05fde28`) was on the core's remote, with PR #11 open (PLAN
  D-8 update). C14's "an unmerged branch" is right. *Fix:* "against a branch not on the core's
  `main`".

**Constraints and design space**

- **DOC-m15. C6 inverts the dependency.** C6 says "the benchmark shape must be set after the rule,
  not before". Design §8.5 (with REPORT §4 item 9 and V3-S2R-A7) says that `T_V`'s **value** is set
  after the shape and the measuring rule, and A7 lets the rule change the shape. *Fix:* "set the
  measuring rule, then the shape, then calibrate `T_V` on the reference machine".
- **DOC-m16. C2 is garbled:** "if it closes O-25, it must do so without C11". *Fix:* "without
  violating C11".
- **DOC-m17. A constraint is missing.** Statement binding of every transcript seed (Fenzi26) is
  "a hard rule in any design" (O-25 §9.2) and O-25 §11 criterion 9, but it is not among C1–C14.
  *Fix:* add C15.
- **DOC-m18. §17's framing is imprecise.** Design §17's "the rest have the review they cite" is
  wrong for D-G, D-H, D-I, D-J and D-K: their sources are F2 §8 and §13, #8 and CORE-HANDOFF,
  which are memos, issues and handoffs, not adversarial reviews. And "which every reviewed
  direction fails" (§17.2) does not fit D-G, D-H and D-I, which fail on V3-5, on the ROM-only rule
  or on scope, not on C11. *Fix:* "the rest cite their source; a review is named where one
  exists". State per row which constraint each direction breaks.

**Omissions**

- **DOC-m19. Small items dropped from DESIGN-v3, the ledger and the issues.** Each is worth one
  line so that it is not rediscovered:
  - DESIGN-v3 §7.5, the binary-field track (a policy board with hand review of sources; relevant
    to C11);
  - DESIGN-v3 §9.3 and #1's "carried over" items: the Clean bridge, `toLayout_rel_iff` and the
    characteristic-2 balance note (O-5), and v2's `Bridge/ArkLib.lean`, now under
    `v2-archive:legacy/v2/`;
  - DESIGN-v3 §6.7 rows: level-aware verifiers (allowed; the proof may carry hints), field choice,
    and parallelism, Sybil and records;
  - DESIGN-v3 §7.7 "Records" (`records.json` per board with contract id, hardware id, `entry_id`,
    the verdict's commit; a copied entry never takes a record), also a #1 intake item;
  - V3-S1-m11 (restrict `final` to `π.size ≤ proofCap`; optional, CORE-HANDOFF §2.13);
  - V3-S2-KS-m4 (the `Fintype (Vector UInt8 n)` instances in CompPoly, VCVio and ArkLib: a note
    for any future allowlist);
  - #5's rejected alternative, the extendable-output `queryN` constructor (ADV-M3), and the
    unbuilt `merkleToy` control.
- **DOC-m20. "Fields as data" loses two points from its own source.** O-25 §7 does not carry two
  points of the proposal as made (the orchestrator, 2026-10-22 08:48):
  - the arithmetic must equal the specification **on the whole representation type, including
    unreduced encodings**, and the **equality test and the challenge derivation** must be
    contract-owned;
  - ring switching works only for binary fields.

  The first is the variant's main soundness hazard. *Fix:* add both to "Where it is incomplete".
- **DOC-m21. Design §18 "Record" is incomplete.** It omits, in the submissions repository:
  - `docs/research/`: R1–R7 and their reviews, including R4-arklib and R7-literature, which F1's
    WHIR sizing cites;
  - `docs/core/` and `docs/report/` (the v1.0 report that Design §2 cites);
  - `docs/snark-baseline/issues/`: I1–I7, the drafts of the very issues this PR closes.

  *Fix:* add them.

**Labelling, wording and hygiene**

- **DOC-m22. Derived figures are not labelled as estimates** (Design §8.5):
  - "about 65 ms of CPU on the development VM" (`T_triv,best/10`, derived from 151–164 ns per
    compression; Lessons §8.3 itself lists "the 65 ms best-linear-verifier figure" among the
    estimates);
  - "at `n = chainCap` the threaded unrolled check is about 2.6 s" (64 × 40 ms, extrapolated);
  - "4–40 s for a WHIR-class verifier" (`10^4`–`10^5` operations from R7, an estimate, times a
    measured 415 µs).

  *Fix:* mark each **estimate (derived)**.
- **DOC-m23. Unlogged durations.** Lessons §8.1's heading says "each of which cost hours", §8.3
  says "writable in a day", and §1 says "both cost time". The project admits durations only as
  measurements with a log. *Fix:* delete them, or replace them with what each trap blocked.
- **DOC-m24. The reading order skips the ideation material.** The Design header says "a
  first-time reader should then read §2, §3, §5, §7 and §14", which omits §15–§17, the reason the
  record exists. *Fix:* add §15, §16 and §17.
- **DOC-m25. A stale reference table is re-pointed to the new design** (`docs/reference/neighbouring-competitions.md`
  §5). The PR edits its intro to say the table is "updated for the v3 design (now compiled into
  `docs/v3-design-…md`)". But the table's "v3 answer" column cites DESIGN-v3 section numbers
  (§4.5, §4.2, §6.5, §2.2, §7.4; line 21, "design v3 §7.6") that do not exist in the new document
  or mean something else there. Several rows are also false for the final v3:
  - row (9), "accept-all admits no `KState`", was withdrawn by V3-S1-A13;
  - rows (1), (2) and (10) describe the counting form and `Nat.card`, superseded by V3-KS;
  - the completeness row describes `Complete`, superseded by V3-S2R-A2.

  `docs/README.md` calls `reference/` "still current". *Fix:* label the table "as of DESIGN-v3,
  2026-10-19; section numbers are that file's, on `v3/contract-archive`", or update those rows.
- **DOC-m26. Hygiene.**
  - Lessons §0 refers to "the core's `scripts/loc.py`", which is not on the stripped `main`; say
    "at `v3/contract-archive`".
  - The skeleton `CLAUDE.md` points to the design workspace without warning that its
    `design/DESIGN-v3-narg-rom.md` is the unpatched master (the DESIGN-v3 header: "The master in
    the design workspace is not patched"), so it predates V3-KS and V3-S2R. Add one line
    saying that the three `docs/` documents supersede it.
- **DOC-m27. "Unaffected" hides that the submissions repository's guidance is now stale.**
  `docs/README.md` and the skeleton `README.md` call the submissions repository "unaffected". Its
  `CLAUDE.md`, `AGENTS.md` and `docs/README.md` still call DESIGN-v3 "the design in force" and S2
  "the task in front of this repository". *Fix:* add "its guidance describes v3 as in force and is
  frozen; a follow-up PR there should say so". This review does not edit that repository's
  guidance.

## 3. Completeness: issues, ledger, open questions, finding ids, user decisions

### 3.1 The issues being closed (body and comments against Design §13)

| Issue | Incorporated | Substantive points missing |
|---|---|---|
| #1 roadmap | stages S1–S7, O-6 … O-25, pins, intake: §13.1, §12.4, §9.4 | the "carried over from v2" items: Clean bridge with `toLayout_rel_iff` and the char-2 note (O-5), v2 `Bridge/ArkLib.lean`, `L_chain`/`check-chain.py` as library examples (only "retired" is said); the "Records" intake item (DOC-m19); O-20's "Clean patches re-verified" (moot) |
| #4 O-25 and its comment | §13.2, O-25 §1–§4 | who filed it (DOC-m1); "two kernel-checked" (DOC-m2). The body's residual-channel table (ambiguous serialisation, extra `D` operations, grammar overlap, escape hatches) is covered by O-25 §4.1/§4.2. |
| #5 KS unsatisfiable, with the comment | §13.3, §6.1, Lessons §4 | the rejected `queryN` alternative and the unbuilt `merkleToy` (DOC-m19). The four comment items are all present (2^96, literal, kernel-checked paper theorem, `noncomputable`). |
| #6 `T_V` and recursion | §8.5, §13.4 | "no threaded `Vb` was built as a certified entry", and the unrolled BLAKE2s is unproved (DOC-M2 item 6) |
| #7 node extraction | §6.5, §13.5 | none of substance (CompPoly's Gao decoder not allowlisted: Lessons §6) |
| #8 honest recursion | §7.2, §13.6, Lessons §5 | none; but option (i) is lost in the wall statements (DOC-M3) |
| #9 ten items | §13.7 table, plus D-11 | item 8 cited to the wrong question (DOC-m6); item 9's unverified `UInt64` loop (1.47 µs) and item 8's 10,777-module closure (trivial) |
| #10 library | §13.8, Lessons §3 | "an entrant cannot wrap the library's `check`: the entrant must re-prove soundness and completeness for a strict copy" (now moot); numbers from a different run (DOC-m12) |

The closure statements ("what remains open, and where it went") are present for every issue.
That is the right shape for closing them.

### 3.2 The ledger

Every amendment id is represented in Design §12:

- V3-S1-A1 … A27: all 27;
- V3-KS-A1 … A8: all 8, with one misattribution (V24 belongs to A6, DOC-m3);
- V3-S2R-A1 … A9: all 9.

The ledger's "answered, not changed" items are partly carried: V3-KS-A7's m4 is not (DOC-m19);
V3-S2R's list maps onto §13.

### 3.3 The open questions of V3-S2R (Q1–Q15)

| Q | Carried? | Where |
|---|---|---|
| 1 `completenessCap` | in passing | §6.4 ("recorded alternative"); not in §14's list |
| 2 budget value | yes | O-21, §13.5 |
| 3 `logCap` against the domain | yes | §6.3 |
| 4 liveness caps | yes | §8.3 step 8, §13.5 |
| 5 succinctness, recursion incentive | yes | §8.5 |
| 6 kernel budget | yes | §8.6, §13.7 |
| 7 interpreter speed, `UInt64` | **no** | — |
| 8 primitive set | **no** | — |
| 9 Q1 superseded | yes | §14 |
| 10 GitHub writes | partly | Lessons §8.3 |
| 11 port entries before the pin moves | partly | Lessons §1 only (DOC-M5) |
| 12 keep the RISC-V machine for O-18 | **no** | — |
| 13 decision (a) reinterpreted | yes | §6.5, §14 |
| 14 A9 domain change | **no** | presented as settled (DOC-M2 item 5, DOC-M5) |
| 15 toy decoder dropped (F-D1) | yes | §6.5, §13.5 |

REPORT §6 Q1–Q11: all are carried except Q8 (organiser library S4; interim harness in S3). The
S2a RESULT §7 open questions 1–8 are all resolved or subsumed (#10, #9 item 4, S3), which the
documents reflect.

### 3.4 Finding ids

Present where they matter:

- V3-S1-M1 … M4 (Lessons §7, Design §12);
- V3-S2-KS-M1, m1, m2 (m3 by name, `step_unstopped`; m4 missing, DOC-m19);
- V3-S2a-M1, M2;
- S2b-M1 … M5 (midreview); V3-S2b-M1, M2, m1 (m2 and m6 by description);
- BP-M1 … M4 and S9-M1 … M3 (Lessons §7, unprefixed);
- V3-S2R-H-M1 … M4 and the H-m items that changed text (m1, m5, m7); V3-S2R-M1, M2, m1, m2;
- O25-M1 … M6 and m1 … m4; O25T-M1 … M6 and m1 … m9 (unprefixed in O-25 §6.3);
- ADV-M1 … M8 and the relevant ADV-m items.

Unprefixed references ("M3", "m7") are unambiguous in their context. This check passes, apart
from DOC-m3.

### 3.5 The user's decisions

| Decision | Recorded correctly? |
|---|---|
| Q1–Q4, Q6 (`DISCUSSION.md`) | mostly; the Q4 rationale is invented, Q6 is over-attributed, and Q5 does not exist (DOC-M4 items 3, 4, 7) |
| 2026-10-19 (a)–(d) | the orchestrator's, not the user's (DOC-M4 item 2) |
| 2026-10-20: the extractor is a Lean function with a proved cost bound | yes in substance; the user's first preference (benchmarked execution) and the attribution of the rationale are missing (DOC-M4 item 5) |
| 2026-10-20: completeness may have a small error, `2^-128` recommended, `2^-96` the alternative | the values yes; "recommended" is lost (DOC-M4 item 5) |
| 2026-10-20: O-25 must be closed | yes |
| 2026-10-20: proof-size direction (R1′, BCHKS25, Johnson later) | yes, sourced to CORE-HANDOFF §2.14 |
| 2026-10-22: PR #11 merged as `059812f` | yes (`git log`: merge at 2026-10-22 09:43 +0100) |
| 2026-10-22: MG1 rejected, with the quote | the quote is exact (a fragment of "I'm not happy with MG1, this severely restricts …"); its extension to T and review-only is not the user's (DOC-M4 item 1) |
| 2026-10-22: back to ideation, the contract archived, `main` stripped, the issues incorporated | yes |

### 3.6 Content of DESIGN-v3 and the RESULTs that was dropped

Nothing central is dropped. The relation, submission, security definitions, extractor, scoring,
caps, trust statement, intake, O-items and build order are all present, and §10's trust statement
is updated correctly to 292 lines and `CertificateR`. The small drops are listed in DOC-m19.
DESIGN-v3 §10 (the v2 → v3 carry-over table) is absorbed into §2 and §9.3 without its Clean and
ArkLib bridge rows. From the RESULTs, only the open questions of §3.3 are missing.

## 4. Accuracy: spot checks against the sources

Forty-seven concrete claims were checked: 35 match exactly and 12 do not. Every mismatch is a
finding above. "✔" means it matches; "✗" gives the finding.

| # | Claim (where) | Source checked | Result |
|---|---|---|---|
| 1 | Contract code lines per file; 292 in total, 9 files (Design §10, §1) | `scripts/loc.py` re-run on `6202402`: 8/68/25/22/33/62/35/8/31 | ✔ |
| 2 | The contract imports Lean core and Mathlib only, four named modules (§10) | `grep ^import` in `Contract/*.lean` | ✔ |
| 3 | `KState`, `KS`, `errorCap`, `logCap = 2^96`, `noncomputable instance` (§6.1) | `Contract/Security.lean` | ✔ verbatim |
| 4 | `failProb`, `CompleteWithError`, `completenessCap` (§6.4) | `Contract/Security.lean` | ✔ |
| 5 | `XOp` (15 operations), `XStmt`, `XProg` (`mem`, `memPerWord`), `Computes` with both domain conditions, `B t`, `outCap`, `progCap` (§6.5) | `Contract/Machine.lean`, `Extractor.lean` | ✔ |
| 6 | `Submission`, `Vb`, `Certificate` with five caps, `Declared`, `CertificateR` (§5.2) | `Contract/Certificate.lean` | ✔ |
| 7 | `Rel`, `chainCap`, the four tags `0x43`/`0x4C`/`0x4E`/`0x52`, `enc64` (§4) | `Contract/Relation.lean` | ✔ |
| 8 | `treeRoot` convention, zero digest (§7.1) | `Contract/Tree.lean` | ✔ |
| 9 | `deep_accepted_but_capped`: a 13-level proof of 1,114,024 B (§4) | `Controls/Relation.lean:206–210`; `136·2^13 − 88` | ✔ |
| 10 | `136·2^r − 88` bytes, 34,728 B at `r = 8` (§9.1) | V3-S1-A15 | ✔ |
| 11 | 600 ms for 2 steps, 15.5 s for 3, 428 ms for 1,000 (§4, Lessons §2.3) | `recursion.fast/logs/V3-S1/digest-probe/*.out` (607 ms, 15,538 ms, 428 ms) | ✔ |
| 12 | Hello-world at 22.9 GB in 20 s (§6.1) | `logs/spartan-chain/oracle-merkle-transcript/init-blowup.log` | ✔ |
| 13 | "6.8 GB in 7 s", "0.20 s and 86 MB", with its log (Lessons §8.1) | cited `rust/kat.log` does not exist | ✗ DOC-m10 |
| 14 | S1 cold build 2:02.50, 4.17 GB, 1,249 jobs; `Controls.Blake2s` 48 s, `Relation` 46 s, `Tree` 15 s (Lessons §2.3) | `logs/V3-S1/build-cold.{log,time}` | ✔ |
| 15 | Trusted lines by stage 320 → 328 → 331 → 288 → 292 (Lessons §2.1) | `loc-contract.log`, `fix-loc-contract.log`, ledger, S2R logs | ✔ |
| 16 | Library and controls S1 563/70, 387/86; fix 511/81, 544/111 (Lessons §2.2) | `logs/V3-S1/{,fix-}loc-{library,controls}.log` | ✔ |
| 17 | S2R builds 2:31.85 / 1:47.86 / 2.77 s / CI 76.97 s; fix 1:41.84, nanoda 5.09 s / 263 MB on 50 targets (Lessons §2.3) | S2R RESULT §2 and fix pass; `logs/s2r/*` | ✔ |
| 18 | S2a 310 code lines, 38 theorems, the file split 158/78/21/53 (Lessons §3) | `logs/V3-S2/fix/check/loc.log` | ✔ |
| 19 | Calibration 20.69/21.11/20.93 s and the first run 20.87/21.23/21.16 s (Lessons §3; Design §8.5, 20.7–21.2 s) | S2a RESULT, #6 | ✔ |
| 20 | 563.26 s to reject a random 1 MiB proof (§13.8) | #10, `logs/V3-S2/dos-unfiltered/run.log` | ✔ |
| 21 | Caterpillars: 212.64 s at depth 2,000; 275.0 s at 6,000 (§8.7, Lessons) | S2a RESULT, S2b review m1 | ✔ |
| 22 | 61 modules, 16,766 lines, 1,561 theorems, 1,880 copied, 3,315 Rust lines, 130.4 s cold, 562.3 s summed (Lessons §4.2–§4.3) | `reports/measurements.md`, S2b RESULT §1 | ✔ (totals; DOC-m13 for the per-row theorems) |
| 23 | Rust prover table: sizes, times, RSS, queries at `n` = 16, 1,024, 16,384 (Lessons §4.4) | `reports/rust-prover.md:143–145` | ✔ |
| 24 | 1,464,107 B and its split 786,432 / 532,480 / 137,020 (Lessons §5.1) | CORE-HANDOFF §2.14, `rust-prover.md` | ✔ |
| 25 | nanoda: 52.0 GB after 23 min; 236 MB export, 22,745 theorems; 41.9 GB; 0.76 s / 33 MB; 70 s / 2,412,072 KB; comparator 1,797 s (Lessons §4.5) | CORE-HANDOFF §2.7, S2b review, REPORT §2.7 | ✔ |
| 26 | Smoke root `Vb` 0.99–1.45 s (Lessons §4.4; Design §8.5: 1.0–1.45 s) | `fix-m2/after-root.log` has 1.707 s | ✗ DOC-m11 |
| 27 | DoS maxima (Design §13.8: 0.25/1.19 s; Lessons §3: 0.28/1.25 s) | two different runs, presented as one fact | ✗ DOC-m12 |
| 28 | The honest potential pays `(2^96(3·2^8+1)+1)/2^256 + (4/5)·2^-129`; `eps_le` (§13.3) | `SpartanChainSoundnessKSBase.lean:875` | ✔ |
| 29 | `qV = 2^14`; 7,774 queries at `n = 2^20` (Lessons §4.1) | BLUEPRINT-R1 review, `reports/leaf-snark.md` | ✔ |
| 30 | Major/minor counts of the fifteen reviews and golf passes (Lessons §7) | review files' finding headings | ✔ |
| 31 | Submissions commits `3171790`, `0358ec5`, `781d98c`, `1f59b38`, `5cb89d8` | `git log` | ✔ |
| 32 | Core history `15e4ae5` → `ecdcbd5`, `c3f6380`, `05fde28` → `059812f`; `4b3356a` → `ef7349a` → `6202402` (`docs/README.md`) | `git log` in both worktrees | ✔ |
| 33 | Q1: `B(k) = 2^(2k+16)`, L1 unranked; Q3: all runs scored (§14) | `DISCUSSION.md` | ✔ |
| 34 | Q4: "the user accepted it in Q6 because it is 25 lines" | `DISCUSSION.md` Q4, Q6 | ✗ DOC-M4 |
| 35 | ADV-M5: "five additions, two kernel-checked" (§13.2) | ADV1 table, the #4 comment | ✗ DOC-m2 |
| 36 | V24 in V3-KS-A4 (§12.2) | ledger A4, A6 | ✗ DOC-m3 |
| 37 | `leaf_at_chainCap` negative (§4) | `Controls/Relation.lean:99` | ✗ DOC-m4 |
| 38 | `2a4588b` on `v3/ks-interim-harness` (§9.3) | `git -C rf-core-s2a log` | ✗ DOC-m5 |
| 39 | ArkLib policy is "REPORT §6 Q8" (§13.7) | REPORT §6 Q8, §4 item 7 | ✗ DOC-m6 |
| 40 | "S2R RESULT §2.15" (§11.2) | the S2R RESULT's headings | ✗ DOC-m7 |
| 41 | "PLAN D-7" (Lessons §4.1) | `PLAN.md` | ✗ DOC-m9 |
| 42 | "Certified against nothing the public core had" for three days (§9.4) | PLAN D-8 update (pushed 2026-10-20 09:09) | ✗ DOC-m14 |
| 43 | AHIV22 closure 102 modules / 24.7k lines; VCVio 107–158 modules (§11.3, Lessons §6) | E2 lines 79–81 | ✔ |
| 44 | leanVM 2→1 step ≈ 18.4k compressions; 15.9k constraints per compression (§7.3, Lessons §5.2) | E3 lines 54–57 | ✔ |
| 45 | Theorem names cited (`twoLucky_*`, `collision_no_bool_kstate`, `colBool_below`, `v24_ks`, `v24_no_bool_kstate`, `queryThenAccept_ge_one`, `grind_exact`, `grind128_complete`, `grind127_not_complete`, `fixed_not_complete`, `rejectAll_not_complete`, `vb_rejects_all_certified`, `choice_certificate`, `scan_computes`, `enum_no_computes`, `treeRoot_kat`, `acceptAll_kstate_iff`, `complete_withError_zero`, `failProb_eq_prob`, `paper`, `backdoor`, `mem_charged(_run)`, `poke_affine/const`) | `grep theorem` at `6202402`; statements of `enum_no_computes`, `fixed_not_complete`, `grind*` read | ✔ |
| 46 | `Backdoor.lean`: `q0`, `trigger`, `magic`, `V`, `S` fields, the boolean state (O-25 §1.2) | `Controls/Backdoor.lean:38–102` | ✔ |
| 47 | The user's MG1 quote (§14, O-25 §8) | timeline 2026-10-22 09:38 | ✔ |

Not checkable here: the literature identifiers of O-25 §9 (no network; they agree with F2 §13 and
review r2 §8.3 where those cite them), and the dates of the v0.3 report.

## 5. Overclaims, estimates and time language

**What passes.**

- **"Fields as data"** is marked unreviewed everywhere it appears: O-25 §7's heading and first
  paragraph ("no adversarial review, no probe and no sizing … so that it is not mistaken for a
  reviewed option"), Design §13.2 ("(unreviewed)") and Design §17.1 D-F ("**unreviewed**"). Its
  soundness paragraph is hedged ("might be sound"). Only DOC-m20 (two lost hazards) remains.
- **N1–N5** are marked "new, unreviewed", each carries a "Con", and §17 says "None is chosen here;
  the user chooses". None is presented as chosen, and no row of §17.1 is recommended. The only
  defect is the false novelty claim and the C11 framing (DOC-M1, DOC-m18).
- **The paper theorem** is described exactly as the contract header describes it: kernel-checked
  for a lazily sampled oracle and a deterministic game, with the passage to a random function and
  to randomised adversaries on paper (Design §6.3).
- **Estimates** are marked as such for: the budget's fixed term (§6.5, "**estimate**, F1 §3.3",
  deviation F-D1); the PCS sizing table (Lessons §5.2: "all **estimates** except the measured
  rows"); #8's sizing ("paper, except the circuit size"); and the V31 gap ("a paper argument").
  Three derived figures in §8.5 are not marked (DOC-m22).
- **Measured durations** carry their logs throughout Lessons §2–§4, with the load average and the
  VM noted (Lessons §0). The exceptions are DOC-m10 and DOC-m11.
- **No time estimates** of future work appear anywhere: a search for hours, days, weeks, "quick",
  "easy" and "a few" found only past-tense or unlogged durations (DOC-m23). The O-25 dependency
  chain is stated "without durations", as the source does.

**What does not pass.**

- **O-25 strength and "kernel" labels:** DOC-M2, items 1–8.
- **The second wall:** DOC-M3.
- **The user's decisions extended beyond the user's words:** DOC-M4 items 1, 3, 5 and 6.
- **A9's justification**, which is a paper argument, is presented as a found fact (DOC-M2 item 5).
  It is also an unconfirmed contract change (DOC-M5, Q14).
- **"Every number names its log or its kernel theorem"** (`docs/README.md`, on the lessons
  document): not quite (DOC-m10).

## 6. Internal consistency and PR hygiene

**Cross-references between the three documents resolve.**

- Every "Lessons §n" cited from the design (§1, §2, §3, §4, §4.4, §4.5, §5, §6, §8) exists.
- Every "O-25 §n" cited from the design (§2, §5, §6, §6.4, §7, §11) exists.
- Every "Design §n" cited from the other two documents (§6.4, §7.3, §8.5, §11.2, §15, §16 C3/C5,
  §17) exists.
- Two citations into other sources do not resolve: DOC-m7 ("S2R RESULT §2.15") and DOC-m8 (bare
  "§6.3" in Lessons).
- Every relative Markdown link in `README.md`, `docs/README.md`, `docs/reference/` and the three
  documents resolves (checked with a script).

**Contradictions.**

- O-25 §10.1 against §10.3 Q2, on whether weaker invariants were excluded (DOC-M2 item 1).
- `docs/README.md`, Design §15.2 and C5 against Design §1, §13.6 and Lessons §5.2, on whether
  WHIR fits (DOC-M3).
- Lessons §9 against O-25 §0/§12, on whether probes are committed (DOC-M6).
- Design §13.8 against Lessons §3 (DoS maxima, DOC-m12); Design §8.5 against the logs (DOC-m11);
  C6 against §8.5 (DOC-m15).
- No contradiction was found between the documents and the skeleton `README.md`/`CLAUDE.md`.

**Commits and branches are consistent.**

- `15e4ae5` (12 citations), `05fde28` (11), `059812f` (7), `4b3356a` (8), `ef7349a` (3) and
  `6202402` (15) are used with one meaning each, and all match `git log` in the archive and
  design worktrees.
- `059812f` merges `05fde28` into `main` on 2026-10-22. The archive branch is
  `15e4ae5` → `ecdcbd5` → `c3f6380` → `05fde28` → `4b3356a` → `ef7349a` → `6202402`, and it does
  not contain `059812f`. `docs/README.md` states this correctly.
- The branch is named `v3/contract-archive` in all eight files that name it, and
  `origin/v3/contract-archive` is `6202402`.

**The skeleton matches the tree.**

- `git status`: the contract, library, controls, vendored model, scripts, tests and the four
  stage/review records are deleted. `RecursionFast.lean` and the four new `docs/` files are
  untracked. `README.md`, `CLAUDE.md`, `lakefile.toml`, `.gitignore` and one paragraph of
  `neighbouring-competitions.md` are modified.
- `RecursionFast.lean` is a module docstring only. `lakefile.toml` has one `lean_lib` and the
  unchanged `[[require]]` pins.
- `docs/reference/notes/` holds R1, R2, R3 and R5, as `docs/README.md` says (R4 was never on the
  core).
- `logs/lake-build-ideation.log`: `Build completed successfully (3 jobs)`, 26.5 s, exit 0.
- The skeleton `README.md` says the submissions repository stays pinned at `15e4ae5`. That commit
  is an ancestor of the new `main`, so the pin stays reachable.

**Commands.**

- No document tells the reader to run a command that is gone from `main` without saying where it
  lives.
- `docs/README.md` states the rule "The branch is the reference whenever a document below cites a
  file under `RecursionFast/`, `scripts/` or `docs/` of the core", which covers the many path
  citations.
- One soft exception remains: Lessons §0's "the core's `scripts/loc.py`" (DOC-m26).
- The `CLAUDE.md` build instructions (symlink the shared package tree, then `lake build`) are
  correct for the skeleton.

**What the PR leaves only on the VM** (DOC-M6): the probes, the interim harness branches, and the
logs. The logs are disclosed as local. The probes and branches are disclosed inconsistently.

## 7. Usability for the next ideation round

**Can a reader of these documents alone understand v3?**

- **Yes, for what v3 was.** Design §1–§11 is a self-contained and faithful restatement of the
  final design, with the ledger folded in. The quoted trusted definitions match the archived Lean
  verbatim (§4, rows 3–8).
- **Mostly, for why it stopped.** Design §15 states the walls with their evidence. Two of the four
  walls are overstated (DOC-M2, DOC-M3), and the reader is never told about the one on-record
  exploration that disputes the first wall's premise (DOC-M1).
- **Yes, for the costs.** Lessons is the strongest of the three documents: it gives the cost of
  every component, with logs.

**The constraints C1–C14.** Most are precise and traceable.

| C | Assessment |
|---|---|
| C1 | precise; justified by H-M1, H-M2, V3-S2R-M1, M2 and the user's 2026-10-20 decision. Its last clause ("with a kernel-checked control, not an estimate") is the right lesson from F-D1. |
| C2 | the clause "without C11" is garbled (DOC-m16); otherwise sound |
| C3 | justified (#5); names v3's own controls, so a non-potential design needs the general form: "a positive control for a multi-answer challenge and for collision charging, and a negative control that the length bound is load-bearing" |
| C4 | justified, but it is a paper argument (DOC-M2 item 7) |
| C5 | the right requirement; its justification "nothing fits" contradicts the WHIR estimate (DOC-M3) |
| C6 | the dependency between rule and shape is inverted relative to §8.5 (DOC-m15). That CPU time is the right measure is itself unvalidated: H-m10 notes CPU time does not remove SIMD. |
| C7, C8, C9, C10, C13, C14 | precise, each with its evidence |
| C11 | an interpretation of the user's objection, presented as the user's constraint (DOC-M4 item 6) |
| C12 | inherits V3-1 ("no field", Q6). The next round should know that this constraint and "fields as data" (D-F) pull against each other. That is a choice for the user, not settled. |
| missing | statement binding of transcript seeds (DOC-m17) |

**Is §17's design space fair?** Mostly. No row is recommended. Every on-record row states the
cost that matters to the user. The rejected rows are marked, though with the attribution problem
of DOC-M4 item 1. §17.3's three questions (write the backdoor for the proposal; size one honest
recursive entry on paper; fix the machine and the measuring rule before any value) are the right
test.

The space is not complete: DOC-M1's relativized/attested-oracle direction is absent. That is the
only O-25 direction on record that claims to meet the user's three objections. The §17.2 preamble
also gives the unreviewed N1–N5 an unearned edge: "they aim at C11 directly, which every reviewed
direction fails" (DOC-m18).

**A reader-only path** (suggested for `docs/README.md`): Design §1, then §15–§17, then O-25
§0, §10 and §11, then Lessons §5 and §8.4, then the rest as needed.

## 8. Verdict

**Changes required before the PR is opened.** The documents are accurate in bulk, the trusted
definitions they quote are verbatim, and the ledger index is complete. But they are about to be
the only record of v3 on `main`, and as written they:

- omit an O-25 exploration that is on the core's remote and starts from the user's own idea
  (DOC-M1);
- state several O-25 and recursion conclusions more strongly than the evidence (DOC-M2, DOC-M3);
- attribute to the user decisions the user did not make (DOC-M4);
- drop four open questions, including an unconfirmed contract change (DOC-M5);
- claim that the evidence for the decisive kernel facts is committed when it is local to the VM
  (DOC-M6).

**Must fix (majors).**

- DOC-M1, DOC-M2, DOC-M3, DOC-M4 and DOC-M5 are text changes to the three documents and
  `docs/README.md`. For DOC-M1, the orchestrator must decide how the relativized exploration is
  cited (a §17.1 row plus O-25 cross-references is proposed).
- DOC-M6 needs either pushes (the probe files and the two interim branches) or a corrected,
  explicit "not archived" list. Pushing is the user's call under the no-push rule.

**Should fix (minors).**

- DOC-m1 … m14 are citation and number corrections, each a one-line edit.
- DOC-m15 … m18 tighten the constraints and the design-space framing.
- DOC-m19 … m21 add one-line mentions so that nothing is rediscovered.
- DOC-m22 … m27 are labelling, wording and hygiene.

None of the minors changes a conclusion. DOC-m11, m12 and m25 correct facts a reader would
otherwise carry forward.

After the fixes, the three documents would be a sound and usable basis for the next ideation
round.
