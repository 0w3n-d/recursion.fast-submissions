# Fix log for `V3-ideation-docs-review.md` (the four ideation documents)

Applied 2026-10-22 to the worktree `/home/devops/Verified-zkEVM/recursion.fast-design`, branch
`v3/ideation-design-docs`: `docs/README.md`, the design (`docs/v3-design-…md`, "Design"), the
lessons (`docs/v3-lessons-…md`, "Lessons"), the open problem (`docs/v3-open-problem-…md`, "O-25"),
and one paragraph of `docs/reference/neighbouring-competitions.md`. One line per finding: **fixed**
(with where) or **argued** (with why). Line counts after the pass (`wc -l`): README 66, Design
1,774, Lessons 690, O-25 1,115; `neighbouring-competitions.md` 254.

## Majors

- **DOC-M1 fixed.** The relativized-NARK exploration (`origin/explore/relativized-nark`, `043bcb3`) is now: O-25 §13 (its own section, from `docs/explore/REPORT.md` with the REPORT's evidence labels kept; the review `EXPLORE-report-review.md` cited); Design §2 (history), §15.1 (a fourth "Known" paragraph), §17.1 row D-L with pros, cons, source and review status, and the per-row constraint list; Design §18 and `docs/README.md` ("Where the code went"). "None is on record" / "Nothing on record does" replaced (O-25 §0, §10.2, §10.3 Q1). The keyed-oracle claim is qualified "under v3's node clause" and the relativized route named (O-25 §1.4, §5 Candidate B; Design §6.7, §13.2). §17.2's "not proposed anywhere" deleted; N3 and N5 marked as overlapping D-L (D2/D4 and D1); "which every reviewed direction fails" replaced by the per-row list. D4 evaluated against C11 in O-25 §10.2 and §13 (agent-written verifier kept, no review, no menu; a trusted service, organiser-only checking until key release, three unchanged issues) without endorsement. No untracked file in any other worktree was read or cited.
- **DOC-M2 fixed.** (1) "only invariant" / "in no weaker form" weakened to "among the candidates examined … no weaker form was found, and none is excluded by a theorem", with §10.3 Q2 named (O-25 §0, §10.1 item 3, the precise statement; Design §15.1 heading and text; `docs/README.md` "among the designs examined"). (2) "broken by kernel probes" → "by a kernel probe or by a paper argument", each break labelled (O-25 §0; Design §1). (3) `cmpNat`, `encodeF`/`cmpF`, `pinned` labelled type-checked definitions plus an `#eval`, the basis density bound labelled paper (O-25 §4.2, §12 table; Design §15.1). (4) O-25 §6.5 prefixed "For T as specified on paper (never implemented)"; §0 "confirmed" → "argued, and found no acceptance backdoor in T as specified". (5) A9 marked a paper argument, with S2R Q14 (Design §6.5, §13.5, §14). (6) The 500× figure captioned as a certified verifier against an unproved chain-only microbenchmark; "no threaded `Vb` was built"; the unrolled hash unproved equal to `chainStep` (Design §8.5, §15.3). (7) C4 marked paper (F1 §3.1–§3.2). (8) The liveness mirror marked paper (H-M4), no control (O-25 §1.5, §10.1 item 1).
- **DOC-M3 fixed.** One statement in all three places: WHIR-class fits "yes, barely" by paper estimate, no Lean proof; the honest entry measured only that Ligero does not fit; #8's option (i) changes nothing but has no proof plan; every other route changes the trusted base or the relation (`docs/README.md`; Design §1 wall 2, §15.2 heading and text, C5).
- **DOC-M4 fixed.** (1) MG1 recorded as the user's words only; T and review-only ranking as the authors' inference, so labelled (Design §1, §14 table, §15.1, §17.1 D-B "rejected by implication"; O-25 §0, §8). (2) The 2026-10-19 (a)–(d) row labelled the orchestrator's decisions. (3) The Q4 parenthesis reworded as the authors' observation. (4) Q6 row: V3-1 … V3-11 with the Q1 clause added; "two repositories" moved to a V3-12 note. (5) 2026-10-20 (a): the user's first proposal (09:12, quoted) and the accepted recommendation (15:19, quoted), the rationale attributed to the orchestrator; (b): "the user recommended `2^-128`, with `2^-96` as the alternative" (Design §14, §6.4). (6) C11's last sentence and O-25 §8's "read as requirements" paragraph and §11 criterion 1 labelled the authors' reading, to be confirmed. (7) "Q1–Q5" → "Q1–Q4 and Q2 revisited; no Q5 was held" (Design §2, §14).
- **DOC-M5 fixed.** S2R Q1, Q7, Q8, Q10, Q11, Q12 and Q14, and REPORT §6 Q8, added to Design §14's list, with Q7/Q8/Q12/Q14 also in §13.5. "Neither entry is certified against the archived contract; S2a at `15e4ae5`, spartan-chain at `05fde28`, both with the interim harness; porting (Q11) never happened" stated in Design §1 (a new closing paragraph), §9.1, §14; Lessons §1; `docs/README.md`.
- **DOC-M6 fixed** (the orchestrator archived the evidence; the documents now point to it). Every "head `6202402`" is now "contract state `6202402`, branch head `f4de3b8`" (`docs/README.md`; Design header, §1, §18; O-25 header, §12; Lessons §0, §9). Lessons §9 rewritten: the three log roots as absolute paths, an "Archived probes" paragraph listing `evidence/README.md`, `evidence/probes/*` and `evidence/interim-harness/*`, and what is still local only; the false "kernel facts live in the committed sources" sentence replaced. Probe citations repointed: O-25 §12 table (archived path and contract per probe); Design §13.2, §15.1, §18; Lessons §9.

## Minors

- **DOC-m1 fixed.** Design §13 intro: #4 opened from the S1 review; #5–#10 and the #4 comment filed by the orchestrating agent (PLAN D-6).
- **DOC-m2 fixed.** Design §13.2: "one kernel-checked", items (1) kernel and (2) paper.
- **DOC-m3 fixed.** Design §12.2: `V24` moved to A6.
- **DOC-m4 fixed.** Design §4: `leaf_at_chainCap` listed as positive.
- **DOC-m5 fixed.** Design §9.3: both interim branches named with their commits and bases, and the archived patch series.
- **DOC-m6 fixed.** Design §13.7 item 8 cites REPORT §4 item 7 and CORE-HANDOFF §2.11 item 8.
- **DOC-m7 fixed.** Design §11.2 heading cites CORE-HANDOFF §2.15.
- **DOC-m8 fixed.** Lessons §3: "the canaries of Design §8.3 step 7".
- **DOC-m9 fixed.** Lessons §4.1: "BLUEPRINT-R1 D-7"; Lessons §1 notes the PLAN/BLUEPRINT numbering collision and which document each cited D-n belongs to; Design §18 says PLAN has no D-7.
- **DOC-m10 fixed.** Lessons §8.1: the nonexistent `rust/kat.log` citation removed; the 6.8 GB / 0.20 s figures marked as text-only (REPORT, PLAN D-9, CORE-HANDOFF) with the 22.9 GB figure kept against `init-blowup.log`. Lessons §9: `logs/field/` as its own row, `logs/review/probes/Review.log`, absolute roots for the three log locations (S1 logs in the main checkout). `docs/README.md`'s "every number names its log or kernel theorem" qualified.
- **DOC-m11 fixed.** Lessons §4.4: the smoke root as 0.99–1.71 s over nine runs (`fix-m2/after-root*.log`, including 1.707 s), 1.06–1.45 s through `Run.verifyProof`, 1.22–1.26 s in the harness runs, and both "before" ranges; the margin "as small as 0.29 s". Design §8.5 and §15.3 quote the same series.
- **DOC-m12 fixed.** Design §13.8 uses the final run (0.28 s / 1.25 s, `logs/V3-S2/fix/check/smoke.log`) and says the issue quoted an earlier run.
- **DOC-m13 fixed.** Lessons §4.2: a note that the per-row theorem counts follow the RESULT's grouping and only the total is exact.
- **DOC-m14 fixed.** Design §9.4: "against a branch that was on the core's remote (pushed 2026-10-20 09:09, PR #11 open) but not on its `main`".
- **DOC-m15 fixed.** C6: measuring rule, then shape, then calibration on the reference machine; Design §8.5's last sentence likewise; H-m10's caveat on CPU time added to both.
- **DOC-m16 fixed.** C2: "without violating C11".
- **DOC-m17 fixed.** C15 added (statement binding of every transcript seed, Fenzi26, with a harness canary).
- **DOC-m18 fixed.** Design §17 intro: "the rest cite their source; a review is named where one exists" with the rows that have one; a per-row "which constraint each breaks" list after the table; §17.2's framing replaced.
- **DOC-m19 fixed.** Design §12.5 added: the binary-field track (§7.5), the Clean bridge with `toLayout_rel_iff` and O-5, v2's `Bridge/ArkLib.lean`, `L_chain`/`check-chain.py`, O-20's moot Clean clause, the §6.7 rows not repeated in §8.7, the Records intake item, V3-S1-m11, V3-S2-KS-m4, #5's `queryN` alternative and the unbuilt `merkleToy`.
- **DOC-m20 fixed.** O-25 §7 "Where it is incomplete" gains (v) equality on the whole representation type including unreduced encodings and the contract-owned equality test and challenge derivation, and (vi) ring switching only for binary fields.
- **DOC-m21 fixed.** Design §18 adds `docs/research/` (R1–R8, A1–A8), `docs/core/`, `docs/report/`, `docs/snark-baseline/issues/` I1–I7, `docs/baseline/v2-example/`, and the two review files of this pass.
- **DOC-m22 fixed.** Design §8.5: 65 ms, 2.6 s and 4–40 s marked **estimate (derived)** with their derivations; §15.3 "an estimated 4–40 s".
- **DOC-m23 fixed.** Lessons §8.1 heading no longer says "cost hours"; §1 "both cost time" removed; §8.3 "in a day" removed.
- **DOC-m24 fixed.** Design header's reading order adds §15–§17 and the reader-only path across the three documents; `docs/README.md` gives the same path.
- **DOC-m25 fixed** (the reference file, minimal edit): the §5 intro now says the table is as of `DESIGN-v3.md` of 2026-10-19, that its section numbers are that file's on `v3/contract-archive`, and which rows are superseded by which amendment and where the compiled design treats them ((1), (2), (10) the counting form; (9) accept-all; the completeness row; (4) the image cap). The rows themselves are unchanged. `docs/README.md` no longer calls `reference/` "still current" and says the table's status.
- **DOC-m26 fixed in part.** Lessons §0: "`scripts/loc.py` at `v3/contract-archive` … not on the stripped `main`". The skeleton `CLAUDE.md` is outside the four files this pass may edit; **follow-up for the orchestrator:** add one line there saying that `design/DESIGN-v3-narg-rom.md` in the design workspace is the unpatched master (it predates V3-KS and V3-S2R) and that the three `docs/` documents supersede it.
- **DOC-m27 fixed in the README; the rest is a follow-up.** `docs/README.md` now says the submissions repository "is not changed by this PR", that its `CLAUDE.md`, `AGENTS.md` and `docs/README.md` still describe DESIGN-v3 as in force and S2 as the task, that this guidance is frozen as of 2026-10-22, and that a follow-up PR there should say so. The submissions repository's own guidance was not edited (outside this PR).

## Argued, not changed

- **DOC-M2 item 1, the heading of Design §15.1.** Changed to "no submission-authored verifier examined could be made safe" as the review proposes; the stronger phrase is gone. Nothing argued.
- **DOC-m13.** The per-row theorem counts are kept (with the note) rather than dropped, because the total and the module-to-row mapping are the record's; dropping them would lose the only per-component theorem figures the sources give.
- **The relativized exploration's untracked draft** (`docs/DESIGN-relativized-recursion.md` in `recursion.fast-reldesign`), which the review read: not read and not cited, per the orchestrator's instruction; the documents cite only the remote branch `explore/relativized-nark` at `043bcb3`.

## Not verified here

- The dates and authorship of the exploration branch's commits beyond `git log` (2026-10-20 to 22, `scaraven`).
- The exploration's numbers are quoted with its own labels from its REPORT and review; none was re-derived or re-measured.
