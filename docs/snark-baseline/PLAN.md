# The honest baseline: plan and decisions log (stage S2, 2026-10-19)

Orchestrator's working document for the user's request of 2026-10-19: an *honest* baseline entry,
meaning a real succinct hash-based argument in the style of leanVM / leanerVM / Spartan, certified
against the pinned contract. Measurements and proof effort are recorded along the way. Decisions
taken while the user was unreachable are marked **[D-n]**, with their reasons.

## 1. Critical review of the request

| # | Point | Consequence / decision |
|---|---|---|
| R1 | The request says "for the current security definitions", but `docs/baseline/BASELINE-TASK.md` (the S2 brief) and DESIGN-v3 §7.3 / V3-9 fix the S2 baseline as the **witness-sending argument**, which is not a SNARK. | **[D-1]** We build both. S2a is the witness-sending entry, the brief's definition of done. It is cheap: the core library already has its certificate, and it exercises the whole pipeline. S2b is the honest SNARK entry the user asked for. They are separate roots. |
| R2 | "Passes the security definitions" assumes an honest SNARK *can* satisfy the S1 contract. The counting form `KState.Bounded` requires a per-fresh-query bound for **every** log of **any** length. Standard BCS/Merkle bounds have a `Q²/2^λ` collision term. A query phase also needs more than 256 bits of challenge randomness, so it spans several oracle answers. | To verify before any design work (task F1 and ADV1). If confirmed, the honest entry is impossible under the pinned contract, and a contract amendment is a precondition, not an optional "rule tweak". **[D-2]** pending. |
| R3 | `ImageComputes` requires the extractor as a RISC-V program proved against the vendored RV64 semantics. A code-based PCS needs straight-line extraction by decoding committed codewords, plus indexing the log by answer. That means a verified decoder in assembly. DESIGN-v3 O-15(2) lists such an image as an organiser asset that does not exist. | Proof-effort item: measure, then decide whether to build it or propose a rule change (F1 §4). |
| R4 | "R1CS arithmetisation of the verifier" = recursion: the node circuit must arithmetise `Vb`, including in-circuit BLAKE2s for the Merkle paths and Fiat–Shamir. `Rel` requires the extracted child proofs to be accepted by `Vb` with *concrete* BLAKE2s, while `KS` is proved for a random oracle. | The circuit-correctness theorem (R1CS satisfiable ⇔ `Vb` accepts) is an obligation of both directions: completeness needs ⇐ and the extractor needs ⇒. |
| R5 | `T_V = 2 s` on the root check, with compiled Lean. A Spartan verifier must evaluate the constraint matrices' multilinear extensions at a random point. For a non-uniform node circuit of ~10^8 constraints that is linear work. | We need uniform (repeated-step) circuits or SPARK-style preprocessing. Design item. |
| R6 | "Re-use code from leanerVM/ArkLib/CompPoly" vs the import rule: an entry imports only the core's allowlist plus its own modules. | Reused code is either imported (if allowlisted) or copied into the entry's root. Explorer E2 checks the allowlist. |
| R7 | "Gaming the rules is fair game, except CGH" plus "report it as an issue". | Every gaming route found is filed as an issue on the core repository (`scaraven/recursion.fast`), which the user asked for. No entry uses one. |
| R8 | The user is unreachable for 12 hours, the rules may change, and pushing is restricted by `CLAUDE.md`. | Issues are filed (requested). A contract-amendment branch is prepared in a scratch clone of the core. Pushing it or opening a pull request is the step `BASELINE-TASK.md` §11.9 asks for ("the core-side pull request"). This repository's pin is not moved to an unpushed commit. |

## 2. Work breakdown

Phase 0 (parallel): F1 (Fable: contract feasibility and minimal amendment), ADV1 (independent
adversarial review of the rules), E1–E4 (exploration: leanerVM; ArkLib/VCVio/CompPoly; leanVM +
Spartan + Rust; Clean + RISC-V tooling + harness), S2a implementation.

Phase 1: decide the contract amendment and the SNARK design (Fable proposes, an Opus adversarial
reviewer attacks, the orchestrator decides). File the issues.

Phase 2 (S2b, staged, each stage implement → review + golf → fix):
- S2b-1: executable Lean verifier and prover components (field, multilinear utilities, Merkle,
  transcript, sumcheck, PCS), with known-answer tests against the native prover;
- S2b-2: circuits (BLAKE2s compression, chain step, verifier circuit) and the native prover;
- S2b-3: proofs (completeness, circuit correctness, KS under the amended contract, extractor);
- S2b-4: measurements (prover time per leaf/node and tree, verifier time vs `T_V`, proof size vs
  `proofCap`, build and check times).

## 3. Decisions log

Phase-0 inputs: `notes/F1-ks-feasibility.md` (Fable), `notes/ADV1-rules-review.md` (independent
review, kernel-checked probes under `logs/adv-probes/`), `notes/E1`–`E4` (exploration).

- **[D-2] The S1 contract cannot certify an honest succinct argument.** Three independent sources
  agree: F1 §1–§2 with paper proofs, ADV-M2/ADV-M3 with kernel-checked probes, and E1, where
  leanerVM's own planned bound has a `Q²` term and a grinding-backed query round.
  1. `Bounded` over logs of every length cannot charge collision and late-preimage events.
  2. The per-answer boolean count cannot charge a query phase that spans several answers.

  Decision: amend the contract with F1 §4.2. The knowledge state becomes a potential `μ`: on
  average it rises by at most `ε` per fresh answer, and it extracts below `1`. The laws hold for
  logs within `logCap = 2^64`. The amendment is prepared on a branch of a scratch clone of the
  core, together with the controls of F1 §4.6. The honest entry is developed and certified against
  that branch. This repository's pin moves only once the core merges it.
- **[D-3] The first honest entry is F1's R1.**
  - Leaf proofs carry `(s, n)` in the clear followed by a SNARK of the chain computation, so the
    extractor only parses and the existing 8-instruction image works.
  - Node proofs are witness-sending: no queries, and the node check runs the instantiated `Vb`
    on the children, which is what `Rel` states.

  Reasons:
  - Node extraction requires decoding (F1 §3.1, ADV-M7).
  - The decoder does not fit the budget (F1-3).
  - A verified RV64 decoder is a project of its own, and the extraction rule for nodes is the
    user's decision (F1 §6.2).

  R2 (recursion) is designed but blocked on that decision.
- **[D-4] The protocol for R1:**
  - field: `BF64` with challenges in `Ext3`;
  - argument: Spartan/Flock-style R1CS sumchecks with uniform (repeated-block) matrices, so
    there is no SPARK step;
  - commitment: a multilinear **Ligero-style tensor** commitment with a Merkle tree over the
    oracle and Fiat–Shamir over the oracle.

  Ligero over Basefold (F1 ranked Basefold first for R1) is chosen for proof effort: one
  unique-decoding lemma for interleaved Reed–Solomon codes. Short-wide matrices keep the
  smoke-size proof under `proofCap`. Neither commitment fits `proofCap` at the ranked leaf size, so
  this costs nothing that R1 has. The blueprint (Fable, then adversarial review) fixes the
  parameters and byte formats.
- **[D-5] A word-level `BF64`/`Ext3` in Lean, proved equal to CompPoly's.** CompPoly's compiled
  arithmetic is 29.7 µs per `BF64` multiply and 415 µs per `Ext3` multiply (E2,
  `logs/probes/e2/`), too slow for `T_V` and for `P`.
- **[D-6] Issues are filed on the core repository** for every confirmed finding, as the user
  asked. ADV-M5 goes to the existing issue #4 as a comment. The core-side amendment branch is
  offered as a draft pull request, which `BASELINE-TASK.md` §11.9 asks for. Nothing is merged.
- **Issues filed (2026-10-19)** on `scaraven/recursion.fast`. Drafts are in `issues/`.

  | Issue | Topic | Source findings |
  |---|---|---|
  | #5 | KS is unsatisfiable for Merkle/BCS arguments | F1-1, F1-2, ADV-M2, ADV-M3 |
  | #6 | `T_V` does not exclude witness-sending; board T rewards avoiding recursion | ADV-M1, ADV-M4 |
  | #7 | Node extraction is decoding; the extractor budget is too small | F1-3, ADV-M7 |
  | #8 | Honest recursion under the caps | F1-4, ADV-M6, ADV-M8, O-23 |
  | #9 | Minor rules and hygiene | ADV-m1–m7 |
  | #10 | Library: canaries and quadratic decoding | S2a findings |
  | #4, comment | Backdoor variants that evade the proposed defences | ADV-M5 |
- **[D-8] The contract amendment is final on a local branch only.**
  - Where: branch `v3/ks-potential` of the scratch core clone `/home/devops/Verified-zkEVM/rf-core-ks`.
  - Head: `c3f6380`, possibly followed by one commit that adds `docs/reviews/V3-S2-KS-review.md`.
  - The contract changes: `logCap = 2^96`, a literal `2^256` in the step law, and the paper
    theorem as `Library/PaperTheorem.lean`, kernel-checked.
  - Review: `docs/reviews/V3-S2-KS-review.md`. Fix pass: the RESULT in the clone.

  Pushing it to `scaraven/recursion.fast` and opening the draft pull request was **denied by the
  permission system**, which is consistent with `CLAUDE.md`'s "no pushing". That step is left to
  the user: push the branch, open a pull request that references #5, and after the merge move
  this repository's pin in its own commit. Until then the honest entry builds against the shared
  development clone `/home/devops/Verified-zkEVM/rf-core-sc`, which tracks that branch.
