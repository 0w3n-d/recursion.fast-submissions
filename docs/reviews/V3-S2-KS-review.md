# V3-S2-KS review: the potential knowledge state and the log-length guard

Adversarial review of the core amendment on branch `v3/ks-potential` (head `ecdcbd5`, on top of the
core's `15e4ae5`) in the scratch clone `/home/devops/Verified-zkEVM/rf-core-ks`: `git diff
15e4ae5..ecdcbd5`. Inputs: the clone's `docs/stages/V3-S2-KS-RESULT.md` and ledger entries
V3-KS-A1 … A5 in its `docs/DESIGN-AMENDMENTS.md`; the motivation is this repository's
`docs/snark-baseline/notes/F1-ks-feasibility.md` §1, §2, §4 and `notes/ADV1-rules-review.md`
(ADV-M2, ADV-M3), filed as scaraven/recursion.fast#5. Skills: `adversarial-review` (passes A
and C; pass B, fidelity to a pinned implementation, does not apply because nothing here is
transcribed) and `lean4:review` (Layer 2 advisory: this is not a Mathlib contribution).

Probes are in `logs/ks-review-probes/` (gitignored). Each one compiles with `timeout 900 lake env
lean <file>` from the clone root, and its log is next to it. Nothing in the clone was edited.

## Verdict

**The definition is sound and does what it is meant to do. Fix V3-S2-KS-M1 before merge.**

- **Not too weak.** The paper theorem holds for the exact Lean text. `PaperTheorem.lean` proves
  it in the kernel for a lazily sampled random oracle: `Probe.paper` shows that the probability
  of an accepted proof the extractor cannot open is at most `n · ε`, for every game that asks at
  most `n ≤ logCap` queries. It uses only the standard three axioms. No certification of an
  unsound verifier was found. Every hypothesis of `KState` either carries load or is harmless:
  two of them are redundant, which is m3.
- **Not too strong.** `twoLucky` and `Vcol` separate the old form from the new, and both are
  kernel-checked. The potential of an honest Merkle plus Fiat–Shamir verifier, sketched below,
  fits under `2^-128`.
- **One major finding.** The value `logCap = 2^64` is justified in the trusted header and in the
  ledger by a sentence that is false. With that value, a verifier whose soundness rests on
  192-bit collision resistance, which is 96-bit generic security, is certified at
  `errorCap = 2^-128`. The kernel proof is `Probe.v24_ks`.

## Evidence

| Check | Result | Log |
|---|---|---|
| `timeout 1800 lake build` (warm) | 1255 jobs, green, 2.7 s | `build.log` |
| `lake build gate axiomaudit && lake exe axiomaudit` | PASS; `Controls.Potential`: 66 declarations audited | `axiomaudit.log` |
| `scripts/check-hygiene.sh` | OK | (terminal) |
| `scripts/loc.py` over the contract (the CI command) | 331 code lines (budget 500); `Security.lean` 26 | (terminal) |
| `PaperTheorem.lean`: `Probe.paper` | `[propext, Classical.choice, Quot.sound]`, 6.1 s | `PaperTheorem.log` |
| `Truncated.lean`: `Probe.v24_ks` | `[propext, Classical.choice, Quot.sound]`, 5.7 s | `Truncated.log` |
| `Redundant.lean`: `Probe.final_unguarded`, `Probe.step_unstopped` | standard three, 5.3 s | `Redundant.log` |
| `Snag.lean`: naive proofs about `Fintype.card Digest` | each fails fast and deterministically (5.6 s for the file) | `Snag.log` |

## Pass A: specification

### 1. Too weak? The paper theorem against the exact text

`PaperTheorem.lean` defines `prob B p L`. This is the probability that a query program `p`,
started with table `L`, ends in a leaf `(x, L')` with `B x L'`. A fresh query is answered
uniformly over `Digest` and recorded. A repeated query reads the table through `find?`, by first
match, which is exactly what `runLog` does. This is the random oracle by lazy sampling. The game
`G` is the adversary followed by the verifier's queries, so `n = Q + qV`. The leaf predicate is
`(V c π).runLog L' = some true ∧ ¬ ∃ w, E c π L' = some w ∧ R c w`. The proof is the header's
argument, mechanised:

- **`pot_le`.** The stopped and capped potential, `min 1 μ` frozen once `μ ≥ 1`, rises by at most
  `ε` per query in expectation.
  - A repeated query costs nothing.
  - A fresh query uses `step`. Its hypotheses are met: `L.length < logCap` follows from
    `L.length + n ≤ logCap` with `n ≥ 1`, `μ L < 1` holds because the potential is not yet
    stopped, and freshness holds because `find? = none`.
- **`prob_le_pot`.** At a leaf within `logCap`, failure forces `μ ≥ 1`. That is the contrapositive
  of `final`. Its hypothesis `L.length ≤ logCap` matches `step`'s strict guard, one entry longer.
- **`paper`.** Combines the two with `μ [] = 0` (`empty`).

The specific worries in the request, each checked:

- **`μ ≥ 1` escaping `step` and `final`.** This is intended, and the stopping makes it sound. A
  log with `μ ≥ 1` is charged in full (capped at `1`) at the moment it is reached. Afterwards
  nothing is required of it.
- **Huge `μ` values.** `step` only bounds an average, and the theorem uses `min 1 μ`. A potential
  that jumps to `2^300` on one answer pays `2^300 / 2^256` in that average, so it cannot hide
  mass. `ℝ≥0` has no `⊤`, so there is no absorbing value to exploit.
- **`<` in `step` against `≤` in `final`.** These are consistent. The last fresh query goes from
  length `logCap − 1` to `logCap`, and `final` covers the result.
- **Repeated queries and first-match lookup.** Logs built by the game hold fresh queries only, so
  first match is the oracle's answer. On unreachable logs with duplicates, `final` is stronger,
  but costs nothing: `μ := 1` there is free, because `step` never leads into such a log.
- **The verifier's own queries.** They are in the game, so they are counted in `n` and charged.
- **The `Fintype` instance.**
  - `Fintype` is a subsingleton, and every instance's `univ` is the full, duplicate-free
    `Finset`. So neither `∑ a : Digest` nor `Fintype.card Digest` (which `fintype_card_digest`
    proves is `2^256`) depends on the instance.
  - The statement is elaborated in the contract with the contract's instance. A submitter's
    local instance cannot change the rendered claim, which the comparator checks.
  - Competing instances do exist in pinned packages: CompPoly `Data.Bytes.Bias`, VCVio
    `SampleableType.Basic` and ArkLib `OracleReduction.Prelude` each declare
    `Fintype (Vector UInt8 n)`. None is on the v2 import allowlist today. See m4.
- **`ε` as a structure parameter.**
  - `Certificate.secure : KS (Rel S.Vb) S.V S.E S.ε S.qV` builds `KState … S.ε`.
  - `cap` bounds `S.ε ≤ errorCap`, and `CertificateR.bounds` gives `S.ε ≤ D.ε`.
  - `KState.mono` makes the declared bound monotone, which is correct: a larger declared error is
    a weaker claim.
  - `acceptAll_no_certificate` now reads `h.secure.1.some` at `S.ε`, which is right.

What `paper` does not cover is unchanged from S1, and the header states it: the step from lazy
sampling to a random function, which is standard, and randomised adversaries, which follow from
the deterministic case by averaging over coins.

Attempts at an unsound certificate all failed:

- **Avoiding the charge with a potential.** No μ escapes `paper`.
- **Order-dependent potentials.** `paper` holds for every `μ`.
- **Statements chosen after seeing the answers.** `final` quantifies `c`.

The only weakening found is the guard's value, M1.

### 2. Too strong? An honest Merkle plus Fiat–Shamir verifier

The potential for a BCS-style verifier, F1 §4.5, re-checked against the text. Here `μ L = 1` if
`L` contains one of the following. Otherwise `μ L` is the sum, over the Fiat–Shamir transcripts
present in `L`, of the IOP's round-by-round doom value.

- **A collision.** Two distinct queries, in formats the verifier compares, with equal answers.
  For a fresh query this costs at most `|L| / 2^256 < 2^-192`.
- **A late preimage.** A fresh answer equal to a digest that some earlier query contains as a
  child or root. A query in the verifier's formats holds at most `proofCap / 32 = 2^15`
  digests, if `V` rejects proofs over `proofCap` itself. That gives at most `2^15 · |L|` targets,
  so the cost is below `2^-177`.

The doom value is `0` or `1` in algebraic rounds. In the query phase it is
`w_j = (1−δ)^{t(1 − j/k)}` after `j` missed position answers out of `k`. Each fresh query feeds one
transcript, since the Fiat–Shamir encoding is injective and domain-separated. The first position
answer of a transcript raises the average by `(1−δ)^t`. Later ones form a martingale, which is the
`twoLucky` pattern at `k = 2`. A new transcript's opening challenge adds at most its
round-by-round error. Logs with duplicate queries get `μ := 1` for free.

Total per query: `(1−δ)^t + d/|Ext3| + 2^-177 + 2^-192 ≤ 2^-128` with `(1−δ)^t ≤ 2^-129` and
`|Ext3| = 2^192`. **This is satisfiable.** It is a paper check, since no full BCS potential is
built; F1 §5 is the plan for that.

The controls really separate the forms, all kernel-checked with the standard three axioms in the
audit:

- `twoLucky_no_bool_kstate` holds even under `BoundedBelow`, against `twoLucky_ks` at the cap.
  This rules out every S1 state: S1's `Bounded` implies `BoundedBelow` (`Bounded.below`).
- `collision_no_bool_kstate` (S1 `Bounded`) against `collision_ks` shows that the guard admits
  `Vcol`.

### 3. Findings

#### V3-S2-KS-M1 (major): `logCap = 2^64` rests on a false justification, and certifies a 96-bit-secure verifier at the 128-bit cap

**Where.**

- `Contract/Security.lean`, the header's "Why the length guard": "the theorem says nothing once
  `Q + qV ≥ 1 / ε` anyway".
- `docs/DESIGN-AMENDMENTS.md` V3-KS-A2: "while the theorem says nothing once
  `Q + qV ≥ 1/ε`".

**What is wrong.** At `ε = errorCap`, `1/ε = 2^128`, not `2^64`.

- Under S1 the bound `(Q + qV)·ε` held for every `Q`. At `Q = 2^100` it said `≤ 2^-28`.
- With the guard, nothing is said for `2^64 < Q + qV < 2^128`. The guard removes a non-trivial
  part of the claim, and the header presents it as cutting off only the trivial part.
- The cost is concrete. Within the guard, the charge for a collision-type event over `t` bits is
  `|L| · 2^-t ≤ 2^64 · 2^-t`, which fits `2^-128` from `t = 192` up. A birthday search breaks
  such an event with about `2^(t/2) = 2^96` queries.

**Probe.** `Truncated.lean` defines `V24`, which accepts two distinct queries whose answers agree
on their first 24 bytes. The state "answers distinct on 24 bytes" has at most
`|L| · 2^64 < 2^128` bad answers within the guard (`card_bad`, `bool24_below`). So
`v24_ks : KS (fun _ _ => False) V24 (fun _ _ _ => none) errorCap 2` holds, through
`KState.ofBool`.

**What this means for entries.** An entry that compares Merkle nodes on 24 bytes, with smaller
proofs and so a faster score, is certified at "2^-128". At `Q = 2^64` the design's own §4.5 target
(`≤ 2^-64`) still holds for it. But the scale beyond `2^64`, which S1's text gave, is gone, and
nothing says so.

**Fix.** Do both.

1. **Correct the text** in the header and in A2. The guard limits the claim to
   `Q + qV ≤ logCap`. At the caps it gives advantage `≤ 2^-64` at `2^64` queries, and it says
   nothing beyond `logCap`. Name the consequence: collision-type events of `≥ 192` bits are
   chargeable at `errorCap`. Cite `v24`, or add it as a control.
2. **Record a decision on `logCap` (O-21).** The honest-design arithmetic in §2 above leaves a
   wide margin.
   - **`logCap = 2^96`** costs an honest Merkle plus Fiat–Shamir verifier about
     `2^15 · 2^96 / 2^256 = 2^-145` per query. That leaves the IOP its `2^-129`, and raises the
     truncation floor to `t ≥ 224`, a birthday cost of `2^112`.
   - **`2^110`** still leaves about `2^-131`.
   - **`2^128`**, the value the current sentence implies, leaves nothing (F1 §4.1, third row).

   Changing the value moves only `colBool_below` (`2^-192` becomes `2^-160` at `2^96`) and the
   §4.5 and §6.6 quotes. If the user keeps `2^64`, the RESULT, the ledger and `AGENTS.md` should
   state the operating point, `(2^64, 2^-64)`, and stop calling `errorCap` "128-bit".

#### V3-S2-KS-m1 (minor): no control shows that the guard carries load for the contract's `KState`

`Vcol` shows that the guard is needed for a **boolean** state (`collision_no_bool_kstate`), and
the RESULT says the potential case is not kernel-checked (its Open question 3).

For `Vcol` itself, a potential without the guard is borderline feasible at exactly `2^-128`.
Following the cheapest answer at each step, `g(n+1)(1 − n/N) ≤ g(n) + ε − n/N`. Its continuous
limit, in `u = n/(εN)` with `Nε² = 1`, is `g' = 1 − u(1 − g)`. That reaches `1` near `u ≈ 1.27`,
which is F1's "exactly one solution at Δ = 1". So `Vcol` cannot be the control for the potential.

**Fix, or record why not.** The answer to Open question 3: the boolean witness does not show it. A
control that would is `V31`: equal answers on 31 bytes, so `Nε² = 2^-8`. Without the guard, the same
recursion keeps `g` small until `n/N > ε`, after which `step` fails. This is an estimate, not
kernel-checked. With the guard it is
`ofBool` at `2^-184`. If that is not built, state in the RESULT that the guard's necessity for
the potential rests on F1 §4.1 (paper, `Δ ≥ 2`).

#### V3-S2-KS-m2 (minor): the `Fintype Digest` instance makes naive goals fail with "maximum recursion depth"

The RESULT records this snag. The probes add to it:

- **More tactics trigger it.** It fires on `positivity` when the goal contains
  `(Fintype.card Digest : ℝ≥0)`, on `gcongr` under `∑ a : Digest`, and on an `exact` whose
  defeq check unfolds a local abbreviation of the card. The error's pretty-printer can itself
  fail with "maximum recursion depth" (`PaperTheorem.lean` drafts). `Redundant.lean` needed
  `bot_le` instead of `positivity`.
- **`rfl`, `by rfl` and `by decide` on `Fintype.card Digest = 2^256`** each fail with the same
  error (`Snag.log`).
- **A related heartbeat timeout.** A `show` in `Truncated.lean`, which forced an unfolding
  through `digestEquiv`, hit the 200 000-heartbeat limit (`(deterministic) timeout at whnf`). The
  failing draft of the file took 27.4 s, against 5.7 s for the final version.

**Harness risk: low.** Every failure is deterministic and bounded by `maxRecDepth` or
`maxHeartbeats`. `check-hygiene.sh` forbids raising either in an entry. A wrong certificate is
therefore rejected with an error, even if a confusing one, and never hangs the elaborator. The
kernel only re-checks terms the elaborator built.

**Fix.**

1. Answer Open question 1 with the literal: write `(μ L + ε) * 2 ^ 256` in `step`. That removes
   `Fintype.card Digest` from every `step` goal a submitter meets. `fintype_card_digest` stays
   in the library as the check that the literal is the count.
2. Add one library lemma that restates `step` with `2^256`, plus a `@[simp]`
   `fintype_card_digest`.
3. Add a sentence in `AGENTS.md` naming the tactics to avoid on that term.

Do not make the instance irreducible; the RESULT also declines this, rightly.

#### V3-S2-KS-m3 (minor): two `KState` hypotheses are redundant

`Redundant.lean` proves both in the kernel:

- **`final_unguarded`.** From every `KState` one gets a potential satisfying `final` on logs of
  every length: set `μ := 1` above `logCap`. `step` never reaches those logs.
- **`step_unstopped`.** One also gets a potential satisfying `step` without `μ L < 1`: stop at
  `1` once a prefix reaches it.

So the only load-bearing restriction of the amendment is `step`'s `L.length < logCap`.

This is not a defect. Both hypotheses spare the submitter work, and the trusted text is easier to
read as written. But the header's list of laws suggests three guards, and the controls header
says `ks1` exercises "the `μ < 1` hypothesis" (of `final`, correctly).

**Fix.** Either keep both and add one sentence to the header ("`final`'s length bound and `step`'s
`μ L < 1` only spare the submitter a stopping argument; they do not weaken the theorem"), or drop
`final`'s `L.length ≤ logCap`, which saves a hypothesis from the trusted text.

#### V3-S2-KS-m4 (minor): the `Fintype (Vector UInt8 n)` diamond with pinned packages

`Digest` is `abbrev Vector UInt8 32`, so the contract's instance is a global
`Fintype (Vector UInt8 32)`. The following pinned packages each declare a different one:

- CompPoly `Data/Bytes/Bias.lean` (`instFintypeVectorUInt8`);
- VCVio `SampleableType/Basic.lean` (`instFintypeVector`);
- ArkLib `OracleReduction/Prelude.lean` (`Vector.instFintype`).

None is on the v2 allowlist (`docs/core/import-allowlist.txt` lists 29 CompPoly modules, not
`Bytes.Bias`). Since `Fintype` is a subsingleton, this does not affect soundness. But once S2's
regenerated allowlist, or a VCVio bridge (§9.1), admits one of them, rewriting with that
package's `card_vector_uint8` against a contract goal will meet m2's unfolding.

**Fix.** Record this in the allowlist regeneration notes, and keep the library's
`fintype_card_digest` as the lemma entries use.

#### V3-S2-KS-m5 (minor): stale documents

- **The core's `docs/DESIGN-v3.md`.** §1.1 figure, §4.1, the §4.2 code block and its reading, and
  §4.5 now contradict the contract. The project rule says to report a design that disagrees with
  the contract. The ledger carries the replacement wording, and the RESULT explains why the agent
  could not edit the design. The orchestrator must patch it (and the master) in the same pull
  request or the next one, not leave it.
- **This repository's `AGENTS.md` §4 and `docs/baseline/BASELINE-TASK.md` §0, §5.** These follow
  the pin move (V3-KS-A5).

#### V3-S2-KS-m6 (minor): library lemmas with no use and no control

`BoolKState.one_le_of_bounded`, `BoolKState.Bounded.mono`, `BoolKState.bounded_of_not_bad` and
`KState.ofBool_μ_eq_zero` are not used anywhere (checked with grep over `RecursionFast/` and
`scripts/`). The library is untrusted, so this costs no trust. But S1's `bounded_ge_one` used
`one_le_of_bounded`, and its port went to `jumpAll_ge_one` on potentials.

**Fix.** Either delete them, or add the boolean-form control: `bounded_ge_one` on `BoolKState`,
which keeps S1's statement verbatim.

## Pass B: fidelity

Not applicable: nothing is transcribed from a pinned implementation. Instead, the S1 controls
were checked for preserved meaning, one by one against `git diff`:

| S1 control | Ported | Meaning kept? |
|---|---|---|
| `ws_ks`, `ws_kstate_trivial`, `ws_complete` | `μ = 0` (`rfl`), `KState.zero 0` | yes |
| `rejectAll_ks`, `rejectAll_not_complete` | `KState.zero 0` | yes |
| `acceptAll_kstate_iff`, `acceptAll_no_kstate_empty`, `_none` | now `∀ ε` | yes, and stronger |
| `queryThenAccept_ge_one` (S1 M2) | `final` forces `μ = 1` on each `[(q, a)]`, `one_le_of_jump` | yes. The `Bounded` hypothesis disappears because `ε` is the parameter |
| `ks1` | the potential `jump` at `ε = 1` | yes |
| `bounded_ge_one`, `badAll`, `badAll_not_capped` | `jumpAll_ge_one`, `badAll` at `ε = 1`, `badAll_not_capped` for every `k` with `badAll`'s `μ` | yes, for potentials (boolean original: m6) |
| `oneQuery_not_KS`, the `Certificate` controls | unchanged (one `.choose` → `.some`) | yes |
| `Backdoor.backdoor` | `boolState` is S1's `kstate` verbatim, renamed; `KState.ofBool … bounded.below` | yes. O-25 unchanged |

`BoolKState` and `BoolKState.Bounded` are S1's `KState` and `KState.Bounded` verbatim, checked
against the `-` lines of the diff and against DESIGN-v3 §4.2. `KState.ofBool` is a faithful
embedding:

- `μ L < 1` holds exactly on the good logs (`ofBool_μ_eq_zero`).
- `step` follows through `step_of_hits` with the hit set `filter (bad L q)`.
- `final` follows from the good-log case.
- It takes `BoundedBelow`, which is weaker than S1's `Bounded`, so every S1 state embeds.

"Nothing a submitter could do before is lost" is therefore kernel-checked.

`WitnessSending.kstate := KState.zero 0 …` gives the same `final` argument (`check_sound`) as S1.

## Pass C: hygiene and trust

- **Trusted base.**
  - The contract grows by 3 code lines, to 331 of 500. Only `Contract/Security.lean` changed.
    `Certificate.lean` elaborates unchanged.
  - The new trusted content is one instance, whose content is irrelevant because `Fintype` is a
    subsingleton, plus `logCap` and the restated structure.
  - No new attribute and no option change.
- **Docstrings.**
  - They are accurate, and say what, not how, apart from M1's sentence.
  - The instance's parenthesis "(Every `Fintype` instance lists each digest exactly once.)" is a
    why. That is acceptable: it is the reason the instance carries no trust.
  - The header's paper theorem now matches `Probe.paper` step for step.
  - Nit: `q₁` and `q₂` in `Controls/Potential.lean` share the docstring "The two queries."
- **Gate and harness.**
  - `KS` is a `Prop` (`Nonempty`), so the instance and `μ` are not on the badge path. Gate rule 4
    (computability) is unaffected.
  - The elaboration snag (m2) is deterministic and bounded. A wrong certificate fails with
    "maximum recursion depth" or a heartbeat timeout, never with a hang. The comparator's
    kernel replay only sees terms that elaborated.
  - S3's comparator should still run under a wall-clock timeout, as it already must for any
    entry.
- **Build and audit.** Both green (Evidence table). The RESULT's measurements are in this
  repository's `logs/ks-amendment/`; they were not re-measured cold here.

## Lean4 review summary (Layer 1)

| Area | Status |
|---|---|
| Build | green (`build.log`) |
| `sorry` audit | none (hygiene OK) |
| Axioms | standard three only (`axiomaudit.log`, PASS) |
| Style | 100-column lines respected. `Controls/Potential.lean` is 297 code lines, and `luckyEquiv` (about 20 lines) could be shortened through `Fin.appendEquiv` alone, which is a golf item |
| Advisory (mathlib-style) | `digestEquiv` duplicates `Equiv.vectorEquivFin`-style API that Mathlib has for `List.Vector`, not for core `Vector`; nothing to upstream here |

## Disposition requested from the fix pass

| Id | Requested |
|---|---|
| M1 | correct the header and the A2 justification; decide `logCap` (recommend `2^96`) or document the `(2^64, 2^-64)` operating point; add `v24` as a control either way |
| m1 | `V31` control, or a RESULT sentence that the potential case rests on F1 §4.1 |
| m2 | `2 ^ 256` literal in `step` (Open question 1), library `step` restatement, `AGENTS.md` note |
| m3 | header sentence, or drop `final`'s length hypothesis |
| m4 | allowlist note |
| m5 | patch DESIGN-v3 (core and master); follow-up in this repository after the pin move |
| m6 | delete, or add the boolean `bounded_ge_one` control |
