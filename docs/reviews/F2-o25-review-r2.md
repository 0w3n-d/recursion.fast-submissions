# F2-o25 review, round 2: adversarial review of Candidate T (O-25, core issue #4)

## 0. Scope, probe and verdict summary

**Reviewed.** Round 2 of `docs/snark-baseline/notes/F2-o25-uninstantiability.md` (R2.0–R2.11,
Candidate T), with round 1 and `docs/reviews/F2-o25-review.md` (O25-M1…M6) as context. I read it
against three sources:

- the core rules stage `recursion.fast-rules` at `4b3356a` (`v3/rules-handoff`): `Contract/*.lean`,
  `docs/stages/V3-S2R-RESULT.md` and `docs/DESIGN-v3.md` §5;
- the honest entry `submissions/spartan-chain/`, in particular `SpartanChainVerifierTop.lean`,
  `SpartanChainVerifier.lean`, `SpartanChainSpartanProtocol.lean`, `SpartanChainChainEval.lean`,
  `SpartanChainChainMle.lean`, `SpartanChainSoundnessKS.lean` and `docs/snark-baseline/REPORT.md`;
- `docs/snark-baseline/issues/I4-honest-recursion-feasibility.md`, `docs/design/DISCUSSION.md` Q6,
  `.contract/RecursionFast/Controls/Backdoor.lean`, ADV-M5 and the user's literature list.

I did not write the design. I did not review round 1.

Two contract changes since the memo was written apply throughout:

- The extractor is now an `XProg` of the step-counting machine with `Computes p E fuel` (no image).
- Completeness is `CompleteWithError` over a lazily sampled random oracle, with
  `δ ≤ completenessCap = 2^-128`.

Wherever the memo writes `img`/`ImageComputes`, read `ext`/`Computes`.

**Probe.** `/home/devops/Verified-zkEVM/rf-core-sc/scratch/o25t/T1_pub_sees.lean`, run with
`timeout 900 systemd-run --user --scope -p MemoryMax=8G lake env lean …` against the contract at
`05fde28`. Its log is `T1_pub_sees.log` next to it. Every theorem depends on `[propext,
Quot.sound]` only. The probe sketches T-1…T-4 literally:

- `UniformR1CS` with `wf : Bool` as a field;
- `Params`;
- `TSubmission` with `pub : Digest → ByteArray → Option (List F)`;
- `TSubmission.V := Template.verify S.params S.cs (S.pub c (preSeg π)) c π`;
- a toy organiser template: the seed query `0x10 ‖ c ‖ csDigest ‖ paramsDigest ‖ x`, absorb the
  root, squeeze `τ`, then fixed checks.

| Theorem | What it shows |
|---|---|
| `pubTau_eq_challenge` (`rfl`) | A `pub` of exactly the T-3 type computes, from `(c, preSeg π)` alone, **the challenge `τ` the template consumes** in deployment. |
| `evil_Vb` | A legal `TSubmission` whose deployed `Vb` branches on that challenge through `pub`. Here it rejects when byte 0 of `τ` is zero. |
| `example : csIllFormed.wf = true` | The memo's "well-formedness decided by the contract" is decided by the submitter. |
| `postHoc_iff` | In a constraint language with a challenge term and later-phase columns, the last line of the post-hoc attack, `α = w₀`, is **data**. |

**Verdict in one paragraph.** T is the first proposal in this line that actually removes the
CGH98/`Backdoor.lean` mechanism from submission-authored code. The reason is structural:

- every **check** that reads an oracle answer is organiser code;
- every submission-supplied input to such a check (`cs`, `x`) is fixed before the first oracle
  answer, because the seed binds it.

So a Backdoor-, ADV-M5-, O25-M1…M5- or post-hoc-style comparison has nowhere to live in a submission.
That part survives this review.

The memo, however, states the wrong invariant, overstates what it buys, and specifies a T that
cannot hold the only honest entry:

- **INV is false as written** (O25T-M1, kernel probe). `pub`, and the node witness, can compute
  outer transcript values, and `pub` can reject on them. The harm is limited to liveness, as
  argued in §3, but the security argument must be re-founded on a *check-operand* invariant.
- **The constraint-system menu has no admissibility rule** (O25T-M2). The first lookup, AIR or
  multi-phase menu item would reopen the post-hoc attack as data.
- **T-1/T-3 cannot express spartan-chain** (O25T-M3). Its matrices depend on `n` and on
  `κ = ⌈log₂ n⌉`, and T has no node branch. With a fixed `k` every leaf is too large for
  `proofCap`.
- **The ranked board under T is empty at launch** (O25T-M4). Ligero leaves at `n = 2^14` exceed
  `proofCap`. Self-verifying recursion with one `cs` is an unsolved design problem that R2.6 does
  not see.
- **The template-proposal process re-imports the unwinnable per-entry review at the template
  level** (O25T-M5). It needs a mechanical anchor.
- **T reverses three of DISCUSSION Q6's decisions** (O25T-M6). It is narrower than the v2 the user
  rejected, so it must go to the user as a reversal.

**Verdict: adopt T's core (a contract-owned composition over first-order, seed-bound data) as the
O-25 closure, but not as specified.** Fix M1–M5 first, and put M6 to the user with the wider
middle ground of §5.

## 1. Major findings

### O25T-M1. INV is false as stated: submission code can compute outer transcript values. Re-found T on a check-operand invariant.

*Attack (kernel-checked, probe T1).* R2.1 states (INV): every function the submission authors "is
applied only to inputs that are independent of `Chal(π)`". `Chal(π)` includes "challenges,
positions, transcript states". R2.4(d) concludes that `pub` "cannot see challenges". R2.3 says that
"a 'reject exactly under BLAKE2s' branch has nowhere to live in `V`". All three are false.

`pub` is authored after `cs` and `params` are fixed. So it may hard-code `csDigest S.cs` and
`paramsDigest S.params` with no fixed point, because `pub` itself is not digested. It chooses its
output `x` first, and then evaluates BLAKE2s locally:

```lean
def pubTau (cs p c seg) : Digest :=
  blake2sOracle (absorbQ (blake2sOracle (seedQ c (csDigest cs) (paramsDigest p) honestX))
    (rootOfSeg seg))
theorem pubTau_eq_challenge (cs p c π) :
    pubTau cs p c (preSeg π) = tmplTau blake2sOracle cs p c honestX π := rfl
```

In deployment, `pub`'s local value **is** the first challenge the template consumes. `evil_Vb`
packages the result as a legal `TSubmission` whose `Vb` is
`if (tmplTau blake2sOracle … π).get 0 = 0 then false else …`. The inputs of `pub` are independent
of `Chal(π)` in the memo's sense, yet `pub` computes `Chal(π)`. The reason is that `Chal(π)` is a
public function of pre-segment data and of `pub`'s own output.

This holds whatever the template designates as `preSeg`:

- if `preSeg` holds the root, `pub` gets `τ`;
- if `preSeg` is only the header, `pub` still gets the seed answer, a transcript state.

The same holds for the constraint system. A node witness can contain wires computing the outer
seed answer `H(0x10 ‖ c ‖ csd ‖ pd ‖ x)` from its own public input `x`, which is not under the root.
With `csd` supplied through `x`, there is no fixed point.

*What it breaks.* Not acceptance, as far as I can find (§3 gives the argument). `pub`'s codomain is
`Option (List F)`:

- `none` rejects;
- `some x` enters the seed. `x` can encode `τ(x₀)` for a candidate `x₀ ≠ x` but never `τ(x)`. That
  would be a fixed point of BLAKE2s.

The template's ROM theorem is generic in `pub`, so `pub`'s choice of `x` is no more than an
adaptive statement choice, which the prover already has. It does break:

1. The stated invariant, which R2.10 lists as "a property of the contract's definitions, checkable
   by reading `TSubmission.V`". A reviewer applying INV literally checks the wrong thing: the
   *inputs* of submission functions rather than the *operands of checks*.
2. The liveness claim. The "reject under BLAKE2s" branch of design §5.4 / O25-M6 lives in `pub`.
   Design §5.4 notes that it harms only its own submitter, so this is a griefing risk only for
   entries that share a `pub` (R2.2 offers "`pub := library default`").
3. The data-flow picture of R2.3/R2.4, which T's justification rests on. "The submission cannot see
   the challenges" is not why T works.

*Smallest fix.*

(a) Replace INV with what actually holds, and what the review must check:

> **(INV′)** Every check in `Vb` whose operands include an oracle answer, or a value computed from
> one, is organiser code. Every submission-authored value that reaches such a check (`cs` data,
> `params`, `x`) is fixed before the seed query and is bound by it. No submission-authored
> function is evaluated on anything the prover writes after the seed.

(b) Make `x` a **contract-fixed injective map** of `(c, header bytes)`, a length-prefixed list of
canonical field encodings. Move every statement check, such as `c = leafStmt h n`, into `cs`. This
removes `pub` from the verification path entirely, and with it the liveness channel and the
`T_V`-priced Lean code. If `pub` is kept, state its liveness power in §5.4 and forbid shared `pub`s.

(c) Put the seed query in the **contract's** composition, not in the library: `V := .query (seedQ c
(csDigest cs) (paramsDigest p) x) (Template.verifyFrom p cs x c π)`. The `cs`/`params` binding is
invisible to the ROM (`cs` is fixed per submission, so `KS` cannot require it), so only the
contract can enforce it (m5).

### O25T-M2. The constraint-system menu has no admissibility rule. Lookups, AIR challenges or multi-phase witnesses reopen the post-hoc attack as data.

*Attack.* T works for single-phase Spartan for one reason: the constraints apply only to `z`, which
is committed before every challenge, and data enters checks only as fixed polynomials evaluated at
challenge points. That is why the post-hoc attack (§R2.1) cannot be written. The BLAKE2s wires of
`prefix₁` would have to be *checked*, and the only data-defined checks act on pre-challenge
commitments.

The memo invites the features that break this: "`CCS`/`AIR` later", "lookup tables … consumed by
the template's lookup argument" (R2.2, R2.4(b)), "menu items with later commitments" (R2.4(c)). It
states only "no function-typed field" and "no post-challenge message influences `x` or `cs`".
Neither excludes the following, which is the standard shape of LogUp / permutation AIRs and of
halo2's `challenge_usable_after`:

- a constraint language with a **challenge term**; and
- **phase-2 columns** committed after a challenge.

Probe T1's `postHoc` is data with no function field:

```lean
def postHoc : List Gate := [⟨.chal, .const 1, .col 0⟩]
theorem postHoc_iff (w α) : holds postHoc w α ↔ α = w 0
```

Extended to "phase-2 columns 1… hold the BLAKE2s wires of the phase-1 root and the transcript
prefix, and `α = Σ outbitᵢ βⁱ` holds", it is the post-hoc attack verbatim. In the ROM it holds with
probability `2^-192`; in deployment it always holds. Wrapped as `real ∨ trigger` (the same
`KState` accounting as `Backdoor.lean`), it accepts a magic proof.

A library KS theorem "generic in `cs`" over such a language either:

- does not exist (the library author cannot prove it for every `cs`, so the entry is not
  certified); or
- is proved with exactly that probability accounting, in which case the entry **is** certified and
  the backdoor is in.

*What it breaks.* R2.4(b)/(c)'s conclusion "with first-order data there is nothing to apply to a
challenge". First-order data interpreted by a template that *applies it to challenges and to later
commitments* is code in the challenge path. INV′ is a property of the *template's interpretation*
of the data, not of the data's Lean type.

*Smallest fix.* A written admissibility rule in the contract header and the template-proposal
checklist (§5). Every menu datatype is interpreted so that:

- (A1) data-defined functions are evaluated only at (i) verifier challenges, and (ii) evaluations
  of oracles committed **before** those challenges and bound by the PCS;
- (A2) no data-defined function or constraint mentions a challenge as a coefficient or variable,
  or constrains a column committed after any challenge;
- (A3) every multi-round sub-protocol (lookup, permutation, grand product, GKR, memory checking)
  is a template-authored gadget whose challenge-using constraints are fixed code, and the data only
  names which pre-challenge columns enter it;
- (A4) no datatype is an interpreter: there is no loop, branch or table whose input is a
  challenge-derived value, and data-defined functions are polynomials of a degree fixed by the
  template.

`UniformR1CS` with single-phase Spartan satisfies A1–A4. Halo2-style challenge APIs and
"AIR with permutation trace and `eval` access to challenges" do not.

### O25T-M3. T-1/T-3 cannot express the honest entry. R2.7's "re-partition, not rewrite" is false.

*Attack (code reading).* spartan-chain's leaf constraint system is **statement-dependent**:

- `SpartanChainVerifier.lean:73` sets `κ := kap n` with `kap n = Nat.clog 2 n` (`:39`), so the
  matrix dimensions depend on the statement's `n`;
- `SpartanChainChain.lean:74` has `chainA (n κ)`, and `SpartanChainChainMle.lean:294–301`'s
  `closedA` contains the term `eqv (shiftPt S 14) κ (n - 1)`. The output check against `h` sits at
  block `n − 1`, a statement-dependent position. It also has non-block rows (`eqv R 14 512`, the
  rows `64`/`65` region) for the public `s`/`h` wiring;
- the verifier's `Evals` is a pair of **functions**
  `mats : List EF → List EF → EF × EF × EF` and `pub : List EF → EF`
  (`SpartanChainSpartanProtocol.lean:130–133`), applied at `(rx, ry)` in `check` (`:160`). Today
  they are submission-authored closed forms.

T-1's `UniformR1CS` has fixed `s m k`, one block, a chain map and block-0 `pubSlots`. It cannot
express "the output row is at block `n − 1`", nor a `κ` chosen per statement. T-3 has one `cs`
and `V := Template.verify …`, with **no node branch**. The "library node template (concatenation
node)" of R2.7 is not in T-4.

There are two ways to force spartan-chain into T-1, and both fail:

- **Pad to `k = 20`** (`chainCap = 2^20`; `CompleteWithError` quantifies over every `n ≤ 2^20`).
  Every leaf proof is then a `2^20`-block proof. That costs 64× the prover work at the ranked
  `n = 2^14`. The Ligero proof is already 1.46 MiB at `2^14` (REPORT §2, measured), so it exceeds
  `proofCap`: completeness fails and the entry is **uncertifiable**.
- **One submission per `n`.** Impossible: the relation is fixed.

*What it breaks.* R2.7's claims "the first `UniformR1CS` instance", "re-partition of the existing
entry … not a rewrite" and "`chainMats_eq` its first correctness instance". The memo's migration
cost picture, and its claim that T is ready to land behind `v3/ks-potential`.

*Smallest fix.*

- The datatype gets a **statement-indexed family**: `k` and the active length read from fixed slots
  of `x`, and an "output tie at block `n − 1`" read from `x`. The evaluator stays generic, with
  `O(nnz(block) + k)` closed forms (spartan-chain's `walkAB` + `closedA` shape).
- T-4 gets a contract-owned dispatch: tag 0 goes to the template, tag 1 to the concatenation node
  over `Vb`.
- Restate the migration as:
  - a new generic evaluator and its correctness theorem for that family;
  - a new generic **knowledge** extractor (m4);
  - the chain soundness kept as `cs_implies_rel`.

Each added datatype feature must then pass M2's A1–A4: an index read from `x` is pre-seed and
bound, which is fine.

### O25T-M4. Under T the ranked board is empty at launch, and self-verifying recursion with one `cs` is an unsolved design problem that R2.6 does not see.

*Attack.* Three facts combine.

1. **The launch template cannot produce a rankable proof.** REPORT §2 (measured): at `n = 2^14`
   the Spartan+Ligero leaf is 1,464,107 B, above `proofCap = 2^20`. Leaves fit only up to
   `n = 4,096`. Concatenation nodes grow linearly, and the depth-8 root of 256 leaves fits only for
   leaves under 4 KiB. I4 (1) puts Ligero/Brakedown at `≥ 25 MiB` for a node circuit. Ranked T
   entries therefore need a WHIR-class template, which does not exist in Lean, plus full recursion.
2. **One `cs` must verify itself.** `Rel S.Vb`'s node clause recurses: a child may be a node
   (`Relation.lean`, `Rel … (.node …) := … Vb c₁ π₁ …`). T-3 has a single `cs`, and the template
   evaluates `Ã_cs(r_x, r_y)` for that same `cs`. A node circuit must therefore evaluate the MLE of
   **its own** matrices at the child's challenge point. With the generic sparse evaluator this
   costs at least `nnz(cs)` field multiplications, so at least `nnz(cs)` constraints, which a
   circuit with `nnz(cs)` non-zeros cannot afford: `|cs| ≥ |cs| + |rest|`. Self-verification closes
   only if evaluation is sublinear in `|cs|`:
   - **(i)** a small uniform block repeated `2^k` times, with the heterogeneous verifier logic
     selected per step from a fixed opcode schedule. That needs either per-block public inputs (not
     in T-1) or a template-owned memory-checking/lookup gadget (multi-phase, so M2 applies);
   - **(ii)** preprocessing (SPARK, a committed index). I4 (3) shows it is incompatible with the
     contract: under a random `H` the honest prover cannot open a BLAKE2s-computed index, and
     recomputing it exceeds `qV ≤ 2^16` and `T_V`.

   R2.9's "ADV-M6 … the template can own an indexer for `cs` (computed once at badge build under
   BLAKE2s), resolving it" is therefore unsupported. It is I4 (3)'s failure mode.
3. **`csDigest` cannot be a constant of the circuit that hashes it.** A node verifying a node child
   needs the child's seed, which contains `csDigest cs`. The node gets it through `x`. Inside the
   circuit it is unbound, but `x` is bound by the outer seed, and `pub` or the contract map pins it.
   That is fine, but it is one more datatype/`x`-layout feature R2.6 does not specify.

*What it breaks.*

- R2.6 point 2 ("the organiser can ship the recursion gadget … parametric in the leaf `cs`"):
  there is no separate leaf `cs`.
- R2.9's "re-partition, not rewrite" cost column.
- R2.10 item 2's implicit claim that T can rank anything soon after the library lands.

Under T-only ranking, **no entrant can be ranked until the organiser has built the entire honest
recursive SNARK**: a WHIR-class PCS with Lean KS, a uniform self-verifying node design, the
in-circuit verifier gadget and the decoder extractor. Competitors would then compete on provers
and on leaf arithmetisation for the organiser's circuits.

*Smallest fix.* State it in R2.5/R2.9 as a dependency: "ranked T requires the organiser's
WHIR-class template and a self-verifying node design (option (i), with its gadget under A3)
before launch". Until then, either:

- leave the board unranked; or
- rank on a measure T's launch template can meet. For example, rank leaves alone at a size that
  fits `proofCap`, which is a change to the score (V3-10) and the user's decision.

### O25T-M5. The template-proposal process re-imports the unwinnable review at the template level.

*Attack.* R2.5 lets anyone, including competitors, propose a template by core PR. Its
non-recognition is "assumed, by one-time review". ADV-M5.1 and the memo's own R2.10 ("rely on
review alone for ranked entries — what I would not do") establish that review cannot separate a
backdoored verifier from an honest one when the backdoor is a disguised comparison.

A template *is* a verifier: the organiser's code on the oracle path. So a competitor-proposed
template with a `LiteralTrigger`-style fast path (ADV-M5.3) faces exactly the review the memo
rejects for entries. It has a larger payoff: once merged, the proposer's own entry uses it, and
so does everyone else's. The memo offers no mechanical criterion for the template review, only
"adversarial review … must cover every module on the oracle path" (R2.11.2).

*What it breaks.* The claimed asymmetry between T and the status quo for every template after the
first, and the "~90%" of R2.10 for any season after launch.

*Smallest fix.* Give the review a mechanical anchor.

- **Each template = a short reference specification plus a kernel theorem `impl = spec`.** The
  spec is a readable decision function written from the paper's protocol: transcript order,
  checks, conjunction. Optimised code may differ but must be proved equal (spartan-chain already
  proves its fast twins equal to specifications, `packFast_eq`, `check_eq`). Recognition in the
  implementation then implies recognition in the spec, so **only the spec is reviewed**. Specs
  count toward the trusted-line budget.
- **The review checklist is enumerable.** It is (a)–(e) of §4.3 below: every local BLAKE2s call
  site, every comparison with an oracle-derived operand, data-dependent control flow, `extern` and
  `implemented_by`, and a pure conjunction of checks.
- **A proposer embargo.** A template proposed by an entrant becomes rankable only after a public
  challenge period and not in the season it is merged. This removes the first-mover payoff the
  memo names as the incentive (R2.5).

### O25T-M6. T reverses three of DISCUSSION Q6's decisions and is narrower than the v2 the user rejected. It must go to the user as a reversal.

*Attack (document reading).* Q6 (decided 2026-10-19) records:

- "The submitted object is the non-interactive argument itself … **No organiser compiler.**" Under T
  the submitted object is an R1CS and parameters for an organiser verifier.
- "The verifier's circuit and execution trace are the agent's internal matter." Under T the
  verifier is the organiser's, and R2.6 has the organiser ship the verifier gadget.
- "**Field-agnostic**: no field in the trusted base (removes v2's `Field`, `Shapes`, `Layout`,
  `Protocol`, `Compile`, `Recursion`)", together with the gripe that "fields are a large part of the
  cost" and that a fixed field "should not be a contract rule". T-1's `A B C : List (ℕ × ℕ × F)`
  and `pub : … → Option (List F)` put `F = EF` in the trusted datatype. Every ranked entry is
  fixed to `GF(2^192)` over `GF(2^64)`, and the field leaves the competition.
- The gripe that v2 "forces every agent through one configuration of the BCS transform". Under v2
  the agent still designed the **IOP** (DESIGN-v2 §3.1, "a holographic public-coin IOP"). Under T
  the agent designs neither IOP nor PCS. T is **strictly narrower than v2** in proof-system freedom.

The memo says T "is close to the v2 feature the user rejected". It is further from Q6 than v2 was.
Note also that v2's shape (agent IOP, organiser BCS) does **not** close O-25: the post-hoc attack
is IOP-sound and BLAKE2s-unsound. Design §5.4 already says v2 "had the same exposure through
recomputed Fiat–Shamir challenges". So the user cannot get O-25 closed by returning to v2 either.

*What it breaks.* The process. R2.10 recommends adopting T as an engineering decision. It is a
reversal of a recorded user decision, with a security reason, and must be presented as one.

*Smallest fix.* Put to the user, in Q-form:

- "O-25 can be closed by construction only by contract-owned composition (R2.3, O25T-M2)";
- the options: T as specified, the wider middle ground MG1 of §5 (agent-chosen arithmetisation
  format, PCS, field and compiler from an admissible menu), or keeping review for ranked entries;
- what each costs in freedom and in organiser work (O25T-M4).

## 2. Minor findings

### O25T-m1. `wf : Bool` is a structure field, so the submitter decides it

T-1 declares `wf : Bool -- well-formedness (bounds) decided by the contract`, and T-4 tests
`S.cs.wf`. Probe T1: `csIllFormed` has out-of-range indices and `wf := true`, and the test passes.

There is no soundness consequence, because `KS` of the actual `S` is still kernel-checked (m3). A
library theorem that assumes `cs.wf = true` cannot derive bounds from a free boolean. Still, it is
a specification slip of exactly the kind R2.11.1 asks the reviewer to hunt.

*Fix.* Use `def UniformR1CS.wf : UniformR1CS → Bool`, contract-owned. Do the same for any
"decided by the contract" predicate.

### O25T-m2. T-3 is out of date against the contract at `4b3356a`

| T-3 has | The contract has / needs |
|---|---|
| `img : Image` and `ImageComputes` | `ext : XProg` and `Computes ext E fuel` (V3-S2R-A1) |
| no `δ` | `δ` and `CompleteWithError` (V3-S2R-A2) |
| a contract line count of 331 | 288 (V3-S2R-RESULT §1.1) |

T-5's `decodeW : w' → Wit` is a submission function that T-3 does not list. The extractor needs
it, so it must be an `XProg` fragment with a step bound.

*Fix.* Re-state T-3/T-5 against `4b3356a`.

### O25T-m3. Hidden hypotheses in `Template.ks` cannot cause unsoundness. `Params.ok` is not needed for soundness. The `Template.ks` sketch is ill-typed.

The `Certificate` still demands `KS (Rel S.Vb) S.V S.E S.ε S.qV` of the actual `S`, and
`S.ε ≤ errorCap`. So:

- every hypothesis of `Template.ks` (well-formedness, `params.ok`, "honest-shaped `cs`") must be
  discharged in Lean for the actual data;
- a menu entry with `queries = 0`, a degenerate rate or an empty `cs` produces no certificate,
  because the `ε` cap fails.

R2.11.3's worry about a smuggled "honest-shaped `cs`" assumption therefore affects only
availability, not soundness. `Params.ok` and its table are redundant for soundness: they are
trusted lines that buy only early rejection. Keep them out of the contract, or keep them as
liveness sanity outside the trusted count.

The sketch `KState (fun c w => ∃ x, pub c … = some x ∧ CSsat cs x w') …` is ill-typed:

- the `KState` relation is over `Wit`, not over R1CS witnesses;
- `preSeg` is a function of `π`, not of `c`.

The correct shape is `R' c w := ∃ seg x w', pub c seg = some x ∧ CSsat cs x w' ∧ decodeW w' = some w`,
composed with `cs_implies_rel` quantified over all `seg`.

### O25T-m4. The generic KS is a new knowledge proof, not a generalisation

spartan-chain proves **soundness with a public witness**:

- the chain start `s` is in the header (`leafS`, `SpartanChainVerifierTop.lean:66`) and in the
  public input (`pubBit`, `SpartanChainChainEval.lean:38`);
- its potential is built on the false-statement predicate `FS es := chainEnd … ≠ …`
  (`SpartanChainSoundnessDefs.lean:269`), with `matA := chainA …` (`:307`);
- `EvalsOK` (`SpartanChainSoundnessKS.lean:151`) fixes the evaluators to the chain matrices.

A `Template.ks` for every `cs` with private witnesses needs three things it does not have:

- a decode-failure potential, not a false-statement potential;
- Merkle-tree recovery from the log;
- an RS decoder as an `XProg` in the step-counting language with a Lean-proved bound under
  `B t = 2^48 + 2^16·t`.

For leaves whose witness sits in `x` (spartan-chain's design), `E` is `decodeW ∘ x`. That is
per-submission, not "a generic decoder per PCS". R2.5's "(ii) is a generalisation of an existing
proof" understates the work. It does not affect security.

### O25T-m5. What `csDigest` binding does and does not do

*What it does.*

- It makes "data encoding a specific challenge value" a BLAKE2s fixed point, since every challenge
  is a function of `csDigest`. This is real, and it is what makes A1's "data-defined function
  evaluated at a challenge" safe. Without it, a table-like datatype could contain the challenge of a
  pre-chosen magic transcript.
- It implements Fenzi's fix (ePrint 2026/1838, abstract: "derive the first challenge from the
  generated statement … reduces soundness to the non-generated relation") **only if** the digest
  covers the instance the evaluator reads: the expanded family member, or `(family, index ∈ x)`.

*What it does not do.*

- It does not defeat KRS25 (ePrint 2025/118). That attack is on GKR-style arguments for every FS
  hash, and in KRS's setting the statement is already hashed. What blocks the KRS mechanism in a
  single-phase Spartan template is that **all** wires are committed before the first challenge. A
  circuit computing its own challenges would need a fixed point of `w ↦ root(w)`.
- It is ROM-invisible: `cs` is constant per submission, so `KS` cannot require the binding.

R2.8(2)'s "This defeats the known generated-relation attacks" should read: "Fenzi's class is
excluded by Fenzi's theorem, given that the seed binds the expanded instance. KRS's class is
excluded heuristically by single-phase commitment (A2). Neither is a proof for this template."

*Fix.* That wording, plus O25T-M1(c): the seed query belongs in the contract.

### O25T-m6. The tier separation is policy, not mechanism

`records.json` is `{"version": 1, "records": {}}`, with no tier field, and the S3 harness is not
built. R2.11.6 asks for the tier to be encoded but T's contract list does not include it.

*Fix.* Make it type-based. The ranked harness path accepts only a solution constant of type
`TSubmission`, with the certificate of its `toSubmission`, checked by the gate. Research entries
are `Submission`s and are never ranked. Add `tier` to `records.json`, written by the harness from
the gate's verdict.

### O25T-m7. The review target is misstated, and so is the trusted-base accounting

R2.5 calls the review "a few thousand lines". Proofs never run and need no non-recognition
review. The executable definitions in the verifier-side modules number about **910 lines**
across 19 modules, by my count of `def`/`structure`/`instance` bodies (`Oracle` 30, `Merkle` 64,
`Transcript` 61, `Sumcheck` 42, `Ligero` 100, `SpartanProtocol` 149, `MLE` 57, `RS` 34,
`RingSwitch` 32, `FieldBase` 79, `FieldExt` 54, `Verifier` 31, `VerifierTop` 57, `ChainEval` 21,
`ChainMle` 31, `Blake2sWalk` 20, `Decode` 48). Of these:

- prover-side and chain-specific definitions are a part;
- the verifier-side closure is roughly **500–900 lines** of Lean, plus the new generic evaluator;
- CompPoly's `BF64`/`Ext3` are reached at run time but pinned by spartan-chain's equality theorems.
  I found no `extern` or `implemented_by` in CompPoly at the shared package tree.

Conversely, the template is part of the **meaning** of every record: `Rel S.Vb` and the harness
run it. So T-4 makes the contract import it, or makes the challenge name it as organiser data. The
"60–90 contract lines" must be shown next to "≈0.5–0.9k template lines, trusted for meaning and
non-recognition".

My own contract estimate with M1(b), M3 and m6 included is **≈100–130 lines**, giving
≈390–420 of 500:

- the datatype with its family slots;
- the `wf` definition;
- `TSubmission`;
- the dispatch;
- the seed;
- an injective serialisation of `cs`/`params`/`x`;
- the `EF` import.

### O25T-m8. Instance sampling and liveness are lower-stakes under T than R2.8(4) says

The ranked shape is fixed and public: depth 8, `n = 2^14` (DESIGN-v3 §5.1). Starts are fresh per
evaluation. Under T every scored proof is checked by `Vb` anyway (the root and sample checks).
The only remaining liveness lever is `pub` (M1), and design §5.4 notes that it harms only its own
submitter.

A post-freeze beacon is needed only if the shape becomes secret. "Smoke on every scored instance"
is implied by scoring.

*Fix.* Downgrade R2.8(4) to: "harness-sampled fresh starts (existing); forbid shared `pub`s (or
remove `pub`, M1(b))".

### O25T-m9. Grinding is specified two ways

T-2 has `grind` as a submission `Params` field. R2.3/R2.8(6) say the template checks leading
zeros "against the contract constant". Either is sound, because `KS` prices it. But a reviewer
needs one rule.

*Fix.* Use the `Params` field, checked by template code. No submission code sees the statistic,
which is what O25-M4 required.

## 3. Channel audit of `TSubmission` (attack 1)

### 3.1 Field by field

"On the acceptance path" means that the field affects `Vb c π` for some `c`, `π`. "Sees
challenge-dependent data" means the field's code or data can be a function of an outer oracle
answer.

| Field | On the acceptance path? | Sees challenge-dependent data? | Channel and status |
|---|---|---|---|
| `cs` (data) | yes: the template evaluates `Ã, B̃, C̃` at `(r_x, r_y)` | data is applied **to** challenges by template code; its witness may compute the seed answer (M1) | Safe under A1–A4: a multilinear polynomial fixed before the seed, bound by `csDigest`, evaluated at challenges by organiser code. Unsafe as soon as the language has challenge terms or phase-2 columns (M2). |
| `params` (data) | yes: loop bounds, PCS choice | no | Soundness by kernel (m3). Non-recognition: the template review must cover **all** parameter values, including degenerate ones, not only the honest ones (§4.3 (c)). |
| `pub` | yes: `none` rejects; `x` enters the seed and `x̃(r_u)` | **computes** the seed answer and the first challenge (probe T1) | Acceptance: closed, argued in §3.2. Liveness: open (M1). Remove it, M1(b). |
| `P` | no (completeness only) | yes, as every prover does | Not a channel. INV's listing of "the prover" is wrong: provers compute on challenges by definition. |
| `E`, `ext`, `decodeW` | no (`final`, `Computes`; never run in deployment except on the harness's liveness log) | yes, the log | Not an acceptance channel. A misbehaving `ext` on the BLAKE2s log fails the harness's liveness check, which only harms the submitter. INV's listing of "the extractor" is wrong for the same reason as for `P`. |
| `ε`, `δ`, `qV`, `fuel` | no | no | Numbers bounded by caps. |

### 3.2 Why `pub`'s knowledge of challenges does not reach acceptance

Fix `S`, `c` and `π`. Then
`Vb c π = Tmpl(cs, params, x, c, π)` under BLAKE2s, with `x = pub(c, preSeg π)`.

1. Under the ROM, `Template.ks` holds for every `pub`. The statement `x` is adversarially adaptive,
   because `final` quantifies over `c` and `π` after the log.
2. `pub` is a public deterministic function, so the prover can compute it. Any `x` that `pub`
   selects using local BLAKE2s, the prover could have placed directly.
3. `x` cannot contain `τ(x)`: that would be a fixed point of BLAKE2s through the seed.

So `pub` gives the adversary nothing beyond choosing the statement, and acceptance of a false
statement under BLAKE2s is an FS failure of the template at the adversarially chosen `(cs, x)`.
That is the residual, not a new hole.

### 3.3 What `preSeg` is, and who decides where it ends

The memo never fixes `preSeg`. It must be **template-fixed by layout**: a byte range determined by
the template from `params`, and from `cs` or `x`-independent header fields, never by a length the
prover writes or `pub` chooses.

If the prover sets the length, `pub` reads post-seed messages. By §3.2 that still does not reach
acceptance, but it breaks INV′'s last clause and invites template code that reads `x` from
post-seed bytes. With M1(b), `preSeg` becomes "the header", of fixed length per template.

### 3.4 How `Ã(r_x, r_y)` is evaluated

T needs a **contract- or library-owned generic evaluator**. Today spartan-chain's evaluator is the
submission's own closed form: `chainMats` = `walkAB` over the BLAKE2s circuit positions plus
`closedA`/`closedB`/`closedC`, about `2^16` multiplications (`SpartanChainChainEval.lean`).
Supplied by a submission, that closed form would be submission code applied to challenges, which
breaks INV′.

For the uniform format, a generic evaluator costs:

- `O(nnz(block) · (log s + log m))` for the block part, through the `eqTable`s of
  `r_x[0..log s)` and `r_y[0..log m)`;
- `O(k)` for the repetition (`eq(r_x^hi, r_y^hi)`);
- `O(|chain| · k)` for the chain links (`shiftMle`);
- `O(|x|)` for the public part.

At spartan-chain's block (`2^14` rows, a few `2^15` non-zeros) this is on the order of today's
`2^16`. That is efficient for `T_V` and needs no oracle queries, so `qV` is unaffected. It is not
efficient enough to evaluate a node `cs` inside that same node (M4).

The evaluator is library code with a correctness theorem against `matMle` of the expanded
matrices. An evaluator correct only for chain-shaped data (R2.11.4) is caught by the kernel,
because the entry's `KS` would not go through.

## 4. Recursion, extraction and cost (attacks 4, 5, 7)

### 4.1 The extractor under T (attack 4)

`E` and `ext` are not on the acceptance path (§3.1). A submission's `E` cannot exploit T. The
issues are cost and specification (m2, m4):

- **Leaves.** If the witness is public in `x`, as in spartan-chain, `ext` is `decodeW ∘ x`: a
  submission-specific `XProg` that re-implements the parse in the word language, with a step
  bound. It is not "a generic decoder per PCS".
- **Private witnesses and SNARK nodes.** Child proofs live in the committed witness. `ext` must:
  - index the log, which the linear term `2^16·t` covers;
  - rebuild the Merkle tree from the queries;
  - RS-decode the needed rows within the fixed `2^48` term. Design §4.4 sized that term for a
    `2^29`-symbol word.

  A generic decoder `XProg` per PCS is the right organiser asset. I did not find it scheduled
  anywhere. #7's "extraction is decoding" is resolved *by* this asset, not by T.

No submission lever appears here. `E` only has to satisfy `final` and `Computes`, both
kernel-checked, and the harness's run of `ext` on the honest BLAKE2s log can only fail the
submitter.

### 4.2 Recursion under T (attack 5)

- **Is the node relation expressible?** Only with M3's dispatch and M4's self-verification design.
  A one-`cs` T must verify proofs of its own `cs` (M4). That forces a uniform VM-like node block
  with a fixed opcode schedule, entered either through per-block public inputs or through a
  template-owned memory-checking gadget under A3.
- **Does a node `cs` give the submission a lever on the outer challenges? No, under A1–A4.** The
  node's witness may contain the BLAKE2s circuit, every **child** challenge, and even the **outer
  seed answer** (M1). But:
  - every outer challenge is derived after the node's root is absorbed, so a wire equal to an outer
    challenge is a fixed point;
  - the only outer checks are template code over pre-root-committed `z` (A2).

  R2.6 point 1 is right in substance, although its reason ("never the node's own [challenges]") is
  stated for values rather than for checks (M1).
- **`proofCap` (#8).** `Vb` keeps `π.size ≤ proofCap`. Under T the launch template's proofs
  exceed it at the ranked size (M4). The menu question "WHIR-class PCS, and which hash" is
  therefore not a later convenience. It is a prerequisite for any ranked T entry. Under a
  WHIR-class template, I4's sizing (621–770 KiB at `2^24`/`2^28`, "yes, barely") is the whole
  margin.

### 4.3 The one-time non-recognition review: size and checklist (attack 6)

**Size.** About 500–900 lines of executable Lean on the verification path (m7), plus the new
generic evaluator, plus the contract's BLAKE2s and Lean core's `extern` byte and `UInt`
primitives, which are trusted anyway.

**What the review must check, concretely.** Run it on the reference spec of O25T-M5 once that
exists.

- **(a) Every local BLAKE2s call site in the closure.** These are `csDigest`, `paramsDigest`, the
  statement checks (`leafStmt`, `nodeStmt`), and the node branch's run of children under
  `blake2sOracle`. Each output may flow only into:
  - an oracle query's input;
  - a comparison with the **statement** `c`;
  - the child verification that `Rel`'s node clause itself defines.

  It must never flow into a comparison with an oracle answer or a value derived from one. This is
  the exact `Backdoor.lean` shape.
- **(b) Every comparison or branch whose operands include an oracle-derived value.** Each must be
  one of the protocol's fixed identities:
  - Merkle path equality;
  - sumcheck round consistency;
  - the final evaluation identity;
  - Ligero column and `ū` consistency;
  - the grinding threshold against `params.grind`;
  - challenge-to-index decoding.

  Enumerate them and match each to the paper's protocol.
- **(c) Data-dependent control flow.** No branch on `cs` or `params` may select a different set of
  checks, other than sizes and loop bounds. Degenerate values (`0` rounds, empty `A`) must not
  short-circuit a check into `true`. The kernel's `KS` catches only ROM-relevant omissions, not
  ROM-invisible ones (m5).
- **(d) No `implemented_by`, `extern` or `@[csimp]` in the template closure** outside Lean core.
  The compiled code the harness runs must be the kernel's definition.
- **(e) The decision is a conjunction.** Acceptance is the `&&` of (b)'s checks, with no `||`,
  no early `true`, and no `match` arm returning `true` on a data or answer pattern.

(a)–(e) are a finite, enumerable checklist over a fixed codebase. That is the real improvement
over reviewing each entry's `V`. It holds only while templates stay few, specs are short (M5), and
A1–A4 hold.

### 4.4 Cost and freedom (attack 7)

- **What remains to compete on.** The arithmetisation (the leaf `cs`; the node `cs` only if the
  organiser does not ship it, R2.6.2), parameters within the menu, and native provers. Gone: the
  IOP, the PCS, the field, the transcript and hash use, verifier optimisation, and accumulation
  (already gone, ADV-M8). This is narrower than v2 (M6).
- **Organiser work before the first ranked T entry.** The dependency chain, without durations:
  1. the generic evaluator with its correctness theorem for the family datatype (M3);
  2. a knowledge-extraction `Template.ks` (m4);
  3. a decoder `XProg`;
  4. a WHIR-class PCS with Lean KS in the unique-decoding regime (I4);
  5. a self-verifying node design and its gadget with circuit-correctness theorems (M4);
  6. the template spec, its `impl = spec` theorem, and the review (M5).

  Items 4 and 5 are each the size of the current honest entry or larger (REPORT §3.1: 16,766
  code lines for a leaf-only Spartan+Ligero).
- **Trusted lines.** About 100–130 contract lines, giving ≈390–420 of 500 (m7). The template's
  0.5–0.9k executable lines are trusted for meaning and non-recognition, and must be listed in
  DESIGN §8.

## 5. Middle grounds, and the admissibility rule every menu item must satisfy

The question is which shapes keep more freedom than T and still satisfy INV′ against the post-hoc
attack. The attack needs one thing: a **check that the submission defines, whose operands are an
earlier challenge and prover data written after it**. Each candidate is judged on that.

| Shape | What the agent chooses | Survives the post-hoc attack? | Why |
|---|---|---|---|
| **MG2: v2-style agent IOP + organiser BCS** | the IOP, its verifier's decision | **no** | The IOP verifier sees `c₁` and later messages and may check `c₁ = Σ outbitᵢ βⁱ` with BLAKE2s wires as later oracles. It is IOP-sound (`c₁` is truly random) and BLAKE2s-unsound. Design §5.4 already records v2's exposure. |
| **Repaired E, driver style** (review §4, R2.3) | the order and subset of contract checks | **no** | The composition is a lever (R2.3, accepted). |
| **MG3: agent polynomial IOP with an algebraic decision over multi-round oracles** | constraints over oracles from several rounds, with challenges as coefficients | **no** | Attack C / `postHoc_iff`: a constraint `α = w₀` over a phase-2 oracle is data. |
| **MG1: admissible menu (recommended for the user's choice)** | single-phase constraint data in any admissible format (uniform R1CS, CCS, AIR or Plonkish with custom gates of template-bounded degree); a compiler from a menu (Spartan-like sumcheck, HyperPlonk-like zerocheck, STARK-AIR quotient); a PCS from a menu (Ligero, WHIR, Basefold, FRI); a field from a menu (`GF(2^64)`/`EF`, Goldilocks², BabyBear⁴, each a library implementation proved equal to its spec) | **yes, under A1–A4** | All data-defined functions are evaluated at challenges and at PCS-bound evaluations of pre-challenge commitments. Lookups, permutations and grand products are template gadgets (A3). The composer is contract code taking first-order data only. |
| **T as specified** | `UniformR1CS`, params | yes, with M1's fix | It is MG1 with one format, one compiler, one PCS and one field. |

**MG1 is T with a wider menu and a precise admissibility rule (A1–A4 of O25T-M2).** Two points
make its safety argument the same as T's.

- **Custom gates.** A data-defined gate polynomial `G` is applied to `(w̃₁(r), …, w̃_k(r))`. These
  are prover-sent values after `r`, but the PCS binds them to oracles committed before `r`, so
  `G(w̃(r))` is a fixed polynomial in `r` once the commitment is fixed. That is the same situation
  as `Ã(r)` in Spartan. Recognition would require choosing the commitment so that `r(root)` lands
  in `G`'s special set, which is grinding and priced by the ROM.
- **A1's degree bound.** Without it, a table-defined function of the challenge could encode one
  target challenge value. `csDigest` binding already makes that a fixed point (m5). The degree
  bound keeps the argument independent of the binding.

**What MG1 restores relative to T:**

- arithmetisation format;
- PCS choice, including WHIR, which ranked recursion needs anyway (M4);
- **field choice**, which addresses Q6's "fields are a large part of the cost";
- the compiler family.

**What it still excludes:**

- new IOPs or new PCSs that are not yet templates;
- verifier-side optimisations;
- accumulation.

New items still enter by core PR, with M5's spec-and-embargo process.

**The research track (R2.5).** Keep it: it is the only place an agent-designed IOP can live. But
it is unranked by **type** (m6), not by policy, and a promoted design enters as a template under
M5. Its rule, review and challenge period are adequate where nothing is ranked, with the caveat
that a research entry's verifier can still win DoS or "first certified" recognition. List such
records as "not O-25-closed".

## 6. The epistemic claims of R2.10, restated

### 6.1 Row by row

| R2.10 claim | Memo's status | Correct status |
|---|---|---|
| `KS (Rel S.Vb) S.V S.E ε qV` for every T entry | proved (kernel) | **Kernel**, and it is the contract's own clause, so it holds independently of `Template.ks`'s hypotheses (m3). |
| `Vb` is the template applied to the submission's data; `pub` has an oracle-free type | proved/mechanical | **Definitional**, true by the contract's definitions. "Oracle-free type" does **not** mean "cannot compute oracle answers" (M1, kernel probe). |
| INV | structural fact, readable from `TSubmission.V` | **False as stated** (M1). What is readable from the definitions is INV′'s first two clauses, given a fixed `preSeg` layout and the seed in the contract. That the template's checks consume data only as A1–A4 allow is **a property of the template's code**, established by review of its spec (M5), not by `TSubmission.V`'s five lines. |
| the generic evaluator is correct for every well-formed `cs` | proved (to be built) | It would be **kernel**, but it is not load-bearing for soundness: the entry's `KS` covers an incorrect evaluator. It is needed for availability. |
| the template does not recognise the deployment oracle | assumed, one-time review | **Review**, of an enumerable checklist (§4.3) over a short spec (M5). Without the spec it is review of 0.5–0.9k lines. For competitor-proposed templates it is the status-quo problem (M5). |
| BLAKE2s-instantiated Spartan+Ligero FS is sound for every `cs` | assumed | **Assumed, and unprovable by the ROM theorem** (§8). Fenzi's class is excluded by Fenzi's theorem given full binding (m5). KRS's mechanism is blocked heuristically by single-phase commitment (A2), not by binding. |
| liveness | process | Under T it is **one submission field, `pub`** (M1). Remove `pub` and the residual is the native prover's correctness, which scoring checks. |
| ranked sampling | trusted process | Existing fresh starts; no beacon needed for T (m8). |

### 6.2 "Cannot be written"

R2.10 says a `Backdoor.lean`/ADV-M5/O25-M1…M5/post-hoc backdoor "**cannot be written** … a
structural fact of the composition, not a conjecture". Precisely:

1. **Structural, readable off the contract's definitions.** No submission-authored *check* has an
   oracle-derived operand: INV′ clauses 1–2, given M1(b)/(c) and a fixed `preSeg`. The
   `Backdoor.lean` mechanism ("`V` compares a locally computed BLAKE2s value with an answer") needs
   such a check, so **a submission cannot author it**. This is a fact about the composition, true by
   definition, and it needs no parametricity meta-theorem. Round 1's `D`-half is no longer
   load-bearing.
2. **Not structural.** That the template, interpreting submission data, performs no such comparison
   either. Data interpreted by code *is* code, as Attack C shows. This rests on A1–A4 holding for
   the template's interpretation, which is review of the spec (M5).
3. **Not structural, and not removable.** That the template's own FS is sound under BLAKE2s for
   every admissible `(cs, x)` (§8).

So "cannot be written by the submission" is right. "Cannot be written" is right only together
with (2), and (2) is review.

### 6.3 "~90% no cheap review-invisible workaround"

A probability with no model behind it should be dropped. What I can state:

- Against T **as specified**, single template and single-phase, I found:
  - no acceptance backdoor;
  - one kernel-checked liveness channel (M1);
  - one ROM-invisible binding left to library code (m5);
  - specification gaps that block the honest entry (M3, M4).

  None is a cheap acceptance workaround.
- Against T **as it would evolve** (more formats, lookups, competitor templates), the defence is
  A1–A4 plus the spec review. A violation of A2 is one datatype constructor (Attack C). Whether
  review catches it depends on A1–A4 being written down. Today they are not.

## 7. Verdict

**Did I break T? Partially.**

- **Not broken.** T's core closes the submission-authored CGH mechanism. That is the
  `Backdoor.lean` shape and every round-1 variant (O25-M1…M5), together with the post-hoc attack,
  because a submission authors no check with an oracle-derived operand. I found no acceptance
  backdoor in T as specified, through any `TSubmission` field.
- **Broken.**
  - The stated invariant is false (M1, kernel). The repaired invariant is INV′.
  - The design lacks the admissibility rule its own menu needs (M2).
  - As specified, T cannot certify the honest entry (M3), cannot rank anything at launch, and has
    no recursion story for a single self-verifying `cs` (M4).
  - Its template process re-imports the review problem (M5).
  - It reverses three Q6 decisions without saying so (M6).

**Recommendation.**

1. Adopt the core of T as the O-25 closure: a contract-owned composition, data-only entries, the
   seed query in the contract, and `x` from a contract-fixed map.
2. Write A1–A4 into the contract header and the rulebook.
3. Re-specify the datatype with statement-indexed families, add a contract dispatch for nodes,
   and replace `wf` with a definition.
4. Require a reference spec plus `impl = spec` for every template, with a proposer embargo.
5. Put Q6 back to the user with three options: T, MG1, or review-only ranking.
6. Record the organiser dependency chain of §4.4 in the plan (M4).

No ranked T entry is possible before items 4 and 5 of that chain exist.

## 8. Strength, stated precisely

### 8.1 What T guarantees against submission-authored backdoors

- **Theorem (kernel), unchanged by T.** `KS (Rel S.Vb) S.V S.E ε qV`. It says nothing about the
  single deployed oracle.
- **Structural, definitional in the contract, given M1(b)/(c).** For every T submission `S`:
  - `Vb_S c π = Tmpl(D_S, x(c, hdr π), c, π)` run under BLAKE2s, where `Tmpl` is fixed organiser
    code and `D_S` is first-order data fixed before the seed and absorbed into it;
  - no submission-authored function runs on the verification path.

  Hence no check that a submission writes compares a locally computed value with an oracle answer.
  The `Backdoor.lean`/ADV-M5/O25-M1…M5/post-hoc mechanism **cannot be authored by a submission**.
  This needs no parametricity meta-theorem.
- **Review (one per template; enumerable with M5's spec).**
  - `Tmpl` itself performs no such comparison: §4.3 (a)–(e).
  - `Tmpl` interprets `D_S` only as A1–A4 allow. Data is evaluated only at challenges and at
    PCS-bound evaluations of pre-challenge commitments, and nothing constrains post-challenge
    columns.

  Given A1–A4, data cannot encode a target challenge (fixed point through `csDigest`) or check a
  BLAKE2s computation over the transcript (there is no post-challenge data for it to constrain).

### 8.2 What remains

- **(R1) The template's own FS heuristic.** Spartan+Ligero, and every menu item, compiled with
  BLAKE2s may be unsound for some admissible `(cs, x)`, while `KS` holds. This is the residual of
  every deployed FS SNARK.
- **(R2) The non-recognition review of each template and spec.** A trusted human judgement, now
  bounded and enumerable.
- **(R3) Liveness through `pub`** (M1). Gone if `pub` is replaced by a contract map. Otherwise it
  harms only its own submitter.
- **(R4) Template evolution.** Every new format, gadget or competitor template re-opens (R2), and
  A1–A4 if they are not enforced.

### 8.3 Can the remainder provably not be removed?

**(R1): no ROM theorem can remove it, and no proof for this template is known.** The certificate
quantifies over all `H`, and BLAKE2s is a single point among `(2^256)^|domain|` oracle functions.

- CGH98 (ePrint 1998/011) shows that ROM security does not imply security under any concrete hash
  for some schemes.
- Goldwasser–Kalai (FOCS'03) and BBHMR19 (ePrint 2019/997) show it for 3-message and
  Kilian/Micali arguments respectively. BBHMR19's covers the BCS family T's template belongs to:
  an interactive PCP that is unsound under FS for every hash.
- KRS25 (ePrint 2025/118) shows it for a deployed GKR-based argument, with every FS hash.
- Fenzi26 (ePrint 2026/1838) shows it for generated-R1CS Spartan/Aurora variants. It also proves
  that binding the generated statement reduces soundness to the non-generated protocol. That
  reduction excludes Fenzi's class for T, given that the seed binds the expanded instance.
- BHK26 (PKC'26) gives simpler counterexamples, including for extended FS, so XFS is not an
  escape.
- Bitansky et al. (ePrint 2012/705) and DJKL (2012/706) show that FS soundness for some protocols
  has no black-box reduction to a falsifiable assumption.

These are *existence* results over protocol families. **None proves that T's specific template is
uninstantiable, and none proves it instantiable.** Removing (R1) would need a standard-model
assumption on BLAKE2s: correlation intractability for the template's bad-challenge relations,
after CCHLRR19 (ePrint 2018/1004). For an unstructured hash that is unproven. By
BDGJKLW13/DJKL13 it is unlikely to be provable by black-box reduction for every protocol on the
menu. Only the ROM-to-concrete gap is provably irreducible. The specific template's insecurity is
not established.

**(R2)** is irreducible by the same CGH argument applied to the organiser. No ROM theorem
distinguishes an honest template from a recognising one.

### 8.4 How hard is a workaround for a very clever adversary?

- **Against T with M1–M5 fixed, single-phase.** The adversary authors no check, and the only data
  lever is a multilinear `Ã` evaluated at bound challenges. A win needs either:
  - (i) a new FS attack on commit-all-wires Spartan+Ligero (or WHIR) with the instance bound in the
    seed. The KRS mechanism then requires a BLAKE2s fixed point `w ↦ root(w)`, and Fenzi's is
    excluded by binding. This would be a research result beyond KRS25/Fenzi26, exhibited through
    first-order data, and visible once published; or
  - (ii) subverting a template review against a short spec.
- **Against T as written.** No acceptance workaround found. One liveness channel (M1). The large
  risk is (R4): one constructor with a challenge term (Attack C) in a future menu item reopens the
  one-line backdoor, and nothing in the memo forbids it.

---
*Probe: `/home/devops/Verified-zkEVM/rf-core-sc/scratch/o25t/T1_pub_sees.lean` (log
`T1_pub_sees.log`). It compiles under Lean v4.34.1 against the contract at `05fde28`.
`pubTau_eq_challenge`, `evil_Vb` and `postHoc_iff` depend on `[propext, Quot.sound]`. No files
were edited outside this review and the probe directory. No commits.*
