# The honest baseline: synthesis report for the recursion.fast designers

Status: draft of 2026-10-19 (evening), written while the last modules of the honest entry were
still being edited. Every figure marked `TBD (final run)` is replaced once the final measurement
run lands (`submissions/spartan-chain/measure.sh`, `check.sh`). Every other number is a
measurement with its log under `logs/` (gitignored, local to the development VM) or a
kernel-checked theorem, and says which. Nothing in this report is an estimate of future human
work.

Audience: the competition's designers (cryptographers and zkVM engineers) and formal-methods
readers. Lean terms are explained in one line where they first matter. Section 1 is the summary;
§2 ranks the findings about the rules; §3 says what an honest entry cost; §4 recommends rule
changes; §5 says what the entry is not; §6 lists the decisions only the user can take.

Sources (all paths relative to this repository unless stated): `docs/snark-baseline/PLAN.md`
(decisions D-1 … D-10), `notes/F1-ks-feasibility.md`, `notes/ADV1-rules-review.md`,
`notes/E1-leanervm.md` … `notes/E4-clean-riscv-tooling.md`, `issues/I1 … I7` (filed as
scaraven/recursion.fast #5 … #10 and a comment on #4), `BLUEPRINT-R1.md` (§0, §12, §13, §14),
`reports/*.md`, `docs/reviews/*.md`, `docs/stages/V3-S2a-RESULT.md`, the git log, and the
amended contract on branch `v3/ks-potential` of `/home/devops/Verified-zkEVM/rf-core-ks`
(its `docs/stages/V3-S2-KS-RESULT.md`).

---

## 1. Executive summary

Three things were built today, against the core pinned at `15e4ae5` (the v3 contract, stage S1).

1. **S2a, the witness-sending baseline** (`submissions/baseline/`): certified (`CertificateR`
   kernel-checked, comparator with both kernels, gate PASS, `HARNESS: ACCEPT`), 310 Lean code
   lines, root check at the ranked size 20.93 s (`docs/stages/V3-S2a-RESULT.md`).
2. **A contract amendment** (branch `v3/ks-potential`, not pushed): the knowledge state becomes a
   potential `μ : Log → ℝ≥0` with a log-length guard `logCap = 2^96`; the paper theorem
   `(Q + qV)·ε` is now a kernel-checked library theorem; the contract grows by 3 trusted lines
   (331 of 500). Without it no hash-based SNARK can be certified (kernel-checked, §2.1).
3. **R1, the honest entry `spartan-chain`**: a leaf SNARK for the BLAKE2s chain (Spartan-style
   R1CS sumchecks over GF(2^64) with challenges in its cubic extension, 64-bit packing with
   Frobenius ring switching, a Ligero tensor commitment under unique decoding, Merkle tree and
   Fiat–Shamir over the contract's oracle), with witness-sending nodes; a Rust prover with a
   known-answer harness against the Lean definitions; about 16 k Lean code lines in 58 modules,
   1.7 k of them copied from leanerVM. Its `step` law and its `final` law are proved for the
   real verifier; the last assembly (the `KState`, `Facts`, `SpartanChainFinal.lean`) and the
   end-to-end harness run are `TBD (final run)` (§3.4).

Headline findings about the rules, each filed on the core: the S1 knowledge-soundness
definition is unsatisfiable for every Merkle/BCS verifier (#5); the succinctness cap `T_V` does
not exclude the witness-sending argument and board T does not reward recursion (#6); node
extraction is decoding, which no honest extractor can do inside `extractorBudget` (#7);
`proofCap`, BLAKE2s-only hashing, R1CS and the unique-decoding regime leave only WHIR-class
sizes for honest recursion, and perfect completeness over every oracle forbids preprocessing,
grinding and accumulation (#8); the O-25 backdoor has variants that evade the proposed defences
(#4); the library verifier and the contract's codec have defects an entry inherits (#10); ten
hygiene items (#9). The amendment itself had a start-up bug (a computable `Fintype Digest`
instance that every compiled binary evaluated at start, 22.9 GB in 20 s) found and fixed today.

---

## 2. Findings about the rules, ranked by consequence

Evidence kinds: **kernel** = a theorem checked by Lean's kernel with only the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); **measured** = a timing with a log; **paper**
= an argument or an estimate from published tables, not machine-checked.

### 2.1 KS at `errorCap` is unsatisfiable for any BCS argument (#5) — fixed by the amendment

**What.** The S1 knowledge state asks the submitter for predicates `good : Log → Prop` and
`bad : Log → query → answer → Prop` such that at most `ε·2^256` answers are bad **for every log
of any length** and every fresh query (`KState.Bounded`), with `ε ≤ 2^-128`. Two things no
hash-based verifier can meet:

- (a) collisions and late preimages: a Merkle-binding argument charges each fresh answer with
  "collides with an earlier answer" or "is the preimage of a dangling root". Those sets grow
  with the log; beyond `2^128` entries they exceed the cap, so `bad` must drop them, `step`
  forces `good` onto a log with a collision, and `final` must extract from a log in which the
  adversary can open one commitment two ways;
- (b) per-answer charging: a unique-decoding query phase needs `t ≥ 128` positions drawn from
  `k ≥ 2` 32-byte answers; the boolean form charges each answer with the worst conditional
  probability, `(1−δ)^{t/k} ≫ 2^-128` at the last one. The real random-oracle argument gives no
  such credit.

**Evidence.** Kernel: `logs/adv-probes/CountingForm.lean` (`collision_not_capped`,
`product16_not_capped`: a 16-query verifier with ROM error `2^-128` has no bounded state below
`2^-8`; `eps_ge_density` shows spreading over more answers never helps). Paper: F1 §1.2's explicit
attack log for a real Merkle-plus-Fiat–Shamir verifier. Three independent sources agree
(`PLAN.md` D-2): F1, ADV1 (ADV-M2, ADV-M3), and leanerVM's own planned bound, which has a `Q²`
term and a grinding-backed query round (E1 §4). Every escape was examined (semantic `good`,
length-dependent `good`, 512-bit roots, extra local checks, larger `qV`, tighter cap): none works
(F1 §1.3, §2.2).

**Consequence.** Under the pinned contract the only certifiable entries are the witness-sending
argument and the O-25 backdoor. The honest entry could not have been started without a contract
change.

**The amendment (done, local branch).** `rf-core-ks` `v3/ks-potential`, head `05fde28` on top of
`15e4ae5` (RESULT `docs/stages/V3-S2-KS-RESULT.md` there; review `docs/reviews/V3-S2-KS-review.md`
here, verdict "sound; fix M1 before merge", M1 fixed). The trusted text, verbatim:

```lean
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

Read: on average over the `2^256` answers to a fresh query, the potential rises by at most `ε`;
below `1` every accepted proof is extracted; both laws are required only within `logCap`
entries. The paper theorem (failure probability `≤ n·ε` for a game of `n ≤ logCap` queries, by a
stopped supermartingale and Markov) is now **kernel-checked** for the exact text, for a lazily
sampled random oracle: `Library/PaperTheorem.lean` (`paper`, 113 code lines, standard axioms).
The boolean form embeds as the library constructor `KState.ofBool`, so nothing a submitter could
do before is lost (kernel-checked); every S1 control ports; new controls separate the forms
(`twoLucky`: a challenge over two answers, potential at `2^-192`, no boolean state below `2^-96`;
`Vcol`: collisions, no boolean state at the cap over unbounded logs). `logCap` was `2^64` in the
first draft; the review (V3-S2-KS-M1) showed that value certifies a verifier that compares
digests on 24 bytes (96-bit generic security) at the 128-bit cap, kernel-checked
(`Probe.v24_ks`); the fix moved it to `2^96`, where collision-type events of `≥ 224` bits are
chargeable and an honest Merkle verifier pays about `2^-145` per query.

**Cost.** Contract `Security.lean` 23 → 26 code lines; contract total 331 of the 500 budget;
`Certificate.lean` unchanged; no new attribute. Build of the amended core: 2 min 00 s cold,
4.16 GB peak, 2.8 s warm; axiom audit PASS, 811 declarations (`logs/ks-amendment/fix/`). Design
text: `DESIGN-v3` §4.1, §4.2, §4.5, §6.6, §8 and `AGENTS.md` §4, `BASELINE-TASK` §0, §5 are stale
until the pin moves (wording in the core's `docs/DESIGN-AMENDMENTS.md`, V3-KS-A1 … A7).

### 2.2 `T_V` does not exclude witness-sending; board T does not reward recursion (#6)

**What.** DESIGN-v3 §6.5 separates SNARKs from the trivial argument by a 2 s wall-clock cap on
the root check and claims a 10× margin ("22–29 s" for the trivial check). The cap rewards threads
and a fast hash implementation, both of which are legitimate compiled Lean. Separately, §5.3 and
§6.7 say a prover "cannot flatten the tree" and that recursion only near the root "pays in
`T_tree`"; in fact witness-sending proofs below level `j` cost nothing to produce, so a prover
recurses only above `j` and saves node proofs.

**Evidence (measured, `logs/adv-probes/`, `logs/V3-S2/`; whole ranked tree, `r = 8`, `n = 2^14`,
`2^22` compressions; QEMU 32-vCPU VM, not the reference machine).**

| chain check | time |
|---|---|
| certified S2a `Vb`, reference BLAKE2s, sequential | 20.69 / 21.11 / 20.93 s |
| reference BLAKE2s + `Task.spawn` | 1.17–1.31 s |
| unrolled BLAKE2s, sequential | 0.64–0.69 s |
| unrolled BLAKE2s + `Task.spawn` | 37–43 ms |

`Task.spawn`/`Task.get` have transparent kernel bodies, so a threaded verifier is *provably equal*
to the sequential one and the certificate carries over (`TaskRfl.lean`: `(Task.spawn f).get = f ()`
by `rfl`); the source rule accepts it. The unrolled hash agrees with `hashlib` on a known-answer
chain but was not proved equal to `chainStep`; no threaded `Vb` was built as an entry.

**Recommended change and cost.** (1) Measure CPU time (user + system) or pin to one core: one
harness change; side effect: no parallel verifiers. (2) Calibrate against the best linear verifier
the organiser can write (about 65 ms CPU on this VM at the ranked size), or change the benchmark
shape (fewer, longer leaves). (3) Better: a deterministic step count of an organiser-compiled
RISC-V image of `Vb` (O-18), which also removes machine noise. For (b): apply the cap to sampled
proofs at every level, or rank column R beside T; correct §5.3, §6.5, §6.7. Trust cost: none;
the change is to the harness and the design text.

### 2.3 Node extraction is decoding; the extractor budget is sized for the proof, not the word (#7)

**What.** `Rel`'s node clause demands `Vb c₁ π₁ = true` under **concrete** BLAKE2s, while the
query log holds answers of the **random** oracle. A log lookup is therefore unprovable: the SNARK
attests that *some* proof with a given hash is accepted, and the log's preimage of that hash is
unrelated. The only provable route is circuit correctness (R1CS satisfiable ⇒ the witness encodes
accepted child proofs), so the extractor must find the committed codeword in the log and
**decode** it. At node size that word is about `2^29` symbols (4 GiB of log); a quasi-linear
Reed–Solomon decoder needs about `2^43` RV64 steps against `B t = 2^40 + 2^8·t`, and it must be
RV64 assembly proved against the vendored machine semantics with `Library/Machine.lean`'s
single-step tooling. Leaves are fine: the witness `(s, n)` goes in the clear and the existing
8-instruction parsing image extracts it (this is what R1 does).

**Evidence.** Paper only (F1 §3, ADV-M7; sizing from WHIR Table 5 and R7). ADV-M7 reaches `2^46`
for Berlekamp–Welch on a `2^23` word independently.

**Recommended change and cost.** Raise `B` to `2^48 + 2^16·t` regardless (no trust cost: `2^48`
still excludes `2^128` enumeration; three proof terms and two negative controls change). Then
choose between an organiser decoder image (O-15(2); kernel-checked; large) and a Lean-level cost
model for `E` (a first-order extractor language with a step-counting interpreter, 60–100 trusted
lines, moderate trust growth). Measured extractor time and a noncomputable `E` are rejected: the
knowledge content would drop to soundness plus a liveness test. The first recursive certification
is blocked on this decision whatever proof system it uses.

### 2.4 Honest recursion under the caps (#8)

**What.** With the amendment and the extraction rule settled, four further features still restrict
honest recursive designs, and DESIGN-v3 does not say so.

1. **`proofCap = 1 MiB` with UD-provable 128 bits, BLAKE2s-only hashing and R1CS.** V3-5 admits
   no proximity-gap conjecture, so the provable regime is unique decoding: `≥ 128` positions; each
   Merkle level in the node circuit is a BLAKE2s R1CS gadget of about `2^14` constraints (the
   measured leanerVM circuit: 14,720 gates + 256 output rows per compression). Node circuit
   `≈ 2^28.3` constraints; proof sizes at that size (paper, WHIR Table 5 UD column, ZCF24):
   WHIR-class 621–770 KiB ("yes, barely"), FRI `≈ 1 MiB` (no), Basefold 7.95 MiB (no), Ligero
   `≥ 25 MiB` (no). The ranked leaf (`2^28` R1CS constraints) needs the same room. R1's own
   measurement confirms the Ligero row: 1,464,107 B at `n = 2^14` (above `proofCap`).
2. **Perfect completeness over every oracle** (`Complete`, `∀ H`): no grinding, no
   challenge-dependent exceptional case, no rejection sampling. §6.6's `δ` row and §6.7's
   grinding row assume a counted form (`CompleteWithError`) that does not exist; S1's m10 is not
   applied.
3. **Preprocessing SNARKs** (Spartan+SPARK, Plonkish, Marlin): a hash-derived verification key
   has no opening under a random `H`, so `Complete ∀H` fails; recomputing it inside `V` exceeds
   `qV ≤ 2^16`. What remains: transparent uniform arguments. R1 avoids SPARK by a uniform
   repeated-block circuit whose matrix MLEs `V` evaluates in `O(2^16 + κ)` operations (a closed
   form, blueprint §2.4; kernel-checked as `chainMats_eq`).
4. **Hash-based accumulation** (ARC, WARP), named in §1 as a reason for v3, is not expressible:
   the node clause demands full verification of each child.

**Evidence.** Paper (F1 §5, ADV-M6, ADV-M8); the circuit size is measured (`rows_digest_matches_leanervm`).

**Recommended change and cost.** (1) a user decision: say in §6.6 that recursion closes only with
WHIR-class sizes, or raise `proofCap` for node proofs, or add an arithmetisation-friendly hash to
a menu (O-14), or admit a named proximity-gap hypothesis (not under V3-5). (2) land O-23's
counted completeness (`δ ≤ 2^-64`); until then say in `AGENTS.md` §4 that `V` must accept the
honest proof for every challenge value. (3) an indexer `I : OProg Key` in the submission, with
`KS` counting its queries honestly and `Vb` using `I.run blake2sOracle` once at badge build: a
handful of trusted lines; it also removes the one legitimate reason for `V` to compare an oracle
answer with a hard-coded constant (§2.5). (4) correct §1 or change the node clause to an
accumulation-shaped relation (a design change).

### 2.5 O-25 backdoor variants (comment on #4)

**What.** The S1 review's proposed gate test (reject a `V` whose constant closure contains
`blake2sOracle`, `tagRO` or `Submission.Vb`) is evaded by a **literal** 32-byte trigger computed
offline: kernel-checked (`logs/adv-probes/LiteralTrigger.lean`, `backdoor_lit`, standard axioms),
and the closure scan shows the backdoor's remaining BLAKE2s footprint equals the honest
witness-sending verifier's. A "trace-check" variant (a debug branch that checks a proof-supplied
concrete trace of the in-circuit BLAKE2s gadget) evaluates no hash at all (paper). The §6.7 rule
"V's local computation must not evaluate the oracle's instantiation" also bans concatenation
nodes, hard-coded verification keys and consistency fast paths. The parametric-digest fix cannot
support Fiat–Shamir: any answer bits `V` can read, `V` can compare with a local BLAKE2s. `AGENTS.md`
at the pin does not state the rule.

**Recommended change.** State the rule semantically in `AGENTS.md` ("no branch of `V` may accept
because an oracle answer agrees with a value `V` did not obtain from the oracle or the proof");
require `NOTES.md` to list every comparison of an oracle answer with anything else; make intake
review (S7) mandatory with a challenge period; drop or narrow the parametric-`D` candidate; adopt
the indexer of §2.4(3). Trust cost: none in Lean; the defence is review, and the amendment's
potential prices spread recognition exactly as it prices a spread challenge.

### 2.6 Library and contract defects an entry inherits (#10, and two found today)

| defect | evidence | consequence | fix, cost |
|---|---|---|---|
| `Library/WitnessSending.check` accepts a leaf proof with one byte appended or its last byte removed (no canonicity in the leaf branch) | kernel (`lib_check_appended`, `lib_check_truncated`, S2a controls) | the organiser's reference entry fails the §6.3 canaries; an entry cannot wrap the library's `check` and must re-prove soundness and completeness for a strict copy | one line in the leaf branch plus the existing proofs, library only |
| the contract's `packBytes`/`bytesAt` compile to quadratic code | measured: 563.26 s to reject a random 1 MiB proof (`logs/V3-S2/dos-unfiltered/run.log`) | any verifier that decodes with them fails the DoS column (`verify_s = 60 s`) | linear twins with equality theorems (S2a's `packFast_eq` …, about 70 lines); the contract's definitions stay as specifications |
| the amendment's `instance : Fintype Digest` was a computable closed term | measured: a binary whose `main` prints "ok" reached 6.8 GB in 7 s and 22.9 GB in 20 s without printing (`logs/spartan-chain/oracle-merkle-transcript/init-blowup.log`, `logs/spartan-chain/rust/kat.log`); bisected to `Contract.Security` | every compiled `verify` that imports the contract never started; the interpreter was unaffected, which is why the review did not see it | `noncomputable instance`, commit `05fde28` (D-9); a compiled binary then starts in 0.20 s with 86 MB |
| failing unifications unfold that instance ("maximum recursion depth", heartbeat timeouts) | measured in the KS review's probes (V3-S2-KS-m2) | confusing but deterministic failures for submitters | the literal `2^256` in `step` (done); `@[simp] fintype_card_digest`; a note in `AGENTS.md` |
| the recursive node check is `O(|π|·depth)` (each level decodes and re-encodes its subtree) | measured: 212.64 s at depth 2,000 on valid caterpillar proofs (`logs/V3-S2/review/caterpillar.log`) | matters for `verify` on prover-chosen statements, not for the benchmark under the root digest | a byte-offset decoder (R1's `nodeParse`, proved equal to the library's decoding; the smoke root dropped from 2.25–2.50 s to 0.99–1.21 s) |

### 2.7 Minor rules and hygiene (#9)

Ten items, each fixable separately (issue I6): completeness through a fallback branch is
vacuous and liveness tests only the fallback (run liveness on the native prover's proofs with an
emitted query log); repeated benchmark runs need a fresh directory each time; `AGENTS.md`
misstated the contract in seven places (`Digest`, the chain tag, `n ≤ chainCap`, `fuel`'s type,
the `2^24` log bound, where `img` is bound, the separation claim) — corrected in this repository
today (commit `5cb89d8`, with a "Known issues" §15); gate rule 4's `badgeFields` are still v2's
(`P`, `cfg`) and never check `V`, `E`, `img` one by one; the trust statement should name core
`extern`s (`Task.spawn`, `Array`/`ByteArray` primitives); the paper theorem's domain is
`Q + qV ≤ min(logCap, ≈2^57)` because of the extractor's `2^60`-word tape; no `Fintype Digest` at
the pin; ArkLib is not allowlisted and the policy (re-prove, copy, or extend) is unstated;
CompPoly's compiled field arithmetic decides `T_V` (29.7 µs per `BF64` product, 415 µs per `Ext3`
product, measured, `logs/probes/e2/bfbench.log`: a WHIR-class verifier would take 4–40 s).

---

## 3. What an honest entry costs today

All Lean figures are from `.contract/scripts/loc.py` (code lines exclude blanks and comments).
"Copied" means a whole file or a marked section carrying a provenance line (leanerVM
`532ebb4`/`9595721`, Apache-2.0, licence in the root; the S2a entry). Everything else was written
today for this entry. Times were measured on a shared 32-vCPU QEMU VM (load average 5–9 during
the measurement run, so every time is an upper bound); peak RSS is the largest single process.

### 3.1 Lean, by component (preliminary run, `reports/measurements.md`, `logs/spartan-chain/measure/20261019-204628/`)

| component | modules | code lines | of which copied | check time, sum (s) | peak RSS, max (MiB) |
|---|---:|---:|---:|---:|---:|
| field (word-level `BF64`/`Ext3` proved equal to CompPoly's) | 5 | 858 | 0 | 109.3 | 2,610 |
| algebra: MLE, sumcheck, ring switching | 4 | 936 | 90 | 28.3 | 2,513 |
| RS code, proximity (AHIV22-style), PCS bounds | 3 | 696 | 0 | 23.5 | 2,599 |
| BLAKE2s circuit + chain R1CS + matrix MLE closed form | 12 | 3,946 | 1,543 | 280.4 | 2,622 |
| Merkle / transcript / oracle | 3 | 993 | 0 | 41.1 | 2,519 |
| protocol: Ligero, Spartan, verifier, prover, decoder | 6 | 1,719 | 54 | 48.7 | 2,678 |
| soundness: log forest, PCS, Spartan rounds, chain, `final`, `step` | 7 | 4,208 | 0 | 157.5 | 2,987 |
| submission, controls, KAT, runner | 12 | 817 | 0 | 280.9 | 4,008 |
| **total (that run)** | **52** | **14,173** | **1,687** | **969.7** | **4,014** |

That run (20:46–21:08) caught the entry mid-edit: two modules failed to elaborate because other
agents were editing them, and the full parallel build was stopped by a signal from another job
at 2,274 of 2,277 jobs after **261.4 s** wall (cold, the core libraries prebuilt; `full.time`).
By the later `check.sh` run (`logs/spartan-chain/infra/check-m2b.log`) the root had 58 modules,
**16,314 code lines and 1,522 theorems**, source rule 0 findings, axiom audit 111 declarations
within the three axioms. Final totals, the full cold build time and the per-module table:
`TBD (final run)`.

Expensive modules and why (per-module `lake env lean` with imports prebuilt; the floor is 4.5 s
of `.olean` loading):

| module | time | RSS | cause |
|---|---:|---:|---|
| `SpartanChainChain` | 134.9 s | 2.3 GB | the closed form of the matrix MLEs, large `simp` sets |
| `SpartanChainSoundnessLogControls` | ≥ 133.9 s (killed) | — | see below; the symbolic rewrite checks in 7.5 s |
| `SpartanChainFieldBaseCorrect` | 75.0 s | 2.5 GB | word-level `BF64` proved equal to CompPoly's |
| `SpartanChainTranscriptControls` | 71.6 s | **4.0 GB** | the only file that evaluates BLAKE2s in the kernel (known-answer tests) |
| `SpartanChainSoundnessLog` | 46.9 s | 2.7 GB | the transcript forest and L-K1 |
| `SpartanChainBlake2sCompress` | 37.5 s | 2.0 GB | leanerVM's compression-circuit proofs, re-targeted to the contract's `compress` |
| `SpartanChainSoundnessKS` | 35.6 s | 3.0 GB | the per-position doom facts (in flight at measurement time) |

The IMPLEMENTERS brief set a budget of 2 minutes and 4 GB per module; every finished module meets
it (midreview check (5)). Two traps cost time before they were avoided: deciding the honest
117-entry transcript chain with `decide +kernel` (the kernel evaluating a decision procedure)
took 7 m 45 s and 5.3 GB for one `predIdx` and was killed in parallel runs; the symbolic proof
of the same control checks in 7.5 s. And `blake2sCircuit`/`chainBlock` had to be
`@[irreducible] noncomputable`: a compiled closed term of `2^14` rows would be evaluated at
program start, and the kernel must never unfold it.

### 3.2 Rust prover and the known-answer harness (`reports/rust-prover.md`)

3,098 code lines, no crates.io dependency (BLAKE2s, the thread pool and the additive FFT are
written here), 21 tests; the circuit is leanerVM's row for row (`rowsDigest =
4056851438423586957`, leanerVM's own `#guard` value). Measured (`logs/spartan-chain/rust/`):

| `n` | proof size | prove wall (3 runs) | peak RSS | native verify | queries |
|---:|---:|---|---:|---|---:|
| 16 | 143,711 B | 0.18 / 0.19 / 0.18 s | 8 MB | 0.084–0.103 s | 3,533 |
| 1,024 | 457,843 B | 0.71 / 0.71 / 0.70 s | 255 MB | 0.39–0.42 s | 4,414 |
| 16,384 | 1,464,107 B (above `proofCap`) | 7.61 / 7.43 / 7.98 s | 3.95 GB | 0.81–0.84 s | 5,156 |

Where the time goes at `n = 2^14`: outer sumcheck 4.4 s, inner 1.5 s, encode 0.5 s, witness
0.4 s, ring switching 0.4 s, Merkle 0.1 s, at about 2,200 % CPU. The `r = 2`, `n = 16` smoke tree:
0.72–0.76 s for the whole tree, root 575,112 B, native root verify 0.17–0.20 s. Field: `K`
product 17.5 ns, `E` product 66 ns (no `pclmulqdq` on this VM; leanVM's fallback is 22–25 ns).

The KAT (`kat.py`): nine dumps (field, MLE, transcript ops, encoding at every point, `Φ`,
sumcheck, walk, the full `2^14`-row circuit, and the `n = 1` leaf recomputed in Lean from the Rust
challenges, 233 lines) all `SAME`; a one-digit change gives `DIFF` and exit 1. Compiled, every
dump runs in 21 s in total; through the interpreter, `walk` had taken 462 s and `leaf` 690 s.
Byte identity of whole proofs (Lean `P` against Rust bytes): `TBD (final run)`.

### 3.3 Runtime of the Lean verifier and field (`reports/leaf-snark.md`, `FIELD.md`)

Compiled Lean `Vb` on the Rust proofs (`logs/spartan-chain/leaf-snark/`, `logs/spartan-chain/fix-m2/`):

| proof | bytes | Lean `Vb` | Rust |
|---|---:|---|---|
| leaf `n = 1` | 95,719 | 138–153 ms | 62.5 ms |
| leaf `n = 16` | 143,711 | 211–227 ms | 92.1 ms |
| level-1 node (two leaves) | 287,512 | 0.47 s (1.01–1.06 s before the codec fix) | |
| smoke root (four leaves) | 575,112 | **0.99–1.21 s** over 8 runs (2.25–2.50 s before) | 0.188 s |

A flipped byte, an appended byte, a removed last byte and a flipped statement bit are rejected on
every proof; a random 1 MiB proof is rejected in 4 ms. The compiled word-level field
(`logs/field/bench-20261019-185727.log`): `F` mul **87 ns** (CompPoly's `BF64.mul` 30,300 ns),
`EF` mul **535 ns** (CompPoly 466,000 ns), `F` inv 1,506 ns, `EF` inv 2,217 ns; the equality with
CompPoly's field is a kernel-checked ring isomorphism (`ringEquivBF64`, `ringEquivExt3`), so
CompPoly stays the specification. Merkle: a build over 4,096 columns (8,191 oracle calls) 65–77 ms,
260 openings 25–28 ms, one oracle call on 33 bytes 5.9–7.3 µs.

### 3.4 Proof effort: what the reviews caught, and what the entry proves

Five review cycles ran today (one per artifact, each with a fix pass):

| review | majors / minors | classes of error found |
|---|---|---|
| `V3-S2a-review` (witness-sending entry) | 2 / 9 | organiser material inside the entry root; a "linear" claim false on lopsided proofs (measured 212.6 s) |
| `V3-S2-KS-review` (the amendment) | 1 / 6 | a false justification of `logCap = 2^64` certifying a 96-bit verifier at the 128-bit cap (kernel probe); redundant hypotheses; the `Fintype` elaboration snag |
| `BLUEPRINT-R1-review` (the protocol and §9) | 4 / 14 | **statement errors in the security argument**: a partially built Merkle tree was "doomed forever" (`final` false); `Bad` omitted state hits (chains assembled out of order); `bounded_chainBlock` false as specified; the quadratic decoder on the node path |
| `BLUEPRINT-R1-S9-review` (§9 rewritten) | 3 / 4 | `step` false on two logs a formaliser hits at once (failed checks did not doom; prefixes double-counted); two lemma statements false (L-M4, L-K7); three further false statements found and corrected by the Merkle implementer |
| `V3-S2b-midreview` (the Lean entry) | 5 / 12 | **a vacuous `Facts`** (`queries` unbounded in `n`, kernel-checked uninhabited); the smoke root over `T_V`; the `step` law generic only; `chain_sound` without a consumer; the final instantiation missing; licence copy missing |

None of the seven blueprint majors touched the protocol, a byte or a parameter; `ε = 2^-129` held
throughout (`PLAN.md` D-10). The lesson for the organiser's documentation: the *definitions* of
the potential (what is a chain, what is bad, when is a chain doomed) are where the errors were,
and a blueprint reviewed on paper twice still had `step` false before the formaliser touched it.

What is proved at the time of writing (all with the three standard axioms, `sorry`-free, source
rule 0 findings on 58 files):

- the field (word-level, equal to CompPoly's), the MLE/sumcheck/ring-switching algebra with every
  counting lemma (L-E1 … L-R5), the RS code's distance and the AHIV22-style proximity lemma
  (`far_bad_le`, with the sharper `(e+1)` form), the numeric R0/R7 bounds at the protocol's
  parameters (`r7_far`: `(4/5)·2^-129`, exact `ℕ` arithmetic);
- the BLAKE2s chain block in both directions against the contract's own `blake2s`
  (`block_sound`, `block_complete`), the chain R1CS (`chain_sound`, `chain_complete`), the verifier's
  closed-form matrix evaluation equal to the abstract MLE (`chainMats_eq`, `chainPub_eq`);
- Merkle completeness and binding on the log, the transcript forest, L-K1 (`bad_step_le`), L-K4
  (`runLog_chain`: an accepting run's Fiat–Shamir queries form a chain of the log), the `final`
  law for the real verifier (`SpartanChainSoundnessKSFinal.final_law`), the `step` law assembled
  from the per-position doom facts (`SpartanChainSoundnessKS.mu_step`, for evaluators satisfying
  `EvalsOK`), perfect completeness of the SNARK for every oracle (`snark_complete`) and of the
  honest tables (`chainHonest : HonestOps`), the query bound (`queries_le`, at most `2^14`), the
  parametrised certificate (`Submission.certificate (F : Facts)`), the positive and negative
  controls of `reports/controls.md` (every definition the certificate relies on has both).

What is not yet done: `EvalsOK chainEvals` from `chainMats_eq`/`chainPub_eq`, the `KState` and
`Facts` record, `SpartanChainFinal.lean`, the solution against the rendered challenge, the three
negative claims, `HARNESS=1 check.sh` (comparator with both kernels, gate), the prover
byte-identity KAT and the final measurement run: all `TBD (final run)`.

### 3.5 What was reusable, and what was not

Reusable, and reused:

- **leanerVM's BLAKE2s circuit framework** (`Flock/{Circuit,Builder,Words}.lean`,
  `Blake2sCircuit.lean`, 1,543 code lines copied with modifications, plus 90 lines of the
  Frobenius map): the only existing proved BLAKE2s R1CS; its `compress` was bridged to the
  contract's by one lemma. Copied, not imported: leanerVM imports ArkLib and CompPoly modules
  outside the allowlist and uses the module system and `#guard` tests, which the source rule
  refuses.
- **leanVM's architecture** (E3): binary field `GF(2^64)`/cubic extension, Flock = Spartan over
  binary fields, ring switching (Annex A), the one-compression Merkle framing; the Rust prover
  follows its field conventions, FFT structure and stage order, and its circuit is a line-by-line
  transcription that leanerVM itself transcribed from leanVM's `hash.rs`.
- **CompPoly's `BF64`/`Ext3`** as the specification field (allowlisted after S2's regeneration;
  too slow compiled, hence D-5).
- **The S2a entry's linear decoder** (54 lines copied) and the library's `E`, `img`, `fuel`,
  `computes`.
- **Mathlib**: `Polynomial.card_roots'`, double counting, `Hamming`, the RS distance.

Not reusable:

- **ArkLib** is not allowlisted; its AHIV22 proximity lemma pulls a 102-module, 24.7 k-line
  closure through VCVio/PolyFun; its Spartan, BCS/FS, FRI, Binius and ring-switching files
  carry `sorry` or are definitions only (E2 §7). `Proximity.lean` was written fresh with ArkLib as
  the guide (statement unchanged, row-by-row induction instead of the maximal-support argument).
- **VCVio's Merkle extractor** (107–158 modules): not allowlisted, and the contract's
  `OProg`/`Log` is a different formalism.
- **Clean** is a frontend, never on the badge path (E4).
- **leanerVM's sumcheck and lincheck security** is ArkLib-framework code; only its mathematics
  (`card_badChallenge_le`'s shape) informed the design.

A reader should note that most of today's fresh Lean (the field, the algebra, the RS/proximity
layer, Merkle/transcript on the log, the generic potential with its round-split lemma, the
BLAKE2s R1CS bridge) is protocol-independent and is the organiser library §4 recommends.

---

## 4. Recommended rule changes, ranked

Each with what it costs in trust (lines of the 500-line contract, or none) and what it saves.

1. **Adopt the potential-form `KS` with `logCap = 2^96`** (branch `v3/ks-potential`, reviewed and
   fixed). Trust cost: +3 contract lines, one instance whose content is irrelevant (`Fintype` is a
   subsingleton), the paper theorem kernel-checked. Without it, no honest entry exists.
   Follow-ups: the design text from the ledger; a `V31` control for the potential-level guard
   (open); the `AGENTS.md` note on the `Fintype` snag.
2. **An organiser library of verified gadgets**, upstreamed from this entry and the core:
   the word-level `BF64`/`Ext3` with its CompPoly isomorphism (858 lines; makes `T_V` reachable
   at all); the BLAKE2s R1CS gadget against the contract's hash (about 2,600 lines with the
   leanerVM copy); Merkle/Fiat–Shamir-on-the-log lemmas (`open_binding_prefix`, `tree_prefix`,
   `pred_unique_lt`, `bad_step_le`, the transcript forest); the generic potential with `muG_step`
   and the round-split lemma `extCount_split` (so a submitter supplies per-position facts, not a
   supermartingale); the AHIV22 proximity lemma; the MLE/sumcheck counting lemmas; the linear
   codec twins (#10). Trust cost: none (library modules are untrusted, kernel-checked); the
   allowlist gains the library's closure, which is Mathlib and CompPoly only. This is the single
   largest reduction of a submitter's work.
3. **Extraction rule for nodes** (#7): raise `B` to `2^48 + 2^16·t` now (no trust cost); then
   choose the organiser decoder image or the Lean-level cost model (60–100 trusted lines). Without
   a decision no recursive entry can be certified.
4. **Succinctness measurement** (#6): CPU time or a step count of an organiser-compiled image
   (O-18); calibrate against an optimised linear verifier; fresh directories per repetition.
   Trust cost: none.
5. **Recursion incentive** (#6b): the cap on sampled proofs at every level, or column R ranked
   beside T; correct §5.3 and §6.7. Trust cost: none.
6. **Allowlist policy**: say which of re-prove / copy / extend is intended for CompPoly's
   multilinear and RS modules and for ArkLib; the measured closures (E2 §1) show that only
   CompPoly's modules are cheap to admit (`Multilinear.Basic`: 3 modules). Trust cost: none for
   a `sorry`-free, kernel-audited closure; the gate already checks axioms transitively.
7. **`proofCap` and the hash menu** (#8): one of (i) document that recursion closes only with
   WHIR-class sizes, (ii) a larger cap for node proofs, (iii) an arithmetisation-friendly hash
   entry in a menu (O-14), (iv) a named proximity hypothesis. (iii) and (iv) change the trusted
   base (a second hash specification; or an axiom-like hypothesis the comparator must track).
8. **`T_V` calibration** depends on 4 and on compiled field speed; with the word-level field a
   leaf of `n = 16` verifies in 0.21 s and the four-leaf smoke root in about 1.1 s, so a cap of
   2 s on a root of 256 leaves is far from any Ligero-class entry; set `T_V` after the benchmark
   shape (`r`, `n`) and the measuring rule are fixed, not before.
9. **Counted completeness** (O-23) and an **indexer** in the submission (#8): a handful of
   trusted lines each; they unblock grinding and preprocessing designs and sharpen the O-25
   review.
10. **Library fixes** (#10): strict leaf branch, linear codec twins; **gate rule 4** with v3's
    field names; the trust statement naming core `extern`s. Trust cost: none.

---

## 5. What R1 is not

- **Not recursive.** Node proofs are witness-sending: a node carries both children's proofs
  verbatim and the node check runs the instantiated `Vb` on them, which is literally what `Rel`'s
  node clause states. No node circuit, no in-circuit BLAKE2s verification, no decoder. The SNARK
  work is at the leaves only.
- **Not rankable.** A node embeds its children and `Vb` rejects proofs above `proofCap = 2^20`
  bytes, so the `r = 8` root of the ranked benchmark (256 leaves) can never fit for any SNARK
  leaf above 4 KiB (blueprint §0, §13 item 1). R1's acceptance run is the `r = 2`, `n = 16` smoke
  tree (root 575,112 B). At the ranked leaf size the Ligero proof alone is 1.46 MiB. `T_V`
  therefore removes nothing R1 could have had; `verify_s = 60 s` is the bound that binds.
- **Certified only against the amended contract**, not the pin. The branch `v3/ks-potential`
  lives in a scratch clone; pushing it and opening the draft pull request was denied by the
  permission system in this session (consistent with `CLAUDE.md`'s "no pushing"), so this
  repository's pin has not moved and the entry builds against a development clone that tracks
  the branch (`PLAN.md` D-8).
- **Not yet end-to-end.** The `step` and `final` laws are proved for the real verifier, but the
  `KState` record, `Facts`, `SpartanChainFinal.lean`, the solution against the rendered
  challenge, the harness run and the prover byte-identity KAT are `TBD (final run)` (§3.4).
- **Extraction rule for R2 open.** R2 (recursive nodes, semi-uniform circuits, a WHIR- or
  FRI-class PCS, a circuit DSL with `toProg`/`toR1CS` and a correctness theorem) is designed
  (F1 §5.3) and blocked on #7. R3 (ranked) additionally needs one of the §4 item 7 decisions.
  Neither is started.

---

## 6. Open questions for the user

1. **Push and merge the amendment?** Push `v3/ks-potential` (`rf-core-ks`, head `05fde28`) to
   `scaraven/recursion.fast`, open the pull request referencing #5, and after the merge move this
   repository's pin in its own commit (`CLAUDE.md`, "The pin"). Until then the honest entry
   cannot be certified against anything the public core has.
2. **`logCap`**: keep `2^96` (the review's recommendation; operating points `2^-64` at `2^64`
   queries, `2^-32` at `2^96`), or `2^58` under the extractor's `2^60`-word tape (ADV-m7)?
3. **The extraction rule for nodes** (#7): raise `B`; then the organiser decoder image or the
   Lean-level cost model? The first recursive certification is blocked on it.
4. **The acceptance run for R1**: certified on the smoke tree and unranked (as designed), or
   change the node encoding so that a listed R1 is possible (a node that hashes its children's
   proofs, which is R2's extraction problem again)?
5. **`proofCap` / hash menu / proximity hypothesis** (#8, §4 item 7): which of the four, if any?
6. **Succinctness measurement** (#6): CPU time, single core, or an organiser-compiled step count
   (O-18)? And whether to rank column R beside T.
7. **The organiser library**: adopt the upstreaming of §4 item 2 as a core stage (S4), and the
   library fixes of #10?
8. **O-25**: the semantic rule in `AGENTS.md`, mandatory intake review with a challenge period,
   and the indexer?
9. **S2a open items** (`V3-S2a-RESULT.md` §7): the library's leaf malleability fix in the core;
   gate rule 4's v3 fields; the allowlist scope (`RecursionFast.Controls` in the closure); the
   stub and claim schema for S3.
10. **The `AGENTS.md` note** on the `Fintype Digest` elaboration snag (V3-S2-KS-m2), and whether
    a potential-level guard control (`V31`) is built in S4 or the paper argument (F1 §4.1) is
    accepted.
