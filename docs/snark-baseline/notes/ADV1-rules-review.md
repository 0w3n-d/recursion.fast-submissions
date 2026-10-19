# ADV1: adversarial review of the v3 security definitions, rules and cost model

Reviewed 2026-10-19, read-only, against the core pinned at `.contract` = `15e4ae5`
(`RecursionFast/Contract/*.lean`), `docs/design/DESIGN-v3.md`, `AGENTS.md` and the core's
`docs/reviews/V3-S1-review.md`. Method: the `adversarial-review` and `lean4:review` skills. Every
Lean claim below is kernel-checked in a probe under `logs/adv-probes/`, compiled with
`cd .contract && timeout 900 lake env lean <file>` after a green `lake build` of the pin
(`logs/adv-probes/build.log`). Every timing is a measurement with its log. All probes use only
`propext`, `Classical.choice` and `Quot.sound`.

**Lean in two lines.** A *query program* (`OProg`) is a tree whose inner nodes ask the oracle a
byte string and branch on the 32-byte answer. `KS` asks the submitter for a predicate `good` on
query logs and a predicate `bad` on (log, fresh query, answer) such that the empty log is good, a
good log stays good unless a fresh answer is bad, a good log makes every accepted proof
extractable, and `Bounded ε` holds: **for every log `L` and query `q`**, at most `ε·2^256` answers
are bad. The paper theorem is the union bound `(Q + qV)·ε`.

## Verdict

The contract is unusable as a ranking instrument in its current form, for two independent
reasons.

1. **The succinctness cap does not hold.** The certified witness-sending baseline, with five
   lines of `Task.spawn` (parallel threads, which the kernel treats as transparent) or with an
   unrolled BLAKE2s, checks the whole ranked tree in 1.2–1.3 s, 0.65 s or 0.04 s. The cap is
   `T_V = 2 s`. Such an entry is certified honestly and wins board T while proving nothing.
2. **`KS` is unsatisfiable for every practical hash-based SNARK.** `Bounded` is quantified over
   logs of unbounded length with a constant per-query `ε ≤ 2^-128`. That kills Merkle binding
   (ADV-M2). The per-query form cannot express a challenge spread over several 32-byte answers,
   and that kills FRI/WHIR/Ligero query phases (ADV-M3). Both are proved for toy verifiers whose
   ROM error is `2^-128` or smaller.

Under the contract as written, the only rankable entries are the ones the competition means to
exclude: non-succinct ones (ADV-M1) and oracle-recognising ones (O-25, made harder to review by
ADV-M5). Six further findings are major, and seven are minor.

| Id | Severity | One line | Evidence |
|---|---|---|---|
| ADV-M1 | **critical** | The `T_V` cap is beaten by the witness-sending argument, using threads or a fast BLAKE2s | measured, `fastchain.log`, `refchain.log`; `TaskRfl.lean` |
| ADV-M2 | **critical** | No `KState` below `ε = 1/2` for any verifier whose soundness needs collision resistance (every Merkle commitment) | kernel, `CountingForm.lean` `collision_not_capped`, `collision_no_bound` |
| ADV-M3 | **critical** | A challenge that spans `k` answers is charged per answer: a `2^-128`-sound 16-query verifier has no `KState` below `2^-8` | kernel, `CountingForm.lean` `product16_not_capped`, `eps_ge_density` |
| ADV-M4 | major | Board T does not reward recursion: witness-sending below the first SNARK level saves all inner node proofs; §5.3 and §6.7 claim the opposite | argument + measured verify costs |
| ADV-M5 | major | O-25 variants evade the proposed closure test and rule; the rule also bans §6.7-allowed designs; the polymorphic-digest fix cannot support Fiat–Shamir | kernel, `LiteralTrigger.lean` |
| ADV-M6 | major | Preprocessing SNARKs (Spartan+SPARK, hard-coded verification-key roots) cannot satisfy `Complete` over all oracles within `qV ≤ 2^16` | argument |
| ADV-M7 | major (usability) | `ImageComputes` needs a verified quasi-linear Reed–Solomon decoder in RV64 assembly | argument |
| ADV-M8 | major (design claim) | Hash-based accumulation (ARC, WARP), a stated reason for v3, is not expressible | argument |
| ADV-m1 … m7 | minor | Vacuous completeness through a fallback branch; liveness only on the fallback; ∀H edge cases; repeated runs on one directory; documentation drift; gate rule 4 still v2; trust statement | see below |

---

## Pass A: security definitions

### ADV-M2 (critical, over-strength): `Bounded` over unbounded logs excludes collision resistance, so it excludes every Merkle commitment

**Where.** `Contract/Security.lean:61-63`, `KState.Bounded`:
`∀ L q, Nat.card {a // k.bad L q a} ≤ ε * Nat.card Digest`. Its use is in `KS` (`:68-70`), with
`errorCap = 2^-128` (`Certificate.lean:69`).

**The problem.** The standard ROM analysis of a Merkle commitment (BCS; Chiesa–Yogev) charges
two bad events to each fresh query:
- *collision*: the answer equals an earlier answer in `L`;
- *inversion*: the answer equals a value already used inside an earlier query.

Each bad set has about `|L|` elements. `Bounded` must hold for **every** `L`, including logs with
more than `ε·2^256 = 2^128` entries. There the collision set is too big, so `bad` must drop some
earlier answers. Then `step` forces `good` onto a log that contains a collision. Then `final` must
extract from a log in which the adversary can open a commitment two ways.

**Kernel-checked counterexample** (`logs/adv-probes/CountingForm.lean`, log `CountingForm.log`):
- **The verifier.** `Vcol` accepts a proof naming two distinct queries with equal answers. Its
  ROM error is at most `(Q+2)^2/2^257`.
- **`collision_no_bound`.** For any relation with a statement `c₀` that has no witness, no
  `KState` of `Vcol` has bad sets of size at most `K` with `2K < 2^256`. The proof builds, by
  induction, a good log of `K+1` distinct answers whose next fresh query must count all of them as
  bad.
- **`collision_not_capped`.** No `KState` of `Vcol` is `Bounded errorCap`.

The argument transfers to any verifier that checks Merkle openings against roots it obtained from
the oracle. With two preimages of a root on a good log, the adversary opens adaptively after the
Fiat–Shamir challenge, so the extractor's reconstruction is wrong. `final` would then require `E`
to find a BLAKE2s preimage within `2^40` steps, which no one can prove. The E1 note
(`docs/snark-baseline/notes/E1-leanervm.md` §4a) suggests that bad sets could be confined to "the
specific nodes the extractor relies on". The probe rules that out: the adversary chooses which
pair collides.

**Fix (one line of contract).** Cap the length of the logs that `Bounded` constrains:

```lean
def KState.Bounded (k) (ε) : Prop :=
  ∀ L q, L.length < logCap → Nat.card {a // k.bad L q a} ≤ ε * Nat.card Digest
```

Take `logCap = 2^64`. Beyond the cap every answer may be bad, so `good` need not persist. The
paper theorem becomes "`(Q + qV)·ε` for `Q + qV ≤ logCap`". `ImageComputes` already restricts to
tapes of at most `2^60` words, so the two caps should agree.

**Positive control:** `colState_bounded` in the same file shows that `Vcol` has a `KState` at
`errorCap` under this fix (cap `2^128`: good = short and collision-free). The fix therefore admits
the standard collision analysis.

### ADV-M3 (critical, over-strength): a challenge drawn from several answers is charged per answer

**Where.** The same definitions. The oracle answer is fixed at 32 bytes (`Oracle.lean:15-20`,
`Digest = Vector UInt8 32`).

**The problem.** The query phase of FRI, STIR, WHIR, Ligero, Brakedown and Basefold needs
`t·log2 n` bits of position randomness. That is about 190 positions × 20 bits ≈ 3,800 bits under
unique decoding at rate 1/4. Implementations squeeze it from several answers
`H(st‖1), …, H(st‖k)`. The ROM error is the product `(1−δ)^t ≈ 2^-128`.

The counting form must put the event "all positions land in the agreement set" into the bad set
of a single fresh answer, whichever the adversary asks last. Conditioned on the others, that
answer is bad with probability only `(1−δ)^{t/k}`, about `2^-8`.

Two shortcuts do not work:
- **One answer.** This needs `t·log n ≤ 256` and `(1−δ)^t ≤ 2^-128`, which is impossible for any
  `n > 4` under unique decoding (E1 §4b).
- **A local PRG expanding one answer.** A sampler property of a concrete PRG over all `2^256`
  seeds cannot be proved in Lean.

**Kernel-checked counterexample** (`CountingForm.lean`):
- **`eps_ge_density`.** Take the verifier that asks `k` fixed queries and accepts iff every answer
  lies in `T`. Its ROM error is exactly `(|T|/2^256)^k`. For a relation with a witnessless
  statement, every `Bounded ε` `KState` of it has `ε·2^256 ≥ |T|`, **whatever `k`**.
- **`product16_ge`, `product16_not_capped`.** With `T` = "first byte is 0" and `k = 16`, the ROM
  error is `2^-128`, every `KState` needs `ε ≥ 2^-8`, and none is `Bounded errorCap`.

**Fix.** Give the oracle extendable output, either as an `OProg` constructor or as a length in the
query:

```lean
| queryN (q : ByteArray) (ℓ : ℕ) (k : (Fin ℓ → Digest) → OProg α)
```

Count `Bounded` over `Fin ℓ → Digest` (that is, `2^{256ℓ}` answers) for that query, and
instantiate it as `BLAKE2s(tagXOF ‖ enc64 ℓ ‖ q ‖ enc64 i)` (or BLAKE2Xs). This is about 15
trusted lines across `Oracle.lean`, `Security.lean` and `Certificate.lean`; `runLog` and `queries`
change accordingly. The alternative, a per-*attempt* bound, would need an adversary model, which
the design deliberately avoided.

### ADV-M7 (major, usability): `ImageComputes` requires a verified RS decoder in assembly

**Where.** `Contract/Extractor.lean:104-107`, with the budget `B t = 2^40 + 2^8·t` (`:92`).

**What a real `E` must do.** For a Merkle-committed code, the straight-line extractor:
1. rebuilds the committed word from the log's leaf queries;
2. **decodes it**: an accepted word may be any `δ`-close word, and the errors can sit on exactly
   the systematic positions holding the witness;
3. reads off the chain start, or the two child proofs (up to `2 × 1 MiB`).

**Why it is too expensive.** Decoding a codeword of length about `2^23` with Berlekamp–Welch
(`O(N^2)` ≈ `2^46`) exceeds the `2^40`-step budget. A quasi-linear decoder (Gao's algorithm with
an additive FFT) fits, but it has to be RV64 assembly with a full functional-correctness proof
against `Machine.run`. CompPoly has a Lean-level Gao decoder (`CompPoly.ReedSolomon.Gao`, seen in
`logs/probes/e2/build.log`), but it is not allowlisted and is not an image.

**Consequence.** Until O-15(2), "a verified decoder extractor image", exists, no succinct entry
can discharge `computes` with ordinary effort.

**Fix (user decision, Q1).** Either the organiser ships the decoder image as a library asset with
its `ImageComputes` lemma (O-15(2) becomes a precondition of board T), or Q1 is relaxed to "`E` is
compiled Lean, with a proved step bound in a Lean cost monad".

### ADV-M6 (major, over-strength): oracle-dependent constants are incompatible with `Complete ∀ H`

**Where.** `Contract/Security.lean:74-76` (`Complete` quantifies over every oracle function `H`),
together with `qV ≤ 2^16` (`Certificate.lean:69`).

**The problem.** A preprocessing SNARK hard-codes a verification key that the indexer computed
with the hash. Examples are the Merkle roots of Spartan's SPARK computation commitments, the
preprocessed columns of Plonkish systems, and Marlin's holographic index. Under a random `H` that
root has no known opening, so the honest prover cannot open it and `Complete` fails. The
alternatives fail too:
- **Recomputing the index commitment inside `V` under `H`** costs as many queries as the index has
  leaves, about `2^20` or more, above `qV ≤ 2^16`, and linear time against `T_V`.
- **Committing the index with concrete BLAKE2s under another tag** makes binding depend on BLAKE2s
  collision resistance, which no counting argument can charge.

**What remains.** Only transparent, uniform arguments can be certified: AIR/STARK, or uniform
R1CS whose matrix MLEs `V` evaluates succinctly. Spartan with SPARK cannot.

**Fix.** Add an indexer to the submission, `I : OProg Key` with `V : Key → Digest → Proof → OProg
Bool`:
- `KS` counts `I`'s queries in the log (they are made honestly, before the adversary);
- `Complete` uses `I.run H`;
- `Vb` uses `I.run blake2sOracle`, computed once at badge build (untimed);
- `qV` excludes `I`'s queries.

The cost is a handful of trusted lines. ADV-M5 explains why this also matters for O-25: a
hard-coded vk root and a backdoor trigger are the same syntactic object.

### ADV-M8 (major, design claim): hash-based accumulation is not expressible

**Where.** DESIGN-v3 §1 gives accumulation (ARC, WARP) as a reason for v3. The obstacle is
`Rel`'s node clause (`Relation.lean:89`), which requires `Vb c₁ π₁ = true`: **full** verification
of each child under **BLAKE2s**.

**Why it fails.**
- **Proof size.** In PCD from (split) accumulation, a node's proof carries the accumulator witness,
  which is linear in the step circuit and well above `proofCap = 1 MiB` for any circuit that
  verifies hash-based arguments.
- **Mixed oracles.** The child's `Vb` runs the decider under BLAKE2s. The parent's soundness is
  proved under a random `H`, and only full in-circuit verification turns a statement about `H`
  into one about concrete BLAKE2s. A decider outside the circuit, which uses the hash on Merkle
  roots, gives no such transfer.
- **The extractor has no source.** The child's accumulator witness is not in the parent's trace,
  so the extractor cannot output a child proof that `Vb` accepts.

**Fix.** Either correct §1 (v3 admits full recursion only, with every intermediate proof
succinct and fully verifiable), or change the node clause to an accumulation-shaped relation,
which is a design change.

### Vacuity check (no new finding)

- **`KState`.** `step` has teeth: ADV-M2 and ADV-M3 are, in passing, strong non-vacuity controls.
- **Knowledge content.** With `E = none` and a complete `V`, some honest log under some `H` is
  good (bad sets are `ε`-small), so `final` fails.
- **`Complete`.** It is vacuous only through a fallback branch (ADV-m1).
- **S1 vacuity fixes.** The step control, `queryThenAccept_ge_one`, is present.

---

## Pass B: incentives, cost model and harness

### ADV-M1 (critical): the succinctness cap `T_V = 2 s` does not exclude the witness-sending argument

**Where.**
- DESIGN-v3 §6.5: "the trivial root check takes 22–29 s", with "a margin of 10× or more" claimed.
- DESIGN-v3 §7.3: the baseline is "unranked by measurement".
- `AGENTS.md` §6.
- The calibration estimates use the reference `Contract/Hash/Blake2s.lean`, about 6 µs per
  compression.

**The exploit.** The certified witness-sending `V` (`Library/WitnessSending.lean`), with its
chain checks made fast in either of two legal ways:

1. **Threads.** Map the chain checks through `Task.spawn` and `Task.get`. These are core functions
   whose kernel definitions are transparent: `(Task.spawn f).get = f ()` holds by `rfl`
   (`logs/adv-probes/TaskRfl.lean`, which also proves `all_par` with `propext` only). The parallel
   check is therefore provably equal to the sequential one, the existing certificate carries over,
   and the source rule accepts the file (`srcrule/`, 0 findings).
2. **A fast BLAKE2s.** Keep the compression state in sixteen `UInt32` locals, fully unrolled, in
   core Lean with no `extern`. It matches `hashlib` (`fastchain.log`, line 1). Proving it equal to
   `chainStep` is a finite symbolic unfolding.

**Measured** on a 32-vCPU QEMU VM (not the reference machine), whole ranked tree (`r = 8`,
`n = 2^14`, 2^22 compressions), three runs each:

| `V`'s chain check | Time for all 256 chains | Log |
|---|---|---|
| reference BLAKE2s, sequential | 5.6–6.1 µs/compression → about 24 s | `refchain.log` |
| **reference BLAKE2s + `Task.spawn`** | **1.17–1.31 s** | `refchain.log` |
| unrolled BLAKE2s, sequential | 151–164 ns/compression → **0.64–0.69 s** | `fastchain.log` |
| unrolled BLAKE2s + `Task.spawn` | **37–43 ms** | `fastchain.log` |

**Consequence.** An honest, certified, non-succinct entry passes the root check. Its tree run is
just hashing the chains natively (2.1 ms per chain, `logs/probes/fieldbench.log`; about 20 ms on
32 cores), so it beats every SNARK on board T. The calibration rule of §6.5 ("raise `n`") cannot
close the gap. Even at `n = chainCap = 2^20`, the threaded unrolled check scales to about 2.6 s
(64× the 40 ms measured), far from the required `5 · T_V = 10 s`.

**Fix (all three needed).**
1. **Measure CPU time.** Use user + system CPU time of the root check, not wall time, or run it on
   one pinned core; this removes the threads.
2. **Calibrate against the best linear verifier.** The organiser publishes an optimised
   compiled-Lean chain checker, such as `FastChain.lean`'s `stepU`, and sets
   `T_V ≤ T_triv,best/10`. At the ranked size that is about 65 ms of CPU time. A FRI- or
   WHIR-shaped verifier with about `2^15` compressions at 160 ns plus about `2^16` field
   operations fits only if it is written with the same care.
3. **Make it deterministic.** Move to O-18 (a step count on an organiser-compiled RISC-V image);
   it also removes threads and machine noise.

If 65 ms is judged too tight for compiled Lean, the benchmark has to change: fewer and longer
leaves (for example `r = 4`, `n = 2^20`), which shifts weight from recursion to chains.

### ADV-M4 (major): board T rewards avoiding recursion

**Where.** DESIGN-v3 §6.7, row "Recursion only near the root, concatenation below: allowed; the
first recursing node arithmetises `2^j` verifications and pays in `T_tree`". Also §5.3 ("a prover
cannot flatten the tree").

**The strategy.** Leaves and nodes below level `j` carry witness-sending proofs: the starts,
48 bytes per leaf. They cost nothing to "prove". The `2^{8−j}` nodes at level `j` are SNARKs of
"both witness-sending children are accepted", which means proving the `2^j` chains in-circuit.
Levels above `j` recurse honestly.

**What it costs.** Total proving work is the same chain work as honest leaf proofs, plus only
`2^{8−j} − 1` recursive nodes instead of 255. "Arithmetising `2^j` witness-sending verifications"
is exactly the leaf work, not an extra cost. So the row's "pays in `T_tree`" is false: it saves
`255 − (2^{8−j} − 1)` node proofs. The limit `j = 8` is one flat SNARK over all 256 chains (2^22
compressions) and no recursion at all.

**Which checks it passes.**
- **Sample checks.** A level-7 witness-sending proof verifies in 2^21 compressions, about 12 s at
  reference speed, inside `verify_s = 60 s`.
- **Canaries.** They pass, because witness-sending decoding is strict.
- **The root check.** Its time is one SNARK verification.
- **Column R.** It becomes huge, but R is not ranked.

**What limits it.** Only memory (96 GB) and parallel efficiency bound `j`. KS still "enforces the
topology" in the sense that valid child proofs exist, but not that they were produced by
recursion, which is what the score is meant to price.

**Fix (design decision).** Apply the CPU-time cap of ADV-M1 to sampled proofs **at every
level**. With `n = 2^14` and 160 ns per compression, a witness-sending proof at level `j` costs
`2^{j+14}·160 ns`. That is about 42 ms at `j = 4` and 84 ms at `j = 5`, so a 65 ms cap forces
recursion from level 5 up but not below. Forcing it at every level needs a level-1 witness-sending
proof (`2n` compressions) to cost about 5× `T_V`. At `T_V = 65 ms` that means `n ≈ 2^20`, which
is `chainCap`. The alternative is to rank column R beside T.
In any case §5.3 and §6.7 should be corrected.

### ADV-M5 (major): O-25, the oracle-recognising backdoor, in new forms

**Known.** `Controls/Backdoor.lean` and GitHub issue #4. The proposed defences are the rule "`V`
must not evaluate the oracle's instantiation" (§6.7) and the S1 gate speed bump: reject a `V`
whose closure contains `blake2sOracle`, `Submission.Vb` or `tagRO`, and flag one that contains
`Blake2s.compress`.

1. **A literal trigger evades the gate test (kernel-checked).** `logs/adv-probes/LiteralTrigger.lean`
   replaces `trigger := blake2sOracle q0` with a 32-byte literal computed offline by `hashlib`.
   - `Vlit_eq : Vlit = Backdoor.V` (by `decide +kernel` on one BLAKE2s), so `backdoor_lit` gives
     `Certificate` and the 32-byte magic proof of every statement.
   - The closure scan (`LiteralTrigger.log`) shows that `Vlit`'s closure contains no
     `blake2sOracle`, `tagRO` or `Submission.Vb`.
   - It does contain `blake2s256` and `compress`, **exactly as the honest `WitnessSending.V`
     does**. The proposed test cannot tell them apart.

   The visible trace is "an oracle answer compared with a 32-byte constant". A preprocessing
   verifier's Merkle-root check has the same form (ADV-M6), so a rule cannot ban one without the
   other.
2. **A trace-check trigger.** `V` legitimately contains the constraint evaluator of its own
   circuit, including the in-circuit BLAKE2s(`tagRO`‖·) gadget it uses for Merkle hashing. A
   "debug mode" branch that checks a proof-supplied concrete trace of that gadget, with output
   equal to the oracle's answer to `q = c`, recognises the instantiation. The bad set is one
   answer per query, so it is certified at `errorCap`. `V` evaluates no hash: it only checks
   constraints. Canaries pass because the magic proof is bound to `c`. Per proof the prover
   generates one BLAKE2s trace.
3. **The rule is over-broad.** A concatenation node, which §6.7 explicitly allows, verifies child
   SNARK proofs locally and therefore evaluates BLAKE2s(`tagRO`‖·) inside `V`. So does a hard-coded
   verification key (ADV-M6). A "consistency fast path", which skips re-verification when the
   oracle agrees with a locally computed transcript, is a natural optimisation and is exactly the
   backdoor.
4. **The O-25 candidate fix cannot work** (DESIGN-v3 §12): a `V` polymorphic in an abstract
   digest type `D` with `DecidableEq` only.
   - **If answers stay opaque.** `V`'s decisions depend on answers only through equality patterns,
     which are "all distinct" for a random oracle with overwhelming probability, so no
     Fiat–Shamir challenge can be derived.
   - **If a challenge interface yields `b` bits per answer.** `V` can compare `b` locally computed
     bits, and recognition has error `2^-b`. Knowledge error `ε ≤ 2^-128` needs `b ≥ 128`, which
     certifies recognition at `errorCap`.

   The tension is information-theoretic. Keying or salting does not help either: the S1 review's
   two-query Markov argument (V3-S1-M1, "Why no salting fixes it") still holds when the key is
   read from the proof.
5. **The rulebook does not state the rule.** `AGENTS.md` says nothing about oracle recognition
   (grep for "O-25", "recogni", "magic": no hits), although the S1 review calls intake review "the
   binding defence".

**Fix.** There is no mechanical one in the ROM. The recommendations:
- state the rule in `AGENTS.md`, semantically, together with the disqualification;
- require the entry's `NOTES.md` to list every place where `V` compares an oracle answer with
  anything other than another oracle answer or a proof-supplied value that is subsequently hashed
  by the oracle;
- make intake review mandatory, with a public challenge period before a record stands;
- drop the "polymorphic `D`" candidate from O-25.

---

## Minor findings

- **ADV-m1. Completeness through a fallback branch is vacuous, and liveness tests only the
  fallback.**
  - **Where.** `V3-4`; §6.3 step 8.
  - **The gap.** With `V = SNARK ∨ witness-sending` and `P` = the witness-sending prover,
    `Complete` is the baseline's proof. Nothing about the scored SNARK path is ever proved complete.
    The liveness check then runs `P` (no queries, an empty log) and the 8-instruction copy image.
  - **Fix.** Run liveness on the **native prover's** proofs, with a query log the native prover
    must emit. The harness checks that every entry hashes correctly and that the log contains
    `V`'s queries, then runs `img`. The output is decidable: `Rel` for a leaf, and `Vb` on the
    extracted children for a node.
- **ADV-m2. Perfect completeness over every `H` forces 2^-170 edge cases into `V`, `P` and the
  proofs.**
  - **Examples.** An out-of-domain point that lands in the trace domain (DEEP-ALI divides by
    `Z_D(z) = 0`); any rejection sampling.
  - **Fix.** O-23 (counted-error form), which also unblocks grinding. The S1 review's m10 (mark
    §6.6's `δ` row and §6.7's grinding row "after O-23") is **not applied** in DESIGN-v3 or
    `AGENTS.md` §6.
- **ADV-m3. Repeated runs on the same instances.**
  - **Where.** §6.3 step 9 repeats steps 3–6 "on the same instances" and takes medians, but does
    not say that each repetition gets a fresh `DIR` and that nothing persists.
  - **The exploit.** A prover that finds its previous `root.bin`, or a cache file outside `DIR`,
    makes two of three runs instant, and the median is the cached time.
  - **Fix.** Carry over v2's "fresh step directory, the only writable path" (harness README) to
    every repetition.
- **ADV-m4. Documentation drift.** `AGENTS.md` misstates the contract in several places; the
  contract is what is checked, so a submitter who follows the rulebook is misled:
  - `AGENTS.md:46` and DESIGN §2.1 use `Digest := Fin 32 → UInt8`; the contract uses
    `Vector UInt8 32`.
  - `AGENTS.md:49` gives an untagged `chainEnd`.
  - `AGENTS.md:58` omits `n ≤ chainCap` from `Rel`.
  - `AGENTS.md:78,87,148,220` give `fuel : ℕ → ℕ → ℕ` and `B p l`; the contract has `fuel : ℕ → ℕ`,
    `B t` over tape words, and an image-size conjunct.
  - `AGENTS.md:146-148` says "`L` of at most `2^24` entries", which the S1 fix of M3 removed.
  - `AGENTS.md:90` says the `img` binding is in `Certificate`; it is `CertificateR`.
  - `AGENTS.md:406-408` says "your proof system never queries a string the relation hashes". S1
    m7 reworded this claim in `Relation.lean`, but `AGENTS.md` still states it.
  - DESIGN §6.5's "22–29 s" and §6.7's "pays in `T_tree`" are refuted by ADV-M1 and ADV-M4.
- **ADV-m5. Gate rule 4 is still v2.**
  - **Where.** `scripts/Gate.lean:251-256` lists `Submission: [P, cfg]`.
  - **The gap.** On a v3 `Submission` that is not computable as a whole, it fails closed
    ("structure … has no field cfg") and never checks `V`, `E` or `img`.
  - **Fix.** This is S3's ("rule 4's new fields"). Note that the baseline's proof half at S2
    cannot pass rule 4 with a noncomputable `ε` until then.
- **ADV-m6. The trust statement should name core `extern`s.** §8 item 6 trusts "what Lean's
  compiler emitted for `Vb`". Entries may call core functions whose compiled code is an `extern`
  with a Lean reference body, such as `Task.spawn`/`Task.get` (ADV-M1) and the `Array`/`ByteArray`
  primitives. Their agreement with those bodies is an extra trusted assumption. The badge `verify`
  may also be multi-threaded (ADV-M1).
- **ADV-m7. Restate the paper theorem after the fixes.** After ADV-M2 it holds for
  `Q + qV ≤ min(logCap, 2^57)`; the second bound is the extractor's addressable tape. The `2^64`
  figure in §4.5 and `AGENTS.md` §5 should be quoted with that domain.

## Other checks: no finding

- **`runLog`'s first-match rule and duplicate log entries.** Logs reached through `step` never
  contain a duplicate query (`step` requires freshness), and `good` is the submitter's choice, so
  duplicates only weaken the obligation. `runLog` follows the run of the oracle "first answer in
  `L`, arbitrary elsewhere", so the `∀ H` query bound covers it.
- **The `qV` bound against `runLog`.** Covered by the same argument.
- **`decodeWit` leniency.** The decoded witness must still be in `Rel`, so leniency only lets the
  image do less work.
- **`enc64` mod `2^64`.** It is injective under `n ≤ chainCap`.
- **The tags.** No chain, leaf or node preimage starts with `tagRO`.
- **`Rel S.Vb`'s mixed semantics for full recursion.** The node clause is about concrete BLAKE2s,
  and the parent's theorem is over a random `H`. For full in-circuit recursion this is consistent:
  the circuit enforces `Vb` concretely. It fails only for accumulation (ADV-M8).
- **`CertificateR` and `Declared`.** `D.fuel ≤ B` is now bound (S1 m9 fixed).

## Status of the S1 review's fixes at the pin

| S1 finding | Status |
|---|---|
| M1 (backdoor) | documented control `Controls/Backdoor.lean`; the gate speed bump is not built (S3) and is evadable (ADV-M5.1) |
| M2 (step never exercised) | **holds**: `queryThenAccept_ge_one`, `ks1` |
| M3 (2^24-entry log bound) | **holds**: only the `2^60`-word tape bound remains (`Extractor.lean:105`) |
| m1, m2, m3, m4, m5, m6, m9 | **hold**: the controls are present (`Controls/Relation.lean:145-160`, `Security.lean:138`, `Certificate.lean:41,69-94`, `Extractor.lean:125-144`) |
| m7 (separation wording) | fixed in `Relation.lean`; **still stated** in `AGENTS.md:406-408` |
| m10 (δ and grinding rows) | **not applied** (DESIGN §6.6, §6.7; `AGENTS.md` §6) |

## Probes and logs (`logs/adv-probes/`)

| File | What | Result |
|---|---|---|
| `CountingForm.lean` | ADV-M2 (`collision_no_bound`, `collision_not_capped`), ADV-M3 (`eps_ge_density`, `product16_ge`, `product16_not_capped`), the fix's positive control `colState_bounded` | `CountingForm.log`: standard axioms, 6.4 s |
| `LiteralTrigger.lean` | ADV-M5.1: literal-trigger backdoor `backdoor_lit`, closure scan of three verifiers | `LiteralTrigger.log` |
| `TaskRfl.lean` | ADV-M1: `Task.spawn` is kernel-transparent; a parallel `all` equals the sequential one | `TaskRfl.log`; source rule: `srcrule/`, 0 findings |
| `FastChain.lean`, `RefChain.lean` | ADV-M1 timings: unrolled and reference BLAKE2s, sequential and `Task.spawn`, KAT against `hashlib` | `fastchain.log`, `refchain.log` (3 runs each; 32-vCPU QEMU VM, load average 1.2–2.8) |
| `build.log` | `lake build` of the pin (contract, library, controls) | green, 1,251 jobs |
