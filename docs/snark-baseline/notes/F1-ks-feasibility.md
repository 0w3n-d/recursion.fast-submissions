# F1. Can an honest BCS/Spartan-style SNARK be certified against the v3 contract?

Status: ideation memo, 2026-10-19. Read against the core at the pin `15e4ae5`
(`.contract/RecursionFast/Contract/{Oracle,Security,Extractor,Certificate,Relation}.lean`),
DESIGN-v3 §2–§6, §12, the S1 review (`.contract/docs/reviews/V3-S1-review.md`) and the
research notes R5, R7. Nothing here is implemented or kernel-checked; every claim is a paper
argument, marked where it rests on an estimate. Finding ids are `F1-n`.

Notation. `Digest = Vector UInt8 32`, `|Digest| = 2^256`. A knowledge state `k` has `good`,
`bad`, `empty`, `step`, `final`; `k.Bounded ε` is `∀ L q, #{a | bad L q a} ≤ ε·2^256`;
`errorCap = 2^-128`, so at the cap **at most `2^128` answers to any fresh query may be bad**.
A log is *reachable* if it is `[]` or `L ++ [(q, a)]` with `L` reachable, `q` fresh and `a` not
bad; by `empty` and `step` every reachable log is good, and since fewer than `2^256` answers are
bad, every fresh query has a non-bad answer, so reachability never gets stuck.

---

## 0. Verdicts in one screen

| | Verdict | Why (section) |
|---|---|---|
| H1 unbounded logs | **Confirmed.** No bounded `KState` at `errorCap` exists for any verifier whose acceptance hinges on a fresh answer equalling a digest that an earlier query of the log committed to (every Merkle-plus-Fiat–Shamir verifier). The attack log is explicit, about `2^130` entries: `2^128 + 1` dangling transcripts over one committed word just beyond the extractor's decoding radius, with position answers chosen accepting (free, since `bad` excludes at most `2^128` of `≥ 2^192`), then one top query whose hit set is the `2^128 + 1` roots. Nothing is lost for `Q ≤ 2^64`, which is why a length guard is free. No `good`/`bad` choice escapes, semantic ones included. | §1 |
| H2 single-answer challenges | **Confirmed.** The boolean counting form charges the worst conditional per answer; a query phase that draws `t` positions from `k > 1` answers is charged `(1−δ)^{t/k}` at its last answer, and `t·log n > 256` forces `k > 1`. No explicit hitter with `2^-128` error on 256 bits is available to prove. Escapes examined, none survive. | §2 |
| H3 extractor image | **Confirmed, and worse than stated.** Node extraction cannot read child proofs off the log at all: `Rel` demands `Vb c₁ π₁ = true` under **concrete** BLAKE2s while the log is the **random** oracle; the only source of a child proof is the decoded R1CS witness. Leaf extraction can be parsing (witness in the clear). A verified quasi-linear RS decoder in RV64 assembly is what an honest node extractor needs, and it does not fit `B t = 2^40 + 2^8 t` at node size. | §3 |
| Amendment | Potential `μ : Log → ℝ≥0` (average rise `≤ ε` per fresh answer, extraction below `1`) **with** a log-length guard `logCap = 2^64`: 18 contract lines, same paper theorem `(Q + qV)·ε` by a stopped supermartingale and Markov, the boolean form embeds as a library constructor, every S1 control ports, two controls are added that separate old from new. | §4 |
| Design ranking | Spartan-style R1CS sumchecks over `BF64`/`Ext3`, semi-uniform circuits (no SPARK), a WHIR-class PCS for size or Basefold-class for proof effort; Ligero/Brakedown are out (`proofCap`). At the ranked size the honest recursive baseline does not close under `proofCap`, R1CS and BLAKE2s-only Merkle hashing; it closes as *certified and unranked*. | §5 |
| Extraction rule | Raise `B` to `2^48 + 2^16·t` regardless; decide between an organiser decoder image (O-15(2)) and a Lean-level cost model for `E`; first baseline avoids the question by making leaves parse and nodes witness-sending. | §6 |
| Prompt | "Passes the security definitions" is infeasible for any succinct hash-based `V` as the contract stands; the amendment is a precondition, not a second-priority tweak. R1CS and BLAKE2s-only hashing are in tension with "decent". Ten autonomous decisions and nine issues to file. | §7 |

---

## 1. H1: `Bounded` over all logs is unsatisfiable for Merkle-committing verifiers

### 1.1 What a Merkle-plus-Fiat–Shamir verifier looks like to the contract

Any succinct hash-based `V` has, for some proof `π = (r, aux, openings)` and statement `c`:

* an FS query `q_FS(c, r)` (the root `r`, 32 bytes, is a chunk of the query) whose answer `ch`
  is the challenge;
* path queries: leaf queries and inner queries `x ‖ y` (64 bytes) whose answers climb to a top
  query `q_top` whose answer `V` **compares with `r`**;
* local checks on the opened leaves that depend on `ch`.

Property (P), which holds for every argument whose soundness rests on the commitment binding
(every PCS: the polynomial may be chosen after the evaluation point; every proximity test: the
word may be chosen after the positions): **for every statement `c` and every challenge value
`ch` there is a leaf vector `ℓ(ch)` that passes the local checks, and `ℓ(ch)` carries no
witness.** An argument violating (P) would be sound with a non-binding commitment, i.e. would not
need the oracle at all.

### 1.2 The attack log (explicit)

Fix any `V` as above, any `E`, any `KState k` for `(Rel Vb, V, E)` with `k.Bounded errorCap`.
Two ingredients, both forced on a provable design:

* **(Q) multi-answer positions.** The opened positions of a transcript `T` are derived from
  `k ≥ 2` oracle answers `H(T ‖ 1), …, H(T ‖ k)` (§2.1: `t·log₂ n > 256` bits are needed).
* **(W) a word beyond the decoding radius.** Take a *true* statement `c*` with witness `z*`,
  the honest committed word `u* = Enc(z*)`, and `ℓ := u*` corrupted on a set `D` of positions
  of relative size `δ'` just above the radius within which `E` decodes. Every algebraic check of
  `V` (sumcheck messages, folds, final evaluations, all computed honestly from `z*`) passes for
  every challenge; the query phase passes exactly when the opened positions (and their folded
  images) avoid `D`. For `V` to be certifiable in the honest order at all, `(1 − δ')^t < 2^-128`
  must hold; so the accepting fraction **per position answer** is `(1 − δ')^{t/k} ≥ 2^{-128/k} ≥
  2^-64`, i.e. at least `2^192` of the `2^256` answers, while `bad` excludes at most `2^128`.
  And `E c* π L` is not a witness: `E` is a fixed unique decoder and `ℓ` is beyond its radius
  (corrupt beyond any list-decoding radius too if `E` is cleverer).

**Phase 1 (`N = 2^128 + 1` dangling transcripts over one tree).** Pick distinct roots
`r₁, …, r_N`, none of which has a preimage in the log. For each `i`, append the fresh FS query
`q_FS(c*, rᵢ)` with any non-bad answer, then the fresh position queries `H(Tᵢ ‖ j)`,
`j = 1..k`, choosing each answer **non-bad and accepting for `ℓ`** (possible: `≥ 2^192` accepting
answers, `≤ 2^128` bad ones). Nothing `bad` can do prevents this: at these steps the root is
dangling, so `bad` cannot refer to `ℓ`, and whatever it refers to it excludes at most `2^128`
values.

**Phase 2 (the tree).** Append the Merkle tree over `ℓ` bottom-up with fresh queries (leaf
queries, then `x ‖ y` inner queries; choose answers that do not make a later query repeat an
earlier one — only the tree's own queries can collide, a few thousand values to avoid). Stop
before the top query `q_top`.

**The bad set.** Let `L` be the log so far; it is reachable, hence good. For every `i ≤ N`,
`L ++ [(q_top, rᵢ)]` answers every query of `V c* πᵢ`, `πᵢ := (rᵢ, honest messages of z*,
openings of ℓ at positionsᵢ)`, and `V` accepts: the FS and position answers are those chosen in
Phase 1, the path answers are those of `L`, the top answer is `rᵢ`. If `rᵢ` were not bad,
`L ++ [(q_top, rᵢ)]` would be good by `step`, and `final` would make `E c* πᵢ _` a witness of
`c*`, which by (W) it is not. So every `rᵢ` is bad for `(L, q_top)`:
`#{a | bad L q_top a} ≥ 2^128 + 1 > errorCap · 2^256`. **No bounded `KState` at `errorCap`
exists.** ∎

The log has about `2^130` entries. That is irrelevant to the definition, which quantifies over
every `L`, and it is the whole point: the union bound `(Q + qV)·ε` says nothing once `Q ≥ 2^128`,
so the contract is demanding a bound in a regime where the theorem it serves is vacuous. In the
real ROM the same adversary would succeed with probability about `N·2^-128` by the query phase
alone, without any late preimage; the counting form lets it take the lucky position answers for
free (`step` admits every non-bad answer) and then charges the hit, which is why `N` dangling
targets is the lever.

Without (Q) (a single-answer challenge, which §2 rules out anyway) the construction needs
`2^128 + 1` transcripts sharing one challenge value; a `bad` that marks the `2^128` most frequent
previous FS answers forces about `2^256` distinct FS queries for that, at the edge of the `2^256`
roots available. The two-ingredient version above does not have this weakness.

A **control-sized** version uses a toy `V` whose leaf check reads one byte of the challenge
(`accept iff H(x) = r ∧ x[0] = ch[0]`): classes are the 256 first bytes, so `256·(2^128 + 1)`
FS steps give a class of size `2^128 + 1` and no `bad` can exclude a class (`2^248 > 2^128`).
This is the proposed negative control `merkleToy_no_kstate` for the current contract (§4.6).

### 1.3 Escapes examined

| Candidate escape | Why it fails |
|---|---|
| Semantic `good L := "no accepted unextractable proof on L"`, `bad` := "the answer breaks it" | This is the *weakest* `good` consistent with `final`; the construction above never mentions `good`, only reachability and the count at `q_top`. |
| `good` false beyond some length, or counting dangling roots | At the threshold `step` needs every answer bad: `2^256 > 2^128`. |
| `good` vacuous on long logs | `final` then requires extraction on them. |
| 512-bit roots (two answers) | The first half's hit set still has `|I|` elements. |
| `V` checks that no two digests in `π` coincide, or any local condition | `V` never sees `L`; `πᵢ` has no repeated digest. |
| Challenge derived from all leaves (`q_FS` contains `ℓ`) | Non-succinct: `V` must query a `|ℓ|`-byte string. The witness-sending argument is the limit case and is unaffected. |
| Accumulation instead of per-level SNARKs | Also Merkle-committed. |
| `V` with no oracle queries and BLAKE2s computed locally | KS on the empty log is standard-model knowledge soundness: unprovable. |

**F1-1.** `KS` at `errorCap` is unsatisfiable for every succinct verifier of this competition.
Only the witness-sending family (no commitment, or `qV = 0`) and the CGH backdoor are
certifiable today.

---

## 2. H2: one answer per `ε` cannot price a multi-answer query phase

### 2.1 The argument

Let the query phase open `t` positions in a domain of size `n`, with the proven per-position
bit yield `b = −log₂(1 − δ)`; `(1 − δ)^t ≤ 2^-128` needs `t ≥ 128/b` positions. In the proven
regimes `b ≤ 1` (unique decoding caps at one bit per query; R7 §3.4: UDR at `ρ = 1/2` needs
309 positions, at `ρ = 1/16` 141; Johnson at `ρ = 1/16` 64). So `t·log₂ n ≥ 128·20 ≫ 256` bits of
position randomness are needed, i.e. the positions come from `k ≥ 10` oracle answers
`H(T ‖ j)`, `j = 1..k`, or from a chain of them.

Boolean counting: at the step appending `(H(T ‖ k), a_k)`, `bad L (H(T‖k)) a_k` may depend on
`L`, which contains `a_1..a_{k−1}`. Take the reachable log in which `a_1..a_{k−1}` all derive
positions that miss the disagreement set of a far committed word (each such answer is one of
`≥ 2^256 − 2^128` non-bad ones, so such a log is reachable whatever `bad` says about it — and if
the submitter marks them bad, that step already has `(1 − δ)^{t/k}·2^256 > 2^128` bad answers).
At the last step the answers for which `V` accepts the unextractable proof have fraction
`(1 − δ)^{t/k} ≥ 2^{-128/k} ≫ 2^-128`; by the same argument as §1.2 they must all be bad.
**No bounded `KState` at `errorCap`.**

The loss is structural: the counting form bounds the worst conditional probability per answer,
and a product `∏ p_j` of `k` conditionals with `∏ p_j ≤ 2^-128` has `max_j p_j ≥ 2^-128/k`. In the
real ROM the adversary cannot retry `H(T ‖ k)` without changing `T`, which refreshes all `k`
answers; the boolean form gives no credit for the `(1 − δ)^{t(k−1)/k}` the prefix cost.

### 2.2 Escapes examined

| Candidate | Status |
|---|---|
| All positions from one 256-bit answer via an explicit map | Information-theoretically possible (a hitter needs about `log n + 128 ≈ 148` bits) but no explicit construction reaches `2^-128` error with `≈ 300` samples from 256 bits: expander walks cost `≥ 1` random bit per bit of hitting at these densities, `k`-wise independence needs `k·log n` bits, extractor-based samplers have `poly(1/ε)` sample complexity. A random function is a hitter, but "the oracle is a random function" is what the contract charges per answer. |
| Algebraic challenges only (sumcheck, batching, folding) | Fine for those rounds: `d/|Ext3| = d/2^192 ≪ 2^-128` per answer. The query phase has no algebraic form in any hash-based PCS; a PCS without a query phase is not hash-based. |
| List-decoding / Johnson regime | Fewer positions (64–140) but still `> 256/log n`; and the regime's theorems are deep (R7 §3). |
| Re-commit per position (one position per round) | Then each round's error really is `(1 − δ)` (state restoration is a real attack); no gain. |
| Proof of work / grinding | Not expressible: `Complete` is perfect over **every** oracle function, and an adversarial `H` defeats any bounded nonce search; `OProg` is inductive so unbounded search is impossible (O-23). |
| Larger `qV` | Each of the verifier's own queries is charged the same way. |
| Tightening `errorCap` (O-21) | Makes it worse. |

**F1-2.** Under the boolean form at `errorCap`, no BCS-compiled IOP with a provable
`(1 − δ)^t` query phase is certifiable. Fixes: a potential (§4), or a long-answer oracle.

---

## 3. H3: node extraction means decoding; leaves can parse

### 3.1 The oracle/BLAKE2s split (new finding)

`Rel S.Vb c (.node c₁ c₂ π₁ π₂)` requires `Vb c₁ π₁ = true`, where `Vb` runs `V` under
`blake2sOracle`, a **concrete function**. `final` must produce such `π₁` from `(c, π, L)` for
**every** good log `L`, whose answers are **arbitrary digests** (the random oracle). Hence:

* An `E` that looks a child proof up in the log (the prover queried `H(π₁)`, the node proof
  carries the answer `h₁`, `E` scans for the entry with answer `h₁`) **cannot be proved**: the
  SNARK attests, through an in-circuit BLAKE2s, that *some* `π₁'` with `BLAKE2s(π₁') = h₁` is
  accepted; the log's preimage `π₁` of `h₁` under `H` is unrelated to `π₁'`. Same for any scheme
  that rebuilds the child's Merkle openings from `L`: the rebuilt paths are `H`-valid, `Vb`
  needs them BLAKE2s-valid.
* The only object the theorem ties to `Vb c₁ π₁' = true` is the **decoded R1CS witness** `z` of
  the node circuit, through the circuit-correctness lemma `R1CS_node(c, c₁, c₂, z) → ∃ π₁' π₂',
  z encodes them ∧ Vb c₁ π₁' = true ∧ Vb c₂ π₂' = true`, which is a statement about BLAKE2s
  gadgets and the concrete `V`, with no oracle in it. (This is the ROM-recursion heuristic of
  §5.4 embodied in one lemma; it is provable, unlike the log route.)
* Therefore `E` for a node must recover `z` from the committed word in `L`: find the Merkle
  tree under the root (by answer, through the log), read the leaves (the codeword), and
  **decode** to the nearest codeword. Reading the systematic part of a δ-close word is not
  enough: a cheating word corrupted in an unopened systematic position is accepted with
  probability about `1 − t/n`, so `final` would be false for a parsing `E`.

Child proofs in the clear instead of decoding fail `proofCap`: the root would carry every
SNARK of the tree (`255 × ≥ 100 KiB`). Child *transcripts* in the clear with openings rebuilt
from `L` fail by the oracle/BLAKE2s split above.

### 3.2 Leaves

A leaf witness is `(s, n)`, 40 bytes. Put it in the clear in the leaf proof: `E` parses, the
image is the existing 8-instruction `proofwords.S` if the leaf proof is `witWords (.leaf s n)`
followed by the SNARK bytes (`decodeWit` ignores trailing words). The leaf SNARK then proves a
**public** computation, `chainEnd s n = h`, and `final` needs only its **soundness** in the
counting form (the decoding happens inside the Lean proof, non-constructively, never in the
image). No zero-knowledge is asked anywhere, so nothing is lost.

### 3.3 Cost of an honest node decoder against the budget

Estimates (R7 §2.2, §5.3; BLAKE2s in R1CS over `BF64` with bits as variables, about `2^14`
constraints per compression — 320 32-bit additions at roughly 50 constraints each, XOR and
rotation free; **estimate**):

| Quantity | Value |
|---|---|
| hash compressions to verify one UD-provable 128-bit PCS proof at `2^24`–`2^28` | 10k–14k (WHIR Table 5, UD column) |
| node circuit (two children) | `≈ 2·10^4 · 2^14 ≈ 2^28.3` R1CS constraints |
| committed word at rate `1/2` | `≈ 2^29` symbols, 4 GiB of log |
| tape `t` | `≈ 2^29`–`2^30` words; `B t ≈ 2^40.1` steps |
| quasi-linear RS decoding of one `2^29` word | `≈ 2^29 · 29^2 ≈ 2^38.7` field operations, `≈ 2^43` RV64 steps with Zbc |
| quadratic (Gao/Euclid, schoolbook) | `≈ 2^58` |

So **no honest node extractor fits `B`**, and the fit of a quasi-linear one needs
`B ≈ 2^48`. The header of `Extractor.lean` sizes `2^40` for "a quasi-linear decoder of a
`2^20`-byte proof"; the decoder's input is the committed word in the **log**, not the proof
(**F1-3**, to report). Tensor (Ligero-style) layouts with short rows make the decoding
`2^35`–`2^41` steps but fail `proofCap` (§5.2).

---

## 4. The amendment

### 4.1 Candidates

| | H1 | H2 | Trusted lines | Side effects |
|---|---|---|---|---|
| (a) `Bounded`, `step`, `final` only for `L.length < logCap`, paper theorem for `Q + qV ≤ logCap` | fixes | no | +2 | none |
| (b) potential `μ` with average rise `≤ ε`, extraction below `1` | fixes | fixes | +8, −4 | needs a `Fintype Digest` instance (Mathlib has none for core `Vector`); boolean states embed |
| (b) alone handling H1 by charging each entry | **no at `errorCap`**: a hit on one of `N` targets needs `N(1 − μ) ≤ 2^128`, saturation at `μ = 1` needs a charge `c` per target with `1/(4c) + 2^256·c·Δ ≤ 2^128` (`Δ` targets per query); at `Δ = 1` this has exactly one solution `c = 2^-129` with nothing left for the IOP, at `Δ = 2` (a 64-byte Merkle query) none. | | | would force `errorCap ≥ 2^-126` |
| (c) XOF / long-answer oracle | no | fixes | changes `OProg`, the tape, `Vb`, the liveness wrapper, the native prover | invasive; still needs (a) |
| (d) block queries (`List ByteArray` answered atomically) | no | fixes | same as (c) | |

**Recommendation: (a) + (b).** The guard removes the collision-type terms from the submitter's
accounting (`≤ 2^64·2^-256 = 2^-192` per query, charged inside `μ` as an ordinary bad event);
the potential prices multi-answer rounds exactly.

### 4.2 Proposed contract text (`Security.lean`; 18 code lines)

```lean
/-- The `2^256` digests, enumerated as `Fin 32 → Fin 256`. -/
instance : Fintype Digest := Fintype.ofEquiv (Fin 32 → Fin 256)
  ⟨fun f => Vector.ofFn fun i => UInt8.ofFin (f i), fun d i => d[i].toFin,
   fun f => by funext i; simp, fun d => by ext i hi; simp⟩

/-- The longest log the knowledge laws cover: an adversary's query budget. -/
def logCap : ℕ := 2 ^ 64

/-- **A knowledge state** with per-query error `ε`: a potential `μ` on logs, `0` on the empty
log, whose average over the `2^256` answers to a fresh query rises by at most `ε` while it is
below `1` and the log is within `logCap`, and below which every accepted proof is extracted. -/
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  μ : Log → ℝ≥0
  empty : μ [] = 0
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

/-- **Knowledge soundness** with per-query error `ε` and at most `qV` verifier queries. -/
def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV
```

`KState.Bounded` disappears (ε is a parameter). If the instance is unwelcome in the trusted
base, write the sum over `Fin 32 → Fin 256` through the same `Vector.ofFn` (Mathlib's
`Pi.fintype`), 2 lines longer and equally readable.

### 4.3 The paper theorem it implies

**Theorem.** For every adversary making `Q` oracle queries with `Q + qV ≤ logCap`, the
probability over a random `H` that it outputs `(c, π)` with `V^H c π = true` and
`E c π L ∉ R c` (`L` the final log, the verifier's queries appended) is at most `(Q + qV)·ε`.

*Proof.* `L_0 = []`, `L_{i+1} = L_i ++ [(q_i, a_i)]` for the fresh queries in order (`q_i` a
function of `L_i`, `a_i` uniform). Let `τ` be the first `i` with `μ L_i ≥ 1` and
`M_i := min 1 (μ L_{min i τ})`. Then `E[M_{i+1} | L_i] ≤ M_i + ε`: if `i ≥ τ` nothing moves;
otherwise `|L_i| < logCap`, `μ L_i < 1`, and `step` bounds the average of `μ L_{i+1}` by
`μ L_i + ε`, hence that of its cap. So `E[M_n] ≤ n·ε` with `n = Q + qV`, and by Markov
`Pr[τ ≤ n] = Pr[M_n = 1] ≤ n·ε`. On `τ > n`, `μ L_n < 1`, `|L_n| ≤ logCap`, and `runLog L_n`
answers `V`'s run (`Library/Oracle.lean`, `runLog_eq_run`), so `final` extracts. ∎

Same bound as DESIGN-v3 §4.5, now for `Q + qV ≤ 2^64`, which is what §4.5 quotes and what
`ImageComputes`'s `2^60`-word tape already presupposes (S1 review M3 restated §4.5 for
`Q + qV ≤ 2^58`; `logCap` could equally be `2^56` to sit under the tape bound).

### 4.4 The boolean form embeds (library, not contract)

Keep the S1 structure in the Library as `BoolKState` with `Bounded`, and prove

```lean
def KState.ofBool (k : BoolKState R V E) (h : k.Bounded ε) : KState R V E ε where
  μ L := if k.good L then 0 else 1
  ...
```

`step`: on a good `L` the sum counts the answers making `L ++ [(q, a)]` not good, which by the
old `step` are bad, at most `ε·2^256`; `final`: `μ L < 1 ↔ good L`. So nothing a submitter could
do before is lost, and the two multi-answer examples below show what is gained. Also
`KState.zero` (μ := 0 when every accepted proof is extractable with no query),
`KState.mono` (ε ≤ ε'), `KState.step_of_hits` (if `μ (L ++ [(q,a)]) ≤ μ L + [a ∈ T]` for a
`Finset T` then `T.card ≤ ε·2^256` discharges `step`): the lemmas a BCS proof actually uses.

### 4.5 Does the potential capture multi-answer rounds and collisions?

*Rounds.* Positions from `k` answers, `w_j := (1−δ)^{t(1 − j/k)}` for a transcript whose first
`j` position answers all miss, `0` once one hits, `w_k = 1`. The first answer raises the average
by `(1−δ)^{t/k}·w_1 = (1−δ)^t ≤ ε`; each later answer leaves it unchanged
(`(1−δ)^{t/k}·w_j = w_{j−1}`): a martingale. The example `twoLucky` (§4.6) is this with `k = 2`.

*Collisions and late preimages.* With `logCap`, "the fresh answer equals one of the `≤ 2^64`
digests the verifier could compare it with" has conditional probability `≤ 2^-192`; charge it as
a jump to `1` inside `μ`. Without `logCap` it cannot be priced at `errorCap` (§4.1, third row).

*What a BCS proof's `μ` looks like.* `μ L = 1` if `L` contains an answer collision among the
queries `V` would compare, or a hit on a dangling target; otherwise the sum over transcripts
present in `L` of the IOP's round-by-round doom value (`0`/`1` for algebraic rounds, `w_j` for
the query phase), plus `d/|Ext3|`-type terms at the algebraic challenges. That is the usual
state-restoration argument written as a potential; `ε = 2^-128` is met with
`|Ext3| = 2^192`, `t` positions with `(1−δ)^t ≤ 2^-129` and the collision terms at `2^-192`.

### 4.6 Controls: what stays, what changes, what is added

| Control / lemma | Fate |
|---|---|
| `ws_ks`, `ws_kstate_trivial`, `WitnessSending.kstate`, `ks` | `μ := fun _ => 0`; `ws_kstate_trivial` states `μ = 0`. |
| `Backdoor.kstate`, `bounded`, `certified`, `backdoor` | `μ L := if (q0, trigger) ∈ L then 1 else 0`; `step` sum is `1 ≤ ε·2^256`. The O-25 gap is unchanged (out of scope). |
| `queryThenAccept_ge_one` (S1 M2, the step law) | Unchanged in meaning: `final` on every `[(q, a)]` forces `μ = 1` there, the sum is `2^256`, so `ε ≥ 1`. Exercises `step`, `final` and the `μ < 1` hypothesis. |
| `acceptAll_kstate_iff`, `acceptAll_no_kstate_*`, `no_kstate_of_empty` | Unchanged (`μ [] = 0 < 1`, `[].length ≤ logCap`). |
| `badAll`, `bounded_ge_one`, `badAll_not_capped` | Become "a potential that is `1` off the empty log needs `ε ≥ 1`". |
| `rejectAll_ks`, `oneQuery_not_KS`, `rejectAll_not_complete` | Unchanged. |
| `KState.bounded_of_not_bad`, `Bounded.mono`, `one_le_of_bounded`, `card_digest` | Replaced by `KState.zero`, `KState.mono`, the same `1 ≤ ε` lemma, `Fintype.card Digest = 2^256`. |
| `Certificate.cap`, `error_one_no_certificate`, the rest of `Controls/Certificate.lean` | Unchanged. |
| **New** `twoLucky` | `V` asks two fixed queries and accepts iff both answers start with 12 zero bytes; relation empty. Boolean form: no state at `errorCap` (`ε ≥ 2^-96`). Potential: `μ [(q₁,a)] := 2^-96·[a lucky]`, `μ` of two lucky `:= 1`, else `0`; `ε = 2^-192`. Separates the forms. |
| **New** `merkleToy` (H1) | §1.2's toy with a 16-byte check (honest grinding `2^128`, so the true error is `2^-128`): `merkleToy_no_kstate` against `BoolKState` without the guard (a theorem over an abstract log of `2^136` entries, no computation); `merkleToy_kstate` at `ε = 2^-128` under the amended contract. Shows `logCap` is load-bearing. |
| Design text | §4.2 (reading), §4.5 (`Q + qV ≤ logCap`), §6.6 caps row; AGENTS.md §4; BASELINE-TASK §5. |

Existing knowledge content is untouched: `ImageComputes` and the named `E` stay the knowledge
clause (A13), `Complete` is untouched, `Vb` is untouched.

### 4.7 Interaction with O-25

Orthogonal. The polymorphic-digest fix changes `V`'s type and the query grammar, not the laws;
a potential over logs of structured queries is the same definition.

---

## 5. Honest designs under the amended contract, ranked

### 5.1 Fixed points of the problem

* Field: `BF64`/`Ext3` (allowlisted, computable, field instances proved; `|Ext3| = 2^192`
  gives `d/2^192` per algebraic challenge). A prime field would need a computable extension with
  an irreducibility proof in the entry. In-circuit `BF64` arithmetic is one constraint per
  multiplication, which is what makes the verifier's algebra cheap to arithmetise.
* Oracle: BLAKE2s only (V3-6). Every Merkle level in the recursion circuit is a BLAKE2s
  compression gadget, about `2^14` R1CS constraints (estimate §3.3). This, not the sumcheck
  algebra, is the whole cost of recursion.
* Provable regimes only (no conjecture, no named hypothesis under V3-5 and the axiom rule):
  unique decoding, at most one bit per query, `≥ 128` positions at `ε = 2^-128`; Johnson-regime
  theorems (BCIKS20, BCHKS25) are out of reach for a baseline proof.
* `Complete` is perfect over every `H`: no grinding (O-23), and no challenge-dependent
  degenerate case may make the honest prover fail (an out-of-domain sample that lands in the
  domain, a zero challenge where something is inverted). The design must handle every challenge
  value or accept the degenerate case in `V` and charge it to `ε`.
* `proofCap = 1 MiB` is enforced by `Vb`, not by `Complete`: an entry with larger proofs
  **certifies** and is unranked (A18), exactly like the witness-sending baseline.
* `T_V = 2 s` with compiled Lean. O-9's `K.mul ≈ 27 µs` is for v2's field; CompPoly `BF64`
  compiled is unmeasured. A WHIR-class verifier does `10^4`–`10^5` extension multiplications
  (R7 §5.3): `0.3`–`3 s` at `27 µs`, negligible at `1 µs`. **Measure first.**

### 5.2 Sizing (estimates; R7 §2.2 Table 5 UD column, R5 leanVM, §3.3)

| Design | Proof at `2^24` / `2^28`, 128-bit UD | Compressions per verification | Fits `proofCap` for the node circuit (`≈ 2^28.3`)? | Lean proof content |
|---|---|---|---|---|
| Spartan + **WHIR**-class | 621 KiB / 770 KiB | 10k / 14k | yes, barely | out-of-domain samples, shift queries, MCA in the UD regime, folding: the largest IOP proof here |
| Spartan + **FRI** arity 8, rate 1/16 | `≈ 1 MiB` / `> 1 MiB` | `≈ 128·8·log` | no at node size | DEEP-free FRI folding in UDR (BCIKS20 correlated agreement for lines, UD case), query phase |
| Spartan + **Basefold** (arity 2, sumcheck-interleaved) | 7.95 MiB at `2^24` (ZCF24, λ=100) | similar | no | the smallest: one folding lemma in UDR; ArkLib #383 has it over binary fields (not allowlisted; copyable only if its dependency closure is Mathlib/CompPoly) |
| Spartan + **Ligero/Brakedown** tensor | `≥ 25 MiB` at `2^27` (`t · √N · 8 B`) | `t · log` plus `t` columns of `√N` | **no at any useful size** (`≤ 2^16` constraints per MiB) | the simplest (interleaved UDR lemma, row decoding) |
| GKR-based (leanVM-style) | — | — | — | grand products and lookups add GKR soundness; R1CS needs none. Not for a baseline. |

**F1-4.** Under `proofCap`, R1CS, UD-provable 128 bits and BLAKE2s Merkle hashing, recursion
closes only with WHIR-class proof sizes, and only just; with a plonkish/AIR arithmetisation of
BLAKE2s (`2^10`–`2^11` cells per compression) the node circuit is `≈ 2^24` and every PCS in the
table but Ligero fits. The ranked leaf (`n = 2^14` compressions `≈ 2^28` R1CS constraints) needs
the same room. The witness and codeword of one such proof are 2–4 GiB; 96 GB holds a few in
flight.

### 5.3 Ranking for the first baseline (proof effort, then build time, then native simplicity)

1. **R1: leaf SNARK with the witness in the clear, witness-sending nodes.** Spartan R1CS
   sumchecks over `BF64`/`Ext3`, Basefold-class PCS, BCS over the oracle, FS from the log,
   `μ` as in §4.5. `E` and `img` are the existing ones (parsing). Certifiable under the
   amendment with no decoder, no node circuit, no fixed point. Runs the smoke tree (leaf
   `n = 16`: `2^18` constraints, proof `≈ 250 KiB`); at the ranked size the leaf is `2^28`
   constraints and the Basefold proof exceeds `proofCap`: unranked by `proofCap` and, through the
   witness-sending root, by `T_V`. This is the honest-pipeline milestone: every Lean component of
   §5.4 except the circuit DSL and the decoder.
2. **R2: recursive, semi-uniform circuits, WHIR- or FRI-class PCS.** Adds the circuit DSL with
   two interpretations (`toProg : Circ → OProg`, `toR1CS : Circ → R1CS`) and the correctness
   theorem `sat (toR1CS c) z → (toProg c).run blake2sOracle = result z`, a BLAKE2s gadget
   (O-15(1)), the verifier's own gadgets (sumcheck rounds in `Ext3`, Merkle path logic, FS
   absorption), the node extractor (decoder: §6), and `P` in Lean for the liveness check at
   `r = 1` (make the node level-aware for leaf children: recompute the 16-step chain, so the
   liveness node has `2^19` constraints and the emulator sees a small tape). Blocked on the
   extraction rule.
3. **R3: ranked.** R2 plus one of: AIR-style BLAKE2s, a hash menu entry (O-14), `proofCap`
   raised, a named proximity-gap hypothesis (not under V3-5). All user decisions.

Succinct matrix evaluation without SPARK: both circuits are a repetition of one block
(a compression, `≈ 3·2^14` nonzeros) chained by a fixed wiring plus a small non-uniform part
(`≤ 2^18` nonzeros). `Ã(r_x, r_y)` for `I ⊗ A_block` plus a shift wiring has a closed form in
`O(nnz(A_block) + log N)` `Ext3` operations; the non-uniform part is summed directly. So `V`
evaluates `Ã, B̃, C̃` in `≈ 2^18` operations and no preprocessing commitment is needed.

### 5.4 Which parts are proved where

| Part | Where | Depends on |
|---|---|---|
| `KState` potential, `logCap`, `Fintype Digest` | contract (amendment) | core PR, pin move |
| `KState.ofBool`, `zero`, `mono`, `step_of_hits`, log lookup lemmas, Fintype card | Library (S4) | amendment |
| sumcheck round-by-round in `Ext3` (Mathlib `MvPolynomial.schwartz_zippel_*` exists) | entry | — |
| R1CS → two sumchecks (Spartan), `eq`/MLE algebra, structured `Ã` evaluation | entry | — |
| PCS: Basefold-class folding in UDR; or FRI/WHIR | entry; or copied from ArkLib #383 if its closure permits; or allowlist extension (organiser) | O-22 for the `BF64` basis |
| Merkle extraction from the log, FS chaining, dangling/collision charges | entry (reusable: Library later) | amendment |
| BLAKE2s gadget and verifier gadgets, DSL correctness | entry; gadget kit organiser-side (O-15(1)) | R2 |
| `E` spec and image: parsing (R1); decoder (R2) | entry; decoder per §6 | rule decision |
| `P` and `Complete` for every `H` | entry | no degenerate challenge cases |

---

## 6. Extraction: the cheapest honest strategy and the rule to change

### 6.1 Without a rule change

Leaf: parse (§3.2). Node: find the committed tree in the log (one pass per tree level,
matching answers to the targets discovered so far, `≈ 100` steps per word over the levels, within
`2^8 t`), then decode. The cheapest *verified* decoder is a unique RS decoder for one row of a
tensor layout (Gao/Euclid, schoolbook, `O(n²)` per row), but a tensor layout fails `proofCap`
(§5.2); for a WHIR/FRI/Basefold word of `2^29` symbols only a quasi-linear decoder (fast Euclid
over the additive NTT) fits any sane budget, and it exceeds the current one by `≈ 2^3` (§3.3).
A verified quasi-linear decoder in RV64 assembly, with `Library/Machine.lean`'s symbolic
execution as the only tooling, is not a baseline component; it is a project.

### 6.2 Rule options

| Option | Trust cost | Who pays | Verdict |
|---|---|---|---|
| **Raise `B`** to `2^48 + 2^16·t` | none (`2^48` still excludes `2^128` enumeration; no 64-bit secret exists in `Rel`) | one constant, O-21 is open anyway | do it regardless |
| Organiser decoder image (O-15(2)) with a linking convention and composition lemmas | none (kernel-checked) | organiser: the verified decoder plus a calling convention in `Library/Machine.lean` | right long-term answer; large |
| Lean-level cost model for `E`: a first-order extractor language (log/word/field primitives, bounded loops) with a step-counting interpreter in the contract (`≈ 60–100` lines) | the interpreter's semantics and that each primitive is `O(1)` machine work; must exclude `Nat`-bignum and list-length-in-one-step gaps (A3 C2) | organiser once; submitters then prove about structured programs, not assembly | viable; moderate trusted growth; the vendored RV64 is already a machine, the pain is proving loops in assembly, which a Hoare-style library would also fix |
| Measured extractor time (like `T_V`) | knowledge content drops to soundness plus a liveness test on honest logs (A13, M3) | — | reject |
| `E` noncomputable, `ImageComputes` dropped | same as above | — | reject |

**Recommendation.** Raise `B` now. For the first baseline take R1 (no decoder). Put the choice
between the organiser decoder and the cost model to the user, with the fact that the first
*recursive* certification is blocked on it either way; while waiting, the R2 Lean work that does
not depend on the decoder (DSL, gadgets, circuit correctness) can proceed with `E` specified in
Lean as the decoder and `ImageComputes` left open.

---

## 7. Review of the task prompt

### 7.1 Ambiguous, missing, infeasible

| Item | Assessment |
|---|---|
| "passes the security definitions and checks" | **Infeasible as written** for any succinct hash-based `V` (§1, §2). The amendment is a precondition; the prompt treats rule tweaks as second priority and conditional on measured difficulty. |
| "inspired by leanVM/leanerVM" | leanVM's parameters rest on Poseidon2 Merkle hashing, 17-bit grinding and a Johnson-regime MCA statement consumed as a hypothesis (R5 §3.2); none of the three is available here (BLAKE2s-only oracle, perfect completeness, V3-5). The inspiration transfers at the level of architecture (sumchecks, WHIR, straight-line extraction), not of numbers. |
| "R1CS arithmetisation" | Right for Lean (Spartan is sumcheck-only, Schwartz–Zippel is in Mathlib), wrong for closing recursion under `proofCap` with BLAKE2s (`2^14` constraints per compression, F1-4). |
| "BCS, Merkle, FS" | Yes, but straight-line extraction from the log reaches only the committed word, never a child proof (§3.1); the prompt's mental model of `E` is probably the lookup one, which is unprovable. |
| "executable verifier/prover" | `V` compiled under `T_V` depends on compiled `BF64` speed, unmeasured (O-9). `P` in Lean at node size is hours; acceptable only because liveness runs at `r = 1, n = 16` with a level-aware node. |
| "decent baseline" | Undefined. Proposed meaning: certified, proves the smoke tree, honest pipeline end to end, unranked at `r = 8` by `proofCap`/`T_V` like the witness-sending baseline. Ranked is R3 and needs user decisions. |
| "measure build time / proof effort" | Build time of the Lean side is dominated by elaboration of structured definitions, not `decide`; nothing may unroll `2^14` compressions at elaboration. Proof effort is not a measurement (CLAUDE.md "no estimates"); report it as the dependency graph of §5.4. |
| Missing: the field, the PCS, the ArkLib question | Decide `BF64`/`Ext3`; Basefold-class for R1; ArkLib is not allowlisted, so either re-prove from Mathlib, copy a Mathlib-only closure, or ask the organiser to extend the allowlist (S4). |
| Missing: perfect completeness vs degenerate challenges | Design `V` to accept every challenge value for the honest prover (§5.1). |
| Missing: the extractor rule for nodes | User decision (§6.2). |
| "avoid CGH constructions" | Also avoid the near-CGH: `V` must not compute BLAKE2s on an oracle input and compare with an oracle answer. The node circuit computing BLAKE2s on *child* oracle inputs is the sanctioned heuristic (§5.4), not CGH. |
| "gaming ... fair game, report as issues" | The issues below. Nothing found that games `KS` itself beyond O-25; the gaps are the other way (unsatisfiability). |

### 7.2 Decisions to take autonomously (user unreachable)

1. Draft the amendment (§4.2) as a core pull request with the control changes of §4.6 and the
   design/AGENTS text; move the pin in its own commit after merge. Do not start Lean work on
   `KS` against the current form.
2. Raise `B` to `2^48 + 2^16·t` in the same PR (O-21).
3. Benchmark compiled CompPoly `BF64`/`Ext3` multiplication and compiled `blake2s256` before
   choosing anything that touches `T_V`; log under `logs/`.
4. First baseline = R1 (§5.3): leaf witness in the clear, witness-sending nodes, existing
   image. Field `BF64`/`Ext3`. PCS Basefold-class, rate `1/2`, UDR, `≥ 129` positions, arity 2;
   proof size is not a goal for R1.
5. Spartan sumchecks with structured matrices; no SPARK, no GKR, no lookups.
6. Perfect completeness: no out-of-domain tricks, no inversions of challenges.
7. Decide the ArkLib question by inspecting #383's import closure; default to re-proving the
   UDR folding lemma from Mathlib.
8. Start the R2 components that do not depend on the extraction rule (DSL, BLAKE2s gadget,
   circuit correctness) only after R1 certifies.
9. Park: the node extraction rule, O-14, `proofCap`, O-23, any named hypothesis. Write them up
   for the user as the three ways R2 becomes R3.
10. Keep the witness-sending baseline as the positive control of the amended contract (its
    `kstate` becomes `μ := 0`).

### 7.3 Issues to file (core repository)

1. `KS` at `errorCap` is unsatisfiable for every Merkle-committing `V` (§1; F1-1).
2. The boolean per-answer form cannot price a multi-answer query phase (§2; F1-2).
3. `Rel`'s concrete `Vb` versus the oracle log: child proofs are not log-extractable; node
   extraction is decoding (§3.1).
4. `extractorBudget` is sized for the proof, not the committed word in the log; `2^40` excludes
   every honest node decoder (§3.3; F1-3).
5. `proofCap = 1 MiB` with UD-provable 128 bits and BLAKE2s Merkle hashing leaves only
   WHIR-class sizes for recursion, and only with a non-R1CS BLAKE2s (§5.2; F1-4). Interacts with
   O-14 and O-18.
6. `Complete` perfect over every `H` forbids grinding and every challenge-dependent exceptional
   case (O-23 is on the critical path of any PCS with out-of-domain samples).
7. No `Fintype Digest` in Mathlib at the pin; the amendment supplies one (or sums over
   `Fin 32 → Fin 256`).
8. ArkLib is not allowlisted; the UDR folding lemma must be re-proved or the allowlist extended
   (S4).
9. `T_V` depends on compiled `BF64` speed, unmeasured (O-9 reframed).
