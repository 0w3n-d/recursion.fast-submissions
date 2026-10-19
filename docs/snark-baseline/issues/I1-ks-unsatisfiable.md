KS at errorCap is unsatisfiable for every Merkle/BCS verifier: `Bounded` over unbounded logs (collisions, late preimages) and per-answer charging (multi-answer query phases)

## Summary

The counting form of knowledge soundness (`KState` + `KState.Bounded`, `Contract/Security.lean` at
`15e4ae5`) cannot be met at `errorCap = 2^-128` by any verifier that checks a Merkle opening against
an oracle-derived root, nor by any verifier whose query phase draws its positions from more than one
32-byte oracle answer. Every hash-based SNARK (FRI, STIR, WHIR, Basefold, Ligero, Brakedown, under
BCS) has both features. Two kernel-checked counterexamples and one paper argument show it. Today
the only certifiable entries are the witness-sending argument and the O-25 backdoor (#4). Proposed
fix: a potential `μ` on logs in place of the boolean `good`/`bad` pair, plus a log-length guard
`logCap`.

## The problem

For readers new to the contract. A verifier `V` is a program that asks an oracle
`ByteArray → Digest` (32-byte answers). A *query log* `L` lists (query, answer) pairs. The
submitter proves knowledge soundness (KS) by exhibiting `good : Log → Prop` and
`bad : Log → ByteArray → Digest → Prop` (`Security.lean:46-58`): the empty log is good; a good
log stays good after a fresh query unless its answer is bad; on a good log every accepted proof
is extracted. Then (`Security.lean:61-63`):

```lean
def KState.Bounded (k : KState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest
```

and `Certificate.cap` (`Certificate.lean:69`) requires `S.ε ≤ errorCap = 2^-128`
(`Security.lean:41`). At the cap, at most `2^128` of the `2^256` answers to any fresh query may be
bad, **for every log `L` of any length**. The paper theorem is the union bound `(Q + qV)·ε`
(DESIGN-v3 §4.5).

**(a) Unbounded logs versus collisions and late preimages.** The ROM analysis of a Merkle
commitment charges each fresh query with two events: its answer collides with an earlier answer,
or it equals a value already used inside an earlier query (a late preimage of a dangling root).
Each event has about `|L|` bad answers. `Bounded` quantifies over logs with more than `2^128`
entries, where these sets exceed the cap. Then `bad` must drop some of them, `step` forces `good`
onto a log that contains a collision or a hit, and `final` must extract from a log where the
adversary can open a commitment two ways. The `(Q + qV)·ε` theorem is vacuous for `Q ≥ 2^128`
anyway, so the definition asks for a bound only in a regime where the theorem says nothing.

**(b) Per-answer charging versus multi-answer query phases.** Under unique decoding a provable
query phase gains at most one bit per position (`(1−δ)^t ≤ 2^-128` needs `t ≥ 128` positions), so
it needs `t·log₂ n ≫ 256` bits of position randomness. The positions come from `k ≥ 2` answers
`H(T‖1), …, H(T‖k)`. The boolean form charges the worst conditional probability per answer. At the
last answer, given lucky earlier answers, the accepting fraction is `(1−δ)^{t/k} ≥ 2^{-128/k}`,
far above `2^-128`. The real ROM gives no such credit: retrying `H(T‖k)` means changing `T`,
which redraws all `k` answers.

## Why it matters

- An honest succinct entry, the purpose of the competition, cannot be certified. The S2b honest
  baseline in the submissions repository is blocked on this issue.
- The certifiable entries today are those the competition means to exclude: non-succinct ones
  (see the `T_V` issue) and oracle-recognising ones (O-25, #4).
- No choice of `good`/`bad` escapes (F1 §1.3, §2.2). Semantic `good`, length-dependent `good`,
  512-bit roots, extra local checks in `V`, larger `qV` and a tighter `errorCap` all fail.

## Evidence

**Kernel-checked** (`logs/adv-probes/CountingForm.lean` in the submissions repository; logs are
local, so the statements are quoted here; compiled against the pin with `lake env lean`). Verifiers:
`Vcol` accepts a proof naming two distinct queries with equal answers (ROM error
`≤ (Q+2)²/2^257`); `Vprod t k` asks `k` fixed queries and accepts iff every answer satisfies `t`
(ROM error `(|T|/2^256)^k`). `c₀` is any statement with no witness.

```lean
-- (a) In context: (hR : ∀ w, ¬ R c₀ w) (ks : KState R Vcol E)
theorem collision_no_bound (K : ℕ) (hK : ∀ L q, Nat.card {a // ks.bad L q a} ≤ K)
    (h2 : 2 * K < 2 ^ 256) : False
theorem collision_not_capped : ¬ ks.Bounded errorCap
-- (b)
theorem eps_ge_density (t : Digest → Bool) (k : ℕ) {R} (c₀ : Digest) (hR : ∀ w, ¬ R c₀ w)
    {E} (ks : KState R (Vprod t k) E) {ε : ℝ≥0} (hb : ks.Bounded ε) :
    (Nat.card {a // t a = true} : ℝ≥0) ≤ ε * Nat.card Digest
theorem product16_not_capped {R} (c₀ : Digest) (hR : ∀ w, ¬ R c₀ w) {E}
    (ks : KState R (Vprod t0 16) E) : ¬ ks.Bounded errorCap   -- t0 a := a[0] = 0; ROM error 2^-128
-- positive control for the length guard: with good := short ∧ collision-free
theorem colState_bounded : BoundedBelow colState errorCap (2 ^ 128)
```

`#print axioms` for `product16_not_capped`, `collision_not_capped` and `colState_bounded`:
`[propext, Classical.choice, Quot.sound]` each (6.4 s). `eps_ge_density` holds **whatever `k`**:
spreading the event over more answers never helps under the boolean form.

**Paper argument for a real Merkle-plus-Fiat–Shamir verifier** (F1 §1.2). Take a true statement
and a committed word just beyond the extractor's decoding radius. Append `2^128 + 1` dangling
transcripts over distinct, never-opened roots `rᵢ`, each with position answers chosen accepting
(at least `2^192` accepting answers per position, at most `2^128` bad). Then append the Merkle tree
of the word up to the top query. Every `rᵢ` must be bad for the top query, since otherwise `final`
must extract from an accepting, unextractable transcript. That is `2^128 + 1 > errorCap·2^256`
bad answers. A toy version with a one-byte leaf check is proposed as the control `merkleToy`.

## Proposed fix

(F1 §4.2, `Security.lean`, about 18 code lines; `Bounded` disappears and `ε` becomes a
parameter. A paper draft: not yet compiled.) A potential replaces `good`/`bad`. On average it
rises by at most `ε` per fresh answer. It extracts below `1`. The laws hold within `logCap`.

```lean
instance : Fintype Digest := Fintype.ofEquiv (Fin 32 → Fin 256) ⟨…⟩   -- or sum over Fin 32 → Fin 256
def logCap : ℕ := 2 ^ 64
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

- **Paper theorem** (F1 §4.3): `(Q + qV)·ε` for `Q + qV ≤ logCap`. Proof: the stopped process
  `min 1 (μ L_i)` is a supermartingale with drift `ε`, then Markov. The bound is the same as
  §4.5, now on the domain §4.5 actually quotes.
- **(a) is fixed by `logCap`**: a collision or a late hit has conditional probability
  `≤ 2^64·2^-256 = 2^-192` and is charged as a jump of `μ` to `1`. `logCap` alone is ADV1's
  one-line fix of (a); `colState_bounded` above is its positive control.
- **(b) is fixed by `μ`**: a round of `k` answers gets weights `w_j = (1−δ)^{t(1−j/k)}`, and the
  first answer pays `(1−δ)^t`. The later answers form a martingale. This is the state-restoration
  argument written as a potential.
- **Nothing is lost**: the boolean form embeds as the library constructor
  `KState.ofBool` (`μ := if good then 0 else 1`). Every S1 control ports (F1 §4.6). Two new
  controls separate the forms: `twoLucky` and `merkleToy`.
- **Cost**: about 18 trusted lines (+8 and −4 in the definitions, plus the instance), and design
  text in §4.2, §4.5 and §6.6, `AGENTS.md` §4 and `BASELINE-TASK` §5. `logCap` could be `2^56` so
  that it stays below `ImageComputes`'s `2^60`-word tape (see ADV-m7 in the hygiene issue).
- **Rejected alternative for (b)**: an extendable-output oracle constructor
  (`queryN (q) (ℓ) (k : (Fin ℓ → Digest) → OProg α)`, ADV-M3). It changes `OProg`, the tape, `Vb`
  and the native prover, and still needs `logCap` for (a).
- **Interaction with O-25** (#4): orthogonal to the definitions. A potential can price
  *spread recognition* exactly as it prices a spread challenge (see the comment on #4).

A draft core branch, `v3/ks-potential`, is being prepared in a scratch clone of the core. It
carries this text, the ported controls and the new controls, and is offered as a draft pull
request. Nothing has been pushed yet.

## Cross-references

F1-1, F1-2 (F1 §1, §2, §4); ADV-M2, ADV-M3; DESIGN-v3 §4.2, §4.5, §6.6; O-21 (error caps); O-25
(#4); roadmap #1 (S2 baseline).
