# F2. Closing the random-oracle uninstantiability gap (O-25, core issue #4)

Status: design memo, 2026-10-20. Ideation and design; nothing here is committed, built, or
kernel-checked unless it cites a probe with a log. Finding ids are `F2-n`; cross-references keep
their ids (O-25, ADV-M5, ADV-M6, V3-S1-M1, V3-KS-A*, V3-n). Read against the core at the pin
`.contract` = `15e4ae5`, the amended KS branch `rf-core-ks` `v3/ks-potential` head `05fde28`, the
honest entry `submissions/spartan-chain/`, issue #4 (`/home/devops/.claude/jobs/e2d4aee0/tmp/issue-4.json`),
`docs/snark-baseline/notes/{ADV1-rules-review.md,F1-ks-feasibility.md}`, `docs/snark-baseline/REPORT.md`,
`docs/design/DESIGN-v3.md` §3.1/§5/§6.6-§6.7/§12, and the user's literature list
(`/tmp/cgh98_snark_followups.md`).

An independent adversarial reviewer will try to break the recommended scheme. The threat model and
the exact rule/type/statement are stated as precisely as a paper memo can; §10 states what is
proved, assumed, and residual.

---

## 0. TL;DR and recommendation

O-25 is the Canetti–Goldreich–Halevi (CGH98) uninstantiability of the ROM, specialised to this
contract: the certificate quantifies over **all** oracle functions `H`, the harness deploys
**one** (`blake2sOracle`), and any single function is a `2^-256`-measure event the theorem cannot
see. A `V` that holds a value correlated with the deployment function (BLAKE2s), obtained other
than through a query, and compares it with a value that did come through a query, accepts a magic
proof in deployment while remaining certified in the ROM (`Controls/Backdoor.lean`, kernel-checked).

**I recommend Candidate E of §9: a typed abstract-digest interface, a small trusted wrapper, a
semantic rule in `AGENTS.md`, and mandatory intake review with a public challenge period — layered,
not relying on any single mechanism.** Concretely:

1. **Type.** `V : ∀ (D : Type) [DecidableEq D], DigestOps D → D → Tape D → OProg D Bool`, where
   oracle answers, statement, and the proof's digest slots are opaque `D`; `V` compares `D`-values
   only by `DecidableEq`; everything the contract needs `V` to compute on digests (relation hashes,
   and a *restricted challenge interface*) is supplied as the record `DigestOps D` of
   contract-owned, `D`-valued operations. Queries are structured `List (ByteArray ⊕ D)` serialised
   by the wrapper. The gate checks the type literally and that `Vb` is computable.
2. **Challenge interface (the hard part).** Fiat–Shamir challenges are produced by a
   contract-owned `squeezeF : D → F` returning values of an abstract field `F` on which `V` has a
   *ring/poly-evaluation interface only* (add, mul, `const`, and "evaluate a prover-supplied
   polynomial and compare two `F`-values for equality") — never a projection `F → bits`, never
   `DecidableEq`-against-a-`V`-chosen-constant. Grinding is expressed by a contract-owned
   `leadingZeros : D → ℕ` the wrapper computes and compares against a *proof/statement-supplied*
   bound, not a `V`-internal constant (§11).
3. **Rule + review.** A semantic rule ("no branch of `V` may accept because a value it did not
   obtain from the oracle, the `DigestOps`/challenge interface, or the proof agrees with a value
   that did") in `AGENTS.md`, a `NOTES.md` disclosure of every answer comparison, mandatory S7
   intake review, and a public challenge period before a record stands.

**What this buys, stated honestly (§10).** The *known* CGH mechanism — `V` evaluates the
instantiation and compares — is **excluded by construction** for the commitment/Merkle part and for
equality-only use of answers: such a comparison does not type-check (meta-theorem: parametricity /
"free theorems", with the Lean-4 caveats of §5). It is **not** a proof that "no verifier in the
allowed class is ROM-secure but BLAKE2s-insecure": that is false in general (Candidate A cannot and
E cannot close it), because the challenge interface necessarily lets `V` compute *some* function of
answer values, and recent results (KRS25, Fenzi26, GK03, BBHMR19) show deployed Fiat–Shamir SNARKs
can be made unsound for every concrete hash. The residual risk is therefore **exactly the
residual risk of any deployed Fiat–Shamir hash-based SNARK**, no better and no worse — which is the
strongest honest statement the ROM can support, and is the user's stated acceptable floor ("gaming
reported, CGH avoided at all costs"). The typing removes the *free, unreviewable, in-source*
backdoor and forces any residual attack to live inside the challenge algebra, where it (a) costs
the attacker a real FS-style unsoundness construction and (b) is visible to review.

**My confidence.** A workaround of the general kind "ROM-secure, BLAKE2s-insecure `V` inside the
allowed class" almost certainly exists in principle (it is the FS-uninstantiability literature); I
am ~80% that no *free, review-invisible, kernel-only* backdoor survives Candidate E with the
challenge interface of §4/§9, and ~50% that a *determined* adversary could still smuggle a
recognising check through the polynomial-evaluation channel in a form review would plausibly miss
(§14, the most dangerous attack). I therefore recommend shipping E **and** keeping review/challenge
period load-bearing, and I flag the challenge interface as the point the reviewer should hammer.

## 1. The problem, restated precisely, and the threat model

### 1.1 The contract objects (at the pin and the amended branch)

- `OProg α`: `ret a | query (q : ByteArray) (k : Digest → OProg α)`. `run H` evaluates against a
  total oracle function; `runLog L` against a log; `queries H` lists what a run asks
  (`Contract/Oracle.lean`).
- `Digest := Vector UInt8 32`; `blake2sOracle q := blake2sDigest (tagRO :: q.data.toList)`,
  `tagRO = 0x52` (`Contract/Relation.lean`, `Contract/Certificate.lean`).
- `Submission.Vb S c π := if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false`.
- `KS R V E ε qV` (amended, `v3/ks-potential`): a `KState` with a potential `μ : Log → ℝ≥0`,
  `empty`, a `step` law (average over the `2^256` answers of a fresh query raises `μ` by ≤ `ε`,
  for `L.length < logCap = 2^96`), and `final` (below potential 1 and within `logCap`, every
  accepted proof is extractable by the named `E`). `errorCap = 2^-128`.
- `Complete R P V := ∀ H c w, R c w → (V c ((P c w).run H)).run H = true` — perfect, over **every**
  `H`. (To be weakened to a δ-error form over a *uniformly random* `H`; §11.)
- `Certificate S`: `KS (Rel S.Vb) S.V S.E S.ε S.qV`, `Complete`, `ImageComputes`, and the caps.

### 1.2 The backdoor, as the kernel sees it

`Controls/Backdoor.lean` builds `S` = witness-sending with one change: `V c π` queries `q0 = ""`,
computes `trigger := blake2sOracle q0` **itself** (BLAKE2s is public), and accepts the 32-byte
`magic c := ⟨c.toArray⟩` when the answer equals `trigger`. The `KState` is
`good L := ∀ e ∈ L, e.1 = q0 → e.2 ≠ trigger`, `bad L q a := q = q0 ∧ a = trigger`; the one bad
answer is `≤ errorCap · 2^256`, so `KS` holds; the honest branch is untouched, so `Complete` holds.
`theorem backdoor : Certificate S ∧ ∀ c, S.Vb c (magic c) = true`. ADV-M5 strengthened this: the
trigger can be a precompiled **literal** (`LiteralTrigger.lean`, kernel-checked), whose constant
closure contains no `blake2sOracle`/`tagRO`/`Submission.Vb`, and whose remaining `blake2s256`/
`compress` footprint is **identical** to the honest `WitnessSending.V`'s. A syntactic/closure gate
cannot separate them.

### 1.3 Threat model (what the reviewer should assume the adversary can do)

The adversary submits an entire `Submission` (`V, P, E, img, ε, qV, fuel`). It wins board T if the
harness prints `HARNESS: ACCEPT` and its deployed `Vb` accepts a proof it produced without the
knowledge the relation demands — in particular, a magic proof — while its certificate is a genuine
kernel-checked `Certificate S` using only `propext, Classical.choice, Quot.sound`, no `sorry`,
no `native_decide`, no code-changing attributes, imports only from the allowlist (plus CompPoly
`BF64`/`Ext3`). The adversary:

- knows BLAKE2s completely and may hardcode any function of it as a Lean/`ByteArray`/`Digest`
  constant, or embed a RISC-V image of it and run it through `Machine.run`, or reach the
  in-closure compression (ADV-M5 forms 1–2);
- may structure queries, split recognition across many answers/bits (the ROM charges the product;
  under the potential `μ` this is priced exactly like a spread challenge, V3-KS, so counting does
  not catch it — F1 §1, ADV-M3);
- controls `good/bad`/`μ` freely (they are the submitter's own witnesses);
- after the completeness change, may use δ-slack to make honest proofs *fail* under one specific
  oracle (the liveness mirror, §11);
- will try to evade any purely-syntactic gate and any human review by disguising the comparison as
  ordinary verifier arithmetic.

The defender controls: the Lean **type** `V` must inhabit (gate-checked), a small **trusted
wrapper** (≈30 lines) that instantiates it, the **rulebook** text, the **review** process, and the
harness's concrete **smoke check** on BLAKE2s. The defender cannot see inside the quantifier
`∀ H` with any Lean theorem.

## 2. What "recognition" is, and the asymmetry the ROM cannot see

The ROM theorem catches everything an adversary does **through the oracle**: a prover that predicts
an answer must query it first, the query lands in the log, and `final` demands a witness. The only
asymmetry the theorem cannot price is a value inside `V` that is **correlated with the deployment
function but did not arrive through a query**. Call a position of `V` a *recognition site* if `V`'s
acceptance can depend on the event "`x = f(a₁,…,a_k)`" where the `aᵢ` are oracle answers (came
through queries) and `x` or `f` encodes information about the deployed instantiation that `V` did
not obtain through queries. In the ROM this event has measure `≈ 2^{-(bits compared)}`, charged to
`bad`/`μ`; in deployment it is forced true.

Two consequences structure the whole design space:

- **(R1) If the only operation `V` has on answers is equality between answers (and against
  proof/statement values that are themselves `D`), there is no recognition site.** Any `V`-internal
  constant it could compare against would have to be a `Digest` (`D`), which `V` cannot name under
  the parametric type. This is the core of Candidate A, and it is *sound* for commitment/Merkle
  verifiers (roots compared with roots).
- **(R2) The moment `V` can compute any function `answer → observable` whose output `V` can also
  produce *independently of the oracle*, a recognition site reopens.** Fiat–Shamir needs exactly
  this: a challenge is `some function of an answer`, and `V` must use it in arithmetic. If `V` can
  see `g` bits of challenge, it can compare them with `g` bits of a locally recomputed BLAKE2s and
  recognise at error `2^-g` (ADV-M5.4). Grinding is the same shape: "answer has `g` leading zero
  bits" is a comparison of answer bits with a constant (§11).

The design problem is therefore **not** "forbid all answer-dependence" (that kills FS and kills
every SNARK); it is "give `V` exactly the answer-dependence an honest FS/grinding verifier needs,
in a form whose outputs `V` cannot reproduce oracle-independently *and compare*." Whether such a
form exists, and how tight it can be made, is the subject of §4 and §9, and the honest answer is:
**partly, for the algebraic part; not completely, because the challenge channel is inherently a
narrow recognition site** — which is why the recommendation is layered.

## 3. Candidate A: parametric-`V` in the digest type (#4's proposal), in depth

### 3.1 The type and the wrapper

```lean
-- Contract-side, trusted (~30 lines):
inductive Tape (D : Type) | …            -- proof grammar: byte segments ⊕ digest slots
abbrev QElem (D) := ByteArray ⊕ D
structure DigestOps (D : Type) where     -- D-valued ops the wrapper fills with BLAKE2s at D:=Digest
  chainStep : D → D
  leafStmt  : D → ℕ → D
  nodeStmt  : D → D → D
-- the submission:
V : ∀ (D : Type) [DecidableEq D], DigestOps D → D → Tape D → OProg D Bool
-- OProg is now indexed by D: query (q : List (ByteArray ⊕ D)) (k : D → OProg D α)
-- wrapper instantiates D := Digest, serialises each query to bytes, hashes with blake2sOracle,
-- parses the submitted bytes into Tape Digest, fills DigestOps with the concrete functions.
```

The claim (#4 §2): a term polymorphic in `D` with only `DecidableEq D` and the fixed
`DigestOps`/query plumbing can depend on the `D`-values it handles only through their **equality
pattern** — which answers equal which answers, the statement, or a slot — because there is no other
closed operation of type `D → …` available to it. The backdoor needs `decide (a = trigger)` with
`trigger : Digest` a `V`-computed constant; at abstract `D` that constant has type `Digest`, not
`D`, so the comparison does not type-check. The exclusion is at the definition: nothing to review,
nothing to obfuscate around, for this part.

### 3.2 Why A is genuinely strong for the Merkle/commitment half

A Merkle verifier (spartan-chain `SpartanChainMerkle`) only ever: hashes columns/nodes (now via the
query interface, answers are `D`), truncates to 31-byte labels (— see §3.3, a problem), and
compares labels for equality (`trunc e₁.2 = trunc e₂.2`, `labelsIn`, root checks). Equality of
answers is all the binding argument needs; `open_binding_prefix` reads columns off the log by
`find?` on label equality. So the commitment half maps cleanly onto R1 of §2 and is backdoor-free
by construction. **This is the part of #4's proposal that works and should be kept.**

### 3.3 Where A already strains, even before Fiat–Shamir

- **Truncation to labels.** spartan-chain uses 31-byte labels `trunc a`, not full 32-byte answers,
  to make node queries 63 bytes. `trunc : Digest → Label` is a projection of answer **bytes**; at
  abstract `D` it is not available. Fix: make labels themselves `D` (the wrapper truncates inside
  the serialiser and exposes only `D`-valued label equality), or add `truncOp : D → D'` with `D'`
  another opaque type carrying only `DecidableEq`. Either is sound (still equality-only) but it is
  more trusted plumbing and it changes spartan-chain's Merkle module.
- **Relation hashes.** `chainStep/leafStmt/nodeStmt` must be `D`-valued and supplied by
  `DigestOps` (as #4 §3 notes). These are fixed public functions the ROM adversary can also compute,
  so they add no channel — **provided their outputs are `D` and `V` cannot read their bytes.** A
  subtlety: the honest `V` checks `c = leafStmt h n` where `c` is the statement (a `D`) and `h` is a
  chain end it computed by iterating `chainStep` on a `D` from the proof. That is fine (equality of
  two `D`). But the node branch checks `c = nodeStmt c₁ c₂` with `c₁,c₂` from the proof — also fine.
  So the relation half survives at `D`, at the cost of the `DigestOps` record.
- **The real recursion.** A node SNARK's `Rel` says children are accepted by `Vb` under concrete
  BLAKE2s; the node circuit computes BLAKE2s in R1CS, so the *prover* and the *circuit matrices*
  contain a BLAKE2s description. Candidate A does not forbid this: the prover `P` is unrestricted
  (it is not security-relevant), and the circuit is the prover's internal matter. `V` only checks a
  succinct proof; its BLAKE2s-in-R1CS "knowledge" lives in matrices `V` evaluates as *field*
  arithmetic on prover-supplied values, never as a `Digest` constant compared with an answer. This
  is the key compatibility point the user flagged, and A (and E) preserve it. The danger is not the
  circuit; it is the **challenge** derived from answers (§4).

### 3.4 Verdict on A alone

A closes the backdoor for everything that uses answers only by equality, i.e. commitments, Merkle,
and the digest relation. It **cannot** support Fiat–Shamir without an added interface (ADV-M5.4,
#4-comment item 4), and the obvious such interface reopens the backdoor. A alone is therefore not
deployable for spartan-chain (which needs field challenges and column indices from answers). The
contribution of A is the *equality-only discipline*; the open problem it leaves is the challenge
channel, addressed next.

## 4. The Fiat–Shamir obstacle to Candidate A, and the challenge interface

### 4.1 What spartan-chain actually needs from answers

From `SpartanChainTranscript`/BLUEPRINT §6, the entry derives from squeeze answers:

- **field challenges** `chE a := EF.ofBytes (first 24 bytes of a)` — an element of `EF = GF(2^64)³`,
  used in sumcheck/PCS polynomial-identity checks;
- **column indices** `idxOf ℓ a i` — `ℓ`-bit slices of `natLE a`, used to pick Merkle columns to
  open.

Both are *functions of answer bytes*, exactly R2 of §2. The soundness proof relies only on the
**fiber-uniformity** facts `card_chE_fiber` (every `EF` value has exactly `2^64` preimage answers)
and `card_idx_fiber` (every index tuple has `2^{256-ℓc}` preimages). It does **not** rely on `V`
being able to read raw bits: it relies on the *challenge value* being uniform and used in an
*identity check* `p(challenge) = q(challenge)` for prover-supplied polynomials `p,q`, or in a
*position* chosen uniformly.

### 4.2 The naive challenge interface reopens the backdoor

If the contract hands `V` a `D → Fin (2^b)` or `D → ByteArray` to extract `b` challenge bits, then
`V` can locally recompute BLAKE2s on the same (structured, known) query, extract the same `b` bits,
and `decide` equality: recognition at `2^-b`, certified at `errorCap` for `b ≥ 128` (counting) or
spread across answers under the potential (ADV-M5.4). **Any interface that lets `V` observe
challenge bits as an ordinary comparable value is as bad as A with no fix.** This is the
information-theoretic tension the ADV1 review identified, and it is real.

### 4.3 The restricted algebraic interface (the proposal)

The way out is to give `V` the challenge as an **opaque field element on which only an algebraic,
equality-of-field-values-after-evaluation interface is available**, never a projection to bits and
never equality against a `V`-named field constant. Concretely, add to `DigestOps` (or a sibling
record `ChallengeOps D F`):

```lean
structure ChallengeOps (D F : Type) [CommRing F] where
  squeezeF   : D → F                      -- derive a field challenge from a (squeeze) answer
  idx        : D → ℕ → ℕ → ℕ              -- idxOf ℓ a i : an opaque *position*, used only to index
  -- F is handed to V ONLY through [CommRing F] plus:
  evalPoly   : List F → F → F             -- Horner eval of a prover-supplied coeff list at a point
  -- and NOTHING that reveals F's bytes; in particular NO (F → ByteArray), NO (F → Bool) except
  -- DecidableEq F used only to compare two interface-produced F-values.
```

`V` is polymorphic in `F` as well: `V : ∀ (D F) [DecidableEq D] [CommRing F] [DecidableEq F],
DigestOps D → ChallengeOps D F → D → Tape D → OProg D Bool`. The wrapper instantiates `F := EF`
and `squeezeF := chE`, `idx := idxOf`. Now:

- `V` can compute `evalPoly coeffs (squeezeF a)` and compare it with `evalPoly coeffs' (squeezeF a')`
  or with another interface-produced `F` — this is exactly the sumcheck/PCS identity check, and it
  is sound.
- `V` **cannot** name a field constant equal to "BLAKE2s of this query mapped through `chE`",
  because the only `F` values it can form are `const 0`, `const 1` (from `CommRing`), sums/products
  of those and of `squeezeF` outputs — i.e. polynomials evaluated at challenge points. To recognise
  the instantiation it would need an `F` value it can *also* compute oracle-independently and that
  *collides with* `squeezeF a` only under BLAKE2s. Because `squeezeF a` is a uniform `EF` element
  over the `2^256` answers (`card_chE_fiber`), the set of `V`-constructible `F` values that equal it
  is, for any fixed polynomial `V` writes, a `≤ deg/2^192`-fraction event — chargeable to `μ` at the
  honest rate, **not** forced in deployment, because `V` has no access to the *bytes* that BLAKE2s
  fixes. (See §5 for the parametricity caveat and §14 for the residual attack through high-degree or
  interpolating polynomials.)

### 4.4 Why `CommRing F` and not a general type

`CommRing` is deliberately *rich enough* for FS identity checks (the honest need) and *poor enough*
that `F`'s only inhabitants `V` can build are ring expressions in `const 0/1` and challenge values.
The danger operations are precisely the ones omitted: `F → ByteArray`/`F → Fin n`/`F → bits`
(would leak bits → §4.2 attack), `OfNat F k` for `k > 1` or a literal field embedding
(`V` could then write `const (chE (localBlake2s q))` — a recognition constant), and `Inhabited`/
`default`/`arbitrary` returning a *specific* field element (same). The gate must check that `V`'s
signature uses exactly `[CommRing F] [DecidableEq F]` and no `[OfNat F _]`, `[Repr F]`, `[Fintype F]`,
`[Coe ByteArray F]`, etc. `OfNat F 0`/`OfNat F 1` come with `CommRing`; the attacker can build
`const n` for any `ℕ n` by repeated addition — but `const n` is a *fixed* field element independent
of the challenge, and a fixed element collides with a uniform `squeezeF a` only at rate `2^-192`,
which is honest and chargeable. The subtle residual is that `V` can build the *polynomial*
`∏ (x - cᵢ)` and evaluate at a challenge, which for adversarially chosen `cᵢ` (from the proof!)
could encode a recognition — this is the §14 attack and the reason review stays load-bearing.

### 4.5 Column indices

`idx : D → ℕ → ℕ → ℕ` returns a *position* (a `ℕ < N`), used only to index into prover-supplied
column data and Merkle paths. A position is `ℓ`-bits of information per index — so it *is* a narrow
recognition site: `V` could accept iff the opened position equals a `V`-constant. But (a) positions
are small (`ℓ ≤ 23`), so one index recognises at only `2^-ℓ`, far above `errorCap`, and spreading
over the `t ≈ 190` indices to reach `2^-128` requires the potential to charge them — which it does
at the honest rate (`card_idx_fiber`), *and* the honest verifier already compares each opened
column against a Merkle path, so a position-recognition branch is an extra acceptance condition that
review can see in `NOTES.md`. Positions cannot be made fully opaque (they must index arrays), so
this is a residual channel closed by "positions are low-entropy + disclosed + priced", not by
typing. Acceptable, because at `2^-ℓ` per index a position backdoor is strictly weaker than the
original and cannot reach `errorCap` without visibly consuming all `t` indices.

## 5. Parametricity-breaking tricks in Lean 4 (is the meta-theorem even true?)

The whole typed approach rests on a **meta-theorem**, not a Lean theorem: "a well-typed closed term
of the polymorphic type can use `D`/`F` only through the supplied interface." This is a free-theorem
/ parametricity claim about Lean 4's type theory. It must be stated with care, because Lean is **not**
System F and parametricity is **not** unconditionally true for it.

### 5.1 What is known

- **Parametricity holds for pure dependent type theory** (Reynolds; Bernardy–Jansson–Paterson for
  dependent types; the "theorems for free" line). Lean 4's core without the three axioms is such a
  theory, and `#check @...`-style free theorems do hold for terms built in it.
- **The three permitted axioms are the danger.** `Classical.choice` (hence `em`, `Classical.dec`),
  `propext`, and `Quot.sound` are *opaque constants* with no computational content and no
  parametricity guarantee. A term may use `Classical.choice` to produce, from `Nonempty D`, an
  element of `D` it did not receive — but that element is still an *abstract* `D`, so it can only be
  compared by `DecidableEq`; choice does **not** give `V` the *bytes* of a `D`. What choice *can* do
  is let `V` branch on an undecidable proposition about `D` (e.g. `Classical.choice`-extract a
  witness of `∃ d : D, P d`), which is a non-computational branch — but the gate requires `Vb` to be
  **computable** (it must `.run` and produce a `Bool` the harness executes), and a `Classical.choice`
  branch that affects the result makes `Vb` noncomputable or constant. This is why #4 §5's table lists
  "noncomputable branches" under the escape hatches closed by "gate: `Vb` computable."

### 5.2 Concrete Lean-4 escape hatches the reviewer must consider, and their status

| Trick | Does it break opacity? | Closed by |
|---|---|---|
| `cast`/`Eq.mpr` on a proof `D = Digest` | Only if such a proof exists. `V` is given no `D = Digest`; it cannot manufacture one (`D` is a bound type variable, not definitionally `Digest`). A `@[simp]`/`decide` "proof" of `D = Digest` cannot be closed for abstract `D`. | type variable is abstract; no `D = Digest` in scope |
| `HEq` / `Eq.rec` across types | Same: needs a type equality it does not have. | same |
| `Classical.choice (h : Nonempty D)` | Produces an abstract `D`, not its bytes; usable only via `DecidableEq`. | opacity preserved; noncomputable-decision closed by `Vb` computable |
| `Decidable`/typeclass resolution picking a `D`-specific instance | At abstract `D`, only the instances **passed as arguments** (`DecidableEq D`, `CommRing F`) resolve; no `Hashable D`, `Repr D`, `ToString D`, `OfNat D _` is in scope. | gate checks the literal type: exactly `[DecidableEq D]` (and `[CommRing F] [DecidableEq F]`), no extra instance binders |
| `structure eta` / projection tricks on `DigestOps`/`ChallengeOps` | The records expose only the declared fields; eta gives nothing new. | field list is contract-fixed |
| Universe polymorphism / `Type u` games | `D : Type` fixed at `Type 0`; no universe channel to bytes. | `D : Type` monomorphic universe |
| `Quot.sound`/`Quot.lift` to collapse distinct `D` | Collapses by a *relation `V` must prove respected*; cannot reveal bytes. | opacity preserved |
| **Learning bytes by query patterns** (the subtle one) | `V` can query `[inr d]` and `[inl b]` and compare answers; if the serialiser made `serialise [inr d] = serialise [inl (bytesof d)]`, equality of answers would be a byte-level test on `D` (#4 §5 "ambiguous serialisation"). | **tagged, length-prefixed, injective serialiser**; kernel lemmas `serialise_inl_ne_inr`, `serialise_injective`, `parse_serialise` (trusted controls). This is essential and is the one place a sloppy wrapper reopens everything. |
| Recursion indexed by `D` / `D`-indexed types | `OProg D` recursion is fine (structural); it gives no byte access. | — |

### 5.3 The honest status of the meta-theorem

**We cannot prove the parametricity meta-theorem inside Lean for arbitrary submitted terms.** The
contract relies on: (i) the gate checking the *exact* type (instances included); (ii) the hygiene
rules (no `unsafe`/`implemented_by`/`extern`/`csimp`, axioms limited to the three, `Vb` computable);
(iii) the kernel-checked serialiser-injectivity controls; and (iv) the informal but robust argument
that, under (i)–(iii), the only `D`/`F` operations in scope are the interface ones. This is the same
epistemic status as #4 §2's concession ("parametricity is a meta-theorem about Lean terms, not a
theorem inside Lean"). A probe can *demonstrate* that specific backdoor terms **fail to type-check**
(it cannot be a Lean theorem that a term is ill-typed, but a build log showing the error is
evidence), and that the honest spartan-chain `V` *does* type-check under the interface. I did not run
such probes (optional per the coordinator); §9.4 lists them as recommended follow-ups. The residual
meta-theoretic risk is genuine but, I argue in §10, smaller than the cryptographic residual, because
the Lean-4 escape hatches above are enumerable and each is closed by a stated check.

## 6. Candidate B: unknowable deployment oracle (salt/beacon/keyed), and why it fails

The idea: make the deployed oracle unknown to `V` at certification time, so `V` cannot carry a
recognition constant.

- **Per-evaluation salt** `H_k(q) = BLAKE2s(tagRO ‖ k ‖ q)`, `k` fresh per benchmark run. Defeated,
  V3-S1-M1 ("Why no salting fixes it"): recursion needs the circuit (hence the native prover) to
  compute `Vb`, so `k` must be available to the prover and therefore can be carried in the proof;
  the backdoor reads `k'` from the proof and checks two oracle points against
  `BLAKE2s(tagRO ‖ k' ‖ ·)`. That two-query check is certifiable by pure counting (put the first
  answers that more than `2^128` salts map to into `bad` by Markov; the second is then bad for
  ≤ `2^128` values), no property of BLAKE2s used. **Within the ROM, every instantiation known to
  the prover can be recognised by a certified verifier.**
- **A public beacon / key sampled after the entry is frozen.** Removes the "carry `k` in the proof"
  only if `V` never learns `k` — but `V` *must* evaluate the oracle on the deployed key (it queries
  it), and the recursion circuit must hash under the same key, so the key is in the honest data
  path. A beacon helps against *precomputed* magic proofs (it is already used for fresh chain
  starts, §6.7 "Precomputed proofs"), but not against a `V` that recognises the key it is run with.
- **Secret-keyed oracle (MAC).** Impossible: the recursion evaluates the oracle, so the key is
  public to the circuit.

**Conclusion.** B is a dead end *on its own* and the literature agrees: there is no black-box ROM
mechanism that hides the instantiation from a verifier that must compute with it. Interestingly,
**B becomes useful only *in combination with* the parametric interface**: if `V` is parametric and
cannot name field/byte constants, then a salt it reads *as an opaque `D`* gives it nothing, and the
"carry `k` in the proof" attack fails to type-check (the carried `k'` would have to be compared
with a `V`-computed BLAKE2s constant, which does not exist at `D`). So salting is not a fix, but it
is a *cheap defence-in-depth* under Candidate E, and it is already present for freshness. I do not
rely on it. The one externally-keyed idea that is *not* dead is the VRF-challenge service of
Ghosal et al. 2026 (§13), which is a standard-model move, not a ROM one, and out of scope for a
ROM contract.

## 7. Candidate C: semantic restrictions — KS over a family of oracles / digest obfuscation

Instead of typing `V`, change *what the theorem quantifies over* so that the single deployment point
is no longer measure-zero-invisible.

### 7.1 KS relative to a family that includes BLAKE2s-like functions

Require `KS` to hold not for a *uniformly random* `H`, but for every `H` in a family `𝓕` that
contains structured/efficiently-computable functions (including BLAKE2s itself). If BLAKE2s ∈ 𝓕 and
the theorem must hold for *every* member, then a `V` that accepts a magic proof under BLAKE2s fails
KS at that member, so it cannot be certified.

**Why it does not work as a Lean contract.** (a) "Efficiently computable" is not a property the
counting/potential form can express — it needs a complexity model, which the design deliberately
avoided (DISCUSSION Q6; the contract is Mathlib-only, no adversary type). (b) If 𝓕 is "all
functions", we are back to the current theorem. (c) If 𝓕 is a *specific finite set* including
BLAKE2s, then the theorem is "`V` is sound when `H` = BLAKE2s", which is **exactly the CGH
heuristic we cannot prove** — it would require proving BLAKE2s has the relevant correlation
intractability, a standard-model assumption on BLAKE2s (see §8, §13). (d) The honest entry would
then also have to be proved sound *at concrete BLAKE2s*, which no one can do (it is why the ROM is
used in the first place). C.1 relocates the gap; it does not close it.

### 7.2 Digest obfuscation by the trusted wrapper (the interesting one)

Run `V` against `H ∘ π` where `π` is a fresh secret permutation/encoding of `Digest` sampled by the
wrapper *after* the entry is frozen, and have the wrapper undo `π` on the parts of the computation
that must match concrete BLAKE2s (the relation hashes, the recursion). The intuition: `V` sees
answers in a scrambled digest space it cannot predict, so a recognition constant it hardcoded for
real BLAKE2s does not match the scrambled answers.

**Analysis.** This is really just a keyed oracle with key `π`, and it inherits B's problem *unless*
`V` is already parametric: if `V` can read answer bytes, it can read the scrambled bytes and
compare them with `π`-scrambled local BLAKE2s — but it does not know `π`... except that the
recursion circuit must compute the *unscrambled* BLAKE2s (the relation is about concrete BLAKE2s),
so `π` must be undone somewhere `V`/the prover can see, re-exposing it. Where `π` genuinely helps is,
again, **only under parametricity**: it is the semantic justification for why the opaque-`D`
discipline is *safe* (the wrapper is free to represent `D` however it likes, including a per-run
re-encoding, and a parametric `V` cannot tell), i.e. it is a *model* of §3's opacity rather than an
independent mechanism. C.2 is therefore best read as the soundness intuition behind E, not a
separate candidate. It does **not** stand alone.

### 7.3 Verdict on C

C does not yield a standalone Lean-checkable closure. C.1 relocates the gap to a BLAKE2s assumption;
C.2 is the semantic shadow of the typed approach. Both reinforce that the only *mechanical* lever is
the type system (restrict `V`'s operations), and the only *cryptographic* closure is a named
standard-model assumption (§8). Everything else is review.

## 8. Candidate D: standard-model / named-assumption alternatives

Replace "`H` is a random oracle" by a concrete, falsifiable assumption on BLAKE2s, stated in the
contract, for each use.

- **Merkle / commitments → collision resistance.** The binding of the Merkle commitment needs only
  that BLAKE2s is collision-resistant. One could state, as a contract hypothesis, "no efficient
  algorithm finds a BLAKE2s collision," and prove binding from it. In this contract, binding is
  already handled by the potential (`Collision` events charged at the birthday rate over `logCap`),
  so the ROM already *models* CR; a named CR assumption would let the harness drop the ROM for the
  commitment half. But it needs a complexity model to state "efficient," which the design avoids,
  and it does not touch the challenge channel. Partial at best.
- **Fiat–Shamir → correlation intractability (CI).** This is the CGH98 notion and the modern route
  to *provably sound* FS (Canetti–Chen–Holmgren–Lombardi–Rothblum–Rothblum STOC'19; Peikert–Shiehian;
  Holmgren–Lombardi–Rothblum; §13). A CI hash makes FS sound *for proofs* in the standard model. But:
  (a) CI hashes are LWE-based constructions, **not** BLAKE2s — there is no theorem that BLAKE2s is
  correlation-intractable for the relevant relation class, and CGH-style and KRS25/Fenzi26 results
  (§13) show that for *arguments* (not proofs) FS can be unsound for every concrete hash including
  idealised ones; (b) encoding CI and an LWE assumption in the trusted base is a large, churny
  addition the design explicitly rejected (DISCUSSION Q6, "ROM-only assumptions"); (c) it changes
  the hash, breaking the BLAKE2s-only deployment and the recursion circuit.
- **A bespoke "BLAKE2s is a good FS hash for this relation" assumption.** This is the honest content
  of what *any* deployed SNARK assumes. It could be *stated* in §5.4 as the residual, but it cannot
  be *proved*, and stating it as a contract *hypothesis* (rather than a disclaimer) would make the
  harness's ACCEPT conditional on an unprovable claim about BLAKE2s — worse than the current honest
  disclaimer.

**Verdict on D.** No standard-model assumption on BLAKE2s is both (i) true/known and (ii)
contract-expressible without a complexity model and a hash change. D is the *right long-term
direction* for the FS part (CI), and the literature is exactly about this, but it is out of scope
for a ROM, BLAKE2s-only contract. The practical takeaway folds into §10's honest statement: the
residual is a BLAKE2s-FS assumption, named but not proved.

## 9. The recommended scheme: typed interface + trusted wrapper + rule + review (Candidate E)

### 9.1 The exact contract changes (trusted)

**(E-1) Query programs indexed by the digest type.** `OProg (D : Type) (α : Type)` with
`query (q : List (ByteArray ⊕ D)) (k : D → OProg D α)`. `run`, `runLog`, `queries` stated at
`D := Digest`, serialising each query. Logs stay `List (ByteArray × Digest)` keyed by serialised
bytes, so `Extractor.lean` (tape, `decodeWit`, budget) is unchanged.

**(E-2) The proof grammar and serialiser.** `Tape D` partitions a proof into byte segments (free
to compute on) and digest slots (only `D`, only comparable). `serialise : List (ByteArray ⊕ D) →
ByteArray` at `D := Digest` (tag byte per element, length-prefixed segments, fixed 32-byte slots);
`parse : Proof → Option (Tape Digest)` its inverse. `Vb` rejects unparsable proofs and proofs above
`proofCap`.

**(E-3) The two operation records.**
```lean
structure DigestOps (D : Type) where
  chainStep : D → D ; leafStmt : D → ℕ → D ; nodeStmt : D → D → D
  -- optional label projection to a second opaque type, for 31-byte labels (§3.3)
structure ChallengeOps (D F : Type) where
  squeezeF : D → F           -- field challenge from an answer (wrapper: chE)
  idx      : D → ℕ → ℕ → ℕ    -- column index (wrapper: idxOf); returns a *position*
```

**(E-4) The submission type.**
```lean
V : ∀ (D F : Type) [DecidableEq D] [CommRing F] [DecidableEq F],
      DigestOps D → ChallengeOps D F → D → Tape D → OProg D Bool
```
`P : Digest → Wit → OProg Digest (Tape Digest)` may stay at `Digest` (not security-relevant).

**(E-5) The wrapper (`Submission.Vb`).** `D := Digest`, `F := EF`, fills `DigestOps` with the
concrete BLAKE2s `chainStep/leafStmt/nodeStmt`, `ChallengeOps` with `chE`/`idxOf`, parses the proof,
runs `V … .run blake2sOracle`, rejects above `proofCap`.

**(E-6) Gate rule.** Check `V`'s type **literally**, including that the instance binders are exactly
`[DecidableEq D] [CommRing F] [DecidableEq F]` and no others (no `Repr`, `Hashable`, `OfNat F _`
beyond `CommRing`'s `0/1`, `Coe _ F`, `Fintype F`, `ToString`, `F → ByteArray`, …); check `Vb`
computable; keep the hygiene bans and axiom audit.

**(E-7) Trusted serialiser lemmas (kernel-checked controls).** `serialise_injective`,
`serialise_inl_ne_inr`, `parse_serialise`. Without these the byte/slot channel of §5.2 reopens
everything.

Trusted-base cost: ≈30–45 lines (`Tape`, `serialise`, `parse`, `DigestOps`, `ChallengeOps`, the
wrapper), within the 500-line budget (currently 331 on the amended branch).

### 9.2 The rule (semantic) and the process

In `AGENTS.md` (which at the pin says nothing about O-25, ADV-M5.5), add, as a disqualification:

> **R-O25.** No branch of `V` may accept a proof because a value it did not obtain from the oracle,
> from the `DigestOps`/`ChallengeOps` interface, or from the proof agrees with a value that it did.
> In particular `V` must not compare a challenge, index, or digest with any oracle-independent
> constant it constructs. Entries that do are disqualified. `NOTES.md` must list every place where
> `V`'s acceptance depends on a value derived from an oracle answer other than (a) equality of two
> digests, (b) a polynomial identity check on challenge field elements, or (c) a Merkle-path check
> at a derived position.

Process (ADV1, F1 §2.5): mandatory S7 intake review of `V`'s source against R-O25 and the
`NOTES.md` disclosure; a **public challenge period** before a record stands, during which anyone may
submit a magic proof the record's `Vb` accepts (an executable refutation — the strongest possible
check, since a real backdoor is exhibited, not argued).

### 9.3 Why E excludes the backdoor and each listed disguise

| Disguise (from #4 §1, ADV-M5) | Excluded by |
|---|---|
| empty/any-query trigger `decide (a = trigger)`, `trigger : Digest` a `V`-constant | type: no `Digest` constant at `D`; `a : D` comparable only with other `D` |
| literal 32-byte trigger (ADV-M5.1) | same — a literal `Digest` is not a `D` |
| recomputed FS challenge compared with oracle | challenge is opaque `F`; no `F`-constant = `chE(localBlake2s q)` is constructible (§4.3) |
| embedded RISC-V BLAKE2s image / vendored compression | produces `ByteArray`/`Digest`, not a `D`/`F` the result can depend on via comparison with an answer |
| partial recognition (128 answer bits) | no `D → bits`/`F → bits` in the interface |
| spread recognition over many answers | each site needs a constructible constant to compare; none exists for `D`/`F` (positions excepted, §4.5, priced + disclosed) |
| ambiguous serialisation byte-test (§5.2) | injective tagged serialiser + kernel lemmas (E-7) |
| any `D`-op beyond equality (`Repr`, `Hashable`, order, projection) | gate checks literal instance list (E-6) |
| trace-check debug branch (ADV-M5.2) | the branch would compare a proof-supplied trace output (a `D`) with an answer (a `D`) — allowed as *equality of two digests*, but it accepts iff `localTrace = answer`, and `localTrace` is computed by the prover and *sent in the proof* as a `D`; crucially the branch cannot *also* check that `localTrace` is BLAKE2s-of-something without a `Digest`-valued hash of its own, which at `D` it does not have. If it uses `DigestOps.chainStep` etc. it is computing the sanctioned relation, not recognition. (This is the subtlest case; see §14.) |
| Lean escape hatches (`cast`, `Classical`, instances, `Quot`, universes) | §5.2 table |

### 9.4 Recommended probes (optional, not run here)

1. Build a scratch file with the Candidate-E type and attempt the literal-trigger backdoor; confirm
   it **fails to type-check** (build-log evidence, not a theorem).
2. Attempt the `squeezeF`-recompute backdoor with `ChallengeOps`; confirm no `F`-constant path.
3. Port spartan-chain's `leafProg`/Merkle/transcript to the interface and confirm it type-checks and
   the fiber-count lemmas (`card_chE_fiber`, `card_idx_fiber`) still go through with `squeezeF`/`idx`
   as abstract-but-wrapper-fixed functions. This is the real feasibility test and the main cost
   (§12).
4. Confirm `serialise_injective`/`serialise_inl_ne_inr`/`parse_serialise` are provable for the
   chosen serialiser. Run under `cd /home/devops/Verified-zkEVM/rf-core-sc && timeout 900 lake env
   lean scratch/<f>.lean`.

## 10. Honest strength assessment: proved / assumed / residual

This is the central deliverable. I separate the three claims the coordinator asked me to
distinguish.

### 10.1 (a) "The known CGH mechanism is excluded by construction" — **largely proved, with a
meta-theoretic and a serialiser assumption**

*Claim.* A `V` of the Candidate-E type cannot contain the backdoor of `Controls/Backdoor.lean` or
any of its §1/ADV-M5 disguises that work by *`V` evaluating the instantiation and comparing with an
oracle answer*, for the digest/commitment/Merkle part and for equality-only use of answers.

*What backs it.* (i) A **meta-theorem** (parametricity / free theorems for Lean-4 terms) that a
well-typed closed term uses `D` only through `DecidableEq D` and the supplied `D`-valued ops; this
is **not** a Lean theorem (§5.3) and is **assumed**, supported by the enumerable escape-hatch
analysis of §5.2 and by the gate+hygiene checks. (ii) Kernel-checked **serialiser injectivity**
lemmas (E-7) — genuinely proved. (iii) The gate's **literal type check** and `Vb` computability —
mechanical. Evidence short of proof: probes showing the backdoor terms fail to type-check (§9.4,
not run).

*Honest caveat.* "Excluded by construction" is true **modulo the parametricity meta-theorem for
Lean 4 with `{propext, Classical.choice, Quot.sound}`**. I believe this meta-theorem holds for the
specific interface (the three axioms cannot manufacture a `Digest` from a `D`, only an abstract
`D`, and non-computational branches are killed by `Vb` computable), but it is an assumption, and a
determined reviewer should probe it (§9.4.1-2). This is strictly stronger than the status quo
(rule+review only) and strictly stronger than #4's Candidate A for the parts A covered.

### 10.2 (b) "No verifier in the allowed class is ROM-secure but BLAKE2s-insecure" — **NOT proved,
NOT provable in general, almost certainly false**

*Claim (the one we would love).* Every `V` that type-checks and is certified in the ROM is actually
sound under BLAKE2s.

*Status.* **False in general, and known to be.** The challenge interface (§4) necessarily lets `V`
compute *some* function of answer values (field challenges, positions) — it must, or FS/SNARKs are
impossible (ADV-M5.4; this is information-theoretic, not a counting artefact). Once `V` computes a
challenge and uses it in a decision, we are in the regime where CGH98 and its SNARK follow-ups bite:
Goldwasser–Kalai FOCS'03 (a ROM-sound argument whose FS version is unsound for *every* hash);
Bartusek–Bronfman–Holmgren–Ma–Rothblum TCC'19 (Kilian/Micali-based SNARGs, the template behind this
very construction, can be FS-unsound); Khovratovich–Rothblum–Soukhanov CRYPTO'25 (a *deployed*
GKR+KZG protocol, FS-unsound under any concrete hash); Fenzi 2026 (extends to Spartan/Aurora-style,
i.e. *exactly spartan-chain's family*). These results construct protocols/statements that are
ROM/argument-sound but whose concrete-hash FS instantiation is unsound. Translating any of them into
a Candidate-E `V` would give a term that type-checks, is ROM-certified, and is BLAKE2s-insecure.
Therefore claim (b) is **unprovable** (proving it would refute the literature) and we must not claim
it. **Candidate E does not, and no mechanical fix can, achieve (b).** The user should understand
this is a theorem-level limitation, not a gap in the design.

### 10.3 (c) The residual, compared with any deployed FS SNARK

*What remains after E.* A `V` can still be ROM-secure and BLAKE2s-insecure **only through the
challenge/position channel** (§4.3, §4.5), and only in the forms the FS-uninstantiability literature
produces — which require the attacker to *build a genuine FS-unsoundness construction for
BLAKE2s-instantiated FS over this relation*, not merely to drop in a one-line magic check. That is:

- **the same residual risk every deployed Fiat–Shamir hash-based SNARK already lives with.** STARKs,
  Spartan, Plonk, WHIR, etc. are all FS-instantiated with a concrete hash and none has a
  standard-model soundness proof for that instantiation; they rely on the ROM heuristic exactly as
  this contract does. Candidate E reduces O-25 from "*any* submitter gets a free, one-line,
  review-invisible backdoor" to "*a submitter who can mount an FS-uninstantiability attack against
  BLAKE2s-FS for the Spartan/WHIR relation* can break board T" — which is a research-paper-level
  effort, is visible to review as unusual challenge handling, and is caught by the public-challenge
  period if it is ever exhibited.
- The honest floor the user set ("avoid CGH at all costs; gaming reported") is met in the sense that
  the *CGH construction itself* (evaluate instantiation, compare) is excluded; what is not excluded
  is the deeper FS-uninstantiability, which is not specific to this contract and cannot be excluded
  by any ROM mechanism.

### 10.4 Could a workaround exist, of what kind, with what confidence

- **A free, review-invisible, kernel-only backdoor of the `Controls/Backdoor.lean` kind:** I am
  ~80% it does **not** survive E (the typing closes the direct mechanism; the residual requires the
  challenge channel). The 20% is the parametricity meta-theorem being subtly false for Lean 4, or a
  serialiser/`DigestOps` slip — both reducible by the probes of §9.4.
- **A determined backdoor through the polynomial-evaluation channel** (`evalPoly` with
  proof-supplied coefficients encoding a recognition — §14): I am ~50% a motivated adversary could
  build one that review would plausibly miss, because `evalPoly` is Turing-rich enough to hide an
  interpolation-based comparison. This is the single most dangerous attack on E and the reason
  review + challenge period stay load-bearing. Mitigation: restrict `evalPoly` to a fixed low degree
  / fixed shape per protocol step (the honest sumcheck polynomials are degree ≤ 3), so the attacker
  cannot interpolate a recognition function; this tightens E at a real cost to `V`'s expressiveness
  and is the main lever a future hardening pass has.
- **An FS-uninstantiability attack (literature-grade):** ~certain it exists *in principle* (10.2);
  the question is only whether a competitor invests the effort for a board-T win, which the
  incentive structure and the public challenge make unattractive but not impossible.

**Bottom line.** E is the strongest *mechanical* position available in a ROM contract: it converts
O-25 from a free, invisible, counting-certified backdoor into the generic FS-uninstantiability
residual shared by all deployed SNARKs, and it makes any residual attack (i) expensive, (ii)
channel-localised to challenges/positions, and (iii) visible to review and refutable in public. It
does **not** close O-25 to a kernel theorem; nothing can, and the design text must say so (§5.4
should read: the residual is the FS/BLAKE2s heuristic, as for every deployed SNARK).

## 11. Completeness error δ, grinding, and the liveness mirror of CGH

The rules will drop perfect completeness over every oracle and allow a completeness error δ
(2^-128 or 2^-96) over a **uniformly random** `H`, enabling grinding and rejection sampling. This
interacts with O-25 in two ways the coordinator flagged.

### 11.1 Grinding looks like partial recognition — and must not become a backdoor

A grinding check is "the answer `a` to this query has `g` leading zero bits," i.e. a comparison of
`g` answer **bits** against the constant `0`. Under a naive bit-reading interface this is exactly
the §4.2 recognition primitive: once `V` can test `leadingZeros(a) ≥ g`, it can test
`a[0..g] = localConstant[0..g]` and recognise. So grinding must be expressed **without** giving `V`
a general bit-projection.

*Proposed safe expression.* Add to the interface a single contract-owned predicate
```lean
  leadZeros : D → ℕ          -- wrapper: number of leading zero bits of the answer
```
and require the grinding **threshold** `g` to come from the **statement or proof**, not from a
`V`-internal constant, and the accepting condition to be `leadZeros a ≥ g` (a comparison with a
*value that entered through the proof/statement*, which R-O25 explicitly permits). Why this is safe
where general bit-reading is not: `leadZeros a ≥ g` depends on the answer only through the single
monotone statistic `leadZeros`, whose value for a uniform answer is geometrically distributed and
**carries no information that identifies BLAKE2s** — every oracle, random or BLAKE2s, has answers
with `g` leading zeros at rate `2^-g`. The event "`leadZeros a ≥ g`" is not correlated with *which*
function `H` is; it is the same event for all `H`. Contrast a recognition check `a[0..g] =
localBlake2s(q)[0..g]`, which *is* correlated with `H` being BLAKE2s. So the discriminating
question for any answer-statistic the interface exposes is: **does the statistic's value on a fixed
answer depend on which oracle produced that answer?** `leadZeros` — no (safe). `a[0..g]` compared
with a local constant — yes (backdoor). The interface may expose any *oracle-agnostic* statistic
(leading zeros, popcount, `a mod m` against a *proof-supplied* residue) but never a comparison
against a `V`-constructed digest/field constant. This is the precise form of the §2 R1/R2 boundary
under the completeness change, and it is review-checkable and type-enforceable (the statistic
functions live in the trusted `DigestOps`; `V` gets only their `ℕ`/`Bool` outputs compared with
proof-supplied values).

*Residual.* `leadZeros a ≥ g` with `g` from the proof is a mild recognition site only if the
*honest* proof's `g` and the *magic* proof's `g` can differ in a way that correlates with BLAKE2s —
they cannot, because `g` is prover-chosen data, not a function of `H`. I am fairly confident
grinding is safe under this interface; the reviewer should check that no *composite* of
`leadZeros`+`idx`+`evalPoly` reconstructs a byte-projection.

### 11.2 The liveness mirror of CGH (the dangerous dual)

Perfect completeness over every `H` currently *also* protects against a dual backdoor: a `V` that
**rejects** honest proofs exactly when the oracle is BLAKE2s. With δ-completeness over a *random*
`H`, a certified `Complete` says only "for a uniformly random `H`, the honest prover is accepted
except with probability δ." A random-`H` statement says **nothing about the single deployed `H`**:
a `V` can reject all honest proofs precisely under BLAKE2s (a `2^-256`-measure set of oracles), keep
δ-completeness over random `H`, and thereby make the honest entry — or a competitor's entry sharing
a library — score zero in deployment while looking complete in the certificate. This is the exact
mirror of the KS backdoor, and it is **newly opened by the completeness change**. Note it is a
*griefing/denial* attack, not a false-acceptance attack, so its payoff is different (sabotage, not a
free win), but it is real and the user was right to flag it.

*Does Candidate E exclude it?* **Partially, by the same typing, with the same residual.** The
natural liveness backdoor "reject iff a computed BLAKE2s constant matches an answer" fails to
type-check for the same reason as the KS backdoor (no `Digest` constant at `D`). But a liveness
backdoor through the *challenge channel* (reject iff the challenge-derived polynomial identity takes
a specific value that only BLAKE2s produces) is as unprovable-to-exclude as 10.2. So typing reduces
liveness-CGH to the same challenge-channel residual.

*What actually covers it: the concrete smoke check.* The decisive defence against the liveness
mirror is **not** typing but the **harness's concrete smoke check** (DESIGN-v3 §6.3; F1 §5.3,
REPORT §2.8 "liveness"): the harness runs the entry's *native prover* and *deployed `Vb` under
BLAKE2s* on the benchmark instances and requires acceptance. A `V` that rejects honest proofs under
BLAKE2s fails the smoke check concretely — the only place in the whole pipeline that evaluates
behaviour *at the deployment oracle* rather than under `∀ H`. ADV-m1 already recommends running
liveness on the native prover's real proofs with an emitted query log; that recommendation becomes
**security-critical** under δ-completeness, not just a vacuity fix. **Recommendation: make the
concrete liveness smoke check mandatory and adversarial** (run `Vb` under real BLAKE2s on honest
proofs for every ranked entry; a rejection is disqualifying), and state in the design that
δ-completeness over random `H` is covered against the liveness mirror *by the smoke check, not by
the certificate*. This is the honest division of labour: the certificate handles `∀ H`/random-`H`
soundness and completeness; the concrete smoke check is the one guard at the deployment point, for
both the acceptance backdoor (public challenge period) and the rejection backdoor (liveness smoke).

## 12. Cost to the honest entry (spartan-chain) and trusted base

### 12.1 What changes in spartan-chain's `V`

spartan-chain's verifier (`SpartanChainVerifierTop`) splits into `leafProg` (the only query program;
Merkle + transcript + sumcheck/PCS) and a node branch (no query). Under Candidate E:

- **Merkle (`SpartanChainMerkle`).** Answers become `D`; `trunc a : Label` becomes a `DigestOps`
  label projection to an opaque label type (§3.3). `parseLeaf/parseNode/parseAbsorbRoot`,
  `labelsIn`, `verify`, `open_binding_prefix` are all equality-on-`D`/label — they port, but the
  module must be rewritten to take labels as opaque. Real work, mechanical.
- **Transcript (`SpartanChainTranscript`).** `chE : Digest → EF` and `idxOf` move into
  `ChallengeOps` (`squeezeF`, `idx`); `V` calls them instead of computing on bytes. The **field
  challenges feed sumcheck/PCS identity checks** (`evalPoly`-style), which is exactly the allowed
  algebraic interface — these port. The **fiber-count lemmas** `card_chE_fiber`, `card_idx_fiber`
  are proved about `chE`/`idxOf` as concrete functions; under E they are facts the *wrapper* guarantees
  about `squeezeF`/`idx`, and the soundness proof uses them as hypotheses (the `KState` is built by
  the submitter against the wrapper-supplied ops). So the KS proof structure
  (`SpartanChainSoundnessKS*`, the potential, `bad_step_le`, the transcript forest) is **unchanged in
  shape** but re-parameterised over the abstract ops — a non-trivial but mostly mechanical refactor,
  since the proofs already treat `chE`/`idxOf` through their fiber counts, not their bit structure.
- **`natLE`/raw bit reads.** Any place `V` reads raw answer bytes outside `chE`/`idxOf`/`trunc` must
  be removed. From the transcript module, `chE` and `idxOf` are the only consumers of answer bytes,
  and both become interface calls — so I expect **no essential loss**, which is the good news:
  spartan-chain already funnels all answer-byte use through two functions whose only proved property
  is fiber-uniformity, exactly what E abstracts. This is strong evidence E is honest-compatible.

### 12.2 What does NOT change

The prover `P`, the extractor `E`, the image, the BLAKE2s-in-R1CS circuit
(`SpartanChainBlake2s*`), the field layer (`BF64`/`Ext3`), and the relation (`Rel`, `chainStep`,
`leafStmt`, `nodeStmt` — now via `DigestOps`) are untouched in substance. The node branch compares
`c = nodeStmt c₁ c₂` (equality of `D`) and recurses; fine. Crucially the recursion-circuit
compatibility (§3.3) holds: `V` never names a BLAKE2s digest constant; it evaluates circuit matrices
as field arithmetic on prover-supplied values.

### 12.3 Build/proof effort and trusted base

- Trusted base: +≈30–45 lines (§9.1), within budget; +3 kernel-checked serialiser controls. No new
  axioms, no new attribute, no hash change. This is the cheapest of all candidates on trusted base
  (B/C/D either need a complexity model or a hash change).
- Honest proof effort: a refactor of the Merkle and transcript modules and a re-parameterisation of
  the KS proof over abstract ops. REPORT §3.1 puts the entry at ~16.8k lines, of which Merkle/
  transcript ~993 and the field/circuit layers (untouched) ~10.5k. I estimate the O-25 refactor
  touches the ~1–2k lines of Merkle+transcript+KS-glue, not the bulk. (No time estimate per the
  rules; the dependency is: it blocks on E-1…E-7 landing as a contract stage *before* the entry is
  finalised, or the entry is rewritten twice. §11 build-order of #4 §3 applies: land E before S2 is
  frozen — but S2b is already certified against the amended contract, so this is now a *migration*,
  which is a real cost the user should weigh against the review-only option.)

### 12.4 The migration tension (honest note)

spartan-chain is **already certified** (HARNESS: ACCEPT on the amended contract, per MEMORY and the
git log). Adopting E now means re-doing its Merkle/transcript/KS layer against the new types. That is
the chief practical cost of E over "rule+review for season 1" (#4 §8's alternative). My
recommendation stands — E is the only mechanical reduction of O-25 and the direct backdoor is
otherwise free and invisible — but the orchestrator should decide between (i) adopt E now and migrate
spartan-chain, or (ii) ship season 1 with rule+review+mandatory-smoke-check+challenge-period (which
§10.3 shows still leaves the *direct* backdoor only behind review) and adopt E for season 2. I lean
(i) because the direct backdoor is too cheap to leave to review alone (ADV-M5.1 shows review cannot
separate it from honest code), but (ii) is defensible if the migration cost is prohibitive and the
challenge period is genuinely public and incentivised.

## 13. Literature (user-supplied list)

Read from `/tmp/cgh98_snark_followups.md` (treated as reference data). I did not need to fetch
papers to confirm the claims used; where I rely on a specific technical point I mark it. Each item:
what it implies for O-25 and for Candidate E.

### 13.0 CGH98 (Canetti–Goldreich–Halevi, ePrint 1998/011)
The source of O-25. Two tools: (a) diagonalization — schemes ROM-secure but broken by *every*
concrete hash; (b) correlation intractability (CI). Implication: O-25 is an instance of (a), and the
only known *positive* route is (b)/CI. Candidate E does **not** achieve CI (it stays in the ROM);
it blocks the *direct evaluate-and-compare* mechanism and localises the residual to the challenge
channel. Confirms §10.2: claim (b) is unprovable.

### 13.1 Attacks on FS with real hash functions

- **Goldwasser–Kalai FOCS'03.** A 3-message argument ROM-sound but FS-unsound for every hash.
  Implication: the strongest statement of 10.2 — *arguments* (not just pathological ones) exist that
  no concrete hash instantiates soundly. Candidate E cannot exclude a `V` encoding such an argument
  through the challenge channel. This is why I refuse to claim (b).
- **Bitansky et al. TCC'13 (2012/705)** and **Dachman-Soled et al. (2012/706).** FS soundness for
  proofs cannot be proven by black-box reduction to any falsifiable assumption; (706) covers Micali's
  CS-proofs specifically. Implication: even if we *wanted* to add a standard-model assumption (§8),
  no falsifiable-assumption proof of FS soundness for the Micali/Kilian template (which this contract
  is) can exist by black-box means. Reinforces "the residual is a non-falsifiable heuristic," and
  that D is not a route.
- **Ananth et al. TCC'13 (2012/721), Fischlin's paradigm.** The online-extractable FS alternative is
  also unsound for any hash with a known running-time bound. Implication: switching to Fischlin to
  get online extraction (which would help the extractor, O-25-adjacent) does not escape
  uninstantiability. No free lunch by changing the transform.
- **Bartusek–Bronfman–Holmgren–Ma–Rothblum TCC'19 (2019/997), Kilian-based SNARGs.** *Directly on
  point:* the FS version of Kilian's argument — "the template behind SNARKs and STARKs," i.e. this
  contract's exact construction — can be unsound: a contrived CR hash breaks it for a broad PCP
  class, and an interactive PCP breaks it unconditionally. Implication: the construction family is
  *known* to be FS-uninstantiable in the worst case. Candidate E's residual is therefore not
  hypothetical; it is realised in the literature for this template. The saving grace is that the
  attack needs a *contrived* hash or a *contrived* PCP — spartan-chain uses neither — so the
  *heuristic* that BLAKE2s + Spartan is fine is the same heuristic every STARK relies on (§10.3).
- **Khovratovich–Rothblum–Soukhanov CRYPTO'25 (2025/118).** First attack on a *natural, deployed*
  protocol: GKR+KZG, FS-unsound under any concrete hash. Implication: the gap is not only for
  contrived schemes — a real, shipped design falls. Raises the stakes: a competitor *could* in
  principle submit a `V` in the KRS25 family. Mitigation in E: such a `V` must route the attack
  through `squeezeF`/`evalPoly`, where (a) it is a research-grade construction, (b) review sees
  non-standard challenge handling, (c) the public challenge period lets anyone exhibit the magic
  proof. KRS25 is the strongest argument that *review+challenge must stay load-bearing* and that E's
  typing alone is not a proof of (b).
- **Fenzi 2026 (2026/1838).** *Most directly on point:* extends KRS25 to statements **generated by
  running a program**, covering **variants of Spartan and Aurora** — spartan-chain's family. And it
  proves a **fix**: derive FS challenges from the *generated statement* rather than from the program.
  Implication for E: (1) confirms the residual applies to spartan-chain's family specifically, not
  just abstractly; (2) **gives a concrete hardening lever** — bind every FS challenge to the
  statement digest `c` (which spartan-chain already does: the transcript is seeded by
  `0x10 ‖ s ‖ enc64 n ‖ h` and `c = leafStmt h n`, §6.2 "Statement binding"). I recommend the design
  make statement-binding of the transcript seed a **rule** (it already holds in the honest entry),
  citing Fenzi26, as cheap defence-in-depth against the generated-statement attack class. This is the
  one actionable positive result in the list for our exact construction.

### 13.2 Defenses and limits of ROM arguments

- **Arnon–Yogev CRYPTO'25 (2025/329), XFS / white-box FS.** FS + a new proof-of-work, proven secure
  in a *relativized* ROM where the diagonalization attacks have analogues. Implication: there is a
  positive direction (add a PoW/grinding step with a security proof in a stronger-than-ROM but
  still-idealised model). Relevant because the contract is *adding grinding* (§11). Worth examining
  whether the grinding step can be specified à la XFS to get a relativized-ROM soundness statement
  that provably survives the known attacks — a possible **future upgrade of E's challenge channel**.
  I flag it as the most promising research lead for genuinely strengthening (not just localising) the
  residual. (Did not fetch; claim used only at the level of its abstract.)
- **Barbara–Chiesa–Guan (2024/728), "Relativized succinct arguments in the ROM do not exist."**
  *Crucial for recursion:* no succinct argument in the ROM can verify computations that *themselves
  query the oracle*. Implication: this is the formal obstacle behind the §3.3 recursion point — the
  node relation is about concrete BLAKE2s, and a *black-box* ROM succinct argument for a
  BLAKE2s-querying computation cannot exist, which is exactly why the recursion is the *sanctioned
  heuristic* (§5.4) and not a theorem, and why the circuit must compute BLAKE2s in R1CS (non-black-box).
  Candidate E is consistent with this: it forbids `V` from *using* a black-box view of the
  instantiation to recognise it, while permitting the prover's non-black-box (in-circuit) BLAKE2s.
  The paper rules out the *route* O-25's keyed/beacon ideas (B) would need, confirming B is dead.
- **Chen–Chiesa–Gur–O'Connor–Spooner EUROCRYPT'23 (2023/587), PCD from Arithmetized Random Oracles
  (AROs).** Uses an oracle model giving a *non-black-box view* so recursion/PCD can be built.
  Implication: the principled way to make recursion sound is to change the oracle model to an ARO,
  not to patch `V`. This is a possible **alternative to E for the recursion layer**: instead of (or
  with) E, adopt an ARO-style trusted model where the oracle is arithmetized and the recognition gap
  is handled by the model's design. It is a larger trusted-base and design change than E (a new
  oracle abstraction), so out of scope for an immediate fix, but it is the literature's answer to the
  deeper problem and should be noted as the long-term direction for recursion (more than for O-25's
  acceptance backdoor, which E handles).
- **Ghosal et al. 2026 (2026/2114), FS from an external VRF service.** Challenges from a VRF whose
  key the prover never sees — a keyed-oracle that *works* because it is external and standard-model.
  Implication: the one "unknowable oracle" idea (§6) that is not dead, but it requires an external
  trusted service and leaves the ROM, incompatible with a self-contained BLAKE2s deployment and
  recursion (the circuit would need the VRF). Not applicable here, but confirms §6's diagnosis: the
  only way to make the instantiation unknowable is to make it external, which recursion forbids.

### 13.3 Provably sound FS via correlation intractability (the CGH positive line)

Kalai–Rothblum–Rothblum CRYPTO'17 (2016/303, from obfuscation); Canetti–Chen–Reyzin–Rothblum
EUROCRYPT'18 (2018/131, KDM); **Canetti–Chen–Holmgren–Lombardi–Rothblum–Rothblum STOC'19
(2018/1004)**, Peikert–Shiehian CRYPTO'19 (2019/158), Holmgren–Lombardi–Rothblum STOC'21 (2021/286),
Jawale et al. STOC'21 (2020/980), Choudhuri–Jain–Jin FOCS'21 (2021/808), Chen–Lombardi–Ma–Quach
CRYPTO'21 (2020/915), Guan–Yogev 2025 (2025/2328).

Common implication: FS *can* be made provably sound in the **standard model** via CI hashes, for
**proofs** (not all arguments) and specific delegation/GKR settings, under LWE-type assumptions.
Two consequences for O-25/E:
1. **The positive results are for proofs, not for the Micali/Kilian *argument* template** this
   contract uses, and they need LWE + a specific CI hash, **not BLAKE2s**. So they do not give a
   standard-model soundness proof for spartan-chain, and D remains out of scope (§8). Chen–Lombardi–
   Ma–Quach (2020/915) is the sharp divider: it identifies settings where a cryptographic hash is
   *provably needed* and settings where simple hashes suffice — telling us the challenge channel's
   security is genuinely assumption-dependent, reinforcing that E cannot prove (b).
2. **Direction of travel:** if a future season wanted to *prove* the FS part, it would adopt a CI
   hash and an LWE assumption in the trusted base (large), abandoning BLAKE2s-only. E is the
   ROM-native stopgap that is cheap and compatible with BLAKE2s; CI is the expensive standard-model
   endgame. The user's "ROM-only, BLAKE2s-only, avoid heavy trusted base" priorities select E now.

### 13.4 CGH TCC'04 (2003/150) and the notes

- **CGH TCC'04 (length-restricted signatures).** Extends the counterexample to short-message
  signatures. Implication: uninstantiability is robust to restricting the input domain — a warning
  that "restrict `V`'s inputs" is not a fix, consistent with our finding that only restricting `V`'s
  *operations* (typing) bites.
- **Notes (Barak FOCS'01; Chiesa et al. 2025/902; Dao et al. 2023/691).** Barak: another early
  counterexample, same lesson. 2025/902 (FS security *in* the ROM): the positive ROM baseline we
  already rely on — our KS theorem is this kind of result; it says nothing about the concrete hash.
  Dao et al. 2023/691 (weak-FS implementation bugs): a reminder that *statement-binding* bugs (not
  hashing the statement into the transcript) are a real, separate vulnerability — which the Fenzi26
  fix and spartan-chain's seed binding (§13.1) already address; worth a canary that the transcript
  seed includes the statement.

**Net literature verdict.** The list confirms, tightly and for our exact construction family
(Kilian/Micali template, Spartan/Aurora variants), that claim 10.2(b) is false/unprovable and that
the residual is the generic FS-uninstantiability of deployed SNARKs. It yields two concrete
actionable items for E: (1) **mandate statement-binding of FS challenges** (Fenzi26, Dao); (2)
consider an **XFS-style grinding step** (Arnon–Yogev) as a future, provably-stronger challenge
channel. It confirms B is dead (Barbara–Chiesa–Guan, Ghosal) and that D (CI/standard model) is the
expensive endgame, not an immediate option.

## 14. My own best attacks on the recommendation

Ordered by how much they worry me. The reviewer should start at the top.

### 14.1 (MOST DANGEROUS) Recognition through `evalPoly` with proof-supplied coefficients
`evalPoly : List F → F → F` lets `V` evaluate an arbitrary prover-supplied polynomial at a
challenge. An adversary can pick coefficients `cᵢ` (sent in the proof) so that the polynomial
*interpolates a recognition function*: e.g. a high-degree `p` with `p(squeezeF a) = 0` iff
`squeezeF a ∈ S` for a target set `S` chosen to be the challenge values BLAKE2s produces on a magic
transcript. Because the proof supplies `cᵢ`, and the magic proof can supply different `cᵢ` than an
honest proof, `V`'s accept condition "`p(challenge) = 0`" can be made to fire exactly in deployment.
This is *within the typed interface* — no bytes read, no digest constant — yet it recognises. It is
the Candidate-E shadow of the KRS25/Fenzi26 attacks (§13).
*Why it is not a free win:* building such a `p` and proving the resulting `V` has a bounded `KState`
(the certificate still requires KS!) is exactly the FS-uninstantiability construction — research
grade, not one line; and the honest sumcheck uses *degree ≤ 3* polynomials, so a high-degree `p`
is visibly anomalous in `NOTES.md`/review.
*Mitigation (should be adopted):* restrict `evalPoly` per protocol step to a **fixed low degree and
fixed arity** declared by the contract for each sumcheck round, so the submitter cannot supply an
interpolating polynomial; the honest entry needs only degree ≤ 3. This materially tightens E and is
the main hardening lever. The reviewer should check whether low-degree + statement-binding (§13.1)
*provably* defeats 14.1 or merely raises the bar — I believe it raises the bar substantially but do
not have a proof it closes it (that would be a positive FS-soundness result, 10.2).

### 14.2 The parametricity meta-theorem is false for Lean 4 in some corner
If some combination of `Classical.choice`, `Quot`, proof irrelevance, or defeq-unfolding lets a
well-typed `V` extract information about a `D` beyond `DecidableEq` (e.g. a `Decidable` instance on
a `Prop` about `D` that the kernel reduces using the concrete `Digest` at instantiation time), the
whole typing argument leaks. §5.2 enumerates the hatches I know and closes each, but the meta-theorem
is unproven (§5.3). *Mitigation:* the probes of §9.4.1–2; and keeping `Vb`-computability strict
(a `Classical`-decided branch that affects output must make `Vb` noncomputable, caught by the gate).
The reviewer should try to construct a well-typed `V` that behaves differently at `D := Digest` than
its parametric reading predicts.

### 14.3 Serialiser ambiguity / `DigestOps` leakage
If the serialiser is not injective across the `inl`/`inr` tag boundary, `V` gets a byte-equality
test on `D` (§5.2, #4 §5) and the full backdoor returns. Likewise if any `DigestOps`/`ChallengeOps`
field accidentally has a `ByteArray`- or `ℕ`-valued output that reveals answer bytes (e.g. a
careless `labelBytes : D → ByteArray`). *Mitigation:* the kernel-checked E-7 lemmas, and a strict
review that every interface field is `D`/`F`/opaque-valued or an oracle-agnostic statistic (§11.1).
This is a wrapper-correctness obligation, mechanical but unforgiving.

### 14.4 Position-channel recognition (§4.5)
`idx : D → ℕ → ℕ → ℕ` returns `ℓ`-bit positions; a `V` that accepts iff an opened position equals a
constant recognises at `2^-ℓ` per index. Spreading over all `t ≈ 190` indices could reach `errorCap`
under the potential. *Why limited:* positions must index real arrays and are checked against Merkle
paths, so a recognition branch is an *extra* acceptance condition visible in review; and it consumes
all indices, which is anomalous. *Mitigation:* R-O25 disclosure of position use; the potential
prices it at the honest rate so it is not *free*; consider requiring positions to be *used* (each
opened column checked) so a pure-recognition branch cannot ignore the openings.

### 14.5 The liveness mirror through the challenge channel (§11.2)
A `V` that *rejects* honest proofs under BLAKE2s via a challenge-channel condition type-checks and
keeps δ-completeness over random `H`. *Covered by:* the mandatory concrete liveness smoke check,
not by typing. *Attack on the mitigation:* if the smoke check uses a *fixed* benchmark instance set,
a `V` could reject only on instances outside the smoke set but inside the ranked set. *Mitigation:*
run the liveness smoke on the **ranked** instances (fresh starts), i.e. the same instances scored,
so there is no gap between "tested complete" and "scored"; ADV-m1's recommendation, made mandatory.

### 14.6 Review/challenge-period evasion
Since E does not prove (b), review+challenge are load-bearing. A backdoor crafted to look like
ordinary sumcheck (14.1) could survive review, and the challenge period only catches it if someone
*finds and exhibits* a magic proof — which for a challenge-channel backdoor may itself be hard
(the adversary knows the magic proof; the public may not). *This is the irreducible residual:* for
the deepest attacks, E degrades to the same trust model as every deployed SNARK plus an incentive
(public challenge) to find breaks. I state this plainly in §10 rather than claim more.

---
*End of memo. Companion probes (§9.4) not run; recommended before the contract stage lands.*
