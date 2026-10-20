# F2-o25 review: adversarial review of Candidate E (O-25, core issue #4)

## 0. Scope, probes and verdict summary

Reviewed: `docs/snark-baseline/notes/F2-o25-uninstantiability.md` (the memo, all of it, including
§5 and §14), against `.contract/RecursionFast/Controls/Backdoor.lean`, ADV-M5
(`docs/snark-baseline/notes/ADV1-rules-review.md`), issue #4, and the honest entry
`submissions/spartan-chain/` (`SpartanChainTranscript.lean`, `SpartanChainLigero.lean`,
`SpartanChainFieldExt.lean`, `SpartanChainFieldBase.lean`, `SpartanChainSpartanProtocol.lean`).
The reviewer did not write the design.

**Verdict in one paragraph.** Candidate E as written does **not** close the known CGH mechanism.
Its typing closes the mechanism for the `D` (digest) half only. The `F` (challenge) half and the
`ℕ` side channels (`idx`, `leadZeros`) give `V` everything the direct backdoor needs. Two
independent breaks follow:

- **O25-M1:** `idx` is a full byte projection of any `D`. This is kernel-checked: `idxOf 256 a 0 = natLE a`.
- **O25-M2:** `CommRing F` plus `DecidableEq F` plus any prover-supplied `F` value lets `V` name
  *every* element of the deployed finite field `EF`, up to a Galois-conjugacy ambiguity of at most
  192 choices. `V` can then compare a locally computed value with `squeezeF(answer)`.

Neither break needs `evalPoly` or a high degree. So the memo's main hardening lever (a degree cap,
§14.1) does not touch either one. A third break comes from the interface itself:

- **O25-M3:** the honest entry needs `ofBytes : bytes → F` to read its own sumcheck and Ligero
  data. That function is the direct backdoor.

Grinding as specified (**O25-M4**) is either unusable by an honest verifier or is a recognition
site. Repairing all of this requires taking field arithmetic away from `V` (§4). That is a much
larger change than the memo proposes, and it moves the competition toward contract-owned protocol
templates.

**Probes** (all under `/home/devops/Verified-zkEVM/rf-core-sc/scratch/o25/`, each run with
`timeout 900 systemd-run --user --scope -p MemoryMax=8G lake env lean <file>`):

| File | Purpose | Result |
|---|---|---|
| `P1_interface.lean` | Sketches the memo's `ChallengeOps`. Proves `idxOf_full : idxOf 256 a 0 = natLE a` for the wrapper's `idxOf` (copied from spartan-chain). Type-checks the parametric, computable fragments `cmpNat` (compare `idx` output with a `V`-computed `ℕ`), `encodeF` / `cmpF` (build `Σ bitᵢ(n) βⁱ : F` from a `V`-computed `n` and a prover `β`, then compare it with `squeezeF a`) and `pinned` (a GF(2)-coefficient minimal-polynomial check on `β`). | Compiles. `idxOf_full` depends on `[propext, Classical.choice, Quot.sound]` only. `#eval pinned (F := ZMod 7) 2 = true`. |
| `P2_hatches.lean` | Lean-4 escape hatches at abstract `D`: `Classical.dec (D = Digest)`, `toString`, `hash`, `cast`, `Classical.choice`, `default`; and `Nat.cast : ℕ → F` from `CommRing`. | As the memo predicts, every `D`-hatch fails: noncomputable (H1, H6), no instance (H3, H4, H7), type mismatch (H5). `Nat.cast` into `F` compiles (H8). |

So the memo's §5.2 table is **right about `D`**: no Lean-4 hatch found recovers bytes of an
abstract `D` computably. The breaks are not parametricity failures. They are **interface**
failures: the interface hands `V` operations whose outputs are byte-faithful (M1, M3) or
algebraically complete (M2). Parametricity in `F` buys nothing once `F` is instantiated at a
single known finite field. The certificate is about that instantiation only.

The reviewer deliberately did **not** build a full certified BLAKE2s-triggered backdoor
submission. The findings below give the term shapes (kernel-checked as fragments), and the counting
argument for `KS` reuses the shape of `Controls/Backdoor.lean` with a larger `bad` set. This is
enough to show that the type does not exclude it.

## 1. Major findings

Every attack below has the same accounting as `Controls/Backdoor.lean`. There is one rare event,
`bad`, whose set of answers is at most `errorCap · 2^256` in the ROM (counting) or is charged once
to the potential `μ` (amended `KS`). The honest branch is left untouched, so `Complete` holds. The
only thing that changes is how the recognition event is written, so that it fits the
Candidate-E type.

### O25-M1. `idx : D → ℕ → ℕ → ℕ` is a full byte projection; §4.5's bound is wrong

*Attack.* E-3 gives `idx : D → ℕ → ℕ → ℕ`, filled by the wrapper with the honest entry's `idxOf`
(`SpartanChainTranscript.lean:67`): `idxOf ℓ a i := natLE a / 2 ^ (i * ℓ) % 2 ^ ℓ`. The memo (§4.5,
§9.3) reads `ℓ` as a small, honest, *wrapper-fixed* width (`ℓ ≤ 23`) and concludes each call leaks
`ℓ` bits, recognising "at only `2^-ℓ`". But `ℓ` is `V`'s own argument. `V` calls `idx a 256 0`.
Probe `P1_interface.lean` proves, kernel-checked (axioms `propext, Classical.choice, Quot.sound`):

```lean
theorem idxOf_full (a : Digest) : idxOf 256 a 0 = natLE a
```

`natLE a` is the whole 32-byte answer as a natural (spartan-chain's own `natEquiv : Digest ≃ Fin 2^256`).
So `idx` is a complete, byte-faithful, computable projection `D → ℕ`, and `ℕ` has `DecidableEq` and
every literal. The backdoor is one line inside the typed interface, no `Digest` constant named:

```lean
def cmpNat {D F : Type} (ops : ChallengeOps D F) (a : D) (loc : ℕ) : Bool :=
  decide (ops.idx a 256 0 = loc)        -- compiles; parametric in D and F
```

`loc` is `natLE (blake2sOracle q0)`, a `V`-computable literal (BLAKE2s is public), exactly
`Controls/Backdoor.lean`'s `trigger` with the byte compare replaced by `idx`'s `ℕ`. The `KState` is
Backdoor's (`good`/`bad` on query `q0`), so `KS` holds at `errorCap`; the honest branch is
untouched, so `Complete` holds; the gate sees a literal type match and computable `Vb`. Accepted.

*What it breaks.* Everything — M1 alone defeats Candidate E. Even restricting to the honest width
`ℓ`, `⌈256/ℓ⌉` calls on **one** answer (`idx a ℓ 0, idx a ℓ 1, …`) return every bit (probe
`idxOf_all_bits`), so all bits come from a single answer and the "spread over `t ≈ 190` indices,
priced by the potential" argument (§4.5) collapses: one answer, charged once.

*Smallest fix.* `idx` must return an **opaque position token** (a second abstract type with only
`DecidableEq` and a `Fin`-bounded `toNat` used *only* by the trusted array-indexing wrapper, never
exposed to `V`), and the width must be a contract constant per step, not a `V` argument. Even then
positions must index arrays and the opened value compared, so the channel is narrow but non-zero.

### O25-M2. `CommRing F` + `DecidableEq F` names every element of `EF` (Galois ambiguity ≤ 192)

*Attack.* §4.3–§4.4 claim the only `F`-values `V` can build are `const 0/1`, sums/products, and
`squeezeF` outputs, so `V` cannot name `chE(localBlake2s q)`. False for the deployed field.
`F := EF = GF(2^64)^3 = GF(2^192)` is one specific finite field, fixed by the certificate. Three
constructions, none using a forbidden op:

1. **Any prover `F`-value generates the field.** The proof carries `F`-values (sumcheck messages,
   claimed evaluations). Let `β` be one, or `β := squeezeF slot` for a proof digest `slot`. For a
   `1 - 2^-96` fraction of elements, `{1, β, …, β¹⁹¹}` is an `F_2`-basis of `EF`, so **every** target
   `τ ∈ EF` — including `chE(localBlake2s q)` — is `Σ_{i<192} bᵢ βⁱ`, bits `bᵢ` computed by `V` from
   BLAKE2s. Probe `P1_interface.lean`'s `encodeF`/`cmpF` build `Σ bitᵢ(n) βⁱ` (with `n` a
   `V`-computed `ℕ`) and compare it with `squeezeF a` via `DecidableEq F`. They type-check and are
   computable. Degree-0 in the challenge; `evalPoly` not used.

2. **Minimal-polynomial pinning needs no local bits.** To test a prover `β` against a fixed target
   `τ`, check `m(β) = 0` for `τ`'s minimal polynomial `m` over `F_2` — coefficients in `{0,1}`,
   built from `const 0/1` and `+/*`, all permitted. Probe `pinned` shows the shape
   (`β²+β+1 = 0`, `#eval pinned (ZMod 7) 2 = true`). Recognition fires at rate ≤ `192/2^192` (the
   Galois conjugates of `τ`), trivially certifiable.

3. `Nat.cast` (free with `CommRing`, probe H8) gives only `0,1` here (char 2) — the memo is right
   on that one point and wrong on the conclusion it draws from it.

*What it breaks.* The whole "restricted algebraic interface", the load-bearing new idea of E. The
memo confines the residual to high-degree `evalPoly` (§14.1) and proposes a degree cap; M2 is
degree ≤ 2 (pinning) or a *fixed linear* combination of precomputed powers (basis expansion), so a
degree cap does nothing. Root cause: parametricity over `F` is worthless once `F` is a single known
finite field with `DecidableEq` — a finite field is generated by one element and `CommRing` supplies
the generation, `DecidableEq` the recognizer.

*Smallest fix.* None that is small. Deny `V` field arithmetic on prover values and `DecidableEq F`
against non-contract values: the sumcheck identity check becomes a contract-owned operation
`checkStep : … → Bool` that `V` only invokes with opaque handles. That removes `[CommRing F]` from
`V`'s signature and makes the challenge algebra a fixed contract template (see §4).

### O25-M3. The honest entry needs `ofBytes : bytes → F`, which is the backdoor

*Attack.* E's premise is that `V` touches answer bytes only through `squeezeF`/`idx`. But the honest
verifier decodes **proof** bytes into `F` throughout its non-oracle path: `SpartanChainLigero.lean:179`
`readEF b o := EF.ofBytes (… b[o+i]! …)` and `:186` `readF` read the prover's sumcheck messages and
Ligero columns; `EF.ofBytes` is a bijection `Vector UInt8 24 ≃ EF` (`ofBytes_bijective`,
`SpartanChainTranscript.lean:174`). So a byte→field map must be in `V`'s scope. Expose it for proof
bytes and `V` applies the *same* map to locally computed BLAKE2s bytes:
`ofBytes(localBlake2s q [0:24]) = chE(…)` — the memo's own §1 attack. §12.1's "chE and idxOf are the
only consumers of answer bytes" is true only for *oracle-answer* bytes; `readEF`/`readF` are a
separate, unavoidable proof-byte→`F` channel the memo never reconciles with §4's interface.

*What it breaks.* Migratability. Either (a) expose `ofBytes` (reopens the direct backdoor), or (b)
move all proof-field decoding into the trusted wrapper so `V` gets opaque `F` handles — which makes
the wrapper parse the whole Spartan/Ligero proof, i.e. protocol-specific trusted code, not a 30-line
generic serialiser. §9.1's size estimate and §12's "mostly mechanical" are wrong on this path.

*Smallest fix.* `Tape D` must carry prover field elements as **opaque `F` slots**, the trusted
serialiser doing `ofBytes` once at parse time and never exposing bytes or `ofBytes`. With M2's
removal of `CommRing F`, the proof becomes a structured list of opaque `D`/`F` tokens and `V` runs a
fixed contract protocol over them — Candidate E in name only.

### O25-M4. Grinding (`leadZeros : D → ℕ`) is redundant for the attacker or a channel

*Attack.* §11.1 adds `leadZeros : D → ℕ` and argues the *threshold test* `leadZeros a ≥ g` is
oracle-agnostic. But it exposes the `ℕ` *value*, and with M1 `idx a 256 0` is already the full byte
projection, so §11.1's own open question ("no composite of `leadZeros`+`idx`+`evalPoly` reconstructs
a byte projection") is settled against the memo. Separately, grinding is incoherent as specified: if
the threshold `g` comes "from the proof", a magic proof supplies `g := 0` and grinding adds no
soundness (vacuous for the attacker); if `g` is a contract constant, the honest prover must
rejection-sample in `P`, so `leadZeros` need not be in `V`'s interface at all.

*What it breaks.* Not soundness beyond M1/M2, but it shows the grinding channel is pure added attack
surface.

*Smallest fix.* Do not expose `leadZeros` to `V`. Make grinding a wrapper-enforced precondition: the
trusted wrapper checks `leadZeros(answer) ≥ g_contract` before `V` runs and rejects otherwise; the
honest prover rejection-samples in `P`.

### O25-M5. `evalPoly` with proof coefficients is Turing-rich (confirms §14.1, raises severity)

*Attack.* Even with M1–M4 all fixed, `evalPoly : List F → F → F` with prover-supplied coefficients
lets `V` evaluate a prover polynomial `p` at a challenge and accept on `p(squeezeF a) = 0`. An
adversary sets the roots of `p` to the challenge values BLAKE2s produces on a magic transcript. The
memo flags this (§14.1) but rates it ~50% "review would plausibly miss" and proposes a degree cap.
Two points raise it to major: (i) M2 shows pinning already works at degree 2, so the "honest degree
≤ 3" cap does **not** separate honest from malicious — the malicious polynomial is *also* low
degree; (ii) a degree cap bounds the number of roots but the adversary needs only *one* root (the
single magic challenge value), so a degree-1 `p(x) = x - τ` with `τ` from the proof already
recognises, and `x - τ` is exactly what an honest linear sumcheck step looks like. The degree cap is
not a mitigation against single-target recognition.

*What it breaks.* The memo's sole proposed hardening of the challenge channel. Confirms that the
challenge algebra cannot be made safe by bounding degree.

*Smallest fix.* As M2: remove general `evalPoly`/`CommRing` from `V`; the sumcheck step must be a
contract-owned check, with `V` supplying only the opaque claimed values and the contract performing
the identity test. There is no fix that keeps `V`-authored field arithmetic.

### O25-M6. The liveness mirror is not covered on the instances that matter

*Attack.* §11.2 concedes the liveness mirror (reject honest proofs under BLAKE2s, stay δ-complete
over random `H`) and leans entirely on the concrete smoke check. §14.5 notes the smoke-set/ranked-set
gap and recommends running the smoke on the ranked instances. Two gaps remain. (i) The smoke check
only covers the acceptance *the harness can reproduce with the native prover*; a `V` that rejects
only on a sub-instance the native prover does not emit (e.g. a specific recursion depth or a specific
statement sub-structure reachable only mid-chain) evades it. (ii) The memo does not say **who picks
the ranked instances and when**. If the instance set is public and fixed before submission, the
adversary tunes the rejection to fire only off-set; if it is sampled after freeze, that sampling is a
new trusted component the memo does not specify. The liveness mirror is a griefing attack (sabotage a
competitor sharing a library), so the payoff is real under the ranked-board design.

*What it breaks.* The claim (§11.2, §14.5) that the smoke check covers the liveness mirror. It covers
it only for behaviours the native prover exercises on the tested instances.

*Smallest fix.* (a) Make the ranked instance set **sampled fresh after entries are frozen**, from a
public beacon, by the harness — and state this as trusted process. (b) Run the liveness smoke on
*every* instance scored, on the native prover's real emitted query log (ADV-m1, made mandatory). (c)
Accept that a `V` rejecting on an un-exercised sub-instance is residual and shared with every
deployed SNARK's "it worked on the test vectors" assurance.

## 2. Minor findings

### O25-m1. §5.2 table is sound for `D` — the probes confirm, not refute, this half
Probe `P2_hatches.lean` confirms every `D`-side escape hatch the memo lists is closed in Lean v4.34.1:
`Classical.dec (D = Digest)` and `Classical.choice` are rejected by the code generator (noncomputable,
caught by the `Vb`-computable gate); `toString`/`hash`/`default` fail instance synthesis at abstract
`D`; `cast rfl : D → Digest` is a type mismatch. This is a genuine strength of E and should be kept.
The finding is that the memo's confidence is misplaced about *where* the strength lies: it is in the
`D` type, not in the scheme as a whole, and the `F`/`ℕ`/byte channels (M1–M3) bypass it entirely.

### O25-m2. Missing citation: Brzuska–Hubáček–Kalsta, "Simple Attacks against (Extended) Fiat–Shamir", PKC 2026
The literature list (`/tmp/cgh98_snark_followups.md`, §1) includes this paper; the memo's §13 does
**not** discuss it. It matters because §13.2 promotes Arnon–Yogev XFS as "the most promising research
lead" for strengthening the challenge channel via a proof-of-work, and BHK26 gives *simpler*
counterexamples to **extended** Fiat–Shamir specifically — i.e. it attacks the XFS family the memo
leans on. The memo should temper §13.2: XFS is not a clean escape; its extended variant has fresh
attacks. (Not fetched online; flagged from the list's own description.)

### O25-m3. `DecidableEq EF` is implemented via `BEq` and is not obviously lawful
`SpartanChainFieldExt.lean:35` gives `BEq EF` componentwise and the entry relies on `DecidableEq`/`BEq`
agreement. Candidate E's whole argument rests on `DecidableEq F` comparing only "interface-produced
values". If the gate is to forbid `V` from comparing against `V`-constructed constants (R-O25), it
must distinguish an interface-produced `F` from a `V`-constructed one — but at the type level both
are just `F`, and `DecidableEq F` cannot tell them apart. So R-O25's `F`-clause is **not
mechanically checkable**; it is a review-only rule. The memo treats R-O25 as if typing enforced it
(§9.3 table rows). It does not: M2 is a direct witness.

### O25-m4. The serialiser-injectivity controls (E-7) are necessary but do not touch M1–M3
§5.2's "ambiguous serialisation" row and the E-7 lemmas (`serialise_injective`, `serialise_inl_ne_inr`,
`parse_serialise`) guard the `D` byte/slot boundary. All three of M1, M2, M3 operate *after* a correct
parse, through `idx`/`CommRing`/`ofBytes`, so E-7 — even if fully proved — does not close them. The
memo's §9.3 lists E-7 against "ambiguous serialisation byte-test" only; correct, but it should not be
read as general protection.

## 3. Honest-entry cost (spartan-chain)

The memo's §12 says the migration touches ~1–2k lines of Merkle/transcript/KS glue and is "mostly
mechanical". The findings change this materially.

- **Merkle half (R1, equality-only): genuinely portable.** `SpartanChainMerkle` compares labels for
  equality (`labelsIn`, `verify`, `open_binding_prefix`). This is the part E is designed for and it
  does port, at the cost of an opaque-label type (§3.3). Agreed with the memo.
- **`trunc` (31-byte label).** `trunc : Digest → Label` is a byte projection; must become a
  `DigestOps` op returning an opaque label type. Mechanical but it is trusted plumbing, and it must
  *not* also be exposable as `ℕ`/bytes (or it is M1 again).
- **Transcript field challenges.** `chE`/`idxOf` move to `ChallengeOps`. But the fiber-count lemmas
  `card_chE_fiber` (`:183`), `card_idx_fiber` are proved about `chE`/`idxOf` as *concrete* functions
  (via `ofBytes_bijective`). Under E they become *hypotheses the wrapper asserts* about `squeezeF`/`idx`.
  The KS soundness proof (`SpartanChainSoundnessKS*`, 26 byte-use sites) consumes them as hypotheses —
  this re-parameterisation is real work but is the memo's honest estimate, and I agree it is feasible
  *for the soundness proof*.
- **Proof-field decode (M3): the blocker.** `readEF`/`readF` (`SpartanChainLigero.lean`,
  `SpartanChainSpartanProtocol.lean:379`) decode the prover's field data from proof bytes. There are
  decode/field-use sites across `SpartanChainLigero` (5), `SpartanChainSpartanProtocol` (10),
  `SpartanChainSoundnessPCS` (17), `SpartanChainSoundnessChain` (26). Under a safe interface these all
  move behind the trusted wrapper as opaque-`F`-slot parsing, i.e. the wrapper gains Spartan-specific
  structure. This is **not** in §12's line count and is the dominant cost. It also undermines §9.1's
  "generic 30–45 line wrapper": the wrapper must know the proof layout.
- **Field arithmetic in `V` (M2/M5): must be removed.** The sumcheck/PCS identity checks that §12.1
  calls "exactly the allowed algebraic interface" are precisely the `CommRing F` arithmetic M2/M5
  break. Making them contract-owned `checkStep` operations is a redesign of the verifier's core, not a
  refactor. The honest `V` becomes a thin driver over contract protocol steps.

Net: the Merkle/transcript/KS-soundness migration is feasible as the memo says; the **proof-field and
challenge-algebra** migration (M2/M3/M5) is a redesign that pushes Spartan's protocol logic into the
trusted base. §12.4's "adopt E now and migrate" decision should be made with that larger cost visible.

## 4. Verdict, repair, and residual

**Does Candidate E as written close the known CGH mechanism? No.** It closes it for the `D`/digest
half (M1-m1 confirms the parametricity story holds there), but the direct CGH mechanism — `V`
evaluates the instantiation locally and compares with an oracle-derived value — survives through
three independent channels the type does not restrict: the `ℕ`-valued `idx` (M1, kernel-checked
byte projection), the `CommRing F`/`DecidableEq F` field algebra (M2, every field element nameable),
and the unavoidable proof-byte `ofBytes` decoder (M3). Each reproduces `Controls/Backdoor.lean` with
the same `KS`/`Complete` accounting, inside the Candidate-E type, past the gate. The memo's
headline — "the known CGH mechanism is excluded by construction for the commitment/Merkle part and
for equality-only use of answers" (§0, §10.1) — is **correct as stated but far narrower than the
scheme's actual coverage needs**: the moment `V` does anything beyond digest equality (and every
SNARK verifier must), the mechanism returns, not merely the "deeper FS-uninstantiability residual"
of §10.2 but the *literal one-line backdoor* of §1.2.

**What a repaired version needs.** The repair is forced by M1–M3/M5 to be the same thing each time:
*`V` must not compute on field or numeric representations of answers/proof data at all.* Concretely:

1. `idx`/positions return opaque tokens, widths are contract constants (fix M1).
2. `V`'s signature loses `[CommRing F]`; field elements are opaque handles; every arithmetic/identity
   check (sumcheck step, PCS opening, Ligero proximity) is a **contract-owned operation** that `V`
   invokes, not Lean arithmetic `V` authors (fix M2, M5).
3. Proof field data enters as opaque `F`-slots parsed by the trusted wrapper; `ofBytes` is never
   exposed (fix M3).
4. `leadZeros`/grinding is a wrapper precondition, not a `V` op (fix M4).
5. The ranked instance set is sampled post-freeze from a beacon and the liveness smoke runs on all of
   it (fix M6).

This is not "Candidate E + a degree cap". It is a **contract-owned protocol template**: the trusted
base contains the Spartan/Ligero verifier skeleton, and an "entry" supplies only the opaque data
plumbing and the soundness certificate. That is a coherent and defensible design — it is essentially
what makes the recognition channel provably absent — but it is a different competition from "submit
your own `V`", and the user/orchestrator should see it as such. The memo's "+30–45 trusted lines"
becomes "+the verifier core in the trusted base".

**Is any residual provably unavoidable?** Yes, and the memo's §10.2 is correct about it: even the
fully contract-owned template above cannot achieve "ROM-secure ⇒ BLAKE2s-secure". Goldwasser–Kalai
(FOCS'03), Bartusek–Bronfman–Holmgren–Ma–Rothblum (TCC'19, the Kilian/Micali template this contract
*is*), Khovratovich–Rothblum–Soukhanov (CRYPTO'25), and Fenzi (2026/1838, Spartan/Aurora specifically)
construct arguments that are ROM-sound and FS-unsound for every concrete hash. If the contract-owned
template is expressive enough to run Spartan, it is expressive enough to run a Fenzi-style unsound
variant, and no ROM theorem can tell them apart. So the *irreducible* residual is exactly the
FS/BLAKE2s heuristic every deployed SNARK assumes — the memo's honest floor. The actionable positive
lever the literature gives for *this* family is Fenzi26's fix: bind every FS challenge to the
*generated statement* digest (spartan-chain already seeds its transcript with `c = leafStmt h n`);
this should be a hard **rule**, not optional defence-in-depth. XFS (Arnon–Yogev) is weakened as a lead
by BHK26 (O25-m2).

**How hard is it for a clever adversary to get around the *repaired* (contract-owned-template)
scheme?** Once M1–M5 are fixed as above, the free, one-line, review-invisible backdoor is gone: the
adversary can no longer author a recognizer because it authors no field/numeric computation on
answers. To win board T it must embed a genuine FS-uninstantiability construction (KRS25/Fenzi26
grade) *inside the fixed protocol template's degrees of freedom* — the prover-chosen polynomials and
openings — and still produce a valid `KS` certificate. That is research-paper effort, is visible as
anomalous proof data to review, is defeated for the known Spartan/Aurora attack by mandatory
statement-binding (Fenzi26), and is exhibitable in the public challenge period. My estimate: with the
contract-owned template **and** statement-binding **and** post-freeze ranked instances, a clever
adversary's cheapest path is a Fenzi-class attack adapted around statement-binding — plausible for a
determined researcher, unattractive under the incentive/challenge structure, and no worse than the
standing assumption of every fielded SNARK. With Candidate E *as written in the memo*, by contrast,
the adversary's cost is **one line** (M1/M2/M3) and the scheme provides essentially no protection
beyond the `D`-equality half. The gap between those two is the whole finding of this review: the memo
describes the repaired scheme's security but specifies the unrepaired one.

---
*Probes: `/home/devops/Verified-zkEVM/rf-core-sc/scratch/o25/P1_interface.lean`,
`P2_hatches.lean`. Both compile under Lean v4.34.1; `idxOf_full` is kernel-checked with axioms
`propext, Classical.choice, Quot.sound`. No files edited outside this review and the two probes;
no commits.*
