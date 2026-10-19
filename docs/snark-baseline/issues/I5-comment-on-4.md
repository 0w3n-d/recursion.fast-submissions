Comment on #4 (O-25): backdoor variants that evade the proposed defences, and why the parametric-`V` fix cannot support Fiat–Shamir

## Summary

An independent review (ADV1, finding ADV-M5) tested the O-25 defences against the pin `15e4ae5`.
(1) A literal 32-byte trigger is kernel-checked to give the same certified backdoor. Its constant
closure contains neither `blake2sOracle`, `tagRO` nor `Submission.Vb`, and its remaining BLAKE2s
footprint is identical to the honest witness-sending `V`'s. (2) A "trace-check" trigger evaluates
no hash at all. (3) The rule of §6.7 also bans designs §6.7 allows. (4) The parametric-digest fix of
§2 above cannot support Fiat–Shamir: any oracle answer whose bits `V` can read is an answer `V` can
compare with a locally computed BLAKE2s value. (5) `AGENTS.md` does not state the rule. These are
additions to this issue, not a separate one.

## 1. A literal trigger evades the closure test (kernel-checked)

The S1 review's proposed gate speed bump rejects a `V` whose constant closure contains
`blake2sOracle`, `Submission.Vb` or `tagRO`, and flags `Blake2s.compress`. The probe
`logs/adv-probes/LiteralTrigger.lean` (submissions repository, local log) replaces
`trigger := blake2sOracle q0` in `Controls/Backdoor.lean` with a literal computed offline
(`hashlib.blake2s(b'R')`):

```lean
def lit : Digest := Vector.ofFn fun i => (#[29, 86, 144, 164, …, 168, 33, 116, 127] : Array UInt8)[i]!
theorem lit_eq : trigger = lit := by decide +kernel
def Vlit (c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = lit) && decide (π = magic c)) || check c π)
theorem Vlit_eq : Vlit = Controls.Backdoor.V
theorem backdoor_lit :
    Certificate Slit ∧ ∀ c, Slit.Vb c (magic c) = true ∧ (magic c).size = 32
-- #print axioms backdoor_lit: [propext, Classical.choice, Quot.sound]
```

Closure scan (`LiteralTrigger.log`):

| `V` | `blake2sOracle` | `tagRO` | `Submission.Vb` | `blake2s256` | `Blake2s.compress` |
|---|---|---|---|---|---|
| `Vlit` (backdoor) | no | no | no | yes | yes |
| `WitnessSending.V` (honest) | no | no | no | yes | yes |
| `Controls.Backdoor.V` | yes | yes | no | yes | yes |

The remaining signal does not separate the backdoor from the honest baseline: both reach
`blake2s256` through `Rel`'s chain check. The only visible trace is "an oracle answer is compared
with a 32-byte constant". An honest preprocessing verifier does the same with its
verification-key root (see the honest-recursion issue, ADV-M6), so a syntactic rule cannot ban one
without the other.

## 2. A trace-check trigger (paper)

`V` legitimately contains the constraint evaluator of its own circuit, including the in-circuit
`BLAKE2s(tagRO ‖ ·)` gadget it uses for Merkle hashing. Add a "debug mode" branch that checks a
proof-supplied concrete trace of that gadget, whose output equals the oracle's answer to `q = c`.
That branch recognises the instantiation while `V` evaluates no hash; it only checks constraints.
The bad set is one answer per query, so it is certified at `errorCap`. Canaries pass, because the
magic proof is bound to `c`. Each magic proof costs the prover one BLAKE2s trace.

## 3. The rule is over-broad

The rule says "`V`'s local computation must not evaluate the oracle's instantiation" (§6.7). It
bans three things the design wants or tolerates:

- a concatenation node, which §6.7 allows and which verifies child SNARKs locally, so it evaluates
  `BLAKE2s(tagRO ‖ ·)` inside `V`;
- a hard-coded verification key;
- a "consistency fast path" that skips re-verification when the oracle agrees with a locally
  computed transcript. This is a natural optimisation, and it is exactly the backdoor.

## 4. The parametric-`V` candidate fix (§2 of this issue)

`V : ∀ (D : Type) [DecidableEq D], D → Tape D → OProg D Bool` lets `V` act on answers only
through equality.

- **If answers stay opaque**, `V`'s decisions depend on answers only through equality patterns.
  For a random oracle these are "all distinct" with overwhelming probability, so no Fiat–Shamir
  challenge (a field element, a position) can be derived. §7 of this issue already concedes that
  "unpacking a digest into field elements inside `V`" is impossible at `D`. That is exactly what
  every Fiat–Shamir verifier does with its challenges, not only in-circuit verifiers.
- **If the contract adds a challenge interface** that yields `b` bits per answer (any
  `D → Fin (2^b)`, or a separate "challenge query" answered in bytes), then `V` can compare those
  `b` bits with `b` bits of a locally computed BLAKE2s, and recognition has error `2^-b`. Under the
  current counting form a challenge must carry its soundness in one answer, which needs `b ≥ 128`,
  and that certifies recognition at `errorCap`. Under the potential `μ` proposed in the KS issue,
  a recognition spread over `k` answers of `b` bits each is priced at `2^-bk`, exactly like a
  spread challenge. The tension is therefore information-theoretic and does not depend on the
  counting form.
- Keying or salting does not help. The S1 review's two-query argument ("Why no salting fixes it",
  V3-S1-M1) still holds when the key is read from the proof.

Parametricity can protect **commitment** answers (roots compared only with other answers). It
cannot protect **challenge** answers, and every succinct hash-based `V` needs challenge answers.

## 5. The rulebook does not state the rule

`AGENTS.md` at the pin says nothing about oracle recognition: grep for "O-25", "recogni" and
"magic" finds no hits. The S1 review calls intake review "the binding defence".

## Recommendations (ADV1)

- State the rule in `AGENTS.md`, **semantically**, together with the disqualification. A
  wording for discussion: "no branch of `V` may accept because an oracle answer agrees with a
  value that `V` did not obtain from the oracle or from the proof".
- Require the entry's `NOTES.md` to list every place where `V` compares an oracle answer with
  anything other than another oracle answer, or with a proof-supplied value that the oracle
  subsequently hashes.
- Make intake review (S7) mandatory, with a public challenge period before a record stands.
- Drop the parametric-`D` candidate from O-25, or narrow it to commitment answers and say what
  it does not cover.
- Adopt the indexer of ADV-M6 (honest-recursion issue). It removes the one legitimate reason for a
  hard-coded 32-byte constant compared with an oracle answer, and that makes review sharper.

Cross-references: ADV-M5 (items 1–5), ADV-M6; V3-S1-M1; DESIGN-v3 §5.4, §6.7, §12 O-25;
`Controls/Backdoor.lean`; KS issue (potential `μ`), honest-recursion issue (indexer).
