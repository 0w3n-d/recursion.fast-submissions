Honest recursion under the v3 caps: proofCap with UD-provable 128 bits and BLAKE2s-only hashing, perfect completeness ∀H (no grinding), preprocessing SNARKs, accumulation

## Summary

Suppose the knowledge-soundness amendment and the extraction rule are settled. Four further
features of the contract still restrict honest recursive designs, and DESIGN-v3 does not say so.
(1) `proofCap = 1 MiB`, a BLAKE2s-only oracle, unique-decoding-provable 128-bit soundness and an
R1CS arithmetisation of BLAKE2s leave only WHIR-class proof sizes for the node circuit, and those
only just (estimate). (2) `Complete` is perfect over **every** oracle function, which forbids
grinding and every challenge-dependent exceptional case. (3) Preprocessing SNARKs, whose
verification key is a hash-derived constant, cannot satisfy `Complete ∀H` within `qV ≤ 2^16`.
(4) Hash-based accumulation (ARC, WARP), named in §1 as a reason for v3, is not expressible.

## The problem

**(1) Proof size versus the provable regime** (F1-4, F1 §5.2). `Relation.lean:41`:
`def proofCap : ℕ := 2 ^ 20`. The oracle is BLAKE2s only (V3-6). V3-5 and the axiom rule admit no
named proximity-gap conjecture, so the provable regime is unique decoding: at most one bit per
query, and at least 128 positions at `ε = 2^-128`. Johnson-regime theorems (BCIKS20, BCHKS25) are
out of reach for a baseline proof. Every Merkle level in the recursion circuit is then a BLAKE2s
compression gadget, about `2^14` R1CS constraints each (estimate). Sizing, from WHIR Table 5 (UD
column) and R7, all estimates:

| PCS (with Spartan) | Proof at `2^24` / `2^28`, 128-bit UD | Fits `proofCap` for the node circuit (`≈ 2^28.3`)? |
|---|---|---|
| WHIR-class | 621 KiB / 770 KiB | yes, barely |
| FRI, arity 8, rate 1/16 | `≈ 1 MiB` / `> 1 MiB` | no |
| Basefold, arity 2 | 7.95 MiB at `2^24` (ZCF24, λ = 100) | no |
| Ligero/Brakedown tensor | `≥ 25 MiB` at `2^27` | no, at any useful size |

With a plonkish/AIR BLAKE2s (`2^10`–`2^11` cells per compression) the node circuit is about `2^24`,
and every row except Ligero fits. The ranked leaf (`n = 2^14` compressions, about `2^28` R1CS
constraints) needs the same room.

**(2) Perfect completeness over every `H`** (`Security.lean:74-76`):

```lean
def Complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true
```

An adversarial `H` defeats any bounded nonce search, and `OProg` is inductive, so unbounded search
is impossible: grinding is out. Every `2^-170`-type edge case must also be handled for every
challenge value: an out-of-domain point that lands in the evaluation domain (DEEP-ALI divides by
`Z_D(z) = 0`), a zero challenge where something is inverted, any rejection sampling. Two design
rows assume a counted form that does not exist. §6.6 has "completeness error `δ` (counted form)
≤ `2^-64`" and §6.7 has "Grinding / proof of work: allowed through the counted completeness form".
The S1 review's m10 asked for both to be marked "after O-23". That is **not applied** in
DESIGN-v3 or in `AGENTS.md` (`AGENTS.md:141`, §4, and `:219`, the §6 caps table).

**(3) Preprocessing** (ADV-M6). A preprocessing SNARK hard-codes a verification key that an
indexer computed with the hash: SPARK's commitment roots in Spartan, Plonkish preprocessed
columns, Marlin's holographic index. Under a random `H` that root has no known opening, so `P`
cannot open it and `Complete` fails. Recomputing the index under `H` inside `V` costs about `2^20`
or more queries, above `qV ≤ 2^16` (`Certificate.lean:69`), and linear time against `T_V`.
Committing it with concrete BLAKE2s under another tag makes binding rest on BLAKE2s collision
resistance, which no counting argument can charge. What remains: transparent, uniform arguments
(AIR/STARK, or uniform R1CS whose matrix MLEs `V` evaluates succinctly).

**(4) Accumulation** (ADV-M8). The node clause `Vb c₁ π₁ = true` (`Relation.lean:89`) demands
**full** verification of each child under BLAKE2s. Three obstacles follow. In PCD from split
accumulation the node proof carries the accumulator witness, which is linear in the step circuit
and above `proofCap`. A decider outside the circuit gives no transfer from the parent's random-`H`
theorem to the child's concrete-BLAKE2s `Vb`. And the child's accumulator witness is not in the
parent's trace, so `E` has no source for a child proof that `Vb` accepts.

## Why it matters

Entrants will design to the design document. With these constraints left implicit, the natural
designs (leanVM-style Poseidon2 Merkle with grinding and a Johnson-regime hypothesis, Spartan with
SPARK, ARC/WARP accumulation) each fail certification, and only after the Lean work is done. The
honest S2b baseline was steered by exactly these points. Its first milestone (F1 R1) is a leaf
SNARK with witness-sending nodes, certified but **unranked** by `proofCap` and `T_V`.

## Evidence

Paper arguments and estimates only (F1 §5.1–§5.2, ADV-M6, ADV-M8). No kernel probe. The sizing
rests on published tables (WHIR Table 5; ZCF24 for Basefold) and on an estimate of BLAKE2s in
R1CS, not on a measured circuit.

## Proposed fixes and decisions

- **(1)**: a user decision among (i) accept that recursion closes only with WHIR-class sizes
  and say so in §6.6; (ii) raise `proofCap` for node proofs; (iii) a hash menu entry with an
  arithmetisation-friendly hash (O-14); (iv) admit a named proximity-gap hypothesis (not under
  V3-5). Interacts with O-18 (a step-count `T_V`).
- **(2)**: land O-23's counted form (`CompleteWithError`, `δ ≤ 2^-64`). Until then, mark §6.6's
  `δ` row and §6.7's grinding row "after O-23", and say in `AGENTS.md` §4 that `V` must accept the
  honest proof for every challenge value.
- **(3)**: an indexer in the submission (ADV-M6): `I : OProg Key`,
  `V : Key → Digest → Proof → OProg Bool`. `KS` counts `I`'s queries in the log, as made honestly
  before the adversary; `Complete` uses `I.run H`; `Vb` uses `I.run blake2sOracle`, computed once
  at badge build and untimed; `qV` excludes `I`'s queries. It costs a handful of trusted lines. It
  also removes the only legitimate reason for `V` to compare an oracle answer with a hard-coded
  32-byte constant, which is the syntactic shape of the O-25 backdoor (see the comment on #4).
- **(4)**: either correct §1 (v3 admits full recursion only, with every intermediate proof
  succinct and fully verifiable) or change the node clause to an accumulation-shaped relation.
  The second is a design change.

## Cross-references

F1-4, F1 §5; ADV-M6, ADV-M8, ADV-m2; V3-S1-m10; DESIGN-v3 §1, §4.3, §6.6, §6.7, §9.4; V3-5, V3-6;
O-14, O-18, O-22, O-23; O-25 (#4).
