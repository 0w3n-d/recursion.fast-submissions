Library: the witness-sending verifier accepts malleated leaf proofs (fails the §6.3 canaries), and the contract's packBytes/bytesAt compile to quadratic code (563 s to reject a 1 MiB proof)

## Summary

Two defects found while certifying the S2a witness-sending baseline against `15e4ae5`. Neither
affects any certificate. Both would fail an entry at the benchmark run. (1)
`Library/WitnessSending.check` does not require the canonical encoding of a leaf proof. A leaf
proof with one byte appended, or with its last byte removed, is accepted. That fails two canaries
of DESIGN-v3 §6.3 step 7 (kernel-checked). (2) The contract's `packBytes` and `bytesAt` compile to
quadratic code. A verifier that decodes through them took 563 s to reject a uniformly random
1 MiB proof, against `verify_s = 60 s`, so it fails the DoS column. The S2a entry has linear-time
twins proved equal, and a strict `check`, that the library can adopt.

## The problem

**(1) Leaf malleability.** `Library/WitnessSending.lean:44` and `:64-72`:

```lean
def decode (π : Proof) : Option Wit := decodeWit (packBytes π.data.toList)
def check (c : Digest) (π : Proof) : Bool :=
  match decode π with
  | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encode (.node c₁ c₂ π₁ π₂) = π then … else false
  | none => false
```

The node branch requires `encode … = π`, but the leaf branch does not. `decodeWit`
(`Extractor.lean:80-89`) reads words 0–5 of a leaf and ignores the rest, and `packBytes` zero-pads
the last word. As a result:

- a 48-byte leaf proof with one byte appended (49 bytes, 7 words) decodes to the same leaf;
- with its last byte removed (47 bytes), it decodes to the same leaf whenever the top byte of the
  length word is zero, which holds for every `n ≤ chainCap`.

§6.3 step 7 requires "the first 8 proofs of each kind must be rejected with one appended byte, with
the last byte removed, …". So the library's `submission` fails the benchmark run, although it is
certified (the extra proofs are valid proofs of true statements).

**(2) Quadratic compiled decoding.** `Extractor.lean:53-54` and `:67-75`:

```lean
def packBytes (b : List UInt8) : List Word :=
  (List.range ((b.length + 7) / 8)).map fun j => toWord (ofLE ((b.drop (8 * j)).take 8))
def wordByte (ws : List Word) (i : ℕ) : UInt8 :=
  ((ws.getD (i / 8) 0).toNat / 256 ^ (i % 8)).toUInt8
def bytesAt (o : List Word) (k n : ℕ) : Proof :=
  ⟨((List.range n).map (wordByte (o.drop k))).toArray⟩
```

Word `j` is computed by `b.drop (8 * j)` on a list, and byte `i` by `List.getD (i / 8)` on a list.
Both are linear per element, so the whole is quadratic in the proof length. These are the right
*specifications*, since they are normative tape and output formats. Any verifier that runs them as
code inherits the cost, and the library's `decode` does.

## Why it matters

- (1) The organiser's reference argument fails the organiser's own benchmark. An entrant who
  reuses the library's `check` fails at intake, after certification. Since
  `Rel S.Vb` is about the submission's own verifier, a strict leaf check also has to be used
  recursively for the children. An entrant therefore cannot wrap the library's `check`: the entrant
  must re-prove soundness and completeness for a strict copy.
- (2) `verify_s = 60 s` covers the root check, the sample checks and the DoS column (§6.6). Any
  entry whose `Vb` decodes a near-`proofCap` proof with the contract's functions fails the DoS
  column, or spends its `T_V` budget on decoding.

## Evidence

**Kernel-checked** in the S2a entry (submissions repository,
`submissions/baseline/BaselineV3Controls.lean`, not yet pushed).
`w₀ := .leaf (dg 1) 16`; `appendByte π b := π.push b`; `dropLast π := ⟨π.data.pop⟩`.

```lean
theorem lib_leaf_appended : decode (appendByte (encode w₀) 0) = some w₀ := by decide +kernel
theorem lib_leaf_truncated : decode (dropLast (encode w₀)) = some w₀ := by decide +kernel
theorem lib_check_appended (c : Digest) :
    WitnessSending.check c (appendByte (encode w₀) 0) = WitnessSending.check c (encode w₀)
theorem lib_check_truncated (c : Digest) :
    WitnessSending.check c (dropLast (encode w₀)) = WitnessSending.check c (encode w₀)
```

`#print axioms` for `lib_check_appended` and `lib_check_truncated`: `[propext, Classical.choice,
Quot.sound]` (`logs/V3-S2/check/axioms.log`, local).

**Measured**, on the development VM: a QEMU virtual CPU, 32 vCPUs, AVX2, no `pclmulqdq`/`gfni`,
**not the reference machine**. A strict `check` over the library's `decode`/`encode`, compiled,
took **563.26 s wall** (128 MB max RSS) to reject a uniformly random `2^20`-byte proof
(`logs/V3-S2/dos-unfiltered/run.log`, with the binary beside it). With the linear-time twins below,
random 1 MiB proofs are rejected in at most 0.25 s, and adversarially shaped 1 MiB proofs in at
most 1.19 s (`logs/V3-S2/check/smoke.log`).

## Proposed fix (library only; no contract change)

1. **Strict leaf branch.** Add `encode (.leaf s n) = π` to the leaf branch of
   `WitnessSending.check` (one line), and adapt `check_sound` and `complete`
   (`Library/WitnessSending.lean:127`, `:175`). Add controls for the
   four canaries, leaf and node, appended and truncated. S2a's
   `leaf_appended_rejected`, `leaf_truncated_rejected`, `node_appended_rejected` and
   `node_truncated_rejected` are ready to port.
2. **Linear-time twins in `Library/Words.lean`.** Add `packFast` (8 bytes at a time), `bytesAtF`
   (through an array), `decodeWitF`, `decodeF` and `encodeF`, with
   `packFast_eq : packFast b = packBytes b`, `bytesAtF_eq`, `decodeWitF_eq`, `decodeF_eq` and
   `encodeF_eq` (S2a `BaselineV3.lean`, the declarations before `check`). The library's `check` then runs them, and a
   `check_eq` restates it with the specification functions for the proofs. The contract's
   definitions stay as they are: they are specifications.
3. Optionally, a remark in the header of `Extractor.lean` that `packBytes`/`bytesAt` are
   specifications and not meant to be executed on proofs.

Cost: library lines only, about 70 code lines for the twins and their equalities in S2a's file,
plus the strict-leaf proofs. The trusted base is
unchanged. Once the library is fixed, the S2a entry could drop its own `check` (S2a RESULT, open
question 1).

## Cross-references

S2a RESULT §4, §6 and open questions 1–2 (submissions repository, `docs/stages/V3-S2a-RESULT.md`);
DESIGN-v3 §6.3 steps 7 and 10, §6.6 (`verify_s`), §7.3; V3-S1-A7, A22 (lenient `decodeWit`);
roadmap #1 (S2 core half).
