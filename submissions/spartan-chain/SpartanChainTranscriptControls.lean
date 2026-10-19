import SpartanChainSoundnessLog
import RecursionFast.Contract.Certificate

/-!
# Controls for the oracle, Merkle and transcript modules (BLUEPRINT-R1 §10.1)

Known answers under the contract's `blake2sOracle` (`H q = BLAKE2s-256(0x52 ‖ q)`), decided by the
kernel. The expected bytes were computed with Python's `hashlib`
(`logs/spartan-chain/oracle-merkle-transcript/kat/transcript_kat.py`, output beside it).

* Transcript: the seed `(s, n, h) = (0..31, 1, 32..63)`, `absorb(root)` with `root = 0xAA × 31`,
  two squeezes (`kat_transcript`); the field challenge of the first squeeze (`kat_chE`) and three
  10-bit indices of the second (`kat_indices`). Negative: one byte of the absorbed root changed
  changes the state (`kat_transcript_root_ne`).
* Merkle: the root of the 2-leaf tree of the columns `0..7`, `8..15` (`kat_merkle_root`); the
  honest opening verifies (`kat_verify`); a changed column byte and a wrong index are rejected
  (`kat_verify_flip`, `kat_verify_index`).
* Log view: a run on the empty log answers nothing (`runLog_empty`). `chE` reads little-endian
  words (`kat_chE`; negative `chE_not_be`).
* `tree_L` (§10.1): on the honest log of a 4-leaf build every column is read (`colL_log4`, an
  L-M2 instance); with one leaf entry removed that column is `none` and the others are still read
  (`colL_log4_missing`).
* `Bad` (§10.1): a two-entry log with a state hit is bad (`bad_stateHit`); a one-entry log is not
  (`not_bad_one`).
* The transcript forest: seed, absorb, squeeze linked by their states form the path `[0, 1, 2]`
  (`pathOf_linked`); a squeeze of a state no entry answers is a path of its own
  (`pathOf_orphan`).
-/

namespace SpartanChain
open RecursionFast Transcript Merkle

namespace TranscriptControls

/-- The KAT statement start `0, 1, …, 31`. -/
def katS : Digest := Vector.ofFn fun i => i.1.toUInt8
/-- The KAT chain end `32, 33, …, 63`. -/
def katH : Digest := Vector.ofFn fun i => (i.1 + 32).toUInt8
/-- The KAT root `0xAA × 31`. -/
def katRoot : Label := Vector.replicate 31 0xAA

/-- Seed, absorb the root, squeeze twice. -/
def katProg (root : Label) : OProg (Digest × Digest) := do
  let st0 ← seed katS 1 katH
  let st1 ← absorb st0 0x01 (bytesOf root)
  let st2 ← squeeze st1
  let st3 ← squeeze st2
  pure (st2, st3)

/-- `st2` of the KAT, from `hashlib`. -/
def katSt2 : Digest :=
  #v[0x6e, 0x4a, 0x6c, 0x9d, 0x7d, 0x99, 0x72, 0xcf, 0x96, 0xe3, 0xa7, 0x52, 0x71, 0xa4, 0x1c, 0x54,
    0xe4, 0x83, 0x72, 0x99, 0xc9, 0x76, 0x4a, 0xe1, 0x65, 0x90, 0x70, 0x82, 0xae, 0x17, 0x21, 0x51]

/-- `st3` of the KAT, from `hashlib`. -/
def katSt3 : Digest :=
  #v[0x1f, 0xac, 0xbc, 0x14, 0xe2, 0xd6, 0x36, 0x69, 0x52, 0xd1, 0x40, 0x5b, 0xfc, 0xa5, 0x5e, 0x10,
    0x84, 0x36, 0x29, 0xd4, 0xef, 0xdb, 0xb0, 0x28, 0x3e, 0xb4, 0x07, 0x83, 0x2e, 0x0e, 0xe0, 0x27]

/-- **Positive**: the transcript under `blake2sOracle` reproduces `hashlib`'s states. -/
theorem kat_transcript : (katProg katRoot).run blake2sOracle = (katSt2, katSt3) := by
  decide +kernel

/-- **Negative**: changing one byte of the absorbed root changes the state. -/
theorem kat_transcript_root_ne :
    ((katProg (katRoot.set 0 0xAB)).run blake2sOracle).1 ≠ katSt2 := by
  decide +kernel

/-- The challenge of `st2`: the three little-endian words of bytes `0..24`. -/
theorem kat_chE : chE katSt2 =
    ⟨⟨0xcf72997d9d6c4a6e⟩, ⟨0x541ca47152a7e396⟩, ⟨0xe14a76c9997283e4⟩⟩ := by
  decide +kernel

/-- Three indices of 10 bits of `st3`, as `hashlib` reads them. -/
theorem kat_indices : indices 10 3 [katSt3] = [31, 811, 331] := by
  decide +kernel

/-- Negative: big-endian words are not the challenge. -/
theorem chE_not_be : chE katSt2 ≠
    ⟨⟨0x6e4a6c9d7d9972cf⟩, ⟨0x96e3a77152a41c54⟩, ⟨0xe4837299c9764ae1⟩⟩ := by
  decide +kernel

/-- The 2-leaf KAT columns. -/
def col0 : ByteArray := ⟨#[0, 1, 2, 3, 4, 5, 6, 7]⟩
/-- The second KAT column. -/
def col1 : ByteArray := ⟨#[8, 9, 10, 11, 12, 13, 14, 15]⟩

/-- The root of the 2-leaf tree, from `hashlib`. -/
def katMerkleRoot : Label :=
  #v[0xf7, 0x6b, 0x86, 0x06, 0x73, 0xce, 0xe5, 0xfe, 0xee, 0x7d, 0x23, 0x98, 0x4c, 0x3c, 0x80, 0xf7,
    0xdc, 0xe1, 0xd5, 0xd7, 0xd3, 0x3a, 0x6c, 0xa4, 0xcd, 0xdf, 0xad, 0x5f, 0x49, 0x6a, 0x8c]

/-- **Positive**: the prover's root under `blake2sOracle` is `hashlib`'s. -/
theorem kat_merkle_root : root ((build #[col0, col1] 1).run blake2sOracle) 1 = katMerkleRoot := by
  decide +kernel

/-- **Positive**: the honest opening of column `1` verifies. -/
theorem kat_verify : (verify katMerkleRoot 1 col1
    (path ((build #[col0, col1] 1).run blake2sOracle) 1 1)).run blake2sOracle = true := by
  decide +kernel

/-- **Negative**: a changed column byte is rejected. -/
theorem kat_verify_flip : (verify katMerkleRoot 1 ⟨#[8, 9, 10, 11, 12, 13, 14, 0]⟩
    (path ((build #[col0, col1] 1).run blake2sOracle) 1 1)).run blake2sOracle = false := by
  decide +kernel

/-- **Negative**: the opening of column `1` at index `0` is rejected. -/
theorem kat_verify_index : (verify katMerkleRoot 0 col1
    (path ((build #[col0, col1] 1).run blake2sOracle) 1 1)).run blake2sOracle = false := by
  decide +kernel

/-- **Negative** (log view): a run on the empty log answers no query. -/
theorem runLog_empty : (OProg.ask ByteArray.empty).runLog [] = none := rfl

/-! ## `tree_L` and `Bad` (§10.1) -/

/-- Four 8-byte columns. -/
def cols4 : Array ByteArray :=
  #[⟨#[0, 1, 2, 3, 4, 5, 6, 7]⟩, ⟨#[8, 9, 10, 11, 12, 13, 14, 15]⟩,
    ⟨#[16, 17, 18, 19, 20, 21, 22, 23]⟩, ⟨#[24, 25, 26, 27, 28, 29, 30, 31]⟩]

/-- The honest log of the 4-leaf build under `blake2sOracle`. -/
def log4 : Log := ((build cols4 2).queries blake2sOracle).map fun q => (q, blake2sOracle q)

/-- The honest root of the 4-leaf tree. -/
def root4 : Label := root ((build cols4 2).run blake2sOracle) 2

/-- **Positive** (L-M2 instance): every column is read off the honest log. -/
theorem colL_log4 : (List.range 4).map (colL log4 8 root4 2) = cols4.toList.map some := by
  decide +kernel

/-- **Negative**: without the leaf entry of column `0`, column `0` is missing and column `1` is
still read. -/
theorem colL_log4_missing :
    colL (log4.filter fun e => e.1 != leafQ cols4[0]) 8 root4 2 0 = none ∧
      colL (log4.filter fun e => e.1 != leafQ cols4[0]) 8 root4 2 1 = some cols4[1] := by
  decide +kernel

/-- **Positive**: a two-entry log whose second answer is the state of the first query is bad
(a state hit). -/
theorem bad_stateHit (x a : Digest) (q : ByteArray) : Bad [(squeezeQ x, a), (q, x)] :=
  Or.inr (Or.inr (Or.inl ⟨0, 1, by omega, by simp, by simp [stateIn_squeezeQ]⟩))

/-- **Negative**: a one-entry log whose answer is not its state is not bad. -/
theorem not_bad_one : ¬ Bad [(squeezeQ katSt2, katSt3)] := by
  rintro (⟨e₁, h₁, e₂, h₂, hne, -⟩ | ⟨i, j, hij, hj, -⟩ | ⟨i, j, hij, hj, hs⟩ | hr)
  · simp only [List.mem_singleton] at h₁ h₂; subst h₁ h₂; exact hne rfl
  · simp at hj; omega
  · simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp only [List.getElem_singleton, stateIn_squeezeQ, Option.some.injEq] at hs
    exact absurd hs (by decide)
  · exact hr (by simp)

/-! ## The transcript forest -/

/-- A constant digest. -/
def dg (k : UInt8) : Digest := Vector.replicate 32 k

/-- Seed, absorb from the seed's answer, squeeze from the absorb's answer. -/
def logLinked : Log :=
  [(seedQ (dg 0) 1 (dg 0), dg 1), (absorbQ (dg 1) 0x01 (bytesOf katRoot), dg 2),
    (squeezeQ (dg 2), dg 3)]

/-- **Positive**: the linked entries form one path. -/
theorem pathOf_linked : SoundnessLog.pathOf logLinked 2 = [0, 1, 2] := by decide +kernel

/-- **Negative**: a squeeze of a state no entry answers has no predecessor. -/
theorem pathOf_orphan :
    SoundnessLog.pathOf [(seedQ (dg 0) 1 (dg 0), dg 1), (squeezeQ (dg 9), dg 3)] 1 = [1] := by
  decide +kernel

end TranscriptControls

end SpartanChain
