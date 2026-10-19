/-
# The linear-time proof decoder (BLUEPRINT-R1 §1.2.1, `Decode.lean`, group A)

Provenance: copied from `submissions/baseline/BaselineV3.lean` (section "Linear-time format
functions, equal to the library's") of the recursion.fast-submissions repository at commit
`91b3a56`; entries do not import each other. Only the namespace changed; the `decodeF_encodeF` and
`decodeF_bad_tag` controls are this module's.

The compiled code of the contract's `packBytes` and `bytesAt` is quadratic in the proof's length,
and the library's `decode` packs the whole proof before it reads the tag (S2a RESULT §6: 563 s to
reject a random 1 MiB proof). The node check runs these equal functions instead, each linear in
the proof it reads; every proof about it rewrites them back to the library's `decode` and
`encode` with `decodeF_eq` and `encodeF_eq`. A whole recursive node check that decodes and
re-encodes each subproof is still `O(|π| · depth)` (S2a RESULT §6).
-/
import RecursionFast.Library.WitnessSending

namespace SpartanChain
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode)

/-- `packBytes`, eight bytes at a time (the contract's `packBytes` re-reads the list from its start
for every word, so its compiled code is quadratic). -/
def packFast : List UInt8 → List Word
  | [] => []
  | b@(_ :: _) => toWord (ofLE (b.take 8)) :: packFast (b.drop 8)
termination_by b => b.length

theorem packFast_eq (b : List UInt8) : packFast b = packBytes b := by
  fun_induction packFast b with
  | case1 => rfl
  | case2 x xs ih =>
    rw [ih, packBytes, packBytes, List.length_drop, List.length_cons,
      show (xs.length + 1 + 7) / 8 = (xs.length + 1 - 8 + 7) / 8 + 1 by omega,
      List.range_succ_eq_map]
    simp [Nat.mul_succ, Nat.add_comm (8 * _) 8, ← List.drop_drop]

/-- `bytesAt`, through an array of the unpacked bytes (`bytesAt` walks the word list per byte). -/
def bytesAtF (o : List Word) (k n : ℕ) : Proof :=
  let a := (wordsBytes (o.drop k)).toArray
  ⟨((List.range n).map fun i => a.getD i 0).toArray⟩

private theorem wordByte_eq (ws : List Word) (i : ℕ) :
    wordByte ws i = (wordsBytes ws).getD i 0 := by
  rw [← wordByte_packBytes, packBytes_wordsBytes]

theorem bytesAtF_eq (o : List Word) (k n : ℕ) : bytesAtF o k n = bytesAt o k n := by
  simp [bytesAtF, bytesAt, wordByte_eq, List.getD_eq_getElem?_getD]

/-- `decodeWit` with `bytesAtF` for `bytesAt`. -/
def decodeWitF : List Word → Option Wit
  | [] => none
  | o@(t :: _) =>
    let w (k : ℕ) := (o.getD k 0).toNat
    let m := (w 9 + 7) / 8
    if t = 0 then some (.leaf (digestAt o 1) (w 5))
    else if t = 1 ∧ w 9 ≤ proofCap ∧ w (10 + m) ≤ proofCap then
      some (.node (digestAt o 1) (digestAt o 5) (bytesAtF o 10 (w 9))
        (bytesAtF o (11 + m) (w (10 + m))))
    else none

theorem decodeWitF_eq (o : List Word) : decodeWitF o = decodeWit o := by
  cases o with
  | nil => rfl
  | cons t r => simp only [decodeWitF, decodeWit, bytesAtF_eq]

/-- The library's `decode`, in linear time (`decodeF_eq`). -/
def decodeF (π : Proof) : Option Wit := decodeWitF (packFast π.data.toList)

theorem decodeF_eq (π : Proof) : decodeF π = decode π := by
  rw [decodeF, decodeWitF_eq, packFast_eq]; rfl

/-- `witWords` with `packFast` for `packBytes`. -/
def witWordsF : Wit → List Word
  | .leaf s n => toWord 0 :: packFast s.toList ++ [toWord n]
  | .node c₁ c₂ π₁ π₂ => toWord 1 :: packFast c₁.toList ++ packFast c₂.toList ++
      (toWord π₁.data.toList.length :: packFast π₁.data.toList) ++
      (toWord π₂.data.toList.length :: packFast π₂.data.toList)

/-- The library's `encode`, in linear time (`encodeF_eq`). -/
def encodeF (w : Wit) : Proof := ⟨(wordsBytes (witWordsF w)).toArray⟩

theorem encodeF_eq (w : Wit) : encodeF w = encode w := by
  cases w <;> simp only [encodeF, witWordsF, encode, witWords, bytesWords, packFast_eq]

/-! ## Controls -/

/-- The linear decoder reads back the linear encoder on every witness that fits the format. -/
theorem decodeF_encodeF (w : Wit) (h : w.Fits) : decodeF (encodeF w) = some w := by
  rw [decodeF_eq, encodeF_eq, decode_encode w h]

/-- An unknown tag word decodes to nothing. -/
theorem decodeF_bad_tag : decodeF ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = none := by
  rw [decodeF_eq]; decide +kernel

end SpartanChain
