/-
# The witness-sending baseline (DESIGN-v3 §7.3, V3-9; stage S2)

The proof is the witness: the verifier decodes it and decides the relation directly, with no
oracle query; the prover sends the witness; the extractor reads it back off the proof.

**What is the core library's and what is this entry's.** The proof format (`encode`, `decode`),
the prover `P`, the extractor `E`, the 8-instruction image `img` (`proofwords.S`) and its proof
`computes` are the organiser library's, `RecursionFast.Library.WitnessSending`, imported as they
are. This module adds two things:
* **A strict verifier.** The library's `check` accepts a leaf proof whenever its packed words
  decode to a leaf witness of the statement, and `decodeWit` ignores the words after a leaf's
  sixth, so it accepts a leaf proof with one byte appended, and with its last byte removed (the
  top byte of the length word, zero for every length up to `chainCap`)
  (`BaselineV3Controls.lib_check_appended`, `lib_check_truncated`). The benchmark's canaries
  reject an entry for that (DESIGN-v3 §6.3 step 7). Here every proof, leaf or node, must be the
  canonical encoding of the witness it decodes to (`check_canonical`). The relation is about the
  instantiated verifier (`Rel submission.Vb`), so the strictness is recursive: a node's children
  are checked by this `check`, and the soundness and completeness proofs are this module's.
* **Linear-time decoding.** The verifier runs `decodeF` and `encodeF`, proved equal to the
  library's `decode` and `encode` (`decodeF_eq`, `encodeF_eq`), whose compiled code is quadratic in
  the proof's length; `check_eq` states `check` with the library's functions.

The certificate (`certificate`) is knowledge soundness at error `0` with no verifier query
(`good := True`, `bad := False`), perfect completeness, the library's image theorem and the caps.
-/
import RecursionFast.Library.WitnessSending

namespace BaselineV3
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

/-! ## Linear-time format functions, equal to the library's

The compiled code of the contract's `packBytes` and `bytesAt` is quadratic in the proof's length,
and `decode` packs the whole proof before it reads the tag. The verifier runs these equal
functions instead; every proof below rewrites them back to the library's. -/

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

/-! ## The verifier -/

/-- **The strict witness-sending decision**: `π` is the canonical encoding of a leaf witness of `c`
(its length within `chainCap`, checked before any hash), or of a node witness of `c` whose two
children (each at most `proofCap` bytes) are accepted, recursively. -/
def check (c : Digest) (π : Proof) : Bool :=
  match decodeF π with
  | some (.leaf s n) =>
    decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
      decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encodeF (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
        (decide (π₂.size ≤ proofCap) && check c₂ π₂)
    else false
  | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, encodeF_eq, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- The verifier: `check`, with no oracle query. -/
def V (c : Digest) (π : Proof) : OProg Bool := .ret (check c π)

/-- **The baseline submission**: the strict verifier, and the library's prover, extractor, image
and fuel (8 steps); error `0`, no verifier query. -/
def submission : Submission where
  V := V
  P := WitnessSending.P
  E := WitnessSending.E
  img := WitnessSending.img
  ε := 0
  qV := 0
  fuel := WitnessSending.fuel

/-! ## The instantiated verifier -/

theorem Vb_eq (c : Digest) (π : Proof) :
    submission.Vb c π = (decide (π.size ≤ proofCap) && check c π) := by
  simp [Submission.Vb, submission, V, OProg.run]

theorem size_le_of_Vb {c : Digest} {π : Proof} (h : submission.Vb c π = true) :
    π.size ≤ proofCap := by
  rw [Vb_eq, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

/-- `check`, with the library's `decode` and `encode`. -/
theorem check_eq (c : Digest) (π : Proof) : check c π =
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ π₁ π₂) =>
      if encode (.node c₁ c₂ π₁ π₂) = π then
        decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
          (decide (π₂.size ≤ proofCap) && check c₂ π₂)
      else false
    | none => false := by
  rw [check, decodeF_eq]
  simp only [encodeF_eq, dite_eq_ite]

/-- **Strictness**: an accepted proof is the canonical encoding of the witness it decodes to. -/
theorem check_canonical {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ encode w = π := by
  rw [check_eq] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, hd, h.1.1⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · exact ⟨_, hd, ‹_›⟩
    · cases h
  · cases h

/-- **Soundness of the decision**: an accepted proof decodes to a witness of the relation of the
instantiated verifier. -/
theorem check_sound {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ Rel submission.Vb c w := by
  rw [check_eq] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.leaf s n, hd, h.1.2, h.2⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, ?_, ?_⟩ <;> rw [Vb_eq] <;> simp [h]
    · cases h
  · cases h

/-- Every witness of the relation fits the format. -/
theorem fits_of_rel {c : Digest} {w : Wit} (h : Rel submission.Vb c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ π₁ π₂ => exact ⟨size_le_of_Vb h.2.1, size_le_of_Vb h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted.** -/
theorem check_encode {c : Digest} {w : Wit} (hR : Rel submission.Vb c w) :
    check c (encode w) = true := by
  rw [check_eq, decode_encode w (fits_of_rel hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    rw [Vb_eq] at h₁ h₂
    simp_all

/-- **What the verifier decides**: a proof is accepted exactly when it is within `proofCap` and is
the canonical encoding of a witness of the relation that it decodes to. -/
theorem Vb_iff (c : Digest) (π : Proof) : submission.Vb c π = true ↔
    π.size ≤ proofCap ∧ ∃ w, decode π = some w ∧ encode w = π ∧ Rel submission.Vb c w := by
  rw [Vb_eq, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun ⟨hs, h⟩ => ⟨hs, ?_⟩, fun ⟨hs, w, _, he, hR⟩ => ⟨hs, he ▸ check_encode hR⟩⟩
  obtain ⟨w, hd, he⟩ := check_canonical h
  obtain ⟨w', hd', hR⟩ := check_sound h
  rw [hd] at hd'; cases hd'
  exact ⟨w, hd, he, hR⟩

/-! ## The certificate -/

/-- The knowledge state: every log is good, no answer is bad. -/
def kstate : KState (Rel submission.Vb) V WitnessSending.E where
  good _ := True
  bad _ _ _ := False
  empty := trivial
  step _ _ _ _ _ _ := trivial
  final _ _ _ _ h := check_sound (Option.some.inj h)

/-- **Knowledge soundness** at error `0` with no verifier query. -/
theorem ks : KS (Rel submission.Vb) submission.V submission.E submission.ε submission.qV :=
  ⟨⟨kstate, kstate.bounded_of_not_bad (fun _ _ _ h => h) _⟩, fun _ _ _ => le_rfl⟩

/-- **Perfect completeness**, for every oracle function. -/
theorem complete : Complete (Rel submission.Vb) submission.P submission.V :=
  fun _ _ _ hR => check_encode hR

/-- **The baseline is certified.** The image clause is the library's theorem: the image, the
extractor and the fuel are the library's. -/
theorem certificate : Certificate submission where
  secure := ks
  complete := complete
  computes := WitnessSending.computes
  cap := ⟨zero_le, Nat.zero_le _, fun _ => Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40),
    by decide⟩

end BaselineV3
