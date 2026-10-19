/-
# The top level of `V` and the node branch (BLUEPRINT-R1 §1.1–§1.3, §14 "Verifier.lean")

This module is the part of `Verifier.lean` that does not depend on the SNARK. The leaf
verifier is a parameter (`LeafVerifier`): the exact leaf size `leafSize n` (§7) and the SNARK
verifier `prog s n h π_S`, a query program (§1.3 step 3). `Verifier.lean` instantiates both.

* **Formats (§1.1).** Word 0 of a proof (bytes 0–7) is the tag: `0` a leaf, `1` a node.
  * A leaf proof is `enc64 0 ‖ s ‖ enc64 n ‖ h ‖ π_S`, of exactly `leafSize n` bytes. Its first 48
    bytes are `encode (.leaf s n)`, so the library's `decode` reads it as `.leaf s n`
    (`decode_leaf`), and the library's extractor image and `computes` apply unchanged.
  * A node proof is exactly `encode (.node c₁ c₂ π₁ π₂)`.
* **`V` and `check` (§1.2).**
  * A proof under 8 bytes, or with any other tag, is rejected.
  * The leaf branch is `leafProg` (§1.3). It parses the header and checks, with no oracle query:
    `n ≤ chainCap`, `π.size = leafSize n` and `c = leafStmt h n`. Then it accepts iff `h = s`
    when `n = 0`, and otherwise runs the SNARK verifier.
  * The node branch decides `Rel` locally, with no query (`checkNode`). The proof must be the
    canonical encoding of the node it decodes to (`decodeF`, `encodeF` of `SpartanChainDecode`,
    linear in the proof). The statement must be `nodeStmt c₁ c₂`. Each child must be at most
    `proofCap` bytes and be accepted by `check`, recursively on the size.
* **`vb`** is the instantiated verifier `π.size ≤ proofCap && check c π`. A submission whose `V`
  is `V LV` has `Submission.Vb = vb LV` (`Vb_eq_vb`), because `V` and `check` take the same
  branches (`V_run`).

Proved here, for every `LeafVerifier`:
* the unfoldings `check_eq`, `checkNode_eq` (library `decode`/`encode`) and `V_run`;
* node soundness `checkNode_sound` and `checkNode_rel`, and node completeness
  `check_encode_node`;
* statement binding `check_stmt_unique`;
* the canaries of DESIGN-v3 §6.3 step 7, for both branches: `leaf_push_rejected`,
  `leaf_pop_rejected`, `node_push_rejected`, `node_pop_rejected`; a flipped statement bit and a
  swapped child pair are rejected by binding;
* the extractor's view of a leaf, `decode_leaf`, and the zero-step leaf `leafProg_zero_rel`;
* the query count of every path except the SNARK: `V_eq_ret`, `leafProg_queries`.
-/
import SpartanChainDecode

namespace SpartanChain
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

/-! ## The leaf verifier, as a parameter -/

/-- The SNARK side of a leaf (§1.3 step 3, §7), supplied by `Verifier.lean`. -/
structure LeafVerifier where
  /-- `leafSize n`: the exact byte length of a leaf proof of a chain of `n` steps. -/
  size : ℕ → ℕ
  /-- A leaf proof holds at least its 80-byte header. -/
  size_ge : ∀ n, 80 ≤ size n
  /-- The SNARK verifier on `π_S` with public input `(s, n, h)`, run when `n ≥ 1`. -/
  prog : (s : Digest) → (n : ℕ) → (h : Digest) → (snark : ByteArray) → OProg Bool

variable (LV : LeafVerifier)

/-! ## Parsing (§1.1) -/

/-- Word 0 of a proof, bytes 0–7 little-endian: the tag. -/
def tagWord (π : Proof) : ℕ := ofLE (π.data.extract 0 8).toList

/-- The 32 bytes of `π` from byte `k` on, as a digest (`0` past the end). -/
def digestFrom (π : Proof) (k : ℕ) : Digest :=
  Vector.ofFn fun i : Fin 32 => π.data.getD (k + i.val) 0

/-- The chain start of a leaf proof, bytes 8–39. -/
def leafS (π : Proof) : Digest := digestFrom π 8

/-- The chain length of a leaf proof, bytes 40–47 little-endian. -/
def leafN (π : Proof) : ℕ := ofLE (π.data.extract 40 48).toList

/-- The claimed chain end of a leaf proof, bytes 48–79. -/
def leafH (π : Proof) : Digest := digestFrom π 48

/-- The SNARK of a leaf proof, bytes 80 to the end. -/
def leafSnark (π : Proof) : ByteArray := π.extract 80 π.size

/-- The leaf header test (§1.3 step 1), no oracle: the length within `chainCap`, the exact size,
and the statement `leafStmt h n`. -/
def leafHeaderOK (c : Digest) (π : Proof) : Bool :=
  decide (leafN π ≤ chainCap) && decide (π.size = LV.size (leafN π)) &&
    decide (c = leafStmt (leafH π) (leafN π))

/-- **The leaf branch** (§1.3), the only query program. -/
def leafProg (c : Digest) (π : Proof) : OProg Bool :=
  if leafHeaderOK LV c π then
    if leafN π = 0 then .ret (decide (leafH π = leafS π))
    else LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)
  else .ret false

/-! ## The decision and the verifier (§1.2) -/

/-- **The instantiated decision.** A leaf runs `leafProg` with the BLAKE2s oracle. A node must be
the canonical encoding of the node it decodes to, with the statement `nodeStmt c₁ c₂` and both
children (each at most `proofCap` bytes) accepted, recursively. -/
def check (c : Digest) (π : Proof) : Bool :=
  if π.size < 8 then false
  else if tagWord π = 0 then (leafProg LV c π).run blake2sOracle
  else if tagWord π = 1 then
    match decodeF π with
    | some (.node c₁ c₂ π₁ π₂) =>
      if _h : encodeF (.node c₁ c₂ π₁ π₂) = π then
        decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
          (decide (π₂.size ≤ proofCap) && check c₂ π₂)
      else false
    | _ => false
  else false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, encodeF_eq, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- The node branch of `check`: no oracle query. -/
def checkNode (c : Digest) (π : Proof) : Bool :=
  match decodeF π with
  | some (.node c₁ c₂ π₁ π₂) =>
    if encodeF (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check LV c₁ π₁) &&
        (decide (π₂.size ≤ proofCap) && check LV c₂ π₂)
    else false
  | _ => false

/-- **The verifier** (§1.2): the leaf branch is a query program, every other branch returns at
once. -/
def V (c : Digest) (π : Proof) : OProg Bool :=
  if π.size < 8 then .ret false
  else if tagWord π = 0 then leafProg LV c π
  else if tagWord π = 1 then .ret (checkNode LV c π)
  else .ret false

/-- The instantiated verifier: `check`, rejecting proofs above `proofCap`. -/
def vb (c : Digest) (π : Proof) : Bool := decide (π.size ≤ proofCap) && check LV c π

/-! ## Unfolding -/

theorem check_eq (c : Digest) (π : Proof) : check LV c π =
    if π.size < 8 then false
    else if tagWord π = 0 then (leafProg LV c π).run blake2sOracle
    else if tagWord π = 1 then checkNode LV c π
    else false := by
  rw [check]
  simp only [checkNode, dite_eq_ite]

/-- `checkNode`, with the library's `decode` and `encode`. -/
theorem checkNode_eq (c : Digest) (π : Proof) : checkNode LV c π =
    match decode π with
    | some (.node c₁ c₂ π₁ π₂) =>
      if encode (.node c₁ c₂ π₁ π₂) = π then
        decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check LV c₁ π₁) &&
          (decide (π₂.size ≤ proofCap) && check LV c₂ π₂)
      else false
    | _ => false := by
  rw [checkNode, decodeF_eq]
  simp only [encodeF_eq]

/-- `V` and `check` take the same branches. -/
theorem V_run (c : Digest) (π : Proof) : (V LV c π).run blake2sOracle = check LV c π := by
  rw [check_eq, V]
  split_ifs <;> rfl

/-- A submission whose verifier is `V LV` has `vb LV` as its instantiated verifier. -/
theorem Vb_eq_vb (S : Submission) (hV : S.V = V LV) : S.Vb = vb LV := by
  funext c π
  rw [Submission.Vb, vb, hV, V_run]
  by_cases h : π.size ≤ proofCap <;> simp [h]

theorem size_le_of_vb {c : Digest} {π : Proof} (h : vb LV c π = true) : π.size ≤ proofCap := by
  rw [vb, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

/-! ## The node branch: soundness and completeness -/

/-- **Node soundness**: an accepted node proof is the canonical encoding of a node whose statement
is `c` and whose children the instantiated verifier accepts. -/
theorem checkNode_sound {c : Digest} {π : Proof} (h : checkNode LV c π = true) :
    ∃ c₁ c₂ π₁ π₂, decode π = some (.node c₁ c₂ π₁ π₂) ∧ encode (.node c₁ c₂ π₁ π₂) = π ∧
      c = nodeStmt c₁ c₂ ∧ vb LV c₁ π₁ = true ∧ vb LV c₂ π₂ = true := by
  rw [checkNode_eq] at h
  split at h
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨c₁, c₂, π₁, π₂, hd, ‹_›, h.1.1, by simp [vb, h], by simp [vb, h]⟩
    · cases h
  · cases h

/-- An accepted node proof decodes to a witness of `Rel (vb LV)`: the `final` law for nodes. -/
theorem checkNode_rel {c : Digest} {π : Proof} (h : checkNode LV c π = true) :
    ∃ w, decode π = some w ∧ Rel (vb LV) c w := by
  obtain ⟨c₁, c₂, π₁, π₂, hd, -, hc, h₁, h₂⟩ := checkNode_sound LV h
  exact ⟨_, hd, hc, h₁, h₂⟩

theorem take8_encode (w : Wit) : (encode w).data.toList.take 8 =
    wordBytes (toWord (match w with | .leaf .. => 0 | .node .. => 1)) := by
  rw [WitnessSending.encode_data]
  cases w <;> simp [witWords, wordsBytes, List.flatMap_cons, wordBytes]

theorem proof_extract_toList (π : Proof) (i j : ℕ) :
    (π.data.extract i j).toList = (π.data.toList.drop i).take (j - i) := by
  simp [Array.toList_extract, List.extract]

theorem tagWord_eq (π : Proof) : tagWord π = ofLE (π.data.toList.take 8) := by
  rw [tagWord, proof_extract_toList]; rfl

theorem tagWord_encode_node (c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    tagWord (encode (.node c₁ c₂ π₁ π₂)) = 1 := by
  rw [tagWord_eq, take8_encode, ofLE_wordBytes]; rfl

theorem size_encode_node (c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    88 ≤ (encode (.node c₁ c₂ π₁ π₂)).size := by
  rw [size_encode]
  simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_digest_length]
  omega

/-- **Node completeness**: the encoding of a node witness of `Rel (vb LV)` is accepted. -/
theorem check_encode_node {c c₁ c₂ : Digest} {π₁ π₂ : Proof}
    (hR : Rel (vb LV) c (.node c₁ c₂ π₁ π₂)) : check LV c (encode (.node c₁ c₂ π₁ π₂)) = true := by
  obtain ⟨hc, h₁, h₂⟩ := hR
  have hf : (Wit.node c₁ c₂ π₁ π₂).Fits := ⟨size_le_of_vb LV h₁, size_le_of_vb LV h₂⟩
  rw [check_eq, ite_eq_right (by have := size_encode_node c₁ c₂ π₁ π₂; omega), tagWord_encode_node,
    ite_eq_right (by decide), ite_eq_left rfl, checkNode_eq, decode_encode _ hf]
  rw [vb, Bool.and_eq_true] at h₁ h₂
  simp_all

/-! ## Leaves: the header, the extractor's view, the zero-step leaf -/

theorem leafProg_header {c : Digest} {π : Proof} {L : Log} {b : Bool}
    (h : (leafProg LV c π).runLog L = some b) (hb : b = true) : leafHeaderOK LV c π = true := by
  subst hb
  by_contra hn
  rw [leafProg, ite_eq_right hn] at h
  cases h

theorem leafProg_header_run {c : Digest} {π : Proof} {H : ByteArray → Digest}
    (h : (leafProg LV c π).run H = true) : leafHeaderOK LV c π = true := by
  by_contra hn
  rw [leafProg, ite_eq_right hn] at h
  cases h

theorem leafHeaderOK_iff {c : Digest} {π : Proof} : leafHeaderOK LV c π = true ↔
    leafN π ≤ chainCap ∧ π.size = LV.size (leafN π) ∧ c = leafStmt (leafH π) (leafN π) := by
  simp [leafHeaderOK, and_assoc]

theorem proof_getD_eq (π : Proof) (i : ℕ) : π.data.getD i 0 = π.data.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold Array.getD
  split
  · rename_i h; rw [Array.getElem?_eq_getElem h]; rfl
  · simp_all

private theorem packBytes_cons8 (l : List UInt8) (h : 8 ≤ l.length) :
    packBytes l = toWord (ofLE (l.take 8)) :: packBytes (l.drop 8) := by
  have := packBytes_append8 (l.drop 8) (pre := l.take 8) (by simp; omega)
  rwa [List.take_append_drop] at this

/-- **The extractor's view of a leaf proof**: the library's `decode` reads the start and the
length of the header, whatever follows byte 48. -/
theorem decode_leaf {π : Proof} (hs : 48 ≤ π.size) (ht : tagWord π = 0) :
    decode π = some (.leaf (leafS π) (leafN π)) := by
  set l := π.data.toList with hl
  have hlen : l.length = π.size := (size_eq_length π).symm
  rw [tagWord_eq] at ht
  have ht0 : toWord (ofLE (l.take 8)) = 0 := by rw [ht]; rfl
  have hS : digestAt (toWord (ofLE (l.take 8)) :: packBytes (l.drop 8)) 1 = leafS π := by
    ext i hi
    simp only [digestAt, Vector.getElem_ofFn, List.drop_succ_cons, List.drop_zero, leafS,
      digestFrom, wordByte_packBytes, proof_getD_eq, ← hl]
    simp [List.getD_eq_getElem?_getD]
  have hN : ((toWord (ofLE (l.take 8)) :: packBytes (l.drop 8)).getD 5 0).toNat = leafN π := by
    have h4 : 4 < (packBytes (l.drop 8)).length := by
      rw [packBytes_length, List.length_drop]; omega
    rw [List.getD_cons_succ, List.getD_eq_getElem _ _ h4]
    simp only [packBytes, List.getElem_map, List.getElem_range, List.drop_drop]
    have hlt : ofLE ((l.drop (8 + 8 * 4)).take 8) < 2 ^ 64 :=
      (ofLE_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) (by simp) : _ ≤ 256 ^ 8)
    rw [toNat_toWord hlt, leafN, proof_extract_toList]
  rw [decode, ← hl, packBytes_cons8 l (by omega), decodeWit_cons, ← hS, ← hN]
  exact ite_eq_left ht0

/-- **The zero-step leaf**: accepted exactly when the header holds and `h = s`, and then the proof
decodes to a witness of the relation. -/
theorem leafProg_zero_rel {c : Digest} {π : Proof} {L : Log}
    (h : (leafProg LV c π).runLog L = some true) (hn : leafN π = 0) (hs : 48 ≤ π.size)
    (ht : tagWord π = 0) : ∃ w, decode π = some w ∧ Rel (vb LV) c w := by
  have hh := leafProg_header LV h rfl
  rw [leafProg, ite_eq_left hh, ite_eq_left hn] at h
  have hhs : leafH π = leafS π := of_decide_eq_true (Option.some.inj h)
  obtain ⟨-, -, hc⟩ := (leafHeaderOK_iff LV).mp hh
  refine ⟨_, decode_leaf hs ht, hn ▸ Nat.zero_le _, ?_⟩
  rw [hc, hhs, hn]; rfl

/-! ## Statement binding -/

/-- An accepted leaf proof binds the statement `leafStmt h n` of its header, for every oracle. -/
theorem leafProg_stmt {c : Digest} {π : Proof} {H : ByteArray → Digest}
    (h : (leafProg LV c π).run H = true) : c = leafStmt (leafH π) (leafN π) :=
  ((leafHeaderOK_iff LV).mp (leafProg_header_run LV h)).2.2

theorem checkNode_stmt_unique {c c' : Digest} {π : Proof} (h : checkNode LV c π = true)
    (h' : checkNode LV c' π = true) : c = c' := by
  obtain ⟨c₁, c₂, π₁, π₂, hd, -, hc, -⟩ := checkNode_sound LV h
  obtain ⟨d₁, d₂, ρ₁, ρ₂, hd', -, hc', -⟩ := checkNode_sound LV h'
  rw [hd] at hd'; cases hd'
  exact hc.trans hc'.symm

/-- **A proof is accepted under at most one statement** (so not under a flipped statement bit, nor,
for a node, under the swapped pair `nodeStmt c₂ c₁ ≠ nodeStmt c₁ c₂`). -/
theorem check_stmt_unique {c c' : Digest} {π : Proof} (h : check LV c π = true)
    (h' : check LV c' π = true) : c = c' := by
  rw [check_eq] at h h'
  by_cases h8 : π.size < 8
  · simp [h8] at h
  by_cases h0 : tagWord π = 0
  · simp only [h8, h0, ↓reduceIte] at h h'
    exact (leafProg_stmt LV h).trans (leafProg_stmt LV h').symm
  by_cases h1 : tagWord π = 1
  · simp only [h8, h1, ↓reduceIte] at h h'
    exact checkNode_stmt_unique LV h h'
  · simp [h8, h0, h1] at h

/-! ## The canaries (DESIGN-v3 §6.3 step 7): one byte appended, the last byte removed -/

/-- `π` without its last byte. -/
def dropLast (π : Proof) : Proof := ⟨π.data.pop⟩

private theorem take_drop_of_take {l l' : List UInt8} {m : ℕ} (h : l.take m = l'.take m)
    {k j : ℕ} (hkj : k + j ≤ m) : (l.drop k).take j = (l'.drop k).take j := by
  have e : ∀ x : List UInt8, (x.drop k).take j = ((x.take m).drop k).take j := fun x => by
    rw [List.drop_take, List.take_take]; congr 1; omega
  rw [e l, e l', h]

private theorem getD_of_take {l l' : List UInt8} {m : ℕ} (h : l.take m = l'.take m) {j : ℕ}
    (hj : j < m) : l.getD j 0 = l'.getD j 0 := by
  have e : ∀ x : List UInt8, x.getD j 0 = (x.take m).getD j 0 := fun x => by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [e l, e l', h]

/-- The tag, the start and the length read only the first 48 bytes. -/
theorem parse48_congr {π π' : Proof} (h : π.data.toList.take 48 = π'.data.toList.take 48) :
    tagWord π = tagWord π' ∧ leafN π = leafN π' ∧ leafS π = leafS π' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tagWord_eq, tagWord_eq, ← List.drop_zero (l := π.data.toList),
      ← List.drop_zero (l := π'.data.toList), take_drop_of_take h (by omega : 0 + 8 ≤ 48)]
  · rw [leafN, leafN, proof_extract_toList, proof_extract_toList,
      take_drop_of_take h (by omega : 40 + 8 ≤ 48)]
  · ext i hi
    simp only [leafS, digestFrom, Vector.getElem_ofFn, proof_getD_eq]
    exact congrArg _ (getD_of_take h (by omega : 8 + i < 48))

/-- The parse reads only the first 80 bytes. -/
theorem parse_congr {π π' : Proof} (h : π.data.toList.take 80 = π'.data.toList.take 80) :
    tagWord π = tagWord π' ∧ leafN π = leafN π' ∧ leafS π = leafS π' ∧ leafH π = leafH π' := by
  have ht : ∀ k j, k + j ≤ 80 → (π.data.toList.drop k).take j = (π'.data.toList.drop k).take j :=
    fun _ _ hkj => take_drop_of_take h hkj
  have hg : ∀ j, j < 80 → π.data.getD j 0 = π'.data.getD j 0 := fun j hj => by
    rw [proof_getD_eq, proof_getD_eq]; exact getD_of_take h hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tagWord_eq, tagWord_eq, ← List.drop_zero (l := π.data.toList),
      ← List.drop_zero (l := π'.data.toList), ht 0 8 (by omega)]
  · rw [leafN, leafN, proof_extract_toList, proof_extract_toList, ht 40 8 (by omega)]
  · ext i hi
    simp only [leafS, digestFrom, Vector.getElem_ofFn]; exact congrArg _ (hg (8 + i) (by omega))
  · ext i hi
    simp only [leafH, digestFrom, Vector.getElem_ofFn]; exact congrArg _ (hg (48 + i) (by omega))

theorem take_push {π : Proof} {m : ℕ} (hs : m ≤ π.size) (b : UInt8) :
    (π.push b).data.toList.take m = π.data.toList.take m := by
  have : m ≤ π.data.toList.length := by rw [← size_eq_length]; exact hs
  simp [ByteArray.push, List.take_append_of_le_length this]

theorem take_dropLast {π : Proof} {m : ℕ} (hs : m + 1 ≤ π.size) :
    (dropLast π).data.toList.take m = π.data.toList.take m := by
  have : m + 1 ≤ π.data.toList.length := by rw [← size_eq_length]; exact hs
  rw [dropLast, Array.toList_pop, List.dropLast_eq_take, List.take_take]
  congr 1; omega

theorem size_dropLast (π : Proof) : (dropLast π).size = π.size - 1 := by
  show π.data.pop.size = π.data.size - 1
  exact Array.size_pop

/-- An accepted leaf proof has exactly `leafSize n` bytes. -/
theorem check_leaf_size {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 0) : π.size = LV.size (leafN π) := by
  rw [check_eq] at h
  by_cases h8 : π.size < 8
  · simp [h8] at h
  simp only [h8, ht, ↓reduceIte] at h
  exact ((leafHeaderOK_iff LV).mp (leafProg_header_run LV h)).2.1

/-- An accepted node proof is a canonical encoding: a multiple of 8 bytes, at least 88. -/
theorem check_node_size {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 1) : 8 ∣ π.size ∧ 88 ≤ π.size := by
  rw [check_eq] at h
  by_cases h8 : π.size < 8
  · simp [h8] at h
  simp only [h8, ht, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at h
  obtain ⟨c₁, c₂, π₁, π₂, -, he, -⟩ := checkNode_sound LV h
  rw [← he]
  exact ⟨⟨_, size_encode _⟩, size_encode_node _ _ _ _⟩

/-- A proof whose first 48 bytes (the tag and the length) are those of an accepted leaf proof, but
whose size differs, is rejected under every statement. -/
theorem leaf_resized_rejected {c c' : Digest} {π π' : Proof} (h : check LV c π = true)
    (ht : tagWord π = 0) (h48 : π.data.toList.take 48 = π'.data.toList.take 48)
    (hsz : π'.size ≠ π.size) (h8 : 8 ≤ π'.size) : check LV c' π' = false := by
  obtain ⟨htt, hn, -⟩ := parse48_congr h48
  have hsize := check_leaf_size LV h ht
  rw [check_eq, ite_eq_right (by omega), ← htt, ite_eq_left ht, leafProg]
  have : leafHeaderOK LV c' π' = false := by
    rw [Bool.eq_false_iff]; intro hh
    exact hsz (((leafHeaderOK_iff LV).mp hh).2.1.trans (by rw [← hn, hsize]))
  rw [this]; rfl

theorem leaf_push_rejected {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 0) (b : UInt8) (c' : Digest) : check LV c' (π.push b) = false := by
  have hs : 80 ≤ π.size := check_leaf_size LV h ht ▸ LV.size_ge _
  exact leaf_resized_rejected LV h ht (take_push (by omega) b).symm
    (by rw [ByteArray.size_push]; omega) (by rw [ByteArray.size_push]; omega)

theorem leaf_pop_rejected {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 0) (c' : Digest) : check LV c' (dropLast π) = false := by
  have hs : 80 ≤ π.size := check_leaf_size LV h ht ▸ LV.size_ge _
  exact leaf_resized_rejected LV h ht (take_dropLast (by omega)).symm
    (by rw [size_dropLast]; omega) (by rw [size_dropLast]; omega)

theorem node_push_rejected {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 1) (b : UInt8) (c' : Digest) : check LV c' (π.push b) = false := by
  obtain ⟨hd, hs⟩ := check_node_size LV h ht
  have htt : tagWord (π.push b) = 1 := by
    exact ht ▸ (parse48_congr (take_push (by omega) b)).1
  rw [Bool.eq_false_iff]; intro h'
  have := (check_node_size LV h' htt).1
  rw [ByteArray.size_push] at this
  omega

theorem node_pop_rejected {c : Digest} {π : Proof} (h : check LV c π = true)
    (ht : tagWord π = 1) (c' : Digest) : check LV c' (dropLast π) = false := by
  obtain ⟨hd, hs⟩ := check_node_size LV h ht
  have htt : tagWord (dropLast π) = 1 := by
    exact ht ▸ (parse48_congr (take_dropLast (by omega))).1
  rw [Bool.eq_false_iff]; intro h'
  have := (check_node_size LV h' htt).1
  rw [size_dropLast] at this
  omega

/-! ## Query counts: only the SNARK asks the oracle -/

/-- Off the leaf branch, `V` returns at once. -/
theorem V_eq_ret {c : Digest} {π : Proof} (h : ¬ (8 ≤ π.size ∧ tagWord π = 0)) :
    V LV c π = .ret (check LV c π) := by
  rw [V, check_eq]
  split_ifs <;> first | rfl | omega

theorem V_queries_of_not_leaf {c : Digest} {π : Proof} (H : ByteArray → Digest)
    (h : ¬ (8 ≤ π.size ∧ tagWord π = 0)) : (V LV c π).queries H = [] := by
  rw [V_eq_ret LV h]; rfl

/-- On the leaf branch, the only queries are the SNARK verifier's. -/
theorem leafProg_queries (c : Digest) (π : Proof) (H : ByteArray → Digest) :
    (leafProg LV c π).queries H =
      if leafHeaderOK LV c π = true ∧ leafN π ≠ 0 then
        (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).queries H
      else [] := by
  unfold leafProg
  split_ifs <;> simp_all [OProg.queries]

/-! ## What `final` gets from an accepted proof (for `Soundness/KS.lean`) -/

/-- **Off the leaf branch**, a proof accepted on any log decodes to a witness of `Rel (vb LV)`,
with no oracle answer used. -/
theorem final_of_not_leaf {c : Digest} {π : Proof} {L : Log}
    (h : (V LV c π).runLog L = some true) (hnl : ¬ (8 ≤ π.size ∧ tagWord π = 0)) :
    ∃ w, decode π = some w ∧ Rel (vb LV) c w := by
  rw [V_eq_ret LV hnl] at h
  have hc : check LV c π = true := Option.some.inj h
  rw [check_eq] at hc
  by_cases h8 : π.size < 8
  · simp [h8] at hc
  have ht0 : tagWord π ≠ 0 := fun ht0 => hnl ⟨by omega, ht0⟩
  by_cases h1 : tagWord π = 1
  · simp only [h8, h1, ↓reduceIte] at hc
    exact checkNode_rel LV hc
  · simp [h8, ht0, h1] at hc

/-- **On the leaf branch**, an accepted proof (on any log) has a header that holds, decodes (for
the extractor) to its start and length, and either is the zero-step leaf with `h = s` or was
accepted by the SNARK verifier on the same log. -/
theorem final_of_leaf {c : Digest} {π : Proof} {L : Log}
    (h : (V LV c π).runLog L = some true) (h8 : 8 ≤ π.size) (ht : tagWord π = 0) :
    decode π = some (.leaf (leafS π) (leafN π)) ∧ leafN π ≤ chainCap ∧
      c = leafStmt (leafH π) (leafN π) ∧ (leafN π = 0 → leafH π = leafS π) ∧
      (leafN π ≠ 0 → (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L =
        some true) := by
  rw [V, ite_eq_right (by omega), ite_eq_left ht] at h
  have hh := leafProg_header LV h rfl
  obtain ⟨hn, hsz, hc⟩ := (leafHeaderOK_iff LV).mp hh
  have hs : 48 ≤ π.size := by have := LV.size_ge (leafN π); omega
  refine ⟨decode_leaf hs ht, hn, hc, fun h0 => ?_, fun h0 => ?_⟩
  · rw [leafProg, ite_eq_left hh, ite_eq_left h0] at h
    exact of_decide_eq_true (Option.some.inj h)
  · rwa [leafProg, ite_eq_left hh, ite_eq_right h0] at h

/-! ## Controls (BLUEPRINT-R1 §10.1, the top level) -/

/-- The start of the control leaf: `01…01`. -/
abbrev ctlStart : Digest := Vector.replicate 32 1

/-- An 80-byte leaf proof of the zero-step chain from `01…01`: tag `0`, `s`, `n = 0`, `h = s`. -/
def zeroLeaf : Proof :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0] ++ Array.replicate 32 1 ++ #[0, 0, 0, 0, 0, 0, 0, 0] ++
    Array.replicate 32 1⟩

theorem zeroLeaf_parse : zeroLeaf.size = 80 ∧ tagWord zeroLeaf = 0 ∧ leafN zeroLeaf = 0 ∧
    leafS zeroLeaf = ctlStart ∧ leafH zeroLeaf = ctlStart := by
  decide +kernel

/-- The statement of the control leaf. -/
abbrev ctlStmt : Digest := leafStmt ctlStart 0

/-- **Positive (leaf)**: the zero-step leaf proof is accepted under its statement, for every leaf
verifier whose `leafSize 0` is 80 (no query: `leafProg_queries`). -/
theorem zeroLeaf_accepted (h0 : LV.size 0 = 80) : check LV ctlStmt zeroLeaf = true := by
  obtain ⟨hs, ht, hn, hS, hH⟩ := zeroLeaf_parse
  have hh : leafHeaderOK LV ctlStmt zeroLeaf = true :=
    (leafHeaderOK_iff LV).mpr ⟨by rw [hn]; exact Nat.zero_le _, by rw [hs, hn, h0], by rw [hH, hn]⟩
  rw [check_eq, ite_eq_right (by omega), ite_eq_left ht, leafProg, ite_eq_left hh, ite_eq_left hn]
  simp [OProg.run, hS, hH]

/-- **Positive (node)**: the node over two control leaves is accepted under `nodeStmt`. -/
theorem zeroNode_accepted (h0 : LV.size 0 = 80) :
    check LV (nodeStmt ctlStmt ctlStmt) (encode (.node ctlStmt ctlStmt zeroLeaf zeroLeaf)) =
      true := by
  have hv : vb LV ctlStmt zeroLeaf = true := by
    rw [vb, zeroLeaf_accepted LV h0, zeroLeaf_parse.1]; rfl
  exact check_encode_node LV ⟨rfl, hv, hv⟩

/-- **Negative (canaries on the controls)**: one byte appended or removed, on the leaf and on the
node, is rejected under every statement; so is the leaf under any other statement. -/
theorem zeroLeaf_canaries (h0 : LV.size 0 = 80) (b : UInt8) (c' : Digest) :
    check LV c' (zeroLeaf.push b) = false ∧ check LV c' (dropLast zeroLeaf) = false := by
  have h := zeroLeaf_accepted LV h0
  have ht := zeroLeaf_parse.2.1
  exact ⟨leaf_push_rejected LV h ht b c', leaf_pop_rejected LV h ht c'⟩

theorem zeroLeaf_other_stmt (h0 : LV.size 0 = 80) {c' : Digest} (hc : c' ≠ ctlStmt) :
    check LV c' zeroLeaf = false := by
  rw [Bool.eq_false_iff]
  exact fun h' => hc (check_stmt_unique LV h' (zeroLeaf_accepted LV h0))

theorem zeroNode_canaries (h0 : LV.size 0 = 80) (b : UInt8) (c' : Digest) :
    check LV c' ((encode (.node ctlStmt ctlStmt zeroLeaf zeroLeaf)).push b) = false ∧
      check LV c' (dropLast (encode (.node ctlStmt ctlStmt zeroLeaf zeroLeaf))) = false :=
  ⟨node_push_rejected LV (zeroNode_accepted LV h0) (tagWord_encode_node ..) b c',
    node_pop_rejected LV (zeroNode_accepted LV h0) (tagWord_encode_node ..) c'⟩

/-- **Negative**: an unknown tag word, and a proof under 8 bytes, are rejected. -/
theorem bad_tag_rejected (c : Digest) :
    check LV c ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = false ∧ check LV c ⟨#[0]⟩ = false := by
  have ht : tagWord ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = 2 := by decide +kernel
  constructor
  · rw [check_eq, ht]; rfl
  · rw [check_eq]; rfl

end SpartanChain
