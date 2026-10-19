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
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

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

/-! ## The node codec over bytes (review S2b-M2)

The list-based `decodeF`/`encodeF` above are linear but slow in compiled code (boxed words, one
list cell per byte): about 1.2 s of the 575 KB smoke root. `nodeParse` reads a node proof by byte
offsets: the two length words, the two digests, the two children cut out with `extract`, and the
canonicity test against `encodeNodeB` (a byte-level `encode`, `encodeNodeB_eq`). `nodeParse_eq`
proves it equal to `nodeSpec`, the canonical node encodings the library's `decode` reads. -/

/-- The zero bytes that pad a length to a multiple of 8. -/
def padLen (l : ℕ) : ℕ := (8 - l % 8) % 8

theorem wordBytes_ofLE {p : List UInt8} (hp : p.length ≤ 8) :
    wordBytes (toWord (ofLE p)) = p ++ List.replicate (8 - p.length) 0 := by
  have hlt : ofLE p < 2 ^ 64 :=
    (ofLE_lt p).trans_le (by
      calc 256 ^ p.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hp
        _ = 2 ^ 64 := by norm_num)
  apply List.ext_getElem
  · simp [wordBytes]; omega
  intro i h1 h2
  simp only [wordBytes, List.getElem_ofFn, toNat_toWord hlt]
  rw [← toUInt8_mod, ofLE_div_mod]
  by_cases hi : i < p.length
  · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]; simp
  · rw [List.getElem_append_right (by omega), List.getElem_replicate,
      List.getD_eq_default _ _ (by omega)]; rfl

theorem wordsBytes_packBytes (b : List UInt8) :
    wordsBytes (packBytes b) = b ++ List.replicate (padLen b.length) 0 := by
  rw [← packFast_eq]
  fun_induction packFast b with
  | case1 => rfl
  | case2 x xs ih =>
    rw [wordsBytes, List.flatMap_cons, ← wordsBytes, ih]
    by_cases h : 8 ≤ (x :: xs).length
    · rw [wordBytes_ofLE (by simp), List.length_take, Nat.min_eq_left h, Nat.sub_self,
        List.replicate_zero, List.append_nil, ← List.append_assoc, List.take_append_drop,
        List.length_drop]
      congr 2; unfold padLen; omega
    · rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega),
        wordBytes_ofLE (by omega)]
      simp only [List.nil_append, List.length_nil, padLen]
      simp only [List.length_cons] at h ⊢
      rw [show (8 - 0 % 8) % 8 = 0 from rfl, List.replicate_zero, List.append_nil]
      congr 2; omega

/-- One child on the wire: its length word, its bytes, its zero padding. -/
def segBytes (π : Proof) : ByteArray :=
  ⟨(wordBytes (toWord π.size)).toArray⟩ ++ π ++ ⟨Array.replicate (padLen π.size) 0⟩

/-- **The canonical node encoding**, built by appends: tag word `1`, the two digests, the two
children. -/
def encodeNodeB (c₁ c₂ : Digest) (π₁ π₂ : Proof) : Proof :=
  ⟨(wordBytes (toWord 1)).toArray⟩ ++ ⟨c₁.toArray⟩ ++ ⟨c₂.toArray⟩ ++ segBytes π₁ ++ segBytes π₂

private theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem segBytes_toList (π : Proof) : (segBytes π).data.toList =
    wordBytes (toWord π.size) ++ π.data.toList ++ List.replicate (padLen π.size) 0 := by
  simp [segBytes]

theorem encodeNodeB_toList (c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    (encodeNodeB c₁ c₂ π₁ π₂).data.toList = wordBytes (toWord 1) ++ c₁.toList ++ c₂.toList ++
      (segBytes π₁).data.toList ++ (segBytes π₂).data.toList := by
  simp [encodeNodeB, Vector.toList]

theorem encodeNodeB_eq (c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    encodeNodeB c₁ c₂ π₁ π₂ = encode (.node c₁ c₂ π₁ π₂) := by
  apply ByteArray.ext
  apply Array.ext'
  rw [encodeNodeB_toList, WitnessSending.encode_data, segBytes_toList, segBytes_toList]
  have hd : ∀ d : Digest, wordsBytes (packBytes d.toList) = d.toList := fun d => by
    rw [wordsBytes_packBytes]; simp [padLen]
  have happ : ∀ a b : List Word, wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
    fun a b => List.flatMap_append
  have hcons : ∀ (w : Word) (a : List Word), wordsBytes (w :: a) = wordBytes w ++ wordsBytes a :=
    fun _ _ => List.flatMap_cons
  simp only [witWords, bytesWords, List.cons_append, hcons, happ, hd, wordsBytes_packBytes,
    ← size_eq_length, List.append_assoc]

/-- The little-endian number in bytes `[i, i + 8)` of a proof. -/
def word8At (π : Proof) (i : ℕ) : ℕ := ofLE (π.data.extract i (i + 8)).toList

/-- The 32 bytes of a proof from byte `k` on, as a digest (`0` past the end). -/
def digestAtB (π : Proof) (k : ℕ) : Digest :=
  Vector.ofFn fun i : Fin 32 => π.data.getD (k + i.val) 0

/-- **The node parser over bytes**: read the two length words, cut out the two children, and
accept iff the proof is exactly the canonical encoding of what was read, with both children within
`proofCap`. Linear in the proof, with no list of it built. -/
def nodeParse (π : Proof) : Option (Digest × Digest × Proof × Proof) :=
  let l₁ := word8At π 72
  let o₂ := 80 + l₁ + padLen l₁
  let l₂ := word8At π o₂
  if l₁ ≤ proofCap ∧ l₂ ≤ proofCap then
    let c₁ := digestAtB π 8
    let c₂ := digestAtB π 40
    let π₁ := π.extract 80 (80 + l₁)
    let π₂ := π.extract (o₂ + 8) (o₂ + 8 + l₂)
    if encodeNodeB c₁ c₂ π₁ π₂ = π then some (c₁, c₂, π₁, π₂) else none
  else none

/-- What `nodeParse` decides: the canonical node encodings, read by the library's `decode`. -/
def nodeSpec (π : Proof) : Option (Digest × Digest × Proof × Proof) :=
  match decode π with
  | some (.node c₁ c₂ π₁ π₂) =>
    if encode (.node c₁ c₂ π₁ π₂) = π then some (c₁, c₂, π₁, π₂) else none
  | _ => none

theorem nodeParse_sound {π : Proof} {c₁ c₂ : Digest} {π₁ π₂ : Proof}
    (h : nodeParse π = some (c₁, c₂, π₁, π₂)) :
    encode (.node c₁ c₂ π₁ π₂) = π ∧ π₁.size ≤ proofCap ∧ π₂.size ≤ proofCap := by
  simp only [nodeParse] at h
  split_ifs at h with hl he
  injection h with h; injection h with h1 h; injection h with h2 h; injection h with h3 h4
  subst h1 h2 h3 h4
  refine ⟨(encodeNodeB_eq ..).symm.trans he, ?_, ?_⟩
  · rw [ByteArray.size_extract]; omega
  · rw [ByteArray.size_extract]; omega

theorem bytes_extract_toList (π : Proof) (i j : ℕ) :
    (π.data.extract i j).toList = (π.data.toList.drop i).take (j - i) := by
  simp [Array.toList_extract, List.extract]

private theorem getD_eq' (π : Proof) (i : ℕ) : π.data.getD i 0 = π.data.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold Array.getD
  split
  · rename_i h; rw [Array.getElem?_eq_getElem h]; rfl
  · simp_all

private theorem read_slice {l A B C : List UInt8} (h : l = A ++ B ++ C) {i j : ℕ}
    (hi : i = A.length) (hj : j = B.length) : (l.drop i).take j = B := by
  subst h hi hj; simp

private theorem read_getD {l A B C : List UInt8} (h : l = A ++ B ++ C) {i k : ℕ}
    (hi : i = A.length) (hk : k < B.length) : l.getD (i + k) 0 = B.getD k 0 := by
  subst h hi
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk,
    List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

theorem nodeParse_encode (c₁ c₂ : Digest) {π₁ π₂ : Proof} (h₁ : π₁.size ≤ proofCap)
    (h₂ : π₂.size ≤ proofCap) :
    nodeParse (encode (.node c₁ c₂ π₁ π₂)) = some (c₁, c₂, π₁, π₂) := by
  rw [← encodeNodeB_eq]
  set π := encodeNodeB c₁ c₂ π₁ π₂ with hπ
  set W0 := wordBytes (toWord 1)
  set W1 := wordBytes (toWord π₁.size)
  set W2 := wordBytes (toWord π₂.size)
  set Z1 := List.replicate (padLen π₁.size) (0 : UInt8)
  set Z2 := List.replicate (padLen π₂.size) (0 : UInt8)
  have hL : π.data.toList =
      W0 ++ c₁.toList ++ c₂.toList ++ W1 ++ π₁.data.toList ++ Z1 ++ W2 ++ π₂.data.toList ++ Z2 := by
    rw [hπ, encodeNodeB_toList, segBytes_toList, segBytes_toList]; simp only [List.append_assoc]; rfl
  have hw : ∀ w : Word, (wordBytes w).length = 8 := fun w => by simp [wordBytes]
  have hs1 : π₁.data.toList.length = π₁.size := (size_eq_length _).symm
  have hs2 : π₂.data.toList.length = π₂.size := (size_eq_length _).symm
  have hz1 : Z1.length = padLen π₁.size := List.length_replicate
  have hlt1 : π₁.size < 2 ^ 64 := by unfold proofCap at h₁; omega
  have hlt2 : π₂.size < 2 ^ 64 := by unfold proofCap at h₂; omega
  have hl₁ : word8At π 72 = π₁.size := by
    rw [word8At, bytes_extract_toList, read_slice (A := W0 ++ c₁.toList ++ c₂.toList) (B := W1)
      (by rw [hL]; all_goals first | (simp only [List.append_assoc]; done) | (simp only [List.append_assoc]; rfl)) (by simp [W0, hw]) (by simp [W1, hw]),
      ofLE_wordBytes, toNat_toWord hlt1]
  have hl₂ : word8At π (80 + π₁.size + padLen π₁.size) = π₂.size := by
    rw [word8At, bytes_extract_toList,
      read_slice (A := W0 ++ c₁.toList ++ c₂.toList ++ W1 ++ π₁.data.toList ++ Z1) (B := W2)
      (by rw [hL]; all_goals first | (simp only [List.append_assoc]; done) | (simp only [List.append_assoc]; rfl)) (by simp [W0, W1, hw, hs1, hz1]; omega)
      (by simp [W2, hw]), ofLE_wordBytes, toNat_toWord hlt2]
  have hd : ∀ (A C : List UInt8) (d : Digest) (k : ℕ), π.data.toList = A ++ d.toList ++ C →
      k = A.length → digestAtB π k = d := by
    intro A C d k hA hk
    ext i hi
    simp only [digestAtB, Vector.getElem_ofFn, getD_eq']
    rw [read_getD hA hk (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  have hc₁ : digestAtB π 8 = c₁ := hd W0 _ c₁ 8 (by rw [hL]; all_goals first | (simp only [List.append_assoc]; done) | (simp only [List.append_assoc]; rfl))
    (by simp [W0, hw])
  have hc₂ : digestAtB π 40 = c₂ := hd (W0 ++ c₁.toList) _ c₂ 40
    (by rw [hL]; all_goals first | (simp only [List.append_assoc]; done) | (simp only [List.append_assoc]; rfl)) (by simp [W0, hw])
  have hx : ∀ (A C : List UInt8) (ρ : Proof) (i : ℕ), π.data.toList = A ++ ρ.data.toList ++ C →
      i = A.length → π.extract i (i + ρ.size) = ρ := by
    intro A C ρ i hA hi
    apply ByteArray.ext; apply Array.ext'
    rw [ByteArray.data_extract, bytes_extract_toList, Nat.add_sub_cancel_left,
      read_slice hA hi (size_eq_length ρ)]
  have hπ₁ : π.extract 80 (80 + π₁.size) = π₁ :=
    hx (W0 ++ c₁.toList ++ c₂.toList ++ W1) _ π₁ 80 (by rw [hL]; all_goals first | (simp only [List.append_assoc]; done) | (simp only [List.append_assoc]; rfl))
      (by simp [W0, W1, hw])
  have hπ₂ : π.extract (80 + π₁.size + padLen π₁.size + 8)
      (80 + π₁.size + padLen π₁.size + 8 + π₂.size) = π₂ :=
    hx (W0 ++ c₁.toList ++ c₂.toList ++ W1 ++ π₁.data.toList ++ Z1 ++ W2) _ π₂ _ (by rw [hL])
      (by simp only [W0, W1, W2, List.length_append, hw, hs1, hz1, Vector.length_toList])
  simp only [nodeParse, hl₁, hl₂, hc₁, hc₂, hπ₁, hπ₂, h₁, h₂, and_self, ↓reduceIte]
  exact ite_eq_left hπ.symm

/-- A node the library's `decode` reads has both children within `proofCap`. -/
theorem decode_node_fits {π : Proof} {c₁ c₂ : Digest} {π₁ π₂ : Proof}
    (h : decode π = some (.node c₁ c₂ π₁ π₂)) : π₁.size ≤ proofCap ∧ π₂.size ≤ proofCap := by
  rw [WitnessSending.decode] at h
  generalize packBytes π.data.toList = o at h
  cases o with
  | nil => cases h
  | cons t r =>
    rw [decodeWit_cons] at h
    split_ifs at h with h0 h1
    · cases h
    · injection h with h; injection h with _ _ h3 h4
      subst h3 h4
      simp only [bytesAt, ByteArray.size, List.size_toArray, List.length_map, List.length_range]
      exact ⟨h1.2.1, h1.2.2⟩

/-- **`nodeParse` decides exactly the canonical node encodings** that the library's `decode`
reads. -/
theorem nodeParse_eq (π : Proof) : nodeParse π = nodeSpec π := by
  cases hp : nodeParse π with
  | some x =>
    obtain ⟨c₁, c₂, π₁, π₂⟩ := x
    obtain ⟨he, h₁, h₂⟩ := nodeParse_sound hp
    rw [nodeSpec, ← he, decode_encode _ (show (Wit.node c₁ c₂ π₁ π₂).Fits from ⟨h₁, h₂⟩)]
    simp
  | none =>
    unfold nodeSpec
    split
    · rename_i c₁ c₂ π₁ π₂ hd
      split_ifs with he
      · obtain ⟨h₁, h₂⟩ := decode_node_fits hd
        rw [← he, nodeParse_encode c₁ c₂ h₁ h₂] at hp
        cases hp
      · rfl
    · rfl

/-! ## Controls -/

/-- The linear decoder reads back the linear encoder on every witness that fits the format. -/
theorem decodeF_encodeF (w : Wit) (h : w.Fits) : decodeF (encodeF w) = some w := by
  rw [decodeF_eq, encodeF_eq, decode_encode w h]

/-- An unknown tag word decodes to nothing. -/
theorem decodeF_bad_tag : decodeF ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = none := by
  rw [decodeF_eq]; decide +kernel

end SpartanChain
