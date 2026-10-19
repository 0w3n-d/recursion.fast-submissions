/-
# Controls of the witness-sending baseline (BASELINE-TASK §6)

Kernel-checked; no proof here evaluates BLAKE2s. The library's controls of the image
(`RecursionFast.Controls.Extractor`: `ws_run_8`, `ws_fuel_7`, `halt_not_ws`) and of the rendered
claim (`RecursionFast.Controls.Certificate`: `ws_certificateR`, `flipped_image`, `fuel_7_claim`)
cover the image and the claim binding of the same image; they are cited, not imported.

Format (positive):
* `encode_leaf_kat`, `encode_node_kat`: known-answer bytes of `encode` on a small leaf and a small
  node, the bytes the native prover writes (`prover.py`, `smoke.py`'s known answers).
* `decode_leaf_kat`: the leaf's bytes decode back to the leaf.
Format and verifier (negative):
* `leaf_appended_rejected`, `leaf_truncated_rejected`, `node_appended_rejected`,
  `node_truncated_rejected`: one appended byte and one removed byte are rejected, on a leaf and on
  a node proof, whatever the statement (the canaries of DESIGN-v3 §6.3 step 7, before any hash).
* `bad_tag_rejected`: an unknown tag word is rejected.
* `stmt_unique`: a proof is accepted under at most one statement, so a flipped statement bit and
  a swapped child pair (`nodeStmt c₂ c₁ ≠ nodeStmt c₁ c₂`) are rejected.
* `leaf_over_chainCap`: a leaf proof of a chain longer than `chainCap` is rejected (before hashing).
* `node_children_capped`: an accepted node's children are within `proofCap` (the general form of
  "a child above `proofCap` is rejected"; `decodeWit` already reads such a child as `none`, the
  core's `decodeWit_long_child`).
Verifier (positive):
* `leaf_zero_accepted`: the honest proof of a zero-step leaf is accepted under its statement
  (from `check_encode`, no hash evaluated).
Claim binding (`CertificateR`, for this entry's `submission`):
* `certificateR`: the claim as `claim.json` declares it is certified (positive);
* `flipped_image`, `fuel_7_claim`, `fuel_over_budget_claim`: one image bit flipped, a declared fuel
  of 7, or one above the budget, is not (negative; the facts `check.sh`'s negative claims test on
  the rendered challenge).
Why the entry has its own verifier (negative, about the library's):
* `lib_leaf_appended`, `lib_leaf_truncated`, `lib_check_appended`, `lib_check_truncated`: the
  library's `decode` reads the leaf proof of `w₀` with one byte appended, or with its last byte
  removed, as the same leaf witness, so the library's `check` (which does not require the
  canonical encoding of a leaf) decides them as the original proof. Shown at `n = 16`; the argument
  holds for every `n < 2^56` (the removed byte is the top byte of the length word).
-/
import BaselineV3

namespace BaselineV3.Controls
open RecursionFast BaselineV3
open RecursionFast.WitnessSending (encode decode)

/-- The digest whose bytes are all `b`. -/
abbrev dg (b : UInt8) : Digest := Vector.replicate 32 b

/-- A small leaf witness: start `01…01`, length 16. -/
abbrev w₀ : Wit := .leaf (dg 1) 16

/-- `encode w₀`: tag word 0, the start, the length word. -/
theorem encode_leaf_kat : encode w₀ = ⟨#[0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    16, 0, 0, 0, 0, 0, 0, 0]⟩ := by decide +kernel

theorem decode_leaf_kat : decode (encode w₀) = some w₀ :=
  WitnessSending.decode_encode w₀ (show 16 < 2 ^ 64 by decide)

/-- A small node witness: children `02…02`, `03…03`, proofs `aa bb cc` and `dd`. -/
abbrev n₀ : Wit := .node (dg 2) (dg 3) ⟨#[0xaa, 0xbb, 0xcc]⟩ ⟨#[0xdd]⟩

/-- `encode n₀`: tag word 1, the two digests, each child proof as a length word and its bytes
zero-padded to a word. -/
theorem encode_node_kat : encode n₀ = ⟨#[1, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 0, 0, 0, 0, 0, 0, 0, 0xaa, 0xbb, 0xcc, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0xdd, 0, 0, 0, 0, 0, 0, 0]⟩ := by decide +kernel

/-! ## Strictness: the canaries that need no hash -/

/-- `π` with the byte `b` appended. -/
def appendByte (π : Proof) (b : UInt8) : Proof := π.push b

/-- `π` without its last byte. -/
def dropLast (π : Proof) : Proof := ⟨π.data.pop⟩

theorem leaf_appended_rejected : check (dg 0) (appendByte (encode w₀) 0) = false := by
  rw [check_eq]; decide +kernel

theorem leaf_truncated_rejected : check (dg 0) (dropLast (encode w₀)) = false := by
  rw [check_eq]; decide +kernel

theorem node_appended_rejected : check (dg 0) (appendByte (encode n₀) 0) = false := by
  rw [check_eq]; decide +kernel

theorem node_truncated_rejected : check (dg 0) (dropLast (encode n₀)) = false := by
  rw [check_eq]; decide +kernel

/-- The leaf's bytes with tag word 2. -/
theorem bad_tag_rejected :
    check (dg 0) ⟨#[2, 0, 0, 0, 0, 0, 0, 0] ++ (encode w₀).data.extract 8 48⟩ = false := by
  rw [check_eq]; decide +kernel

/-- A leaf proof of a chain of `chainCap + 1` steps is rejected, before any hash. -/
theorem leaf_over_chainCap : check (dg 0) (encode (.leaf (dg 1) (chainCap + 1))) = false := by
  rw [check_eq]; decide +kernel

/-! ## Binding: the canaries on the statement -/

/-- **A proof is accepted under at most one statement**: so not under a statement with a flipped
bit, nor, for a node, under the swapped pair `nodeStmt c₂ c₁` unless it equals `nodeStmt c₁ c₂`. -/
theorem stmt_unique {c c' : Digest} {π : Proof} (h : check c π = true) (h' : check c' π = true) :
    c = c' := by
  obtain ⟨w, hd, hR⟩ := check_sound h
  obtain ⟨w', hd', hR'⟩ := check_sound h'
  rw [hd] at hd'; cases hd'
  cases w with
  | leaf s n => exact hR.2.trans hR'.2.symm
  | node c₁ c₂ π₁ π₂ => exact hR.1.trans hR'.1.symm

/-- An accepted node proof's children are within `proofCap`. -/
theorem node_children_capped {c c₁ c₂ : Digest} {π π₁ π₂ : Proof} (h : check c π = true)
    (hd : decode π = some (.node c₁ c₂ π₁ π₂)) : π₁.size ≤ proofCap ∧ π₂.size ≤ proofCap := by
  obtain ⟨w, hd', hR⟩ := check_sound h
  rw [hd] at hd'; cases hd'
  exact fits_of_rel hR

/-- The honest proof of a zero-step leaf is accepted. -/
theorem leaf_zero_accepted (s : Digest) :
    check (leafStmt (chainEnd s 0) 0) (encode (.leaf s 0)) = true :=
  check_encode ⟨Nat.zero_le _, rfl⟩

/-! ## The claim binding -/

/-- The claim of `claim.json`: the image of `extractor.bin`, error `0`, no query, fuel 8. -/
def declared : Declared where
  img := ⟨[0x00100313, 0x03f31313, 0x02033583, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
    0x00000073], []⟩
  ε := 0
  qV := 0
  fuel _ := 8

theorem certificateR : CertificateR declared submission :=
  ⟨certificate, rfl, le_rfl, le_rfl,
    fun _ => ⟨le_rfl, Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40)⟩⟩

/-- The claim with bit 0 of the third instruction flipped. -/
def flipped : Declared :=
  { declared with
    img := ⟨[0x00100313, 0x03f31313, 0x02033582, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
      0x00000073], []⟩ }

theorem flipped_image : ¬ CertificateR flipped submission := fun h => by
  simpa [submission, WitnessSending.img, flipped] using h.img

theorem fuel_7_claim : ¬ CertificateR { declared with fuel := fun _ => 7 } submission :=
  fun h => absurd (h.bounds.2.2 0).1 (by simp [submission, WitnessSending.fuel])

theorem fuel_over_budget_claim :
    ¬ CertificateR { declared with fuel := fun _ => 2 ^ 41 } submission :=
  fun h => absurd (h.bounds.2.2 0).2 (by simp [extractorBudget])

/-! ## The library's verifier is not strict on leaves -/

deriving instance DecidableEq for Wit

theorem lib_leaf_appended : decode (appendByte (encode w₀) 0) = some w₀ := by decide +kernel

theorem lib_leaf_truncated : decode (dropLast (encode w₀)) = some w₀ := by decide +kernel

/-- Hence the library's `check` decides the appended and truncated leaf proofs as the original. -/
theorem lib_check_appended (c : Digest) :
    WitnessSending.check c (appendByte (encode w₀) 0) = WitnessSending.check c (encode w₀) := by
  rw [WitnessSending.check, WitnessSending.check, lib_leaf_appended, decode_leaf_kat]

theorem lib_check_truncated (c : Digest) :
    WitnessSending.check c (dropLast (encode w₀)) = WitnessSending.check c (encode w₀) := by
  rw [WitnessSending.check, WitnessSending.check, lib_leaf_truncated, decode_leaf_kat]

end BaselineV3.Controls
