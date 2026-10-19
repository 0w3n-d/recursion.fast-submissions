import RecursionFast.Contract.Relation
import Mathlib.Tactic.IntervalCases
import SpartanChainBlake2sCompress

/-!
# The chain block: one chain step of the contract as a block of `2 ^ 14` positions (L-C1)

BLUEPRINT-R1 §2.2. The chain step of the contract (`chainStep d = blake2sDigest (0x43 :: d)`, 33
bytes) is one compression of BLAKE2s: chaining value `h0` (`iv` with the parameter block
`0x01010020` of an unkeyed 32-byte digest), message block `block (0x43 :: d)`, counter `33`, flags
`0xFFFFFFFF` and `0` (`chainStep_eq`). The chain block is the BLAKE2s compression circuit
(`SpartanChainBlake2sCompress.lean`) with

* the constants fixed by rows: `h0` at `0 … 255`, the tag `0x43` at `640 … 647`, the zero message
  bytes `33 … 63` at `904 … 1151`, the counter `33` at `1152`, its high word and the last-node flag
  `0` at `1184`, `1248`, the last-block flag `0xFFFFFFFF` at `1216`. A position whose constant bit
  is `1` gets the row `(var 512, var 512)`, one whose bit is `0` the row `(0, 0)`
  (BLUEPRINT-R1 §2.2.1). In the `ProductCircuit` both are recorded as gates placed before the
  compression's (`constGates`), so that the circuit stays `Bounded`;
* the free inputs: the digest `d` being hashed, bits `648 … 903` (byte `e` bit `b` at
  `648 + 8 e + b`);
* the rest of `blake2sCircuit` unchanged: its 14 720 gates from `1280`, its output rows
  `(out bit, var 512)` at `256 … 511`, the constant at `512`, zero rows elsewhere.

Results:
* `block_sound` (L-C1): a Boolean block satisfying the chain block's R1CS over a nontrivial ring
  of characteristic two, with `1` at position `512`, carries at `256 … 511` the chain step of the
  digest it carries at `648 … 903`;
* `block_complete` (L-C1): the trace of a digest satisfies the R1CS, holds `1` at `512`, carries
  the digest at `648 … 903` and its chain step at `256 … 511`;
* the negative control `not_holds_flip`: flipping any output bit of a satisfying block (in
  particular of the honest trace) breaks the R1CS.
-/

namespace SpartanChain

open RecursionFast RecursionFast.Blake2s ProductCircuit

namespace Blake2sCircuit

/-! ## The chain step as one compression -/

/-- The chaining value of an unkeyed 32-byte BLAKE2s (RFC 7693 §2.5, §3.3): `iv` with the parameter
block `0x0101kknn`, `kk = 0`, `nn = 32`, XORed into word `0`. -/
def h0 : Vector UInt32 8 :=
  iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ (0 : ℕ).toUInt32 <<< 8 ^^^ (32 : ℕ).toUInt32)

/-- The 32-byte digest whose byte `e` is byte `e mod 4` of word `e / 4`, little-endian (the `le`
encoding of `blake2s`). -/
def leDigest (H : Vector UInt32 8) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ (H[e.val / 4] >>> (8 * (e.val % 4)).toUInt32).toUInt8

/-- The compression that a chain step is: chaining value `h0`, message block `0x43 ‖ d`, counter
`33`, the last-block flag set and the last-node flag clear. -/
def stepWords (d : Digest) : Vector UInt32 8 :=
  compress h0 (block (tagChain :: d.toList)) 33 0xFFFFFFFF 0

private theorem toList_eq_ofFn {α : Type} (H : Vector α 8) :
    H.toList = [H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.length_toList] at h1
  interval_cases i <;> simp

/-- One BLAKE2s-256 of an input of `1 … 64` bytes is one compression: the final block, counter the
input length, the last-block flag set. -/
theorem blake2s256_oneBlock (l : List UInt8) (h1 : 1 ≤ l.length) (h2 : l.length ≤ 64) :
    blake2s256 l = ((compress h0 (block l) l.length.toUInt64 0xFFFFFFFF 0).toList.flatMap
      (fun w : UInt32 ↦ [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
        (w >>> 24).toUInt8])).take 32 := by
  have h : (l.length - 1) / 64 = 0 := by omega
  simp only [blake2s256, blake2s, List.length_nil, ↓reduceIte, List.nil_append, h, compressInput,
    Nat.zero_add]
  rfl

/-- The chain step of the contract is one compression (`(33 - 1) / 64 = 0` blocks before the
final one), encoded little-endian. -/
theorem chainStep_eq (d : Digest) : chainStep d = leDigest (stepWords d) := by
  have hlen : (tagChain :: d.toList).length = 33 := by simp
  apply Vector.ext
  intro e he
  simp only [chainStep, blake2sDigest, Vector.getElem_mk, List.getElem_toArray]
  simp only [blake2s256_oneBlock _ (by rw [hlen]; omega) (by rw [hlen]; omega), hlen,
    toList_eq_ofFn]
  simp only [leDigest, Vector.getElem_ofFn, stepWords]
  interval_cases e <;> rfl

/-! ## Bits of bytes and words -/

/-- Bit `b < 8` of a byte of a word is a bit of the word. -/
theorem toUInt8_shiftRight_getLsbD (w : UInt32) (q b : ℕ) (hq : q < 4) (hb : b < 8) :
    ((w >>> (8 * q).toUInt32).toUInt8).toBitVec.getLsbD b = w.toBitVec.getLsbD (8 * q + b) := by
  simp [hb, Nat.mod_eq_of_lt (show 8 * q < 32 by omega)]

/-- Bit `b` of byte `e` of `leDigest H` is bit `8 (e mod 4) + b` of word `e / 4`. -/
theorem leDigest_getLsbD (H : Vector UInt32 8) (e : ℕ) (he : e < 32) (b : ℕ) (hb : b < 8) :
    (leDigest H)[e].toBitVec.getLsbD b =
      (H[e / 4]'(by omega)).toBitVec.getLsbD (8 * (e % 4) + b) := by
  rw [leDigest, Vector.getElem_ofFn]
  exact toUInt8_shiftRight_getLsbD _ _ _ (by omega) hb

/-- Bit `i` of message word `j` is bit `i mod 8` of byte `4 j + i / 8` of the input (zero past
its end), for an input of at most 64 bytes. -/
theorem block_getLsbD (l : List UInt8) (hl : l.length ≤ 64) (j : Fin 16) (i : ℕ) (hi : i < 32) :
    (block l)[j].toBitVec.getLsbD i = (l.getD (4 * j.val + i / 8) 0).toBitVec.getLsbD (i % 8) := by
  simp only [block, List.take_of_length_le hl]
  simp [hi]
  have ge : ∀ k, 8 ≤ k → ∀ x : UInt8, x.toBitVec.getLsbD k = false :=
    fun k hk x ↦ BitVec.getLsbD_of_ge _ _ hk
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h
  · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, show i < 16 by omega, show i < 24 by omega]
  · simp [ge i (by omega), show ¬ i < 8 by omega, h.2, show i < 24 by omega,
      show i / 8 = 1 by omega, show i % 8 = i - 8 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), show ¬ i < 8 by omega, show ¬ i < 16 by omega,
      h.2, show i / 8 = 2 by omega, show i % 8 = i - 16 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), ge (i - 16) (by omega), show ¬ i < 8 by omega,
      show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i / 8 = 3 by omega,
      show i % 8 = i - 24 by omega]

/-! ## Reading bytes and digests off a block -/

/-- The byte a block holds at the positions `b, …, b + 7`, low bit first. -/
def readByte (z : Pos m → Bool) (b : ℕ) : UInt8 := ⟨BitVec.ofFnLE fun i : Fin 8 ↦ z (pos (b + i))⟩

/-- The digest a block holds from position `b`: byte `e` bit `b'` at `b + 8 e + b'`. -/
def readDigest (z : Pos m → Bool) (b : ℕ) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ readByte z (b + 8 * e)

theorem readByte_getLsbD (z : Pos m → Bool) (b : ℕ) {i : ℕ} (hi : i < 8) :
    (readByte z b).toBitVec.getLsbD i = z (pos (b + i)) := by
  simp [readByte, BitVec.getLsbD_ofFnLE, hi]

theorem readDigest_getLsbD (z : Pos m → Bool) (b e : ℕ) (he : e < 32) {i : ℕ} (hi : i < 8) :
    (readDigest z b)[e].toBitVec.getLsbD i = z (pos (b + 8 * e + i)) := by
  rw [readDigest, Vector.getElem_ofFn, readByte_getLsbD _ _ hi]

/-- Two digests are equal when their bits are. -/
theorem digest_ext {d d' : Digest}
    (h : ∀ e (he : e < 32), ∀ i < 8, d[e].toBitVec.getLsbD i = d'[e].toBitVec.getLsbD i) :
    d = d' :=
  Vector.ext fun e he ↦ UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ h e he i hi)

/-- The digest a block holds depends only on its positions. -/
theorem readDigest_congr {z z' : Pos m → Bool} {b : ℕ}
    (h : ∀ e < 32, ∀ i < 8, z (pos (b + 8 * e + i)) = z' (pos (b + 8 * e + i))) :
    readDigest z b = readDigest z' b :=
  digest_ext fun e he i hi ↦ by
    rw [readDigest_getLsbD _ _ _ he hi, readDigest_getLsbD _ _ _ he hi, h e he i hi]

/-- A word denoted at the input positions `b, …, b + 31`, read bit by bit. -/
theorem den_inW_apply {z : Pos m → Bool} {b : ℕ} {u : UInt32} (h : Den z (inW b) u) {i : ℕ}
    (hi : i < 32) : z (pos (b + i)) = u.toBitVec.getLsbD i := by
  have := h ⟨i, hi⟩
  simpa [inW, eval_var] using this

/-! ## The constant positions -/

/-- The constant positions of the chain block: the chaining value `0 … 255`, the tag byte
`640 … 647`, and `904 … 1279` (message bytes `33 … 63`, the counter, the flags). -/
def constPositions : List ℕ :=
  (List.range 1280).filter fun k ↦ decide (k < 256 ∨ (640 ≤ k ∧ k < 648) ∨ 904 ≤ k)

theorem mem_constPositions {k : ℕ} :
    k ∈ constPositions ↔ k < 256 ∨ (640 ≤ k ∧ k < 648) ∨ (904 ≤ k ∧ k < 1280) := by
  simp only [constPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

/-- The bit a constant position must hold: `h0`, the tag `0x43`, zero message bytes, the counter
`33` (low word) and `0` (high word), the last-block flag `0xFFFFFFFF`, the last-node flag `0`. -/
def constBit (k : ℕ) : Bool :=
  if h : k < 256 then (h0[k / 32]'(by omega)).toBitVec.getLsbD (k % 32)
  else if k < 648 then tagChain.toBitVec.getLsbD (k - 640)
  else if k < 1152 then false
  else if k < 1184 then (33 : UInt32).toBitVec.getLsbD (k - 1152)
  else if k < 1216 then false
  else decide (k < 1248)

/-- The row of a constant position: `(var 512, var 512)` if its bit is `1`, `(0, 0)` if `0`. -/
def constGate (k : ℕ) : Pos m × Gate m :=
  (pos k, if constBit k then ⟨Form.var constPos, Form.var constPos⟩ else ⟨0, 0⟩)

/-- The constant rows, recorded as gates before the compression's. -/
def constGates : List (Pos m × Gate m) := constPositions.map constGate

/-- The free inputs of the chain block: the digest, bits `648 … 903`. -/
def chainInputs : Form m := BitVec.ofNat _ (2 ^ 256 - 1) <<< 648

theorem getLsbD_chainInputs (j : ℕ) : chainInputs.getLsbD j = decide (648 ≤ j ∧ j < 904) := by
  have h2 : 2 ^ m = 16384 := rfl
  unfold chainInputs
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, h2]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- The chain block: the constant rows, then `blake2sCircuit`'s gates and output rows, with the
digest bits `648 … 903` as the only inputs and `1` at `512`. Irreducible, so that no unification
evaluates it. -/
@[irreducible] noncomputable def chainBlock : ProductCircuit m :=
  { cpos := constPos, inputs := chainInputs, gates := constGates.toArray ++ blake2sCircuit.gates }

theorem chainBlock_cpos : chainBlock.cpos = constPos := by unfold chainBlock; rfl

theorem chainBlock_inputs : chainBlock.inputs = chainInputs := by unfold chainBlock; rfl

theorem chainBlock_gates : chainBlock.gates = constGates.toArray ++ blake2sCircuit.gates := by
  unfold chainBlock; rfl

/-! ## Boundedness -/

private theorem constPos_val' : (constPos : ℕ) = 512 := rfl

theorem availAfter_getLsbD (a : Form m) (L : List (Pos m × Gate m)) (j : ℕ) :
    (availAfter a L).getLsbD j = (a.getLsbD j || L.any fun kg ↦ decide ((kg.1 : ℕ) = j)) := by
  induction L generalizing a with
  | nil => simp [availAfter]
  | cons kg L ih =>
    change (availAfter (a ||| Form.var kg.1) L).getLsbD j = _
    rw [ih, BitVec.getLsbD_or, getLsbD_var, List.any_cons, Bool.or_assoc]

private theorem any_constGates (j : ℕ) :
    (constGates.any fun kg ↦ decide ((kg.1 : ℕ) = j)) = decide (j ∈ constPositions) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp only [constGates, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, he⟩
    have hk' := mem_constPositions.mp hk
    rw [constGate, pos_val (by show k < 16384; omega)] at he
    exact he ▸ hk
  · intro hj
    have hj' := mem_constPositions.mp hj
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [constGate, pos_val (by show j < 16384; omega)]⟩

/-- After the constant rows, exactly `blake2sCircuit`'s inputs and the constant are available. -/
theorem availAfter_constGates :
    availAfter (chainInputs ||| Form.var constPos) constGates = inputs ||| Form.var constPos := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [availAfter_getLsbD, any_constGates, BitVec.getLsbD_or, BitVec.getLsbD_or,
    getLsbD_chainInputs, getLsbD_inputs, getLsbD_var, constPos_val', Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_constPositions]
  omega

/-- The chain block is bounded: the constant rows read only the constant, at fresh distinct
positions, and after them `blake2sCircuit`'s gates see exactly its own start availability. -/
theorem bounded_chainBlock : chainBlock.Bounded := by
  rw [Bounded, chainBlock_inputs, chainBlock_cpos, chainBlock_gates, Array.toList_append,
    List.toList_toArray, boundedFrom_append, availAfter_constGates]
  have hc : (chainInputs ||| Form.var constPos).getLsbD (constPos : ℕ) = true := by
    simp only [BitVec.getLsbD_or, getLsbD_var, decide_true, Bool.or_true]
  -- `constGates` is generalised: elaborating `boundedFrom_of_nodup constGates` evaluates the list
  refine ⟨?_, ?_⟩
  · generalize hL : constGates = L
    refine boundedFrom_of_nodup L _ (fun kg hkg ↦ ?_) (fun kg hkg ↦ ?_) ?_
    all_goals subst hL
    · unfold constGates at hkg
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hkg
      have hv : Sub (Form.var constPos) (chainInputs ||| Form.var constPos) :=
        sub_iff.mpr fun j hj ↦ by
          rw [getLsbD_var, decide_eq_true_iff] at hj
          rw [← hj]; exact hc
      have h0' : Sub (0 : Form m) (chainInputs ||| Form.var constPos) :=
        sub_iff.mpr fun j hj ↦ by simp at hj
      unfold constGate
      split
      · exact ⟨hv, hv⟩
      · exact ⟨h0', h0'⟩
    · unfold constGates at hkg
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hkg
      have hk' := mem_constPositions.mp hk
      rw [constGate, BitVec.getLsbD_or, getLsbD_chainInputs, getLsbD_var, constPos_val',
        pos_val (by show k < 16384; omega)]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega
    · rw [constGates, List.map_map]
      refine List.Nodup.map_on (fun x hx y hy he ↦ ?_) ?_
      · have hx' := mem_constPositions.mp hx
        have hy' := mem_constPositions.mp hy
        have := congrArg Fin.val he
        simp only [Function.comp_apply, constGate] at this
        rwa [pos_val (by show x < 16384; omega), pos_val (by show y < 16384; omega)] at this
      · exact List.nodup_range.filter _
  · have := bounded_blake2s
    rwa [Bounded, blake2sCircuit_inputs, blake2sCircuit_cpos] at this

/-! ## Soundness (L-C1) -/

section Soundness

variable {z : Pos m → Bool}

/-- At a block where every gate of the chain block holds and position `512` holds `1`, every
constant position holds its constant. -/
theorem const_of_gates (hg : ∀ kg ∈ chainBlock.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z))
    (h1 : z constPos = true) {k : ℕ} (hk : k ∈ constPositions) : z (pos k) = constBit k := by
  have := hg (constGate k) (by
    rw [chainBlock_gates]
    exact Array.mem_append_left _ (List.mem_toArray.mpr (List.mem_map_of_mem hk)))
  by_cases hc : constBit k
  · simp only [constGate, hc, ↓reduceIte, eval_var, h1, Bool.and_self] at this
    rw [hc]; exact this
  · simp only [constGate, hc, Bool.false_eq_true, ↓reduceIte, eval_zero, Bool.and_self] at this
    rw [Bool.not_eq_true] at hc
    rw [hc]; exact this

/-- A word of constants is denoted where every gate holds. -/
private theorem den_const (hg : ∀ kg ∈ chainBlock.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z))
    (h1 : z constPos = true) {b : ℕ} {u : UInt32}
    (hb : ∀ i < 32, b + i ∈ constPositions ∧ constBit (b + i) = u.toBitVec.getLsbD i) :
    Den z (inW b) u :=
  den_inW fun i ↦ by rw [const_of_gates hg h1 (hb i i.isLt).1, (hb i i.isLt).2]

private theorem constBit_cv : ∀ k : Fin 8, ∀ i : Fin 32,
    constBit (32 * k.val + i.val) = h0[k].toBitVec.getLsbD i := by decide

private theorem constBit_tag : ∀ i : Fin 8, constBit (640 + i.val) = tagChain.toBitVec.getLsbD i := by
  decide

private theorem constBit_counter : ∀ i : Fin 32,
    constBit (1152 + i.val) = (33 : UInt32).toBitVec.getLsbD i ∧
    constBit (1184 + i.val) = (0 : UInt32).toBitVec.getLsbD i ∧
    constBit (1216 + i.val) = (0xFFFFFFFF : UInt32).toBitVec.getLsbD i ∧
    constBit (1248 + i.val) = (0 : UInt32).toBitVec.getLsbD i := by decide

private theorem constBit_zero {k : ℕ} (h1 : 904 ≤ k) (h2 : k < 1152) : constBit k = false := by
  unfold constBit
  rw [dif_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- The message words of a block where every gate holds: `block (0x43 ‖ d)` for the digest `d` the
block holds at `648 … 903`. -/
private theorem den_msg (hg : ∀ kg ∈ chainBlock.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z))
    (h1 : z constPos = true) (j : Fin 16) :
    Den z (msgW j) (block (tagChain :: (readDigest z 648).toList))[j] := by
  refine den_inW fun i ↦ ?_
  have hl : (tagChain :: (readDigest z 648).toList).length ≤ 64 := by simp
  rw [block_getLsbD _ hl j i i.isLt]
  have hj := j.isLt
  have hi := i.isLt
  rcases Nat.lt_or_ge (4 * j.val + i.val / 8) 33 with hp | hp
  · rcases Nat.eq_zero_or_pos (4 * j.val + i.val / 8) with h0' | h0'
    · have hi8 : i.val < 8 := by omega
      have hj0 : j.val = 0 := by omega
      rw [h0', List.getD_cons_zero, Nat.mod_eq_of_lt hi8, ← constBit_tag ⟨i.val, hi8⟩,
        ← const_of_gates hg h1 (mem_constPositions.mpr (by omega))]
      congr 2
      simp only [msgBase, hj0]
      all_goals omega
    · obtain ⟨q, hq⟩ : ∃ q, 4 * j.val + i.val / 8 = q + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos h0').symm⟩
      rw [hq, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega),
        Vector.getElem_toList, readDigest_getLsbD z 648 q (by omega) (Nat.mod_lt _ (by omega))]
      congr 2
      simp only [msgBase]
      omega
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp only [UInt8.toBitVec_zero, BitVec.getLsbD_zero]
    rw [const_of_gates hg h1 (mem_constPositions.mpr (by simp only [msgBase]; omega)),
      constBit_zero (by simp only [msgBase]; omega) (by simp only [msgBase]; omega)]

/-- The gate-level form of `block_sound`. -/
theorem block_sound_of_gates
    (hg : ∀ kg ∈ chainBlock.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z))
    (h1 : z constPos = true) : readDigest z 256 = chainStep (readDigest z 648) := by
  have hb : ∀ kg ∈ blake2sCircuit.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) :=
    fun kg h ↦ hg kg (by rw [chainBlock_gates]; exact Array.mem_append_right _ h)
  have hc := constBit_counter
  have hout := blake2s_sound_of_gates z hb h1 (h := h0) (t := 33) (f0 := 0xFFFFFFFF) (f1 := 0)
    (fun k ↦ den_const hg h1 fun i hi ↦
      ⟨mem_constPositions.mpr (by omega), constBit_cv k ⟨i, hi⟩⟩)
    (den_msg hg h1)
    (den_congr (den_const (b := 1152) hg h1 fun i hi ↦
      ⟨mem_constPositions.mpr (by omega), (hc ⟨i, hi⟩).1⟩) (by decide))
    (den_congr (den_const (b := 1184) hg h1 fun i hi ↦
      ⟨mem_constPositions.mpr (by omega), (hc ⟨i, hi⟩).2.1⟩) (by decide))
    (den_const (b := 1216) hg h1 fun i hi ↦
      ⟨mem_constPositions.mpr (by omega), (hc ⟨i, hi⟩).2.2.1⟩)
    (den_const (b := 1248) hg h1 fun i hi ↦
      ⟨mem_constPositions.mpr (by omega), (hc ⟨i, hi⟩).2.2.2⟩)
  rw [chainStep_eq]
  refine digest_ext fun e he i hi ↦ ?_
  rw [readDigest_getLsbD _ _ _ he hi, leDigest_getLsbD _ _ he _ hi, stepWords]
  have := den_inW_apply (hout ⟨e / 4, by omega⟩) (i := 8 * (e % 4) + i) (by omega)
  simp only [Fin.getElem_fin] at this
  rw [← this]
  congr 2
  first | omega | (simp only [Fin.val_mk]; omega)

/-- **L-C1, soundness.** A Boolean block satisfying the chain block's R1CS over a nontrivial ring
of characteristic two, with `1` at position `512`, carries at `256 … 511` the chain step of the
digest it carries at `648 … 903`. -/
theorem block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (z : Pos m → Bool)
    (hz : chainBlock.toBlockR1CS.Holds (liftBlock R z)) (h1 : z constPos = true) :
    readDigest z 256 = chainStep (readDigest z 648) :=
  block_sound_of_gates (gates_of_holds bounded_chainBlock z hz) h1

end Soundness

/-! ## Completeness (L-C1) -/

/-- The input block of a digest `d`: bit `b` of byte `e` at `648 + 8 e + b`, `0` elsewhere. -/
def chainInp (d : Digest) : Pos m → Bool := fun k ↦
  if h : 648 ≤ k.val ∧ k.val < 904 then
    (d[(k.val - 648) / 8]'(by omega)).toBitVec.getLsbD ((k.val - 648) % 8)
  else false

/-- The honest block of a chain step from `d`: the trace of the chain block on `d`. -/
noncomputable def chainTrace (d : Digest) : Pos m → Bool := chainBlock.traceF (chainInp d)

/-- The trace holds the digest it was given at `648 … 903`. -/
theorem readDigest_chainTrace (d : Digest) : readDigest (chainTrace d) 648 = d := by
  refine digest_ext fun e he i hi ↦ ?_
  have hv : 648 + 8 * e + i < 2 ^ m := by show _ < 16384; omega
  rw [readDigest_getLsbD _ _ _ he hi, chainTrace, traceF_input bounded_chainBlock _
    (by rw [chainBlock_inputs, getLsbD_chainInputs, pos_val hv]; simp; omega)
    (by rw [chainBlock_cpos]; intro h; have := congrArg Fin.val h; rw [pos_val hv] at this
        simp only [constPos_val'] at this; omega)]
  simp only [chainInp, pos_val hv]
  rw [dif_pos (by omega)]
  simp only [show (648 + 8 * e + i - 648) / 8 = e by omega,
    show (648 + 8 * e + i - 648) % 8 = i by omega]

/-- **L-C1, completeness.** Over a ring of characteristic two, the trace of a digest satisfies the
chain block's R1CS, holds `1` at `512`, carries the digest at `648 … 903` and its chain step at
`256 … 511`. -/
theorem block_complete {R : Type*} [CommRing R] [CharP R 2] (d : Digest) :
    chainBlock.toBlockR1CS.Holds (liftBlock R (chainTrace d)) ∧ chainTrace d constPos = true ∧
      readDigest (chainTrace d) 648 = d ∧ readDigest (chainTrace d) 256 = chainStep d := by
  have hs := trace_satisfies (R := R) bounded_chainBlock (chainInp d)
  have h1 : chainTrace d constPos = true := by
    rw [chainTrace, ← chainBlock_cpos]; exact traceF_cpos bounded_chainBlock _
  refine ⟨hs.1, h1, readDigest_chainTrace d, ?_⟩
  have hg := gates_of_rows bounded_chainBlock _ (trace_holds bounded_chainBlock (chainInp d))
  rw [← chainTrace] at hg
  rw [block_sound_of_gates hg h1, readDigest_chainTrace]

/-! ## Controls -/

/-- Negative control: flipping any output bit of a satisfying block breaks the R1CS (over a
nontrivial ring of characteristic two). With `block_complete`, this applies to every honest
trace. -/
theorem not_holds_flip {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (z : Pos m → Bool)
    (hz : chainBlock.toBlockR1CS.Holds (liftBlock R z)) (h1 : z constPos = true) (k : Pos m)
    (hk : 256 ≤ k.val ∧ k.val < 512) :
    ¬ chainBlock.toBlockR1CS.Holds (liftBlock R (Function.update z k (!z k))) := by
  intro hz'
  have hne : constPos ≠ k := fun h ↦ by have := congrArg Fin.val h; simp [constPos_val'] at this; omega
  have h1' : Function.update z k (!z k) constPos = true := by rw [Function.update_of_ne hne]; exact h1
  have hin : readDigest (Function.update z k (!z k)) 648 = readDigest z 648 :=
    readDigest_congr fun e he i hi ↦ by
      rw [Function.update_of_ne]
      intro h; have := congrArg Fin.val h; rw [pos_val (by show _ < 16384; omega)] at this; omega
  have hout := block_sound _ hz' h1'
  rw [hin, ← block_sound z hz h1] at hout
  have hb := congrArg (fun d : Digest ↦ (d[(k.val - 256) / 8]'(by omega)).toBitVec.getLsbD
    ((k.val - 256) % 8)) hout
  rw [readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega)),
    readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))] at hb
  have hp : (pos (256 + 8 * ((k.val - 256) / 8) + (k.val - 256) % 8) : Pos m) = k :=
    Fin.ext (by rw [pos_val (by show _ < 16384; omega)]; omega)
  simp only [hp, Function.update_self] at hb
  cases z k <;> simp at hb

/-- Positive known-answer control (kernel-checked): the chain step of the zero digest, i.e.
BLAKE2s-256 of `0x43 ‖ 0^32` (Python's `hashlib.blake2s`). -/
theorem chainStep_zero_kat : chainStep (Vector.replicate 32 0) =
    #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5, 0x9d, 0x21,
      0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd, 0x41, 0x8d, 0x8d]
    := by decide +kernel

/-- Positive control: the honest trace of the zero digest satisfies the chain block and carries
the known answer at its output positions. -/
theorem chainTrace_zero_kat {R : Type*} [CommRing R] [CharP R 2] :
    chainBlock.toBlockR1CS.Holds (liftBlock R (chainTrace (Vector.replicate 32 0))) ∧
      readDigest (chainTrace (Vector.replicate 32 0)) 256 =
        #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5, 0x9d, 0x21,
          0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd, 0x41, 0x8d, 0x8d] := by
  obtain ⟨h, -, -, ho⟩ := block_complete (R := R) (Vector.replicate 32 0)
  exact ⟨h, ho.trans chainStep_zero_kat⟩

end Blake2sCircuit

end SpartanChain
