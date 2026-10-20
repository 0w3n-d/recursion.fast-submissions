import SpartanChainFieldBase

/-!
# `F` agrees with CompPoly's `BF64`

`toBF64 : F → BF64` reads the word as CompPoly's `BitVec 64` coordinates. It is a bijection
(`equivBF64`) that commutes with every operation, and `F` is a field through it.

## Main statements

* `toBF64_add`, `toBF64_mul`, `toBF64_sq`, `toBF64_inv`: the word operations are `BF64`'s.
* `ringEquivBF64 : F ≃+* BF64`: the bijection as a ring isomorphism.
* `instField`: `F` is a field, with computable word operations.
* `card_F`: every enumeration of `F` has `2 ^ 64` elements.
* `toBytes_eq`, `ofBytes_eq`: the byte codec is `ByteCodec BF64`'s.

## How the product is proved

`mulLoop` is proved against CompPoly's specification, not against its `carryLessMul`: every word
denotes a polynomial over `ZMod 2` (CompPoly's `toPoly`), and the loop keeps the polynomial
`lo + x^64 hi + a (bl + x^64 bh)` invariant (`mulStep_inv`); `reduce` maps `lo + x^64 hi` to the
same class of `AdjoinRoot basePoly` (`mk_reduce`). The class map is CompPoly's `BF64.toQuot`,
which is injective and multiplicative (`BF64.toQuot_injective`, `BF64.toQuot_mul`), so the word
product is `BF64`'s product.
-/

namespace SpartanChain.F

open Polynomial BinaryField

/-! ## The map to `BF64` -/

/-- The `BF64` element with the same polynomial-basis bits. -/
def toBF64 (a : F) : BF64 := BF64.ofBitVec a.val.toBitVec

/-- The `F` element with the same polynomial-basis bits. -/
def ofBF64 (a : BF64) : F := ⟨UInt64.ofBitVec a.toBitVec⟩

@[simp] theorem toBF64_ofBF64 (a : BF64) : toBF64 (ofBF64 a) = a := rfl

@[simp] theorem ofBF64_toBF64 (a : F) : ofBF64 (toBF64 a) = a := rfl

/-- `F` and `BF64` are in bijection by their common coordinates. -/
def equivBF64 : F ≃ BF64 where
  toFun := toBF64
  invFun := ofBF64
  left_inv := ofBF64_toBF64
  right_inv := toBF64_ofBF64

theorem toBF64_injective : Function.Injective toBF64 := equivBF64.injective

theorem toBF64_inj {a b : F} : toBF64 a = toBF64 b ↔ a = b := toBF64_injective.eq_iff

/-! ## Words as polynomials (proof helpers) -/

/-- The polynomial over `ZMod 2` denoted by a word, CompPoly's `toPoly`. -/
noncomputable abbrev P (x : UInt64) : (ZMod 2)[X] := toPoly x.toBitVec

/-- The class of a word in `AdjoinRoot basePoly`, which is `BF64.toQuot` of its `BF64`. -/
noncomputable abbrev Q (x : UInt64) : BF64.BF64Quot := AdjoinRoot.mk BF64.basePoly (P x)

theorem toQuot_toBF64 (a : F) : BF64.toQuot (toBF64 a) = Q a.val := rfl

private theorem coeff_toPoly (x : BitVec 64) (n : ℕ) :
    (toPoly x).coeff n = if x.getLsbD n then 1 else 0 := by
  rw [toPoly_coeff]
  by_cases h : n < 64
  · simp [h, BitVec.getLsb, BitVec.getLsbD]
  · simp [h, BitVec.getLsbD_of_ge x n (by omega)]

/-- Multiplying by `x^k` splits into the truncated left shift and the bits shifted out. -/
private theorem toPoly_mul_X_pow (x : BitVec 64) (k : ℕ) (hk : k ≤ 64) :
    toPoly x * X ^ k = toPoly (x <<< k) + X ^ 64 * toPoly (x >>> (64 - k)) := by
  ext n
  simp only [coeff_add, coeff_mul_X_pow', coeff_X_pow_mul', coeff_toPoly,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h64 : 64 ≤ n
  · have : ¬ n < 64 := by omega
    have e : 64 - k + (n - 64) = n - k := by omega
    simp [h64, this, e, show k ≤ n by omega]
  · by_cases hkn : k ≤ n <;> simp [h64, hkn, show n < 64 by omega]

/-- The low bit splits off a word: `a = x * (a >>> 1) + (a &&& 1)`. -/
private theorem toPoly_split_low (a : BitVec 64) :
    toPoly a = toPoly (a >>> 1) * X + toPoly (a &&& 1#64) := by
  ext n
  rcases n with _ | n
  · simp [coeff_toPoly]
  · simp [coeff_toPoly, BitVec.getLsbD_and, BitVec.getLsbD_one, coeff_mul_X,
      BitVec.getLsbD_ushiftRight, Nat.add_comm 1 n]

private theorem P_xor (x y : UInt64) : P (x ^^^ y) = P x + P y := by
  simp [P, toPoly_xor]

private theorem P_zero : P 0 = 0 := toPoly_zero_eq_zero

/-- `toPoly_mul_X_pow` for words; the caller supplies the two shifts as `BitVec` shifts. -/
private theorem P_shiftLeft (x : UInt64) (k : ℕ) (hk : k ≤ 64) {s r : UInt64}
    (hs : (x <<< s).toBitVec = x.toBitVec <<< k)
    (hr : (x >>> r).toBitVec = x.toBitVec >>> (64 - k)) :
    P (x <<< s) = P x * X ^ k - X ^ 64 * P (x >>> r) := by
  have h := toPoly_mul_X_pow x.toBitVec k hk
  simp only [P, hs, hr]
  linear_combination (-1 : (ZMod 2)[X]) * h

/-- The mask `0 - (a &&& 1)` selects `x` exactly when bit `0` of `a` is set. -/
private theorem and_mask (a x : UInt64) :
    x &&& (0 - (a &&& 1)) = if a.toBitVec.getLsbD 0 then x else 0 := by
  have h : (a &&& 1).toNat = a.toNat % 2 := by simp [UInt64.toNat_and, Nat.and_one_is_mod]
  have hb : a.toBitVec.getLsbD 0 = decide (a.toNat % 2 = 1) := by
    simp [BitVec.getLsbD, Nat.testBit_zero]
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h0 | h1
  · have : a &&& 1 = 0 := UInt64.toNat_inj.mp (by simp [h, h0])
    simp [this, h0]
  · have : a &&& 1 = 1 := UInt64.toNat_inj.mp (by simp [h, h1])
    simp [this, h1]

/-! ## The product loop -/

/-- The polynomial a product state stands for: the accumulator plus what is left to add. -/
private noncomputable def Φ (s : MulState) : (ZMod 2)[X] :=
  P s.lo + X ^ 64 * P s.hi + P s.a * (P s.bl + X ^ 64 * P s.bh)

/-- The bounds that keep the shifted multiplicand inside 128 bits: `r` bits of `a` are left. -/
private def Good (r : ℕ) (s : MulState) : Prop := s.a.toNat < 2 ^ r ∧ s.bh.toNat < 2 ^ (64 - r)

/-- One step keeps the denoted polynomial, provided the top bit of `bh` is clear. -/
private theorem mulStep_inv (s : MulState) (h : s.bh.toNat < 2 ^ 63) :
    Φ (mulStep s) = Φ s := by
  have hbh : s.bh >>> 63 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simpa using h
  have e1 := P_shiftLeft s.bl 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have e2 := P_shiftLeft s.bh 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have hand : s.a.toBitVec &&& 1#64 = if s.a.toBitVec.getLsbD 0 then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases i with _ | i
    · split_ifs with h <;> simp_all [BitVec.getLsbD_eq_getElem]
    · split_ifs <;> simp
  have ea : P s.a = P (s.a >>> 1) * X + if s.a.toBitVec.getLsbD 0 then 1 else 0 := by
    have h1 : toPoly (1#64) = 1 := toPoly_one_eq_one (by norm_num)
    have hA : (s.a >>> 1).toBitVec = s.a.toBitVec >>> 1 := by simp
    simp only [P, hA]
    rw [toPoly_split_low s.a.toBitVec, hand]
    split_ifs <;> simp [h1, toPoly_zero_eq_zero]
  simp only [Φ, mulStep, P_xor, and_mask, hbh, P_zero, mul_zero, sub_zero] at e2 ⊢
  rw [e1, e2, ea]
  split_ifs <;> (try simp only [P_zero]) <;> ring

/-- One step uses up one bit of `a` and keeps the multiplicand inside 128 bits. -/
private theorem mulStep_good {r : ℕ} {s : MulState} (h : Good (r + 1) s) (hr : r < 64) :
    Good r (mulStep s) ∧ Φ (mulStep s) = Φ s := by
  obtain ⟨ha, hb⟩ := h
  have hb63 : s.bh.toNat < 2 ^ 63 :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨⟨?_, ?_⟩, mulStep_inv s hb63⟩
  · simp only [mulStep, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    simpa [pow_succ] using ha
  · simp only [mulStep, UInt64.toNat_xor, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    refine Nat.xor_lt_two_pow ?_ ?_
    · refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
      have : 64 - r = (64 - (r + 1)) + 1 := by omega
      rw [this, pow_succ]
      simpa using hb
    · have : s.bl.toNat / 2 ^ 63 < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact s.bl.toNat_lt
      exact lt_of_lt_of_le this
        (by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ 64 - r by omega))

/-! ## The reduction -/

/-- The bits of `reduce`'s fold word `d` above position 60 are those of `hi`. -/
private theorem fold_shiftRight (hi : UInt64) (s : UInt64) (hs : 60 ≤ s.toNat) (hs' : s.toNat < 64) :
    (hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)) >>> s = hi >>> s := by
  have key : ∀ x : UInt64, (x >>> s).toBitVec = x.toBitVec >>> s.toNat := by
    intro x; simp [Nat.mod_eq_of_lt hs']
  apply UInt64.toBitVec_inj.mp
  rw [key, key]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have k63 : (hi >>> 63).toBitVec = hi.toBitVec >>> 63 := by simp
  have k61 : (hi >>> 61).toBitVec = hi.toBitVec >>> 61 := by simp
  have k60 : (hi >>> 60).toBitVec = hi.toBitVec >>> 60 := by simp
  rw [k63, k61, k60]
  simp only [BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge _ (63 + (s.toNat + i)) (by omega),
    BitVec.getLsbD_of_ge _ (61 + (s.toNat + i)) (by omega),
    BitVec.getLsbD_of_ge _ (60 + (s.toNat + i)) (by omega)]
  simp

/-- `reduce lo hi` is the class of `lo + x^64 hi` modulo the `GF(2^64)` modulus. -/
theorem mk_reduce (lo hi : UInt64) : Q (reduce lo hi) = AdjoinRoot.mk BF64.basePoly
    (P lo + X ^ 64 * P hi) := by
  set d := hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60) with hd
  have e1 := P_shiftLeft d 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have e3 := P_shiftLeft d 3 (by norm_num) (s := 3) (r := 61) (by simp) (by simp)
  have e4 := P_shiftLeft d 4 (by norm_num) (s := 4) (r := 60) (by simp) (by simp)
  rw [fold_shiftRight hi 63 (by decide) (by decide)] at e1
  rw [fold_shiftRight hi 61 (by decide) (by decide)] at e3
  rw [fold_shiftRight hi 60 (by decide) (by decide)] at e4
  have ed : P d = P hi + P (hi >>> 63) + P (hi >>> 61) + P (hi >>> 60) := by
    simp only [hd, P_xor]
  have er : P (reduce lo hi) = P lo + P d + P (d <<< 1) + P (d <<< 3) + P (d <<< 4) := by
    simp only [reduce, P_xor, hd]
  rw [Q, er, e1, e3, e4, ed, AdjoinRoot.mk_eq_mk, BF64.basePoly_eq]
  refine ⟨-(P hi + P (hi >>> 63) + P (hi >>> 61) + P (hi >>> 60)), ?_⟩
  linear_combination ((X ^ 4 + X ^ 3 + X + 1) * (P hi + P (hi >>> 63) + P (hi >>> 61) +
    P (hi >>> 60))) * ZMod2Poly.two_eq_zero

/-! ## The product -/

/-- `n` rounds of the loop compute the class of the polynomial the start state stands for. -/
private theorem mulLoop_spec (n : ℕ) (a bl bh lo hi : UInt64) (hn : 4 * n ≤ 64)
    (h : Good (4 * n) ⟨a, bl, bh, lo, hi⟩) :
    Q (mulLoop n a bl bh lo hi) = AdjoinRoot.mk BF64.basePoly (Φ ⟨a, bl, bh, lo, hi⟩) := by
  induction n generalizing a bl bh lo hi with
  | zero =>
    have ha : a = 0 := UInt64.toNat_inj.mp (by simpa [Good] using h.1)
    simp [mulLoop, mk_reduce, Φ, ha, P_zero]
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 3 + 1 by ring] at h
    obtain ⟨g1, e1⟩ := mulStep_good h (by omega)
    obtain ⟨g2, e2⟩ := mulStep_good g1 (by omega)
    obtain ⟨g3, e3⟩ := mulStep_good g2 (by omega)
    obtain ⟨g4, e4⟩ := mulStep_good g3 (by omega)
    rw [mulLoop]
    set s4 := mulStep (mulStep (mulStep (mulStep ⟨a, bl, bh, lo, hi⟩)))
    exact (ih s4.a s4.bl s4.bh s4.lo s4.hi (by omega) g4).trans
      (congrArg _ (e4.trans (e3.trans (e2.trans e1))))

/-- The class of the word product is the product of the classes. -/
theorem Q_mul (a b : F) : Q (a * b).val = Q a.val * Q b.val := by
  change Q (mulLoop 16 a.val b.val 0 0 0) = _
  rw [mulLoop_spec 16 _ _ _ _ _ (by norm_num) ⟨a.val.toNat_lt, by simp⟩, ← map_mul]
  simp [Φ, P_zero]

/-- **Multiplication is `BF64`'s.** -/
@[simp] theorem toBF64_mul (a b : F) : toBF64 (a * b) = toBF64 a * toBF64 b := by
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul, toQuot_toBF64, toQuot_toBF64, toQuot_toBF64, Q_mul]

/-! ## Squaring -/

/-! ### `spread`, one mask-and-shift step at a time

After the steps down to chunk size `c`, bit `j` of the word is bit `j / (2c) * c + j % (2c)` of
the input when `j % (2c) < c`, and `0` otherwise (`c = 32` after the first mask, `c = 1` at the
end). Each step is one lemma whose index arithmetic is linear, closed by `omega`; the masks are
read off by `decide` over the 64 bit positions. -/

private theorem mask32 : ∀ j < 64,
    (0x00000000FFFFFFFF : UInt64).toBitVec.getLsbD j = decide (j % 64 < 32) := by
  decide +kernel

private theorem spread_stage32 (x : UInt64) : ∀ j < 64,
    (x &&& 0x00000000FFFFFFFF).toBitVec.getLsbD j =
      (decide (j % 64 < 32) && x.toBitVec.getLsbD (j / 64 * 32 + j % 64)) := by
  intro j hj
  simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, mask32 j hj, Nat.mod_eq_of_lt hj,
    Nat.div_eq_of_lt hj, Nat.zero_mul, Nat.zero_add]
  exact Bool.and_comm _ _

private theorem mask16 : ∀ j < 64, (0x0000FFFF0000FFFF : UInt64).toBitVec.getLsbD j = decide (j % 32 < 16) := by
  decide +kernel

private theorem spread_stage16 (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % 64 < 32) && x.toBitVec.getLsbD (j / 64 * 32 + j % 64))) :
    ∀ j < 64, ((y ||| (y <<< 16)) &&& 0x0000FFFF0000FFFF).toBitVec.getLsbD j =
      (decide (j % 32 < 16) && x.toBitVec.getLsbD (j / 32 * 16 + j % 32)) := by
  intro j hj
  have hs : (y <<< 16).toBitVec = y.toBitVec <<< 16 := by simp
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hs, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, mask16 j hj, hy j hj]
  by_cases hm : j % 32 < 16
  · by_cases ht : j % 64 < 32
    · have e : j / 64 * 32 + j % 64 = j / 32 * 16 + j % 32 := by omega
      by_cases hh : j < 16
      · simp [hm, ht, e, hh, hj]
      · rw [hy (j - 16) (by omega)]
        have : ¬ (j - 16) % 64 < 32 := by omega
        simp [hm, ht, e, hh, hj, this]
    · have hh : ¬ j < 16 := by omega
      rw [hy (j - 16) (by omega)]
      have e : (j - 16) / 64 * 32 + (j - 16) % 64 = j / 32 * 16 + j % 32 := by omega
      have : (j - 16) % 64 < 32 := by omega
      simp [hm, ht, e, hh, hj, this]
  · simp [hm]

private theorem mask8 : ∀ j < 64, (0x00FF00FF00FF00FF : UInt64).toBitVec.getLsbD j = decide (j % 16 < 8) := by
  decide +kernel

private theorem spread_stage8 (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % 32 < 16) && x.toBitVec.getLsbD (j / 32 * 16 + j % 32))) :
    ∀ j < 64, ((y ||| (y <<< 8)) &&& 0x00FF00FF00FF00FF).toBitVec.getLsbD j =
      (decide (j % 16 < 8) && x.toBitVec.getLsbD (j / 16 * 8 + j % 16)) := by
  intro j hj
  have hs : (y <<< 8).toBitVec = y.toBitVec <<< 8 := by simp
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hs, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, mask8 j hj, hy j hj]
  by_cases hm : j % 16 < 8
  · by_cases ht : j % 32 < 16
    · have e : j / 32 * 16 + j % 32 = j / 16 * 8 + j % 16 := by omega
      by_cases hh : j < 8
      · simp [hm, ht, e, hh, hj]
      · rw [hy (j - 8) (by omega)]
        have : ¬ (j - 8) % 32 < 16 := by omega
        simp [hm, ht, e, hh, hj, this]
    · have hh : ¬ j < 8 := by omega
      rw [hy (j - 8) (by omega)]
      have e : (j - 8) / 32 * 16 + (j - 8) % 32 = j / 16 * 8 + j % 16 := by omega
      have : (j - 8) % 32 < 16 := by omega
      simp [hm, ht, e, hh, hj, this]
  · simp [hm]

private theorem mask4 : ∀ j < 64, (0x0F0F0F0F0F0F0F0F : UInt64).toBitVec.getLsbD j = decide (j % 8 < 4) := by
  decide +kernel

private theorem spread_stage4 (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % 16 < 8) && x.toBitVec.getLsbD (j / 16 * 8 + j % 16))) :
    ∀ j < 64, ((y ||| (y <<< 4)) &&& 0x0F0F0F0F0F0F0F0F).toBitVec.getLsbD j =
      (decide (j % 8 < 4) && x.toBitVec.getLsbD (j / 8 * 4 + j % 8)) := by
  intro j hj
  have hs : (y <<< 4).toBitVec = y.toBitVec <<< 4 := by simp
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hs, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, mask4 j hj, hy j hj]
  by_cases hm : j % 8 < 4
  · by_cases ht : j % 16 < 8
    · have e : j / 16 * 8 + j % 16 = j / 8 * 4 + j % 8 := by omega
      by_cases hh : j < 4
      · simp [hm, ht, e, hh, hj]
      · rw [hy (j - 4) (by omega)]
        have : ¬ (j - 4) % 16 < 8 := by omega
        simp [hm, ht, e, hh, hj, this]
    · have hh : ¬ j < 4 := by omega
      rw [hy (j - 4) (by omega)]
      have e : (j - 4) / 16 * 8 + (j - 4) % 16 = j / 8 * 4 + j % 8 := by omega
      have : (j - 4) % 16 < 8 := by omega
      simp [hm, ht, e, hh, hj, this]
  · simp [hm]

private theorem mask2 : ∀ j < 64, (0x3333333333333333 : UInt64).toBitVec.getLsbD j = decide (j % 4 < 2) := by
  decide +kernel

private theorem spread_stage2 (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % 8 < 4) && x.toBitVec.getLsbD (j / 8 * 4 + j % 8))) :
    ∀ j < 64, ((y ||| (y <<< 2)) &&& 0x3333333333333333).toBitVec.getLsbD j =
      (decide (j % 4 < 2) && x.toBitVec.getLsbD (j / 4 * 2 + j % 4)) := by
  intro j hj
  have hs : (y <<< 2).toBitVec = y.toBitVec <<< 2 := by simp
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hs, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, mask2 j hj, hy j hj]
  by_cases hm : j % 4 < 2
  · by_cases ht : j % 8 < 4
    · have e : j / 8 * 4 + j % 8 = j / 4 * 2 + j % 4 := by omega
      by_cases hh : j < 2
      · simp [hm, ht, e, hh, hj]
      · rw [hy (j - 2) (by omega)]
        have : ¬ (j - 2) % 8 < 4 := by omega
        simp [hm, ht, e, hh, hj, this]
    · have hh : ¬ j < 2 := by omega
      rw [hy (j - 2) (by omega)]
      have e : (j - 2) / 8 * 4 + (j - 2) % 8 = j / 4 * 2 + j % 4 := by omega
      have : (j - 2) % 8 < 4 := by omega
      simp [hm, ht, e, hh, hj, this]
  · simp [hm]

private theorem mask1 : ∀ j < 64, (0x5555555555555555 : UInt64).toBitVec.getLsbD j = decide (j % 2 < 1) := by
  decide +kernel

private theorem spread_stage1 (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % 4 < 2) && x.toBitVec.getLsbD (j / 4 * 2 + j % 4))) :
    ∀ j < 64, ((y ||| (y <<< 1)) &&& 0x5555555555555555).toBitVec.getLsbD j =
      (decide (j % 2 < 1) && x.toBitVec.getLsbD (j / 2 * 1 + j % 2)) := by
  intro j hj
  have hs : (y <<< 1).toBitVec = y.toBitVec <<< 1 := by simp
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hs, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, mask1 j hj, hy j hj]
  by_cases hm : j % 2 < 1
  · by_cases ht : j % 4 < 2
    · have e : j / 4 * 2 + j % 4 = j / 2 * 1 + j % 2 := by omega
      by_cases hh : j < 1
      · simp [hm, ht, e, hh, hj]
      · rw [hy (j - 1) (by omega)]
        have : ¬ (j - 1) % 4 < 2 := by omega
        simp [hm, ht, e, hh, hj, this]
    · have hh : ¬ j < 1 := by omega
      rw [hy (j - 1) (by omega)]
      have e : (j - 1) / 4 * 2 + (j - 1) % 4 = j / 2 * 1 + j % 2 := by omega
      have : (j - 1) % 4 < 2 := by omega
      simp [hm, ht, e, hh, hj, this]
  · simp [hm]

/-- `spread` moves bit `i` of the low half to bit `2 i` and clears the odd bits. -/
private theorem spread_getLsbD (x : UInt64) (j : ℕ) (hj : j < 64) :
    (spread x).toBitVec.getLsbD j = (decide (j % 2 = 0) && x.toBitVec.getLsbD (j / 2)) := by
  have h := spread_stage1 x _ (spread_stage2 x _ (spread_stage4 x _ (spread_stage8 x _
    (spread_stage16 x _ (spread_stage32 x))))) j hj
  have e : j / 2 * 1 + j % 2 = j / 2 + j % 2 := by omega
  rw [e] at h
  change _ = _ at h
  unfold spread
  rw [h]
  by_cases h2 : j % 2 = 0
  · simp [h2]
  · simp [show ¬ j % 2 < 1 by omega, h2]

/-- In characteristic two the square of a word's polynomial spreads its bits. -/
private theorem P_spread (a : UInt64) :
    P (spread a) + X ^ 64 * P (spread (a >>> 32)) = P a ^ 2 := by
  rw [← ZMod.expand_card]
  ext n
  simp only [coeff_add, coeff_X_pow_mul', coeff_expand (by norm_num : 0 < 2), P, coeff_toPoly]
  have hs : ((a >>> 32).toBitVec) = a.toBitVec >>> 32 := by simp
  by_cases h64 : n < 64
  · simp only [spread_getLsbD a n h64, show ¬ 64 ≤ n by omega, ite_false, add_zero]
    by_cases h2 : n % 2 = 0
    · simp [h2, Nat.dvd_iff_mod_eq_zero]
    · simp [h2, Nat.dvd_iff_mod_eq_zero]
  · by_cases h128 : n < 128
    · simp only [spread_getLsbD _ (n - 64) (by omega), show 64 ≤ n by omega, ite_true, hs,
        BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ n (by omega : 64 ≤ n),
        Bool.false_eq_true, ite_false, zero_add]
      have e : 32 + (n - 64) / 2 = n / 2 := by omega
      by_cases h2 : n % 2 = 0
      · simp [h2, Nat.dvd_iff_mod_eq_zero, e, show (n - 64) % 2 = 0 by omega]
      · simp [h2, Nat.dvd_iff_mod_eq_zero, show (n - 64) % 2 ≠ 0 by omega]
    · simp only [BitVec.getLsbD_of_ge _ n (by omega : 64 ≤ n),
        BitVec.getLsbD_of_ge _ (n - 64) (by omega : 64 ≤ n - 64), show 64 ≤ n by omega,
        Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [BitVec.getLsbD_of_ge _ (n / 2) (by omega)]
      simp

/-- **Squaring is `BF64`'s.** -/
@[simp] theorem toBF64_sq (a : F) : toBF64 (sq a) = toBF64 a * toBF64 a := by
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul, toQuot_toBF64, toQuot_toBF64]
  change Q (reduce _ _) = _
  rw [mk_reduce, P_spread, map_pow, _root_.sq]

/-! ## Addition, constants, powers and the inverse -/

@[simp] theorem toBF64_zero : toBF64 0 = 0 := rfl

@[simp] theorem toBF64_one : toBF64 1 = 1 := rfl

/-- **Addition is `BF64`'s.** -/
@[simp] theorem toBF64_add (a b : F) : toBF64 (a + b) = toBF64 a + toBF64 b := by
  apply BF64.ext
  simp [toBF64, HAdd.hAdd, Add.add, add]

@[simp] theorem toBF64_neg (a : F) : toBF64 (-a) = -toBF64 a := rfl

@[simp] theorem toBF64_sub (a b : F) : toBF64 (a - b) = toBF64 a - toBF64 b := by
  apply BF64.ext
  simp [toBF64, HSub.hSub, Sub.sub, add, BF64.ofBitVec]

theorem toBF64_eq_zero {a : F} : toBF64 a = 0 ↔ a.val = 0 := by
  rw [← toBF64_zero, toBF64_inj]
  exact ⟨fun h => h ▸ rfl, fun h => by cases a; cases h; rfl⟩

@[simp] theorem toBF64_frob (k : ℕ) (a : F) :
    toBF64 (frob k a) = BF64.powTwoPow (toBF64 a) k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [frob, BF64.powTwoPow, ih, toBF64_sq]

/-- **The inverse is `BF64`'s Itoh-Tsujii inverse.** -/
@[simp] theorem toBF64_inv (a : F) : toBF64 a⁻¹ = (toBF64 a)⁻¹ := by
  change toBF64 (inv a) = BF64.invItohTsujii (toBF64 a)
  by_cases h : a.val = 0
  · have h' := toBF64_eq_zero.mpr h
    simp only [inv, h, ↓reduceIte, BF64.invItohTsujii, h']
    rfl
  · have h' : ¬ toBF64 a = 0 := fun h' => h (toBF64_eq_zero.mp h')
    simp only [inv, h, ↓reduceIte, BF64.invItohTsujii, h', toBF64_mul, toBF64_frob,
      toBF64_sq]

/-! ## The field structure, transported from `BF64` -/

instance : SMul ℕ F := ⟨nsmulRec⟩
instance : SMul ℤ F := ⟨zsmulRec nsmulRec⟩

/-- Cast a natural number by its parity, as `BF64.natCast`. -/
@[inline] def natCast (n : ℕ) : F := if n % 2 = 0 then 0 else 1

instance : NatCast F := ⟨natCast⟩
instance : IntCast F := ⟨Int.castDef⟩

@[simp] theorem toBF64_natCast (n : ℕ) : toBF64 (n : F) = (n : BF64) := by
  change toBF64 (natCast n) = BF64.natCast n
  unfold natCast BF64.natCast
  split_ifs <;> rfl

@[simp] theorem toBF64_intCast (n : ℤ) : toBF64 (n : F) = (n : BF64) := by
  rcases n with n | n
  · exact toBF64_natCast n
  · change toBF64 (-((n + 1 : ℕ) : F)) = -((n + 1 : ℕ) : BF64)
    rw [toBF64_neg, toBF64_natCast]

theorem toBF64_nsmul (n : ℕ) (a : F) : toBF64 (n • a) = n • toBF64 a := by
  change toBF64 (nsmulRec n a) = nsmulRec n (toBF64 a)
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulRec, toBF64_add, ih]

theorem toBF64_zsmul (n : ℤ) (a : F) : toBF64 (n • a) = n • toBF64 a := by
  rcases n with n | n
  · exact toBF64_nsmul n a
  · change toBF64 (-(nsmulRec (n + 1) a)) = -(nsmulRec (n + 1) (toBF64 a))
    rw [toBF64_neg]
    exact congrArg _ (toBF64_nsmul (n + 1) a)

theorem toBF64_powGo (k : ℕ) (b : F) (e : ℕ) (acc : F) (he : e ≤ k) :
    toBF64 (powGo k b e acc) = toBF64 acc * toBF64 b ^ e := by
  induction k generalizing b e acc with
  | zero => obtain rfl : e = 0 := by omega
            simp [powGo]
  | succ k ih =>
    rw [powGo]
    split_ifs with h0 ho
    · simp [h0]
    · rw [ih _ _ _ (by omega)]; simp only [toBF64_mul, toBF64_sq]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by omega, pow_succ, pow_mul, _root_.sq]
      ring
    · rw [ih _ _ _ (by omega), toBF64_sq]
      conv_rhs => rw [show e = 2 * (e / 2) by omega, pow_mul, _root_.sq]

theorem toBF64_npow (a : F) (n : ℕ) : toBF64 (a ^ n) = toBF64 a ^ n := by
  change toBF64 (powGo n a n 1) = _
  rw [toBF64_powGo n a n 1 le_rfl, toBF64_one, one_mul]

instance instCommRing : CommRing F where
  add_assoc a b c := toBF64_injective (by simp only [toBF64_add, add_assoc])
  zero_add a := toBF64_injective (by simp only [toBF64_add, toBF64_zero, zero_add])
  add_zero a := toBF64_injective (by simp only [toBF64_add, toBF64_zero, add_zero])
  add_comm a b := toBF64_injective (by simp only [toBF64_add, add_comm])
  neg_add_cancel a :=
    toBF64_injective (by simp only [toBF64_add, toBF64_neg, toBF64_zero, neg_add_cancel])
  sub_eq_add_neg a b :=
    toBF64_injective (by simp only [toBF64_sub, toBF64_add, toBF64_neg, sub_eq_add_neg])
  nsmul n a := n • a
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul n a := n • a
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  left_distrib a b c := toBF64_injective (by simp only [toBF64_mul, toBF64_add, mul_add])
  right_distrib a b c := toBF64_injective (by simp only [toBF64_mul, toBF64_add, add_mul])
  zero_mul a := toBF64_injective (by simp only [toBF64_mul, toBF64_zero, zero_mul])
  mul_zero a := toBF64_injective (by simp only [toBF64_mul, toBF64_zero, mul_zero])
  mul_assoc a b c := toBF64_injective (by simp only [toBF64_mul, mul_assoc])
  one_mul a := toBF64_injective (by simp only [toBF64_mul, toBF64_one, one_mul])
  mul_one a := toBF64_injective (by simp only [toBF64_mul, toBF64_one, mul_one])
  mul_comm a b := toBF64_injective (by simp only [toBF64_mul, mul_comm])
  npow n a := a ^ n
  npow_zero a := toBF64_injective (by simp only [toBF64_npow, toBF64_one, pow_zero])
  npow_succ n a := toBF64_injective (by simp only [toBF64_npow, toBF64_mul, pow_succ])
  natCast n := (n : F)
  natCast_zero := toBF64_injective (by simp only [toBF64_natCast, toBF64_zero, Nat.cast_zero])
  natCast_succ n := toBF64_injective
    (by simp only [toBF64_natCast, toBF64_add, toBF64_one, Nat.cast_succ])
  intCast n := (n : F)
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl

instance : Div F := ⟨fun a b => a * b⁻¹⟩

/-- **`F` is a field**, with the word operations. -/
instance instField : Field F where
  inv := inv
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel a h := toBF64_injective (by
    show toBF64 (a * a⁻¹) = toBF64 1
    rw [toBF64_mul, toBF64_inv, toBF64_one]
    exact mul_inv_cancel₀ (fun h' => h (by rw [← toBF64_inj, h', toBF64_zero])))
  inv_zero := rfl
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toBF64` as a ring isomorphism. -/
def ringEquivBF64 : F ≃+* BF64 where
  toEquiv := equivBF64
  map_mul' := toBF64_mul
  map_add' := toBF64_add

@[simp] theorem ringEquivBF64_apply (a : F) : ringEquivBF64 a = toBF64 a := rfl

@[simp] theorem toBF64_div (a b : F) : toBF64 (a / b) = toBF64 a / toBF64 b := by
  change toBF64 (a * b⁻¹) = _
  rw [toBF64_mul, toBF64_inv, div_eq_mul_inv]

instance : CharP F 2 where
  cast_eq_zero_iff n := by
    rw [← toBF64_inj, toBF64_natCast, toBF64_zero]
    exact CharP.cast_eq_zero_iff BF64 2 n

/-! ## Cardinality -/

instance : Finite F := Finite.of_equiv BF64 equivBF64.symm

/-- `F` has `2 ^ 64` elements. -/
theorem nat_card_F : Nat.card F = 2 ^ 64 := by
  rw [Nat.card_congr equivBF64, BF64.nat_card_bf64]

/-- An enumeration of `F`, for statements that need one. It is noncomputable on purpose: a
computable enumeration of `2 ^ 64` elements would be a closed term built at program start. -/
noncomputable instance : Fintype F := Fintype.ofFinite F

/-- Every enumeration of `F` has `2 ^ 64` elements. -/
theorem card_F [Fintype F] : Fintype.card F = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, nat_card_F]

/-! ## Word access, Frobenius powers and the conjugates of `x` -/

@[simp] theorem toUInt64_ofUInt64 (w : UInt64) : (ofUInt64 w).toUInt64 = w := rfl

@[simp] theorem ofUInt64_toUInt64 (a : F) : ofUInt64 a.toUInt64 = a := rfl

theorem sq_eq_mul (a : F) : sq a = a * a := toBF64_injective (by rw [toBF64_sq, toBF64_mul])

/-- `frob k` is the `2 ^ k`-th power. -/
theorem frob_eq_pow (k : ℕ) (a : F) : frob k a = a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [frob]
  | succ k ih => rw [frob, ih, sq_eq_mul, ← _root_.sq, ← pow_mul, pow_succ, mul_comm]

/-- **The 64 conjugates `x^(2^k)`, `k < 64`, of the generator over `GF(2)` are distinct.**
Kernel-decided on the word arithmetic. -/
theorem conj_distinct : ((List.range 64).map (fun k => x ^ (2 ^ k))).Nodup := by
  have h : (fun k => x ^ (2 ^ k)) = (fun k => frob k x) := funext fun k => (frob_eq_pow k x).symm
  rw [h]
  decide +kernel

/-- The power `x ^ i`, `i < 64`, is the word with only bit `i` set (no reduction below degree
64). Proved through the polynomial, not by evaluation, so its kernel check is cheap. -/
theorem x_pow_word (i : Fin 64) : x ^ (i : ℕ) = ⟨(1 : UInt64) <<< i.val.toUInt64⟩ := by
  apply toBF64_injective
  apply BF64.toQuot_injective
  rw [toBF64_npow, BF64.toQuot_npow, toQuot_toBF64, toQuot_toBF64]
  have h1 : ((1 : UInt64) <<< i.val.toUInt64).toBitVec = ((1 <<< i.val : ℕ) : BitVec 64) := by
    have := i.isLt
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt i.isLt, Nat.toUInt64, Nat.shiftLeft_eq]
  have h2 : x.val.toBitVec = ((1 <<< 1 : ℕ) : BitVec 64) := by decide
  show AdjoinRoot.mk BF64.basePoly (toPoly x.val.toBitVec) ^ (i : ℕ) =
    AdjoinRoot.mk BF64.basePoly (toPoly ((1 : UInt64) <<< i.val.toUInt64).toBitVec)
  rw [h1, h2, toPoly_one_shiftLeft (w := 64) _ i.isLt,
    toPoly_one_shiftLeft (w := 64) 1 (by norm_num), pow_one, map_pow]

/-! ## Bytes -/

/-- The encoding is the eight little-endian bytes of the word. -/
theorem toBytes_toList (a : F) : (toBytes a).toList = CompPoly.Bytes.toListLE 8 a.val.toNat := by
  simp [toBytes, CompPoly.Bytes.toListLE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

/-- **The encoding is CompPoly's `ByteCodec BF64` encoding.** -/
theorem toBytes_eq (a : F) :
    (toBytes a).toList = (CompPoly.ByteCodec.toBytes (toBF64 a)).toList := by
  rw [toBytes_toList]
  change _ = CompPoly.Bytes.toListLE (CompPoly.ByteCodec.width BF64) a.val.toBitVec.toNat
  rw [BF64.byteCodec_width]
  rfl

/-- The decoding reads the little-endian natural of the bytes. -/
theorem ofBytes_toNat (v : Vector UInt8 8) : (ofBytes v).val.toNat = CompPoly.Bytes.ofVecLE v := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp [ofBytes, CompPoly.Bytes.ofVecLE, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    omega

/-- **The decoding is CompPoly's** (`CanonicalNat.ofBytesModOrder`, the total decoder; on
eight bytes it never reduces). -/
theorem ofBytes_eq (v : Vector UInt8 8) :
    toBF64 (ofBytes v) = CompPoly.CanonicalNat.ofBytesModOrder v := by
  apply BF64.ext
  change (ofBytes v).val.toBitVec = BitVec.ofNat 64 (CompPoly.Bytes.ofVecLE v)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← ofBytes_toNat]
  simp [Nat.mod_eq_of_lt (ofBytes v).val.toNat_lt]

/-- Decoding inverts encoding. -/
@[simp] theorem ofBytes_toBytes (a : F) : ofBytes (toBytes a) = a := by
  have h : (ofBytes (toBytes a)).val.toNat = a.val.toNat := by
    rw [ofBytes_toNat, CompPoly.Bytes.ofVecLE, toBytes_toList,
      CompPoly.Bytes.ofListLE_toListLE_of_lt (by simpa using a.val.toNat_lt)]
  cases a
  exact congrArg F.mk (UInt64.toNat_inj.mp h)

/-- Encoding inverts decoding: every eight-byte string is the encoding of one element. -/
@[simp] theorem toBytes_ofBytes (v : Vector UInt8 8) : toBytes (ofBytes v) = v := by
  apply Vector.toList_inj.mp
  rw [toBytes_toList, ofBytes_toNat, CompPoly.Bytes.ofVecLE]
  simpa using CompPoly.Bytes.toListLE_ofListLE v.toList

end SpartanChain.F
