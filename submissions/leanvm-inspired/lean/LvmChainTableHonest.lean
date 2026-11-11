-- New for lvm (WP-8): non-vacuity of `chain_of_CHRel`. lvm2 S1-L: the gated table (dead rows hold the
-- zero input, P-GATE's `Chain::run_gated`) and the gated link's relations; no longer imports `CHRel`.
import LvmChainTableLink

/-!
# The honest gated `CH` table

`honCol h ys s n`: row `x < n` holds `in_x = Pad43(chainEnd s x)` in slots `0 … 24`, a row `x ≥ n`
the zero state (lvm2 S1: A9 deleted; the honest prover stops the chain at `n`); twelve rounds of the
input in slots `25 … 49`, the permutation's lanes `0 … 3` in slots `ys … ys + 3`, zero elsewhere.
**`linkRel_honest`** (non-vacuity of `chLinkSpec`'s precondition and of `chain_of_CH`): for every
`1 ≤ n ≤ 2^h` it meets the output tie on every row, the gated `LinkBits` and `ConstLanes`, the start
claim, and the end claim with `hd = chainEnd s n`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

/-- The honest input of row `x` of a chain of `n` steps (zero on the dead rows `x ≥ n`). -/
def honIn (s : RecursionFast.Digest) (n x : ℕ) : RecursionFast.Keccak.State :=
  if x < n then pad43St (digestBits (RecursionFast.chainEnd s x)) else zeroSt

/-- **The honest gated chain table.** -/
def honCol (h ys : ℕ) (s : RecursionFast.Digest) (n w : ℕ) : K :=
  if w / 2 ^ h < 25 then K.ofLane (Keccak.lane (honIn s n (w % 2 ^ h)) (w / 2 ^ h))
  else if w / 2 ^ h < 50 then
    K.ofLane (Keccak.lane (roundsFrom 0 12 (honIn s n (w % 2 ^ h))) (w / 2 ^ h - 25))
  else if ys ≤ w / 2 ^ h ∧ w / 2 ^ h < ys + 4 then
    laneWord (keccakF1600 (honIn s n (w % 2 ^ h))) (w / 2 ^ h - ys)
  else 0

variable (h ys : ℕ) (s : RecursionFast.Digest) (n : ℕ)

theorem honCol_at {x t : ℕ} (hx : x < 2 ^ h) :
    honCol h ys s n (x + 2 ^ h * t) =
      if t < 25 then K.ofLane (Keccak.lane (honIn s n x) t)
      else if t < 50 then K.ofLane (Keccak.lane (roundsFrom 0 12 (honIn s n x)) (t - 25))
      else if ys ≤ t ∧ t < ys + 4 then laneWord (keccakF1600 (honIn s n x)) (t - ys)
      else 0 := by
  simp only [honCol, idx_div h hx, idx_mod h hx]

theorem honIn_state {x : ℕ} (hx : x < 2 ^ h) (m : ℕ) (hm : m < 2) :
    inState h (honCol h ys s n) m x =
      if m = 0 then honIn s n x else roundsFrom 0 12 (honIn s n x) := by
  refine Vector.ext fun l hl ↦ ?_
  simp only [inState, Vector.getElem_ofFn, honCol_at h ys s n hx]
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add, if_pos hl, ite_true, K.lane, K.ofLane,
      BF64.toBitVec_ofBitVec, LeanVM.Protocol.KeccakGkr.lane_eq _ hl]
  · simp only [Nat.mul_one, if_neg (show ¬ 25 + l < 25 by omega), if_pos (show 25 + l < 50 by omega),
      show 25 + l - 25 = l by omega, one_ne_zero, ite_false, K.lane, K.ofLane,
      BF64.toBitVec_ofBitVec, LeanVM.Protocol.KeccakGkr.lane_eq _ hl]

theorem honIn_eq {x : ℕ} (hx : x < 2 ^ h) : inState h (honCol h ys s n) 0 x = honIn s n x := by
  rw [honIn_state h ys s n hx 0 (by norm_num), if_pos rfl]

/-- A lane of a state is the little-endian word of its digest's bytes (lanes `0 … 3`). -/
theorem lane_stDigest (a : RecursionFast.Keccak.State) {m : ℕ} (hm : m < 4) :
    Keccak.lane a m = RecursionFast.Keccak.blockLane (stDigest a).toArray m := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz ↦ ?_)
  rw [blockLane_bit _ _ hz]
  have he : 8 * m + z / 8 < 32 := by omega
  have hg : (stDigest a).toArray.getD (8 * m + z / 8) 0 = (stDigest a)[8 * m + z / 8] := by
    simp [Array.getD, he]
  rw [hg, stDigest_bit _ he (Nat.mod_lt _ (by decide)), stBit_eq_sbit _ (by omega), sbit,
    show (8 * (8 * m + z / 8) + z % 8) / 64 = m by omega,
    show (8 * (8 * m + z / 8) + z % 8) % 64 = z by omega]

/-- The lanes `8 … 24` of `Pad43` are the constants. -/
theorem lane_pad43St (y : ℕ → Bool) {l : ℕ} (h8 : 8 ≤ l) (h25 : l < 25) :
    Keccak.lane (pad43St y) l = padConstLane l := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz ↦ ?_)
  have := stBit_ofBits (pad43Bit y) (show 64 * l + z < 1600 by omega)
  rw [stBit_eq_sbit _ (by omega), sbit, show (64 * l + z) / 64 = l by omega,
    show (64 * l + z) % 64 = z by omega] at this
  rw [← pad43St] at this
  rw [this]
  unfold pad43Bit
  rw [if_neg (by omega), if_neg (by omega), padConstLane]
  by_cases h16 : l = 16
  · subst h16
    rw [if_pos rfl]
    have e : (64 * 16 + z = 264 ∨ 64 * 16 + z = 1087) ↔ z = 63 := by omega
    simp only [e, UInt64.toBitVec_shiftLeft]
    interval_cases z <;> decide
  · rw [if_neg h16]
    have : ¬ (64 * l + z = 264 ∨ 64 * l + z = 1087) := by omega
    simp [this]

theorem lane_zeroSt (l : ℕ) : Keccak.lane zeroSt l = 0 := by
  unfold Keccak.lane zeroSt
  by_cases hl : l < 25
  · simp [Array.getD, hl]
  · simp [Array.getD, hl]

theorem ofLane_zero : K.ofLane 0 = 0 := rfl

/-- **Non-vacuity of the gated link**: for every `1 ≤ n ≤ 2^h` the honest gated table meets the
output tie on every row, the gated `LinkBits` and `ConstLanes` (`chLinkSpec`'s precondition), the
start claim, and the end claim with `hd = chainEnd s n` (so `ChainRel` and `chain_of_CH`). -/
theorem linkRel_honest (hys : 50 ≤ ys) (hys4 : ys + 4 ≤ 64) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ h) :
    (∀ x < 2 ^ h, ∀ m < 4, honCol h ys s n (x + 2 ^ h * (ys + m)) =
      laneWord (keccakF1600 (inState h (honCol h ys s n) 0 x)) m) ∧
    LinkBits h ys (honCol h ys s n) n ∧ ConstLanes h (honCol h ys s n) n ∧
    inState h (honCol h ys s n) 0 0 = pad43St (digestBits s) ∧
    ∀ m < 4, honCol h ys s n (n - 1 + 2 ^ h * (ys + m)) =
      K.ofLane (RecursionFast.Keccak.blockLane (RecursionFast.chainEnd s n).toArray m) := by
  have hp := Nat.two_pow_pos h
  have hlive : ∀ x < n, honIn s n x = pad43St (digestBits (RecursionFast.chainEnd s x)) :=
    fun x hx ↦ if_pos hx
  -- the outputs
  have hout : ∀ x < 2 ^ h, ∀ m < 4, honCol h ys s n (x + 2 ^ h * (ys + m)) =
      laneWord (keccakF1600 (honIn s n x)) m := by
    intro x hx m hm
    rw [honCol_at h ys s n hx, if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
      show ys + m - ys = m by omega]
  -- the gated link
  have hlink : ∀ x, x + 1 < n →
      inState h (honCol h ys s n) 0 (x + 1) = pad43St (yBits h ys (honCol h ys s n) x) := by
    intro x hx
    rw [honIn_eq h ys s n (by omega), hlive _ hx]
    refine pad43St_congr fun j hj ↦ ?_
    rw [yBits_eq h ys (honCol h ys s n) (fun m hm ↦ by
      rw [hout x (by omega) m hm, honIn_eq h ys s n (by omega)]) hj, honIn_eq h ys s n (by omega),
      hlive _ (by omega), ← chainStep_pad43, RecursionFast.chainEnd, RecursionFast.chainEnd,
      Function.iterate_succ_apply']
  refine ⟨fun x hx m hm ↦ ?_, fun x hx hxn l hl p hp' ↦ ?_, fun x hx l h8 h25 ↦ ?_,
    by rw [honIn_eq h ys s n hp, hlive 0 hn]; rfl, fun m hm ↦ ?_⟩
  · rw [hout x hx m hm, honIn_eq h ys s n hx]
  · have := stBit_inState h (honCol h ys s n) (x + 1) (show 64 * l + p < 1600 by omega)
    rw [hlink x hxn, pad43St, stBit_ofBits _ (by omega), show (64 * l + p) / 64 = l by omega,
      show (64 * l + p) % 64 = p by omega] at this
    simp only [inBit, show x + 1 < 2 ^ h by omega, decide_true, Bool.true_and]
    exact this.symm
  · rw [honCol_at h ys s n hx, if_pos h25, honIn]
    by_cases hxn : x < n
    · rw [if_pos hxn, if_pos hxn, lane_pad43St _ h8 h25]
    · rw [if_neg hxn, if_neg hxn, lane_zeroSt, ofLane_zero]
  · have hc : RecursionFast.chainStep (RecursionFast.chainEnd s (n - 1)) =
        RecursionFast.chainEnd s n := by
      rw [RecursionFast.chainEnd, RecursionFast.chainEnd,
        ← Function.iterate_succ_apply' RecursionFast.chainStep (n - 1), Nat.succ_eq_add_one,
        Nat.sub_add_cancel hn]
    rw [hout _ (by omega) m hm, laneWord, lane_stDigest _ hm, hlive _ (by omega), keccakF1600_eq',
      ← chainStep_pad43, hc]

end Lvm.KG
