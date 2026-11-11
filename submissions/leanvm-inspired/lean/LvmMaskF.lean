-- New for lvm2 (S1-V): V_S's closed forms of the gated CH link (LvmDecideKeccak `ltPairF`, `gStateF`)
-- are S1-L's `LvmMask` automata through `FE.toExt3` (V-PERF's fast-twin pattern), and the native sums
-- they evaluate. Low in the import graph (no V_S, no circuit), so both the VEq refinement
-- (`LvmVEqLinkArith`) and the circuit's gadget proofs can use it.
import LvmMask
import LvmDecideKeccak
import LvmLoopTable
import LvmFieldCorrect

/-!
# The gated link's closed forms: `FE` twins

* **`toExt3_ltPairF`**, **`toExt3_gStateF`**: `V_S`'s automata are `LvmMask`'s `ltPair`, `gState`
  over `E`, text for text (one induction each); hence `toExt3_ltEvalF`, `toExt3_gMaskEvalF`,
  `toExt3_gShiftEvalF`.
* **`ltEvalF_eq_sum`**, **`gMaskEvalF_eq_sum`**, **`gShiftEvalF_eq_sum`**: what they compute, as native
  sums of WP-10's `eqW` (from S1-L's `ltPair_eq`, `gState_eq` and `FE.toExt3_injective`):
  `lt̃_t(y) = Σ_{k<t} eq(y, k)` (`t ≤ 2^|y|`), `Ẽ'(ρ, y) = Σ_{k<t} eq(ρ, k)·eq(y, k)` (`t ≤ 2^|ρ|`),
  `S̃(ρ, y) = Σ_{k<t} eq(ρ, k)·eq(y, k + 1)` (`t < 2^|ρ|`). `V_S` uses them at `t = n − 1` and
  `t = n` with `1 ≤ n ≤ 2^logN` (`parseOk`, A1).
-/

set_option autoImplicit false

namespace Lvm

open LeanVM.Parameters LeanVM.Protocol.KeccakGkr Lvm.Loop Finset

/-! ## The automata's twins -/

theorem toExt3_ite01 (c : Prop) [Decidable c] :
    FE.toExt3 (if c then 1 else 0) = if c then 1 else 0 := by
  split_ifs
  · exact FE.toExt3_one
  · exact FE.toExt3_zero

/-- **The threshold automaton's twin.** -/
theorem toExt3_ltPairF : ∀ (x : List FE) (t : ℕ),
    (FE.toExt3 (ltPairF x t).1, FE.toExt3 (ltPairF x t).2) = Lvm.KG.ltPair (x.map FE.toExt3) t
  | [], t => by simp only [ltPairF, Lvm.KG.ltPair, List.map_nil, toExt3_ite01, FE.toExt3_one]
  | a :: xs, t => by
    have ih := toExt3_ltPairF xs (t / 2)
    simp only [ltPairF, Lvm.KG.ltPair, List.map_cons]
    rw [← ih]
    split_ifs <;> simp only [FE.toExt3_add, FE.toExt3_mul, FE.toExt3_one]

theorem toExt3_ltEvalF (x : List FE) (t : ℕ) :
    FE.toExt3 (ltEvalF x t) = Lvm.KG.ltEvalE (x.map FE.toExt3) t := by
  rw [ltEvalF, Lvm.KG.ltEvalE, ← toExt3_ltPairF]

/-- **The gated kernels' automaton's twin.** -/
theorem toExt3_gStateF : ∀ (x y : List FE) (t : ℕ),
    (FE.toExt3 (gStateF x y t).1, FE.toExt3 (gStateF x y t).2.1, FE.toExt3 (gStateF x y t).2.2.1,
      FE.toExt3 (gStateF x y t).2.2.2) = Lvm.KG.gState (x.map FE.toExt3) (y.map FE.toExt3) t
  | [], _, t => by
    simp only [gStateF, Lvm.KG.gState, List.map_nil, toExt3_ite01, FE.toExt3_one, FE.toExt3_zero]
  | _ :: _, [], t => by
    simp only [gStateF, Lvm.KG.gState, List.map_nil, List.map_cons, toExt3_ite01, FE.toExt3_one,
      FE.toExt3_zero]
  | a :: xs, b :: ys, t => by
    have ih := toExt3_gStateF xs ys (t / 2)
    simp only [gStateF, Lvm.KG.gState, List.map_cons]
    rw [← ih]
    split_ifs <;> simp only [FE.toExt3_add, FE.toExt3_mul, FE.toExt3_one]

theorem toExt3_gMaskEvalF (x y : List FE) (t : ℕ) :
    FE.toExt3 (gMaskEvalF x y t) = Lvm.KG.gMaskEvalE (x.map FE.toExt3) (y.map FE.toExt3) t := by
  rw [gMaskEvalF, Lvm.KG.gMaskEvalE, ← toExt3_gStateF]

theorem toExt3_gShiftEvalF (x y : List FE) (t : ℕ) :
    FE.toExt3 (gShiftEvalF x y t) = Lvm.KG.gShiftEvalE (x.map FE.toExt3) (y.map FE.toExt3) t := by
  rw [gShiftEvalF, Lvm.KG.gShiftEvalE, ← toExt3_gStateF]

/-! ## What they compute: native sums -/

/-- WP-10's native equality weight read over `E`. -/
theorem toExt3_eqWL : ∀ (y : List FE) (w : ℕ), FE.toExt3 (eqW y w) = eqAt (y.map FE.toExt3) w
  | [], _ => by simp only [eqW, List.map_nil, eqAt_nil, FE.toExt3_one]
  | r :: l, w => by
    simp only [List.map_cons, eqW, eqAt_cons, FE.toExt3_mul, toExt3_eqWL l]
    split_ifs
    · rfl
    · rw [FE.toExt3_sub, FE.toExt3_one, CharTwo.sub_eq_add]

theorem toExt3_sumR (s : Finset ℕ) (f : ℕ → FE) :
    FE.toExt3 (∑ k ∈ s, f k) = ∑ k ∈ s, FE.toExt3 (f k) :=
  map_sum FE.ringEquivExt3 f s

theorem sum_ite_lt (f : ℕ → E) {t N : ℕ} (h : t ≤ N) :
    ∑ k ∈ range N, (if k < t then f k else 0) = ∑ k ∈ range t, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **`V_S`'s `lt̃_t(y)` is `Σ_{k<t} eq(y, k)`** (`t ≤ 2^|y|`). -/
theorem ltEvalF_eq_sum (y : List FE) {t : ℕ} (ht : t ≤ 2 ^ y.length) :
    ltEvalF y t = ∑ k ∈ range t, eqW y k := by
  apply FE.toExt3_injective
  rw [toExt3_ltEvalF, Lvm.KG.ltEvalE, Lvm.KG.ltPair_eq, toExt3_sumR]
  simp only [toExt3_eqWL, Lvm.KG.ltS, Lvm.KG.ltK, List.length_map]
  exact sum_ite_lt _ ht

/-- **`V_S`'s `Ẽ'(ρ, y)` is `Σ_{k<t} eq(ρ, k)·eq(y, k)`** (`t ≤ 2^|ρ|`). -/
theorem gMaskEvalF_eq_sum (rho y : List FE) (h : rho.length = y.length) {t : ℕ}
    (ht : t ≤ 2 ^ rho.length) :
    gMaskEvalF rho y t = ∑ k ∈ range t, eqW rho k * eqW y k := by
  apply FE.toExt3_injective
  rw [toExt3_gMaskEvalF, Lvm.KG.gMaskEvalE, Lvm.KG.gState_eq _ _ (by simp [h]), toExt3_sumR]
  simp only [FE.toExt3_mul, toExt3_eqWL, Lvm.KG.q0S, List.length_map]
  exact sum_ite_lt _ ht

/-- **`V_S`'s `S̃(ρ, y)` is `Σ_{k<t} eq(ρ, k)·eq(y, k + 1)`** (`t < 2^|ρ|`: no row wraps). -/
theorem gShiftEvalF_eq_sum (rho y : List FE) (h : rho.length = y.length) {t : ℕ}
    (ht : t < 2 ^ rho.length) :
    gShiftEvalF rho y t = ∑ k ∈ range t, eqW rho k * eqW y (k + 1) := by
  apply FE.toExt3_injective
  rw [toExt3_gShiftEvalF, Lvm.KG.gShiftEvalE, Lvm.KG.gState_eq _ _ (by simp [h]), toExt3_sumR]
  simp only [FE.toExt3_mul, toExt3_eqWL, Lvm.KG.q1S, List.length_map]
  rw [← sum_ite_lt _ ht.le]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.1 hk
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.1 h2
  · exact absurd ⟨h2, by omega⟩ h1
  · rfl

end Lvm
