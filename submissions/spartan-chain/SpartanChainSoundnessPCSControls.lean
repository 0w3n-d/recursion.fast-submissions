import SpartanChainSoundnessPCS

/-!
# Controls for `SpartanChainSoundnessPCS` (blueprint §10.1, §14: `Dset` on a toy code)

* `not_close_of_weight`: a word of weight `w` with `e < w` and `w + e < d` is not `e`-close to a
  code of minimum distance `d`.
* Positive: at `κ = 0` (`k = 128`, `N = 1024`, `d = 897`, `e = 298`) the matrix whose first row
  is `1` on columns `0 … 299` makes `far_Dset_card`'s hypothesis hold for `r = (1, 0)`
  (`toy_not_close`), so every `ū` leaves at least `299` columns in `D_far` (`toy_Dset_card`).
* Negative: for the zero matrix and the zero message, `Dset` is empty (`zero_Dset`).
-/

namespace SpartanChain.SoundnessPCS.Controls

open RS PCS Finset

theorem not_close_of_weight {E ι : Type*} [Field E] [DecidableEq E] [Fintype ι]
    {C : Submodule E (ι → E)} {d e : ℕ} (hC : MinDist C d) {w : ι → E}
    (h1 : e < hammingNorm w) (h2 : hammingNorm w + e < d) : ¬ Close C e w := by
  rintro ⟨c, hc, hd⟩
  by_cases h0 : c = 0
  · subst h0; rw [hammingDist_zero_right] at hd; omega
  · have h3 := hC c hc h0
    have ht := hammingDist_triangle c w 0
    rw [hammingDist_zero_right, hammingDist_zero_right, hammingDist_comm] at ht
    omega

/-- Row 0 is `1` on columns `0 … 299`, row 1 is `0` (`κ = 0`, `m = 2`). -/
def U0 : Fin (rows 0) → Fin (cols 0) → F := fun i c => if i.val = 0 ∧ c.val < 300 then 1 else 0

/-- The coefficients `r = (1, 0)`. -/
def r0 : Fin (rows 0) → EF := fun i => if i.val = 0 then 1 else 0

theorem toy_params : radius 0 = 298 ∧ PCS.dist 0 = 897 ∧ rows 0 = 2 := by decide

theorem toy_word (c : Fin (cols 0)) :
    (∑ i, r0 i • UE 0 U0 i) c = if c.val < 300 then 1 else 0 := by
  rw [UE_sum_apply]
  have h2 : rows 0 = 2 := toy_params.2.2
  rw [Fintype.sum_eq_single ⟨0, by rw [h2]; norm_num⟩ fun i hi => by
    simp only [r0]
    rw [ite_eq_right_iff.2 (fun h => absurd (Fin.ext h) hi), zero_mul]]
  by_cases hc : c.val < 300 <;> simp [r0, U0, hc, ← EF.algebraMap_eq_ofF]

theorem toy_weight : hammingNorm (∑ i, r0 i • UE 0 U0 i) = 300 := by
  unfold hammingNorm
  have : (univ.filter fun c : Fin (cols 0) => (∑ i, r0 i • UE 0 U0 i) c ≠ 0) =
      univ.filter fun c : Fin (cols 0) => c.val < 300 := by
    ext c
    simp only [mem_filter, mem_univ, true_and]
    rw [toy_word]
    split_ifs with h <;> simp [h]
  rw [this, Fin.card_filter_val_lt]; decide

/-- **Positive**: `far_Dset_card`'s hypothesis is reachable. -/
theorem toy_not_close : ¬ Close (code 0) (radius 0) (∑ i, r0 i • UE 0 U0 i) := by
  have hw := toy_weight
  obtain ⟨h1, h2, -⟩ := toy_params
  exact not_close_of_weight (code_minDist 0 (by norm_num)) (by omega) (by omega)

theorem toy_Dset_card (msg : Fin (2 ^ lk 0) → EF) : 299 ≤ (Dset 0 U0 r0 msg).card := by
  have := far_Dset_card U0 r0 toy_not_close msg
  have h1 := toy_params.1
  omega

/-- **Negative**: consistent data (zero matrix, zero message) has an empty difference set. -/
theorem zero_Dset : Dset 0 (fun _ _ => 0) r0 0 = ∅ := by
  ext c
  simp only [Dset, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_not]
  have : enc (kap (lk 0)) (lk 0) (dom (cols 0)) (0 : Fin (2 ^ lk 0) → EF) = 0 :=
    (encL (kap (lk 0)) (lk 0) (dom (cols 0))).map_zero
  rw [this]
  simp [← EF.algebraMap_eq_ofF]

end SpartanChain.SoundnessPCS.Controls
