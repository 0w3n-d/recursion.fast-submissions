import SpartanChainLigero

/-!
# Controls for `SpartanChainLigero` (blueprint §10.1)

* Positive: the honest columns pass both column equations for every `r`, `a`
  (`Ligero.colCheck_honest`), and the verifier accepts the honest openings for every oracle
  (`Ligero.verify2_complete`).
* Negative: a column with one entry changed is rejected by the proximity equation whenever that
  row's coefficient is nonzero (`colCheck_tampered`).
-/

namespace SpartanChain.Ligero.Controls

open PCS

theorem ofF_add (x y : F) : EF.ofF (x + y) = EF.ofF x + EF.ofF y := by
  simp [← EF.algebraMap_eq_ofF, map_add]

theorem ofF_ne_zero {x : F} (h : x ≠ 0) : EF.ofF x ≠ 0 := by
  rw [← EF.algebraMap_eq_ofF]; exact (map_ne_zero _).2 h

/-- Changing entry `i₀` of a column by `δ` changes `Σ_i w_i·col_i` by `δ·w_{i₀}`. -/
theorem comb_tamper (m : ℕ) (w : Array EF) (col col' : Array F) (i₀ : Fin m) (δ : F)
    (h : ∀ i : Fin m, col'.getD i 0 = col.getD i 0 + if i = i₀ then δ else 0) :
    comb m w col' = comb m w col + EF.ofF δ * w.getD i₀ 0 := by
  rw [comb_eq, comb_eq]
  simp only [h, ofF_add, add_mul, Finset.sum_add_distrib]
  congr 1
  simp [apply_ite EF.ofF, ite_mul, Finset.sum_ite_eq', ← EF.algebraMap_eq_ofF]

/-- **Negative control**: a tampered column (one entry changed by `δ ≠ 0`, in a row whose
proximity coefficient is nonzero) fails the column check against the honest `ū`, `v`. -/
theorem colCheck_tampered (κ : ℕ) (ks : Array F) (r a : Array EF) (Q : Array (Array F))
    {N : ℕ} (c : Fin N) (i₀ : Fin (rows κ)) {δ : F} (hδ : δ ≠ 0) (hr : r.getD i₀ 0 ≠ 0)
    (col' : Array F)
    (h : ∀ i : Fin (rows κ), col'.getD i 0 =
      (columnAt ks (lk κ) Q (ptOf c)).getD i 0 + if i = i₀ then δ else 0) :
    colCheck κ ks r a (combRows (rows κ) (msgLen κ) r Q) (combRows (rows κ) (msgLen κ) a Q) c
      col' = false := by
  rw [colCheck_eq, comb_tamper _ _ _ _ i₀ δ h, enc_combRows]
  have hne : comb (rows κ) r (columnAt ks (lk κ) Q (ptOf c)) ≠
      comb (rows κ) r (columnAt ks (lk κ) Q (ptOf c)) + EF.ofF δ * r.getD i₀ 0 := by
    intro h'
    exact mul_ne_zero (ofF_ne_zero hδ) hr (left_eq_add.1 h')
  simp only [hne, decide_false, Bool.false_and]

end SpartanChain.Ligero.Controls
