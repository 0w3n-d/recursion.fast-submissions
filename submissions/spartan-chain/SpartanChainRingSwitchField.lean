import SpartanChainRingSwitch
import SpartanChainField
import Mathlib.FieldTheory.Finite.Basic

/-!
# L-R1 at the word-level field (blueprint §9.4 L-R1)

`ring_inj` instantiated at `K = F`, `E = EF`, `x = F.x`, `y = EF.y`, `n = 64`: every hypothesis is
discharged from the field module.

* `conj_distinct` is `F.conj_distinct` verbatim;
* `|F| = 2^64` and `|EF| = 2^192` give the Frobenius periods (`F.pow_two_pow_64`,
  `EF.pow_two_pow_192`);
* the coordinates: `EF.mk_eq : ⟨a, b, c⟩ = a + b y + c y²` (through `toExt3`), hence `E = F + F y +
  F y²` (`EF.span`) and the independence of `1, y, y²` (`EF.indep`);
* the bases `1, y^(2^k), y^(2^(k+1))` follow by `ybasis_of_period` (so `EF.ybasis`'s determinants
  are not needed).

Controls: `ring_inj_EF` itself (every hypothesis of L-R1 holds at the protocol's field, so L-R1 is
not vacuous), a family it applies to, and two negative controls showing that the hypotheses
`hconj` and the independence of `1, y, y²` are real constraints (they fail for `x = 1`, `y = 1`).
-/

namespace SpartanChain

open Finset

/-- `a ^ 2 ^ 64 = a` on `F`. -/
theorem F.pow_two_pow_64 (a : F) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  simp only [F.card_F] at h
  exact h

/-- `e ^ 2 ^ 192 = e` on `EF`. -/
theorem EF.pow_two_pow_192 (e : EF) : e ^ 2 ^ 192 = e := by
  have h := FiniteField.pow_card e
  simp only [EF.card_EF] at h
  exact h

/-- The coordinates: `⟨a, b, c⟩ = a + b·y + c·y²`. -/
theorem EF.mk_eq (a b c : F) :
    (⟨a, b, c⟩ : EF) =
      algebraMap F EF a + algebraMap F EF b * EF.y + algebraMap F EF c * EF.y ^ 2 := by
  apply EF.ringEquivExt3.injective
  simp only [map_add, map_mul, map_pow, EF.ringEquivExt3_apply, EF.algebraMap_eq_ofF,
    EF.toExt3_ofF, EF.toExt3_y]
  exact EF.toExt3_eq ⟨a, b, c⟩

/-- `EF = F + F·y + F·y²`. -/
theorem EF.span (e : EF) : ∃ a b c : F,
    e = algebraMap F EF a + algebraMap F EF b * EF.y + algebraMap F EF c * EF.y ^ 2 :=
  ⟨e.c₀, e.c₁, e.c₂, EF.mk_eq _ _ _⟩

/-- `1, y, y²` are `F`-independent. -/
theorem EF.indep (a b c : F)
    (h : algebraMap F EF a + algebraMap F EF b * EF.y + algebraMap F EF c * EF.y ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [← EF.mk_eq] at h
  exact ⟨congrArg EF.c₀ h, congrArg EF.c₁ h, congrArg EF.c₂ h⟩

/-- **L-R1 at the protocol's fields.** A nonzero family `δ ∈ EF^64` has
`Σ_i x^i · δ_i ^ 2 ^ k ≠ 0` for some `k < 64`. -/
theorem ring_inj_EF (δ : Fin 64 → EF) (hδ : δ ≠ 0) :
    ∃ k < 64, ∑ i : Fin 64, algebraMap F EF (F.x ^ (i : ℕ)) * δ i ^ 2 ^ k ≠ 0 :=
  ring_inj F.x F.conj_distinct F.pow_two_pow_64 EF.y EF.span
    (fun k hk ↦ ybasis_of_period EF.pow_two_pow_192 EF.y EF.indep k (by omega)) δ hδ

/-- Positive control: the family `δ = (1, 0, …, 0)` (a wrong first slice) is detected at
`k = 0`. -/
theorem ring_inj_EF_single :
    ∃ k < 64, ∑ i : Fin 64,
      algebraMap F EF (F.x ^ (i : ℕ)) * (Pi.single 0 1 : Fin 64 → EF) i ^ 2 ^ k ≠ 0 :=
  ring_inj_EF _ fun h ↦ one_ne_zero (congrFun h 0 |>.symm.trans (Pi.single_eq_same _ _)).symm

/-- Negative control: `hconj` is a real constraint (it fails for `x = 1`). -/
theorem conj_distinct_one_false : ¬((List.range 64).map fun k ↦ (1 : F) ^ 2 ^ k).Nodup := by
  simp

/-- Negative control: the independence of `1, y, y²` is a real constraint (it fails for
`y = 1`: `1 + 1·1 + 0·1 = 0` in characteristic two). -/
theorem indep_one_false : ¬∀ a b c : F,
    algebraMap F EF a + algebraMap F EF b * 1 + algebraMap F EF c * 1 ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  intro h
  exact one_ne_zero (h 1 1 0 (by
    rw [map_one, map_zero, mul_one, zero_mul, add_zero, CharTwo.add_self_eq_zero])).1

end SpartanChain
