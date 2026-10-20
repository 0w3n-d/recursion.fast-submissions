import SpartanChainChainMle

/-!
# The columns of the chain matrices: `Σ_x eq(r_x, x) · M(x, y)` (the prover's inner table)

For the inner sumcheck the prover needs, for every column `y`, `M̃(r_x, y) = Σ_x eq(r_x, x) M(x, y)`
(Spartan; `matMle_cube`). For the chain matrices this is, column by column (`colA`, `colB`,
`colC`): the block part `(1 − r_top) · eq(r_T, t) · (A0ᵀ e)(j)` for `y = j + 2^14 t` (the transpose
of the block against `e(k) = eq(r_x[0..14), k)`, `bsum`), plus the few `eq(r_x, x)` of the wiring,
tail and row-512 entries in that column. `col_chainA` … prove the formulas from the sparse
definitions.
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast

variable {E : Type} [Field E]

/-- The transpose of a block matrix against `eq(r_x[0..14), ·)`: `Σ_k M0(k, j) eq(R, k)`. -/
def bsum (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool) (R : ℕ → E) (j : ℕ) : E :=
  ∑ k : Pos Blake2sCircuit.m, if bk k (pos j) = true then eqv R 14 k.val else 0

/-- Column `v` of `Ã(r_x, ·)`: `Q x = eq(r_x, x)`, `QT t = eq(r_x[14..14+κ), t)`, `rtop` the top
coordinate, `bA` the block transpose. -/
def colA (n κ : ℕ) (Q QT : ℕ → E) (rtop : E) (bA : ℕ → E) (v : ℕ) : E :=
  (if v < wLen κ then (1 - rtop) * QT (v / 16384) * bA (v % 16384)
    else 0) +
  (if v = wLen κ then ∑ t : Fin (2 ^ κ), Q (512 + 16384 * t.val) else 0) +
  (if v < wLen κ ∧ 256 ≤ v % 16384 ∧ v % 16384 < 512 ∧ v / 16384 + 1 < 2 ^ κ then
    Q (wLen κ + 256 * (v / 16384 + 1) + (v % 16384 - 256)) else 0) +
  (if wLen κ + 1 ≤ v ∧ v < wLen κ + 1 + 256 then
    Q (wLen κ + (v - (wLen κ + 1))) else 0) +
  (if 256 + 16384 * (n - 1) ≤ v ∧ v < 256 + 16384 * (n - 1) + 256 then
    Q (wLen κ + 2 ^ (8 + κ) + (v - (256 + 16384 * (n - 1)))) else 0)

/-- Column `v` of `B̃(r_x, ·)`. -/
def colB (κ : ℕ) (Q QT : ℕ → E) (rtop : E) (bB : ℕ → E) (v : ℕ) : E :=
  (if v < wLen κ then (1 - rtop) * QT (v / 16384) * bB (v % 16384)
    else 0) +
  (if v = wLen κ then ∑ t : Fin (2 ^ κ), Q (512 + 16384 * t.val) +
    ∑ p : Fin (2 ^ κ) × Fin 256, Q (wLen κ + 256 * p.1.val + p.2.val) +
    ∑ j : Fin 256, Q (wLen κ + 2 ^ (8 + κ) + j.val) else 0)

/-- Column `v` of `C̃(r_x, ·)`. -/
def colC (κ : ℕ) (Q : ℕ → E) (v : ℕ) : E :=
  (if v < wLen κ then Q v else 0) +
  (if v < wLen κ ∧ 648 ≤ v % 16384 ∧ v % 16384 < 904 then
    Q (wLen κ + 256 * (v / 16384) + (v % 16384 - 648)) else 0) +
  (if wLen κ + 257 ≤ v ∧ v < wLen κ + 257 + 256 then
    Q (wLen κ + 2 ^ (8 + κ) + (v - (wLen κ + 257))) else 0)

/-! ## Sums over the rows -/

/-- The rows of one indicator term, in column `y`. -/
theorem colSum {L : ℕ} (rx : Fin L → E) (y : Fin (2 ^ L)) {ι : Type} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (f g : ι → ℕ) (hf : ∀ p, P p → f p < 2 ^ L) :
    ∑ x : Fin (2 ^ L), eq rx (cube x) * (∑ p, if P p ∧ x.val = f p ∧ y.val = g p then (1 : E) else 0) =
      ∑ p, if P p ∧ y.val = g p then eqv (extPt rx) L (f p) else 0 := by
  simp only [mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p _ ↦ ?_
  by_cases hp : P p ∧ y.val = g p
  · rw [ite_eq_left hp, sum_eq_single ⟨f p, hf p hp.1⟩ (fun x _ hx ↦ by
      rw [ite_eq_right (fun h ↦ hx (Fin.ext h.2.1)), mul_zero]) (by simp)]
    simp [hp, eq_ext]
  · rw [ite_eq_right hp]
    exact sum_eq_zero fun x _ ↦ by
      rw [ite_eq_right (fun h ↦ hp ⟨h.1, h.2.2⟩), mul_zero]

/-- The rows of one indicator term without side condition, in column `y`. -/
theorem colSum' {L : ℕ} (rx : Fin L → E) (y : Fin (2 ^ L)) {ι : Type} [Fintype ι] (f g : ι → ℕ)
    (hf : ∀ p, f p < 2 ^ L) :
    ∑ x : Fin (2 ^ L), eq rx (cube x) * (∑ p, if x.val = f p ∧ y.val = g p then (1 : E) else 0) =
      ∑ p, if y.val = g p then eqv (extPt rx) L (f p) else 0 := by
  have := colSum rx y (fun _ : ι ↦ True) f g (fun p _ ↦ hf p)
  simpa using this

section Terms

variable {κ : ℕ} (R : ℕ → E) (v : ℕ)

private theorem lt14 (k : Pos Blake2sCircuit.m) : k.val < 16384 := k.isLt

theorem colT1 (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool) :
    (∑ p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m,
      if bk p.2.1 p.2.2 = true ∧ v = p.2.2.val + 16384 * p.1.val then
        eqv R (14 + κ + 1) (p.2.1.val + 16384 * p.1.val) else 0) =
    if v < wLen κ then (1 - R (14 + κ)) * eqv (shiftPt R 14) κ (v / 16384) * bsum bk R (v % 16384)
      else 0 := by
  have hw := wLen_eq κ
  have hp : ((pos (v % 16384) : Pos Blake2sCircuit.m) : ℕ) = v % 16384 :=
    pos_val (show v % 16384 < 2 ^ Blake2sCircuit.m by show _ < 16384; omega)
  rw [Fintype.sum_prod_type]
  split_ifs with hv
  · rw [sum_eq_single (⟨v / 16384, by omega⟩ : Fin (2 ^ κ))]
    · rw [Fintype.sum_prod_type, bsum, mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sum_eq_single (pos (v % 16384) : Pos Blake2sCircuit.m)]
      · by_cases hb : bk k (pos (v % 16384)) = true
        · rw [ite_eq_left ⟨hb, by rw [hp]; simp; omega⟩, ite_eq_left hb,
            eqv_w R _ _ (lt14 k) (by simp; omega)]
          simp only; ring
        · rw [ite_eq_right (fun h ↦ hb h.1), ite_eq_right hb, mul_zero]
      · intro j _ hj
        refine ite_eq_right fun h ↦ hj (Fin.ext ?_)
        rw [hp]; have := lt14 j; simp at h; omega
      · simp
    · intro t _ ht
      refine sum_eq_zero fun p _ ↦ ite_eq_right fun h ↦ ht (Fin.ext ?_)
      have := lt14 p.2; simp only at h ⊢; omega
    · simp
  · refine sum_eq_zero fun t _ ↦ sum_eq_zero fun p _ ↦ ite_eq_right fun h ↦ hv ?_
    have := lt14 p.2; have := t.isLt; simp only at h; omega

theorem colT2 {ι : Type} [Fintype ι] (c : ℕ) (f : ι → E) :
    (∑ t : ι, if v = c then f t else 0) = if v = c then ∑ t, f t else 0 := by
  split_ifs <;> simp

theorem colT3A :
    (∑ p : Fin (2 ^ κ) × Fin 256, if 1 ≤ p.1.val ∧ v = 256 + p.2.val + 16384 * (p.1.val - 1) then
      eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val) else 0) =
    if v < wLen κ ∧ 256 ≤ v % 16384 ∧ v % 16384 < 512 ∧ v / 16384 + 1 < 2 ^ κ then
      eqv R (14 + κ + 1) (wLen κ + 256 * (v / 16384 + 1) + (v % 16384 - 256)) else 0 := by
  have hw := wLen_eq κ
  split_ifs with hv
  · exact sum_ite_single _ (fun p : Fin (2 ^ κ) × Fin 256 ↦
        eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val))
      (⟨v / 16384 + 1, hv.2.2.2⟩, ⟨v % 16384 - 256, by omega⟩)
      fun p ↦ ⟨fun h ↦ Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega)),
        fun h ↦ by subst h; simp; omega⟩
  · exact sum_ite_none _ _ fun p h ↦ hv (by have := p.1.isLt; have := p.2.isLt; omega)

theorem colT5A (n : ℕ) :
    (∑ j : Fin 256, if v = 256 + j.val + 16384 * (n - 1) then
      eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j.val) else 0) =
    if 256 + 16384 * (n - 1) ≤ v ∧ v < 256 + 16384 * (n - 1) + 256 then
      eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + (v - (256 + 16384 * (n - 1)))) else 0 := by
  rw [← sum_offset (N := 256) (fun j ↦ eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j))
    (256 + 16384 * (n - 1)) v]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases h : v = 256 + j.val + 16384 * (n - 1)
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem colT2C :
    (∑ p : Fin (2 ^ κ) × Fin 256, if v = 648 + p.2.val + 16384 * p.1.val then
      eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val) else 0) =
    if v < wLen κ ∧ 648 ≤ v % 16384 ∧ v % 16384 < 904 then
      eqv R (14 + κ + 1) (wLen κ + 256 * (v / 16384) + (v % 16384 - 648)) else 0 := by
  have hw := wLen_eq κ
  split_ifs with hv
  · exact sum_ite_single _ (fun p : Fin (2 ^ κ) × Fin 256 ↦
        eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val))
      (⟨v / 16384, by omega⟩, ⟨v % 16384 - 648, by omega⟩)
      fun p ↦ ⟨fun h ↦ Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega)),
        fun h ↦ by subst h; simp; omega⟩
  · exact sum_ite_none _ _ fun p h ↦ hv (by have := p.1.isLt; have := p.2.isLt; omega)

end Terms

/-! ## The columns -/

section Cols

variable {κ : ℕ}

private theorem bnd' (κ : ℕ) : 2 ^ (14 + κ + 1) = 32768 * 2 ^ κ := ixLen_eq κ

theorem col_chainA {n : ℕ} (rx : Fin (14 + κ + 1) → E) (y : Ix κ) :
    ∑ x : Ix κ, eq rx (cube x) * chainA n κ x y =
      colA n κ (eqv (extPt rx) (14 + κ + 1)) (eqv (shiftPt (extPt rx) 14) κ) (extPt rx (14 + κ))
        (bsum blockA (extPt rx)) y.val := by
  have hL := bnd' κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [chainA, mul_add, sum_add_distrib]
  rw [colSum rx y (fun p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m ↦
        blockA p.2.1 p.2.2 = true) (fun p ↦ p.2.1.val + 16384 * p.1.val)
        (fun p ↦ p.2.2.val + 16384 * p.1.val)
        (fun p _ ↦ by have := p.1.isLt; have : p.2.1.val < 16384 := p.2.1.isLt; omega),
    colSum' rx y (fun t : Fin (2 ^ κ) ↦ 512 + 16384 * t.val) (fun _ ↦ wLen κ)
      (fun t ↦ by have := t.isLt; omega),
    colSum rx y (fun p : Fin (2 ^ κ) × Fin 256 ↦ 1 ≤ p.1.val)
      (fun p ↦ wLen κ + 256 * p.1.val + p.2.val) (fun p ↦ 256 + p.2.val + 16384 * (p.1.val - 1))
      (fun p _ ↦ by have := p.1.isLt; have := p.2.isLt; omega),
    colSum' rx y (fun j : Fin 256 ↦ wLen κ + j.val) (fun j ↦ wLen κ + 1 + j.val)
      (fun j ↦ by have := j.isLt; omega),
    colSum' rx y (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val)
      (fun j ↦ 256 + j.val + 16384 * (n - 1)) (fun j ↦ by have := j.isLt; omega),
    colT1, colT2, colT3A, colT5A,
    sum_offset (N := 256) (fun j ↦ eqv (extPt rx) (14 + κ + 1) (wLen κ + j)) (wLen κ + 1) y.val,
    colA]

theorem col_chainB (rx : Fin (14 + κ + 1) → E) (y : Ix κ) :
    ∑ x : Ix κ, eq rx (cube x) * chainB κ x y =
      colB κ (eqv (extPt rx) (14 + κ + 1)) (eqv (shiftPt (extPt rx) 14) κ) (extPt rx (14 + κ))
        (bsum blockB (extPt rx)) y.val := by
  have hL := bnd' κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [chainB, mul_add, sum_add_distrib]
  rw [colSum rx y (fun p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m ↦
        blockB p.2.1 p.2.2 = true) (fun p ↦ p.2.1.val + 16384 * p.1.val)
        (fun p ↦ p.2.2.val + 16384 * p.1.val)
        (fun p _ ↦ by have := p.1.isLt; have : p.2.1.val < 16384 := p.2.1.isLt; omega),
    colSum' rx y (fun t : Fin (2 ^ κ) ↦ 512 + 16384 * t.val) (fun _ ↦ wLen κ)
      (fun t ↦ by have := t.isLt; omega),
    colSum' rx y (fun p : Fin (2 ^ κ) × Fin 256 ↦ wLen κ + 256 * p.1.val + p.2.val)
      (fun _ ↦ wLen κ) (fun p ↦ by have := p.1.isLt; have := p.2.isLt; omega),
    colSum' rx y (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val) (fun _ ↦ wLen κ)
      (fun j ↦ by have := j.isLt; omega),
    colT1, colT2, colT2, colT2, colB]
  by_cases hv : y.val = wLen κ <;> simp [hv]

theorem col_chainC (rx : Fin (14 + κ + 1) → E) (y : Ix κ) :
    ∑ x : Ix κ, eq rx (cube x) * chainC κ x y = colC κ (eqv (extPt rx) (14 + κ + 1)) y.val := by
  have hL := bnd' κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [chainC, mul_add, sum_add_distrib]
  rw [colSum' rx y (fun u : Fin (wLen κ) ↦ u.val) (fun u ↦ u.val)
      (fun u ↦ by have := u.isLt; omega),
    colSum' rx y (fun p : Fin (2 ^ κ) × Fin 256 ↦ wLen κ + 256 * p.1.val + p.2.val)
      (fun p ↦ 648 + p.2.val + 16384 * p.1.val)
      (fun p ↦ by have := p.1.isLt; have := p.2.isLt; omega),
    colSum' rx y (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val) (fun j ↦ wLen κ + 257 + j.val)
      (fun j ↦ by have := j.isLt; omega),
    colT2C,
    sum_offset (N := 256) (fun j ↦ eqv (extPt rx) (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j))
      (wLen κ + 257) y.val, colC]
  have h0 : (∑ u : Fin (wLen κ), if y.val = u.val then eqv (extPt rx) (14 + κ + 1) u.val else 0) =
      if y.val < wLen κ then eqv (extPt rx) (14 + κ + 1) y.val else 0 := by
    have := sum_offset (N := wLen κ) (fun u ↦ eqv (extPt rx) (14 + κ + 1) u) 0 y.val
    simpa using this
  rw [h0]

end Cols

end SpartanChain
