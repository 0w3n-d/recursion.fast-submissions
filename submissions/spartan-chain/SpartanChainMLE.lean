import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise

/-!
# Multilinear extensions over the Boolean cube (blueprint §3, §9.4 L-E1 … L-E4)

Generic over a commutative ring `R`. An index `u < 2 ^ ℓ` is the Boolean point whose coordinate
`l` is bit `l` of `u` (little-endian, variable `0` is the low bit, the one a sumcheck binds
first).

Specification (tables `Fin (2 ^ ℓ) → R`, points `Fin ℓ → R`):

* `cube u` the Boolean point of `u`; `eq a b = ∏_l (a_l b_l + (1 - a_l)(1 - b_l))`;
  `mle f r = Σ_u eq(r, u) · f(u)`; `fix0 f c` the table with variable `0` fixed to `c`.
* **L-E1** `eq_sum_one`, **L-E2** `eq_mle`, **L-E3** `mle_split` (the tensor split, with
  `join u₁ u₂ = u₁ + 2^a u₂`), **L-E4** `eq_frob`; and `mle_cube` (an extension agrees with
  its table on the cube), `mle_fix0` (fixing variable `0` is evaluating it).

Computable code (tables `Array R`, points `List R`, short):

* `eqTable r`: the `2 ^ |r|` values `eq(r, u)`, one pass per variable;
* `mleEval t r`: `Σ_u eq(r, u) · t[u]`; `bind0 t c`: variable `0` of `t` fixed to `c`;
* `eqPts a b`: `eq(a, b)` on two points.

They are proved equal to the specification through `tbl ℓ t u = t.getD u 0`, `pt r l = r[l]` and
`ptOf ℓ r l = r.getD l 0` (`tbl_eqTable`, `mleEval_eq`, `tbl_bind0`, `eqPts_eq`).
-/

namespace SpartanChain

open Finset

/-! ## Indices -/

/-- The index `2u + b` of `Fin (2 ^ (ℓ + 1))`: bit `0` is `b`, the bits above are `u`. -/
def dbl {ℓ : ℕ} (u : Fin (2 ^ ℓ)) (b : Bool) : Fin (2 ^ (ℓ + 1)) :=
  ⟨2 * u.val + b.toNat, by have := u.isLt; cases b <;> simp [pow_succ] <;> omega⟩

/-- The index `u₁ + 2^a u₂` of `Fin (2 ^ (a + b))`: low bits `u₁`, high bits `u₂`. -/
def join {a b : ℕ} (u₁ : Fin (2 ^ a)) (u₂ : Fin (2 ^ b)) : Fin (2 ^ (a + b)) :=
  ⟨2 ^ a * u₂.val + u₁.val, by
    have h1 := u₁.isLt; have h2 := u₂.isLt
    calc 2 ^ a * u₂.val + u₁.val < 2 ^ a * u₂.val + 2 ^ a := by omega
      _ = 2 ^ a * (u₂.val + 1) := by ring
      _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (a + b) := (pow_add 2 a b).symm⟩

theorem testBit_dbl_zero {ℓ : ℕ} (u : Fin (2 ^ ℓ)) (b : Bool) : (dbl u b).val.testBit 0 = b := by
  cases b <;> simp [dbl]

theorem testBit_dbl_succ {ℓ : ℕ} (u : Fin (2 ^ ℓ)) (b : Bool) (l : ℕ) :
    (dbl u b).val.testBit (l + 1) = u.val.testBit l := by
  rw [Nat.testBit_succ]
  congr 1
  cases b <;> simp [dbl] <;> omega

/-- `Fin (2 ^ ℓ) × Bool ≃ Fin (2 ^ (ℓ + 1))` by `dbl`. -/
def dblEquiv (ℓ : ℕ) : Fin (2 ^ ℓ) × Bool ≃ Fin (2 ^ (ℓ + 1)) where
  toFun p := dbl p.1 p.2
  invFun v := (⟨v.val / 2, by have := v.isLt; have := pow_succ 2 ℓ; omega⟩, v.val % 2 = 1)
  left_inv p := by
    obtain ⟨u, b⟩ := p
    refine Prod.ext (Fin.ext ?_) ?_ <;> cases b <;> simp [dbl] <;> omega
  right_inv v := by
    ext
    simp only [dbl]
    by_cases h : v.val % 2 = 1 <;> simp [h] <;> omega

/-- `Fin (2 ^ a) × Fin (2 ^ b) ≃ Fin (2 ^ (a + b))` by `join`. -/
def joinEquiv (a b : ℕ) : Fin (2 ^ a) × Fin (2 ^ b) ≃ Fin (2 ^ (a + b)) where
  toFun p := join p.1 p.2
  invFun v := (⟨v.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩,
    ⟨v.val / 2 ^ a, by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      exact lt_of_lt_of_eq v.isLt (by rw [pow_add, mul_comm])⟩)
  left_inv p := by
    obtain ⟨u₁, u₂⟩ := p
    have h1 := u₁.isLt
    ext <;> simp only [join]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h1]
    · rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt h1, add_zero]
  right_inv v := by
    ext
    simp only [join]
    exact Nat.div_add_mod v.val (2 ^ a)

/-- A sum over `Fin (2 ^ (ℓ + 1))` is a sum over pairs `2u, 2u + 1`. -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (F : Fin (2 ^ (ℓ + 1)) → M) :
    ∑ u, F u = ∑ u : Fin (2 ^ ℓ), (F (dbl u false) + F (dbl u true)) := by
  rw [← (dblEquiv ℓ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Fintype.sum_bool, add_comm]
  rfl

/-- A sum over `Fin (2 ^ 0)` is its one term. -/
theorem sum_cube_zero {M : Type*} [AddCommMonoid M] (F : Fin (2 ^ 0) → M) : ∑ u, F u = F 0 :=
  Fintype.sum_eq_single 0 fun u hu ↦ absurd (Fin.ext (by have := u.isLt; simp at this; omega)) hu

/-- **Sum of a product of per-bit factors** over the cube:
`Σ_u ∏_l g_l(u_l) = ∏_l (g_l 0 + g_l 1)`. -/
theorem sum_cube_prod {R : Type*} [CommSemiring R] {ℓ : ℕ} (g : Fin ℓ → Bool → R) :
    ∑ u : Fin (2 ^ ℓ), ∏ l : Fin ℓ, g l (u.val.testBit l) = ∏ l, (g l false + g l true) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [sum_cube_succ, Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ, Fin.val_zero, testBit_dbl_zero, Fin.val_succ, testBit_dbl_succ]
    rw [← ih (fun l ↦ g l.succ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    ring

/-! ## Specification -/

variable {R : Type*} [CommRing R]

/-- The Boolean point of the index `u`: coordinate `l` is bit `l` of `u`. -/
def cube {ℓ : ℕ} (u : Fin (2 ^ ℓ)) : Fin ℓ → R := fun l ↦ if u.val.testBit l then 1 else 0

/-- `eq(a, b) = ∏_l (a_l b_l + (1 - a_l)(1 - b_l))` (`∏_l (1 + a_l + b_l)` in characteristic
two). On the cube it is the indicator of `a = b`. -/
def eq {ℓ : ℕ} (a b : Fin ℓ → R) : R := ∏ l, (a l * b l + (1 - a l) * (1 - b l))

/-- The multilinear extension of the table `f` at `r`: `Σ_u eq(r, u) · f(u)`. -/
def mle {ℓ : ℕ} (f : Fin (2 ^ ℓ) → R) (r : Fin ℓ → R) : R := ∑ u, eq r (cube u) * f u

/-- The table `f` with variable `0` fixed to `c`: `f(2u) + c · (f(2u + 1) - f(2u))`. -/
def fix0 {ℓ : ℕ} (f : Fin (2 ^ (ℓ + 1)) → R) (c : R) : Fin (2 ^ ℓ) → R :=
  fun u ↦ f (dbl u false) + c * (f (dbl u true) - f (dbl u false))

theorem eq_cube {ℓ : ℕ} (r : Fin ℓ → R) (u : Fin (2 ^ ℓ)) :
    eq r (cube u) = ∏ l : Fin ℓ, if u.val.testBit l then r l else 1 - r l := by
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  by_cases h : u.val.testBit l <;> simp [cube, h]

theorem eq_swap {ℓ : ℕ} (a b : Fin ℓ → R) : eq a b = eq b a :=
  Finset.prod_congr rfl fun _ _ ↦ by ring

/-- The first factor of `eq` split off. -/
theorem eq_succ {ℓ : ℕ} (a b : Fin (ℓ + 1) → R) :
    eq a b = (a 0 * b 0 + (1 - a 0) * (1 - b 0)) * eq (Fin.tail a) (Fin.tail b) :=
  Fin.prod_univ_succ _

/-- `eq` on `2u + b` splits off variable `0`. -/
theorem eq_dbl {ℓ : ℕ} (r : Fin (ℓ + 1) → R) (u : Fin (2 ^ ℓ)) (b : Bool) :
    eq r (cube (dbl u b)) = (if b then r 0 else 1 - r 0) * eq (Fin.tail r) (cube u) := by
  rw [eq_cube, eq_cube, Fin.prod_univ_succ]
  simp only [Fin.val_zero, testBit_dbl_zero, Fin.val_succ, testBit_dbl_succ, Fin.tail]

/-- **Fixing variable `0` is evaluating it.** -/
theorem mle_fix0 {ℓ : ℕ} (f : Fin (2 ^ (ℓ + 1)) → R) (r : Fin (ℓ + 1) → R) :
    mle f r = mle (fix0 f (r 0)) (Fin.tail r) := by
  rw [mle, sum_cube_succ, mle]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [eq_dbl, fix0, Bool.false_eq_true, ↓reduceIte]
  ring

/-- With no variables the extension is the one entry. -/
theorem mle_zero (f : Fin (2 ^ 0) → R) (r : Fin 0 → R) : mle f r = f 0 := by
  rw [mle, sum_cube_zero, eq, Finset.univ_eq_empty, Finset.prod_empty, one_mul]

/-- **L-E1.** `Σ_u eq(r, u) = 1`. -/
theorem eq_sum_one {ℓ : ℕ} (r : Fin ℓ → R) : ∑ u : Fin (2 ^ ℓ), eq r (cube u) = 1 := by
  simp only [eq_cube]
  rw [sum_cube_prod (fun l b ↦ if b then r l else 1 - r l)]
  simp

/-- **L-E2.** `Σ_u eq(a, u) · eq(u, b) = eq(a, b)`. -/
theorem eq_mle {ℓ : ℕ} (a b : Fin ℓ → R) :
    ∑ u : Fin (2 ^ ℓ), eq a (cube u) * eq (cube u) b = eq a b := by
  simp only [eq_swap (cube _) b, eq_cube, ← Finset.prod_mul_distrib]
  rw [sum_cube_prod (fun l c ↦ (if c then a l else 1 - a l) * if c then b l else 1 - b l)]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

/-- `eq` on the cube is the indicator of equality. -/
theorem eq_cube_cube {ℓ : ℕ} (u v : Fin (2 ^ ℓ)) :
    eq (cube u) (cube v) = if u = v then (1 : R) else 0 := by
  rw [eq_cube]
  split_ifs with h
  · subst h
    refine Finset.prod_eq_one fun l _ ↦ ?_
    by_cases hb : u.val.testBit l <;> simp [cube, hb]
  · obtain ⟨l, hl⟩ : ∃ l : Fin ℓ, u.val.testBit l ≠ v.val.testBit l := by
      by_contra hall
      push Not at hall
      refine h (Fin.ext (Nat.eq_of_testBit_eq fun i ↦ ?_))
      by_cases hi : i < ℓ
      · exact hall ⟨i, hi⟩
      · have hu := u.isLt; have hv := v.isLt
        rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right two_pos
          (not_lt.mp hi))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv
          (Nat.pow_le_pow_right two_pos (not_lt.mp hi)))]
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    cases hv : v.val.testBit l <;> cases hu : u.val.testBit l <;> simp_all [cube]

/-- An extension agrees with its table on the cube. -/
theorem mle_cube {ℓ : ℕ} (f : Fin (2 ^ ℓ) → R) (v : Fin (2 ^ ℓ)) : mle f (cube v) = f v := by
  simp [mle, eq_cube_cube]

/-- A table whose extension vanishes everywhere is zero. -/
theorem eq_zero_of_mle {ℓ : ℕ} (f : Fin (2 ^ ℓ) → R) (h : ∀ r, mle f r = 0) : f = 0 :=
  funext fun v ↦ by rw [← mle_cube f v, h]; rfl

/-- `eq` on `join`: the low coordinates against `u₁`, the high ones against `u₂`. -/
theorem eq_append_join {a b : ℕ} (r₁ : Fin a → R) (r₂ : Fin b → R) (u₁ : Fin (2 ^ a))
    (u₂ : Fin (2 ^ b)) :
    eq (Fin.append r₁ r₂) (cube (join u₁ u₂)) = eq r₁ (cube u₁) * eq r₂ (cube u₂) := by
  simp only [eq_cube]
  rw [Fin.prod_univ_add]
  congr 1 <;> refine Finset.prod_congr rfl fun l _ ↦ ?_
  · simp only [join, Fin.val_castAdd, Fin.append_left]
    rw [Nat.testBit_two_pow_mul_add _ u₁.isLt, ite_eq_left l.isLt]
  · simp only [join, Fin.val_natAdd, Fin.append_right]
    rw [Nat.testBit_two_pow_mul_add _ u₁.isLt, ite_eq_right (show ¬(a + l.val < a) by omega),
      Nat.add_sub_cancel_left]

/-- **L-E3 (tensor split).** With the low `a` coordinates `r₁` and the high `b` coordinates `r₂`,
`f̃(r₁, r₂) = Σ_{u₁} eq(r₁, u₁) · f(u₁, ·)~(r₂)`: the slice form of §4.2. -/
theorem mle_split {a b : ℕ} (f : Fin (2 ^ (a + b)) → R) (r₁ : Fin a → R) (r₂ : Fin b → R) :
    mle f (Fin.append r₁ r₂) = ∑ u₁, eq r₁ (cube u₁) * mle (fun u₂ ↦ f (join u₁ u₂)) r₂ := by
  rw [mle, ← (joinEquiv a b).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u₁ _ ↦ ?_
  rw [mle, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u₂ _ ↦ ?_
  change eq (Fin.append r₁ r₂) (cube (join u₁ u₂)) * f (join u₁ u₂) = _
  rw [eq_append_join]
  ring

/-- **L-E4.** In characteristic two, `eq(r, u) ^ 2 ^ k = eq(r ^ 2 ^ k, u)` for Boolean `u`. -/
theorem eq_frob [CharP R 2] {ℓ : ℕ} (r : Fin ℓ → R) (u : Fin (2 ^ ℓ)) (k : ℕ) :
    eq r (cube u) ^ 2 ^ k = eq (fun l ↦ r l ^ 2 ^ k) (cube u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [eq_cube, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  split_ifs
  · rfl
  · rw [sub_pow_char_pow, one_pow]

/-- An extension is linear in its table. -/
theorem mle_add {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → R) (r : Fin ℓ → R) :
    mle (f + g) r = mle f r + mle g r := by
  simp only [mle, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## Computable code -/

/-- The table view of an array: entry `u` is `t[u]`, or `0` past the end. -/
def tbl (ℓ : ℕ) (t : Array R) : Fin (2 ^ ℓ) → R := fun u ↦ t.getD u 0

/-- The point of a list: coordinate `l` is `r[l]`. -/
def pt (r : List R) : Fin r.length → R := fun l ↦ r[l]

/-- The point of a list read at length `ℓ`: coordinate `l` is `r[l]`, or `0` past the end. -/
def ptOf (ℓ : ℕ) (r : List R) : Fin ℓ → R := fun l ↦ r.getD l 0

theorem pt_eq_ptOf (r : List R) : pt r = ptOf r.length r := by
  funext l
  simp [pt, ptOf, List.getD_eq_getElem?_getD, l.isLt]

omit [CommRing R] in
theorem pt_cons (c : R) (r : List R) : pt (c :: r) = Fin.cons c (pt r) := by
  funext l
  refine Fin.cases ?_ (fun i ↦ ?_) l <;> rfl

/-- `Σ_{i < n} F i` as a loop. -/
def sumTo {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) : M :=
  Nat.fold n (fun i _ acc ↦ acc + F i) 0

theorem sumTo_eq {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    sumTo n F = ∑ i ∈ range n, F i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, Nat.fold_succ, ← sumTo, ih, Finset.sum_range_succ]

theorem sumTo_eq_fin {M : Type*} [AddCommMonoid M] (ℓ : ℕ) (F : ℕ → M) :
    sumTo (2 ^ ℓ) F = ∑ u : Fin (2 ^ ℓ), F u := by
  rw [sumTo_eq, Fin.sum_univ_eq_sum_range]

/-- The `2 ^ |r|` values `eq(r, u)`, variable `0` the low bit: one pass per variable. -/
def eqTable : List R → Array R
  | [] => #[1]
  | c :: r =>
    let t := eqTable r
    Array.ofFn (n := 2 * t.size) fun u ↦
      t[u.val / 2]'(by omega) * if u.val % 2 = 1 then c else 1 - c

theorem eqTable_size (r : List R) : (eqTable r).size = 2 ^ r.length := by
  induction r with
  | nil => rfl
  | cons c r ih => simp [eqTable, ih, pow_succ, mul_comm]

/-- **The table of `eq` is `eq`.** -/
theorem tbl_eqTable (r : List R) : tbl r.length (eqTable r) = fun u ↦ eq (pt r) (cube u) := by
  induction r with
  | nil => funext u; simp [tbl, eqTable, eq, Fin.fin_one_eq_zero u]
  | cons c r ih =>
    funext v
    obtain ⟨⟨u, b⟩, rfl⟩ := (dblEquiv r.length).surjective v
    change tbl (r.length + 1) (eqTable (c :: r)) (dbl u b) = eq (pt (c :: r)) (cube (dbl u b))
    rw [eq_dbl, pt_cons, Fin.cons_zero, Fin.tail_cons, ← congrFun ih u]
    have hs := eqTable_size r
    have hu := u.isLt
    have hlt : 2 * u.val + b.toNat < 2 * (eqTable r).size := by
      rw [hs]; cases b <;> simp <;> omega
    simp only [tbl, eqTable, dbl, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt,
      dite_true, Option.getD_some]
    have h2 : (2 * u.val + b.toNat) / 2 = u.val := by cases b <;> simp <;> omega
    have hlt' : u.val < (eqTable r).size := by rw [hs]; exact hu
    simp only [h2, Array.getElem?_eq_getElem hlt', Option.getD_some]
    cases b <;> simp [mul_comm]

/-- `tbl_eqTable` at a length given by an equation. -/
theorem tbl_eqTable' {ℓ : ℕ} (r : List R) (h : r.length = ℓ) :
    tbl ℓ (eqTable r) = fun u ↦ eq (ptOf ℓ r) (cube u) := by
  subst h
  rw [tbl_eqTable, pt_eq_ptOf]

/-- `Σ_u t[u] · s[u]` over the indices of `t`. -/
def dot (t s : Array R) : R := sumTo t.size fun u ↦ t.getD u 0 * s.getD u 0

/-- `f̃(r) = Σ_u eq(r, u) · t[u]`, computed with `eqTable`. -/
def mleEval (t : Array R) (r : List R) : R := dot (eqTable r) t

/-- **The computed extension is the extension** of the table `t` (entries past the end are
`0`). -/
theorem mleEval_eq (t : Array R) (r : List R) : mleEval t r = mle (tbl r.length t) (pt r) := by
  rw [mleEval, dot, eqTable_size, sumTo_eq_fin, mle]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← congrFun (tbl_eqTable r) u]
  rfl

/-- `mleEval_eq` at a length given by an equation. -/
theorem mleEval_eq' {ℓ : ℕ} (t : Array R) (r : List R) (h : r.length = ℓ) :
    mleEval t r = mle (tbl ℓ t) (ptOf ℓ r) := by
  subst h
  rw [mleEval_eq, pt_eq_ptOf]

/-- Variable `0` of `t` fixed to `c`: `t[2j] + c · (t[2j + 1] - t[2j])`. -/
def bind0 (t : Array R) (c : R) : Array R :=
  Array.ofFn (n := t.size / 2) fun j ↦
    t[2 * j.val]'(by omega) + c * (t[2 * j.val + 1]'(by omega) - t[2 * j.val]'(by omega))

theorem bind0_size (t : Array R) (c : R) : (bind0 t c).size = t.size / 2 := Array.size_ofFn

/-- **`bind0` is `fix0`** on a table of the right size. -/
theorem tbl_bind0 {ℓ : ℕ} (t : Array R) (c : R) (ht : t.size = 2 ^ (ℓ + 1)) :
    tbl ℓ (bind0 t c) = fix0 (tbl (ℓ + 1) t) c := by
  funext u
  have hu := u.isLt
  have hj : u.val < t.size / 2 := by rw [ht, pow_succ]; omega
  have h0 : 2 * u.val < t.size := by omega
  have h1 : 2 * u.val + 1 < t.size := by omega
  simp only [tbl, fix0, dbl, bind0, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj,
    dite_true, Option.getD_some, Bool.toNat_false, add_zero, Bool.toNat_true,
    Array.getElem?_eq_getElem h0, Array.getElem?_eq_getElem h1]

/-- `eq(a, b)` on two points of the same length. -/
def eqPts (a b : List R) : R := (List.zipWith (fun x y ↦ x * y + (1 - x) * (1 - y)) a b).prod

theorem eqPts_cons (x y : R) (a b : List R) :
    eqPts (x :: a) (y :: b) = (x * y + (1 - x) * (1 - y)) * eqPts a b := by
  rw [eqPts, List.zipWith_cons_cons, List.prod_cons, ← eqPts]

/-- **`eqPts` is `eq`** on two points of length `ℓ`. -/
theorem eqPts_eq {ℓ : ℕ} (a b : List R) (ha : a.length = ℓ) (hb : b.length = ℓ) :
    eqPts a b = eq (ptOf ℓ a) (ptOf ℓ b) := by
  induction ℓ generalizing a b with
  | zero =>
    rw [List.length_eq_zero_iff.mp ha, List.length_eq_zero_iff.mp hb]
    simp [eqPts, eq]
  | succ ℓ ih =>
    obtain _ | ⟨x, a⟩ := a
    · simp at ha
    obtain _ | ⟨y, b⟩ := b
    · simp at hb
    simp only [List.length_cons, add_left_inj] at ha hb
    rw [eqPts_cons, ih a b ha hb, eq_succ]
    rfl

end SpartanChain
