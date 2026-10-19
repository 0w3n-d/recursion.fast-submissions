import SpartanChainChain
import SpartanChainBlake2sWalk

/-!
# The extensions of the chain matrices (BLUEPRINT-R1 §2.4; L-C4 `shift_mle`, `matrix_mle_eq`)

Points are functions `ℕ → R` (coordinate `l` is variable `l`; a point of `Fin L → R` is read
through `extPt`). `eqv r L v = ∏_{l < L} (v_l ? r_l : 1 − r_l)` is `eq(r, v)` on the bits of `v`
(`eq_cube_eqv`); it factors along a split of the bits (`eqv_add`).

* `shiftMle a b κ`: the extension of `S(t, t') = [t' + 1 = t]` (§2.4.1), by recursion on the low
  bit: `S̃(a, b) = a_0 (1 − b_0) eq(a', b') + (1 − a_0) b_0 S̃(a', b')`. In characteristic two this
  is the blueprint's closed formula. **L-C4 `shift_mle`**: on the cube it is the Boolean shift;
  `shift_sum`: it is the extension (`Σ_{t,t'} eq(a,t) eq(b,t') [t'+1 = t]`).
* `matMle_ind`: the extension of an indicator matrix is a sum of `eqv` products over its nonzero
  entries.
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast

variable {R : Type*} [CommRing R]

/-! ## `eq` on the bits of a natural number -/

/-- `eq(r, v)` on the low `L` bits of `v`. -/
def eqv (r : ℕ → R) (L v : ℕ) : R := ∏ l ∈ range L, if v.testBit l then r l else 1 - r l

/-- The point `r` shifted by `p`: coordinate `l` is `r (p + l)`. -/
def shiftPt (r : ℕ → R) (p : ℕ) : ℕ → R := fun l ↦ r (p + l)

/-- `eq(a, b) = ∏_{l < L} (a_l b_l + (1 − a_l)(1 − b_l))` on two points. -/
def eqp (a b : ℕ → R) (L : ℕ) : R := ∏ l ∈ range L, (a l * b l + (1 - a l) * (1 - b l))

/-- A point of `Fin L → R`, read on `ℕ` (`0` past the end). -/
def extPt {L : ℕ} (r : Fin L → R) : ℕ → R := fun l ↦ if h : l < L then r ⟨l, h⟩ else 0

theorem eqv_zero_len (r : ℕ → R) (v : ℕ) : eqv r 0 v = 1 := by simp [eqv]

theorem eqv_succ (r : ℕ → R) (L v : ℕ) :
    eqv r (L + 1) v = (if v.testBit 0 then r 0 else 1 - r 0) * eqv (shiftPt r 1) L (v / 2) := by
  rw [eqv, prod_range_succ', mul_comm, eqv]
  congr 1
  refine prod_congr rfl fun l _ ↦ ?_
  simp only [shiftPt, Nat.testBit_succ, show 1 + l = l + 1 by omega]

theorem shiftPt_shiftPt (r : ℕ → R) (p q : ℕ) : shiftPt (shiftPt r p) q = shiftPt r (p + q) := by
  funext l; simp only [shiftPt, Nat.add_assoc]

theorem shiftPt_zero (r : ℕ → R) : shiftPt r 0 = r := by funext l; simp [shiftPt]

/-- **The split of `eq` along the bits**: low `p` bits `a`, high bits `b`. -/
theorem eqv_add (r : ℕ → R) {p L : ℕ} (hp : p ≤ L) {a : ℕ} (ha : a < 2 ^ p) (b : ℕ) :
    eqv r L (a + 2 ^ p * b) = eqv r p a * eqv (shiftPt r p) (L - p) b := by
  induction p generalizing r L a with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    simp [eqv_zero_len, shiftPt_zero]
  | succ p ih =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have e2 : 2 ^ (p + 1) * b = 2 * (2 ^ p * b) := by ring
    have ha' : a / 2 < 2 ^ p := by rw [pow_succ] at ha; omega
    have hpL : p ≤ L := by omega
    rw [eqv_succ, eqv_succ, show (a + 2 ^ (p + 1) * b) / 2 = a / 2 + 2 ^ p * b by rw [e2]; omega,
      ih (shiftPt r 1) hpL ha', shiftPt_shiftPt,
      show L + 1 - (p + 1) = L - p by omega, show 1 + p = p + 1 by omega]
    have hm : (a + 2 ^ (p + 1) * b) % 2 = a % 2 := by rw [e2]; omega
    have : (a + 2 ^ (p + 1) * b).testBit 0 = a.testBit 0 := by
      simp only [Nat.testBit_zero, hm]
    rw [this, mul_assoc]

/-- `eqv` at zero: `∏ (1 − r_l)`. -/
theorem eqv_zero (r : ℕ → R) (L : ℕ) : eqv r L 0 = ∏ l ∈ range L, (1 - r l) := by
  simp [eqv]

/-- `eqv` reads only the low `L` bits. -/
theorem eqv_mod (r : ℕ → R) (L v : ℕ) : eqv r L (v % 2 ^ L) = eqv r L v := by
  refine prod_congr rfl fun l hl ↦ ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (mem_range.mp hl), Bool.true_and]

/-- `eqv` is `eq` on the cube. -/
theorem eqv_eq_eq (r : ℕ → R) (L : ℕ) (v : Fin (2 ^ L)) :
    eqv r L v.val = eq (fun l : Fin L ↦ r l) (cube v) := by
  rw [eq_cube, eqv, ← Fin.prod_univ_eq_prod_range (fun l ↦ if v.val.testBit l then r l else 1 - r l)]

theorem eqp_eq_eq (a b : ℕ → R) (L : ℕ) :
    eqp a b L = eq (fun l : Fin L ↦ a l) (fun l : Fin L ↦ b l) := by
  rw [eqp, eq, ← Fin.prod_univ_eq_prod_range (fun l ↦ a l * b l + (1 - a l) * (1 - b l))]

/-- **L-E1** on `eqv`: `Σ_{v < 2^L} eq(r, v) = 1`. -/
theorem sum_eqv (r : ℕ → R) (L : ℕ) : ∑ v : Fin (2 ^ L), eqv r L v.val = 1 := by
  simp only [eqv_eq_eq]; exact eq_sum_one _

/-- **L-E2** on `eqv`: `Σ_{v < 2^L} eq(a, v) eq(b, v) = eq(a, b)`. -/
theorem sum_eqv_mul (a b : ℕ → R) (L : ℕ) :
    ∑ v : Fin (2 ^ L), eqv a L v.val * eqv b L v.val = eqp a b L := by
  simp only [eqv_eq_eq, eqp_eq_eq]
  rw [← eq_mle]
  exact sum_congr rfl fun v _ ↦ by rw [eq_swap (fun l : Fin L ↦ b l) (cube v)]

theorem eqv_dbl (r : ℕ → R) (L : ℕ) (u : Fin (2 ^ L)) (c : Bool) :
    eqv r (L + 1) (dbl u c).val = (if c then r 0 else 1 - r 0) * eqv (shiftPt r 1) L u.val := by
  rw [eqv_succ, testBit_dbl_zero]
  congr 2
  cases c <;> simp [dbl] <;> omega

/-! ## The shift -/

/-- `S̃(a, b)`, the extension of `[t' + 1 = t]` (`a ↔ t`, `b ↔ t'`) on `κ` variables. -/
def shiftMle (a b : ℕ → R) : ℕ → R
  | 0 => 0
  | κ + 1 => a 0 * (1 - b 0) * eqp (shiftPt a 1) (shiftPt b 1) κ +
      (1 - a 0) * b 0 * shiftMle (shiftPt a 1) (shiftPt b 1) κ

/-- **`shift_sum`**: `S̃(a, b) = Σ_{t, t'} eq(a, t) eq(b, t') [t' + 1 = t]`. -/
theorem shift_sum (κ : ℕ) : ∀ a b : ℕ → R,
    ∑ t : Fin (2 ^ κ), ∑ t' : Fin (2 ^ κ),
      eqv a κ t.val * eqv b κ t'.val * (if t'.val + 1 = t.val then 1 else 0) = shiftMle a b κ := by
  induction κ with
  | zero =>
    intro a b
    simp only [shiftMle]
    refine sum_eq_zero fun t _ ↦ sum_eq_zero fun t' _ ↦ ?_
    have h1 : t.val = 0 := by have := t.isLt; simp at this; omega
    have h2 : t'.val = 0 := by have := t'.isLt; simp at this; omega
    rw [h1, h2, ite_eq_right (by omega), mul_zero]
  | succ κ ih =>
    intro a b
    have hS := ih (shiftPt a 1) (shiftPt b 1)
    have hE := sum_eqv_mul (shiftPt a 1) (shiftPt b 1) κ
    have hE' : eqp (shiftPt a 1) (shiftPt b 1) κ = ∑ u : Fin (2 ^ κ), ∑ u' : Fin (2 ^ κ),
        eqv (shiftPt a 1) κ u.val * eqv (shiftPt b 1) κ u'.val *
          (if u'.val = u.val then 1 else 0) := by
      rw [← hE]
      refine sum_congr rfl fun u _ ↦ ?_
      rw [sum_eq_single u (fun u' _ hu ↦ by rw [ite_eq_right (fun h ↦ hu (Fin.ext h)), mul_zero])
        (by simp)]
      all_goals simp
    rw [shiftMle, hE', ← hS, mul_sum, mul_sum, ← sum_add_distrib, sum_cube_succ]
    simp only [sum_cube_succ, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    refine sum_congr rfl fun u' _ ↦ ?_
    simp only [eqv_dbl, Bool.false_eq_true, ↓reduceIte]
    simp only [dbl, Bool.toNat_false, Bool.toNat_true]
    have c1 : (2 * u'.val + 0 + 1 = 2 * u.val + 0) ↔ False := iff_false_intro (by omega)
    have c4 : (2 * u'.val + 1 + 1 = 2 * u.val + 1) ↔ False := iff_false_intro (by omega)
    have c2 : (2 * u'.val + 1 + 1 = 2 * u.val + 0) ↔ (u'.val + 1 = u.val) := by
      constructor <;> intro h <;> omega
    have c3 : (2 * u'.val + 0 + 1 = 2 * u.val + 1) ↔ (u'.val = u.val) := by
      constructor <;> intro h <;> omega
    simp only [c1, c2, c3, c4, ↓reduceIte]
    by_cases h1 : u'.val = u.val
    · have h2 : ¬ (u'.val + 1 = u.val) := by omega
      simp only [h1, h2, ↓reduceIte]; ring
    · by_cases h2 : u'.val + 1 = u.val
      · simp only [h1, h2, ↓reduceIte]; ring
      · simp only [h1, h2, ↓reduceIte]; ring

/-- **L-C4 `shift_mle`**: on the cube, `S̃` is the Boolean shift `[t' + 1 = t]`. -/
theorem shift_mle (κ : ℕ) (t t' : Fin (2 ^ κ)) :
    shiftMle (fun l ↦ if t.val.testBit l then (1 : R) else 0)
      (fun l ↦ if t'.val.testBit l then (1 : R) else 0) κ =
      if t'.val + 1 = t.val then 1 else 0 := by
  rw [← shift_sum]
  have hc : ∀ (v w : Fin (2 ^ κ)),
      eqv (fun l ↦ if v.val.testBit l then (1 : R) else 0) κ w.val = if w = v then 1 else 0 := by
    intro v w
    rw [eqv_eq_eq]
    have : (fun l : Fin κ ↦ if v.val.testBit l then (1 : R) else 0) = cube v := rfl
    rw [this, eq_cube_cube]
    split_ifs with h1 h2 h2 <;> first | rfl | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
  simp only [hc]
  rw [sum_eq_single t (fun u _ hu ↦ sum_eq_zero fun u' _ ↦ by rw [ite_eq_right hu]; ring) (by simp),
    sum_eq_single t' (fun u' _ hu ↦ by rw [ite_eq_right hu]; ring) (by simp)]
  simp

/-! ## The chain layout, bit by bit -/

section Layout

variable (r : ℕ → R) {κ : ℕ}

theorem eqv_one_zero (r : ℕ → R) : eqv r 1 0 = 1 - r 0 := by simp [eqv]
theorem eqv_one_one (r : ℕ → R) : eqv r 1 1 = r 0 := by simp [eqv]

/-- A witness position `k + 2^14 t`: block bits, batch bits, `top = 0`. -/
theorem eqv_w (k t : ℕ) (hk : k < 16384) (ht : t < 2 ^ κ) :
    eqv r (14 + κ + 1) (k + 16384 * t) =
      eqv r 14 k * eqv (shiftPt r 14) κ t * (1 - r (14 + κ)) := by
  rw [show k + 16384 * t = k + 2 ^ 14 * (t + 2 ^ κ * 0) by ring, eqv_add r (by omega) hk,
    show 14 + κ + 1 - 14 = κ + 1 by omega, eqv_add _ (by omega) ht, Nat.add_sub_cancel_left,
    shiftPt_shiftPt, eqv_one_zero, mul_assoc]
  rfl

/-- A public position `2^(14+κ) + u`, `u < 2^(14+κ)`: `top = 1`. -/
theorem eqv_pub (u : ℕ) (hu : u < 2 ^ (14 + κ)) :
    eqv r (14 + κ + 1) (wLen κ + u) = eqv r (14 + κ) u * r (14 + κ) := by
  rw [show wLen κ + u = u + 2 ^ (14 + κ) * 1 by rw [wLen]; ring, eqv_add r (by omega) hu,
    Nat.add_sub_cancel_left, eqv_one_one]
  rfl

/-- The low `14 + κ` bits of a block position. -/
theorem eqv_blk (k t : ℕ) (hk : k < 16384) :
    eqv r (14 + κ) (k + 16384 * t) = eqv r 14 k * eqv (shiftPt r 14) κ t := by
  rw [show k + 16384 * t = k + 2 ^ 14 * t by norm_num, eqv_add r (by omega) hk,
    Nat.add_sub_cancel_left]

/-- A wiring row `2^(14+κ) + 256 t + j`. -/
theorem eqv_wire (j t : ℕ) (hj : j < 256) (ht : t < 2 ^ κ) :
    eqv r (14 + κ + 1) (wLen κ + 256 * t + j) =
      eqv r 8 j * eqv (shiftPt r 8) κ t * eqv (shiftPt r (8 + κ)) 7 64 := by
  have h : wLen κ + 256 * t + j = j + 2 ^ 8 * (t + 2 ^ κ * 64) := by
    rw [wLen_eq]; ring_nf
  rw [h, eqv_add r (by omega) hj, show 14 + κ + 1 - 8 = κ + 7 by omega, eqv_add _ (by omega) ht,
    show κ + 7 - κ = 7 by omega, shiftPt_shiftPt, mul_assoc]

/-- A tail row `2^(14+κ) + 2^(8+κ) + j`. -/
theorem eqv_tail (j : ℕ) (hj : j < 256) :
    eqv r (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j) =
      eqv r 8 j * eqv (shiftPt r 8) κ 0 * eqv (shiftPt r (8 + κ)) 7 65 := by
  have h : wLen κ + 2 ^ (8 + κ) + j = j + 2 ^ 8 * (0 + 2 ^ κ * 65) := by
    rw [wLen_eq, pow_add]; ring_nf
  rw [h, eqv_add r (by omega) hj, show 14 + κ + 1 - 8 = κ + 7 by omega,
    eqv_add _ (by omega) (show 0 < 2 ^ κ by positivity), show κ + 7 - κ = 7 by omega,
    shiftPt_shiftPt, mul_assoc]

end Layout

/-! ## Extensions of indicator matrices -/

section Ind

variable {E : Type} [Field E]

theorem eq_ext {L : ℕ} (r : Fin L → E) (x : Fin (2 ^ L)) : eq r (cube x) = eqv (extPt r) L x.val := by
  rw [eqv_eq_eq]; congr 1; funext l; simp [extPt, l.isLt]

private theorem dsum_single {L : ℕ} (rx ry : Fin L → E) {a b : ℕ} (ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    ∑ x : Fin (2 ^ L), ∑ y : Fin (2 ^ L),
      eq rx (cube x) * eq ry (cube y) * (if x.val = a ∧ y.val = b then (1 : E) else 0) =
      eqv (extPt rx) L a * eqv (extPt ry) L b := by
  rw [sum_eq_single ⟨a, ha⟩ (fun x _ hx ↦ sum_eq_zero fun y _ ↦ by
      rw [ite_eq_right (fun h ↦ hx (Fin.ext h.1)), mul_zero]) (by simp)]
  rw [sum_eq_single ⟨b, hb⟩ (fun y _ hy ↦ by
      rw [ite_eq_right (fun h ↦ hy (Fin.ext h.2)), mul_zero]) (by simp)]
  simp [eq_ext]

/-- The extension of an indicator matrix (with a side condition `P`). -/
theorem matMle_termP {L : ℕ} (rx ry : Fin L → E) {ι : Type} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (f g : ι → ℕ) (hfg : ∀ p, P p → f p < 2 ^ L ∧ g p < 2 ^ L) :
    ∑ x : Fin (2 ^ L), ∑ y : Fin (2 ^ L), eq rx (cube x) * eq ry (cube y) *
      (∑ p, if P p ∧ x.val = f p ∧ y.val = g p then (1 : E) else 0) =
    ∑ p, if P p then eqv (extPt rx) L (f p) * eqv (extPt ry) L (g p) else 0 := by
  calc _ = ∑ x : Fin (2 ^ L), ∑ p : ι, ∑ y : Fin (2 ^ L), eq rx (cube x) * eq ry (cube y) *
          (if P p ∧ x.val = f p ∧ y.val = g p then (1 : E) else 0) := by
        simp only [mul_sum]; exact sum_congr rfl fun x _ ↦ Finset.sum_comm
    _ = ∑ p : ι, ∑ x : Fin (2 ^ L), ∑ y : Fin (2 ^ L), eq rx (cube x) * eq ry (cube y) *
          (if P p ∧ x.val = f p ∧ y.val = g p then (1 : E) else 0) := Finset.sum_comm
    _ = _ := ?_
  refine sum_congr rfl fun p _ ↦ ?_
  by_cases hp : P p
  · rw [ite_eq_left hp, ← dsum_single rx ry (hfg p hp).1 (hfg p hp).2]
    simp [hp]
  · rw [ite_eq_right hp]
    exact sum_eq_zero fun x _ ↦ sum_eq_zero fun y _ ↦ by simp [hp]

/-- The extension of an indicator matrix. -/
theorem matMle_term {L : ℕ} (rx ry : Fin L → E) {ι : Type} [Fintype ι] (f g : ι → ℕ)
    (hfg : ∀ p, f p < 2 ^ L ∧ g p < 2 ^ L) :
    ∑ x : Fin (2 ^ L), ∑ y : Fin (2 ^ L), eq rx (cube x) * eq ry (cube y) *
      (∑ p, if x.val = f p ∧ y.val = g p then (1 : E) else 0) =
    ∑ p, eqv (extPt rx) L (f p) * eqv (extPt ry) L (g p) := by
  have := matMle_termP rx ry (fun _ : ι ↦ True) f g (fun p _ ↦ hfg p)
  simpa using this

end Ind

/-! ## The closed forms (§2.4) -/

section Closed

variable {E : Type} [Field E]

/-- `Σ_{j < 256} eq(r_x[0..8), j) · eq(r_y[0..14), b + j)`. -/
def sig (R S : ℕ → E) (b : ℕ) : E := ∑ j : Fin 256, eqv R 8 j.val * eqv S 14 (b + j.val)

/-- The block part `Σ_k Σ_j M0(k, j) · eq(r_k, k) · eq(r_j, j)` of a block matrix `M0`. -/
def blockSum (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool) (R S : ℕ → E) : E :=
  ∑ k : Pos Blake2sCircuit.m, ∑ j : Pos Blake2sCircuit.m,
    if bk k j = true then eqv R 14 k.val * eqv S 14 j.val else 0

/-- `Ã(r_x, r_y)` (§2.4), given the block part `wA`. -/
def closedA (n κ : ℕ) (R S : ℕ → E) (wA : E) : E :=
  (1 - R (14 + κ)) * ((1 - S (14 + κ)) * eqp (shiftPt R 14) (shiftPt S 14) κ * wA +
      S (14 + κ) * eqv R 14 512 * eqv S (14 + κ) 0) +
  eqv (shiftPt R (8 + κ)) 7 64 *
    ((1 - S (14 + κ)) * shiftMle (shiftPt R 8) (shiftPt S 14) κ * sig R S 256 +
      S (14 + κ) * eqv (shiftPt R 8) κ 0 * eqv (shiftPt S 14) κ 0 * sig R S 1) +
  eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * (1 - S (14 + κ)) *
    eqv (shiftPt S 14) κ (n - 1) * sig R S 256

/-- `B̃(r_x, r_y)` (§2.4), given the block part `wB`. -/
def closedB (κ : ℕ) (R S : ℕ → E) (wB : E) : E :=
  (1 - R (14 + κ)) * ((1 - S (14 + κ)) * eqp (shiftPt R 14) (shiftPt S 14) κ * wB +
      S (14 + κ) * eqv R 14 512 * eqv S (14 + κ) 0) +
  eqv (shiftPt R (8 + κ)) 7 64 * S (14 + κ) * eqv S (14 + κ) 0 +
  eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * S (14 + κ) * eqv S (14 + κ) 0

/-- `C̃(r_x, r_y)` (§2.4). -/
def closedC (κ : ℕ) (R S : ℕ → E) : E :=
  (1 - R (14 + κ)) * (1 - S (14 + κ)) * eqp R S (14 + κ) +
  eqv (shiftPt R (8 + κ)) 7 64 * (1 - S (14 + κ)) * eqp (shiftPt R 8) (shiftPt S 14) κ *
    sig R S 648 +
  eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * S (14 + κ) * eqv (shiftPt S 14) κ 0 *
    sig R S 257

variable {κ : ℕ} (R S : ℕ → E)

private theorem pos14 (k : Pos Blake2sCircuit.m) : k.val < 16384 := k.isLt

/-- The region-0 part of a block matrix. -/
theorem sum_region0 (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool) :
    (∑ p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m,
      if bk p.2.1 p.2.2 = true then eqv R (14 + κ + 1) (p.2.1.val + 16384 * p.1.val) *
        eqv S (14 + κ + 1) (p.2.2.val + 16384 * p.1.val) else 0) =
      (1 - R (14 + κ)) * (1 - S (14 + κ)) * eqp (shiftPt R 14) (shiftPt S 14) κ *
        blockSum bk R S := by
  set c := (1 - R (14 + κ)) * (1 - S (14 + κ))
  set G : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → E := fun k j ↦
    if bk k j = true then eqv R 14 k.val * eqv S 14 j.val else 0
  set A : Fin (2 ^ κ) → E := fun t ↦ eqv (shiftPt R 14) κ t.val * eqv (shiftPt S 14) κ t.val
  calc _ = ∑ t : Fin (2 ^ κ), ∑ k : Pos Blake2sCircuit.m, ∑ j : Pos Blake2sCircuit.m,
          c * A t * G k j := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ ?_
        simp only [A, G, c]
        rw [eqv_w R _ _ (pos14 k) t.isLt, eqv_w S _ _ (pos14 j) t.isLt]
        split <;> ring
    _ = ∑ t : Fin (2 ^ κ), c * A t * blockSum bk R S := by
        refine sum_congr rfl fun t _ ↦ ?_
        rw [blockSum, mul_sum]
        exact sum_congr rfl fun k _ ↦ by rw [mul_sum]
    _ = c * eqp (shiftPt R 14) (shiftPt S 14) κ * blockSum bk R S := by
        rw [← sum_mul, ← mul_sum, sum_eqv_mul]

/-- The row-512 part: `(512 + 2^14 t, pub(0))`. -/
theorem sum_row512 :
    (∑ t : Fin (2 ^ κ), eqv R (14 + κ + 1) (512 + 16384 * t.val) * eqv S (14 + κ + 1) (wLen κ)) =
      (1 - R (14 + κ)) * (S (14 + κ) * eqv R 14 512 * eqv S (14 + κ) 0) := by
  have := sum_eqv (shiftPt R 14) κ
  have hp : eqv S (14 + κ + 1) (wLen κ) = eqv S (14 + κ) 0 * S (14 + κ) := by
    have := eqv_pub (κ := κ) S 0 (by positivity)
    rwa [add_zero] at this
  rw [hp]
  calc _ = ∑ t : Fin (2 ^ κ), eqv (shiftPt R 14) κ t.val *
          ((1 - R (14 + κ)) * (S (14 + κ) * eqv R 14 512 * eqv S (14 + κ) 0)) := by
        refine sum_congr rfl fun t _ ↦ ?_
        rw [eqv_w R _ _ (by norm_num : 512 < 16384) t.isLt]
        ring
    _ = _ := by rw [← sum_mul, this, one_mul]

/-- `Σ_{t ≥ 1} eq(a, t) eq(b, t − 1) = S̃(a, b)`. -/
theorem sum_shift (a b : ℕ → E) :
    (∑ t : Fin (2 ^ κ), if 1 ≤ t.val then eqv a κ t.val * eqv b κ (t.val - 1) else 0) =
      shiftMle a b κ := by
  rw [← shift_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  by_cases ht : 1 ≤ t.val
  · rw [ite_eq_left ht, sum_eq_single ⟨t.val - 1, by omega⟩ (fun t' _ h ↦ by
      rw [ite_eq_right (fun e ↦ h (Fin.ext (by simp; omega))), mul_zero]) (by simp)]
    simp only [show t.val - 1 + 1 = t.val by omega, ↓reduceIte, mul_one]
  · rw [ite_eq_right ht]
    exact (sum_eq_zero fun t' _ ↦ by rw [ite_eq_right (by omega), mul_zero]).symm

theorem sum_eqv8 (r : ℕ → E) : ∑ j : Fin 256, eqv r 8 j.val = 1 := sum_eqv r 8

/-- A sum over pairs of a product. -/
theorem sum_pair_mul {a b : ℕ} (f : Fin a → E) (g : Fin b → E) :
    (∑ p : Fin a × Fin b, f p.1 * g p.2) = (∑ t, f t) * ∑ j, g j := by
  rw [Fintype.sum_prod_type, sum_mul_sum]

theorem eqv_w0 (j : ℕ) (hj : j < 16384) :
    eqv S (14 + κ + 1) j = eqv S 14 j * eqv (shiftPt S 14) κ 0 * (1 - S (14 + κ)) := by
  have := eqv_w (κ := κ) S j 0 hj (by positivity)
  rwa [mul_zero, add_zero] at this

theorem eqv_pub0 (j : ℕ) (hj : j < 16384) :
    eqv S (14 + κ + 1) (wLen κ + j) = eqv S 14 j * eqv (shiftPt S 14) κ 0 * S (14 + κ) := by
  have hκ : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  rw [eqv_pub S j (by rw [pow_add]; norm_num; omega),
    show j = j + 16384 * 0 by ring, eqv_blk S j 0 hj, mul_zero, add_zero]

/-- The wiring rows of `A`, `t ≥ 1`. -/
theorem sum_wireA :
    (∑ p : Fin (2 ^ κ) × Fin 256, if 1 ≤ p.1.val then
      eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val) *
        eqv S (14 + κ + 1) (256 + p.2.val + 16384 * (p.1.val - 1)) else 0) =
      eqv (shiftPt R (8 + κ)) 7 64 * (1 - S (14 + κ)) *
        shiftMle (shiftPt R 8) (shiftPt S 14) κ * sig R S 256 := by
  calc _ = ∑ p : Fin (2 ^ κ) × Fin 256, (eqv (shiftPt R (8 + κ)) 7 64 * (1 - S (14 + κ)) *
          (if 1 ≤ p.1.val then eqv (shiftPt R 8) κ p.1.val * eqv (shiftPt S 14) κ (p.1.val - 1)
            else 0)) * (eqv R 8 p.2.val * eqv S 14 (256 + p.2.val)) := by
        refine sum_congr rfl fun p _ ↦ ?_
        split
        · rw [eqv_wire R _ _ p.2.isLt p.1.isLt, eqv_w S _ _ (by omega) (by omega)]
          ring
        · ring
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, ← sum_mul]
        rw [sum_shift, sig]

/-- The wiring rows of `A`, `t = 0`. -/
theorem sum_wire0A :
    (∑ j : Fin 256, eqv R (14 + κ + 1) (wLen κ + j.val) *
        eqv S (14 + κ + 1) (wLen κ + 1 + j.val)) =
      eqv (shiftPt R (8 + κ)) 7 64 * (S (14 + κ) * eqv (shiftPt R 8) κ 0 *
        eqv (shiftPt S 14) κ 0 * sig R S 1) := by
  rw [sig, mul_sum, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  have h1 := eqv_wire (κ := κ) R j.val 0 j.isLt (by positivity)
  rw [mul_zero, add_zero] at h1
  rw [h1, show wLen κ + 1 + j.val = wLen κ + (1 + j.val) by ring, eqv_pub0 S _ (by omega)]
  ring

/-- The tail rows of `A`. -/
theorem sum_tailA (n : ℕ) (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) :
    (∑ j : Fin 256, eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j.val) *
        eqv S (14 + κ + 1) (256 + j.val + 16384 * (n - 1))) =
      eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * (1 - S (14 + κ)) *
        eqv (shiftPt S 14) κ (n - 1) * sig R S 256 := by
  rw [sig, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eqv_tail R _ j.isLt, eqv_w S _ _ (by omega) (by omega)]
  ring

/-- The wiring rows of `B`. -/
theorem sum_wireB :
    (∑ p : Fin (2 ^ κ) × Fin 256, eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val) *
        eqv S (14 + κ + 1) (wLen κ)) =
      eqv (shiftPt R (8 + κ)) 7 64 * S (14 + κ) * eqv S (14 + κ) 0 := by
  have hp : eqv S (14 + κ + 1) (wLen κ) = eqv S (14 + κ) 0 * S (14 + κ) := by
    have := eqv_pub (κ := κ) S 0 (by positivity)
    rwa [add_zero] at this
  calc _ = ∑ p : Fin (2 ^ κ) × Fin 256, (eqv (shiftPt R (8 + κ)) 7 64 * S (14 + κ) *
          eqv S (14 + κ) 0 * eqv (shiftPt R 8) κ p.1.val) * eqv R 8 p.2.val := by
        refine sum_congr rfl fun p _ ↦ ?_
        rw [eqv_wire R _ _ p.2.isLt p.1.isLt, hp]
        ring
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, ← sum_mul]
        rw [sum_eqv8, mul_one, sum_eqv, mul_one]

/-- The tail rows of `B`. -/
theorem sum_tailB :
    (∑ j : Fin 256, eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j.val) *
        eqv S (14 + κ + 1) (wLen κ)) =
      eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * S (14 + κ) * eqv S (14 + κ) 0 := by
  have hp : eqv S (14 + κ + 1) (wLen κ) = eqv S (14 + κ) 0 * S (14 + κ) := by
    have := eqv_pub (κ := κ) S 0 (by positivity)
    rwa [add_zero] at this
  calc _ = ∑ j : Fin 256, (eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * S (14 + κ) *
          eqv S (14 + κ) 0) * eqv R 8 j.val := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [eqv_tail R _ j.isLt, hp]
        ring
    _ = _ := by rw [← mul_sum, sum_eqv8, mul_one]

/-- The region-0 part of `C`. -/
theorem sum_region0C :
    (∑ u : Fin (wLen κ), eqv R (14 + κ + 1) u.val * eqv S (14 + κ + 1) u.val) =
      (1 - R (14 + κ)) * (1 - S (14 + κ)) * eqp R S (14 + κ) := by
  have h : ∀ (r : ℕ → E) (u : Fin (wLen κ)),
      eqv r (14 + κ + 1) u.val = eqv r (14 + κ) u.val * (1 - r (14 + κ)) := fun r u ↦ by
    have := eqv_add r (show 14 + κ ≤ 14 + κ + 1 by omega) u.isLt 0
    rw [mul_zero, add_zero, Nat.add_sub_cancel_left, eqv_one_zero] at this
    rw [this]; rfl
  calc _ = ∑ u : Fin (wLen κ), (1 - R (14 + κ)) * (1 - S (14 + κ)) *
          (eqv R (14 + κ) u.val * eqv S (14 + κ) u.val) := by
        refine sum_congr rfl fun u _ ↦ ?_
        rw [h R u, h S u]; ring
    _ = _ := by rw [← mul_sum, sum_eqv_mul]

/-- The wiring rows of `C`. -/
theorem sum_wireC :
    (∑ p : Fin (2 ^ κ) × Fin 256, eqv R (14 + κ + 1) (wLen κ + 256 * p.1.val + p.2.val) *
        eqv S (14 + κ + 1) (648 + p.2.val + 16384 * p.1.val)) =
      eqv (shiftPt R (8 + κ)) 7 64 * (1 - S (14 + κ)) * eqp (shiftPt R 8) (shiftPt S 14) κ *
        sig R S 648 := by
  calc _ = ∑ p : Fin (2 ^ κ) × Fin 256, (eqv (shiftPt R (8 + κ)) 7 64 * (1 - S (14 + κ)) *
          (eqv (shiftPt R 8) κ p.1.val * eqv (shiftPt S 14) κ p.1.val)) *
          (eqv R 8 p.2.val * eqv S 14 (648 + p.2.val)) := by
        refine sum_congr rfl fun p _ ↦ ?_
        rw [eqv_wire R _ _ p.2.isLt p.1.isLt, eqv_w S _ _ (by omega) p.1.isLt]
        ring
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, ← sum_mul]
        rw [sum_eqv_mul, sig]

/-- The tail rows of `C`. -/
theorem sum_tailC :
    (∑ j : Fin 256, eqv R (14 + κ + 1) (wLen κ + 2 ^ (8 + κ) + j.val) *
        eqv S (14 + κ + 1) (wLen κ + 257 + j.val)) =
      eqv (shiftPt R 8) κ 0 * eqv (shiftPt R (8 + κ)) 7 65 * S (14 + κ) *
        eqv (shiftPt S 14) κ 0 * sig R S 257 := by
  rw [sig, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eqv_tail R _ j.isLt, show wLen κ + 257 + j.val = wLen κ + (257 + j.val) by ring,
    eqv_pub0 S _ (by omega)]
  ring

end Closed

/-! ## `matrix_mle_eq` -/

section MatrixMle

variable {E : Type} [Field E] {κ : ℕ}

private theorem bnd (κ : ℕ) : 2 ^ (14 + κ + 1) = 32768 * 2 ^ κ := ixLen_eq κ

/-- **L-C4 (`matrix_mle_eq`), `A`.** The extension of the chain matrix `A` is the closed form of
§2.4 with the block part `Σ_{k ≠ 512} e(k) Σ_j A0(k, j) wt(j)`. -/
theorem matMle_chainA {n : ℕ} (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) (rx ry : Fin (14 + κ + 1) → E) :
    matMle (chainA n κ) rx ry =
      closedA n κ (extPt rx) (extPt ry) (blockSum blockA (extPt rx) (extPt ry)) := by
  have hL := bnd κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [matMle, chainA, mul_add, sum_add_distrib]
  rw [matMle_termP rx ry (fun p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m ↦
        blockA p.2.1 p.2.2 = true) (fun p ↦ p.2.1.val + 16384 * p.1.val)
        (fun p ↦ p.2.2.val + 16384 * p.1.val)
        (fun p _ ↦ ⟨by have := p.1.isLt; have : p.2.1.val < 16384 := p.2.1.isLt; omega,
          by have := p.1.isLt; have : p.2.2.val < 16384 := p.2.2.isLt; omega⟩),
    matMle_term rx ry (fun t : Fin (2 ^ κ) ↦ 512 + 16384 * t.val) (fun _ ↦ wLen κ)
      (fun t ↦ ⟨by have := t.isLt; omega, by omega⟩),
    matMle_termP rx ry (fun p : Fin (2 ^ κ) × Fin 256 ↦ 1 ≤ p.1.val)
      (fun p ↦ wLen κ + 256 * p.1.val + p.2.val) (fun p ↦ 256 + p.2.val + 16384 * (p.1.val - 1))
      (fun p _ ↦ ⟨by have := p.1.isLt; have := p.2.isLt; omega,
        by have := p.1.isLt; have := p.2.isLt; omega⟩),
    matMle_term rx ry (fun j : Fin 256 ↦ wLen κ + j.val) (fun j ↦ wLen κ + 1 + j.val)
      (fun j ↦ ⟨by have := j.isLt; omega, by have := j.isLt; omega⟩),
    matMle_term rx ry (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val)
      (fun j ↦ 256 + j.val + 16384 * (n - 1))
      (fun j ↦ ⟨by have := j.isLt; omega, by have := j.isLt; omega⟩),
    sum_region0, sum_row512, sum_wireA, sum_wire0A, sum_tailA _ _ n hn hnκ, closedA]
  ring

/-- **L-C4 (`matrix_mle_eq`), `B`.** -/
theorem matMle_chainB (rx ry : Fin (14 + κ + 1) → E) :
    matMle (chainB κ) rx ry =
      closedB κ (extPt rx) (extPt ry) (blockSum blockB (extPt rx) (extPt ry)) := by
  have hL := bnd κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [matMle, chainB, mul_add, sum_add_distrib]
  rw [matMle_termP rx ry (fun p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m ↦
        blockB p.2.1 p.2.2 = true) (fun p ↦ p.2.1.val + 16384 * p.1.val)
        (fun p ↦ p.2.2.val + 16384 * p.1.val)
        (fun p _ ↦ ⟨by have := p.1.isLt; have : p.2.1.val < 16384 := p.2.1.isLt; omega,
          by have := p.1.isLt; have : p.2.2.val < 16384 := p.2.2.isLt; omega⟩),
    matMle_term rx ry (fun t : Fin (2 ^ κ) ↦ 512 + 16384 * t.val) (fun _ ↦ wLen κ)
      (fun t ↦ ⟨by have := t.isLt; omega, by omega⟩),
    matMle_term rx ry (fun p : Fin (2 ^ κ) × Fin 256 ↦ wLen κ + 256 * p.1.val + p.2.val)
      (fun _ ↦ wLen κ) (fun p ↦ ⟨by have := p.1.isLt; have := p.2.isLt; omega, by omega⟩),
    matMle_term rx ry (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val) (fun _ ↦ wLen κ)
      (fun j ↦ ⟨by have := j.isLt; omega, by omega⟩),
    sum_region0, sum_row512, sum_wireB, sum_tailB, closedB]
  ring

/-- **L-C4 (`matrix_mle_eq`), `C`.** -/
theorem matMle_chainC (rx ry : Fin (14 + κ + 1) → E) :
    matMle (chainC κ) rx ry = closedC κ (extPt rx) (extPt ry) := by
  have hL := bnd κ
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hκ1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  simp only [matMle, chainC, mul_add, sum_add_distrib]
  rw [matMle_term rx ry (fun u : Fin (wLen κ) ↦ u.val) (fun u ↦ u.val)
      (fun u ↦ ⟨by have := u.isLt; omega, by have := u.isLt; omega⟩),
    matMle_term rx ry (fun p : Fin (2 ^ κ) × Fin 256 ↦ wLen κ + 256 * p.1.val + p.2.val)
      (fun p ↦ 648 + p.2.val + 16384 * p.1.val)
      (fun p ↦ ⟨by have := p.1.isLt; have := p.2.isLt; omega,
        by have := p.1.isLt; have := p.2.isLt; omega⟩),
    matMle_term rx ry (fun j : Fin 256 ↦ wLen κ + 2 ^ (8 + κ) + j.val)
      (fun j ↦ wLen κ + 257 + j.val) (fun j ↦ ⟨by have := j.isLt; omega, by have := j.isLt; omega⟩),
    sum_region0C, sum_wireC, sum_tailC, closedC]

end MatrixMle

/-! ## The block part is the walk -/

section BlockWalk

variable {E : Type} [Field E] [CharP E 2]

private theorem blockSum_eq (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool)
    (row : Pos Blake2sCircuit.m → Form Blake2sCircuit.m)
    (hbk : ∀ k j, bk k j = (decide (k ≠ constPos) && (row k).getLsbD j)) (R S : ℕ → E) :
    blockSum bk R S = ∑ k : Pos Blake2sCircuit.m, if k = constPos then 0 else
      eqv R 14 k.val * ∑ j : Pos Blake2sCircuit.m,
        if (row k).getLsbD j = true then eqv S 14 j.val else 0 := by
  rw [blockSum]
  refine sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k = constPos
  · simp [hbk, hk]
  · rw [ite_eq_right hk, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [hbk, hk, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
    split <;> simp

/-- **The walk computes the block part of `Ã`, `B̃`** (with `walk_eq_sum`, row 512 skipped). -/
theorem walkAB_blockSum (R S : ℕ → E) :
    walkAB (fun k ↦ eqv R 14 k.val) (fun j ↦ eqv S 14 j.val) =
      (blockSum blockA R S, blockSum blockB R S) := by
  rw [walk_eq_sum]
  refine Prod.ext ?_ ?_
  · rw [blockSum_eq blockA (fun k ↦ (chainBlock.rowOf k).a) (fun _ _ ↦ rfl)]
    rfl
  · rw [blockSum_eq blockB (fun k ↦ (chainBlock.rowOf k).b) (fun _ _ ↦ rfl)]
    rfl

end BlockWalk

end SpartanChain
