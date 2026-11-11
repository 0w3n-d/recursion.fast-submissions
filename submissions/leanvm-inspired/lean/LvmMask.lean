-- New for lvm2 (S1-L): the gated link's mask kernels and their closed forms (BLUEPRINT2 §2.1, §5, §6 group S1).
-- Pattern: `LvmShift` (kernels on the cube, `O(|ρ|)` evaluators, extensions by the low-bit recursion of
-- FRShift's `shiftRec`). The evaluators are P-GATE's `lt_mle` and `gated_kernel` (`prover/src/lvm/link.rs`,
-- branch lvm2/PGATE), restated as low-bit-first automata.
import LvmShift

/-!
# The mask kernels of the gated `CH` link

With `n` the chain length (`1 ≤ n ≤ 2^h`) and `m = n − 1`, the gated link (S1) constrains the rows
`k ≤ m` only. Its kernels on the cube (`|ρ| = h`, characteristic two, the first coordinate on the
lowest bit):

* `ltK ρ t k = [k < t]·eq(ρ, k)`: `lt̃_t(ρ) = Σ_k ltK ρ t k`, and the gated equality kernel
  `E'_n(ρ, k) = ltK ρ m k`;
* `gShiftK ρ m k = [1 ≤ k ≤ m]·eq(ρ, k − 1)`: the gated shift kernel `S_n(ρ, k)`.

The verifier evaluates their extensions in `O(h)`, low bit first:

* `ltEvalE x t`, the 2-state threshold automaton `ltPair` (state `(lt̃_t, lt̃_{t+1})`):
  **`sum_ltK`**: `Σ_k ltK x t k = ltEvalE x t` (any `t`; `1` once `t ≥ 2^|x|`, `ltEvalE_of_le`);
* `gMaskEvalE ρ y m` and `gShiftEvalE ρ y m`, the 4-state automaton `gState` (the carry of `k + 1`
  times the threshold offset `{t, t + 1}`): **`sum_ltK_eqAt`**: `Σ_k eq(y, k)·ltK ρ m k =
  gMaskEvalE ρ y m`, and **`sum_gShiftK`**: `Σ_k eq(y, k)·gShiftK ρ m k = gShiftEvalE ρ y m`;
* at `m = 2^h − 1` (`n = 2^h`) they are v1's kernels and closed forms: `ltK_full`, `gShiftK_full`,
  `ltEvalE_full` (`1 + Π ρ`), `gMaskEvalE_full` (`eqMaskedE`), `gShiftEvalE_full` (`shiftEvalE`).

The four values the gated link's verifier needs are `gShiftEvalE ρ ρ' m` (`S̃_n(ρ, ρ')`),
`gMaskEvalE ρ ρ' m` (`Ẽ'_n(ρ, ρ')`), `ltEvalE ρ m` (`lt̃_m(ρ)`) and `ltEvalE ρ' n` (`lt̃_n(ρ')`).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

/-! ## Kernels -/

/-- The threshold kernel `[k < t]·eq(ρ, k)`; at `t = m` it is the gated equality kernel `E'_n`. -/
def ltK (ρ : List E) (t k : ℕ) : E := if k < t then eqAt ρ k else 0

/-- The gated shift kernel `S_n(ρ, k) = [1 ≤ k ≤ m]·eq(ρ, k − 1)` (`m = n − 1`). -/
def gShiftK (ρ : List E) (m k : ℕ) : E := if 1 ≤ k ∧ k ≤ m then eqAt ρ (k - 1) else 0

/-! ## Evaluators -/

/-- `(lt̃_t(x), lt̃_{t+1}(x))`, low bit first: the 2-state threshold automaton. -/
def ltPair : List E → ℕ → E × E
  | [], t => (if 0 < t then 1 else 0, 1)
  | a :: xs, t =>
    let p := ltPair xs (t / 2)
    if t % 2 = 0 then (p.1, (1 + a) * p.2 + a * p.1) else ((1 + a) * p.2 + a * p.1, p.2)

/-- `lt̃_t(x) = Σ_{k < t} eq(x, k)` in `O(|x|)`. -/
def ltEvalE (x : List E) (t : ℕ) : E := (ltPair x t).1

/-- The 4-state automaton of the gated kernels, low bit first:
`(Q₀(t), Q₀(t + 1), Q₁(t), Q₁(t + 1))` with `Q_c(t) = Σ_{j < t, j + c < 2^|x|} eq(x, j)·eq(y, j + c)`
(`c` the carry of `+ 1`). Per bit: `e₀ = (1 + a)(1 + b)`, `e₁ = ab` (no carry), `c₀ = (1 + a) b`
(carry absorbed), `c₁ = a(1 + b)` (carry propagated). -/
def gState : List E → List E → ℕ → E × E × E × E
  | [], _, t => (if 0 < t then 1 else 0, 1, 0, 0)
  | _ :: _, [], t => (if 0 < t then 1 else 0, 1, 0, 0)
  | a :: xs, b :: ys, t =>
    let s := gState xs ys (t / 2)
    let e0 := (1 + a) * (1 + b)
    let e1 := a * b
    let c0 := (1 + a) * b
    let c1 := a * (1 + b)
    if t % 2 = 0 then
      ((e0 + e1) * s.1, e0 * s.2.1 + e1 * s.1, c0 * s.1 + c1 * s.2.2.1, c0 * s.2.1 + c1 * s.2.2.1)
    else
      (e0 * s.2.1 + e1 * s.1, (e0 + e1) * s.2.1, c0 * s.2.1 + c1 * s.2.2.1,
        c0 * s.2.1 + c1 * s.2.2.2)

/-- `Ẽ'_n(ρ, y) = Σ_{k < m} eq(ρ, k)·eq(y, k)` in `O(|ρ|)`. -/
def gMaskEvalE (ρ y : List E) (m : ℕ) : E := (gState ρ y m).1

/-- `S̃_n(ρ, y) = Σ_{k < m} eq(ρ, k)·eq(y, k + 1)` in `O(|ρ|)`. -/
def gShiftEvalE (ρ y : List E) (m : ℕ) : E := (gState ρ y m).2.2.1

/-! ## The automata's sums (proof helpers) -/

/-- `lt̃_t(x)` as a sum. -/
def ltS (x : List E) (t : ℕ) : E := ∑ k ∈ range (2 ^ x.length), ltK x t k

/-- `Q₀(t) = Σ_{j < t} eq(x, j)·eq(y, j)` as a sum. -/
def q0S (x y : List E) (t : ℕ) : E :=
  ∑ j ∈ range (2 ^ x.length), if j < t then eqAt x j * eqAt y j else 0

/-- `Q₁(t) = Σ_{j < t, j + 1 < 2^|x|} eq(x, j)·eq(y, j + 1)` as a sum. -/
def q1S (x y : List E) (t : ℕ) : E :=
  ∑ j ∈ range (2 ^ x.length), if j < t ∧ j + 1 < 2 ^ x.length then eqAt x j * eqAt y (j + 1) else 0

theorem ite_lt_mul {c c' : Prop} [Decidable c] [Decidable c'] (hc : c ↔ c') (u v : E) :
    (if c then u * v else 0) = u * (if c' then v else 0) := by
  by_cases h : c'
  · rw [if_pos (hc.2 h), if_pos h]
  · rw [if_neg (fun h' ↦ h (hc.1 h')), if_neg h, mul_zero]

/-- The threshold sum peels its low bit. -/
theorem ltS_cons (a : E) (xs : List E) (T : ℕ) :
    ltS (a :: xs) T = (1 + a) * ltS xs ((T + 1) / 2) + a * ltS xs (T / 2) := by
  unfold ltS
  rw [List.length_cons, sum_cube_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [ltK, eqAt_even, eqAt_odd]
  rw [ite_lt_mul (show 2 * w < T ↔ w < (T + 1) / 2 by omega),
    ite_lt_mul (show 2 * w + 1 < T ↔ w < T / 2 by omega)]

/-- `Q₀` peels its low bit. -/
theorem q0S_cons (a b : E) (xs ys : List E) (T : ℕ) :
    q0S (a :: xs) (b :: ys) T =
      (1 + a) * (1 + b) * q0S xs ys ((T + 1) / 2) + a * b * q0S xs ys (T / 2) := by
  unfold q0S
  rw [List.length_cons, sum_cube_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [eqAt_even, eqAt_odd]
  rw [show (1 + a) * eqAt xs w * ((1 + b) * eqAt ys w) = (1 + a) * (1 + b) * (eqAt xs w * eqAt ys w)
      by ring, show a * eqAt xs w * (b * eqAt ys w) = a * b * (eqAt xs w * eqAt ys w) by ring,
    ite_lt_mul (show 2 * w < T ↔ w < (T + 1) / 2 by omega),
    ite_lt_mul (show 2 * w + 1 < T ↔ w < T / 2 by omega)]

/-- `Q₁` peels its low bit: the carry is absorbed by a `0` bit, propagated by a `1` bit. -/
theorem q1S_cons (a b : E) (xs ys : List E) (T : ℕ) :
    q1S (a :: xs) (b :: ys) T =
      (1 + a) * b * q0S xs ys ((T + 1) / 2) + a * (1 + b) * q1S xs ys (T / 2) := by
  unfold q1S q0S
  have hp : 2 ^ (xs.length + 1) = 2 * 2 ^ xs.length := by ring
  rw [List.length_cons, sum_cube_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  have hw' := Finset.mem_range.1 hw
  rw [show 2 * w + 1 + 1 = 2 * (w + 1) by ring]
  simp only [eqAt_even, eqAt_odd]
  rw [show (1 + a) * eqAt xs w * (b * eqAt ys w) = (1 + a) * b * (eqAt xs w * eqAt ys w) by ring,
    show a * eqAt xs w * ((1 + b) * eqAt ys (w + 1)) =
      a * (1 + b) * (eqAt xs w * eqAt ys (w + 1)) by ring,
    ite_lt_mul (show 2 * w < T ∧ 2 * w + 1 < 2 ^ (xs.length + 1) ↔ w < (T + 1) / 2 by omega),
    ite_lt_mul (show 2 * w + 1 < T ∧ 2 * (w + 1) < 2 ^ (xs.length + 1) ↔
      w < T / 2 ∧ w + 1 < 2 ^ xs.length by omega)]

theorem char2_absorb (a X : E) : (1 + a) * X + a * X = X := by
  linear_combination (a * X) * CharTwo.two_eq_zero (R := E)

/-- **The 2-state automaton computes the threshold sums.** -/
theorem ltPair_eq : ∀ (x : List E) (t : ℕ), ltPair x t = (ltS x t, ltS x (t + 1))
  | [], t => by
    simp only [ltPair, ltS, List.length_nil, pow_zero, Finset.sum_range_one, ltK, eqAt_nil]
    rw [if_pos (Nat.succ_pos t)]
  | a :: xs, t => by
    simp only [ltPair, ltPair_eq xs]
    obtain ⟨u, rfl | rfl⟩ : ∃ u, t = 2 * u ∨ t = 2 * u + 1 := ⟨t / 2, by omega⟩
    · rw [if_pos (by omega), ltS_cons, ltS_cons, show (2 * u + 1) / 2 = u by omega,
        show 2 * u / 2 = u by omega, show (2 * u + 1 + 1) / 2 = u + 1 by omega, char2_absorb]
    · rw [if_neg (by omega), ltS_cons, ltS_cons, show (2 * u + 1 + 1) / 2 = u + 1 by omega,
        show (2 * u + 1) / 2 = u by omega, show (2 * u + 1 + 1 + 1) / 2 = u + 1 by omega,
        char2_absorb]

/-- **The 4-state automaton computes `Q₀`, `Q₁`.** -/
theorem gState_eq : ∀ (x y : List E), x.length = y.length → ∀ t : ℕ,
    gState x y t = (q0S x y t, q0S x y (t + 1), q1S x y t, q1S x y (t + 1))
  | [], [], _, t => by
    simp only [gState, q0S, q1S, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil,
      mul_one]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: xs, b :: ys, h, t => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [gState, gState_eq xs ys h]
    obtain ⟨u, rfl | rfl⟩ : ∃ u, t = 2 * u ∨ t = 2 * u + 1 := ⟨t / 2, by omega⟩
    · rw [if_pos (by omega), q0S_cons, q0S_cons, q1S_cons, q1S_cons,
        show (2 * u + 1) / 2 = u by omega, show 2 * u / 2 = u by omega,
        show (2 * u + 1 + 1) / 2 = u + 1 by omega]
      refine Prod.ext (by ring) (Prod.ext rfl (Prod.ext rfl rfl))
    · rw [if_neg (by omega), q0S_cons, q0S_cons, q1S_cons, q1S_cons,
        show (2 * u + 1 + 1) / 2 = u + 1 by omega, show (2 * u + 1) / 2 = u by omega,
        show (2 * u + 1 + 1 + 1) / 2 = u + 1 by omega]
      refine Prod.ext rfl (Prod.ext (by ring) (Prod.ext rfl rfl))

/-! ## The extensions -/

/-- **`lt̃_t` is the threshold automaton.** -/
theorem sum_ltK (x : List E) (t : ℕ) :
    ∑ k ∈ range (2 ^ x.length), ltK x t k = ltEvalE x t := by
  rw [ltEvalE, ltPair_eq]
  rfl

/-- `lt̃_{t+1}` is the automaton's second state at `t`: all four values of the gated link's verifier
(`lt̃_n(ρ') = lt̃_{m+1}(ρ')`) come from `ltPair` and `gState` at `m`. -/
theorem ltEvalE_succ (x : List E) (t : ℕ) : ltEvalE x (t + 1) = (ltPair x t).2 := by
  rw [ltEvalE, ltPair_eq, ltPair_eq]

/-- A threshold column's extension: `Σ_k eq(pt, k)·[k < t]·c = c·lt̃_t(pt)`. -/
theorem sum_eqAt_lt (pt : List E) (t : ℕ) (c : E) :
    ∑ k ∈ range (2 ^ pt.length), eqAt pt k * (if k < t then c else 0) = c * ltEvalE pt t := by
  rw [← sum_ltK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold ltK
  split_ifs <;> ring

/-- `lt̃_t = 1` once the threshold covers the cube. -/
theorem ltEvalE_of_le (x : List E) {t : ℕ} (ht : 2 ^ x.length ≤ t) : ltEvalE x t = 1 := by
  rw [← sum_ltK, ← sum_eqAt x]
  exact Finset.sum_congr rfl fun k hk ↦ if_pos (by have := Finset.mem_range.1 hk; omega)

/-- **The gated equality kernel's extension** is the automaton's `Q₀`. -/
theorem sum_ltK_eqAt (ρ y : List E) (h : ρ.length = y.length) (m : ℕ) :
    ∑ k ∈ range (2 ^ ρ.length), eqAt y k * ltK ρ m k = gMaskEvalE ρ y m := by
  rw [gMaskEvalE, gState_eq ρ y h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold ltK
  split_ifs <;> ring

/-- **The gated shift kernel's extension** is the automaton's `Q₁`. -/
theorem sum_gShiftK (ρ y : List E) (h : ρ.length = y.length) (m : ℕ) :
    ∑ k ∈ range (2 ^ ρ.length), eqAt y k * gShiftK ρ m k = gShiftEvalE ρ y m := by
  rw [gShiftEvalE, gState_eq ρ y h]
  show _ = q1S ρ y m
  unfold q1S
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ ρ.length = M + 1 := ⟨2 ^ ρ.length - 1, by have := Nat.two_pow_pos ρ.length; omega⟩
  rw [hM, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [gShiftK, show ¬ (1 ≤ 0 ∧ 0 ≤ m) by omega, if_false, mul_zero, add_zero,
    show ¬ (M < m ∧ M + 1 < M + 1) by omega]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [Nat.add_sub_cancel, mul_comm, ite_lt_mul (show j < m ∧ j + 1 < M + 1 ↔ 1 ≤ j + 1 ∧ j + 1 ≤ m by omega)]
  split_ifs <;> ring

/-! ## `n = 2^h`: v1's kernels -/

/-- At `m = 2^h − 1` the gated equality kernel is v1's `maskK`. -/
theorem ltK_full (ρ : List E) : ltK ρ (2 ^ ρ.length - 1) = maskK ρ := by
  funext k
  have := Nat.two_pow_pos ρ.length
  unfold ltK maskK
  by_cases hk : k + 1 < 2 ^ ρ.length
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

/-- At `m = 2^h − 1` the gated shift kernel is v1's `shiftK` on the cube. -/
theorem gShiftK_full (ρ : List E) {k : ℕ} (hk : k < 2 ^ ρ.length) :
    gShiftK ρ (2 ^ ρ.length - 1) k = shiftK ρ k := by
  unfold gShiftK shiftK
  by_cases h1 : 1 ≤ k
  · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
  · rw [if_neg (by omega), if_neg h1]

/-- `lt̃_{2^h − 1}(ρ) = 1 + Π ρ` (v1's target factor). -/
theorem ltEvalE_full (ρ : List E) : ltEvalE ρ (2 ^ ρ.length - 1) = 1 + prodE ρ := by
  rw [← sum_ltK, ltK_full, sum_maskK_one]

/-- `Ẽ'_{2^h}` is v1's `eqMaskedE`. -/
theorem gMaskEvalE_full (ρ y : List E) (h : ρ.length = y.length) :
    gMaskEvalE ρ y (2 ^ ρ.length - 1) = eqMaskedE ρ y := by
  rw [← sum_ltK_eqAt ρ y h, ltK_full, sum_maskK ρ y h]

/-- `S̃_{2^h}` is v1's `shiftEvalE`. -/
theorem gShiftEvalE_full (ρ y : List E) (h : ρ.length = y.length) :
    gShiftEvalE ρ y (2 ^ ρ.length - 1) = shiftEvalE ρ y := by
  rw [← sum_gShiftK ρ y h, ← sum_shiftK ρ y h]
  exact Finset.sum_congr rfl fun k hk ↦ by rw [gShiftK_full ρ (Finset.mem_range.1 hk)]

end Lvm.KG
