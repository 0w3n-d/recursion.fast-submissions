import SpartanChainProximity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Controls for `SpartanChainRS` and `SpartanChainProximity` (blueprint §10.1)

* `Enc` at `k = 4` against naive polynomial evaluation (`enc_four`, and `enc_toy`/`encAt_toy` on
  `ZMod 7`); a nonzero message has a nonzero codeword (`enc_toy_ne_zero`); the basis is not the
  monomial basis (`enc_toy_not_monomial`).
* `eClose` on a toy `2 × 8` matrix over `ZMod 11` (code of length 8, `k = 2`, `d = 7`,
  `e = 2`): `close_toy` is `e`-close; `far_toy` is not, although each of its rows is
  (`far_toy_rows_close`); `far_bad_le` applies to it (`far_toy_bound`).
* The bound is tight: over `ZMod 3` with the length-2 repetition code and `e = 0`, exactly
  `(e+1)·|E|^{m−1} = 1` coefficient makes a far row close (`tight_toy`).
-/

namespace SpartanChain.RS.Controls

open Finset

/-! ### `Enc` at `k = 4` -/

/-- `Enc` at `k = 4`: `X_0 = 1`, `X_1 = X`, `X_2 = X(X + κ_0)`, `X_3 = X·X(X + κ_0)`. -/
theorem enc_four {K ι : Type*} [Field K] (κ : ℕ → K) (ω : ι → K) (msg : Fin (2 ^ 2) → K)
    (c : ι) :
    enc κ 2 ω msg c = msg 0 + msg 1 * ω c + msg 2 * (ω c * (ω c + κ 0)) +
      msg 3 * (ω c * (ω c * (ω c + κ 0))) := by
  have h1 : Nat.testBit 1 1 = false := by decide
  have h2 : Nat.testBit 2 1 = true := by decide
  have h3 : Nat.testBit 3 1 = true := by decide
  simp [enc, Fin.sum_univ_four, basisVal, bitProd, wVal, prod_range_succ, h1, h2, h3]
  ring

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Points `0, …, 6` of `ZMod 7`. -/
def ω7 (c : Fin 7) : ZMod 7 := (c.val : ZMod 7)

/-- The constants of §5.1 with `pt i = 2^i`. -/
def κ7 (i : ℕ) : ZMod 7 := (kappaArr (fun i => ((2 ^ i : ℕ) : ZMod 7)) 2).getD i 0

/-- `κ_0 = W_0(1) = 1`, `κ_1 = W_1(2) = 2·(2 + 1) = 6`. -/
theorem kappa_toy : kappaArr (fun i => ((2 ^ i : ℕ) : ZMod 7)) 2 = #[1, 6] := by decide

/-- Positive: `Enc(1,2,3,4) = 1 + 2X + 3(X² + X) + 4(X³ + X²) = 1 + 5X + 4X³` over `ZMod 7`. -/
theorem enc_toy : ∀ c, enc κ7 2 ω7 ![1, 2, 3, 4] c = 1 + 5 * ω7 c + 4 * ω7 c ^ 3 := by decide

/-- The verifier's `encAt` agrees on the same instance. -/
theorem encAt_toy :
    ∀ c, encAt κ7 2 #[(1 : ZMod 7), 2, 3, 4] (ω7 c) = 1 + 5 * ω7 c + 4 * ω7 c ^ 3 := by
  decide +kernel

/-- Negative: a nonzero message has a nonzero codeword. -/
theorem enc_toy_ne_zero : enc κ7 2 ω7 (![0, 0, 0, 1] : Fin (2 ^ 2) → ZMod 7) ≠ 0 := by decide

/-- Negative: `X_2 = X² + X` here, not the monomial `X²`. -/
theorem enc_toy_not_monomial : enc κ7 2 ω7 (![0, 0, 1, 0] : Fin (2 ^ 2) → ZMod 7) ≠ fun c => ω7 c ^ 2 := by decide

/-! ### `eClose` on a `2 × 8` matrix -/

/-- Points `0, …, 7` of `ZMod 11`. -/
def ω11 (c : Fin 8) : ZMod 11 := (c.val : ZMod 11)

/-- The code: degree `< 2` over `ZMod 11` at 8 points. -/
abbrev C11 : Submodule (ZMod 11) (Fin 8 → ZMod 11) := rsCode (fun _ => (0 : ZMod 11)) 1 ω11

theorem ω11_injective : Function.Injective ω11 := by decide

/-- Minimum distance `8 − 2 + 1 = 7`. -/
theorem C11_dist : MinDist C11 7 := by
  simpa using code_dist (E := ZMod 11) (fun _ => (0 : ZMod 11)) 1 ω11_injective

/-- The codewords `1` and `X`. -/
def t0 : Fin 8 → ZMod 11 := fun _ => 1
def t1 : Fin 8 → ZMod 11 := ω11

theorem t0_mem : t0 ∈ C11 := ⟨![1, 0], by decide⟩
theorem t1_mem : t1 ∈ C11 := ⟨![0, 1], by decide⟩

/-- Rows `1` and `X`, both corrupted at columns `0, 1`. -/
def closeToy : Fin 2 → Fin 8 → ZMod 11 :=
  ![fun x => if x.val < 2 then 5 else 1, fun x => if x.val < 2 then 0 else ω11 x]

/-- Rows `1` corrupted at columns `0, 1` and `X` corrupted at columns `2, 3`. -/
def farToy : Fin 2 → Fin 8 → ZMod 11 :=
  ![fun x => if x.val < 2 then 5 else 1, fun x => if 2 ≤ x.val ∧ x.val < 4 then 0 else ω11 x]

/-- Positive: `closeToy` is `2`-close (one common set `{0, 1}`). -/
theorem close_toy : eClose C11 closeToy 2 := by
  refine ⟨univ.filter (·.val < 2), ![t0, t1], by decide, fun i => ?_, by decide⟩
  fin_cases i
  · exact t0_mem
  · exact t1_mem

/-- Each row of `farToy` is `2`-close on its own. -/
theorem far_toy_rows_close : ∀ i, Close C11 2 (farToy i) := by
  intro i
  fin_cases i
  · exact close_iff_agree.2 ⟨t0, t0_mem, univ.filter (·.val < 2), by decide, by decide⟩
  · exact close_iff_agree.2 ⟨t1, t1_mem, univ.filter (fun x : Fin 8 => 2 ≤ x.val ∧ x.val < 4),
      by decide, by decide⟩

/-- Negative: `farToy` is not `2`-close: the two rows need four distinct columns. -/
theorem far_toy : ¬ eClose C11 farToy 2 := by
  rintro ⟨S, c, hS, hc, hag⟩
  let T0 : Finset (Fin 8) := univ.filter (·.val < 2)
  let T1 : Finset (Fin 8) := univ.filter (fun x => 2 ≤ x.val ∧ x.val < 4)
  have hT0 : T0.card = 2 := by decide
  have hT1 : T1.card = 2 := by decide
  have hrow : ∀ (i : Fin 2) (t : Fin 8 → ZMod 11) (T : Finset (Fin 8)), t ∈ C11 → T.card = 2 →
      (∀ x ∉ T, farToy i x = t x) → c i = t := by
    intro i t T ht hT h
    refine C11_dist.eq_of_agree (hc i) ht (S ∪ T)
      (lt_of_le_of_lt (card_union_le _ _) (by omega)) fun x hx => ?_
    simp only [mem_union, not_or] at hx
    rw [← hag i x hx.1, h x hx.2]
  have hc0 := hrow 0 t0 T0 t0_mem hT0 (by decide)
  have hc1 := hrow 1 t1 T1 t1_mem hT1 (by decide)
  have hbad : ∀ x : Fin 8, x ∈ T0 ∪ T1 → farToy 0 x = t0 x → farToy 1 x = t1 x → False := by
    decide
  have hsub : T0 ∪ T1 ⊆ S := by
    intro x hx
    by_contra hxS
    have h0 := hag 0 x hxS
    have h1 := hag 1 x hxS
    rw [hc0] at h0
    rw [hc1] at h1
    exact hbad x hx h0 h1
  have : (T0 ∪ T1).card = 4 := by decide
  have := card_le_card hsub
  omega

/-- `far_bad_le` applies to `farToy`: `3·2 < 7 < 11`. -/
theorem far_toy_bound :
    Nat.card {r : Fin 2 → ZMod 11 // Close C11 2 (∑ i, r i • farToy i)} ≤ 7 * 11 ^ (2 - 1) := by
  simpa using far_bad_le C11_dist (by norm_num) (by simp [ZMod.card]) farToy far_toy

/-! ### Tightness -/

/-- The length-2 repetition code over `ZMod 3` (`k = 1`, `d = 2`). -/
abbrev C3 : Submodule (ZMod 3) (Fin 2 → ZMod 3) :=
  rsCode (fun _ => (0 : ZMod 3)) 0 (fun c : Fin 2 => (c.val : ZMod 3))

/-- The far row `(0, 1)`. -/
def U3 : Fin 1 → Fin 2 → ZMod 3 := ![![0, 1]]

theorem close_C3_iff (w : Fin 2 → ZMod 3) :
    Close C3 0 w ↔ ∃ msg : Fin (2 ^ 0) → ZMod 3,
      hammingDist w (enc (fun _ => (0 : ZMod 3)) 0 (fun c : Fin 2 => (c.val : ZMod 3)) msg) ≤ 0 :=
  ⟨fun ⟨_, ⟨msg, h⟩, hd⟩ => ⟨msg, by subst h; exact hd⟩, fun ⟨msg, hd⟩ => ⟨_, ⟨msg, rfl⟩, hd⟩⟩

theorem U3_far : ¬ eClose C3 U3 0 := by
  rintro ⟨S, c, hS, hc, hag⟩
  obtain rfl : S = ∅ := card_eq_zero.1 (by omega)
  have : Close C3 0 (U3 0) := ⟨c 0, hc 0, by
    exact Nat.le_zero.2 (hammingDist_eq_zero.2 (funext fun x => hag 0 x (by simp)))⟩
  revert this
  rw [close_C3_iff]
  decide

/-- **Tight**: exactly `(e+1)·|E|^{m−1} = 1` coefficient (`r = 0`) makes `U3`'s combination
close, matching `far_bad_card`. -/
theorem tight_toy :
    Nat.card {r : Fin 1 → ZMod 3 // Close C3 0 (∑ i, r i • U3 i)} = (0 + 1) * 3 ^ (1 - 1) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun r => close_C3_iff _), Nat.card_eq_fintype_card]
  decide

end SpartanChain.RS.Controls
