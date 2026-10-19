import SpartanChainProximity
import SpartanChainField

/-!
# The PCS parameters and their error terms (blueprint §5.2, §5.5, §9.2 rows R0 and R7)

* The shape of §5.2 as functions of `κ` (`muR`, `lk`, `lN`, `rows`, `msgLen`, `cols`, `dist`,
  `radius`, `tQ = 260`) and its arithmetic (`cols_eq`, `dist_eq`, `three_radius_lt`, `rows_mul`).
* The protocol's code over `F ⊂ EF`: the points `dom N c` (the element of `F` whose word is
  `c`), the constants `kap` (§5.1's `κ_i = W_i(ω_{2^i})`), `code κ`, and its minimum distance
  `code_minDist`.
* R0: `r0_far_bad` is `far_bad_le` at the protocol's code, with `d/|EF| ≤ 2^-169` in exact form.
* R7: `far_miss` (`(17/24)^260 ≤ (4/5)·2^-129`, so `< 2^-129.32`) and `close_miss`
  (`(5/12)^260 ≤ 2^-328`), as L-RS3 at the protocol's parameters, in exact `ℕ` form.
* `eps_budget`: the per-step sum stays below `2^-129` with `logCap = 2^96`
  (`3·2^-152` collisions and hits, `2^-160` state hits, `2^-256` the `i ≤ j` state hit).

Every inequality between large numbers is a `ℕ` comparison decided by the kernel's `GMP`
arithmetic.
-/

namespace SpartanChain.PCS

open RS

/-! ### Shape (§5.2) -/

/-- `μ_r(κ) = ⌊(κ+3)/2⌋`, the log of the number of rows. -/
def muR (κ : ℕ) : ℕ := (κ + 3) / 2
/-- `ℓ_k = 8 + κ − μ_r`, the log of the message length. -/
def lk (κ : ℕ) : ℕ := 8 + κ - muR κ
/-- `ℓ_N = ℓ_k + 3` (rate `1/8`). -/
def lN (κ : ℕ) : ℕ := lk κ + 3
/-- `m = 2^{μ_r}` rows. -/
def rows (κ : ℕ) : ℕ := 2 ^ muR κ
/-- `k = 2^{ℓ_k}`. -/
def msgLen (κ : ℕ) : ℕ := 2 ^ lk κ
/-- `N = 2^{ℓ_N}` columns. -/
def cols (κ : ℕ) : ℕ := 2 ^ lN κ
/-- `d = N − k + 1`. -/
def dist (κ : ℕ) : ℕ := cols κ - msgLen κ + 1
/-- `e = ⌊(d − 1)/3⌋`. -/
def radius (κ : ℕ) : ℕ := (dist κ - 1) / 3
/-- `t = 260` opened columns. -/
def tQ : ℕ := 260

theorem msgLen_pos (κ : ℕ) : 0 < msgLen κ := by unfold msgLen; positivity

theorem cols_eq (κ : ℕ) : cols κ = 8 * msgLen κ := by
  unfold cols msgLen lN; rw [pow_add]; ring

theorem dist_eq (κ : ℕ) : dist κ = 7 * msgLen κ + 1 := by
  unfold dist; rw [cols_eq]; omega

theorem radius_eq (κ : ℕ) : radius κ = 7 * msgLen κ / 3 := by
  unfold radius; rw [dist_eq]; omega

theorem three_radius_lt (κ : ℕ) : 3 * radius κ < dist κ := by
  rw [radius_eq, dist_eq]; omega

/-- The packed witness `2^{8+κ}` is the `m × k` matrix. -/
theorem rows_mul (κ : ℕ) : rows κ * msgLen κ = 2 ^ (8 + κ) := by
  unfold rows msgLen lk muR; rw [← pow_add]; congr 1; omega

/-- The table of §5.2. -/
theorem shape_table :
    (rows 0, msgLen 0, cols 0) = (2, 128, 1024) ∧ (rows 4, msgLen 4, cols 4) = (8, 512, 4096) ∧
    (rows 10, msgLen 10, cols 10) = (64, 4096, 32768) ∧
    (rows 14, msgLen 14, cols 14) = (256, 16384, 2 ^ 17) ∧
    (rows 20, msgLen 20, cols 20) = (2048, 2 ^ 17, 2 ^ 20) := by decide

/-! ### The code over `F ⊂ EF` -/

/-- `ω_c`: the element of `F` whose word is `c`. -/
def dom (N : ℕ) (c : Fin N) : F := F.ofUInt64 (UInt64.ofNat c)

/-- `ω_{2^i}` (`= x^i` for `i < 64`). -/
def pt (i : ℕ) : F := F.ofUInt64 (UInt64.ofNat (2 ^ i))

/-- §5.1's constants `κ_i = W_i(ω_{2^i})` for `i < ℓ`. -/
def kap (ℓ : ℕ) (i : ℕ) : F := (kappaArr pt ℓ).getD i 0

/-- The protocol's code: `Enc` over `EF` at the points `ω_0, …, ω_{N−1}`. -/
abbrev code (κ : ℕ) : Submodule EF (Fin (cols κ) → EF) := rsCode (kap (lk κ)) (lk κ) (dom (cols κ))

theorem dom_injective {N : ℕ} (hN : N ≤ 2 ^ 64) : Function.Injective (dom N) := by
  intro a b h
  have h' := congrArg (fun z : F => z.val.toNat) h
  simp only [dom, F.ofUInt64, UInt64.toNat_ofNat'] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact Fin.ext h'

theorem cols_le (κ : ℕ) (hκ : κ ≤ 20) : cols κ ≤ 2 ^ 20 := by
  unfold cols lN lk muR; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The protocol's code has minimum distance `d = 7k + 1`. -/
theorem code_minDist (κ : ℕ) (hκ : κ ≤ 20) : MinDist (code κ) (dist κ) := by
  have := code_dist (E := EF) (kap (lk κ)) (lk κ)
    (dom_injective (N := cols κ) ((cols_le κ hκ).trans (by norm_num)))
  simpa [dist, msgLen] using this

/-! ### R0: the proximity test -/

/-- `d · 2^169 ≤ 2^192` for every `κ ≤ 20`. -/
theorem dist_mul_le (κ : ℕ) (hκ : κ ≤ 20) : dist κ * 2 ^ 169 ≤ 2 ^ 192 := by
  have h : msgLen κ ≤ 2 ^ 17 := by
    unfold msgLen lk muR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [dist_eq]
  calc (7 * msgLen κ + 1) * 2 ^ 169 ≤ (7 * 2 ^ 17 + 1) * 2 ^ 169 := by gcongr
    _ ≤ 2 ^ 192 := by norm_num

/-- **R0** (L-RS2 at the protocol's code): if `U` is not `e`-close, at most a `2^-169` fraction of
the coefficient vectors `r ∈ EF^m` make `Σ r_i U_i` `e`-close. -/
theorem r0_far_bad (κ : ℕ) (hκ : κ ≤ 20) {m : ℕ} (U : Fin m → Fin (cols κ) → EF)
    (hfar : ¬ eClose (code κ) U (radius κ)) :
    Nat.card {r : Fin m → EF // Close (code κ) (radius κ) (∑ i, r i • U i)} * 2 ^ 169 ≤
      (2 ^ 192) ^ m := by
  have hm : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    exact hfar ⟨∅, fun i => i.elim0, by simp, fun i => i.elim0, fun i => i.elim0⟩
  have hb := far_bad_le (code_minDist κ hκ) (three_radius_lt κ)
    (by rw [EF.card_EF]; have := dist_mul_le κ hκ; omega) U hfar
  rw [EF.card_EF] at hb
  calc _ ≤ dist κ * (2 ^ 192) ^ (m - 1) * 2 ^ 169 := Nat.mul_le_mul_right _ hb
    _ = dist κ * 2 ^ 169 * (2 ^ 192) ^ (m - 1) := by ring
    _ ≤ 2 ^ 192 * (2 ^ 192) ^ (m - 1) := Nat.mul_le_mul_right _ (dist_mul_le κ hκ)
    _ = (2 ^ 192) ^ m := by rw [← pow_succ']; congr 1; omega

/-! ### R7: the column queries -/

set_option exponentiation.threshold 600

/-- `(17/24)^260 · 2^129 ≤ 4/5`, i.e. `(17/24)^260 ≤ 2^{-129.32}`. -/
theorem pow17_le : 17 ^ 260 * 2 ^ 129 * 5 ≤ 24 ^ 260 * 4 := by decide

/-- `(5/12)^260 ≤ 2^-328`. -/
theorem pow5_le : 5 ^ 260 * 2 ^ 328 ≤ 12 ^ 260 := by decide

/-- Negative control: `t = 259` columns do not reach `2^-129`. -/
theorem pow17_259 : ¬ 17 ^ 259 * 2 ^ 129 ≤ 24 ^ 259 := by decide

/-- One column misses `e + 1` disagreements with probability `≤ 17/24`. -/
theorem far_ratio (κ : ℕ) : 24 * (cols κ - (radius κ + 1)) ≤ 17 * cols κ := by
  rw [cols_eq, radius_eq]; omega

/-- One column misses `d − e` disagreements with probability `≤ 5/12`. -/
theorem close_ratio (κ : ℕ) : 12 * (cols κ - (dist κ - radius κ)) ≤ 5 * cols κ := by
  rw [cols_eq, radius_eq, dist_eq]; omega

/-- `a ≤ (N − s)^t`, `b·(N − s) ≤ a'·N` ⇒ `a · b^t ≤ a'^t · N^t`. -/
theorem miss_pow {N s t a b a' : ℕ} (ha : a ≤ (N - s) ^ t) (hr : b * (N - s) ≤ a' * N) :
    a * b ^ t ≤ a' ^ t * N ^ t := by
  calc a * b ^ t ≤ (N - s) ^ t * b ^ t := Nat.mul_le_mul_right _ ha
    _ = (b * (N - s)) ^ t := by ring
    _ ≤ (a' * N) ^ t := Nat.pow_le_pow_left hr t
    _ = a' ^ t * N ^ t := by ring

/-- **R7, far case** (L-RS3 at the protocol's parameters): if the difference set has more than
`e` columns, the `t = 260` index tuples that miss it are at most a `(4/5)·2^-129` fraction. -/
theorem far_miss (κ : ℕ) (D : Finset (Fin (cols κ))) (hD : radius κ + 1 ≤ D.card) :
    Nat.card {c : Fin tQ → Fin (cols κ) // ∀ j, c j ∉ D} * 2 ^ 129 * 5 ≤ 4 * cols κ ^ tQ := by
  have h := miss_pow (t := tQ) (b := 24) (a' := 17)
    ((miss_le D tQ hD).trans_eq (by rw [Fintype.card_fin])) (far_ratio κ)
  have h24 : 0 < 24 ^ tQ := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ h24
  calc _ = (Nat.card {c : Fin tQ → Fin (cols κ) // ∀ j, c j ∉ D} * 24 ^ tQ) * (2 ^ 129 * 5) := by
          ring
    _ ≤ (17 ^ tQ * cols κ ^ tQ) * (2 ^ 129 * 5) := Nat.mul_le_mul_right _ h
    _ = (17 ^ 260 * 2 ^ 129 * 5) * cols κ ^ tQ := by unfold tQ; ring
    _ ≤ (24 ^ 260 * 4) * cols κ ^ tQ := Nat.mul_le_mul_right _ pow17_le
    _ = _ := by unfold tQ; ring

/-- **R7, close case**: if the difference set has at least `d − e` columns, the tuples that miss
it are at most a `2^-328` fraction. -/
theorem close_miss (κ : ℕ) (D : Finset (Fin (cols κ))) (hD : dist κ - radius κ ≤ D.card) :
    Nat.card {c : Fin tQ → Fin (cols κ) // ∀ j, c j ∉ D} * 2 ^ 328 ≤ cols κ ^ tQ := by
  have h := miss_pow (t := tQ) (b := 12) (a' := 5)
    ((miss_le D tQ hD).trans_eq (by rw [Fintype.card_fin])) (close_ratio κ)
  have h12 : 0 < 12 ^ tQ := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ h12
  calc _ = (Nat.card {c : Fin tQ → Fin (cols κ) // ∀ j, c j ∉ D} * 12 ^ tQ) * 2 ^ 328 := by ring
    _ ≤ (5 ^ tQ * cols κ ^ tQ) * 2 ^ 328 := Nat.mul_le_mul_right _ h
    _ = (5 ^ 260 * 2 ^ 328) * cols κ ^ tQ := by unfold tQ; ring
    _ ≤ 12 ^ 260 * cols κ ^ tQ := Nat.mul_le_mul_right _ pow5_le
    _ = _ := by unfold tQ; ring

/-! ### The per-step budget -/

/-- `(4/5)·2^-129 + 3·2^-152 + 2^-160 + 2^-256 ≤ 2^-129`: R7 plus the `Bad` terms at
`logCap = 2^96` (the last one the `i ≤ j` state hit, §9.3). -/
theorem eps_budget :
    (4 / 5 : ℚ) / 2 ^ 129 + 3 / 2 ^ 152 + 1 / 2 ^ 160 + 1 / 2 ^ 256 ≤ 1 / 2 ^ 129 := by
  norm_num

/-- A single-answer round (`≤ 3` bad answers in `|EF|`) and R0 are far below `2^-129`. -/
theorem single_round_le : (3 : ℚ) / 2 ^ 192 ≤ 1 / 2 ^ 169 ∧ (1 : ℚ) / 2 ^ 169 ≤ 1 / 2 ^ 129 := by
  norm_num

end SpartanChain.PCS
