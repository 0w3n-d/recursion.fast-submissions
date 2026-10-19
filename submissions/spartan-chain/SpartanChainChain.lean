import SpartanChainBlake2sWitness
import SpartanChainSoundnessSpartan

/-!
# The chain R1CS (BLUEPRINT-R1 §2.3; L-C2, L-C3)

`2 ^ κ` copies of the chain block (`SpartanChainBlake2sR1CS.lean`) and the wiring of a hash chain
of length `n` (`1 ≤ n ≤ 2 ^ κ`), as an R1CS `(A z) ∘ (B z) = C z` over a field `E` of
characteristic two, on `2 ^ (15 + κ)` rows and columns.

**Columns** `z = (w ‖ pub)`: column `u < 2^(14+κ)` is the witness `w(u)`, `u = k + 2^14 t`
(position `k` of block `t`); column `2^(14+κ) + u` is `pub(u)`: `pub(0) = 1`, `pub(1 + j)` bit `j`
of `s`, `pub(257 + j)` bit `j` of `h` (`j < 256`, byte `j / 8` bit `j % 8`), else `0`.

**Rows** (the matrices are given by their nonzero entries, all `1`; `NB = 2^(14+κ)`):

| rows | `A` | `B` | `C` |
|---|---|---|---|
| `k + 2^14 t`, `k ≠ 512` | `A0(k, ·)` on block `t` | `B0(k, ·)` on block `t` | `w(k + 2^14 t)` |
| `512 + 2^14 t` | `pub(0)` | `pub(0)` | `w(512 + 2^14 t)` |
| `NB + j` (wiring, `t = 0`) | `pub(1 + j)` | `pub(0)` | `w(648 + j)` |
| `NB + 256 t + j`, `t ≥ 1` | `w(256 + j + 2^14 (t − 1))` | `pub(0)` | `w(648 + j + 2^14 t)` |
| `NB + 2^(8+κ) + j` (tail) | `w(256 + j + 2^14 (n − 1))` | `pub(0)` | `pub(257 + j)` |
| every other row | — | — | — |

`A0`, `B0` are the chain block's row forms **with row 512 cleared** (BLUEPRINT-R1 §2.3, §14;
the review's BP-m5): `blockA k j = (k ≠ 512) ∧ (rowOf k).a_j`.

* `chainA`, `chainB`, `chainC`: the matrices, as sums of indicators of their nonzero entries;
  `rowA`, `rowB`, `rowC` with `matVec_chainA` …: the same, row by row.
* `pubVal`, `zOf w s h`: the extended witness; `ChainSat n κ w s h := Sat chainA chainB chainC
  (zOf w s h)` (the abstract `Sat` of `SpartanChainSoundnessSpartan.lean`).
* L-C2 `chain_sound` and L-C3 `chain_complete` are proved in `SpartanChainChainSound.lean`.
-/

namespace SpartanChain

open RecursionFast ProductCircuit Blake2sCircuit Finset

/-! ## Layout -/

/-- The witness length: `2 ^ κ` blocks of `2 ^ 14` positions. -/
abbrev wLen (κ : ℕ) : ℕ := 2 ^ (14 + κ)

/-- Row and column indices of the chain R1CS: `(w ‖ pub)`, `2 ^ (15 + κ)`. -/
abbrev Ix (κ : ℕ) := Fin (2 ^ (14 + κ + 1))

theorem wLen_eq (κ : ℕ) : wLen κ = 16384 * 2 ^ κ := by
  rw [wLen, pow_add]; norm_num

theorem ixLen_eq (κ : ℕ) : 2 ^ (14 + κ + 1) = 32768 * 2 ^ κ := by
  rw [pow_succ, pow_add]; ring

theorem pow8_eq (κ : ℕ) : 2 ^ (8 + κ) = 256 * 2 ^ κ := by
  rw [pow_add]; norm_num

/-- Bit `j < 256` of a digest: bit `j % 8` of byte `j / 8`. -/
def dbit (d : Digest) (j : ℕ) : Bool :=
  if h : j < 256 then (d[j / 8]'(by omega)).toBitVec.getLsbD (j % 8) else false

/-- Row `k` of the chain block's left matrix, row `512` cleared. -/
noncomputable def blockA (k j : Pos Blake2sCircuit.m) : Bool :=
  decide (k ≠ constPos) && (chainBlock.rowOf k).a.getLsbD j

/-- Row `k` of the chain block's right matrix, row `512` cleared. -/
noncomputable def blockB (k j : Pos Blake2sCircuit.m) : Bool :=
  decide (k ≠ constPos) && (chainBlock.rowOf k).b.getLsbD j

variable {E : Type} [Field E]

/-! ## The matrices (nonzero entries) -/

/-- The left matrix of the chain R1CS with `n` steps laid out in `2 ^ κ` blocks. -/
noncomputable def chainA (n κ : ℕ) (x y : Ix κ) : E :=
  (∑ p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m,
    if blockA p.2.1 p.2.2 = true ∧ x.val = p.2.1.val + 16384 * p.1.val ∧
      y.val = p.2.2.val + 16384 * p.1.val then 1 else 0) +
  (∑ t : Fin (2 ^ κ), if x.val = 512 + 16384 * t.val ∧ y.val = wLen κ then 1 else 0) +
  (∑ p : Fin (2 ^ κ) × Fin 256, if 1 ≤ p.1.val ∧ x.val = wLen κ + 256 * p.1.val + p.2.val ∧
      y.val = 256 + p.2.val + 16384 * (p.1.val - 1) then 1 else 0) +
  (∑ j : Fin 256, if x.val = wLen κ + j.val ∧ y.val = wLen κ + 1 + j.val then 1 else 0) +
  (∑ j : Fin 256, if x.val = wLen κ + 2 ^ (8 + κ) + j.val ∧
      y.val = 256 + j.val + 16384 * (n - 1) then 1 else 0)

/-- The right matrix of the chain R1CS. -/
noncomputable def chainB (κ : ℕ) (x y : Ix κ) : E :=
  (∑ p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m,
    if blockB p.2.1 p.2.2 = true ∧ x.val = p.2.1.val + 16384 * p.1.val ∧
      y.val = p.2.2.val + 16384 * p.1.val then 1 else 0) +
  (∑ t : Fin (2 ^ κ), if x.val = 512 + 16384 * t.val ∧ y.val = wLen κ then 1 else 0) +
  (∑ p : Fin (2 ^ κ) × Fin 256, if x.val = wLen κ + 256 * p.1.val + p.2.val ∧
      y.val = wLen κ then 1 else 0) +
  (∑ j : Fin 256, if x.val = wLen κ + 2 ^ (8 + κ) + j.val ∧ y.val = wLen κ then 1 else 0)

/-- The output matrix of the chain R1CS. -/
def chainC (κ : ℕ) (x y : Ix κ) : E :=
  (∑ u : Fin (wLen κ), if x.val = u.val ∧ y.val = u.val then 1 else 0) +
  (∑ p : Fin (2 ^ κ) × Fin 256, if x.val = wLen κ + 256 * p.1.val + p.2.val ∧
      y.val = 648 + p.2.val + 16384 * p.1.val then 1 else 0) +
  (∑ j : Fin 256, if x.val = wLen κ + 2 ^ (8 + κ) + j.val ∧
      y.val = wLen κ + 257 + j.val then 1 else 0)

/-! ## The extended witness and the relation -/

/-- The public part: `pub(0) = 1`, `pub(1 + j) = s_j`, `pub(257 + j) = h_j`, else `0`. -/
def pubVal (s h : Digest) (u : ℕ) : E :=
  if u = 0 then 1
  else if u < 257 then ofBool E (dbit s (u - 1))
  else if u < 513 then ofBool E (dbit h (u - 257))
  else 0

/-- The extended witness `(w ‖ pub(s, h))`. -/
def zOf {κ : ℕ} (w : Fin (wLen κ) → E) (s h : Digest) (y : Ix κ) : E :=
  if hy : y.val < wLen κ then w ⟨y.val, hy⟩ else pubVal s h (y.val - wLen κ)

/-- **The chain relation** (BLUEPRINT-R1 §2.3 `Sat n s h z`): the chain R1CS holds on
`(w ‖ pub(s, h))`. -/
def ChainSat (n κ : ℕ) (w : Fin (wLen κ) → E) (s h : Digest) : Prop :=
  Sat (chainA n κ) (chainB κ) (chainC κ) (zOf w s h)

/-! ## Rows -/

/-- A vector on the indices read at a natural number (`0` out of range). -/
def zN {κ : ℕ} (z : Ix κ → E) (v : ℕ) : E := if h : v < 2 ^ (14 + κ + 1) then z ⟨v, h⟩ else 0

/-- Row `x` of `A z`. -/
noncomputable def rowA (n κ : ℕ) (z : ℕ → E) (x : ℕ) : E :=
  if x < wLen κ then
    if x % 16384 = 512 then z (wLen κ)
    else ∑ j : Pos Blake2sCircuit.m,
      if blockA (pos (x % 16384)) j = true then z (j.val + 16384 * (x / 16384)) else 0
  else if x - wLen κ < 256 then z (wLen κ + 1 + (x - wLen κ))
  else if x - wLen κ < 2 ^ (8 + κ) then
    z (256 + (x - wLen κ) % 256 + 16384 * ((x - wLen κ) / 256 - 1))
  else if x - wLen κ < 2 ^ (8 + κ) + 256 then
    z (256 + (x - wLen κ - 2 ^ (8 + κ)) + 16384 * (n - 1))
  else 0

/-- Row `x` of `B z`. -/
noncomputable def rowB (κ : ℕ) (z : ℕ → E) (x : ℕ) : E :=
  if x < wLen κ then
    if x % 16384 = 512 then z (wLen κ)
    else ∑ j : Pos Blake2sCircuit.m,
      if blockB (pos (x % 16384)) j = true then z (j.val + 16384 * (x / 16384)) else 0
  else if x - wLen κ < 2 ^ (8 + κ) + 256 then z (wLen κ)
  else 0

/-- Row `x` of `C z`. -/
def rowC (κ : ℕ) (z : ℕ → E) (x : ℕ) : E :=
  if x < wLen κ then z x
  else if x - wLen κ < 2 ^ (8 + κ) then
    z (648 + (x - wLen κ) % 256 + 16384 * ((x - wLen κ) / 256))
  else if x - wLen κ < 2 ^ (8 + κ) + 256 then z (wLen κ + 257 + (x - wLen κ - 2 ^ (8 + κ)))
  else 0

section RowLemmas

variable {κ : ℕ}

/-- The sum over columns of one indicator. -/
private theorem sum_col (z : Ix κ → E) (c : Prop) [Decidable c] (v : ℕ) :
    ∑ y : Ix κ, (if c ∧ y.val = v then (1 : E) else 0) * z y = if c then zN z v else 0 := by
  by_cases hc : c
  · simp only [hc, true_and, ite_mul, one_mul, zero_mul, ↓reduceIte, zN]
    split_ifs with hv
    · rw [Finset.sum_eq_single ⟨v, hv⟩ (fun y _ hy ↦ by
          rw [ite_eq_right (fun h ↦ hy (Fin.ext h))]) (by simp)]
      simp
    · exact Finset.sum_eq_zero fun y _ ↦ by rw [ite_eq_right (by omega)]
  · simp [hc]

/-- The sum over columns of a sum of indicators. -/
private theorem sum_col_sum {ι : Type} [Fintype ι] (z : Ix κ → E) (c : ι → Prop)
    [DecidablePred c] (v : ι → ℕ) :
    ∑ y : Ix κ, (∑ p, if c p ∧ y.val = v p then (1 : E) else 0) * z y =
      ∑ p, if c p then zN z (v p) else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ ↦ sum_col z (c p) (v p)

private theorem and_assoc_ite {α : Type} {a b c : Prop} [Decidable a] [Decidable b] [Decidable c]
    (u v : α) : (if a ∧ b ∧ c then u else v) = if (a ∧ b) ∧ c then u else v := by
  simp only [and_assoc]

end RowLemmas

/-- A sum whose terms vanish except at one index. -/
theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (g : ι → E) (i₀ : ι) (h : ∀ i, P i ↔ i = i₀) :
    ∑ i, (if P i then g i else 0) = g i₀ := by
  rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by rw [ite_eq_right (fun hp ↦ hi ((h i).mp hp))])
    (by simp), ite_eq_left ((h i₀).mpr rfl)]

/-- A sum whose terms all vanish. -/
theorem sum_ite_none {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (g : ι → E)
    (h : ∀ i, ¬ P i) : ∑ i, (if P i then g i else 0) = 0 :=
  Finset.sum_eq_zero fun i _ ↦ by rw [ite_eq_right (h i)]

/-- One index read off an offset: `Σ_{j < N} [x = a + j] g(j) = g(x - a)` if `a ≤ x < a + N`. -/
theorem sum_offset {N : ℕ} (g : ℕ → E) (a x : ℕ) :
    ∑ j : Fin N, (if x = a + j.val then g j.val else 0) =
      if a ≤ x ∧ x < a + N then g (x - a) else 0 := by
  split_ifs with hx
  · exact sum_ite_single (fun j : Fin N ↦ x = a + j.val) (fun j ↦ g j.val) ⟨x - a, by omega⟩
      fun j ↦ ⟨fun h ↦ Fin.ext (by simp; omega), fun h ↦ by subst h; simp; omega⟩
  · exact sum_ite_none _ _ fun j h ↦ hx (by omega)

section RowSums

variable {κ : ℕ}

private theorem sumS1 (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool) (z : ℕ → E)
    (x : ℕ) :
    (∑ p : Fin (2 ^ κ) × Pos Blake2sCircuit.m × Pos Blake2sCircuit.m,
      if bk p.2.1 p.2.2 = true ∧ x = p.2.1.val + 16384 * p.1.val then
        z (p.2.2.val + 16384 * p.1.val) else 0) =
    if x < wLen κ then ∑ j : Pos Blake2sCircuit.m,
      (if bk (pos (x % 16384)) j = true then z (j.val + 16384 * (x / 16384)) else 0) else 0 := by
  have hw := wLen_eq κ
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have h14 : (2 : ℕ) ^ Blake2sCircuit.m = 16384 := rfl
  split_ifs with hx
  · rw [Finset.sum_eq_single (⟨x / 16384, by omega⟩ : Fin (2 ^ κ))]
    · rw [Finset.sum_eq_single (pos (x % 16384) : Pos Blake2sCircuit.m)]
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hp : ((pos (x % 16384) : Pos Blake2sCircuit.m) : ℕ) = x % 16384 :=
          pos_val (by rw [h14]; omega)
        by_cases hb : bk (pos (x % 16384)) j = true
        · rw [ite_eq_left ⟨hb, by rw [hp]; simp; omega⟩, ite_eq_left hb]
        · rw [ite_eq_right (fun h ↦ hb h.1), ite_eq_right hb]
      · intro k _ hk
        refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hk (Fin.ext ?_)
        have : k.val < 16384 := k.isLt
        rw [pos_val (by rw [h14]; omega)]
        simp at h; omega
      · simp
    · intro t _ ht
      refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ ht (Fin.ext ?_)
      have : k.val < 16384 := k.isLt
      simp only at h ⊢
      omega
    · simp
  · refine Finset.sum_eq_zero fun t _ ↦ Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun j _ ↦
      ite_eq_right fun h ↦ hx ?_
    have : k.val < 16384 := k.isLt
    have := t.isLt
    omega

private theorem sumS2 (v : E) (x : ℕ) :
    (∑ t : Fin (2 ^ κ), if x = 512 + 16384 * t.val then v else 0) =
      if x < wLen κ ∧ x % 16384 = 512 then v else 0 := by
  have hw := wLen_eq κ
  split_ifs with hx
  · exact sum_ite_single (fun t : Fin (2 ^ κ) ↦ x = 512 + 16384 * t.val) (fun _ ↦ v)
      ⟨x / 16384, by omega⟩ fun t ↦ ⟨fun h ↦ Fin.ext (by simp; omega), fun h ↦ by subst h; simp; omega⟩
  · exact sum_ite_none _ _ fun t h ↦ hx ⟨by have := t.isLt; omega, by omega⟩

private theorem sumS3 (z : ℕ → ℕ → E) (c x : ℕ) (lo : ℕ) :
    (∑ p : Fin (2 ^ κ) × Fin 256, if lo ≤ p.1.val ∧ x = c + 256 * p.1.val + p.2.val then
        z p.1.val p.2.val else 0) =
      if c + 256 * lo ≤ x ∧ x < c + 2 ^ (8 + κ) then z ((x - c) / 256) ((x - c) % 256) else 0 := by
  have h8 := pow8_eq κ
  rw [Fintype.sum_prod_type]
  split_ifs with hx
  · rw [Finset.sum_eq_single (⟨(x - c) / 256, by omega⟩ : Fin (2 ^ κ))]
    · exact sum_ite_single (fun j : Fin 256 ↦ lo ≤ (x - c) / 256 ∧
          x = c + 256 * ((x - c) / 256) + j.val) (fun j ↦ z ((x - c) / 256) j.val)
        ⟨(x - c) % 256, by omega⟩
        fun j ↦ ⟨fun h ↦ Fin.ext (by simp; omega), fun h ↦ by subst h; simp; omega⟩
    · intro t _ ht
      exact sum_ite_none _ _ fun j h ↦ ht (Fin.ext (by simp only at h ⊢; omega))
    · simp
  · exact Finset.sum_eq_zero fun t _ ↦ sum_ite_none _ _ fun j h ↦ hx
      ⟨by simp only at h; omega, by simp only at h; have := t.isLt; have := j.isLt; omega⟩

end RowSums

theorem blockA_cpos (j : Pos Blake2sCircuit.m) : blockA (pos 512) j = false := by
  have : (pos 512 : Pos Blake2sCircuit.m) = constPos := Fin.ext (pos_val (by decide))
  simp [blockA, this]

theorem blockB_cpos (j : Pos Blake2sCircuit.m) : blockB (pos 512) j = false := by
  have : (pos 512 : Pos Blake2sCircuit.m) = constPos := Fin.ext (pos_val (by decide))
  simp [blockB, this]

section MatVec

variable {κ : ℕ}

/-- `A z`, row by row. -/
theorem matVec_chainA (n : ℕ) (z : Ix κ → E) (x : Ix κ) :
    matVec (chainA n κ) z x = rowA n κ (zN z) x.val := by
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hL := ixLen_eq κ
  have hx := x.isLt
  simp only [matVec, chainA, add_mul, Finset.sum_add_distrib, ← and_assoc]
  rw [sum_col_sum, sum_col_sum, sum_col_sum, sum_col_sum, sum_col_sum,
    sumS1 blockA (zN z) x.val, sumS2 (zN z (wLen κ)) x.val,
    sumS3 (fun t j ↦ zN z (256 + j + 16384 * (t - 1))) (wLen κ) x.val 1,
    sum_offset (fun j ↦ zN z (wLen κ + 1 + j)) (wLen κ) x.val,
    sum_offset (fun j ↦ zN z (256 + j + 16384 * (n - 1))) (wLen κ + 2 ^ (8 + κ)) x.val]
  unfold rowA
  by_cases h0 : x.val < wLen κ
  · by_cases h512 : x.val % 16384 = 512
    · simp only [h0, h512, blockA_cpos, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
        and_self]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · simp only [h0, h512, ↓reduceIte, and_false]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  · simp only [h0, ↓reduceIte, false_and]
    by_cases h1 : x.val - wLen κ < 256
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h1]
      simp only [zero_add, add_zero]
      all_goals (congr 1 <;> omega)
    · rw [ite_eq_right h1]
      by_cases h2 : x.val - wLen κ < 2 ^ (8 + κ)
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
        simp only [zero_add, add_zero]
        all_goals (congr 1 <;> omega)
      · rw [ite_eq_right h2]
        by_cases h3 : x.val - wLen κ < 2 ^ (8 + κ) + 256
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h3]
          simp only [zero_add]
          all_goals (congr 1 <;> omega)
        · rw [ite_eq_right h3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          simp

/-- `B z`, row by row. -/
theorem matVec_chainB (z : Ix κ → E) (x : Ix κ) :
    matVec (chainB κ) z x = rowB κ (zN z) x.val := by
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hx := x.isLt
  have hL := ixLen_eq κ
  simp only [matVec, chainB, add_mul, Finset.sum_add_distrib, ← and_assoc]
  rw [sum_col_sum, sum_col_sum, sum_col_sum, sum_col_sum,
    sumS1 blockB (zN z) x.val, sumS2 (zN z (wLen κ)) x.val]
  have hS3 := sumS3 (κ := κ) (fun _ _ ↦ zN z (wLen κ)) (wLen κ) x.val 0
  simp only [Nat.zero_le, true_and, mul_zero, add_zero] at hS3
  rw [hS3, sum_offset (fun _ ↦ zN z (wLen κ)) (wLen κ + 2 ^ (8 + κ)) x.val]
  unfold rowB
  by_cases h0 : x.val < wLen κ
  · by_cases h512 : x.val % 16384 = 512
    · simp only [h0, h512, blockB_cpos, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
        and_self]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · simp only [h0, h512, ↓reduceIte, and_false]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  · simp only [h0, ↓reduceIte, false_and]
    by_cases h2 : x.val - wLen κ < 2 ^ (8 + κ)
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      simp
    · by_cases h3 : x.val - wLen κ < 2 ^ (8 + κ) + 256
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h3]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h3]
        simp

/-- `C z`, row by row. -/
theorem matVec_chainC (z : Ix κ → E) (x : Ix κ) :
    matVec (chainC κ) z x = rowC κ (zN z) x.val := by
  have hw := wLen_eq κ
  have h8 := pow8_eq κ
  have hx := x.isLt
  have hL := ixLen_eq κ
  simp only [matVec, chainC, add_mul, Finset.sum_add_distrib]
  have hS3 := sumS3 (κ := κ) (fun t j ↦ zN z (648 + j + 16384 * t)) (wLen κ) x.val 0
  simp only [Nat.zero_le, true_and, mul_zero, add_zero] at hS3
  rw [sum_col_sum, sum_col_sum, sum_col_sum, hS3,
    sum_offset (fun j ↦ zN z (wLen κ + 257 + j)) (wLen κ + 2 ^ (8 + κ)) x.val]
  have hS0 : (∑ u : Fin (wLen κ), if x.val = u.val then zN z u.val else 0) =
      if x.val < wLen κ then zN z x.val else 0 := by
    have := sum_offset (N := wLen κ) (fun u ↦ zN z u) 0 x.val
    simpa using this
  rw [hS0]
  unfold rowC
  by_cases h0 : x.val < wLen κ
  · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_right (by omega), ite_eq_right (by omega)]
    simp
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h2 : x.val - wLen κ < 2 ^ (8 + κ)
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h2]
      simp only [add_zero, zero_add]
    · by_cases h3 : x.val - wLen κ < 2 ^ (8 + κ) + 256
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right h2, ite_eq_left h3]
        simp only [zero_add]
        all_goals (congr 1 <;> omega)
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h3]
        simp

end MatVec

end SpartanChain
