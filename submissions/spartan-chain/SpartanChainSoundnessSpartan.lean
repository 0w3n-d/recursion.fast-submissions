import SpartanChainRingSwitch

/-!
# The algebraic rounds of the security argument (blueprint §9.2, rounds R1–R6)

Generic over a field `E` of characteristic two (the challenges; `EF` in R1) and, for ring
switching, a ring `K` with `[Algebra K E]` (`F`). The R1CS is abstract: three matrices on the cube
`A B C : Fin (2^a) → Fin (2^b) → E` with their extensions `matMle` (the concrete chain matrices and
their formulas `matrix_mle_eq` plug in through `Chain.lean`), and an extended witness
`z : Fin (2^b) → E` (the decoded `z_dec`, already fixed by the close-mode decoding when the
challenges are drawn).

Each round of §9.2 has a **doom predicate** on the chain's state and a lemma in counting form:
*from a doomed state, the number of challenge values in `E` that make the next state not doomed is
at most the bound*. The absorb rows between rounds carry doom without a challenge ("after …"
lemmas, no division).

| round | doom (state) | lemma | bound |
|---|---|---|---|
| start | `¬ Sat A B C z` ⇒ the residual table `F` is nonzero | `zc_start` | — |
| R1, `τ_l` | the table `F` bound at `τ_{<l}` is nonzero | `zc_escape_le` | 1 |
| R1 → R2 | all bound: `F̃(τ) ≠ 0`, the outer claim `0` is false | `zc_end`, `outer_start` | — |
| R2, `r_{x,l}` | `claim ≠ trueSum outerExpr (outer tables bound at r_{x,<l})` | `round_escape_le` | 3 |
| after R2 | the triple `(v_A, v_B, v_C)` is wrong | `outer_final`, `triple_wrong` | — |
| R3, `ρ` | the triple is wrong; escape: the batched claim is true | `batch_escape_le` | 2 |
| R4, `r_{y,l}` | `claim ≠ trueSum innerExpr (inner tables bound)` | `round_escape_le` | 2 |
| after R4 | the slices are wrong (`δ ≠ 0`) | `inner_final`, `z_mle_slices`, `ne_of_claim` | — |
| R5, `f_p` | `rsDoom` (`∃ k < 2^(s'+1-p), π_k ≠ 0`); start by L-R1 | `rs_start`, `rs_escape_le` | 1 |
| after R5 | `T ≠ Σ_{u'} W(u') q(u')` | `rs_end`, `prod_trueSum` | — |
| R6, `r''_l` | `claim ≠ trueSum innerExpr (#[W, q] bound)` | `round_escape_le` | 2 |
| after R6 | the evaluation claim `v'` is wrong | `ne_of_claim` | — |

`round_escape_le` (R2, R4, R6) is in `SpartanChainSumcheck`; it covers a round polynomial of any
size (a wrong size fails the check, so the escape set is empty).
-/

namespace SpartanChain

open Finset

/-! ## Tables from functions -/

section Tables

variable {R : Type*} [CommRing R]

theorem tbl_ofFn {ℓ : ℕ} (f : Fin (2 ^ ℓ) → R) : tbl ℓ (Array.ofFn f) = f := by
  funext u
  simp [tbl]

/-- One table bound at `cs`, in order. -/
def bindT (t : Array R) : List R → Array R
  | [] => t
  | c :: cs => bindT (bind0 t c) cs

theorem bindT_size (t : Array R) (cs : List R) {m : ℕ} (ht : t.size = 2 ^ (cs.length + m)) :
    (bindT t cs).size = 2 ^ m := by
  induction cs generalizing t with
  | nil => simpa [bindT] using ht
  | cons c cs ih =>
    refine ih _ ?_
    rw [bind0_size, ht, List.length_cons, show cs.length + 1 + m = (cs.length + m) + 1 by omega,
      pow_succ, Nat.mul_div_cancel _ two_pos]

/-- All variables bound: the one entry is the extension at `cs`. -/
theorem tbl_bindT (t : Array R) (cs : List R) (ht : t.size = 2 ^ cs.length) (u : Fin (2 ^ 0)) :
    tbl 0 (bindT t cs) u = mle (tbl cs.length t) (pt cs) := by
  induction cs generalizing t with
  | nil => rw [bindT, mle_zero]; congr 1; exact Fin.ext (by simp)
  | cons c cs ih =>
    have hs : (bind0 t c).size = 2 ^ cs.length := by
      rw [bind0_size, ht, List.length_cons, pow_succ, Nat.mul_div_cancel _ two_pos]
    rw [bindT, ih _ hs, tbl_bind0 t c ht]
    symm
    rw [mle_fix0, pt_cons]
    rfl

/-- A summand of two tables: `t₀ · t₁` (inner, ring-switching). -/
def innerExpr : Expr := .mul (.var 0) (.var 1)

theorem innerExpr_deg : innerExpr.deg = 2 := rfl

/-- The true sum of `t₀ · t₁` over two tables given as functions. -/
theorem prod_trueSum {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → R) :
    trueSum innerExpr #[Array.ofFn f, Array.ofFn g] ℓ = ∑ u, f u * g u := by
  simp [trueSum, innerExpr, Expr.eval, tbl_ofFn]

omit [CommRing R] in
theorem prod_sizes {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → R) :
    ∀ t ∈ #[Array.ofFn f, Array.ofFn g], t.size = 2 ^ ℓ := by
  simp

/-- The extension of `eq(a, ·)` is `eq(a, ·)`. -/
theorem mle_eqPt {ℓ : ℕ} (a r : Fin ℓ → R) : mle (fun u ↦ eq a (cube u)) r = eq a r := by
  rw [mle, eq_swap a r, ← eq_mle r a]
  exact Finset.sum_congr rfl fun u _ ↦ by rw [eq_swap a (cube u)]

/-- The extension of `z = (w ‖ pub)` (top variable selects `pub`) at `(r_lo, r_hi, r_top)`:
`(1 - r_top) · Σ_i eq(r_lo, i) · Q̃_i(r_hi) + r_top · p̃ub(r_lo, r_hi)` with the slices
`Q_i(u') = w(i + 2^lo u')` (§4.2; in characteristic two `1 - r_top = 1 + r_top`). -/
theorem z_mle_slices {lo hi : ℕ} (w pub : Fin (2 ^ (lo + hi)) → R)
    (z : Fin (2 ^ (lo + hi + 1)) → R)
    (hz : ∀ u (c : Fin (2 ^ 1)), z (join u c) = if c.val = 0 then w u else pub u)
    (rlo : Fin lo → R) (rhi : Fin hi → R) (rtop : R) :
    mle z (Fin.append (Fin.append rlo rhi) fun _ ↦ rtop) =
      (1 - rtop) * ∑ i, eq rlo (cube i) * mle (fun u' ↦ w (join i u')) rhi +
        rtop * mle pub (Fin.append rlo rhi) := by
  rw [mle_split, ← mle_split w rlo rhi, mle, mle, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [mle_fix0, mle_zero]
  simp only [fix0, hz]
  simp [dbl]
  ring

/-- **No division.** A claim that is false for the true value `t` and passes the check with the
value `v`, both against the same factor `A` (`W̃(r'')`, `M̃_ρ(r_x, r_y)`, `eq(τ, r_x)`, possibly
`0`), has `v ≠ t`. -/
theorem ne_of_claim {claim A v t : R} (hdoom : claim ≠ A * t) (hchk : claim = A * v) : v ≠ t :=
  fun h ↦ hdoom (h ▸ hchk)

end Tables

/-! ## The abstract R1CS -/

section R1CS

variable {E : Type*} [Field E] {a b : ℕ}

/-- `(M z)(x) = Σ_y M(x, y) · z(y)`. -/
def matVec (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Fin (2 ^ a) → E :=
  fun x ↦ ∑ y, M x y * z y

/-- `M̃(r_x, r_y) = Σ_{x, y} eq(r_x, x) · eq(r_y, y) · M(x, y)`. -/
def matMle (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (ry : Fin b → E) : E :=
  ∑ x, ∑ y, eq rx (cube x) * eq ry (cube y) * M x y

/-- The R1CS holds: `(Az)(x) · (Bz)(x) = (Cz)(x)` on the cube. -/
def Sat (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Prop :=
  ∀ x, matVec A z x * matVec B z x = matVec C z x

/-- The residual `F(x) = (Az)(x) · (Bz)(x) + (Cz)(x)` (characteristic two: `-` is `+`). -/
def residual (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Fin (2 ^ a) → E :=
  fun x ↦ matVec A z x * matVec B z x + matVec C z x

theorem matMle_cube (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (y : Fin (2 ^ b)) :
    matMle M rx (cube y) = ∑ x, eq rx (cube x) * M x y := by
  simp [matMle, eq_cube_cube]

/-- `(Mz)~(r_x) = Σ_y M̃(r_x, y) · z(y)`. -/
theorem mle_matVec (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) (rx : Fin a → E) :
    mle (matVec M z) rx = ∑ y, matMle M rx (cube y) * z y := by
  simp only [mle, matVec, matMle_cube, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The extension in `y` of `M̃(r_x, y)` on the cube is `M̃(r_x, ·)`. -/
theorem mle_matMle (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (ry : Fin b → E) :
    mle (fun y ↦ matMle M rx (cube y)) ry = matMle M rx ry := by
  simp only [mle, matMle_cube, Finset.mul_sum]
  rw [matMle, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem mle_comb {ℓ : ℕ} (p q s : Fin (2 ^ ℓ) → E) (ρ : E) (r : Fin ℓ → E) :
    mle (fun u ↦ p u + ρ * q u + ρ ^ 2 * s u) r = mle p r + ρ * mle q r + ρ ^ 2 * mle s r := by
  simp only [mle, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ### R1: the zerocheck coordinates -/

/-- **Start.** An unsatisfied R1CS has a nonzero residual table (`P_0 ≢ 0`). -/
theorem zc_start [CharP E 2] {A B C : Fin (2 ^ a) → Fin (2 ^ b) → E} {z : Fin (2 ^ b) → E}
    (h : ¬Sat A B C z) : tbl a (Array.ofFn (residual A B C z)) ≠ 0 := by
  rw [tbl_ofFn]
  intro hr
  refine h fun x ↦ ?_
  have := congrFun hr x
  simp only [residual, Pi.zero_apply] at this
  exact eq_of_sub_eq_zero (by rwa [CharTwo.sub_eq_add])

/-- **R1, one coordinate.** From a nonzero bound table (doomed), at most one value of the next
coordinate makes the bound table zero (escape). -/
theorem zc_escape_le [Fintype E] [DecidableEq E] (t : Array E) {m : ℕ}
    (ht : t.size = 2 ^ (m + 1)) (hd : tbl (m + 1) t ≠ 0) :
    (univ.filter fun c ↦ tbl m (bind0 t c) = 0).card ≤ 1 := by
  simp only [tbl_bind0 t _ ht]
  exact zerocheck_bad_le _ hd

/-- **End of R1.** With every coordinate drawn and the bound table still nonzero, `F̃(τ) ≠ 0`. -/
theorem zc_end (t : Array E) (τs : List E) (ht : t.size = 2 ^ τs.length)
    (hd : tbl 0 (bindT t τs) ≠ 0) : mle (tbl τs.length t) (pt τs) ≠ 0 := fun h ↦
  hd (funext fun u ↦ by rw [tbl_bindT t τs ht, h]; rfl)

/-! ### R2: the outer sumcheck -/

/-- The outer summand `eq(τ, x) · ((Az)(x) · (Bz)(x) + (Cz)(x))`, degree 3. -/
def outerExpr : Expr := .mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))

theorem outerExpr_deg : outerExpr.deg = 3 := rfl

/-- The outer tables: `eq(τ, ·)`, `Az`, `Bz`, `Cz`. -/
def outerTables (τs : List E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) :
    Array (Array E) :=
  #[eqTable τs, Array.ofFn (matVec A z), Array.ofFn (matVec B z), Array.ofFn (matVec C z)]

theorem outer_sizes (τs : List E) (hτ : τs.length = a) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) : ∀ t ∈ outerTables τs A B C z, t.size = 2 ^ a := by
  simp [outerTables, eqTable_size, hτ]

/-- The outer true sum is the zerocheck polynomial at `τ`: `Σ_x eq(τ, x) F(x) = F̃(τ)`. -/
theorem outer_trueSum (τs : List E) (hτ : τs.length = a) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) :
    trueSum outerExpr (outerTables τs A B C z) a = mle (residual A B C z) (ptOf a τs) := by
  simp only [trueSum, mle, outerTables, outerExpr, Expr.eval]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [tbl_ofFn, tbl_eqTable' τs hτ, residual]

/-- **Start of R2.** With `F̃(τ) ≠ 0` the outer claim `0` is false. -/
theorem outer_start (τs : List E) (hτ : τs.length = a) {A B C : Fin (2 ^ a) → Fin (2 ^ b) → E}
    {z : Fin (2 ^ b) → E} (h : mle (residual A B C z) (ptOf a τs) ≠ 0) :
    (0 : E) ≠ trueSum outerExpr (outerTables τs A B C z) a := by
  rw [outer_trueSum τs hτ]
  exact h.symm

/-- **End of R2.** All variables bound: the true value is
`eq(τ, r_x) · ((Az)~(r_x) · (Bz)~(r_x) + (Cz)~(r_x))`. -/
theorem outer_final (τs rx : List E) (hτ : τs.length = a) (hx : rx.length = a)
    (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) :
    trueSum outerExpr (bindAll (outerTables τs A B C z) rx) 0 =
      eq (ptOf a τs) (ptOf a rx) * (mle (matVec A z) (ptOf a rx) * mle (matVec B z) (ptOf a rx) +
        mle (matVec C z) (ptOf a rx)) := by
  subst hx
  rw [trueSum_bindAll _ _ _ (outer_sizes τs hτ A B C z)]
  simp only [outerExpr, Expr.eval, outerTables, ← pt_eq_ptOf]
  simp [tbl_ofFn, tbl_eqTable' τs hτ, mle_eqPt]

/-- **After R2.** A false final claim that passes the check has a wrong triple. -/
theorem triple_wrong {claim e vA vB vC tA tB tC : E} (hdoom : claim ≠ e * (tA * tB + tC))
    (hchk : claim = e * (vA * vB + vC)) : (vA, vB, vC) ≠ (tA, tB, tC) := by
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact hdoom hchk

/-! ### R3, R4: batching and the inner sumcheck -/

/-- The inner tables: `M̃_ρ(r_x, ·) = Ã + ρ B̃ + ρ² C̃` on the cube, and `z`. -/
def innerTables (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) : Array (Array E) :=
  #[Array.ofFn fun y ↦ matMle A rx (cube y) + ρ * matMle B rx (cube y) + ρ ^ 2 * matMle C rx (cube y),
    Array.ofFn z]

/-- The inner true sum is the batched true triple. -/
theorem inner_trueSum (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) :
    trueSum innerExpr (innerTables rx ρ A B C z) b =
      mle (matVec A z) rx + ρ * mle (matVec B z) rx + ρ ^ 2 * mle (matVec C z) rx := by
  rw [innerTables, prod_trueSum, mle_matVec, mle_matVec, mle_matVec, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **R3.** With a wrong triple, at most two `ρ` make the batched claim true. -/
theorem batch_escape_le [Fintype E] [DecidableEq E] (rx : Fin a → E)
    (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) {vA vB vC : E}
    (h : (vA, vB, vC) ≠ (mle (matVec A z) rx, mle (matVec B z) rx, mle (matVec C z) rx)) :
    (univ.filter fun ρ ↦
      vA + ρ * vB + ρ ^ 2 * vC = trueSum innerExpr (innerTables rx ρ A B C z) b).card ≤ 2 := by
  simp only [inner_trueSum]
  exact batch_bad_le h

/-- **End of R4.** All variables bound: the true value is `M̃_ρ(r_x, r_y) · z̃(r_y)`. -/
theorem inner_final (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) (ry : List E) (hy : ry.length = b) :
    trueSum innerExpr (bindAll (innerTables rx ρ A B C z) ry) 0 =
      (matMle A rx (ptOf b ry) + ρ * matMle B rx (ptOf b ry) + ρ ^ 2 * matMle C rx (ptOf b ry)) *
        mle z (ptOf b ry) := by
  subst hy
  rw [innerTables, trueSum_bindAll _ _ _ (prod_sizes _ _)]
  simp only [innerExpr, Expr.eval, ← pt_eq_ptOf]
  simp [tbl_ofFn, mle_comb, mle_matMle]

/-! ### R5, R6: ring switching and the weighted sumcheck -/

/-- The ring-switching doom after the coefficients `fs`: some `π_k ≠ 0`, `k < 2 ^ (s' + 1 - p)`,
of the family `δ` after the first `p = |fs|` stages. -/
def rsDoom {n : ℕ} (w δ : Fin n → E) (s' : ℕ) (fs : List E) : Prop :=
  ∃ k < 2 ^ (s' + 1 - fs.length), frobPair univ w (fun i ↦ frobMap (stages s' fs) (δ i)) k ≠ 0

/-- **Start of R5.** L-R1's conclusion (`ring_inj`, `ring_inj_EF`) is the doom before any
coefficient. -/
theorem rs_start {n : ℕ} (w δ : Fin n → E) (s' : ℕ)
    (h : ∃ k < 2 ^ (s' + 1), ∑ i, w i * δ i ^ 2 ^ k ≠ 0) : rsDoom w δ s' [] := h

open scoped Classical in
/-- **R5, one coefficient.** From a doomed state at most one coefficient escapes. -/
theorem rs_escape_le [CharP E 2] [Fintype E] [DecidableEq E] {n : ℕ} (w δ : Fin n → E)
    (s' : ℕ) (fs : List E) (hp : fs.length ≤ s') (h : rsDoom w δ s' fs) :
    (univ.filter fun f ↦ ¬rsDoom w δ s' (fs ++ [f])).card ≤ 1 := by
  convert stage_bad_le_one univ w δ s' fs hp h using 2
  ext f
  simp only [rsDoom, List.length_append, List.length_singleton, not_exists, not_and, not_not,
    Nat.add_sub_add_right, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **End of R5.** Doom after all `s' + 1` coefficients means the switched claim is false:
`T = Σ_i x^i Φ(s_i) ≠ Σ_u Φ(eq(r, u)) · q(u)` for the slices' errors `δ_i = s_i - Q̃_i(r)`. -/
theorem rs_end [CharP E 2] {K : Type*} [CommRing K] [Algebra K E] {n ℓ : ℕ} (x : K)
    (Q : Fin n → Fin (2 ^ ℓ) → K) (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (r : Fin ℓ → E)
    (s : Fin n → E) (s' : ℕ) (fs : List E) (hlen : fs.length = s' + 1)
    (h : rsDoom (fun i ↦ algebraMap K E (x ^ (i : ℕ)))
      (fun i ↦ s i - mle (fun u ↦ algebraMap K E (Q i u)) r) s' fs) :
    ∑ i : Fin n, algebraMap K E (x ^ (i : ℕ)) * Phi fs (s i) ≠
      ∑ u, Phi fs (eq r (cube u)) * algebraMap K E (∑ i : Fin n, Q i u * x ^ (i : ℕ)) := by
  obtain ⟨k, hk, hne⟩ := h
  rw [hlen, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hk
  subst hk
  have hPhi : Phi fs = frobMap (stages s' fs) := by rw [Phi, hlen, Nat.add_sub_cancel]
  intro heq
  apply hne
  have := ring_final (frobMapHom (stages s' fs)) x Q hQ r s
  simp only [frobMapHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← hPhi] at this ⊢
  rw [← this, heq, sub_self]

end R1CS

end SpartanChain
