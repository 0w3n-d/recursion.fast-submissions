import SpartanChainSumcheck
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Frobenius ring switching (blueprint §4.3, §9.4 L-R1 … L-R5)

The verifier draws `f_0 … f_{s'}` (`s' = 5` in R1) and applies the `F₂`-linear map
`Φ(a) = a_{s'+1}`, `a_{p+1} = a_p + f_p · a_p ^ 2 ^ M_p`, `M_p = 2 ^ (s' - p)`.

* Copied from leanerVM (Mathlib-only): the staged map `frobMap`, its Frobenius-sum form
  `frobMap_eq_sum` (**L-R5**), additivity, `frobPair` (`π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`),
  `frobPair_stage` and `card_stage_zero_le_one` (**L-R2**).
* `stages s' fs` (stage `p` has shift `2 ^ (s' - p)`), `Phi fs` (all stages), and the computable
  `phiApply` (squarings, no `npow`), `phiTable` (the `c_k`, built stage by stage), `target`
  (`T = Σ_i x^i · Φ(s_i)`), `weightTable` (the prover's `W(u') = Φ(eq(r, u'))`) and
  `weightEval` (`W̃(r'') = Σ_k c_k · eq(r ^ 2 ^ k, r'')`).
* **L-R1** `ring_inj`: a nonzero family `δ ∈ E^n` has some `Σ_i x^i · δ_i ^ 2 ^ k ≠ 0`, `k < n`,
  from the field facts as hypotheses (distinct conjugates of `x`, `|K| = 2^n`, `{1, y, y²}`
  spanning `E` over `K`, and the bases `{1, y^(2^k), y^(2^(k+1))}`); `ybasis_of_period` derives
  the last from the period of `E` and the independence of `{1, y, y²}`.
* **L-R2** `stage_bad_le_one`: the protocol form of `card_stage_zero_le_one`.
* **L-R3** `ring_complete`, and `ring_final`: the switched claim's error is `π_0` of `Φ(δ)`.
* **L-R4** `weight_mle`, and `mleEval_weightTable`: the verifier's `W̃` is the extension of the
  prover's table.
* **L-R5** `frobMap_eq_sum` (copied) and its dense form `Phi_eq_table`.
-/

namespace SpartanChain

open Finset

/-! ## The staged map (copied)

Copied from leanerVM, https://github.com/Verified-zkEVM/leanerVM, commit
`532ebb457a6bc95e9e9f3b442e17bb7d5a03e372`, file
`LeanerVM/Protocol/ToArkLib/Flock/FrobeniusMap.lean` (Apache-2.0): `frobMap`, `frobTerms`,
`frobMap_eq_sum`, `frobMap_append`, `frobMap_add`, `frobMap_zero`, `frobMapHom`, `frobPair`,
`frobPair_stage`, `card_frob_root_le_one`, `card_stage_zero_le_one`. Changes: the namespace, no
`module`/`public` (this repository does not use the module system). -/

section Copied

variable {R : Type*} [CommRing R]

/-- The staged map: each stage `(s, f)` sends `a` to `a + f · a ^ 2 ^ s`, in order. -/
def frobMap : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMap st (a + f * a ^ 2 ^ s)

/-- The terms `(c, e)` of the staged map as a sum of Frobenius powers `c · a ^ 2 ^ e`. -/
def frobTerms : List (ℕ × R) → List (R × ℕ)
  | [] => [(1, 0)]
  | (s, f) :: st => (frobTerms st).flatMap fun t ↦ [(t.1, t.2), (t.1 * f ^ 2 ^ t.2, s + t.2)]

variable [CharP R 2]

/-- **L-R5.** The staged map is the sum of its terms: `frobMap st a = Σ_{(c, e)} c · a ^ 2 ^ e`. -/
theorem frobMap_eq_sum (st : List (ℕ × R)) (a : R) :
    frobMap st a = ((frobTerms st).map fun t ↦ t.1 * a ^ 2 ^ t.2).sum := by
  induction st generalizing a with
  | nil => simp [frobMap, frobTerms]
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    rw [frobMap, ih, frobTerms]
    generalize frobTerms st = L
    induction L with
    | nil => simp
    | cons t L ihL =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, add_zero, ihL]
      rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
      ring

omit [CharP R 2] in
/-- Stages in sequence: the later list applies after the earlier. -/
theorem frobMap_append (st₁ st₂ : List (ℕ × R)) (a : R) :
    frobMap (st₁ ++ st₂) a = frobMap st₂ (frobMap st₁ a) := by
  induction st₁ generalizing a with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    exact ih _

/-- The staged map is additive. -/
theorem frobMap_add (st : List (ℕ × R)) (a b : R) :
    frobMap st (a + b) = frobMap st a + frobMap st b := by
  induction st generalizing a b with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [← ih, add_pow_char_pow]
    congr 1
    ring

omit [CharP R 2] in
/-- The staged map sends `0` to `0`. -/
theorem frobMap_zero (st : List (ℕ × R)) : frobMap st 0 = 0 := by
  induction st with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, add_zero, ih]

/-- The staged map as an additive homomorphism. -/
def frobMapHom (st : List (ℕ × R)) : R →+ R where
  toFun := frobMap st
  map_zero' := frobMap_zero st
  map_add' := frobMap_add st

omit [CharP R 2] in
/-- `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. -/
def frobPair {ι : Type*} (s : Finset ι) (w b : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, w i * b i ^ 2 ^ k

/-- One stage with shift `M` and coefficient `f` sends `π_k` to `π_k + f ^ 2 ^ k · π_{M + k}`. -/
theorem frobPair_stage {ι : Type*} (s : Finset ι) (w b : ι → R) (M : ℕ) (f : R) (k : ℕ) :
    frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k =
      frobPair s w b k + f ^ 2 ^ k * frobPair s w b (M + k) := by
  simp only [frobPair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
  ring

end Copied

section CopiedField

/-- `a + f ^ 2 ^ k · b = 0` with `(a, b) ≠ (0, 0)` has one root `f` at most, in a field of
characteristic two. -/
theorem card_frob_root_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    (k : ℕ) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun f : F ↦ a + f ^ 2 ^ k * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun f₁ h₁ f₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero] at h₁
    exact hab.elim (· h₁.2) (· rfl)
  have heq : f₁ ^ 2 ^ k = f₂ ^ 2 ^ k :=
    mul_right_cancel₀ hb (add_left_cancel (h₁.2.trans h₂.2.symm))
  exact iterateFrobenius_inj F 2 k heq

/-- **L-R2 (copied form). One bad coefficient at most.** If some `π_k`, `k < 2M`, of the family
is nonzero, then after one stage with shift `M` every `π_k`, `k < M`, vanishes for one coefficient
at most. -/
theorem card_stage_zero_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    {ι : Type*} (s : Finset ι) (w b : ι → F) (M : ℕ) (h : ∃ k < 2 * M, frobPair s w b k ≠ 0) :
    (Finset.univ.filter fun f : F ↦
      ∀ k < M, frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k = 0).card ≤ 1 := by
  obtain ⟨k₀, hk₀, hne⟩ := h
  -- The index below `M` whose pair of values is nonzero.
  obtain ⟨k, hk, hab⟩ : ∃ k < M, frobPair s w b k ≠ 0 ∨ frobPair s w b (M + k) ≠ 0 := by
    by_cases hlt : k₀ < M
    · exact ⟨k₀, hlt, Or.inl hne⟩
    · refine ⟨k₀ - M, by omega, Or.inr ?_⟩
      rwa [show M + (k₀ - M) = k₀ by omega]
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (card_frob_root_le_one k hab)
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← frobPair_stage]
  exact hf.2 k hk

end CopiedField

/-! ## The stages of `Φ` -/

variable {R : Type*} [CommRing R]

/-- The stages for the coefficients `fs`: stage `p` is `(2 ^ (s' - p), f_p)`. -/
def stages (s' : ℕ) (fs : List R) : List (ℕ × R) := fs.mapIdx fun p f ↦ (2 ^ (s' - p), f)

omit [CommRing R] in
theorem stages_cons (s' : ℕ) (f : R) (fs : List R) :
    stages s' (f :: fs) = (2 ^ s', f) :: stages (s' - 1) fs := by
  rw [stages, List.mapIdx_cons, stages]
  congr 1
  refine List.mapIdx_eq_mapIdx_iff.mpr fun i h ↦ ?_
  simp only [Prod.mk.injEq, and_true]
  rw [show s' - (i + 1) = s' - 1 - i by omega]

omit [CommRing R] in
/-- One more coefficient is one more stage, with shift `2 ^ (s' - p)`. -/
theorem stages_append (s' : ℕ) (fs : List R) (f : R) :
    stages s' (fs ++ [f]) = stages s' fs ++ [(2 ^ (s' - fs.length), f)] := by
  simp [stages, List.mapIdx_append]

/-- `Φ` for the coefficients `fs`: all `|fs|` stages, shifts `2 ^ (|fs| - 1), …, 2, 1`. -/
def Phi (fs : List R) : R → R := frobMap (stages (fs.length - 1) fs)

/-- With every coefficient zero, `Φ` is the identity (§10.1 positive control). -/
theorem frobMap_stages_zeros (s' m : ℕ) (a : R) :
    frobMap (stages s' (List.replicate m (0 : R))) a = a := by
  induction m generalizing s' with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, stages_cons, frobMap, zero_mul, add_zero, ih]

/-! ## Computable code -/

/-- `n` squarings: `a ^ 2 ^ n`. -/
def sqIter : ℕ → R → R
  | 0, a => a
  | n + 1, a => sqIter n (a * a)

theorem sqIter_eq (n : ℕ) (a : R) : sqIter n a = a ^ 2 ^ n := by
  induction n generalizing a with
  | zero => simp [sqIter]
  | succ n ih => rw [sqIter, ih, ← sq, ← pow_mul, pow_succ']

theorem sqIter_succ' (n : ℕ) (a : R) : sqIter (n + 1) a = sqIter n a * sqIter n a := by
  rw [sqIter_eq, sqIter_eq, ← sq, ← pow_mul, pow_succ]

/-- The staged map with squarings. -/
def frobMapC : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMapC st (a + f * sqIter s a)

theorem frobMapC_eq (st : List (ℕ × R)) (a : R) : frobMapC st a = frobMap st a := by
  induction st generalizing a with
  | nil => rfl
  | cons p st ih => obtain ⟨s, f⟩ := p; rw [frobMapC, frobMap, ih, sqIter_eq]

/-- `Φ(a)`, computed: `63` squarings and `6` multiplications for six stages. -/
def phiApply (fs : List R) (a : R) : R := frobMapC (stages (fs.length - 1) fs) a

theorem phiApply_eq (fs : List R) (a : R) : phiApply fs a = Phi fs a := frobMapC_eq _ _

/-- The coefficients `c_k` of `Φ(a) = Σ_k c_k · a ^ 2 ^ k`, `2 ^ |fs|` of them: the table of the
later stages, then the same table times `f ^ 2 ^ e`. -/
def phiTable : List R → Array R
  | [] => #[1]
  | f :: fs =>
    let t := phiTable fs
    t ++ Array.ofFn (n := t.size) fun e ↦ t[e] * sqIter e.val f

theorem phiTable_size (fs : List R) : (phiTable fs).size = 2 ^ fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [phiTable, ih, pow_succ, mul_two]

theorem getD_append (xs ys : Array R) (i : ℕ) :
    (xs ++ ys).getD i 0 = if i < xs.size then xs.getD i 0 else ys.getD (i - xs.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split_ifs <;> rfl

/-- **L-R5, dense form.** `Φ(a) = Σ_{k < 2^|fs|} c_k · a ^ 2 ^ k`. -/
theorem Phi_eq_table [CharP R 2] (fs : List R) (a : R) :
    Phi fs a = ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * a ^ 2 ^ k := by
  induction fs generalizing a with
  | nil => simp [Phi, stages, frobMap, phiTable]
  | cons f fs ih =>
    have hs := phiTable_size fs
    rw [Phi, List.length_cons, Nat.add_sub_cancel, stages_cons, frobMap, ← Phi, ih,
      pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    have hk' : k < (phiTable fs).size := hs ▸ hk
    rw [phiTable, getD_append, ite_eq_left hk', getD_append, ite_eq_right (by omega),
      Nat.sub_eq_of_eq_add (by omega : 2 ^ fs.length + k = k + (phiTable fs).size), getD_ofFn,
      dite_eq_left (by omega), add_pow_char_pow, mul_add, mul_pow,
      ← pow_mul, ← pow_add, sqIter_eq]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some,
      Fin.getElem_fin]
    ring

/-- The target `T = Σ_i x^i · Φ(s_i)` (Horner in `x`). -/
def target (x : R) (fs : List R) (s : Array R) : R := peval (s.map (phiApply fs)) x

theorem target_eq (x : R) (fs : List R) (s : Array R) :
    target x fs s = ∑ i ∈ range s.size, x ^ i * Phi fs (s.getD i 0) := by
  rw [target, peval_eq_sum, Array.size_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, phiApply_eq, mul_comm]

/-- The prover's weight table `W(u') = Φ(eq(r, u'))`. -/
def weightTable (fs r : List R) : Array R := (eqTable r).map (phiApply fs)

/-- `W̃(r'') = Σ_k c_k · eq(r ^ 2 ^ k, r'')`, the point squared once per `k`. -/
def weightEval (fs r r'' : List R) : R :=
  let c := phiTable fs
  (Nat.fold c.size (fun k _ (p : R × List R) ↦
    (p.1 + c.getD k 0 * eqPts p.2 r'', p.2.map fun a ↦ a * a)) (0, r)).1

theorem weightEval_fold (c : Array R) (r r'' : List R) (n : ℕ) :
    Nat.fold n (fun k _ (p : R × List R) ↦
      (p.1 + c.getD k 0 * eqPts p.2 r'', p.2.map fun a ↦ a * a)) (0, r) =
    (∑ k ∈ range n, c.getD k 0 * eqPts (r.map (sqIter k)) r'', r.map (sqIter n)) := by
  induction n with
  | zero => simp [sqIter]
  | succ n ih =>
    rw [Nat.fold_succ, ih, Finset.sum_range_succ, List.map_map]
    congr 2
    funext a
    simp [sqIter_succ']

theorem weightEval_eq (fs r r'' : List R) :
    weightEval fs r r'' =
      ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * eqPts (r.map (sqIter k)) r'' := by
  rw [weightEval, weightEval_fold, phiTable_size]

/-! ## L-R4: the weight's extension -/

/-- **L-R4.** `W̃(r'') = Σ_k c_k · eq(r ^ 2 ^ k, r'')` for `W(u) = Φ(eq(r, u))`. -/
theorem weight_mle [CharP R 2] {ℓ : ℕ} (fs : List R) (r r'' : Fin ℓ → R) :
    mle (fun u ↦ Phi fs (eq r (cube u))) r'' =
      ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * eq (fun l ↦ r l ^ 2 ^ k) r'' := by
  simp only [mle, Phi_eq_table, eq_frob, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eq_swap _ r'', ← eq_mle r'' (fun l ↦ r l ^ 2 ^ k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eq_swap (cube u) (fun l ↦ r l ^ 2 ^ k)]
  ring

/-- **The verifier's `W̃` is the extension of the prover's table** (points of length `ℓ`). -/
theorem mleEval_weightTable [CharP R 2] {ℓ : ℕ} (fs r r'' : List R) (hr : r.length = ℓ)
    (hr'' : r''.length = ℓ) : mleEval (weightTable fs r) r'' = weightEval fs r r'' := by
  have htbl : tbl ℓ (weightTable fs r) = fun u ↦ Phi fs (eq (ptOf ℓ r) (cube u)) := by
    funext u
    rw [← congrFun (tbl_eqTable' r hr) u, ← phiApply_eq]
    have hu : u.val < (eqTable r).size := by rw [eqTable_size, hr]; exact u.isLt
    simp [tbl, weightTable, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]
  rw [mleEval_eq' _ _ hr'', htbl, weight_mle, weightEval_eq]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eqPts_eq _ _ (by simp [hr]) hr'']
  congr 2
  funext l
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r[l.val]? <;> simp [sqIter_eq]

/-! ## L-R3: completeness, and the error of the switched claim -/

section Switch

variable {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]

/-- **L-R3.** For Boolean bit-planes `Q_i` packed as `q(u) = Σ_i Q_i(u) · x^i ∈ K` and any
additive `Φ`, `Σ_u Φ(eq(r, u)) · q(u) = Σ_i x^i · Φ(Q̃_i(r))`. -/
theorem ring_complete {n ℓ : ℕ} (Φ : E →+ E) (x : K) (Q : Fin n → Fin (2 ^ ℓ) → K)
    (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (r : Fin ℓ → E) :
    ∑ u, Φ (eq r (cube u)) * algebraMap K E (∑ i : Fin n, Q i u * x ^ (i : ℕ)) =
      ∑ i : Fin n, algebraMap K E (x ^ (i : ℕ)) * Φ (mle (fun u ↦ algebraMap K E (Q i u)) r) := by
  have hbit : ∀ i u, Φ (eq r (cube u) * algebraMap K E (Q i u)) =
      algebraMap K E (Q i u) * Φ (eq r (cube u)) := fun i u ↦ by
    rcases hQ i u with h | h <;> simp [h]
  simp only [mle, map_sum, hbit, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The switched claim's error.** `T - Σ_u Φ(eq(r, u)) · q(u)` is `π_0` of the family
`Φ(s_i - Q̃_i(r))` with weights `x^i`: the claim handed on is true exactly when this `π_0`
vanishes (the end of the six stages). -/
theorem ring_final {n ℓ : ℕ} (Φ : E →+ E) (x : K) (Q : Fin n → Fin (2 ^ ℓ) → K)
    (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (r : Fin ℓ → E) (s : Fin n → E) :
    (∑ i : Fin n, algebraMap K E (x ^ (i : ℕ)) * Φ (s i)) -
        ∑ u, Φ (eq r (cube u)) * algebraMap K E (∑ i : Fin n, Q i u * x ^ (i : ℕ)) =
      frobPair univ (fun i : Fin n ↦ algebraMap K E (x ^ (i : ℕ)))
        (fun i ↦ Φ (s i - mle (fun u ↦ algebraMap K E (Q i u)) r)) 0 := by
  rw [ring_complete Φ x Q hQ r, ← Finset.sum_sub_distrib, frobPair]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pow_zero, pow_one, map_sub, mul_sub]

end Switch

/-! ## L-R2: one stage at a time -/

/-- **L-R2 (protocol form).** After `p = |fs| ≤ s'` coefficients, a family with some
`π_k ≠ 0`, `k < 2 ^ (s' + 1 - p)`, keeps some `π_k ≠ 0`, `k < 2 ^ (s' - p)`, after the next
coefficient `f`, for every `f` but at most one. -/
theorem stage_bad_le_one {E : Type*} [Field E] [Fintype E] [DecidableEq E] [CharP E 2]
    {ι : Type*} (s : Finset ι) (w δ : ι → E) (s' : ℕ) (fs : List E) (hp : fs.length ≤ s')
    (h : ∃ k < 2 ^ (s' + 1 - fs.length),
      frobPair s w (fun i ↦ frobMap (stages s' fs) (δ i)) k ≠ 0) :
    (univ.filter fun f ↦ ∀ k < 2 ^ (s' - fs.length),
      frobPair s w (fun i ↦ frobMap (stages s' (fs ++ [f])) (δ i)) k = 0).card ≤ 1 := by
  have h2 : 2 ^ (s' + 1 - fs.length) = 2 * 2 ^ (s' - fs.length) := by
    rw [show s' + 1 - fs.length = (s' - fs.length) + 1 by omega, pow_succ, mul_comm]
  rw [h2] at h
  refine le_of_eq_of_le ?_ (card_stage_zero_le_one s w _ _ h)
  congr 1
  refine Finset.filter_congr fun f _ ↦ ?_
  simp only [stages_append, frobMap_append, frobMap]

/-! ## L-R1: injectivity of ring switching -/

/-- The `K` half of L-R1 (Annex A §A.3): with the `n` conjugates `x ^ 2 ^ m` distinct and
`|K| = 2 ^ n`, a family `d ∈ K^n` with `Σ_i x^i · d_i ^ 2 ^ k = 0` for every `k < n` is zero
(Vandermonde in the conjugates). -/
theorem frob_sums_eq_zero {K : Type*} [Field K] [CharP K 2] {n : ℕ} (x : K)
    (hconj : ((List.range n).map fun k ↦ x ^ 2 ^ k).Nodup) (hK : ∀ a : K, a ^ 2 ^ n = a)
    (d : Fin n → K) (h : ∀ k < n, ∑ i : Fin n, x ^ (i : ℕ) * d i ^ 2 ^ k = 0) : d = 0 := by
  have hinj : Function.Injective fun m : Fin n ↦ x ^ 2 ^ (m : ℕ) := fun a b hab ↦
    Fin.ext (List.inj_on_of_nodup_map hconj (List.mem_range.mpr a.isLt)
      (List.mem_range.mpr b.isLt) hab)
  refine Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj fun m ↦ ?_
  by_cases hm : (m : ℕ) = 0
  · simpa [hm] using h 0 (by omega)
  have hk := congrArg (· ^ 2 ^ (m : ℕ)) (h (n - m) (by omega))
  simp only [zero_pow (pow_ne_zero _ two_ne_zero), sum_pow_char_pow] at hk
  rw [← hk]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ (m : ℕ)) (i : ℕ), ← pow_mul (d i), ← pow_add,
    Nat.sub_add_cancel m.isLt.le, hK]

/-- **L-R1.** A nonzero family `δ ∈ E^n` has `Σ_i x^i · δ_i ^ 2 ^ k ≠ 0` for some `k < n`.
Hypotheses (the facts of the word-level field): the conjugates `x ^ 2 ^ k`, `k < n`, are distinct
(`conj_distinct`), `|K| = 2^n` (as `a ^ 2 ^ n = a`), `E = K + K y + K y²`, and for every `k < n`
the family `1, y ^ 2 ^ k, y ^ 2 ^ (k + 1)` is `K`-independent (`ybasis`). -/
theorem ring_inj {K E : Type*} [Field K] [Field E] [Algebra K E] [CharP K 2] [CharP E 2] {n : ℕ}
    (x : K) (hconj : ((List.range n).map fun k ↦ x ^ 2 ^ k).Nodup) (hK : ∀ a : K, a ^ 2 ^ n = a)
    (y : E) (hspan : ∀ e : E, ∃ a b c : K,
      e = algebraMap K E a + algebraMap K E b * y + algebraMap K E c * y ^ 2)
    (hbasis : ∀ k < n, ∀ a b c : K, algebraMap K E a + algebraMap K E b * y ^ 2 ^ k +
      algebraMap K E c * y ^ 2 ^ (k + 1) = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (δ : Fin n → E) (hδ : δ ≠ 0) :
    ∃ k < n, ∑ i : Fin n, algebraMap K E (x ^ (i : ℕ)) * δ i ^ 2 ^ k ≠ 0 := by
  by_contra hall
  push Not at hall
  choose a b c habc using fun i ↦ hspan (δ i)
  have hsplit : ∀ k < n, (∑ i : Fin n, x ^ (i : ℕ) * a i ^ 2 ^ k) = 0 ∧
      (∑ i : Fin n, x ^ (i : ℕ) * b i ^ 2 ^ k) = 0 ∧
      (∑ i : Fin n, x ^ (i : ℕ) * c i ^ 2 ^ k) = 0 := by
    intro k hk
    refine hbasis k hk _ _ _ ?_
    rw [← hall k hk]
    simp only [map_sum, map_mul, map_pow, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [habc i, add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, ← pow_mul y 2, ← pow_succ']
    ring
  have ha := frob_sums_eq_zero x hconj hK a fun k hk ↦ (hsplit k hk).1
  have hb := frob_sums_eq_zero x hconj hK b fun k hk ↦ (hsplit k hk).2.1
  have hc := frob_sums_eq_zero x hconj hK c fun k hk ↦ (hsplit k hk).2.2
  refine hδ (funext fun i ↦ ?_)
  rw [habc i, congrFun ha i, congrFun hb i, congrFun hc i]
  simp

/-- `ybasis` from the period of `E`: if `e ^ 2 ^ N = e` on `E` and `1, y, y²` are
`K`-independent, then so are `1, y ^ 2 ^ k, y ^ 2 ^ (k + 1)` for every `k ≤ N` (apply
`(·) ^ 2 ^ (N - k)`, a ring map fixing `y`'s orbit back to `y`). -/
theorem ybasis_of_period {K E : Type*} [Field K] [Field E] [Algebra K E] [CharP E 2] {N : ℕ}
    (hE : ∀ e : E, e ^ 2 ^ N = e) (y : E)
    (hind : ∀ a b c : K, algebraMap K E a + algebraMap K E b * y + algebraMap K E c * y ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0)
    (k : ℕ) (hk : k ≤ N) (a b c : K)
    (h : algebraMap K E a + algebraMap K E b * y ^ 2 ^ k + algebraMap K E c * y ^ 2 ^ (k + 1) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hp := congrArg (· ^ 2 ^ (N - k)) h
  simp only [zero_pow (pow_ne_zero _ two_ne_zero)] at hp
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_add,
    ← pow_add, Nat.add_sub_cancel' hk, show k + 1 + (N - k) = N + 1 by omega, pow_succ, pow_mul,
    hE, ← map_pow, ← map_pow, ← map_pow] at hp
  obtain ⟨ha, hb, hc⟩ := hind _ _ _ hp
  have h0 : 2 ^ (N - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  exact ⟨pow_eq_zero_iff h0 |>.mp ha, pow_eq_zero_iff h0 |>.mp hb, pow_eq_zero_iff h0 |>.mp hc⟩

end SpartanChain
