import Mathlib.Algebra.Polynomial.Roots
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-!
# The Reed–Solomon code of the Ligero PCS (blueprint §5.1, L-RS1, L-RS5)

Generic over a field `K` (the code's coordinates and evaluation points) and a field `E` with
`[Algebra K E]` (the messages of the proximity and evaluation tests). The protocol instantiates
`K := F`, `E := EF` and the domain `ω c := ` the element of `F` whose word is `c`.

* `W κ i` are the unnormalised subspace polynomials `W_0 = X`, `W_{i+1} = W_i (W_i + κ_i)`;
  `wVal` evaluates them by the same recursion on values. They are monic of degree `2^i` for
  **every** choice of the constants `κ`; `kappaArr` is the choice of §5.1 (`κ_i = W_i(ω_{2^i})`),
  which matters only for the native prover's additive NTT, never for soundness.
* `basisPoly κ ℓ j = ∏_{i<ℓ} W_i^{bit_i j}` is monic of degree `j` for `j < 2^ℓ` (`basis_deg`).
* `enc κ ℓ ω msg c = Σ_j X_j(ω_c) · msg_j` is the encoding `E^{2^ℓ} → E^ι`, `encL` the same as an
  `E`-linear map, `rsCode` its range. `code_dist` (L-RS1) is the minimum distance
  `|ι| − 2^ℓ + 1`; `rsCode_kRational` says the code is defined over `K`.
* `tensor`, `encAt`: the verifier's computation of one coordinate (the tensor of the `W_i(ω)` in
  `2^ℓ − 1` multiplications, then a dot product), proved equal to `enc` (`encAt_eq`, L-RS5).
-/

namespace SpartanChain.RS

open Polynomial Finset

section Bits

variable {R : Type*} [CommMonoid R]

/-- `∏_{i<ℓ} f_i^{bit_i j}`. -/
def bitProd (f : ℕ → R) (ℓ j : ℕ) : R := ∏ i ∈ range ℓ, if j.testBit i then f i else 1

theorem bitProd_succ_lo (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) j = bitProd f ℓ j := by
  simp [bitProd, prod_range_succ, Nat.testBit_lt_two_pow hj]

theorem bitProd_succ_hi (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) (2 ^ ℓ + j) = bitProd f ℓ j * f ℓ := by
  simp only [bitProd, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj,
    Bool.not_false, ite_true]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

/-- Induction on `ℓ` for statements about `j < 2^ℓ`, splitting off the top bit. -/
theorem bit_induction {P : ℕ → ℕ → Prop} (h0 : P 0 0)
    (hlo : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) j)
    (hhi : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) (2 ^ ℓ + j)) : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j := by
  intro ℓ
  induction ℓ with
  | zero => intro j hj; obtain rfl : j = 0 := by simpa using hj
            exact h0
  | succ ℓ ih =>
    intro j hj
    by_cases hlt : j < 2 ^ ℓ
    · exact hlo ℓ j hlt (ih j hlt)
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
      have : j' < 2 ^ ℓ := by rw [pow_succ] at hj; omega
      exact hhi ℓ j' this (ih j' this)

end Bits

section Basis

variable {K : Type*} [Field K]

/-- The unnormalised subspace polynomials: `W_0 = X`, `W_{i+1} = W_i · (W_i + κ_i)` (§5.1). -/
noncomputable def W (κ : ℕ → K) : ℕ → K[X]
  | 0 => X
  | i + 1 => W κ i * (W κ i + C (κ i))

/-- `W_i(a)` by the recursion on values (`i` multiplications). -/
def wVal (κ : ℕ → K) : ℕ → K → K
  | 0, a => a
  | i + 1, a => let w := wVal κ i a; w * (w + κ i)

theorem wVal_eq (κ : ℕ → K) (i : ℕ) (a : K) : wVal κ i a = (W κ i).eval a := by
  induction i with
  | zero => simp [wVal, W]
  | succ i ih => simp [wVal, W, ih]

/-- `W_i` is monic of degree `2^i`, whatever the constants `κ`. -/
theorem W_monic (κ : ℕ → K) (i : ℕ) : (W κ i).Monic ∧ (W κ i).natDegree = 2 ^ i := by
  induction i with
  | zero => simp [W]
  | succ i ih =>
    obtain ⟨hm, hd⟩ := ih
    have hpos : 0 < (W κ i).degree := by
      rw [← natDegree_pos_iff_degree_pos, hd]; positivity
    have hm' : (W κ i + C (κ i)).Monic := hm.add_of_left (degree_C_le.trans_lt hpos)
    refine ⟨hm.mul hm', ?_⟩
    rw [W, hm.natDegree_mul hm', natDegree_add_C, hd, pow_succ]; ring

/-- `κ_0, …, κ_{ℓ-1}` with `κ_i = W_i(pt i)`, `W_i` built from the earlier constants. With
`pt i = ω_{2^i}` this is §5.1's choice. Any constants give the same code properties. -/
def kappaArr (pt : ℕ → K) : ℕ → Array K
  | 0 => #[]
  | i + 1 => let ks := kappaArr pt i; ks.push (wVal (fun j => ks.getD j 0) i (pt i))

/-- The basis polynomial `X_j = ∏_{i<ℓ} W_i^{bit_i j}`. -/
noncomputable def basisPoly (κ : ℕ → K) (ℓ j : ℕ) : K[X] := bitProd (W κ) ℓ j

/-- `X_j(a)` from the values `W_i(a)`. -/
def basisVal (κ : ℕ → K) (ℓ j : ℕ) (a : K) : K := bitProd (fun i => wVal κ i a) ℓ j

theorem basisVal_eq (κ : ℕ → K) (ℓ j : ℕ) (a : K) :
    basisVal κ ℓ j a = (basisPoly κ ℓ j).eval a := by
  simp only [basisVal, basisPoly, bitProd, eval_prod]
  exact prod_congr rfl fun i _ => by split_ifs <;> simp [wVal_eq]

/-- **`basis_deg`**: `X_j` is monic of degree `j` for `j < 2^ℓ`. -/
theorem basis_deg (κ : ℕ → K) :
    ∀ ℓ j, j < 2 ^ ℓ → (basisPoly κ ℓ j).Monic ∧ (basisPoly κ ℓ j).natDegree = j := by
  apply bit_induction
  · simp [basisPoly, bitProd]
  · intro ℓ j hj ih; rwa [basisPoly, bitProd_succ_lo _ hj]
  · intro ℓ j hj ih
    obtain ⟨hm, hd⟩ := ih
    obtain ⟨hWm, hWd⟩ := W_monic κ ℓ
    rw [basisPoly, bitProd_succ_hi _ hj, ← basisPoly]
    exact ⟨hm.mul hWm, by rw [hm.natDegree_mul hWm, hd, hWd, add_comm]⟩

end Basis

section Code

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {ι : Type*}

/-- **Encoding** `Enc(msg)_c = Σ_{j<2^ℓ} X_j(ω_c) · msg_j` (§5.1). -/
def enc (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (msg : Fin (2 ^ ℓ) → E) (c : ι) : E :=
  ∑ j : Fin (2 ^ ℓ), algebraMap K E (basisVal κ ℓ j (ω c)) * msg j

/-- `Enc` as an `E`-linear map. -/
def encL (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) : (Fin (2 ^ ℓ) → E) →ₗ[E] (ι → E) where
  toFun := enc κ ℓ ω
  map_add' x y := by funext c; simp [enc, mul_add, sum_add_distrib]
  map_smul' r x := by funext c; simp [enc, mul_sum, mul_left_comm]

/-- The code `C = {Enc(msg)}`, an `E`-subspace of `E^ι`. -/
def rsCode (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) : Submodule E (ι → E) :=
  LinearMap.range (encL κ ℓ ω)

theorem mem_rsCode {κ : ℕ → K} {ℓ : ℕ} {ω : ι → K} {c : ι → E} :
    c ∈ rsCode κ ℓ ω ↔ ∃ msg, enc κ ℓ ω msg = c := Iff.rfl

theorem enc_mem_rsCode (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (msg : Fin (2 ^ ℓ) → E) :
    enc κ ℓ ω msg ∈ rsCode κ ℓ ω := ⟨msg, rfl⟩

/-- **L-RS5** (linearity): `Enc(Σ_i r_i Q_i) = Σ_i r_i Enc(Q_i)`. -/
theorem encode_complete (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) {m : ℕ} (r : Fin m → E)
    (Q : Fin m → Fin (2 ^ ℓ) → E) :
    enc κ ℓ ω (∑ i, r i • Q i) = ∑ i, r i • enc κ ℓ ω (Q i) := by
  change encL κ ℓ ω _ = ∑ i, r i • encL κ ℓ ω (Q i)
  simp [map_sum, map_smul]

/-- `K`-rows encode to `K`-rows: `Enc_E(ι_K ∘ q) = ι_K ∘ Enc_K(q)`. -/
theorem enc_algebraMap (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (q : Fin (2 ^ ℓ) → K) (c : ι) :
    enc κ ℓ ω (fun j => algebraMap K E (q j)) c = algebraMap K E (enc κ ℓ ω q c) := by
  simp [enc, map_sum, map_mul]

/-- A `K`-linear map applied coordinatewise commutes with `Enc`. -/
theorem enc_linearMap (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (π : E →ₗ[K] E)
    (msg : Fin (2 ^ ℓ) → E) (c : ι) : π (enc κ ℓ ω msg c) = enc κ ℓ ω (fun j => π (msg j)) c := by
  simp [enc, map_sum, ← Algebra.smul_def, map_smul]

/-- `C` is defined over `K`: closed under every `K`-linear map applied coordinatewise. -/
def KRational (K : Type*) [Field K] [Algebra K E] (C : Submodule E (ι → E)) : Prop :=
  ∀ π : E →ₗ[K] E, ∀ c ∈ C, (fun x => π (c x)) ∈ C

theorem rsCode_kRational (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) :
    KRational K (rsCode (E := E) κ ℓ ω) := by
  rintro π _ ⟨msg, rfl⟩
  exact ⟨fun j => π (msg j), funext fun c => (enc_linearMap κ ℓ ω π msg c).symm⟩

/-- The polynomial `Σ_j msg_j X_j ∈ E[X]` that `Enc(msg)` evaluates. -/
noncomputable def encPoly (κ : ℕ → K) (ℓ : ℕ) (msg : Fin (2 ^ ℓ) → E) : E[X] :=
  ∑ j : Fin (2 ^ ℓ), C (msg j) * (basisPoly κ ℓ j).map (algebraMap K E)

theorem encPoly_eval (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (msg : Fin (2 ^ ℓ) → E) (c : ι) :
    (encPoly κ ℓ msg).eval (algebraMap K E (ω c)) = enc κ ℓ ω msg c := by
  simp only [encPoly, enc, eval_finsetSum, eval_mul, eval_C, eval_map, eval₂_at_apply,
    basisVal_eq]
  exact sum_congr rfl fun _ _ => mul_comm _ _

theorem encPoly_natDegree_lt (κ : ℕ → K) (ℓ : ℕ) (msg : Fin (2 ^ ℓ) → E) :
    (encPoly κ ℓ msg).natDegree < 2 ^ ℓ := by
  have h := natDegree_sum_le_of_forall_le univ
    (fun j : Fin (2 ^ ℓ) => C (msg j) * (basisPoly κ ℓ j).map (algebraMap K E))
    (n := 2 ^ ℓ - 1) fun j _ => by
      refine (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans ?_)
      rw [(basis_deg κ ℓ j j.2).2]; omega
  have : 0 < 2 ^ ℓ := by positivity
  exact lt_of_le_of_lt h (by omega)

/-- `Σ_j msg_j X_j ≠ 0` for `msg ≠ 0`: the coefficient at the top nonzero index is `msg_j`. -/
theorem encPoly_ne_zero (κ : ℕ → K) (ℓ : ℕ) {msg : Fin (2 ^ ℓ) → E} (h : msg ≠ 0) :
    encPoly κ ℓ msg ≠ 0 := by
  classical
  have hne : (univ.filter fun j => msg j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h; exact ⟨j, by simpa using hj⟩
  set t := (univ.filter fun j => msg j ≠ 0).max' hne
  have ht : msg t ≠ 0 := by simpa using (univ.filter fun j => msg j ≠ 0).max'_mem hne
  intro h0
  have hc := congrArg (fun p => p.coeff t) h0
  simp only [encPoly, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at hc
  rw [sum_eq_single t] at hc
  · have h1 := (basis_deg κ ℓ t t.2).1.coeff_natDegree
    rw [(basis_deg κ ℓ t t.2).2] at h1
    simp [h1, ht] at hc
  · intro j _ hjt
    by_cases hj : msg j = 0
    · simp [hj]
    · have hle : j ≤ t := le_max' _ _ (by simpa using hj)
      have hlt : (j : ℕ) < t := lt_of_le_of_ne hle (fun e => hjt (Fin.ext e))
      rw [coeff_eq_zero_of_natDegree_lt (by rw [(basis_deg κ ℓ j j.2).2]; exact hlt)]
      simp
  · simp

theorem encPoly_add (κ : ℕ → K) (ℓ : ℕ) (msg msg' : Fin (2 ^ ℓ) → E) :
    encPoly κ ℓ (msg + msg') = encPoly κ ℓ msg + encPoly κ ℓ msg' := by
  simp [encPoly, add_mul, sum_add_distrib]

theorem encPoly_single (κ : ℕ → K) (ℓ : ℕ) (t : Fin (2 ^ ℓ)) (a : E) :
    encPoly κ ℓ (Pi.single t a) = C a * (basisPoly κ ℓ t).map (algebraMap K E) := by
  classical
  rw [encPoly, sum_eq_single t (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- Every polynomial of degree `< 2^ℓ` is `Σ_j msg_j X_j` (the `X_j` span `E[X]_{<2^ℓ}`). -/
theorem exists_encPoly (κ : ℕ → K) (ℓ : ℕ) :
    ∀ n, n < 2 ^ ℓ → ∀ p : E[X], p.natDegree ≤ n → ∃ msg, encPoly κ ℓ msg = p := by
  intro n
  induction n with
  | zero =>
    intro h0 p hp
    refine ⟨Pi.single ⟨0, h0⟩ (p.coeff 0), ?_⟩
    rw [encPoly_single, eq_C_of_natDegree_le_zero hp]
    simp [basisPoly, bitProd]
  | succ n ih =>
    intro hn p hp
    set t : Fin (2 ^ ℓ) := ⟨n + 1, hn⟩
    obtain ⟨hm, hd⟩ := basis_deg κ ℓ t t.2
    set q := p - C (p.coeff (n + 1)) * (basisPoly κ ℓ t).map (algebraMap K E)
    have hq : q.natDegree ≤ n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [q, coeff_sub, coeff_C_mul, coeff_map]
      rcases Nat.lt_or_ge (n + 1) N with h | h
      · have h1 : p.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt h)
        have h2 : (basisPoly κ ℓ t).coeff N = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact h)
        simp [h1, h2]
      · obtain rfl : N = n + 1 := by omega
        have h1 := hm.coeff_natDegree
        rw [hd] at h1
        simp [t, h1]
    obtain ⟨msg, hmsg⟩ := ih (by omega) q hq
    refine ⟨msg + Pi.single t (p.coeff (n + 1)), ?_⟩
    rw [encPoly_add, hmsg, encPoly_single]
    simp [q]

/-- The code is the Reed–Solomon code: the evaluations at the points `ω` of the polynomials
of degree `< 2^ℓ` over `E`. -/
theorem mem_rsCode_iff (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (c : ι → E) :
    c ∈ rsCode κ ℓ ω ↔
      ∃ p : E[X], p.natDegree < 2 ^ ℓ ∧ c = fun x => p.eval (algebraMap K E (ω x)) := by
  constructor
  · rintro ⟨msg, rfl⟩
    exact ⟨encPoly κ ℓ msg, encPoly_natDegree_lt κ ℓ msg,
      funext fun x => (encPoly_eval κ ℓ ω msg x).symm⟩
  · rintro ⟨p, hp, rfl⟩
    have : 0 < 2 ^ ℓ := by positivity
    obtain ⟨msg, rfl⟩ := exists_encPoly κ ℓ (2 ^ ℓ - 1) (by omega) p (by omega)
    exact ⟨msg, funext fun x => (encPoly_eval κ ℓ ω msg x).symm⟩

omit [Algebra K E] in
/-- A `K`-linear projection of `E` onto the image of `K`. -/
theorem exists_proj [Algebra K E] : ∃ π : E →ₗ[K] E,
    (∀ y, π y ∈ Set.range (algebraMap K E)) ∧ ∀ a, π (algebraMap K E a) = algebraMap K E a := by
  let p : Submodule K E := LinearMap.range (Algebra.linearMap K E)
  obtain ⟨q, hpq⟩ := p.exists_isCompl
  refine ⟨p.subtype ∘ₗ p.projectionOnto q hpq, fun y => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := (p.projectionOnto q hpq y).2
    exact ⟨a, by simpa using ha⟩
  · have := Submodule.projectionOnto_apply_left hpq ⟨algebraMap K E a, ⟨a, rfl⟩⟩
    simp [this]

end Code

section Distance

variable {E : Type*} [Field E] [DecidableEq E] {ι : Type*} [Fintype ι]

/-- `C` has minimum distance at least `d`: every nonzero codeword has weight `≥ d`. -/
def MinDist (C : Submodule E (ι → E)) (d : ℕ) : Prop := ∀ c ∈ C, c ≠ 0 → d ≤ hammingNorm c

theorem MinDist.le_dist {C : Submodule E (ι → E)} {d : ℕ} (hC : MinDist C d) {c c' : ι → E}
    (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') : d ≤ hammingDist c c' := by
  rw [hammingDist_eq_hammingNorm]
  exact hC _ (C.add_mem (C.neg_mem hc) hc') (by
    intro h; exact hne (by simpa [neg_add_eq_zero] using h))

/-- Two codewords that agree outside fewer than `d` positions are equal. -/
theorem MinDist.eq_of_agree {C : Submodule E (ι → E)} {d : ℕ} (hC : MinDist C d) {c c' : ι → E}
    (hc : c ∈ C) (hc' : c' ∈ C) (T : Finset ι) (hT : T.card < d) (h : ∀ x ∉ T, c x = c' x) :
    c = c' := by
  classical
  by_contra hne
  have h1 := hC.le_dist hc hc' hne
  have h2 : hammingDist c c' ≤ T.card := by
    unfold hammingDist
    exact card_le_card fun x hx => by
      by_contra hxT; exact (mem_filter.1 hx).2 (h x hxT)
  omega

variable {K : Type*} [Field K] [Algebra K E]

/-- **L-RS1 `code_dist`**: for distinct points the code has minimum distance `|ι| − 2^ℓ + 1`. -/
theorem code_dist (κ : ℕ → K) (ℓ : ℕ) {ω : ι → K} (hω : Function.Injective ω) :
    MinDist (rsCode (E := E) κ ℓ ω) (Fintype.card ι - 2 ^ ℓ + 1) := by
  classical
  rintro _ ⟨msg, rfl⟩ hc
  have hmsg : msg ≠ 0 := by
    rintro rfl; exact hc (map_zero _)
  change enc κ ℓ ω msg ≠ 0 at hc
  change Fintype.card ι - 2 ^ ℓ + 1 ≤ hammingNorm (enc κ ℓ ω msg)
  by_contra hlt
  set c := enc κ ℓ ω msg
  let Z := univ.filter fun x => c x = 0
  have hsplit : Z.card + hammingNorm c = Fintype.card ι := by
    unfold hammingNorm; exact card_filter_add_card_filter_not (s := univ) _
  have hpos : 0 < hammingNorm c := hammingNorm_pos_iff.2 hc
  have hZ : 2 ^ ℓ ≤ Z.card := by omega
  apply encPoly_ne_zero κ ℓ hmsg
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (f := fun z : Z => algebraMap K E (ω z))
  · intro a b hab
    exact Subtype.ext (hω ((algebraMap K E).injective hab))
  · intro z; rw [encPoly_eval]; exact (mem_filter.1 z.2).2
  · rw [Fintype.card_coe]; exact (encPoly_natDegree_lt κ ℓ msg).trans_le hZ

/-- `Enc` is injective when there are at least `2^ℓ` distinct points. -/
theorem enc_injective (κ : ℕ → K) (ℓ : ℕ) {ω : ι → K} (hω : Function.Injective ω)
    (hk : 2 ^ ℓ ≤ Fintype.card ι) : Function.Injective (enc (E := E) κ ℓ ω) := by
  change Function.Injective (encL κ ℓ ω)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro msg h0
  by_contra hmsg
  apply encPoly_ne_zero κ ℓ hmsg
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (f := fun x : ι => algebraMap K E (ω x)) (fun a b hab => hω ((algebraMap K E).injective hab))
  · intro x; rw [encPoly_eval]; exact congrFun h0 x
  · exact (encPoly_natDegree_lt κ ℓ msg).trans_le hk

/-- A codeword with entries in `K` has its message in `K` (enough points). -/
theorem msg_in_K (κ : ℕ → K) (ℓ : ℕ) {ω : ι → K} (hω : Function.Injective ω)
    (hk : 2 ^ ℓ ≤ Fintype.card ι) {msg : Fin (2 ^ ℓ) → E}
    (h : ∀ x, enc κ ℓ ω msg x ∈ Set.range (algebraMap K E)) :
    ∀ j, msg j ∈ Set.range (algebraMap K E) := by
  obtain ⟨π, hπ, hfix⟩ := exists_proj (K := K) (E := E)
  have heq : (fun j => π (msg j)) = msg := enc_injective κ ℓ hω hk <| funext fun x => by
    rw [← enc_linearMap]; obtain ⟨a, ha⟩ := h x; rw [← ha, hfix]
  intro j; rw [← congrFun heq j]; exact hπ _

end Distance

section Tensor

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]

/-- `(tensor, W_ℓ(a))`: the tensor `(X_j(a))_{j<2^ℓ}` built bit by bit (`2^ℓ − 1`
multiplications), together with the next `W` value. -/
def tensorAux (κ : ℕ → K) (a : K) : ℕ → Array K × K
  | 0 => (#[1], a)
  | ℓ + 1 =>
    let p := tensorAux κ a ℓ
    (p.1 ++ p.1.map (· * p.2), p.2 * (p.2 + κ ℓ))

/-- The tensor `(X_j(a))_{j<2^ℓ}`. -/
def tensor (κ : ℕ → K) (ℓ : ℕ) (a : K) : Array K := (tensorAux κ a ℓ).1

/-- One coordinate of the encoding, as the verifier computes it: the tensor at `a`, then the
dot product with the message (`msg` is read with default `0`). -/
def encAt (κ : ℕ → K) (ℓ : ℕ) (msg : Array E) (a : K) : E :=
  let t := tensor κ ℓ a
  Fin.foldl (2 ^ ℓ) (fun acc j => acc + t.getD j 0 • msg.getD j 0) 0

theorem tensorAux_snd (κ : ℕ → K) (a : K) (ℓ : ℕ) : (tensorAux κ a ℓ).2 = wVal κ ℓ a := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [tensorAux, wVal, ih]

theorem tensor_size (κ : ℕ → K) (ℓ : ℕ) (a : K) : (tensor κ ℓ a).size = 2 ^ ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [tensor, tensorAux] at ih ⊢; rw [ih, pow_succ]; ring

theorem tensor_getD (κ : ℕ → K) (a : K) :
    ∀ ℓ j, j < 2 ^ ℓ → (tensor κ ℓ a).getD j 0 = basisVal κ ℓ j a := by
  apply bit_induction
  · rfl
  · intro ℓ j hj ih
    have hs := tensor_size κ ℓ a
    rw [basisVal, bitProd_succ_lo _ hj, ← basisVal, ← ih]
    simp only [tensor, tensorAux, Array.getD_eq_getD_getElem?] at hs ⊢
    rw [Array.getElem?_append_left (by omega)]
  · intro ℓ j hj ih
    have hs := tensor_size κ ℓ a
    rw [basisVal, bitProd_succ_hi _ hj, ← basisVal, ← ih, ← tensorAux_snd]
    simp only [tensor, tensorAux, Array.getD_eq_getD_getElem?] at hs ⊢
    rw [Array.getElem?_append_right (by omega), hs, Nat.add_sub_cancel_left,
      Array.getElem?_map, Array.getElem?_eq_getElem (by omega)]
    simp

theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : Fin n → M) :
    Fin.foldl n (fun acc j => acc + g j) 0 = ∑ j, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.foldl_succ_last, ih, Fin.sum_univ_castSucc]

/-- **L-RS5** (tensor evaluation): the verifier's `encAt` at `ω_c` is `Enc(·)_c`. -/
theorem encAt_eq {ι : Type*} (κ : ℕ → K) (ℓ : ℕ) (ω : ι → K) (msg : Array E) (c : ι) :
    encAt κ ℓ msg (ω c) = enc κ ℓ ω (fun j => msg.getD j 0) c := by
  rw [encAt, foldl_add_eq_sum, enc]
  exact sum_congr rfl fun j _ => by rw [tensor_getD κ _ ℓ j j.2, Algebra.smul_def]

end Tensor

end SpartanChain.RS
