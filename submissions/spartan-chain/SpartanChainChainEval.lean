import SpartanChainChainMle
import SpartanChainSpartanProtocol

/-!
# The verifier's evaluators of the chain R1CS (BLUEPRINT-R1 §2.4; Rust `matrix_eval`, `pub_mle`)

* `chainMats n κ r_x r_y = (Ã, B̃, C̃)(r_x, r_y)`: the closed forms of §2.4
  (`SpartanChainChainMle.lean`) with the block parts `A0̃`, `B0̃` computed by the walk over the
  tables `eq(r_x[0..14), ·)`, `eq(r_y[0..14), ·)`. Cost `≈ 2^16` multiplications, independent
  of `n`.
* `chainPub κ s h r_u = p̃ub(r_u)`: `Σ_{u ≤ 512} pub(u) · eq(r_u, u)`.
* `chainEvals : ℕ → ℕ → Digest → Digest → Spartan.Evals` (the verifier's `EvalsFor`).

Correctness against the abstract R1CS of `SpartanChainSoundnessSpartan.lean`:
`chainMats_eq` (`= (matMle A, matMle B, matMle C)` of the chain matrices on the protocol's cube
`Fin (2 ^ ly κ)`, `chainA'` …) and `chainPub_eq` (`= mle pub`).
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast Spartan

/-- A point given as a list, read on `ℕ` (`0` from `L` on). -/
def ptN {R : Type*} [Zero R] (L : ℕ) (r : List R) : ℕ → R := fun l ↦ if l < L then r.getD l 0 else 0

/-- **The verifier's evaluator** of `(Ã, B̃, C̃)` at `(r_x, r_y)` (§2.4, Rust `matrix_eval`
without `ρ`). -/
def chainMats (n κ : ℕ) (rx ry : List EF) : EF × EF × EF :=
  let R := ptN (14 + κ + 1) rx
  let S := ptN (14 + κ + 1) ry
  let e := eqTable (rx.take 14)
  let wt := eqTable (ry.take 14)
  let ab := walkAB (fun k : Pos Blake2sCircuit.m ↦ e.getD k.val 0)
    (fun j : Pos Blake2sCircuit.m ↦ wt.getD j.val 0)
  (closedA n κ R S ab.1, closedB κ R S ab.2, closedC κ R S)

/-- The public bit `pub(u)`: `pub(0) = 1`, `pub(1 + j) = s_j`, `pub(257 + j) = h_j`. -/
def pubBit (s h : Digest) (u : ℕ) : Bool :=
  if u = 0 then true
  else if u < 257 then dbit s (u - 1)
  else if u < 513 then dbit h (u - 257)
  else false

/-- **The verifier's evaluator** of `p̃ub(r_u)` (Rust `pub_mle`). -/
def chainPub (κ : ℕ) (s h : Digest) (ru : List EF) : EF :=
  ∑ u : Fin 513, if pubBit s h u.val then eqv (ptN (14 + κ) ru) (14 + κ) u.val else 0

/-- The evaluators for the verifier: `ev κ n s h`. -/
def chainEvals (κ n : ℕ) (s h : Digest) : Spartan.Evals := ⟨chainMats n κ, chainPub κ s h⟩

/-! ## The chain matrices on the protocol's cube -/

theorem ly_eq (κ : ℕ) : ly κ = 14 + κ + 1 := by simp only [ly, lu, lq]; omega

theorem lu_eq (κ : ℕ) : lu κ = 14 + κ := by simp only [lu, lq]; omega

/-- The protocol's index `Fin (2 ^ ly κ)` as a chain index. -/
def castIx (κ : ℕ) (x : Fin (2 ^ ly κ)) : Ix κ := Fin.cast (by rw [ly_eq]) x

/-- `A` on the protocol's cube. -/
noncomputable def chainA' (n κ : ℕ) (x y : Fin (2 ^ ly κ)) : EF := chainA n κ (castIx κ x) (castIx κ y)

/-- `B` on the protocol's cube. -/
noncomputable def chainB' (κ : ℕ) (x y : Fin (2 ^ ly κ)) : EF := chainB κ (castIx κ x) (castIx κ y)

/-- `C` on the protocol's cube. -/
def chainC' (κ : ℕ) (x y : Fin (2 ^ ly κ)) : EF := chainC κ (castIx κ x) (castIx κ y)

/-- Extensions are invariant under renaming the number of variables. -/
theorem matMle_cast {E : Type} [Field E] {L L' : ℕ} (h : L' = L)
    (M : Fin (2 ^ L) → Fin (2 ^ L) → E) (r r' : Fin L' → E) :
    matMle (fun x y : Fin (2 ^ L') ↦ M (Fin.cast (by rw [h]) x) (Fin.cast (by rw [h]) y)) r r' =
      matMle M (fun l ↦ r (Fin.cast h.symm l)) (fun l ↦ r' (Fin.cast h.symm l)) := by
  subst h; rfl

theorem extPt_ptOf {L L' : ℕ} (h : L' = L) (r : List EF) :
    extPt (fun l : Fin L ↦ ptOf L' r (Fin.cast h.symm l)) = ptN L r := by
  funext l; simp [extPt, ptOf, ptN]

/-! ## The tables -/

theorem eqTable_take_getD (r : List EF) (p : ℕ) (hr : p ≤ r.length) {L : ℕ} (hp : p ≤ L)
    (u : Fin (2 ^ p)) : (eqTable (r.take p)).getD u.val 0 = eqv (ptN L r) p u.val := by
  have := congrFun (tbl_eqTable' (r.take p) (by simp; omega)) u
  simp only [tbl] at this
  rw [this, eqv_eq_eq]
  congr 1
  funext l
  have := l.isLt
  simp [ptOf, ptN, List.getD_eq_getElem?_getD, List.getElem?_take, show (l : ℕ) < L by omega, l.isLt]

/-- **`matrix_mle_eq`, as the verifier computes it**: the evaluator is the extension of the
chain matrices, for points of `ℓ_y` coordinates. -/
theorem chainMats_eq {n κ : ℕ} (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) (rx ry : List EF)
    (hx : rx.length = ly κ) (hy : ry.length = ly κ) :
    chainMats n κ rx ry = (matMle (chainA' n κ) (ptOf _ rx) (ptOf _ ry),
      matMle (chainB' κ) (ptOf _ rx) (ptOf _ ry), matMle (chainC' κ) (ptOf _ rx) (ptOf _ ry)) := by
  have hl := ly_eq κ
  have hx' : 14 ≤ rx.length := by omega
  have hy' : 14 ≤ ry.length := by omega
  have hwalk : walkAB (fun k : Pos Blake2sCircuit.m ↦ (eqTable (rx.take 14)).getD k.val 0)
      (fun j : Pos Blake2sCircuit.m ↦ (eqTable (ry.take 14)).getD j.val 0) =
      (blockSum blockA (ptN (14 + κ + 1) rx) (ptN (14 + κ + 1) ry),
        blockSum blockB (ptN (14 + κ + 1) rx) (ptN (14 + κ + 1) ry)) := by
    rw [← walkAB_blockSum]
    congr 1
    · funext k; exact eqTable_take_getD rx 14 hx' (by omega) k
    · funext j; exact eqTable_take_getD ry 14 hy' (by omega) j
  simp only [chainMats, hwalk]
  unfold chainA' chainB' chainC' castIx
  rw [matMle_cast hl (chainA n κ), matMle_cast hl (chainB κ), matMle_cast hl (chainC κ),
    matMle_chainA hn hnκ, matMle_chainB, matMle_chainC, extPt_ptOf hl, extPt_ptOf hl]

/-- **`pub_mle`**: the evaluator is the extension of the public column. -/
theorem chainPub_eq (κ : ℕ) (s h : Digest) (ru : List EF) :
    chainPub κ s h ru =
      mle (fun u : Fin (2 ^ lu κ) ↦ pubVal (E := EF) s h u.val) (ptOf (lu κ) ru) := by
  have hl := lu_eq κ
  have h513 : 513 ≤ 2 ^ lu κ := by
    rw [hl, pow_add]; have : 1 ≤ 2 ^ κ := Nat.one_le_two_pow; norm_num; omega
  have hpv : ∀ v : ℕ, pubVal (E := EF) s h v = if pubBit s h v then 1 else 0 := by
    intro v
    unfold pubVal pubBit ofBool
    split_ifs <;> simp_all
  have h1 : ∀ u : Fin (2 ^ lu κ), eq (ptOf (lu κ) ru) (cube u) * pubVal (E := EF) s h u.val =
      (fun v ↦ if pubBit s h v then eqv (ptN (14 + κ) ru) (14 + κ) v else 0) u.val := by
    intro u
    have he := eqv_eq_eq (ptN (14 + κ) ru) (lu κ) u
    have hf : (fun l : Fin (lu κ) ↦ ptN (14 + κ) ru l) = ptOf (lu κ) ru := by
      funext l; have := l.isLt; simp [ptN, ptOf, show (l : ℕ) < 14 + κ by omega]
    rw [hf, congrArg (fun L ↦ eqv (ptN (14 + κ) ru) L u.val) hl] at he
    rw [hpv, ← he]
    by_cases hb : pubBit s h u.val = true <;> simp [hb]
  rw [mle, chainPub, sum_congr rfl fun u _ ↦ h1 u,
    Fin.sum_univ_eq_sum_range (fun v ↦ if pubBit s h v then eqv (ptN (14 + κ) ru) (14 + κ) v
      else 0),
    Fin.sum_univ_eq_sum_range (fun v ↦ if pubBit s h v then eqv (ptN (14 + κ) ru) (14 + κ) v
      else 0)]
  have hz : ∑ v ∈ Finset.Ico 513 (2 ^ lu κ),
      (if pubBit s h v then eqv (ptN (14 + κ) ru) (14 + κ) v else 0) = 0 := by
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    have : 513 ≤ v := (Finset.mem_Ico.mp hv).1
    have hb : pubBit s h v = false := by
      unfold pubBit
      rw [ite_eq_right (show v ≠ 0 by omega), ite_eq_right (show ¬ v < 257 by omega),
        ite_eq_right (show ¬ v < 513 by omega)]
    rw [hb]
    rfl
  rw [← Finset.sum_range_add_sum_Ico _ h513, hz, add_zero]

end SpartanChain
