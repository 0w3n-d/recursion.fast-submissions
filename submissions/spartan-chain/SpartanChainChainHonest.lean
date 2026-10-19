import SpartanChainChainInner
import SpartanChainProver

/-!
# The chain operations of the leaf SNARK, and their honesty (`HonestOps`, `sat_iff_abstract`)

* `chainWit κ n s : Spartan.Witness`: the prover's tables for a leaf `(s, n)` in `2 ^ κ` blocks —
  `z = (w ‖ pub)` (bits in `F`), `Az`, `Bz`, `Cz`, the packed witness `q(u') = Σ_i z(i + 64u') x^i`,
  and the inner table `innerTab`. `chainWf : WitFor` and `chainEvals : EvalsFor` are the leaf
  SNARK's parameters.
* `chainHonest : HonestOps chainEvals chainWf`: for every true leaf statement, the tables and
  the evaluators are honest for the chain R1CS (`chainA'`, `chainB'`, `chainC'`), from L-C3
  (`chain_complete`), `matrix_mle_eq` (`chainMats_eq`), `pub_mle` (`chainPub_eq`), the row lemmas
  (`rowA_honest` …) and `innerTab_eq`.
* `sat_iff_abstract`: the chain relation `ChainSat` is the abstract `Sat` of the protocol's
  matrices on the extended witness (so L-C2 applies to the decoded witness of the soundness
  argument).
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast Spartan

/-! ## The witness -/

/-- **The prover's tables** for a leaf `(s, n)` laid out in `2 ^ κ` blocks. -/
def chainWit (κ n : ℕ) (s : Digest) : Spartan.Witness :=
  let msgs := chainDigests s (2 ^ κ + 1)
  let forms := chainForms s κ
  let rows := rowArray gateBase
  let zf : Array F := Array.ofFn (n := 2 ^ ly κ) fun x ↦
    if zBit κ s (msgs.getD n default) forms x.val then 1 else 0
  { az := Array.ofFn (n := 2 ^ ly κ) fun x ↦ ofBool EF (azBit n κ msgs forms rows x.val)
    bz := Array.ofFn (n := 2 ^ ly κ) fun x ↦ ofBool EF (bzBit κ forms rows x.val)
    cz := Array.ofFn (n := 2 ^ ly κ) fun x ↦ ofBool EF (czBit n κ msgs forms x.val)
    z := zf
    q := Array.ofFn (n := 2 ^ lq κ) fun u ↦
      ∑ i : Fin (2 ^ 6), zf.getD (2 ^ 6 * u.val + i) 0 * F.x ^ (i : ℕ)
    innerTab := innerTab n κ }

/-- The prover's parameter of the leaf SNARK. -/
def chainWf : Leaf.WitFor := fun κ n s ↦ chainWit κ n s

/-- The verifier's parameter of the leaf SNARK. -/
def chainEv : Leaf.EvalsFor := chainEvals

/-! ## Transport to the protocol's cube -/

theorem matVec_cast {E : Type} [Field E] {L L' : ℕ} (h : L' = L)
    (M : Fin (2 ^ L) → Fin (2 ^ L) → E) (z : Fin (2 ^ L) → E) (x : Fin (2 ^ L')) :
    matVec (fun x y : Fin (2 ^ L') ↦ M (Fin.cast (by rw [h]) x) (Fin.cast (by rw [h]) y))
      (fun y ↦ z (Fin.cast (by rw [h]) y)) x = matVec M z (Fin.cast (by rw [h]) x) := by
  subst h; rfl

/-- **`sat_iff_abstract`**: the chain relation is the abstract R1CS relation of the protocol's
matrices on the extended witness. -/
theorem sat_iff_abstract {n κ : ℕ} (w : Fin (wLen κ) → EF) (s h : Digest) :
    ChainSat n κ w s h ↔
      Sat (chainA' n κ) (chainB' κ) (chainC' κ) (fun y ↦ zOf w s h (castIx κ y)) := by
  have hl := ly_eq κ
  unfold ChainSat Sat chainA' chainB' chainC' castIx
  constructor
  · intro hs x
    rw [matVec_cast hl, matVec_cast hl, matVec_cast hl]
    exact hs _
  · intro hs x
    have := hs (Fin.cast (by rw [hl]) x)
    rw [matVec_cast hl, matVec_cast hl, matVec_cast hl] at this
    simpa using this

/-! ## Honesty -/

section Honest

variable {n κ : ℕ} (s : Digest)

private theorem msgs_n (hnκ : n ≤ 2 ^ κ) :
    (chainDigests s (2 ^ κ + 1)).getD n default = chainEnd s n :=
  chainDigests_getD s (by omega)

theorem zT_chainWit (hnκ : n ≤ 2 ^ κ) :
    zT κ (chainWit κ n s) = fun y ↦ zHonest (E := EF) s n κ (castIx κ y) := by
  have hl := ly_eq κ
  funext y
  have hy : y.val < 2 ^ (14 + κ + 1) := by rw [← hl]; exact y.isLt
  have := zBits_eq (E := EF) (n := n) s hy
  rw [zN, dite_eq_left hy] at this
  rw [show (castIx κ y) = (⟨y.val, hy⟩ : Ix κ) from Fin.ext rfl, this]
  simp only [zT, tbl, chainWit, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_ofFn, y.isLt, ↓reduceDIte, Option.map_some, Option.getD_some, msgs_n s hnκ]
  unfold ofBool
  split <;> simp

theorem matVec_honest {M : Ix κ → Ix κ → EF} (hnκ : n ≤ 2 ^ κ) (x : Fin (2 ^ ly κ)) :
    matVec (fun x y ↦ M (castIx κ x) (castIx κ y)) (zT κ (chainWit κ n s)) x =
      matVec M (zHonest (E := EF) s n κ) (castIx κ x) := by
  rw [zT_chainWit s hnκ]
  exact matVec_cast (ly_eq κ) M _ x

theorem tbl_ofFn_bits (b : ℕ → Bool) :
    tbl (ly κ) (Array.ofFn (n := 2 ^ ly κ) fun x ↦ ofBool EF (b x.val)) =
      fun x ↦ ofBool EF (b x.val) := tbl_ofFn _

/-- **The chain operations are honest** (the hypothesis of `snark_complete`). -/
theorem chainHonest : Leaf.HonestOps chainEv chainWf := by
  intro s n hn _
  set κ := Leaf.kap n
  have hnκ : n ≤ 2 ^ κ := Nat.le_pow_clog (by norm_num) n
  have hl := ly_eq κ
  have hL : ∀ x : Fin (2 ^ ly κ), (castIx κ x).val < 2 ^ (14 + κ + 1) := fun x ↦ (castIx κ x).isLt
  refine ⟨chainA' n κ, chainB' κ, chainC' κ, ?_⟩
  refine
    { z_size := Array.size_ofFn
      z_bool := fun j ↦ ?_
      az := ⟨Array.size_ofFn, ?_⟩
      bz := ⟨Array.size_ofFn, ?_⟩
      cz := ⟨Array.size_ofFn, ?_⟩
      sat := ?_
      inner := fun rx ρ hx ↦ innerTab_eq rx hx ρ
      mats := fun rx ry hx hy ↦ chainMats_eq hn hnκ rx ry hx hy
      pub := fun ru hu ↦ ?_
      q_size := Array.size_ofFn
      q_pack := fun u ↦ ?_ }
  · simp only [chainWf, chainWit, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    split
    · split <;> simp
    · simp
  · funext x
    unfold chainA'
    rw [chainWf, matVec_honest s hnκ, matVec_chainA, rowA_honest s hn hnκ (hL x)]
    exact congrFun (tbl_ofFn_bits _) x
  · funext x
    unfold chainB'
    rw [chainWf, matVec_honest s hnκ, matVec_chainB, rowB_honest s (hL x)]
    exact congrFun (tbl_ofFn_bits _) x
  · funext x
    unfold chainC'
    rw [chainWf, matVec_honest s hnκ, matVec_chainC, rowC_honest s hnκ (hL x)]
    exact congrFun (tbl_ofFn_bits _) x
  · intro x
    unfold chainA' chainB' chainC'
    rw [chainWf, matVec_honest s hnκ, matVec_honest s hnκ, matVec_honest s hnκ]
    exact chain_complete hn hnκ s _
  · simp only [chainEv, chainEvals, chainWf]
    rw [chainPub_eq]
    congr 1
    funext u
    rw [zT_chainWit s hnκ, zHonest]
    beta_reduce
    have hu' : (castIx κ (join u (1 : Fin (2 ^ 1)))).val = wLen κ + u.val := by
      change 2 ^ lu κ * (1 : Fin (2 ^ 1)).val + u.val = wLen κ + u.val
      have h2 : 2 ^ lu κ = wLen κ := congrArg (2 ^ ·) (lu_eq κ)
      have h1 : (1 : Fin (2 ^ 1)).val = 1 := rfl
      generalize u.val = v
      rw [h2, h1, mul_one]
    rw [zOf, dite_eq_right (by rw [hu']; omega), hu', Nat.add_sub_cancel_left]
  · simp [chainWf, chainWit]

end Honest

end SpartanChain
