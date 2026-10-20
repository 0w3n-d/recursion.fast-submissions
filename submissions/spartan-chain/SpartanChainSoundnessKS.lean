import SpartanChainSoundnessKSBase
import SpartanChainChainSound
import SpartanChainSoundnessPack
import SpartanChainChainEval

/-!
# The knowledge state of the leaf SNARK: the per-position facts and the `step` law (BLUEPRINT-R1 §9.2–§9.3)

The generic potential, its step law from per-position facts (`muG_step_of`), the shape positions,
locality, `doom_mid` and the round bounds are in `SpartanChainSoundnessKSBase`. This module proves
`doom_absorb` and `esc_single_le` for `Doom`, `chainEvals_ok` (the verifier's evaluators are the
extensions of the chain R1CS), and assembles `mu_step` / `mu_step_chain`.
-/

namespace SpartanChain
open RecursionFast Merkle Transcript SoundnessLog
open scoped NNReal

namespace KS

section Lengths
open PCS

theorem length_tauOf (κ : ℕ) (es : Log) : (tauOf κ es).length = 15 + κ := by simp [tauOf]
theorem length_rxOf (κ : ℕ) (es : Log) : (rxOf κ es).length = 15 + κ := by simp [rxOf]
theorem length_ryOf (κ : ℕ) (es : Log) : (ryOf κ es).length = 15 + κ := by simp [ryOf]
theorem length_rrOf (κ : ℕ) (es : Log) : (rrOf κ es).length = 8 + κ := by simp [rrOf]
theorem length_fsOf (κ : ℕ) (es : Log) : (fsOf κ es).length = 6 := by simp [fsOf]

theorem size_fTbl (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    (fTbl κ U es).size = 2 ^ (14 + κ + 1) := by simp [fTbl]

theorem oTbls_sizes (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    ∀ t ∈ oTbls κ U es, t.size = 2 ^ (14 + κ + 1) :=
  outer_sizes _ (by rw [length_tauOf]; omega) _ _ _ _

theorem iTbls_sizes (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    ∀ t ∈ iTbls κ U es, t.size = 2 ^ (14 + κ + 1) := by
  simp [iTbls, innerTables]

theorem wTbls_sizes (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    ∀ t ∈ wTbls κ U es, t.size = 2 ^ (8 + κ) := by
  simp [wTbls]

end Lengths



section MleHelpers

variable {R : Type*} [CommRing R]

theorem ptOf_split (a b : ℕ) (r : List R) :
    ptOf (a + b) r = Fin.append (ptOf a (r.take a)) (ptOf b (r.drop a)) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · rw [Fin.append_left]
    simp [ptOf, List.getD_eq_getElem?_getD, i.isLt]
  · rw [Fin.append_right]
    simp [ptOf, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **L-E3 for the packed layout** (`mle_split`): the extension of `u ↦ Q[u / 2^a][u mod 2^a]` at
`r` is `Σ_j eq(r_lo, j) Σ_i eq(r_hi, i) Q[i][j]`. -/
theorem mle_pack (a b n : ℕ) (hn : a + b = n) (Q : Fin (2 ^ b) → Fin (2 ^ a) → R)
    (h1 : ∀ u : Fin (2 ^ n), u.val / 2 ^ a < 2 ^ b) (r : List R) :
    mle (fun u : Fin (2 ^ n) => Q ⟨u.val / 2 ^ a, h1 u⟩ ⟨u.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩)
      (ptOf n r) =
      ∑ j : Fin (2 ^ a), eq (ptOf a (r.take a)) (cube j) *
        ∑ i : Fin (2 ^ b), eq (ptOf b (r.drop a)) (cube i) * Q i j := by
  subst hn
  rw [ptOf_split, mle_split]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [mle]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  · apply Fin.ext
    simp only [join]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt j.isLt, zero_add]
  · apply Fin.ext
    simp only [join]
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

theorem dot_eqTable {ℓ : ℕ} (r : List R) (hr : r.length = ℓ) (v : Array R) :
    dot (eqTable r) v = ∑ u : Fin (2 ^ ℓ), eq (ptOf ℓ r) (cube u) * v.getD u 0 := by
  rw [dot, eqTable_size, hr, sumTo_eq_fin]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← congrFun (tbl_eqTable' r hr) u]
  rfl

theorem eqTable_getD {ℓ : ℕ} (r : List R) (hr : r.length = ℓ) (u : Fin (2 ^ ℓ)) :
    (eqTable r).getD u 0 = eq (ptOf ℓ r) (cube u) := by
  rw [← congrFun (tbl_eqTable' r hr) u]
  rfl

theorem weightEval_mle [CharP R 2] {ℓ : ℕ} (fs r r'' : List R) (hr : r.length = ℓ)
    (hr'' : r''.length = ℓ) :
    weightEval fs r r'' = mle (fun u : Fin (2 ^ ℓ) => Phi fs (eq (ptOf ℓ r) (cube u)))
      (ptOf ℓ r'') := by
  rw [← mleEval_weightTable fs r r'' hr hr'', mleEval_eq' _ _ hr'']
  congr 1
  funext u
  rw [← congrFun (tbl_eqTable' r hr) u, ← phiApply_eq]
  have hu : u.val < (eqTable r).size := by rw [eqTable_size, hr]; exact u.isLt
  simp [tbl, weightTable, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]

/-- `mle_split` with the number of variables given by an equation. -/
theorem mle_split_cast (a b n : ℕ) (hn : a + b = n) (f : Fin (2 ^ n) → R) (r : List R) :
    mle f (ptOf n r) = ∑ u₁ : Fin (2 ^ a), eq (ptOf a (r.take a)) (cube u₁) *
      mle (fun u₂ : Fin (2 ^ b) => f (Fin.cast (by rw [← hn]) (join u₁ u₂))) (ptOf b (r.drop a)) := by
  subst hn
  rw [ptOf_split, mle_split]
  rfl

theorem sum_two_pow_one (f : Fin (2 ^ 1) → R) : ∑ u, f u = f 0 + f 1 := Fin.sum_univ_two f

/-- The extension of `(w ‖ p)` (the top variable selects `p`). -/
theorem mle_top (m : ℕ) (w : Fin (2 ^ m) → R) (p : ℕ → R) (r : List R) :
    mle (fun y : Fin (2 ^ (m + 1)) => if hy : y.val < 2 ^ m then w ⟨y.val, hy⟩ else p (y.val - 2 ^ m))
      (ptOf (m + 1) r) =
      (1 - r.getD m 0) * mle w (ptOf m (r.take m)) +
        r.getD m 0 * mle (fun u : Fin (2 ^ m) => p u.val) (ptOf m (r.take m)) := by
  rw [ptOf_split m 1, mle_split]
  conv_rhs => rw [mle, mle, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mle, sum_two_pow_one]
  have h0 : (join u (0 : Fin (2 ^ 1))).val = u.val := by simp [join]
  have h1 : (join u (1 : Fin (2 ^ 1))).val = 2 ^ m + u.val := by simp [join]
  have hu := u.isLt
  simp only [h0, h1, hu, (show ¬ 2 ^ m + u.val < 2 ^ m by omega), ↓reduceDIte,
    Nat.add_sub_cancel_left]
  have e0 : eq (ptOf 1 (r.drop m)) (cube (0 : Fin (2 ^ 1))) = 1 - r.getD m 0 := by
    simp [eq, cube, ptOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have e1 : eq (ptOf 1 (r.drop m)) (cube (1 : Fin (2 ^ 1))) = r.getD m 0 := by
    simp [eq, cube, ptOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e0, e1]
  have : (⟨u.val, hu⟩ : Fin (2 ^ m)) = u := rfl
  rw [this]
  ring

end MleHelpers

/-! ## Part E: `doom_absorb` -/

section Absorb
open PCS Spartan SoundnessPCS RS

/-- **The evaluators are the extensions** of the chain matrices and of the public column
(L-C4 `matrix_mle_eq`, `pub_mle`; for the verifier's `chainEvals` by `chainMats_eq`,
`chainPub_eq`). -/
structure EvalsOK (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) : Prop where
  mats : ∀ κ n s h (rx ry : List EF), 1 ≤ n → n ≤ 2 ^ κ → rx.length = 15 + κ →
    ry.length = 15 + κ → (ev κ n s h).mats rx ry =
      (matMle (chainA n κ) (ptOf (14 + κ + 1) rx) (ptOf (14 + κ + 1) ry),
        matMle (chainB κ) (ptOf (14 + κ + 1) rx) (ptOf (14 + κ + 1) ry),
        matMle (chainC κ) (ptOf (14 + κ + 1) rx) (ptOf (14 + κ + 1) ry))
  pub : ∀ κ n s h (ru : List EF), ru.length = 14 + κ →
    (ev κ n s h).pub ru = mle (fun u : Fin (2 ^ (14 + κ)) => pubVal (E := EF) s h u.val)
      (ptOf (14 + κ) ru)

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

theorem mle_tbl_ofFn_pt {R : Type*} [CommRing R] (a : ℕ) (f : Fin (2 ^ a) → R) (r : List R)
    (h : r.length = a) : mle (tbl r.length (Array.ofFn f)) (pt r) = mle f (ptOf a r) := by
  subst h; rw [tbl_ofFn, pt_eq_ptOf]

/-- `absorb(g_0)` after `τ_{ℓ−1}`: `zc_end`, `outer_start`. -/
theorem absorb_g0 {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pG κ 0 + 1) (H : AlgRow κ U es (.tau (14 + κ))) :
    AlgRow κ U es (.gOut 0) := by
  simp only [AlgRow, SumWrong] at H ⊢
  rcases H with hf | ⟨hF, hd⟩
  · exact Or.inl hf
  refine Or.inr ⟨hF, ?_⟩
  have hτ : (tauOf κ es).length = 14 + κ + 1 := by rw [length_tauOf]; omega
  rw [show 14 + κ + 1 - (14 + κ) - 1 = 0 by omega, List.take_of_length_le (by omega)] at hd
  have h1 := zc_end (fTbl κ U es) (tauOf κ es) (by rw [size_fTbl, hτ]) hd
  rw [fTbl, mle_tbl_ofFn_pt _ _ _ hτ] at h1
  have := outer_start (tauOf κ es) hτ h1
  simpa [clOut, bindAll, oTbls] using this

/-- `absorb(v_A ‖ v_B ‖ v_C)` after `r_{x,ℓ−1}`: `outer_final`, check (b), `triple_wrong`. -/
theorem absorb_tri {es : Log} {κ : ℕ} (hk : kapOf es = κ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pTri κ + 1) (H : AlgRow κ U es (.rx (14 + κ))) :
    Rej ev es ∨ AlgRow κ U es .tri := by
  simp only [AlgRow, SumWrong] at H ⊢
  rcases H with hf | ⟨hF, hd⟩
  · exact Or.inr (Or.inl hf)
  have hτ : (tauOf κ es).length = 14 + κ + 1 := by rw [length_tauOf]; omega
  have hx : (rxOf κ es).length = 14 + κ + 1 := by rw [length_rxOf]; omega
  rw [show 14 + κ + 1 - (14 + κ + 1) = 0 by omega, List.take_of_length_le (by omega),
    oTbls, outer_final _ _ hτ hx] at hd
  by_cases hb : clOut κ es (15 + κ) = eqPts (tauOf κ es) (rxOf κ es) *
      ((triOf κ es).1 * (triOf κ es).2.1 + (triOf κ es).2.2)
  · refine Or.inr (Or.inr ⟨hF, ?_⟩)
    have hb' : clOut κ es (14 + κ + 1) = eqPts (tauOf κ es) (rxOf κ es) *
        ((triOf κ es).1 * (triOf κ es).2.1 + (triOf κ es).2.2) := by
      rw [show 14 + κ + 1 = 15 + κ by omega]; exact hb
    rw [eqPts_eq _ _ hτ hx] at hb'
    exact triple_wrong hd hb'
  · left
    simp only [Rej]
    rw [hk]
    exact Or.inr (Or.inl ⟨by omega, hb⟩)

theorem stmt_bounds {es : Log} (hm : Matches es) {κ : ℕ} (hk : kapOf es = κ) :
    1 ≤ (stmtOf es).2.1 ∧ (stmtOf es).2.1 ≤ 2 ^ κ := by
  obtain ⟨s, n, h, h0, h1, -, -⟩ := (matches_iff' es).mp hm
  have hκ : κ = Nat.clog 2 n := by rw [← hk, kapOf_of h0]
  have hst : stmtOf es = (s, n, h) := by
    cases he : es[0]? with
    | none => rw [he] at h0; cases h0
    | some e =>
      rw [he, Option.bind_some] at h0
      simp [stmtOf, entAt, List.getD_eq_getElem?_getD, he, h0]
  rw [hst]
  exact ⟨h1, by rw [hκ]; exact (Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl⟩

/-- **The slices, when correct, give the verifier's `z̃`** (`z_mle_slices` in the layout of
`zOf`, with `pub_mle`): if `δ = 0` then `z̃_V(r_y) = z̃_dec(r_y)`. -/
theorem zV_eq_of_delta {ev : ℕ → ℕ → Digest → Digest → Spartan.Evals} (hev : EvalsOK ev)
    {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F) (hδ : deltaOf κ U es = 0) :
    zV κ (ev κ (stmtOf es).2.1 (stmtOf es).1 (stmtOf es).2.2) (slicesOf κ es) (ryOf κ es) =
      mle (zOfU κ U es) (ptOf (14 + κ + 1) (ryOf κ es)) := by
  have hlu : lu κ = 14 + κ := by simp only [lu, lq]; omega
  have hry : (ryOf κ es).length = 15 + κ := length_ryOf κ es
  set ry := ryOf κ es
  set ru := ry.take (14 + κ)
  have hru : ru.length = 14 + κ := by simp only [ru, List.length_take, hry]; omega
  have hz : zOfU κ U es = fun y : Fin (2 ^ (14 + κ + 1)) =>
      if hy : y.val < 2 ^ (14 + κ) then (fun u : Fin (2 ^ (14 + κ)) => EF.ofF (wDec κ U u)) ⟨y.val, hy⟩
      else (fun v : ℕ => pubVal (E := EF) (stmtOf es).1 (stmtOf es).2.2 v) (y.val - 2 ^ (14 + κ)) := by
    funext y; rfl
  rw [hz, mle_top (14 + κ) (fun u : Fin (2 ^ (14 + κ)) => EF.ofF (wDec κ U u))
    (fun v : ℕ => pubVal (E := EF) (stmtOf es).1 (stmtOf es).2.2 v) ry]
  simp only [zV]
  rw [hlu, hev.pub _ _ _ _ _ hru,
    mle_split_cast 6 (8 + κ) (14 + κ) (by omega) (fun u => EF.ofF (wDec κ U u)),
    dot_eqTable (R := EF) (ℓ := 6) _ (by simp only [List.length_take, hry]; omega)]
  have hsl : ∀ i : Fin (2 ^ 6), (slicesOf κ es).getD i 0 =
      mle (fun u₂ : Fin (2 ^ (8 + κ)) =>
        EF.ofF (wDec κ U (Fin.cast (pack_eq κ) (join i u₂)))) (ptOf (8 + κ) (ru.drop 6)) := by
    intro i
    have := congrFun hδ i
    simp only [deltaOf, Pi.zero_apply] at this
    have hr : rhiOf κ es = ru.drop 6 := by simp only [rhiOf, hlu]; rfl
    rw [hr] at this
    exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact this)
  rw [CharTwo.sub_eq_add]
  simp only [hsl]
  rfl

/-- `absorb(slices)` after `r_{y,ℓ−1}`: `inner_final`, check (d) with `EvalsOK` (`matrix_mle_eq`),
`ne_of_claim`, and `zV_eq_of_delta`. -/
theorem absorb_sl (hev : EvalsOK ev) {es : Log} (hm : Matches es) {κ : ℕ} (hk : kapOf es = κ)
    (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pS κ + 1) (H : AlgRow κ U es (.ry (14 + κ))) :
    Rej ev es ∨ AlgRow κ U es .sl := by
  simp only [AlgRow, SumWrong] at H ⊢
  rcases H with hf | ⟨hF, hd⟩
  · exact Or.inr (Or.inl hf)
  have hry : (ryOf κ es).length = 14 + κ + 1 := by rw [length_ryOf]; omega
  have hrx : (rxOf κ es).length = 15 + κ := length_rxOf κ es
  rw [show 14 + κ + 1 - (14 + κ + 1) = 0 by omega, List.take_of_length_le (by omega), iTbls,
    inner_final _ _ _ _ _ _ _ hry] at hd
  obtain ⟨hn1, hn2⟩ := stmt_bounds hm hk
  set E := ev κ (stmtOf es).2.1 (stmtOf es).1 (stmtOf es).2.2 with hE
  set M := E.mats (rxOf κ es) (ryOf κ es) with hMdef
  have hM : M = (matMle (chainA (stmtOf es).2.1 κ) (ptOf (14 + κ + 1) (rxOf κ es))
        (ptOf (14 + κ + 1) (ryOf κ es)),
      matMle (chainB κ) (ptOf (14 + κ + 1) (rxOf κ es)) (ptOf (14 + κ + 1) (ryOf κ es)),
      matMle (chainC κ) (ptOf (14 + κ + 1) (rxOf κ es)) (ptOf (14 + κ + 1) (ryOf κ es))) :=
    hev.mats _ _ _ _ _ _ hn1 hn2 hrx (by omega)
  by_cases hdd : clIn κ es (15 + κ) =
      (M.1 + rhoOf κ es * M.2.1 + rhoOf κ es ^ 2 * M.2.2) * zV κ E (slicesOf κ es) (ryOf κ es)
  · refine Or.inr (Or.inr ⟨hF, fun hδ => ?_⟩)
    rw [hM] at hdd
    rw [show 15 + κ = 14 + κ + 1 by omega] at hdd
    exact ne_of_claim hd hdd (zV_eq_of_delta hev U hδ)
  · left
    simp only [Rej]
    rw [hk]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hdd⟩)))

/-- **The packing identity** (S2b-M4, `SpartanChainSoundnessPack.qPack_eq_sum`): the decoded packed
element is the sum of its bit planes, `q_dec(u') = Σ_{i<64} Q_i(u') · x^i`, bit `i` of the `BF64`
word being the coefficient of `x^i`. -/
theorem qPack_eq_bits (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ))) :
    qPack κ U u = ∑ i : Fin (2 ^ 6), wDec κ U (Fin.cast (pack_eq κ) (join i u)) * F.x ^ (i : ℕ) :=
  qPack_eq_sum κ U u

theorem size_slicesOf (κ : ℕ) (es : Log) : (slicesOf κ es).size = 64 := by
  simp [slicesOf, efsAt, Ligero.readEFs]

/-- `absorb(g''_0)` after `f_5`: `rs_end` (L-R3) with `prod_trueSum` and the packing identity. -/
theorem absorb_gR0 {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pGr κ 0 + 1) (H : AlgRow κ U es (.f 5)) :
    AlgRow κ U es (.gRs 0) := by
  simp only [AlgRow, SumWrong] at H ⊢
  rcases H with hf | ⟨hF, hd⟩
  · exact Or.inl hf
  refine Or.inr ⟨hF, ?_⟩
  rw [List.take_of_length_le (by rw [length_fsOf])] at hd
  have hrs := rs_end (K := F) (E := EF) F.x
    (fun (i : Fin (2 ^ 6)) u => wDec κ U (Fin.cast (pack_eq κ) (join i u)))
    (fun i u => wDec_bool κ U _) (ptOf (8 + κ) (rhiOf κ es))
    (fun i => (slicesOf κ es).getD i 0) 5 (fsOf κ es) (length_fsOf κ es) (by
      convert hd using 2 <;> rfl)
  simp only [clRs, List.take_zero, bindAll, Nat.sub_zero, wTbls]
  rw [prod_trueSum, target_eq, size_slicesOf]
  intro heq
  apply hrs
  rw [← Fin.sum_univ_eq_sum_range (fun i => xE ^ i * Phi (fsOf κ es) ((slicesOf κ es).getD i 0))
    64] at heq
  convert heq using 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [xE, ← map_pow]
    try rfl
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [qPack_eq_bits, EF.algebraMap_eq_ofF]

theorem lk_add_muR (κ : ℕ) : lk κ + muR κ = 8 + κ := by unfold lk muR; omega

/-- `absorb(v)` after `r''_{7+κ}`: check (f), `weightEval_mle` (L-R4), `ne_of_claim`, and
`mle_pack` (L-E3): a correct `v` would make `v' = q̃_dec(r'')`. -/
theorem absorb_v {es : Log} {κ : ℕ} (hk : kapOf es = κ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pV κ + 1) (H : AlgRow κ U es (.rr (7 + κ))) :
    Rej ev es ∨ AlgRow κ U es .vabs := by
  simp only [AlgRow, SumWrong] at H ⊢
  rcases H with hf | ⟨hF, hd⟩
  · exact Or.inr (Or.inl hf)
  have hrr : (rrOf κ es).length = 8 + κ := length_rrOf κ es
  rw [show 8 + κ - (7 + κ + 1) = 0 by omega, List.take_of_length_le (by omega),
    trueSum_bindAll _ _ _ (fun t ht => by rw [wTbls_sizes κ U es t ht, hrr])] at hd
  simp only [innerExpr, Expr.eval, wTbls] at hd
  rw [show (#[Array.ofFn (n := 2 ^ (8 + κ)) fun u =>
        Phi (fsOf κ es) (eq (ptOf (8 + κ) (rhiOf κ es)) (cube u)),
      Array.ofFn (n := 2 ^ (8 + κ)) fun u => EF.ofF (qPack κ U u)] : Array (Array EF)).getD 0 #[] =
      Array.ofFn (n := 2 ^ (8 + κ)) fun u =>
        Phi (fsOf κ es) (eq (ptOf (8 + κ) (rhiOf κ es)) (cube u)) from rfl,
    show (#[Array.ofFn (n := 2 ^ (8 + κ)) fun u =>
        Phi (fsOf κ es) (eq (ptOf (8 + κ) (rhiOf κ es)) (cube u)),
      Array.ofFn (n := 2 ^ (8 + κ)) fun u => EF.ofF (qPack κ U u)] : Array (Array EF)).getD 1 #[] =
      Array.ofFn (n := 2 ^ (8 + κ)) fun u => EF.ofF (qPack κ U u) from rfl,
    mle_tbl_ofFn_pt (8 + κ) _ _ hrr, mle_tbl_ofFn_pt (8 + κ) _ _ hrr] at hd
  have hrhi : (rhiOf κ es).length = 8 + κ := by
    simp [rhiOf, length_ryOf, lu, lq]; omega
  by_cases hf : clRs κ es (8 + κ) = weightEval (fsOf κ es) (rhiOf κ es) (rrOf κ es) *
      dot (eqTable ((rrOf κ es).take (lk κ))) (vOf κ es)
  · refine Or.inr (Or.inr ⟨hF, ?_⟩)
    rw [weightEval_mle _ _ _ hrhi hrr] at hf
    have hne := ne_of_claim (by rwa [show 7 + κ + 1 = 8 + κ by omega] at hd) hf
    intro hv
    apply hne
    have hlo : ((rrOf κ es).take (lk κ)).length = lk κ := by
      rw [List.length_take, hrr]; have := lk_add_muR κ; omega
    have hhi : ((rrOf κ es).drop (lk κ)).length = muR κ := by
      rw [List.length_drop, hrr]; have := lk_add_muR κ; omega
    rw [dot_eqTable _ hlo]
    have hpack := mle_pack (lk κ) (muR κ) (8 + κ) (lk_add_muR κ)
      (fun i j => EF.ofF (qDec κ U i j)) (fun u => qRow_lt κ u) (rrOf κ es)
    refine Eq.trans ?_ hpack.symm
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [show (vOf κ es).getD j 0 = (fun j : Fin (2 ^ lk κ) => (vOf κ es).getD j 0) j from rfl, hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (· * EF.ofF (qDec κ U i j))
      (eqTable_getD _ hhi (show Fin (2 ^ muR κ) from i))
  · left
    simp only [Rej]
    rw [hk]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hf⟩))))

/-- **`doom_absorb`** (§9.2): an absorb never undooms. -/
theorem doom_absorb (hev : EvalsOK ev) (L₀ es : Log) (x : ByteArray × Digest) (k : UInt8)
    (l : ℕ) (hm : Matches (es ++ [x])) (hsh : (shape (kapOf es))[es.length]? = some (.absorb k l))
    (hd : Doom ev L₀ es) : Doom ev L₀ (es ++ [x]) := by
  have hne : es ≠ [] := by
    rintro rfl; rw [List.length_nil, shape_seed] at hsh; cases hsh
  have hm0 : Matches es := matches_of_append hne hm
  obtain ⟨hk, hlen, hroot⟩ := append_facts hm hne
  obtain ⟨κ, hκ⟩ : ∃ κ, kapOf es = κ := ⟨_, rfl⟩
  rw [hκ] at hsh hlen hk
  rw [doom_iff ev hκ] at hd
  rw [doom_iff ev hk]
  rcases hd with hr | ha
  · exact Or.inl (rej_mono ev hne _ hr)
  have hag := agree_append es [x]
  have hl1 : (es ++ [x]).length - 1 = es.length := by simp
  have hL1 : (es ++ [x]).length = es.length + 1 := by simp
  rw [hl1]
  have tr : ∀ c, posOfC κ c < es.length →
      AlgRow κ (filled κ L₀ (rootOf es)) es c →
        AlgRow κ (filled κ L₀ (rootOf es)) (es ++ [x]) c :=
    fun c hc h => (algRow_agree hag κ _ c hc).mpr h
  have hpos : 1 ≤ es.length := List.length_pos_iff.mpr hne
  rcases pos_cover κ es.length hlen with h | h | ⟨j, hj1, hj2, h⟩ | h | ⟨l', hl', h⟩ |
      ⟨l', hl', h⟩ | ⟨l', hl', h⟩ | h | h | ⟨l', hl', h⟩ | ⟨l', hl', h⟩ | h | ⟨q, hq, h⟩ |
      ⟨l', hl', h⟩ | ⟨l', hl', h⟩ | h | ⟨j, hj1, hj2, h⟩
  · omega
  · -- `absorb(root)` after the seed: `FS` on both sides
    rw [h, posClass_root]
    rw [h, show (1 : ℕ) - 1 = 0 from rfl, posClass_seed] at ha
    exact Or.inr ((FS_agree hag (by omega)).mpr ha)
  · rw [h, shape_r0 κ j hj1 hj2] at hsh; cases hsh
  · -- `absorb(ū)` after R0 answer `m`
    have h2 : 2 ≤ es.length := by simp only [pU] at h; omega
    rw [hroot h2, h, posClass_ubar]
    rw [h, show pU κ - 1 = 1 + rows κ by simp only [pU]; omega, posClass_r0 κ (rows κ) (by unfold rows; exact Nat.one_le_two_pow) le_rfl] at ha
    have := tr (.r0 (rows κ)) (by simp only [posOfC, pU] at h ⊢; omega) ha
    simp only [AlgRow] at this ⊢
    rw [ite_eq_right (lt_irrefl _)] at this
    exact Or.inr this
  · rw [h, shape_tau κ l' hl'] at hsh; cases hsh
  · -- `absorb(g_l)`
    have h2 : 2 ≤ es.length := by simp only [pG] at h; omega
    rw [hroot h2]
    rcases l' with _ | l'
    · rw [h, posClass_gOut κ 0 hl']
      rw [h, show pG κ 0 - 1 = pTau κ (14 + κ) by simp only [pG, pTau]; omega,
        posClass_tau κ _ (by omega)] at ha
      have := tr (.tau (14 + κ)) (by simp only [posOfC, pG, pTau] at h ⊢; omega) ha
      exact Or.inr (absorb_g0 _ (by rw [hL1, h]) this)
    · rw [h, posClass_gOut κ _ hl']
      rw [h, show pG κ (l' + 1) - 1 = pG κ l' + 1 by simp only [pG]; omega,
        posClass_rx κ _ (by omega)] at ha
      exact Or.inr (tr (.rx l') (by simp only [posOfC, pG] at h ⊢; omega) ha)
  · rw [h, shape_rx κ l' hl'] at hsh; cases hsh
  · -- `absorb(v_A ‖ v_B ‖ v_C)`
    have h2 : 2 ≤ es.length := by simp only [pTri] at h; omega
    rw [hroot h2, h, posClass_tri]
    rw [h, show pTri κ - 1 = pG κ (14 + κ) + 1 by simp only [pG, pTri]; omega,
      posClass_rx κ _ (by omega)] at ha
    have := tr (.rx (14 + κ)) (by simp only [posOfC, pG, pTri] at h ⊢; omega) ha
    exact absorb_tri ev hk _ (by rw [hL1, h]) this
  · rw [h, shape_rho κ] at hsh; cases hsh
  · -- `absorb(g'_l)`
    have h2 : 2 ≤ es.length := by simp only [pGi, pTri] at h; omega
    rw [hroot h2]
    rcases l' with _ | l'
    · rw [h, posClass_gIn κ 0 hl']
      rw [h, show pGi κ 0 - 1 = pTri κ + 1 by simp only [pGi]; omega, posClass_rho] at ha
      exact Or.inr (tr .rho (by simp only [posOfC, pGi] at h ⊢; omega) ha)
    · rw [h, posClass_gIn κ _ hl']
      rw [h, show pGi κ (l' + 1) - 1 = pGi κ l' + 1 by simp only [pGi]; omega,
        posClass_ry κ _ (by omega)] at ha
      exact Or.inr (tr (.ry l') (by simp only [posOfC, pGi] at h ⊢; omega) ha)
  · rw [h, shape_ry κ l' hl'] at hsh; cases hsh
  · -- `absorb(slices)`
    have h2 : 2 ≤ es.length := by simp only [pS, pTri] at h; omega
    rw [hroot h2, h, posClass_sl]
    rw [h, show pS κ - 1 = pGi κ (14 + κ) + 1 by simp only [pGi, pS]; omega,
      posClass_ry κ _ (by omega)] at ha
    have := tr (.ry (14 + κ)) (by simp only [posOfC, pGi, pS] at h ⊢; omega) ha
    exact absorb_sl ev hev hm hk _ (by rw [hL1, h]) this
  · rw [h, shape_f κ q hq] at hsh; cases hsh
  · -- `absorb(g''_l)`
    have h2 : 2 ≤ es.length := by simp only [pGr, pS, pTri] at h; omega
    rw [hroot h2]
    rcases l' with _ | l'
    · rw [h, posClass_gRs κ 0 hl']
      rw [h, show pGr κ 0 - 1 = pF κ 5 by simp only [pGr, pF]; omega, posClass_f κ 5 (by omega)] at ha
      have := tr (.f 5) (by simp only [posOfC, pGr, pF] at h ⊢; omega) ha
      exact Or.inr (absorb_gR0 _ (by rw [hL1, h]) this)
    · rw [h, posClass_gRs κ _ hl']
      rw [h, show pGr κ (l' + 1) - 1 = pGr κ l' + 1 by simp only [pGr]; omega,
        posClass_rr κ _ (by omega)] at ha
      exact Or.inr (tr (.rr l') (by simp only [posOfC, pGr] at h ⊢; omega) ha)
  · rw [h, shape_rr κ l' hl'] at hsh; cases hsh
  · -- `absorb(v)`
    have h2 : 2 ≤ es.length := by simp only [pV, pS, pTri] at h; omega
    rw [hroot h2, h, posClass_vabs]
    rw [h, show pV κ - 1 = pGr κ (7 + κ) + 1 by simp only [pGr, pV]; omega,
      posClass_rr κ _ (by omega)] at ha
    have := tr (.rr (7 + κ)) (by simp only [posOfC, pGr, pV] at h ⊢; omega) ha
    exact absorb_v ev hk _ (by rw [hL1, h]) this
  · rw [h, shape_r7 κ j hj1 hj2] at hsh; cases hsh

end Absorb



/-! ## Part E: `esc_single_le` -/

section Single
open PCS Spartan SoundnessPCS RS

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

/-- A bound on a set of challenges under a hypothesis, as a fixed finite set. -/
theorem esc_of_bound {P : Prop} (f : EF → Prop) [DecidablePred f] {d : ℕ}
    (hcard : P → (Finset.univ.filter f).card ≤ d) :
    ∃ S : Finset EF, S.card ≤ d ∧ ∀ c, P → f c → c ∈ S := by
  by_cases hP : P
  · exact ⟨_, hcard hP, fun c _ hc => by simp [hc]⟩
  · exact ⟨∅, by simp, fun c h => absurd h hP⟩

/-- **`ubar → τ_0`** (S2b-M4): a false statement makes the residual table of `z_dec` nonzero, by
L-C2 `chain_sound` (`w_dec` is Boolean, `wDec_bool`) and `zc_start`. -/
theorem ftbl_ne_zero {es : Log} (hm : Matches es) {κ : ℕ} (hk : kapOf es = κ)
    (U : Fin (rows κ) → Fin (cols κ) → F) (hfs : FS es) :
    tbl (14 + κ + 1) (fTbl κ U es) ≠ 0 := by
  obtain ⟨s, n, h, h0, h1, -, -⟩ := (matches_iff' es).mp hm
  have hκ : κ = Nat.clog 2 n := by rw [← hk, kapOf_of h0]
  have hst : stmtOf es = (s, n, h) := by
    cases he : es[0]? with
    | none => rw [he] at h0; cases h0
    | some e =>
      rw [he, Option.bind_some] at h0
      simp [stmtOf, entAt, List.getD_eq_getElem?_getD, he, h0]
  apply zc_start
  intro hsat
  apply hfs
  rw [hst]
  refine chain_sound h1 (by rw [hκ]; exact (Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl)
    (w := fun u => EF.ofF (wDec κ U u)) (fun u => ?_) ?_
  · rcases wDec_bool κ U u with h' | h'
    · left; rw [h', ← EF.algebraMap_eq_ofF, map_zero]
    · right; rw [h', ← EF.algebraMap_eq_ofF, map_one]
  · unfold ChainSat
    have : zOfU κ U es = zOf (fun u => EF.ofF (wDec κ U u)) s h := by
      simp [zOfU, zDec, hst]
    have hA : matA κ es = chainA n κ := by simp only [matA, hst]
    rw [hA, this] at hsat
    exact hsat

/-- `τ_0` after `absorb(ū)`. -/
theorem esc_tau0 {es : Log} (hm : Matches es) {κ : ℕ} (hk : kapOf es = κ)
    (U : Fin (rows κ) → Fin (cols κ) → F) (hlen : es.length = pTau κ 0) :
    ∃ S : Finset EF, S.card ≤ 1 ∧ ∀ a, AlgRow κ U es .ubar →
      ¬ AlgRow κ U (ext1 es a) (.tau 0) → chE a ∈ S := by
  classical
  obtain ⟨S, hS, hmem⟩ := esc_of_bound (P := tbl (14 + κ + 1) (fTbl κ U es) ≠ 0)
    (fun c => tbl (14 + κ) (bind0 (fTbl κ U es) c) = 0)
    (fun hd => zc_escape_le _ (size_fTbl κ U es) hd)
  refine ⟨S, hS, fun a hold hnew => hmem _ (ftbl_ne_zero hm hk U ?_) ?_⟩
  · exact hold.1
  · have hag := agree_ext1 es a
    have hR : 1 + rows κ < es.length := by simp only [pTau] at hlen; omega
    simp only [AlgRow] at hold hnew
    rw [FarDoom_agree hag κ U hR, fTbl_agree hag (by omega)] at hnew
    have htk : (tauOf κ (ext1 es a)).take (0 + 1) = (tauOf κ es).take 0 ++ [chE a] :=
      take_snoc_ch es a (15 + κ) 0 (pTau κ) (by omega) hlen.symm (by omega)
    rw [htk] at hnew
    simp only [List.take_zero, List.nil_append, SpartanChain.bindT] at hnew
    obtain ⟨-, hor⟩ := hold
    by_contra hc
    apply hnew
    rcases hor with hf | hf
    · exact Or.inl hf
    · exact Or.inr ⟨hf, by rwa [show 14 + κ + 1 - 0 - 1 = 14 + κ by omega]⟩

/-- `τ_{l+1}` after `τ_l`. -/
theorem esc_tauS {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F) (l : ℕ)
    (hl : l + 1 < 15 + κ) (hlen : es.length = pTau κ (l + 1)) :
    ∃ S : Finset EF, S.card ≤ 1 ∧ ∀ a, AlgRow κ U es (.tau l) →
      ¬ AlgRow κ U (ext1 es a) (.tau (l + 1)) → chE a ∈ S := by
  classical
  set t := SpartanChain.bindT (fTbl κ U es) ((tauOf κ es).take (l + 1))
  have hsz : t.size = 2 ^ (13 + κ - l + 1) := by
    refine bindT_size _ _ ?_
    rw [size_fTbl, List.length_take, length_tauOf]; congr 1; omega
  obtain ⟨S, hS, hmem⟩ := esc_of_bound (P := tbl (13 + κ - l + 1) t ≠ 0)
    (fun c => tbl (13 + κ - l) (bind0 t c) = 0) (fun hd => zc_escape_le t hsz hd)
  refine ⟨S, hS, fun a hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pTau] at hlen; omega
  simp only [AlgRow] at hold hnew
  rw [FarDoom_agree hag κ U hR, fTbl_agree hag (by omega)] at hnew
  have htk : (tauOf κ (ext1 es a)).take (l + 1 + 1) = (tauOf κ es).take (l + 1) ++ [chE a] :=
    take_snoc_ch es a (15 + κ) (l + 1) (pTau κ) hl hlen.symm (fun l' hl' => by
      simp only [pTau] at hlen ⊢; omega)
  rw [htk, bindT_snoc] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  refine hmem _ ?_ ?_
  · rwa [show 14 + κ + 1 - l - 1 = 13 + κ - l + 1 by omega] at hd
  · by_contra hc
    exact hnew (Or.inr ⟨hF, by rwa [show 14 + κ + 1 - (l + 1) - 1 = 13 + κ - l by omega]⟩)

/-- One sumcheck round from a false claim, as a fixed set of escaping challenges (`round_escape_le`). -/
theorem esc_round (e : Expr) (ts : Array (Array EF)) (m : ℕ)
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) (claim : EF) (g : Array EF) :
    ∃ S : Finset EF, S.card ≤ e.deg ∧ ∀ c, claim ≠ trueSum e ts (m + 1) → RoundOK e.deg g claim →
      peval g c = trueSum e (ts.map (bind0 · c)) m → c ∈ S := by
  classical
  obtain ⟨S, hS, hmem⟩ := esc_of_bound (P := claim ≠ trueSum e ts (m + 1))
    (fun c => (g.size = e.deg + 1 ∧ peval g 0 + peval g 1 = claim) ∧
      peval g c = trueSum e (ts.map (bind0 · c)) m)
    (fun hf => round_escape_le e ts hts hf g)
  exact ⟨S, hS, fun c hf hok hc => hmem c hf ⟨hok, hc⟩⟩

/-- `r_{x,l}` after `absorb(g_l)`. -/
theorem esc_rx {es : Log} {κ : ℕ} (hk : kapOf es = κ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (l : ℕ) (hl : l < 15 + κ) (hlen : es.length = pG κ l + 1) :
    ∃ S : Finset EF, S.card ≤ 3 ∧ ∀ a, ¬ Rej ev es → AlgRow κ U es (.gOut l) →
      ¬ AlgRow κ U (ext1 es a) (.rx l) → chE a ∈ S := by
  classical
  have hsz := bindAll_sizes (oTbls κ U es) ((rxOf κ es).take l) (14 + κ - l + 1) (by
    rw [List.length_take, length_rxOf]; intro t ht; rw [oTbls_sizes κ U es t ht]; congr 1; omega)
  obtain ⟨S, hS, hmem⟩ := esc_round outerExpr _ _ hsz (clOut κ es l) (gOut κ es l)
  refine ⟨S, hS, fun a hrej hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pG] at hlen; omega
  simp only [AlgRow, SumWrong] at hold hnew
  rw [FarDoom_agree hag κ U hR, oTbls_agree hag (by omega) κ U (by simp only [pG] at *; omega)]
    at hnew
  have htk : (rxOf κ (ext1 es a)).take (l + 1) = (rxOf κ es).take l ++ [chE a] :=
    take_snoc_ch es a (15 + κ) l (fun l => pG κ l + 1) hl hlen.symm (fun l' hl' => by
      simp only [pG] at hlen ⊢; omega)
  have hcl : clOut κ (ext1 es a) (l + 1) = peval (gOut κ es l) (chE a) := by
    simp only [clOut]
    rw [gOut_agree hag κ l (by omega)]
    exact congrArg _ (getD_snoc_ch es a (15 + κ) l (fun l => pG κ l + 1) hl hlen.symm)
  rw [htk, bindAll_snoc, hcl] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  have hok : RoundOK 3 (gOut κ es l) (clOut κ es l) := by
    by_contra hc
    apply hrej
    simp only [Rej]
    rw [hk]
    exact Or.inl ⟨l, hl, by omega, hc⟩
  refine hmem _ ?_ hok ?_
  · rwa [show 14 + κ + 1 - l = 14 + κ - l + 1 by omega] at hd
  · by_contra hc
    exact hnew (Or.inr ⟨hF, by rwa [show 14 + κ + 1 - (l + 1) = 14 + κ - l by omega]⟩)

/-- `r_{y,l}` after `absorb(g'_l)`. -/
theorem esc_ry {es : Log} {κ : ℕ} (hk : kapOf es = κ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (l : ℕ) (hl : l < 15 + κ) (hlen : es.length = pGi κ l + 1) :
    ∃ S : Finset EF, S.card ≤ 2 ∧ ∀ a, ¬ Rej ev es → AlgRow κ U es (.gIn l) →
      ¬ AlgRow κ U (ext1 es a) (.ry l) → chE a ∈ S := by
  classical
  have hsz := bindAll_sizes (iTbls κ U es) ((ryOf κ es).take l) (14 + κ - l + 1) (by
    rw [List.length_take, length_ryOf]; intro t ht; rw [iTbls_sizes κ U es t ht]; congr 1; omega)
  obtain ⟨S, hS, hmem⟩ := esc_round innerExpr _ _ hsz (clIn κ es l) (gIn κ es l)
  refine ⟨S, hS, fun a hrej hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pGi, pTri] at hlen; omega
  simp only [AlgRow, SumWrong] at hold hnew
  rw [FarDoom_agree hag κ U hR, iTbls_agree hag (by omega) κ U (by simp only [pGi] at *; omega)]
    at hnew
  have htk : (ryOf κ (ext1 es a)).take (l + 1) = (ryOf κ es).take l ++ [chE a] :=
    take_snoc_ch es a (15 + κ) l (fun l => pGi κ l + 1) hl hlen.symm (fun l' hl' => by
      simp only [pGi] at hlen ⊢; omega)
  have hcl : clIn κ (ext1 es a) (l + 1) = peval (gIn κ es l) (chE a) := by
    simp only [clIn]
    rw [gIn_agree hag κ l (by omega)]
    exact congrArg _ (getD_snoc_ch es a (15 + κ) l (fun l => pGi κ l + 1) hl hlen.symm)
  rw [htk, bindAll_snoc, hcl] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  have hok : RoundOK 2 (gIn κ es l) (clIn κ es l) := by
    by_contra hc
    apply hrej
    simp only [Rej]
    rw [hk]
    exact Or.inr (Or.inr (Or.inl ⟨l, hl, by omega, hc⟩))
  refine hmem _ ?_ hok ?_
  · rwa [show 14 + κ + 1 - l = 14 + κ - l + 1 by omega] at hd
  · by_contra hc
    exact hnew (Or.inr ⟨hF, by rwa [show 14 + κ + 1 - (l + 1) = 14 + κ - l by omega]⟩)

/-- `r''_l` after `absorb(g''_l)`. -/
theorem esc_rr {es : Log} {κ : ℕ} (hk : kapOf es = κ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (l : ℕ) (hl : l < 8 + κ) (hlen : es.length = pGr κ l + 1) :
    ∃ S : Finset EF, S.card ≤ 2 ∧ ∀ a, ¬ Rej ev es → AlgRow κ U es (.gRs l) →
      ¬ AlgRow κ U (ext1 es a) (.rr l) → chE a ∈ S := by
  classical
  have hsz := bindAll_sizes (wTbls κ U es) ((rrOf κ es).take l) (7 + κ - l + 1) (by
    rw [List.length_take, length_rrOf]; intro t ht; rw [wTbls_sizes κ U es t ht]; congr 1; omega)
  obtain ⟨S, hS, hmem⟩ := esc_round innerExpr _ _ hsz (clRs κ es l) (gRs κ es l)
  refine ⟨S, hS, fun a hrej hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pGr, pS, pTri] at hlen; omega
  simp only [AlgRow, SumWrong] at hold hnew
  rw [FarDoom_agree hag κ U hR, wTbls_agree hag κ U (by simp only [pGr] at *; omega)] at hnew
  have htk : (rrOf κ (ext1 es a)).take (l + 1) = (rrOf κ es).take l ++ [chE a] :=
    take_snoc_ch es a (8 + κ) l (fun l => pGr κ l + 1) hl hlen.symm (fun l' hl' => by
      simp only [pGr] at hlen ⊢; omega)
  have hcl : clRs κ (ext1 es a) (l + 1) = peval (gRs κ es l) (chE a) := by
    simp only [clRs]
    rw [gRs_agree hag κ l (by omega)]
    exact congrArg _ (getD_snoc_ch es a (8 + κ) l (fun l => pGr κ l + 1) hl hlen.symm)
  rw [htk, bindAll_snoc, hcl] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  have hok : RoundOK 2 (gRs κ es l) (clRs κ es l) := by
    by_contra hc
    apply hrej
    simp only [Rej]
    rw [hk]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, by omega, hc⟩))))
  refine hmem _ ?_ hok ?_
  · rwa [show 8 + κ - l = 7 + κ - l + 1 by omega] at hd
  · by_contra hc
    exact hnew (Or.inr ⟨hF, by rwa [show 8 + κ - (l + 1) = 7 + κ - l by omega]⟩)

/-- `ρ` after `absorb(v_A ‖ v_B ‖ v_C)`: `batch_escape_le`. -/
theorem esc_rho {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pTri κ + 1) :
    ∃ S : Finset EF, S.card ≤ 2 ∧ ∀ a, AlgRow κ U es .tri →
      ¬ AlgRow κ U (ext1 es a) .rho → chE a ∈ S := by
  classical
  set rx := ptOf (14 + κ + 1) (rxOf κ es)
  set z := zOfU κ U es
  obtain ⟨S, hS, hmem⟩ := esc_of_bound (P := triOf κ es ≠ (mle (matVec (matA κ es) z) rx,
      mle (matVec (matB κ) z) rx, mle (matVec (matC κ) z) rx))
    (fun ρ => (triOf κ es).1 + ρ * (triOf κ es).2.1 + ρ ^ 2 * (triOf κ es).2.2 =
      trueSum innerExpr (innerTables rx ρ (matA κ es) (matB κ) (matC κ) z) (14 + κ + 1))
    (fun h => batch_escape_le rx _ _ _ z h)
  refine ⟨S, hS, fun a hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pTri] at hlen; omega
  simp only [AlgRow, SumWrong] at hold hnew
  rw [FarDoom_agree hag κ U hR] at hnew
  have hrho : rhoOf κ (ext1 es a) = chE a := by
    unfold rhoOf; rw [← hlen, chAt_ext1]
  have hIT : iTbls κ U (ext1 es a) = innerTables rx (chE a) (matA κ es) (matB κ) (matC κ) z := by
    unfold iTbls
    rw [rxOf_agree hag κ (by omega), hrho, matA_agree hag (by omega), zOfU_agree hag (by omega)]
  have hcl : clIn κ (ext1 es a) 0 = (triOf κ es).1 + chE a * (triOf κ es).2.1 +
      chE a ^ 2 * (triOf κ es).2.2 := by
    simp only [clIn]; rw [triOf_agree hag κ (by omega), hrho]
  rw [hIT, hcl] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  refine hmem _ hd ?_
  by_contra hc
  exact hnew (Or.inr ⟨hF, by simpa [bindAll] using hc⟩)

/-- `f_0` after `absorb(slices)`: L-R1 `ring_inj_EF`, `rs_start`, `rs_escape_le`. -/
theorem esc_f0 {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F)
    (hlen : es.length = pF κ 0) :
    ∃ S : Finset EF, S.card ≤ 1 ∧ ∀ a, AlgRow κ U es .sl →
      ¬ AlgRow κ U (ext1 es a) (.f 0) → chE a ∈ S := by
  classical
  obtain ⟨S, hS, hmem⟩ := esc_of_bound (P := rsDoom wX (deltaOf κ U es) 5 [])
    (fun f => ¬ rsDoom wX (deltaOf κ U es) 5 ([] ++ [f]))
    (fun h => rs_escape_le wX _ 5 [] (by norm_num) h)
  refine ⟨S, hS, fun a hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pF, pS, pTri] at hlen; omega
  simp only [AlgRow] at hold hnew
  rw [FarDoom_agree hag κ U hR, deltaOf_agree hag κ U (by simp only [pF] at hlen; omega)] at hnew
  have htk : (fsOf κ (ext1 es a)).take (0 + 1) = (fsOf κ es).take 0 ++ [chE a] :=
    take_snoc_ch es a 6 0 (pF κ) (by omega) hlen.symm (by omega)
  rw [htk] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  refine hmem _ (rs_start _ _ 5 ?_) ?_
  · obtain ⟨k, hk, hne⟩ := ring_inj_EF (deltaOf κ U es) hd
    exact ⟨k, by norm_num; omega, hne⟩
  · by_contra hc
    exact hnew (Or.inr ⟨hF, by simpa using hc⟩)

/-- `f_{q+1}` after `f_q`: `rs_escape_le`. -/
theorem esc_fS {es : Log} {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F) (q : ℕ)
    (hq : q + 1 < 6) (hlen : es.length = pF κ (q + 1)) :
    ∃ S : Finset EF, S.card ≤ 1 ∧ ∀ a, AlgRow κ U es (.f q) →
      ¬ AlgRow κ U (ext1 es a) (.f (q + 1)) → chE a ∈ S := by
  classical
  obtain ⟨S, hS, hmem⟩ := esc_of_bound
    (P := rsDoom wX (deltaOf κ U es) 5 ((fsOf κ es).take (q + 1)))
    (fun f => ¬ rsDoom wX (deltaOf κ U es) 5 ((fsOf κ es).take (q + 1) ++ [f]))
    (fun h => rs_escape_le wX _ 5 _ (by rw [List.length_take, length_fsOf]; omega) h)
  refine ⟨S, hS, fun a hold hnew => ?_⟩
  have hag := agree_ext1 es a
  have hR : 1 + rows κ < es.length := by simp only [pF, pS, pTri] at hlen; omega
  simp only [AlgRow] at hold hnew
  rw [FarDoom_agree hag κ U hR, deltaOf_agree hag κ U (by simp only [pF] at hlen; omega)] at hnew
  have htk : (fsOf κ (ext1 es a)).take (q + 1 + 1) = (fsOf κ es).take (q + 1) ++ [chE a] :=
    take_snoc_ch es a 6 (q + 1) (pF κ) hq hlen.symm (fun l hl => by
      simp only [pF] at hlen ⊢; omega)
  rw [htk] at hnew
  rcases hold with hf | ⟨hF, hd⟩
  · exact absurd (Or.inl hf) hnew
  refine hmem _ hd ?_
  by_contra hc
  exact hnew (Or.inr ⟨hF, by simpa using hc⟩)

set_option linter.constructorNameAsVariable false in
open Classical in
/-- The count of single-answer escapes from a set of escaping challenges (`card_chE_mem`). -/
theorem esc_card (L₀ es : Log) {κ : ℕ} (hk : kapOf es = κ) (h2 : 2 ≤ es.length)
    (S : Finset EF) (hS : S.card ≤ 3)
    (hesc : ∀ a, ¬ Rej ev es →
      AlgRow κ (filled κ L₀ (rootOf es)) es (posClass κ (es.length - 1)) →
      ¬ AlgRow κ (filled κ L₀ (rootOf es)) (ext1 es a) (posClass κ es.length) → chE a ∈ S) :
    (Finset.univ.filter fun a => Doom ev L₀ es ∧ ¬ Doom ev L₀ (ext1 es a)).card ≤ 3 * 2 ^ 64 := by
  classical
  have hne : es ≠ [] := by rintro rfl; simp at h2
  calc (Finset.univ.filter fun a => Doom ev L₀ es ∧ ¬ Doom ev L₀ (ext1 es a)).card
      ≤ (Finset.univ.filter fun a : Digest => chE a ∈ S).card := by
        refine Finset.card_le_card fun a ha => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        obtain ⟨hd, hnd⟩ := ha
        have hk' : kapOf (ext1 es a) = κ := (kapOf_append hne _).trans hk
        have hroot : rootOf (ext1 es a) = rootOf es := rootOf_agree (agree_ext1 es a) (by omega)
        have hl : (ext1 es a).length - 1 = es.length := by simp [ext1]
        rw [doom_iff ev hk] at hd
        rw [doom_iff ev hk', hroot, hl] at hnd
        have hnr : ¬ Rej ev es := fun h => hnd (Or.inl (rej_mono ev hne _ h))
        exact hesc a hnr (hd.resolve_left hnr) (fun h => hnd (Or.inr h))
    _ = S.card * 2 ^ 64 := card_chE_mem S
    _ ≤ 3 * 2 ^ 64 := Nat.mul_le_mul_right _ hS

theorem rnd_ne_none_r0 (κ j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ rows κ) : rnd κ (1 + j) ≠ none := by
  unfold rnd; rw [ite_eq_left ⟨by omega, by omega⟩]; simp

theorem rnd_ne_none_r7 (κ j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ nJ κ) : rnd κ (pV κ + j) ≠ none := by
  have := pre8_pV κ
  have := len_pV κ
  unfold rnd
  by_cases hc : 2 ≤ pV κ + j ∧ pV κ + j ≤ 1 + rows κ
  · rw [ite_eq_left hc]; simp
  · rw [ite_eq_right hc, ite_eq_left ⟨by omega, by omega⟩]; simp

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **`esc_single_le`** (§9.2): at a single-answer squeeze, at most `3 · 2^64` answers escape. -/
theorem esc_single_le (L₀ es : Log) (hm : Matches es)
    (hsq : (shape (kapOf es))[es.length]? = some .squeeze) (hr : rnd (kapOf es) es.length = none) :
    (Finset.univ.filter fun a => Doom ev L₀ es ∧ ¬ Doom ev L₀ (ext1 es a)).card ≤ 3 * 2 ^ 64 := by
  have hne := matches_ne_nil hm
  obtain ⟨κ, hκ⟩ : ∃ κ, kapOf es = κ := ⟨_, rfl⟩
  rw [hκ] at hsq hr
  have hlen : es.length < len κ := by
    by_contra hc
    rw [List.getElem?_eq_none (by unfold len at hc; omega)] at hsq
    cases hsq
  have hpos : 1 ≤ es.length := List.length_pos_iff.mpr hne
  have hle3 : ∀ d, d ≤ 3 → ∀ S : Finset EF, S.card ≤ d → S.card ≤ 3 := fun d hd S h => h.trans hd
  rcases pos_cover κ es.length hlen with h | h | ⟨j, hj1, hj2, h⟩ | h | ⟨l, hl, h⟩ |
      ⟨l, hl, h⟩ | ⟨l, hl, h⟩ | h | h | ⟨l, hl, h⟩ | ⟨l, hl, h⟩ | h | ⟨q, hq, h⟩ |
      ⟨l, hl, h⟩ | ⟨l, hl, h⟩ | h | ⟨j, hj1, hj2, h⟩
  · omega
  · rw [h, shape_root] at hsq; cases hsq
  · exact absurd (h ▸ hr) (rnd_ne_none_r0 κ j hj1 hj2)
  · rw [h, shape_ubar] at hsq; cases hsq
  · -- `τ_l`
    have h2 : 2 ≤ es.length := by simp only [pTau] at h; omega
    rcases l with _ | l
    · obtain ⟨S, hS, hesc⟩ := esc_tau0 hm hκ (filled κ L₀ (rootOf es)) h
      refine esc_card ev L₀ es hκ h2 S (hle3 1 (by omega) S hS) fun a _ hold hnew => ?_
      rw [h, show pTau κ 0 - 1 = pU κ by simp only [pTau, pU]; omega, posClass_ubar] at hold
      rw [h, posClass_tau κ 0 hl] at hnew
      exact hesc a hold hnew
    · obtain ⟨S, hS, hesc⟩ := esc_tauS (filled κ L₀ (rootOf es)) l hl h
      refine esc_card ev L₀ es hκ h2 S (hle3 1 (by omega) S hS) fun a _ hold hnew => ?_
      rw [h, show pTau κ (l + 1) - 1 = pTau κ l by simp only [pTau]; omega,
        posClass_tau κ l (by omega)] at hold
      rw [h, posClass_tau κ _ hl] at hnew
      exact hesc a hold hnew
  · rw [h, shape_gOut κ l hl] at hsq; cases hsq
  · -- `r_{x,l}`
    have h2 : 2 ≤ es.length := by simp only [pG] at h; omega
    obtain ⟨S, hS, hesc⟩ := esc_rx ev hκ (filled κ L₀ (rootOf es)) l hl h
    refine esc_card ev L₀ es hκ h2 S hS fun a hrej hold hnew => ?_
    rw [h, show pG κ l + 1 - 1 = pG κ l by omega, posClass_gOut κ l hl] at hold
    rw [h, posClass_rx κ l hl] at hnew
    exact hesc a hrej hold hnew
  · rw [h, shape_tri] at hsq; cases hsq
  · -- `ρ`
    have h2 : 2 ≤ es.length := by simp only [pTri] at h; omega
    obtain ⟨S, hS, hesc⟩ := esc_rho (filled κ L₀ (rootOf es)) h
    refine esc_card ev L₀ es hκ h2 S (hle3 2 (by omega) S hS) fun a _ hold hnew => ?_
    rw [h, show pTri κ + 1 - 1 = pTri κ by omega, posClass_tri] at hold
    rw [h, posClass_rho] at hnew
    exact hesc a hold hnew
  · rw [h, shape_gIn κ l hl] at hsq; cases hsq
  · -- `r_{y,l}`
    have h2 : 2 ≤ es.length := by simp only [pGi, pTri] at h; omega
    obtain ⟨S, hS, hesc⟩ := esc_ry ev hκ (filled κ L₀ (rootOf es)) l hl h
    refine esc_card ev L₀ es hκ h2 S (hle3 2 (by omega) S hS) fun a hrej hold hnew => ?_
    rw [h, show pGi κ l + 1 - 1 = pGi κ l by omega, posClass_gIn κ l hl] at hold
    rw [h, posClass_ry κ l hl] at hnew
    exact hesc a hrej hold hnew
  · rw [h, shape_sl] at hsq; cases hsq
  · -- `f_q`
    have h2 : 2 ≤ es.length := by simp only [pF, pS, pTri] at h; omega
    rcases q with _ | q
    · obtain ⟨S, hS, hesc⟩ := esc_f0 (filled κ L₀ (rootOf es)) h
      refine esc_card ev L₀ es hκ h2 S (hle3 1 (by omega) S hS) fun a _ hold hnew => ?_
      rw [h, show pF κ 0 - 1 = pS κ by simp only [pF]; omega, posClass_sl] at hold
      rw [h, posClass_f κ 0 hq] at hnew
      exact hesc a hold hnew
    · obtain ⟨S, hS, hesc⟩ := esc_fS (filled κ L₀ (rootOf es)) q hq h
      refine esc_card ev L₀ es hκ h2 S (hle3 1 (by omega) S hS) fun a _ hold hnew => ?_
      rw [h, show pF κ (q + 1) - 1 = pF κ q by simp only [pF]; omega,
        posClass_f κ q (by omega)] at hold
      rw [h, posClass_f κ _ hq] at hnew
      exact hesc a hold hnew
  · rw [h, shape_gRs κ l hl] at hsq; cases hsq
  · -- `r''_l`
    have h2 : 2 ≤ es.length := by simp only [pGr, pS, pTri] at h; omega
    obtain ⟨S, hS, hesc⟩ := esc_rr ev hκ (filled κ L₀ (rootOf es)) l hl h
    refine esc_card ev L₀ es hκ h2 S (hle3 2 (by omega) S hS) fun a hrej hold hnew => ?_
    rw [h, show pGr κ l + 1 - 1 = pGr κ l by omega, posClass_gRs κ l hl] at hold
    rw [h, posClass_rr κ l hl] at hnew
    exact hesc a hrej hold hnew
  · rw [h, shape_vabs] at hsq; cases hsq
  · exact absurd (h ▸ hr) (rnd_ne_none_r7 κ j hj1 hj2)

end Single


/-! ## The verifier's evaluators satisfy `EvalsOK` -/

section ChainEvals
open PCS Spartan

theorem mle_nat_cast {n m : ℕ} (h : n = m) (f : ℕ → EF) (r : List EF) :
    mle (fun u : Fin (2 ^ n) => f u.val) (ptOf n r) = mle (fun u : Fin (2 ^ m) => f u.val) (ptOf m r) := by
  subst h; rfl

theorem matMle_chain' {L : ℕ} (hL : ly L = 14 + L + 1) (M : Ix L → Ix L → EF) (rx ry : List EF) :
    matMle (fun x y : Fin (2 ^ ly L) => M (Fin.cast (by rw [hL]) x) (Fin.cast (by rw [hL]) y))
      (ptOf (ly L) rx) (ptOf (ly L) ry) = matMle M (ptOf (14 + L + 1) rx) (ptOf (14 + L + 1) ry) := by
  rw [matMle_cast hL M]
  rfl

theorem pub_cast (κ : ℕ) (s h : Digest) (ru : List EF) :
    mle (fun u : Fin (2 ^ lu κ) => pubVal (E := EF) s h u.val) (ptOf (lu κ) ru) =
      mle (fun u : Fin (2 ^ (14 + κ)) => pubVal (E := EF) s h u.val) (ptOf (14 + κ) ru) :=
  mle_nat_cast (lu_eq κ) _ ru

/-- **`chainEvals` are the extensions** of the chain R1CS (`chainMats_eq`, `chainPub_eq`). -/
theorem chainEvals_ok : EvalsOK chainEvals where
  mats κ n s h rx ry hn1 hn2 hx hy := by
    show chainMats n κ rx ry = _
    rw [chainMats_eq hn1 hn2 rx ry (by rw [hx, ly_eq]; omega) (by rw [hy, ly_eq]; omega)]
    unfold chainA' chainB' chainC' castIx
    rw [matMle_chain' (ly_eq κ) (chainA n κ), matMle_chain' (ly_eq κ) (chainB κ),
      matMle_chain' (ly_eq κ) (chainC κ)]
  pub κ n s h ru _ := by
    rw [show (chainEvals κ n s h).pub ru = chainPub κ s h ru by simp only [chainEvals]]
    exact (chainPub_eq κ s h ru).trans (pub_cast κ s h ru)

end ChainEvals

/-! ## `mu_step`: the contract's `step` law for `μ` -/

/-- **`mu_step`** (§9.3): for evaluators that are the extensions of the chain R1CS (`EvalsOK`),
`Σ_a μ(L ++ [(q, a)]) ≤ (μ L + 2^-129) · 2^256` for a fresh query on a log below `logCap` with
`μ L < 1`. -/
theorem mu_step (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (hev : EvalsOK ev) {L : Log}
    {q : ByteArray} (hl : L.length < logCap) (hμ : μ ev L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, μ ev (L ++ [(q, a)]) ≤ (μ ev L + εKS) * 2 ^ 256 :=
  muG_step_of (D := Doom ev)
    (fun L₀ es x k l hm hsh hd => doom_absorb ev hev L₀ es x k l hm hsh hd)
    (fun L₀ es x s0 r hm hr hlt => doom_mid ev L₀ es x s0 r hm hr hlt)
    (fun L₀ es hm hsq hr => esc_single_le ev L₀ es hm hsq hr)
    (fun L₀ es₀ s0 r hm hlen hr => round_le ev L₀ es₀ s0 r hm hlen hr) hl hμ hq

theorem mu_empty (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) : μ ev [] = 0 :=
  muG_empty _ _

/-- **`mu_step` for the verifier's evaluators** `chainEvals`. -/
theorem mu_step_chain {L : Log} {q : ByteArray} (hl : L.length < logCap)
    (hμ : μ chainEvals L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, μ chainEvals (L ++ [(q, a)]) ≤ (μ chainEvals L + εKS) * 2 ^ 256 :=
  mu_step chainEvals chainEvals_ok hl hμ hq

end KS

end SpartanChain
