import SpartanChainRS
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Proximity of the committed matrix (blueprint §5.5, L-RS2 … L-RS4)

Generic over a linear code `C ⊆ E^ι` with minimum distance `≥ d` (`RS.MinDist`); the protocol
instantiates `C := RS.rsCode` (`RS.code_dist`) over `E := EF`.

* `Close C e w`: `w` is within Hamming distance `e` of `C`.
* `IsDecomp C U e S c` / `eClose C U e`: the rows of `U` agree with codewords `c i` outside one
  common set `S` of at most `e` columns.
* **L-RS2** `far_bad_le` (AHIV22 Lemmas 4.3–4.5, counting form): if `U` is not `e`-close,
  `3e < d` and `d < |E|`, at most `d·|E|^{m−1}` of the `|E|^m` coefficient vectors `r` make
  `Σ_i r_i U_i` `e`-close to `C`. Proved from `line_close` (the affine-line lemma),
  `exists_far_comb` (a far word in the row span) and a double count; `far_bad_card` is the
  sharper `(e+1)·|E|^{m−1}`.
* **L-RS3** `miss_card`, `miss_le`, `miss_le_rat`: index tuples avoiding a set.
* **L-RS4** `close_unique`, `close_in_K`.

The argument follows ArkLib's `ProximityGap/AHIV22.lean` (ArkLib `7653a90`,
`exists_codewords_agree_of_many_close_scalars`, `prob_of_bad_pts`) as a guide; nothing is copied.
The row-span lemma (`exists_far_comb`) is proved here by a row-by-row induction instead of
ArkLib's maximal-support argument.
-/

namespace SpartanChain.RS

open Finset

variable {E : Type*} [Field E] [DecidableEq E] {ι : Type*} [Fintype ι]

/-- `w` is within Hamming distance `e` of the code `C`. -/
def Close (C : Submodule E (ι → E)) (e : ℕ) (w : ι → E) : Prop := ∃ c ∈ C, hammingDist w c ≤ e

/-- `(S, c)` exhibits `U` as `e`-close: `|S| ≤ e`, every `c i ∈ C`, and `U i = c i` off `S`. -/
def IsDecomp {m : ℕ} (C : Submodule E (ι → E)) (U : Fin m → ι → E) (e : ℕ) (S : Finset ι)
    (c : Fin m → ι → E) : Prop :=
  S.card ≤ e ∧ (∀ i, c i ∈ C) ∧ ∀ i, ∀ x ∉ S, U i x = c i x

/-- **`eClose`** (§5.5): the rows of `U` agree with codewords off a common set of `≤ e`
columns. -/
def eClose {m : ℕ} (C : Submodule E (ι → E)) (U : Fin m → ι → E) (e : ℕ) : Prop :=
  ∃ S c, IsDecomp C U e S c

/-- A word within distance `e` of `c` agrees with it off a set of `≤ e` positions. -/
theorem close_iff_agree {C : Submodule E (ι → E)} {e : ℕ} {w : ι → E} :
    Close C e w ↔ ∃ c ∈ C, ∃ T : Finset ι, T.card ≤ e ∧ ∀ x ∉ T, w x = c x := by
  constructor
  · rintro ⟨c, hc, hd⟩
    exact ⟨c, hc, univ.filter fun x => w x ≠ c x, hd, fun x hx => by simpa using hx⟩
  · rintro ⟨c, hc, T, hT, h⟩
    refine ⟨c, hc, le_trans (card_le_card fun x hx => ?_) hT⟩
    by_contra hxT; exact (mem_filter.1 hx).2 (h x hxT)

/-- At a position where `(a, b) ≠ (a', b')`, `a + α b = a' + α b'` for at most one `α`. -/
theorem affine_eq_unique {a b a' b' α β : E} (hab : a ≠ a' ∨ b ≠ b')
    (hα : a + α * b = a' + α * b') (hβ : a + β * b = a' + β * b') : α = β := by
  by_contra hne
  have hb : b = b' := by
    have : (α - β) * (b - b') = 0 := by linear_combination hα - hβ
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  subst hb
  exact hab.elim (fun h => h (by linear_combination hα)) (fun h => h rfl)

variable {C : Submodule E (ι → E)} {d e : ℕ}

/-- **Affine-line lemma** (AHIV22 Lemma 4.3/4.4 core). If `3e < d` and `u + α v` is `e`-close
to `C` for more than `e + 1` scalars `α`, then `u` and `v` agree with codewords `u'`, `v'` off a
common set of at most `e` positions. -/
theorem line_close (hC : MinDist C d) (h3 : 3 * e < d) {u v : ι → E} (A : Finset E)
    (hA : e + 1 < A.card) (hcl : ∀ α ∈ A, Close C e (u + α • v)) :
    ∃ u' ∈ C, ∃ v' ∈ C, ∃ D : Finset ι, D.card ≤ e ∧ ∀ x ∉ D, u x = u' x ∧ v x = v' x := by
  classical
  have hcl' : ∀ α : A, ∃ c ∈ C, ∃ T : Finset ι, T.card ≤ e ∧ ∀ x ∉ T, u x + α * v x = c x :=
    fun α => by simpa using close_iff_agree.1 (hcl α α.2)
  choose c hcC T hT hagree using hcl'
  obtain ⟨α₁, hα₁, α₂, hα₂, h12⟩ := one_lt_card.1 (by omega : 1 < A.card)
  set a₁ : A := ⟨α₁, hα₁⟩
  set a₂ : A := ⟨α₂, hα₂⟩
  -- the direction and base codewords through the two decoded points
  set v' : ι → E := (α₁ - α₂)⁻¹ • (c a₁ - c a₂)
  set u' : ι → E := c a₁ - α₁ • v'
  have hv'C : v' ∈ C := C.smul_mem _ (C.sub_mem (hcC a₁) (hcC a₂))
  have hu'C : u' ∈ C := C.sub_mem (hcC a₁) (C.smul_mem _ hv'C)
  have hsub : α₁ - α₂ ≠ 0 := sub_ne_zero.2 h12
  -- off `T a₁ ∪ T a₂`, `(u, v) = (u', v')`
  have hbase : ∀ x, x ∉ T a₁ → x ∉ T a₂ → u x = u' x ∧ v x = v' x := by
    intro x h1 h2
    have e1 := hagree a₁ x h1
    have e2 := hagree a₂ x h2
    have hv : v x = v' x := by
      simp only [v', Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← e1, ← e2]
      field_simp; ring
    refine ⟨?_, hv⟩
    simp only [u', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv, ← e1]; ring
  -- every decoded point lies on the codeword line
  have hline : ∀ α : A, c α = u' + (α : E) • v' := by
    intro α
    have h3c : (T a₁ ∪ T a₂ ∪ T α).card < d := by
      have := card_union_le (T a₁ ∪ T a₂) (T α); have := card_union_le (T a₁) (T a₂)
      have := hT a₁; have := hT a₂; have := hT α; omega
    refine hC.eq_of_agree (hcC α) (C.add_mem hu'C (C.smul_mem _ hv'C)) _ h3c fun x hx => ?_
    simp only [mem_union, not_or] at hx
    obtain ⟨b1, b2⟩ := hbase x hx.1.1 hx.1.2
    rw [← hagree α x hx.2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, b1, b2]
  -- the double count
  let D := univ.filter fun x => u x ≠ u' x ∨ v x ≠ v' x
  let r : ι → E → Prop := fun x α => u x + α * v x ≠ u' x + α * v' x
  have hrow : ∀ x ∈ D, A.card - 1 ≤ (A.bipartiteAbove r x).card := by
    intro x hx
    have hx' : u x ≠ u' x ∨ v x ≠ v' x := (mem_filter.1 hx).2
    have hle : (A.filter fun α => ¬ r x α).card ≤ 1 :=
      card_le_one.2 fun α hα β hβ => affine_eq_unique hx' (by simpa [r] using (mem_filter.1 hα).2)
        (by simpa [r] using (mem_filter.1 hβ).2)
    have hsplit : (A.bipartiteAbove r x).card + (A.filter fun α => ¬ r x α).card = A.card := by
      unfold bipartiteAbove; exact card_filter_add_card_filter_not _
    omega
  have hcol : ∀ α ∈ A, (D.bipartiteBelow r α).card ≤ e := by
    intro α hα
    refine le_trans (card_le_card fun x hx => ?_) (hT ⟨α, hα⟩)
    simp only [bipartiteBelow, mem_filter] at hx
    by_contra hxT
    apply hx.2
    have := hagree ⟨α, hα⟩ x hxT
    rw [this, hline ⟨α, hα⟩]; simp
  have hdc := card_mul_le_card_mul r hrow hcol
  refine ⟨u', hu'C, v', hv'C, D, ?_, fun x hx => by simpa [D] using hx⟩
  by_contra hD
  have hAe : e + 1 ≤ A.card - 1 := by omega
  have : (e + 1) * (A.card - 1) ≤ A.card * e :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hdc
  have : A.card - 1 + 1 = A.card := by omega
  nlinarith

/-- Two decompositions of the same `U` have the same codewords when `2e < d`. -/
theorem close_unique {m : ℕ} (hC : MinDist C d) (h2 : 2 * e < d) {U : Fin m → ι → E}
    {S S' : Finset ι} {c c' : Fin m → ι → E} (h : IsDecomp C U e S c)
    (h' : IsDecomp C U e S' c') : c = c' := by
  classical
  funext i
  refine hC.eq_of_agree (h.2.1 i) (h'.2.1 i) (S ∪ S')
    (lt_of_le_of_lt (card_union_le _ _) (by have := h.1; have := h'.1; omega)) fun x hx => ?_
  simp only [mem_union, not_or] at hx
  rw [← h.2.2 i x hx.1, h'.2.2 i x hx.2]

omit [DecidableEq E] [Fintype ι] in
/-- A combination of a decomposed `U` agrees with the same combination of its codewords off
`S`, and that combination is a codeword (§5.5, close case). -/
theorem IsDecomp.comb {m : ℕ} {U : Fin m → ι → E} {S : Finset ι} {c : Fin m → ι → E}
    (h : IsDecomp C U e S c) (a : Fin m → E) :
    ∑ i, a i • c i ∈ C ∧ ∀ x ∉ S, (∑ i, a i • U i) x = (∑ i, a i • c i) x := by
  refine ⟨C.sum_mem fun i _ => C.smul_mem _ (h.2.1 i), fun x hx => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply, h.2.2 _ x hx]

/-- A codeword `c` other than the codeword `c'` that `w` agrees with off `S` is at distance at
least `d − |S|` from `w` (§5.5: a wrong `v` is caught in `≥ d − e` columns). -/
theorem dist_ge_of_agree (hC : MinDist C d) {c c' w : ι → E} (hc : c ∈ C) (hc' : c' ∈ C)
    (hne : c ≠ c') {S : Finset ι} (hS : ∀ x ∉ S, w x = c' x) : d ≤ hammingDist c w + S.card := by
  have h1 := hC.le_dist hc hc' hne
  have h2 : hammingDist w c' ≤ S.card := by
    unfold hammingDist
    exact card_le_card fun x hx => by
      by_contra hxS; exact (mem_filter.1 hx).2 (hS x hxS)
  have := hammingDist_triangle c w c'
  omega

/-- **Row-span lemma** (AHIV22 Lemma 4.3 of the journal version): if `U` is not `e`-close,
`3e < d` and `e + 1 < |E|`, some combination `Σ_i s_i U_i` is not `e`-close to `C`. -/
theorem exists_far_comb [Fintype E] (hC : MinDist C d) (h3 : 3 * e < d)
    (hE : e + 1 < Fintype.card E) {m : ℕ} (U : Fin m → ι → E) (hfar : ¬ eClose C U e) :
    ∃ s : Fin m → E, ¬ Close C e (∑ i, s i • U i) := by
  classical
  by_contra hall
  push Not at hall
  apply hfar
  -- invariant after `j` rows: codewords `c`, a row-span word `Σ β_i U_i` and a codeword `ĉ` that
  -- disagree exactly on the joint disagreement set `S j c` of the first `j` rows
  let S : ℕ → (Fin m → ι → E) → Finset ι := fun j c =>
    univ.filter fun x => ∃ i : Fin m, (i : ℕ) < j ∧ U i x ≠ c i x
  have key : ∀ j ≤ m, ∃ c : Fin m → ι → E, (∀ i, c i ∈ C) ∧ (S j c).card ≤ e ∧
      ∃ β : Fin m → E, ∃ ĉ ∈ C, ∀ x, x ∈ S j c ↔ (∑ i, β i • U i) x ≠ ĉ x := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨0, fun _ => C.zero_mem, by simp [S], 0, 0, C.zero_mem, fun x => by simp [S]⟩
    | succ j ih =>
      intro hj
      obtain ⟨c, hcC, hS, β, ĉ, hĉ, hSx⟩ := ih (by omega)
      set jj : Fin m := ⟨j, by omega⟩
      set u := ∑ i, β i • U i
      -- every point of the line `u + α U_j` is in the row span, hence close
      have hline : ∀ α ∈ (univ : Finset E), Close C e (u + α • U jj) := by
        intro α _
        have := hall (β + α • Pi.single jj 1)
        convert this using 1
        simp [u, add_smul, sum_add_distrib, Pi.single_apply, ite_smul]
      obtain ⟨u', hu', v', hv', D, hD, hDx⟩ :=
        line_close hC h3 (A := univ) (by simpa using hE) hline
      -- the line's base codeword is `ĉ`, so the old disagreement set lies in `D`
      have hu'ĉ : u' = ĉ := by
        refine hC.eq_of_agree hu' hĉ (D ∪ S j c)
          (lt_of_le_of_lt (card_union_le _ _) (by omega)) fun x hx => ?_
        simp only [mem_union, not_or] at hx
        rw [← (hDx x hx.1).1]; by_contra h; exact hx.2 ((hSx x).2 h)
      subst hu'ĉ
      let c' := Function.update c jj v'
      have hS' : ∀ x, x ∈ S (j + 1) c' ↔ x ∈ S j c ∨ U jj x ≠ v' x := by
        intro x
        simp only [S, mem_filter, mem_univ, true_and, c']
        constructor
        · rintro ⟨i, hi, hne⟩
          by_cases hij : i = jj
          · subst hij; right; simpa using hne
          · left
            have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            exact ⟨i, by omega, by simpa [Function.update_of_ne hij] using hne⟩
        · rintro (⟨i, hi, hne⟩ | hne)
          · have hij : i ≠ jj := fun h => by rw [h] at hi; simp [jj] at hi
            exact ⟨i, by omega, by simpa [Function.update_of_ne hij] using hne⟩
          · exact ⟨jj, by simp [jj], by simpa using hne⟩
      have hS'D : S (j + 1) c' ⊆ D := by
        intro x hx
        by_contra hxD
        obtain ⟨h1, h2⟩ := hDx x hxD
        rcases (hS' x).1 hx with hx | hx
        · exact (hSx x).1 hx h1
        · exact hx h2
      -- a scalar `α` keeps every disagreement visible: at most `|S'| ≤ e` scalars are bad
      let bad : ι → Finset E := fun x =>
        univ.filter fun α => u x + α * U jj x = u' x + α * v' x
      have hbad1 : ∀ x ∈ S (j + 1) c', (bad x).card ≤ 1 := by
        intro x hx
        have hx' : u x ≠ u' x ∨ U jj x ≠ v' x := by
          rcases (hS' x).1 hx with h | h
          · exact Or.inl ((hSx x).1 h)
          · exact Or.inr h
        exact card_le_one.2 fun α hα β hβ =>
          affine_eq_unique hx' (mem_filter.1 hα).2 (mem_filter.1 hβ).2
      have hcardB : ((S (j + 1) c').biUnion bad).card < Fintype.card E := by
        refine lt_of_le_of_lt (card_biUnion_le.trans ?_) (by omega : e < Fintype.card E)
        exact (sum_le_sum hbad1).trans (by simpa using (card_le_card hS'D).trans hD)
      obtain ⟨α, -, hα⟩ := exists_mem_notMem_of_card_lt_card
        (s := (S (j + 1) c').biUnion bad) (t := (univ : Finset E)) (by rwa [card_univ])
      refine ⟨c', fun i => ?_, (card_le_card hS'D).trans hD, β + α • (Pi.single jj 1 : Fin m → E),
        u' + α • v', C.add_mem hu' (C.smul_mem _ hv'), fun x => ?_⟩
      · by_cases hij : i = jj
        · subst hij; simpa [c'] using hv'
        · simpa [c', Function.update_of_ne hij] using hcC i
      · have hfun : ∑ i, (β + α • (Pi.single jj 1 : Fin m → E)) i • U i = u + α • U jj := by
          simp [u, add_smul, sum_add_distrib, Pi.single_apply, ite_smul]
        rw [hfun]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        constructor
        · intro hx heq
          exact hα (mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_univ _, by simpa using heq⟩⟩)
        · intro hne
          by_contra hx
          rw [hS'] at hx
          push Not at hx
          have hu : u x = u' x := by by_contra h; exact hx.1 ((hSx x).2 h)
          exact hne (by rw [hu, hx.2])
  obtain ⟨c, hcC, hS, -⟩ := key m le_rfl
  exact ⟨S m c, c, hS, hcC, fun i x hx => by
    by_contra hne; exact hx (mem_filter.2 ⟨mem_univ _, i, i.2, hne⟩)⟩

/-- **L-RS2, sharp form**: at most `(e+1)·|E|^{m−1}` coefficient vectors make a far `U`'s
combination `e`-close. -/
theorem far_bad_card [Fintype E] (hC : MinDist C d) (h3 : 3 * e < d)
    (hE : e + 1 < Fintype.card E) {m : ℕ} (U : Fin m → ι → E) (hfar : ¬ eClose C U e) :
    Nat.card {r : Fin m → E // Close C e (∑ i, r i • U i)} ≤
      (e + 1) * Fintype.card E ^ (m - 1) := by
  classical
  obtain ⟨s, hs⟩ := exists_far_comb hC h3 hE U hfar
  have hm : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    exact hfar ⟨∅, fun i => i.elim0, by simp, fun i => i.elim0, fun i => i.elim0⟩
  let L : (Fin m → E) → ι → E := fun r => ∑ i, r i • U i
  let P : (Fin m → E) → Prop := fun r => Close C e (L r)
  have hL : ∀ r (α : E), L (r + α • s) = L r + α • L s := by
    intro r α; simp [L, add_smul, sum_add_distrib, smul_sum, mul_smul]
  -- each line in direction `s` has at most `e + 1` close points
  have hline : ∀ r, (univ.filter fun α : E => P (r + α • s)).card ≤ e + 1 := by
    intro r
    by_contra hmany
    push Not at hmany
    obtain ⟨u', -, v', hv', D, hD, hDx⟩ := line_close hC h3 _ hmany fun α hα => by
      simpa [P, hL] using (mem_filter.1 hα).2
    exact hs (close_iff_agree.2 ⟨v', hv', D, hD, fun x hx => (hDx x hx).2⟩)
  -- double count the pairs `(r, α)` with `r + α s` bad
  let bad := univ.filter P
  have htr : ∀ α : E, (univ.filter fun r => P (r + α • s)).card = bad.card := fun α =>
    card_equiv (Equiv.addRight (α • s)) fun r => by simp [bad]
  have hcount : bad.card * Fintype.card E ≤ Fintype.card (Fin m → E) * (e + 1) :=
    calc bad.card * Fintype.card E
        = ∑ α : E, (univ.filter fun r => P (r + α • s)).card := by
          rw [sum_congr rfl fun α _ => htr α, sum_const, card_univ, smul_eq_mul, mul_comm]
      _ = ∑ r : Fin m → E, (univ.filter fun α : E => P (r + α • s)).card := by
          simp only [card_filter]; exact sum_comm
      _ ≤ ∑ _r : Fin m → E, (e + 1) := sum_le_sum fun r _ => hline r
      _ = Fintype.card (Fin m → E) * (e + 1) := by rw [sum_const, card_univ, smul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_fin] at hcount
  have hpow : Fintype.card E ^ m = Fintype.card E ^ (m - 1) * Fintype.card E := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow] at hcount
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Nat.le_of_mul_le_mul_right (by linarith) hpos

/-- **L-RS2 `far_bad_le`** (AHIV22 Lemmas 4.3–4.5, counting form): `3e < d → d < |E| →
¬ eClose U e → #{r ∈ E^m : Δ(Σ r_i U_i, C) ≤ e} ≤ d·|E|^{m−1}`. -/
theorem far_bad_le [Fintype E] (hC : MinDist C d) (h3 : 3 * e < d)
    (hdE : d < Fintype.card E) {m : ℕ} (U : Fin m → ι → E) (hfar : ¬ eClose C U e) :
    Nat.card {r : Fin m → E // Close C e (∑ i, r i • U i)} ≤ d * Fintype.card E ^ (m - 1) :=
  (far_bad_card hC h3 (by omega) U hfar).trans (Nat.mul_le_mul_right _ (by omega))

/-- **L-RS3** (exact): the index tuples `c ∈ ι^t` that miss `D` number `(|ι| − |D|)^t`. -/
theorem miss_card (D : Finset ι) (t : ℕ) :
    Nat.card {c : Fin t → ι // ∀ j, c j ∉ D} = (Fintype.card ι - D.card) ^ t := by
  classical
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin t) (x : ι) => x ∉ D)),
    Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_coe]

/-- **L-RS3 `miss_le`**: if `|D| ≥ a`, at most `(|ι| − a)^t` tuples miss `D`. -/
theorem miss_le (D : Finset ι) (t : ℕ) {a : ℕ} (ha : a ≤ D.card) :
    Nat.card {c : Fin t → ι // ∀ j, c j ∉ D} ≤ (Fintype.card ι - a) ^ t := by
  rw [miss_card]; exact Nat.pow_le_pow_left (by omega) t

/-- **L-RS3** (rational form): `|D| ≥ δN → #{tuples missing D} ≤ (1 − δ)^t · N^t`. -/
theorem miss_le_rat (D : Finset ι) (t : ℕ) {δ : ℚ} (hδ : δ * Fintype.card ι ≤ D.card) :
    (Nat.card {c : Fin t → ι // ∀ j, c j ∉ D} : ℚ) ≤ (1 - δ) ^ t * (Fintype.card ι : ℚ) ^ t := by
  have hle : D.card ≤ Fintype.card ι := card_le_univ D
  rw [miss_card, ← mul_pow, Nat.cast_pow, Nat.cast_sub hle]
  exact pow_le_pow_left₀ (by linarith [(Nat.cast_le (α := ℚ)).2 hle]) (by linarith) t

/-- **L-RS4 `close_in_K`**: if `C` is defined over `K` (`KRational`), every row of `U` has
entries in `K`, and `e < d`, the codewords of a decomposition have entries in `K`. -/
theorem close_in_K {K : Type*} [Field K] [Algebra K E] (hK : KRational K C) (hC : MinDist C d)
    (hed : e < d) {m : ℕ} {U : Fin m → ι → E}
    (hU : ∀ i x, U i x ∈ Set.range (algebraMap K E)) {S : Finset ι} {c : Fin m → ι → E}
    (h : IsDecomp C U e S c) : ∀ i x, c i x ∈ Set.range (algebraMap K E) := by
  obtain ⟨π, hπ, hfix⟩ := exists_proj (K := K) (E := E)
  intro i x
  have heq : (fun x => π (c i x)) = c i :=
    hC.eq_of_agree (hK π _ (h.2.1 i)) (h.2.1 i) S (by have := h.1; omega) fun x hx => by
      rw [← h.2.2 i x hx]; obtain ⟨a, ha⟩ := hU i x; rw [← ha, hfix]
  rw [← congrFun heq x]; exact hπ _

end SpartanChain.RS
