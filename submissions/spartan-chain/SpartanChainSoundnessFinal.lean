import SpartanChainSoundnessDefs
import SpartanChainVerifierTop

/-!
# The `final` direction of the knowledge state (BLUEPRINT-R1 §9.3 `final`, L-K3)

* `leafProg_accept`: what an accepting run of the leaf branch on a log gives without the SNARK:
  the header checks (`n ≤ chainCap`, the exact size, `c = leafStmt h n`), `h = s` when `n = 0`,
  and an accepting run of the SNARK verifier when `n ≥ 1`.
* Path facts: `pathOf_cases` (a path is `[j]` or its predecessor's path with `j` appended),
  `doom_seed` (a one-entry chain of a false statement is doomed for every prefix log).
* **`doom_of_not_esc`** (§9.3): under `¬ Esc`, every chain of a false statement is doomed.
* **L-K3 `accept_not_doomed`**: a complete chain whose checks all pass (`¬ Rej`) and whose column
  phase accepts on the log (`ColumnsAccepted`, delivered by L-K4 `runLog_chain`) is not doomed:
  its last `Alg` row needs an opened index in `Dof`, and `verify2_miss` (L-M3 through
  `opened_not_mem`, on the split `split_at_cut`) puts every opened index outside it.
* **`leaf_final`** (`mu_final` for the leaf branch): under `¬ Bad`, `¬ Esc` and an accepting run
  of `leafProg`, the parsed statement is true: `chainEnd s n = h`, `c = leafStmt h n`,
  `n ≤ chainCap`, given `runLog_chain` in the form `RunChain`.
-/

namespace SpartanChain.SoundnessFinal

open RecursionFast

/-- **The leaf branch accepting on a log**: the header checks hold; `h = s` if `n = 0`; else the
SNARK verifier accepts on the log. -/
theorem leafProg_accept (LV : LeafVerifier) {c : Digest} {π : Proof} {L : Log}
    (h : (leafProg LV c π).runLog L = some true) :
    leafN π ≤ chainCap ∧ π.size = LV.size (leafN π) ∧ c = leafStmt (leafH π) (leafN π) ∧
      (leafN π = 0 → leafH π = leafS π) ∧
      (leafN π ≠ 0 → (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L = some true) := by
  unfold leafProg at h
  split_ifs at h with hok hn
  · simp only [leafHeaderOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [RecursionFast.OProg.runLog, Option.some.injEq, decide_eq_true_eq] at h
    exact ⟨hok.1.1, hok.1.2, hok.2, fun _ => h, fun h' => absurd hn h'⟩
  · simp only [leafHeaderOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨hok.1.1, hok.1.2, hok.2, fun h' => absurd h' hn, fun _ => h⟩
  · simp [RecursionFast.OProg.runLog] at h

open SoundnessLog KS PCS SoundnessPCS Merkle Transcript

/-! ### Paths -/

theorem pathOf_cases (L : Log) (j : ℕ) :
    pathOf L j = [j] ∨ ∃ i, i < j ∧ predIdx L j = some i ∧ pathOf L j = pathOf L i ++ [j] := by
  unfold pathOf
  simp only [back]
  cases hp : predIdx L j with
  | none => left; rfl
  | some i =>
    simp only
    split_ifs with h
    · right; exact ⟨i, h, rfl, by rw [back_fuel L j i h]; rfl⟩
    · left; rfl

theorem entriesOf_snoc (L : Log) (p : List ℕ) (j : ℕ) :
    entriesOf L (p ++ [j]) = entriesOf L p ++ [L[j]!] := by
  simp [entriesOf]

theorem stmtOf_snoc {es : Log} (hne : es ≠ []) (x : ByteArray × Digest) :
    stmtOf (es ++ [x]) = stmtOf es := by
  unfold stmtOf entAt
  rw [List.getD_append _ _ _ _ (List.length_pos_iff.mpr hne)]

theorem kapOf_snoc {es : Log} (hne : es ≠ []) (x : ByteArray × Digest) :
    kapOf (es ++ [x]) = kapOf es := by
  unfold kapOf; rw [stmtOf_snoc hne]

theorem FS_snoc {es : Log} (hne : es ≠ []) (x : ByteArray × Digest) :
    FS (es ++ [x]) ↔ FS es := by
  unfold FS; rw [stmtOf_snoc hne]

theorem cut_snoc {L : Log} {i j : ℕ} (h2 : 2 ≤ (pathOf L i).length)
    (hp : pathOf L j = pathOf L i ++ [j]) : cut L j = cut L i := by
  unfold cut
  rw [hp, getElem!_pos _ 1 (by simp; omega), getElem!_pos _ 1 (by omega),
    List.getElem_append_left]

theorem posClass_zero (κ : ℕ) : posClass κ 0 = .seed := by
  simp [posClass]

/-- A one-entry chain of a false statement is doomed, for every prefix log. -/
theorem doom_seed (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L₀ : Log) {es : Log}
    (h1 : es.length = 1) (hfs : FS es) : Doom ev L₀ es := by
  right
  unfold Alg
  rw [h1, Nat.sub_self, posClass_zero]
  exact hfs

/-! ### `doom_of_not_esc` -/

/-- **`doom_of_not_esc`** (§9.3 `final`): if no chain of `L` escapes, every chain of a false
statement is doomed (for its own prefix log). -/
theorem doom_of_not_esc (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) {L : Log}
    (hesc : ¬ Esc ev L) :
    ∀ j, IsChain L j → FS (entriesOf L (pathOf L j)) →
      Doom ev (L₀ L j) (entriesOf L (pathOf L j)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hc hfs
    rcases pathOf_cases L j with hp | ⟨i, hij, hpred, hp⟩
    · exact doom_seed ev _ (by rw [hp]; simp [entriesOf]) hfs
    · have hne : entriesOf L (pathOf L i) ≠ [] := by
        simp [entriesOf, pathOf_ne_nil]
      have hes : entriesOf L (pathOf L j) = entriesOf L (pathOf L i) ++ [L[j]!] := by
        rw [hp, entriesOf_snoc]
      have hci : IsChain L i := by
        refine ⟨by have := hc.1; omega, matches_of_append (x := L[j]!) hne ?_⟩
        rw [← hes]; exact hc.2
      have hfsi : FS (entriesOf L (pathOf L i)) := by
        rw [hes, FS_snoc hne] at hfs; exact hfs
      -- doom of the predecessor, for chain `j`'s prefix log
      have hdi : Doom ev (L₀ L j) (entriesOf L (pathOf L i)) := by
        by_cases h1 : (pathOf L i).length = 1
        · exact doom_seed ev _ (by simp [entriesOf, h1]) hfsi
        · have h2 : 2 ≤ (pathOf L i).length := by
            have := List.length_pos_iff.mpr (pathOf_ne_nil L i); omega
          have hL : L₀ L j = L₀ L i := by unfold L₀; rw [cut_snoc h2 hp]
          rw [hL]; exact ih i hij hci hfsi
      by_contra hnd
      apply hesc
      refine ⟨j, ?_, ?_, ?_, hnd⟩
      · simp only [chains, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hc.1, hc⟩
      · rw [hes, List.length_append]; have := List.length_pos_iff.mpr hne; simp; omega
      · rw [hes, List.dropLast_concat]; exact hdi

/-! ### L-K3 -/

theorem len_eq (κ : ℕ) : len κ = pV κ + 1 + nJ κ := by
  simp [len, shape_eq_pre8, pre8, pV, pS, pTri, List.length_flatten, List.map_replicate,
    List.sum_replicate]
  omega

theorem posClass_last (κ : ℕ) (hJ : 0 < nJ κ) : posClass κ (pV κ + nJ κ) = .r7 (nJ κ) := by
  have h0 : ¬ pV κ + nJ κ = 0 := by omega
  have h1 : ¬ pV κ + nJ κ = 1 := by simp only [pV, pS, pTri]; omega
  have h2 : ¬ pV κ + nJ κ ≤ 1 + rows κ := by simp only [pV, pS, pTri]; omega
  have h3 : ¬ pV κ + nJ κ = pU κ := by simp only [pV, pS, pTri, pU]; omega
  have h4 : ¬ pV κ + nJ κ < pG κ 0 := by simp only [pV, pS, pTri, pG]; omega
  have h5 : ¬ pV κ + nJ κ < pTri κ := by simp only [pV, pS, pTri]; omega
  have h6 : ¬ pV κ + nJ κ = pTri κ := by simp only [pV, pS, pTri]; omega
  have h7 : ¬ pV κ + nJ κ = pTri κ + 1 := by simp only [pV, pS, pTri]; omega
  have h8 : ¬ pV κ + nJ κ < pS κ := by simp only [pV, pS, pTri]; omega
  have h9 : ¬ pV κ + nJ κ = pS κ := by simp only [pV, pS, pTri]; omega
  have h10 : ¬ pV κ + nJ κ < pGr κ 0 := by simp only [pV, pS, pTri, pGr]; omega
  have h11 : ¬ pV κ + nJ κ < pV κ := by omega
  have h12 : ¬ pV κ + nJ κ = pV κ := by omega
  unfold posClass
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ite_false,
    Nat.add_sub_cancel_left]

/-- The shape parameter of a chain is at most `20` (`n ≤ chainCap = 2^20`). -/
theorem kapOf_le {es : Log} (hm : Matches es) : kapOf es ≤ 20 := by
  obtain ⟨s, n, h, h0, -, hcap, -⟩ := hm
  have hst : stmtOf es = (s, n, h) := by
    cases es with
    | nil => simp at h0
    | cons e t => simp only [List.getElem?_cons_zero, Option.bind_some] at h0; simp [stmtOf, entAt, h0]
  rw [show kapOf es = Nat.clog 2 n by simp [kapOf, hst]]
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hcap

theorem nJ_pos {κ : ℕ} (hκ : κ ≤ 20) : 0 < nJ κ := by
  have h := (layout_ok κ hκ).2.2
  rcases Nat.eq_zero_or_pos (nJ κ) with h0 | h0
  · simp only [nJ] at h0; rw [h0] at h; simp [tQ] at h
  · exact h0

/-- What L-K4 `runLog_chain` delivers about the column phase of a complete chain `es` on `L`:
`verify2` with the chain's root, `r`, `a`, `ū` and `v` accepts on `L`, and its index answers are
the chain's last `J` answers. -/
def ColumnsAccepted (L es : Log) : Prop :=
  ∃ st opens,
    (Ligero.verify2 (kapOf es) st (rootOf es) (rVec (kapOf es) es).toArray (aOf (kapOf es) es)
        (ubarOf (kapOf es) es) (msgOf (entAt es (pV (kapOf es))).1) opens).runLog L = some true ∧
      idxTuple L (kapOf es) st (msgOf (entAt es (pV (kapOf es))).1) = bOf (kapOf es) es

theorem rootOf_eq {L : Log} {j : ℕ} (h2 : 2 ≤ (pathOf L j).length) (hcut : cut L j < L.length)
    {root : Label} (hr : parseAbsorbRoot L[cut L j].1 = some root) :
    rootOf (entriesOf L (pathOf L j)) = root := by
  unfold rootOf entAt
  rw [List.getD_eq_getElem _ _ (by simp [entriesOf]; omega), entriesOf_getElem]
  have : (pathOf L j)[1]'(by omega) = cut L j := by
    unfold cut; rw [getElem!_pos _ 1 (by omega)]
  rw [this, getElem!_pos L _ hcut, hr]; rfl

theorem toArray_getD (l : List EF) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **L-K3 `accept_not_doomed`**: a complete chain with no failed check (`¬ Rej`) whose column
phase accepts on `L` (`ColumnsAccepted`) is not doomed, for `L` without bad events. -/
theorem accept_not_doomed (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) {L : Log} {j : ℕ}
    (hb : ¬ Bad L) (hc : IsChain L j)
    (hlen : (pathOf L j).length = len (kapOf (entriesOf L (pathOf L j))))
    (hnr : ¬ Rej ev (entriesOf L (pathOf L j)))
    (hcols : ColumnsAccepted L (entriesOf L (pathOf L j))) :
    ¬ Doom ev (L₀ L j) (entriesOf L (pathOf L j)) := by
  set es := entriesOf L (pathOf L j) with hes
  set κ := kapOf es
  rintro (hrej | halg)
  · exact hnr hrej
  have h2 : 2 ≤ (pathOf L j).length := by rw [hlen, len_eq]; simp only [pV, pS, pTri]; omega
  obtain ⟨hcut, hsplit, root, hroot⟩ := split_at_cut hc h2
  have hroot' : rootOf es = root := rootOf_eq h2 hcut hroot
  obtain ⟨st, opens, hv, hidx⟩ := hcols
  have hcol : ¬ Merkle.Collision L := fun h => hb (Or.inl h)
  have hhit : ¬ Merkle.Hit L := fun h => hb (Or.inr (Or.inl h))
  rw [hsplit] at hv hcol hhit
  rw [hroot'] at hv
  obtain ⟨m1, m2⟩ := verify2_miss hcol hhit hroot st _ _ _ _ opens hv
  rw [← hsplit, hidx] at m1 m2
  -- the last row of `Alg`
  have hJ : 0 < nJ κ := nJ_pos (kapOf_le hc.2)
  have hpos : posClass κ (es.length - 1) = .r7 (nJ κ) := by
    rw [show es.length = (pathOf L j).length by simp [es, entriesOf], hlen, len_eq,
      show pV κ + 1 + nJ κ - 1 = pV κ + nJ κ by omega]
    exact posClass_last κ hJ
  unfold Alg at halg
  rw [hpos] at halg
  try simp only [AlgRow] at halg
  split_ifs at halg with hlt
  · exact absurd hlt (lt_irrefl _)
  obtain ⟨-, hmiss⟩ := halg
  apply hmiss
  unfold Dof Uof
  rw [hroot']
  split_ifs
  · simpa only [toArray_getD] using m1
  · exact m2

/-! ### `final` for the leaf branch -/

/-- What L-K4 `runLog_chain` delivers for an accepted SNARK run (`n ≥ 1`) on a log without bad
events: a complete chain of `L` with the proof's statement, no failed check, and an accepting
column phase. -/
def RunChain (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L : Log) (s : Digest) (n : ℕ)
    (h : Digest) : Prop :=
  ∃ j, IsChain L j ∧
    (pathOf L j).length = len (kapOf (entriesOf L (pathOf L j))) ∧
    stmtOf (entriesOf L (pathOf L j)) = (s, n, h) ∧
    ¬ Rej ev (entriesOf L (pathOf L j)) ∧ ColumnsAccepted L (entriesOf L (pathOf L j))

/-- **`final` for a chain**: on a log without bad events and escapes, a chain as delivered by
`runLog_chain` has a true statement. -/
theorem chainEnd_of_runChain (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) {L : Log}
    (hb : ¬ Bad L) (hesc : ¬ Esc ev L) {s : Digest} {n : ℕ} {h : Digest}
    (hrc : RunChain ev L s n h) : chainEnd s n = h := by
  obtain ⟨j, hc, hlen, hst, hnr, hcols⟩ := hrc
  by_contra hfs
  have hFS : FS (entriesOf L (pathOf L j)) := by unfold FS; rw [hst]; exact hfs
  exact accept_not_doomed ev hb hc hlen hnr hcols (doom_of_not_esc ev hesc j hc hFS)

/-- **`mu_final` for the leaf branch**: on a log without bad events and escapes, an accepted
leaf proof has a true statement — `n ≤ chainCap`, `c = leafStmt h n` and `chainEnd s n = h`
for the parsed `(s, n, h)` — given L-K4 `runLog_chain` for the SNARK verifier in the form
`RunChain`. -/
theorem leaf_final (LV : LeafVerifier) (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)
    {L : Log} {c : Digest} {π : Proof} (hb : ¬ Bad L) (hesc : ¬ Esc ev L)
    (hacc : (leafProg LV c π).runLog L = some true)
    (hchain : leafN π ≠ 0 →
      (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L = some true →
      RunChain ev L (leafS π) (leafN π) (leafH π)) :
    leafN π ≤ chainCap ∧ c = leafStmt (leafH π) (leafN π) ∧
      chainEnd (leafS π) (leafN π) = leafH π := by
  obtain ⟨hcap, -, hc, h0, h1⟩ := leafProg_accept LV hacc
  refine ⟨hcap, hc, ?_⟩
  by_cases hn : leafN π = 0
  · rw [hn, h0 hn]; rfl
  · exact chainEnd_of_runChain ev hb hesc (hchain hn (h1 hn))

/-- `μ L < 1` excludes bad events and escapes (§9.3: `μ` is `1` on them). -/
theorem not_bad_esc_of_mu (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) {L : Log}
    (h : μ ev L < 1) : ¬ Bad L ∧ ¬ Esc ev L := by
  unfold μ muG at h
  split_ifs at h with hbe
  · exact absurd h (lt_irrefl 1)
  · exact not_or.1 hbe

/-- **`mu_final`, leaf branch** (§9.3 `final`): if `μ L < 1` and `leafProg` accepts on `L`, the
parsed statement is true, given L-K4 `runLog_chain` in the form `RunChain`. -/
theorem mu_final_leaf (LV : LeafVerifier) (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)
    {L : Log} {c : Digest} {π : Proof} (hμ : μ ev L < 1)
    (hacc : (leafProg LV c π).runLog L = some true)
    (hchain : ¬ Bad L → leafN π ≠ 0 →
      (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L = some true →
      RunChain ev L (leafS π) (leafN π) (leafH π)) :
    leafN π ≤ chainCap ∧ c = leafStmt (leafH π) (leafN π) ∧
      chainEnd (leafS π) (leafN π) = leafH π :=
  let ⟨hb, he⟩ := not_bad_esc_of_mu ev hμ
  leaf_final LV ev hb he hacc (hchain hb)

end SpartanChain.SoundnessFinal
