import SpartanChainSoundnessDefs

/-!
# The knowledge state of the leaf SNARK: the potential and its `step` law (BLUEPRINT-R1 §9.2–§9.4)

**Part A, the potential over chains** (generic in the doom predicate and the per-chain charge).
For a doom predicate `D L₀ es` and a per-chain charge `φ L₀ es` (both functions of a chain's
prefix log `L₀` and its entries `es`), the potential of §9.3 is

`μ L := if Bad L ∨ Esc L then 1 else Σ_{j ∈ chains L} [OnFrontier L L[j]] φ (L₀ L j) (es j)`

with `EscAt L₀ es := 2 ≤ |es| ∧ D L₀ es.dropLast ∧ ¬ D L₀ es` and `Esc L` some chain escaping.
`muG_step` proves the contract's `step` law for it from one **local** inequality `hloc` on a single
chain and one fresh query (the "intended values" of §9.3 step 4), plus `hseed` (a seed is charged
nothing). The proof is §9.3 steps 1–5: `mu_le` (pointwise), `step_bad` (L-K1), `step_split`
(L-K8: old chains keep their paths, prefixes and charges, the predecessor `i*` of the new entry
leaves the frontier exactly when the query is its squeeze).
-/

namespace SpartanChain
open RecursionFast Merkle Transcript SoundnessLog
open scoped NNReal

namespace KS

/-! ## Log facts -/

/-- Under `¬ Bad`, distinct entries have distinct answers. -/
theorem ans_inj {L : Log} (hb : ¬ Bad L) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (h : L[i].2 = L[j].2) : i = j := by
  have hq : L[i].1 = L[j].1 := by
    by_contra hne
    exact hb (Or.inl ⟨L[i], List.getElem_mem hi, L[j], List.getElem_mem hj, hne, by rw [h]⟩)
  have hn : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  exact (List.Nodup.getElem_inj_iff hn (i := i) (j := j) (hi := by simpa using hi)
    (hj := by simpa using hj)).mp (by simpa using hq)

/-- Under `¬ Bad`, the answer index of an entry's own answer is the entry. -/
theorem ansIdx_self {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) :
    ansIdx L L[j].2 = some j := by
  unfold ansIdx
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp, fun k hk => ?_⟩
  simp only [decide_eq_true_eq]
  intro h
  exact absurd (ans_inj hb (hk.trans hj) hj h) (Nat.ne_of_lt hk)

/-- The squeeze of an old answer has that entry as its predecessor. -/
theorem istar_of_squeeze {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) {q : ByteArray}
    (hq : q = squeezeQ L[j]!.2) : (stateIn q).bind (ansIdx L) = some j := by
  rw [hq, stateIn_squeezeQ, Option.bind_some, getElem!_pos L j hj, ansIdx_self hb hj]

theorem back_getLast? (L : Log) (f j : ℕ) : (back L (f + 1) j).getLast? = some j := by
  simp only [back]
  cases predIdx L j with
  | none => rfl
  | some i => simp only; split_ifs <;> simp

theorem pathOf_getLast? (L : Log) (j : ℕ) : (pathOf L j).getLast? = some j :=
  back_getLast? L j j

theorem entriesOf_getLast? (L : Log) (j : ℕ) :
    (entriesOf L (pathOf L j)).getLast? = some L[j]! := by
  rw [entriesOf, List.getLast?_map, pathOf_getLast?]
  rfl

theorem length_entriesOf (L : Log) (is : List ℕ) : (entriesOf L is).length = is.length := by
  simp [entriesOf]

theorem lt_of_ansIdx {L : Log} {q : ByteArray} {i : ℕ} (h : (stateIn q).bind (ansIdx L) = some i) :
    i < L.length ∧ stateIn q = some L[i]!.2 := by
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st, hst, hi⟩ := h
  obtain ⟨hiL, hia⟩ := ansIdx_lt hi
  exact ⟨hiL, by rw [hst, getElem!_pos L i hiL, hia]⟩

open Classical in
/-- `Bad` of a log with an entry appended, as a filter count, is at most L-K1's bound. -/
theorem card_bad_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) ≤
      ((2 ^ 96 * (3 * 2 ^ 8 + 1) + 1 : ℕ) : ℝ≥0) := by
  classical
  rw [Finset.sum_boole]
  exact_mod_cast bad_step_frac hb hq hl

/-! ## Part A: the potential over chains -/

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

theorem muG_empty : muG D φ [] = 0 := by
  have hb : ¬ Bad ([] : Log) := by
    rintro (⟨e, he, -⟩ | ⟨i, j, -, hj, -⟩ | ⟨i, j, -, hj, -⟩ | hr)
    · simp at he
    · simp at hj
    · simp at hj
    · exact hr List.nodup_nil
  have hc : chains ([] : Log) = [] := rfl
  have he : ¬ EscG D [] := by rintro ⟨j, hj, -⟩; simp [hc] at hj
  rw [muG, ite_eq_right (by tauto), sumG, hc]
  rfl

theorem muG_lt_one {L : Log} (h : muG D φ L < 1) : ¬ Bad L ∧ ¬ EscG D L := by
  by_contra hc
  rw [muG, ite_eq_left (by tauto)] at h
  exact lt_irrefl _ h

theorem chains_nodup (L : Log) : (chains L).Nodup :=
  (List.nodup_range).filter _

theorem mem_chains {L : Log} {j : ℕ} : j ∈ chains L ↔ IsChain L j := by
  unfold chains
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A function supported on one index sums, over a duplicate-free list, to its value there if the
index is in the list. -/
theorem sum_map_single {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℝ≥0) (i : ℕ)
    (hf : ∀ j ∈ l, j ≠ i → f j = 0) : (l.map f).sum = if i ∈ l then f i else 0 := by
  classical
  rw [← List.sum_toFinset f hl]
  split_ifs with hi
  · exact Finset.sum_eq_single i (fun j hj hji => hf j (List.mem_toFinset.mp hj) hji)
      (fun h => absurd (List.mem_toFinset.mpr hi) h)
  · exact Finset.sum_eq_zero fun j hj => hf j (List.mem_toFinset.mp hj)
      (fun h => hi (h ▸ List.mem_toFinset.mp hj))

theorem sum_map_zero {l : List ℕ} (f : ℕ → ℝ≥0) (hf : ∀ j ∈ l, f j = 0) : (l.map f).sum = 0 := by
  rw [List.map_congr_left hf]; simp

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

/-- An old chain's charge after appending a fresh non-bad entry, plus the charge it loses when the
query is its squeeze, is its charge before. -/
theorem termG_append (hq : q ∉ L.map Prod.fst) (hb : ¬ Bad (L ++ [(q, a)])) {j : ℕ}
    (hj : j < L.length) :
    termG φ (L ++ [(q, a)]) j +
        (if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0) =
      termG φ L j := by
  classical
  have hget : (L ++ [(q, a)])[j]! = L[j]! := by
    rw [getElem!_pos (L ++ [(q, a)]) j (by simp; omega), getElem!_pos L j hj,
      List.getElem_append_left hj]
  have hmem : L[j]! ∈ L := by rw [getElem!_pos L j hj]; exact List.getElem_mem hj
  unfold termG
  rw [hget, L₀_append hj hb, entriesOf_pathOf_append hb hj]
  have hfr := frontier_append (q := q) (a := a) hmem
  generalize L[j]! = e at hmem hfr ⊢
  by_cases hs : q = squeezeQ e.2
  · have hf : OnFrontier L e := ⟨hmem, hs ▸ hq⟩
    rw [ite_eq_right (fun h => (hfr.mp h).2 hs), ite_eq_left hs, ite_eq_left hf, zero_add]
  · rw [ite_eq_right hs, add_zero]
    by_cases hf : OnFrontier L e
    · rw [ite_eq_left (hfr.mpr ⟨hf, hs⟩), ite_eq_left hf]
    · rw [ite_eq_right (fun h => hf (hfr.mp h).1), ite_eq_right hf]

/-- The sum over the chains of an extended (non-bad) log: the old chains, then the new entry. -/
theorem sumG_append (hb : ¬ Bad (L ++ [(q, a)])) :
    sumG φ (L ++ [(q, a)]) = ((chains L).map (termG φ (L ++ [(q, a)]))).sum +
      (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) := by
  rw [sumG, chains_append hb, List.map_append, List.sum_append]
  split_ifs <;> simp

/-- The prefix of the new chain extending `i`. -/
theorem L₀_new (hb : ¬ Bad (L ++ [(q, a)])) {i : ℕ} (hi : (stateIn q).bind (ansIdx L) = some i) :
    L₀ (L ++ [(q, a)]) L.length = L.take ((pathOf L i ++ [L.length])[1]!) := by
  have hpath := back_new hb
  rw [hi] at hpath
  dsimp only at hpath
  unfold L₀ cut
  rw [hpath]
  apply List.take_append_of_le_length
  have hiL := (lt_of_ansIdx hi).1
  by_cases h1 : 1 < (pathOf L i ++ [L.length]).length
  · rw [getElem!_pos _ 1 h1]
    have hm := List.getElem_mem h1
    rcases List.mem_append.mp hm with hm | hm
    · exact ((mem_pathOf_le hm).trans hiL.le)
    · simp at hm; omega
  · rw [getElem!_neg _ 1 h1]; exact Nat.zero_le _

/-- The new chain's prefix is the predecessor's once the predecessor has two entries. -/
theorem L₀_new_eq {i : ℕ} (hiL : i < L.length) (h2 : 2 ≤ (entriesOf L (pathOf L i)).length) :
    L.take ((pathOf L i ++ [L.length])[1]!) = L₀ L i := by
  rw [length_entriesOf] at h2
  unfold L₀ cut
  rw [getElem!_pos _ 1 (by simp; omega), getElem!_pos _ 1 (by omega),
    List.getElem_append_left (by omega)]

/-- An escape after appending a non-bad entry is at the new entry. -/
theorem escG_append (hb : ¬ Bad (L ++ [(q, a)])) (he : ¬ EscG D L)
    (h : EscG D (L ++ [(q, a)])) :
    IsChain (L ++ [(q, a)]) L.length ∧
      EscAtG D (L₀ (L ++ [(q, a)]) L.length)
        (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  classical
  obtain ⟨j, hj, hesc⟩ := h
  rw [chains_append hb, List.mem_append] at hj
  rcases hj with hj | hj
  · have hjL : j < L.length := (mem_chains.mp hj).1
    rw [L₀_append hjL hb, entriesOf_pathOf_append hb hjL] at hesc
    exact absurd ⟨j, hj, hesc⟩ he
  · split_ifs at hj with hc
    · simp only [List.mem_singleton] at hj
      subst hj
      exact ⟨hc, hesc⟩
    · simp at hj

/-- The new entry of a seed chain is charged nothing and cannot escape. -/
theorem new_seed (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0) (hb : ¬ Bad (L ++ [(q, a)]))
    (hn : (stateIn q).bind (ansIdx L) = none) (hc : IsChain (L ++ [(q, a)]) L.length) :
    termG φ (L ++ [(q, a)]) L.length = 0 ∧
      ¬ EscAtG D (L₀ (L ++ [(q, a)]) L.length)
        (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  classical
  have hpath := back_new hb
  rw [hn] at hpath
  have hes : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) = [(q, a)] := by
    rw [hpath]; simp [entriesOf]
  have hm := hc.2
  rw [hes] at hm
  refine ⟨?_, ?_⟩
  · unfold termG; rw [hes, hseed _ _ hm]; simp
  · rw [hes]; rintro ⟨h2, -⟩; simp at h2

end Step

open Classical in
/-- **`mu_step` (generic)**: the contract's `step` law for the potential `muG D φ`, with error
L-K1's bad fraction plus `δ`, from the local inequality `hloc` on one chain and one fresh query
(§9.3 step 4, "intended values") and `hseed`. -/
theorem muG_step (δ : ℝ≥0)
    (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0)
    (hloc : ∀ L₀ L₀' es e q, Matches es → es.getLast? = some e → (2 ≤ es.length → L₀' = L₀) →
      stateIn q = some e.2 →
      ∑ a : Digest, (if Matches (es ++ [(q, a)]) then
          (if EscAtG D L₀' (es ++ [(q, a)]) then 1 else 0) + φ L₀' (es ++ [(q, a)]) else 0) ≤
        2 ^ 256 * ((if q = squeezeQ e.2 then φ L₀ es else 0) + δ))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D φ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D φ (L ++ [(q, a)]) ≤
      (muG D φ L + (((2 ^ 96 * (3 * 2 ^ 8 + 1) + 1 : ℕ) : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256 := by
  obtain ⟨hbL, heL⟩ := muG_lt_one D φ hμ
  have hX : muG D φ L = sumG φ L := by rw [muG, ite_eq_right (by tauto)]
  set X := sumG φ L with hXdef
  set B : ℝ≥0 := ((2 ^ 96 * (3 * 2 ^ 8 + 1) + 1 : ℕ) : ℝ≥0)
  -- The charges lost by the old chains, and the new chain's intended value.
  -- `c` and `nt` depend on the predecessor of the new entry.
  obtain ⟨c, nt, hcX, hpt, hnt⟩ : ∃ (c : ℝ≥0) (nt : Digest → ℝ≥0), c ≤ X ∧
      (∀ a, ¬ Bad (L ++ [(q, a)]) → muG D φ (L ++ [(q, a)]) + c ≤ X + nt a) ∧
      ∑ a, nt a ≤ 2 ^ 256 * (c + δ) := by
    -- the old chains' losses sum to `c`
    have hold : ∀ (c : ℝ≥0), (((chains L).map fun j =>
        if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c) →
        ∀ a, ¬ Bad (L ++ [(q, a)]) →
          ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c = X := by
      intro c hc a hb
      rw [← hc, ← List.sum_map_add, hXdef, sumG]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact termG_append hq hb (mem_chains.mp hj).1
    cases hi : (stateIn q).bind (ansIdx L) with
    | none =>
      refine ⟨0, fun _ => 0, zero_le, fun a hb => ?_, by simp⟩
      have hc0 := sum_map_zero (l := chains L) (fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0)
        (fun j hj => by
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          cases hi)
      have hsum := hold 0 hc0 a hb
      have hesc : ¬ EscG D (L ++ [(q, a)]) := fun h => by
        obtain ⟨hc, hesc⟩ := escG_append hb heL h
        exact (new_seed hseed hb hi hc).2 hesc
      rw [muG, ite_eq_right (by tauto), sumG_append hb, add_zero, add_zero]
      split_ifs with hc
      · rw [(new_seed (D := D) hseed hb hi hc).1, add_zero, ← hsum, add_zero]
      · rw [add_zero, ← hsum, add_zero]
    | some i =>
      obtain ⟨hiL, hst⟩ := lt_of_ansIdx hi
      set es := entriesOf L (pathOf L i) with hes
      set L₀' := L.take ((pathOf L i ++ [L.length])[1]!) with hL₀'
      let c : ℝ≥0 := if IsChain L i ∧ q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0
      let nt : Digest → ℝ≥0 := fun a => if Matches (es ++ [(q, a)]) then
          (if EscAtG D L₀' (es ++ [(q, a)]) then 1 else 0) + φ L₀' (es ++ [(q, a)]) else 0
      have hc : ((chains L).map fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c := by
        rw [sum_map_single (chains_nodup L) _ i]
        · by_cases h1 : IsChain L i
          · rw [ite_eq_left (mem_chains.mpr h1)]; simp only [c, h1, true_and]; rfl
          · rw [ite_eq_right (fun h => h1 (mem_chains.mp h))]; simp only [c, h1, false_and]; rfl
        · intro j hj hji
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          exact hji (Option.some.inj hi)
      refine ⟨c, nt, ?_, fun a hb => ?_, ?_⟩
      · -- `c ≤ X`: `c` is the charge of the frontier chain `i`, one summand of `X`
        simp only [c]
        split_ifs with hh
        · obtain ⟨hci, hs⟩ := hh
          have hmem : L[i]! ∈ L := by rw [getElem!_pos L i hiL]; exact List.getElem_mem hiL
          have hterm : termG φ L i = φ (L₀ L i) es := by
            unfold termG; rw [ite_eq_left ⟨hmem, hs ▸ hq⟩]
          rw [← hterm, hXdef, sumG]
          exact List.single_le_sum (fun _ _ => zero_le) _
            (List.mem_map_of_mem (mem_chains.mpr hci))
        · exact zero_le
      · have hsum := hold c hc a hb
        have hpath := back_new hb
        rw [hi] at hpath
        have hesn : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
            es ++ [(q, a)] := by
          rw [hpath, hes]
          unfold entriesOf
          rw [List.map_append]
          congr 1
          · exact entriesOf_append fun x hx => (mem_pathOf_le hx).trans_lt hiL
          · simp
        have hL₀n := L₀_new hb hi
        -- `[Esc] + new charge ≤ nt a`
        have hnew : (if EscG D (L ++ [(q, a)]) then 1 else 0) +
            (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) ≤
            nt a := by
          by_cases hc' : IsChain (L ++ [(q, a)]) L.length
          · have hm : Matches (es ++ [(q, a)]) := by have := hc'.2; rwa [hesn] at this
            simp only [nt, ite_eq_left hm, ite_eq_left hc']
            gcongr
            · split_ifs with h1 h2 h2
              · exact le_rfl
              · obtain ⟨-, h3⟩ := escG_append hb heL h1
                rw [hL₀n, hesn] at h3
                exact absurd h3 h2
              · exact zero_le
              · exact le_rfl
            · unfold termG
              rw [hL₀n, hesn]
              split_ifs
              · exact le_rfl
              · exact zero_le
          · have : ¬ EscG D (L ++ [(q, a)]) := fun h => hc' (escG_append hb heL h).1
            simp [this, hc']
        calc muG D φ (L ++ [(q, a)]) + c
            ≤ ((if EscG D (L ++ [(q, a)]) then 1 else 0) + sumG φ (L ++ [(q, a)])) + c := by
              gcongr
              rw [muG]
              split_ifs with h1 h2
              · exact le_add_right le_rfl
              · tauto
              · tauto
              · exact le_add_self
          _ = ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c +
                ((if EscG D (L ++ [(q, a)]) then 1 else 0) +
                  (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length
                    else 0)) := by rw [sumG_append hb]; ring
          _ ≤ X + nt a := by rw [hsum]; gcongr
      · -- the local inequality
        by_cases hci : IsChain L i
        · have hloc' := hloc (L₀ L i) L₀' es L[i]! q hci.2 (entriesOf_getLast? L i)
            (fun h2 => L₀_new_eq hiL h2) hst
          have hcc : c = if q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0 := by
            simp only [c, hci, true_and]
          rw [hcc]
          exact hloc'
        · have : ∀ a, nt a = 0 := fun a => by
            simp only [nt]
            rw [ite_eq_right]
            intro hm
            exact hci ⟨hiL, matches_of_append (by
              rw [← List.length_pos_iff, length_entriesOf, List.length_pos_iff]
              exact pathOf_ne_nil L i) hm⟩
          simp [this]
  -- Summation.
  have hpt' : ∀ a, muG D φ (L ++ [(q, a)]) ≤
      (if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a) := by
    intro a
    by_cases hb : Bad (L ++ [(q, a)])
    · rw [muG, ite_eq_left (Or.inl hb), ite_eq_left hb]; exact le_self_add
    · rw [ite_eq_right hb, zero_add]
      have h := hpt a hb
      have : (X - c) + c = X := tsub_add_cancel_of_le hcX
      rw [← this, add_assoc, add_comm c, ← add_assoc] at h
      exact le_of_add_le_add_right h
  calc ∑ a : Digest, muG D φ (L ++ [(q, a)])
      ≤ ∑ a : Digest, ((if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a)) :=
        Finset.sum_le_sum fun a _ => hpt' a
    _ = (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) + 2 ^ 256 * (X - c) +
          ∑ a, nt a := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          fintype_card_digest, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ) := by
        gcongr
        exact card_bad_le hbL hq hl
    _ = (muG D φ L + (B / 2 ^ 256 + δ)) * 2 ^ 256 := by
        rw [hX, add_mul, add_mul, div_mul_cancel₀ _ (by positivity)]
        have : (X - c) + c = X := tsub_add_cancel_of_le hcX
        calc B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ)
            = B + 2 ^ 256 * ((X - c) + c) + 2 ^ 256 * δ := by ring
          _ = X * 2 ^ 256 + (B + δ * 2 ^ 256) := by rw [this]; ring

end Potential


/-! ## Part A2: positions and rounds of the shape -/

section Positions
open PCS

theorem len_eq (κ : ℕ) : len κ = (pre8 κ).length + nJ κ := by
  rw [len, shape_eq_pre8, List.length_append, List.length_replicate]

theorem pre8_length (κ : ℕ) :
    (pre8 κ).length = 13 + rows κ + 5 * (15 + κ) + 2 * (8 + κ) := by
  simp [pre8]; ring

theorem shape_zero (κ : ℕ) : (shape κ)[0]? = some .seed := by simp [shape]

theorem shape_one (κ : ℕ) : (shape κ)[1]? = some (.absorb 0x01 31) := by
  simp [shape, List.append_assoc]

theorem shape_ne_seed (κ p : ℕ) (h1 : 1 ≤ p) : (shape κ)[p]? ≠ some .seed := by
  simp only [shape, List.append_assoc, List.cons_append, List.nil_append]
  intro h
  rcases p with _ | p
  · omega
  rw [List.getElem?_cons_succ] at h
  have := List.mem_of_getElem? h
  simp [List.mem_flatten] at this

theorem shape_R0 (κ p : ℕ) (h1 : 2 ≤ p) (h2 : p ≤ 1 + rows κ) :
    (shape κ)[p]? = some .squeeze := by
  simp only [shape, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_replicate]; omega

theorem shape_R7 (κ p : ℕ) (h1 : (pre8 κ).length ≤ p) (h2 : p < len κ) :
    (shape κ)[p]? = some .squeeze := by
  rw [len_eq] at h2
  rw [shape_eq_pre8, List.getElem?_append_right h1, List.getElem?_replicate,
    ite_eq_left (by omega)]

theorem shape_pre8_last (κ : ℕ) :
    (shape κ)[(pre8 κ).length - 1]? = some (.absorb 0x08 (24 * msgLen κ)) := by
  have := pre8_length κ
  rw [shape_eq_pre8, List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?, pre8,
    List.getLast?_append]
  rfl

/-- A multi-answer round `(s0, r)` of shape `κ`: entered at the absorb position `s0 ≥ 1`, with its
`r` answers at the squeeze positions `s0 + 1 … s0 + r < len κ`, each of which has the round. -/
structure RoundSpec (κ s0 r : ℕ) : Prop where
  pos : 1 ≤ s0
  lt : s0 + r < len κ
  entry : ∃ k l, (shape κ)[s0]? = some (.absorb k l)
  sq : ∀ p, s0 < p → p ≤ s0 + r → (shape κ)[p]? = some .squeeze ∧ rnd κ p = some (s0, r)

theorem rnd_spec {κ p s0 r : ℕ} (h : rnd κ p = some (s0, r)) :
    s0 < p ∧ p ≤ s0 + r ∧ RoundSpec κ s0 r := by
  have hl := pre8_length κ
  have hlen := len_eq κ
  unfold rnd at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by omega, by omega, ⟨le_rfl, by omega, ⟨_, _, shape_one κ⟩, fun p hp1 hp2 =>
      ⟨shape_R0 κ p (by omega) (by omega), ?_⟩⟩⟩
    unfold rnd; rw [ite_eq_left ⟨by omega, by omega⟩]
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by omega, by omega, ⟨by omega, by omega, ⟨_, _, shape_pre8_last κ⟩, fun p hp1 hp2 =>
      ⟨shape_R7 κ p (by omega) (by omega), ?_⟩⟩⟩
    unfold rnd; rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]

theorem rnd_none_of_absorb {κ p : ℕ} {k : UInt8} {l : ℕ}
    (h : (shape κ)[p]? = some (.absorb k l)) : rnd κ p = none := by
  cases hr : rnd κ p with
  | none => rfl
  | some sr =>
    obtain ⟨s0, r⟩ := sr
    obtain ⟨h1, h2, hs⟩ := rnd_spec hr
    rw [(hs.sq p h1 h2).1] at h
    cases h

end Positions

/-! ## Part A2: chains as entry lists -/

section Chains

theorem lastAns_append (es : Log) (x : ByteArray × Digest) : lastAns (es ++ [x]) = x.2 := by
  simp [lastAns]

theorem lastAns_of_getLast? {es : Log} {e : ByteArray × Digest} (h : es.getLast? = some e) :
    lastAns es = e.2 := by
  simp [lastAns, h]

theorem ext_append (es : Log) (as : List Digest) (a : Digest) :
    ext es (as ++ [a]) = ext1 (ext es as) a := by
  simp [ext, List.foldl_append]

theorem ext_eq_append (es : Log) (as : List Digest) :
    ∃ t : Log, ext es as = es ++ t ∧ t.map Prod.snd = as := by
  induction as using List.reverseRecOn with
  | nil => exact ⟨[], by simp [ext], rfl⟩
  | append_singleton as a ih =>
    obtain ⟨t, ht, hs⟩ := ih
    refine ⟨t ++ [(squeezeQ (lastAns (ext es as)), a)], ?_, by simp [hs]⟩
    rw [ext_append, ext1, ht, List.append_assoc]

theorem length_ext (es : Log) (as : List Digest) : (ext es as).length = es.length + as.length := by
  obtain ⟨t, ht, hs⟩ := ext_eq_append es as
  rw [ht, List.length_append, ← hs, List.length_map]

theorem take_ext (es : Log) (as : List Digest) : (ext es as).take es.length = es := by
  obtain ⟨t, ht, -⟩ := ext_eq_append es as
  rw [ht, List.take_left']; rfl

theorem drop_ext (es : Log) (as : List Digest) : ((ext es as).drop es.length).map Prod.snd = as := by
  obtain ⟨t, ht, hs⟩ := ext_eq_append es as
  rw [ht, List.drop_left']; exact hs; rfl

theorem stmtOf_append {es : Log} (hne : es ≠ []) (t : Log) : stmtOf (es ++ t) = stmtOf es := by
  unfold stmtOf entAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (List.length_pos_iff.mpr hne)]

theorem kapOf_append {es : Log} (hne : es ≠ []) (t : Log) : kapOf (es ++ t) = kapOf es := by
  unfold kapOf; rw [stmtOf_append hne]

theorem kapOf_of {es : Log} {s : Digest} {n : ℕ} {h : Digest}
    (h0 : (es[0]?.bind fun e => seedOf e.1) = some (s, n, h)) : kapOf es = Nat.clog 2 n := by
  cases he : es[0]? with
  | none => rw [he] at h0; cases h0
  | some e =>
    rw [he, Option.bind_some] at h0
    simp [kapOf, stmtOf, entAt, List.getD_eq_getElem?_getD, he, h0]

theorem matches_ne_nil {es : Log} (hm : Matches es) : es ≠ [] := by
  rintro rfl
  obtain ⟨_, _, _, h0, -⟩ := hm
  simp at h0

/-- `Matches` with optional indexing. -/
theorem matches_iff' (es : Log) : Matches es ↔
    ∃ s n h, (es[0]?.bind fun e => seedOf e.1) = some (s, n, h) ∧ 1 ≤ n ∧ n ≤ chainCap ∧
      es.length ≤ len (Nat.clog 2 n) ∧
      ∀ i e e', es[i]? = some e → es[i + 1]? = some e' →
        stateIn e'.1 = some e.2 ∧ ∃ st, (shape (Nat.clog 2 n))[i + 1]? = some st ∧ st.matches e'.1 := by
  constructor
  · rintro ⟨s, n, h, h0, h1, h2, hl, H⟩
    refine ⟨s, n, h, h0, h1, h2, hl, fun i e e' he he' => ?_⟩
    obtain ⟨hi1, rfl⟩ := List.getElem?_eq_some_iff.mp he'
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hs, hm⟩ := H i hi1
    exact ⟨hs, _, List.getElem?_eq_getElem (by unfold len at hl; omega), hm⟩
  · rintro ⟨s, n, h, h0, h1, h2, hl, H⟩
    refine ⟨s, n, h, h0, h1, h2, hl, fun i hi => ?_⟩
    obtain ⟨hs, st, hst, hm⟩ := H i es[i] es[i + 1] (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem hi)
    refine ⟨hs, ?_⟩
    rw [List.getElem?_eq_getElem (by unfold len at hl; omega), Option.some.injEq] at hst
    rw [hst]; exact hm

theorem matches_len {es : Log} (hm : Matches es) : es.length ≤ len (kapOf es) := by
  obtain ⟨s, n, h, h0, -, -, hl, -⟩ := (matches_iff' es).mp hm
  rwa [kapOf_of h0]

theorem matches_get {es : Log} (hm : Matches es) {i : ℕ} {e e' : ByteArray × Digest}
    (he : es[i]? = some e) (he' : es[i + 1]? = some e') :
    stateIn e'.1 = some e.2 ∧ ∃ st, (shape (kapOf es))[i + 1]? = some st ∧ st.matches e'.1 := by
  obtain ⟨s, n, h, h0, -, -, -, H⟩ := (matches_iff' es).mp hm
  rw [kapOf_of h0]
  exact H i e e' he he'

/-- **One more entry matches** iff the next step of the shape matches its query and its state is
the last answer. -/
theorem matches_append_iff {es : Log} (hm : Matches es) (x : ByteArray × Digest) :
    Matches (es ++ [x]) ↔ ∃ st, (shape (kapOf es))[es.length]? = some st ∧
      stateIn x.1 = some (lastAns es) ∧ st.matches x.1 := by
  have hne := matches_ne_nil hm
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  obtain ⟨s, n, h, h0, h1, h2, hl, H⟩ := (matches_iff' es).mp hm
  have hk := kapOf_of h0
  have hlast : es[es.length - 1]? = some (es.getLast hne) := by
    rw [List.getLast_eq_getElem]; exact List.getElem?_eq_getElem _
  have hla : lastAns es = (es.getLast hne).2 := by
    simp [lastAns, List.getLast?_eq_getLast hne]
  rw [matches_iff', hk, hla]
  constructor
  · rintro ⟨s', n', h', h0', -, -, hl', H'⟩
    rw [List.getElem?_append_left hpos, h0] at h0'
    simp only [Option.some.injEq, Prod.mk.injEq] at h0'
    obtain ⟨rfl, rfl, rfl⟩ := h0'
    obtain ⟨hs, st, hst, hm'⟩ := H' (es.length - 1) (es.getLast hne) x
      (by rw [List.getElem?_append_left (by omega)]; exact hlast)
      (by rw [show es.length - 1 + 1 = es.length by omega]; simp)
    rw [show es.length - 1 + 1 = es.length by omega] at hst
    exact ⟨st, hst, hs, hm'⟩
  · rintro ⟨st, hst, hs, hm'⟩
    have hlt : es.length < len (Nat.clog 2 n) := by
      by_contra hc
      rw [List.getElem?_eq_none (by unfold len at hc; omega)] at hst
      cases hst
    refine ⟨s, n, h, by rw [List.getElem?_append_left hpos, h0], h1, h2, by simp; omega,
      fun i e e' he he' => ?_⟩
    by_cases hi : i + 1 < es.length
    · rw [List.getElem?_append_left hi] at he'
      rw [List.getElem?_append_left (by omega)] at he
      exact H i e e' he he'
    · have hi' : i + 1 = es.length := by
        have := (List.getElem?_eq_some_iff.mp he').1; simp at this; omega
      rw [hi', List.getElem?_concat_length, Option.some.injEq] at he'
      subst he'
      rw [List.getElem?_append_left (by omega), show i = es.length - 1 by omega, hlast,
        Option.some.injEq] at he
      subst he
      exact ⟨hs, st, by rw [hi']; exact hst, hm'⟩

/-- A query matching the squeeze step with state `st` is `squeezeQ st`. -/
theorem eq_squeezeQ {q : ByteArray} {st : Digest} (hm : Step.squeeze.matches q)
    (hs : stateIn q = some st) : q = squeezeQ st := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [squeezeQ_data]
  simp only [Step.matches, Step.check, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨htag, hsz⟩ := hm
  unfold tagOf at htag
  unfold stateIn at hs
  cases hq : q.data.toList with
  | nil => rw [hq] at htag; cases htag
  | cons b rest =>
    rw [hq] at htag hs
    simp only [List.head?_cons, Option.some.injEq] at htag
    subst htag
    have hlen : rest.length = 32 := by
      have : q.data.toList.length = 33 := by rw [Array.length_toList]; exact hsz
      rw [hq] at this; simpa using this
    dsimp only at hs
    rw [dite_eq_left (Or.inr ⟨rfl, hlen⟩), Option.some.injEq] at hs
    rw [← hs]
    simp [Vector.toList, List.take_of_length_le hlen.le]

/-- On the squeeze positions after `s0`, a matching chain is the formal extension of its first
`s0 + 1` entries by its later answers. -/
theorem ext_take {es : Log} (hm : Matches es) {s0 : ℕ} (hs : s0 < es.length)
    (hsq : ∀ p, s0 < p → p < es.length → (shape (kapOf es))[p]? = some .squeeze) :
    es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) := by
  suffices H : ∀ k, s0 + 1 + k ≤ es.length →
      es.take (s0 + 1 + k) = ext (es.take (s0 + 1)) (((es.take (s0 + 1 + k)).drop (s0 + 1)).map
        Prod.snd) by
    have := H (es.length - (s0 + 1)) (by omega)
    rwa [show s0 + 1 + (es.length - (s0 + 1)) = es.length by omega, List.take_length] at this
  intro k
  induction k with
  | zero =>
    intro _
    simp [ext]
  | succ k ih =>
    intro hk
    have hn : s0 + 1 + k < es.length := by omega
    rw [show s0 + 1 + (k + 1) = s0 + 1 + k + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hn, Option.toList_some, List.drop_append_of_le_length
        (by simp; omega), List.map_append, List.map_cons, List.map_nil, ext_append, ← ih (by omega)]
    simp only [List.map_cons, List.map_nil, ext1]
    congr 1
    have hprev : es[s0 + k]? = some es[s0 + k] := List.getElem?_eq_getElem (by omega)
    have hcur : es[s0 + k + 1]? = some es[s0 + 1 + k] := by
      rw [show s0 + k + 1 = s0 + 1 + k by omega]; exact List.getElem?_eq_getElem hn
    obtain ⟨hst, st, hsh, hmt⟩ := matches_get hm hprev hcur
    rw [show s0 + k + 1 = s0 + 1 + k by omega, hsq _ (by omega) hn, Option.some.injEq] at hsh
    subst hsh
    have hla : lastAns (es.take (s0 + 1 + k)) = es[s0 + k].2 := by
      rw [lastAns, List.getLast?_eq_getElem?, List.length_take,
        show min (s0 + 1 + k) es.length - 1 = s0 + k by omega, List.getElem?_take_of_lt
          (by omega), hprev]
      rfl
    rw [hla, ← eq_squeezeQ hmt hst]

end Chains

/-! ## Part A2: the conditional counts -/

section Counts

variable (D : Log → Log → Prop)

theorem condCount_split (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length < r) :
    ∑ a : Digest, condCount D L₀ es₀ r (pre ++ [a]) = 2 ^ 256 * condCount D L₀ es₀ r pre := by
  classical
  unfold condCount
  obtain ⟨k, hk⟩ : ∃ k, r - pre.length = k + 1 := ⟨r - pre.length - 1, by omega⟩
  have hk' : ∀ a : Digest, r - (pre ++ [a]).length = k := fun a => by simp; omega
  simp only [hk', hk]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Nat.cast_sum, extCount_split, show 256 * (k + 1) = 256 * k + 256 by ring, pow_add, mul_inv]
  have h2 : (2 : ℝ≥0) ^ 256 ≠ 0 := by positivity
  have h3 : (2 : ℝ≥0) ^ (256 * k) ≠ 0 := by positivity
  field_simp

open Classical in
theorem condCount_last (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length = r) :
    condCount D L₀ es₀ r pre = if EscAtG D L₀ (ext es₀ pre) then 1 else 0 := by
  classical
  unfold condCount
  rw [h, Nat.sub_self, mul_zero, pow_zero, div_one, extCount, Finset.card_filter,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [List.ofFn_zero, List.append_nil]
  split_ifs <;> simp

end Counts


/-! ## Part A2: the local inequality from per-position facts -/

section Local

variable {D : Log → Log → Prop}

open Classical in
/-- **The local inequality** `hloc` of `muG_step` for the charge `pRoundG D`, from the four
per-position facts of §9.2: an absorb never undooms (`habs`, `doom_absorb`), a middle answer of a
multi-answer round neither dooms nor undooms (`hmid`, `doom_mid`), a single-answer squeeze escapes
on at most `3 · 2^64` answers (`hsingle`, `esc_single_le`), and a multi-answer round's escape count
from its entry is at most `δ` (`hround`, `r0_esc_le`/`r7_esc_le`). The proof is §9.3 step 4. -/
theorem hloc_of (δ : ℝ≥0) (hδ : (3 * 2 ^ 64 : ℝ≥0) ≤ 2 ^ 256 * δ)
    (habs : ∀ L₀ es x k l, Matches (es ++ [x]) →
      (shape (kapOf es))[es.length]? = some (.absorb k l) → D L₀ es → D L₀ (es ++ [x]))
    (hmid : ∀ L₀ es x s0 r, Matches (es ++ [x]) → rnd (kapOf es) es.length = some (s0, r) →
      es.length < s0 + r → (D L₀ (es ++ [x]) ↔ D L₀ es))
    (hsingle : ∀ L₀ es, Matches es → (shape (kapOf es))[es.length]? = some .squeeze →
      rnd (kapOf es) es.length = none →
      (Finset.univ.filter fun a => D L₀ es ∧ ¬ D L₀ (ext1 es a)).card ≤ 3 * 2 ^ 64)
    (hround : ∀ L₀ es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (kapOf es₀) (s0 + 1) = some (s0, r) → condCount D L₀ es₀ r [] ≤ δ)
    (L₀ L₀' es : Log) (e : ByteArray × Digest) (q : ByteArray) (hm : Matches es)
    (hlast : es.getLast? = some e) (hL₀ : 2 ≤ es.length → L₀' = L₀)
    (hst : stateIn q = some e.2) :
    ∑ a : Digest, (if Matches (es ++ [(q, a)]) then
        (if EscAtG D L₀' (es ++ [(q, a)]) then 1 else 0) + pRoundG D L₀' (es ++ [(q, a)]) else 0) ≤
      2 ^ 256 * ((if q = squeezeQ e.2 then pRoundG D L₀ es else 0) + δ) := by
  have hne := matches_ne_nil hm
  have hla : lastAns es = e.2 := lastAns_of_getLast? hlast
  have hkap : ∀ x, kapOf (es ++ [x]) = kapOf es := fun x => kapOf_append hne _
  have hlen : ∀ x : ByteArray × Digest, (es ++ [x]).length - 1 = es.length := fun x => by simp
  have hiff : ∀ a, Matches (es ++ [(q, a)]) ↔
      ∃ st, (shape (kapOf es))[es.length]? = some st ∧ st.matches q := by
    intro a; rw [matches_append_iff hm, hla]; simp [hst]
  by_cases hex : ∃ st, (shape (kapOf es))[es.length]? = some st ∧ st.matches q
  swap
  · have : ∀ a, ¬ Matches (es ++ [(q, a)]) := fun a h => hex ((hiff a).mp h)
    simp only [this, ite_false, Finset.sum_const_zero]; exact zero_le
  obtain ⟨st, hsh, hsm⟩ := hex
  have hM : ∀ a, Matches (es ++ [(q, a)]) := fun a => (hiff a).mpr ⟨st, hsh, hsm⟩
  simp only [hM, ite_true]
  have hp1 : 1 ≤ es.length := List.length_pos_iff.mpr hne
  have hpr0 : ∀ L₁ x, rnd (kapOf es) es.length = none → pRoundG D L₁ (es ++ [x]) = 0 := by
    intro L₁ x hr; unfold pRoundG; rw [hkap, hlen, hr]
  cases st with
  | seed => exact absurd hsh (shape_ne_seed _ _ hp1)
  | absorb k l =>
    have hr := rnd_none_of_absorb hsh
    have hz : ∀ a, (if EscAtG D L₀' (es ++ [(q, a)]) then 1 else 0) +
        pRoundG D L₀' (es ++ [(q, a)]) = (0 : ℝ≥0) := by
      intro a
      rw [hpr0 _ _ hr, add_zero, ite_eq_right]
      rintro ⟨-, hd, hnd⟩
      rw [List.dropLast_concat] at hd
      exact hnd (habs L₀' es _ k l (hM a) hsh hd)
    simp only [hz, Finset.sum_const_zero]; exact zero_le
  | squeeze =>
    have hq : q = squeezeQ e.2 := eq_squeezeQ hsm hst
    have hp2 : 2 ≤ es.length := by
      by_contra h
      have h1 : es.length = 1 := by omega
      rw [h1, shape_one] at hsh; cases hsh
    have hL := hL₀ hp2
    subst hL hq
    rw [ite_eq_left rfl]
    have hext1 : ∀ a, es ++ [(squeezeQ e.2, a)] = ext1 es a := fun a => by rw [ext1, hla]
    cases hr : rnd (kapOf es) es.length with
    | none =>
      calc ∑ a, ((if EscAtG D L₀' (es ++ [(squeezeQ e.2, a)]) then 1 else 0) +
              pRoundG D L₀' (es ++ [(squeezeQ e.2, a)]))
          ≤ ∑ a, (if D L₀' es ∧ ¬ D L₀' (ext1 es a) then 1 else 0 : ℝ≥0) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [hpr0 _ _ hr, add_zero]
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exfalso; obtain ⟨-, hd, hnd⟩ := h1
              rw [List.dropLast_concat, hext1] at *
              exact h2 ⟨hd, hnd⟩
            · exact zero_le
            · exact le_rfl
        _ = ((Finset.univ.filter fun a => D L₀' es ∧ ¬ D L₀' (ext1 es a)).card : ℝ≥0) := by
            rw [Finset.sum_boole]
        _ ≤ 3 * 2 ^ 64 := by exact_mod_cast hsingle L₀' es hm hsh hr
        _ ≤ 2 ^ 256 * δ := hδ
        _ ≤ 2 ^ 256 * (pRoundG D L₀' es + δ) := by gcongr; exact le_add_self
    | some sr =>
      obtain ⟨s0, r⟩ := sr
      obtain ⟨hs0, hpr, hspec⟩ := rnd_spec hr
      have hes : es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) :=
        ext_take hm (by omega) (fun p h1 h2 => (hspec.sq p h1 (by omega)).1)
      have hes0len : (es.take (s0 + 1)).length = s0 + 1 := by simp; omega
      have hnew : ∀ a, es ++ [(squeezeQ e.2, a)] =
          ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a; rw [ext_append, ← hes, hext1]
      have hterm : ∀ a, (if EscAtG D L₀' (es ++ [(squeezeQ e.2, a)]) then 1 else 0) +
          pRoundG D L₀' (es ++ [(squeezeQ e.2, a)]) =
          condCount D L₀' (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a
        have hpRnew : pRoundG D L₀' (es ++ [(squeezeQ e.2, a)]) =
            if es.length - s0 < r then
              condCount D L₀' (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a])
            else 0 := by
          unfold pRoundG
          rw [hkap, hlen, hr]
          simp only
          rw [List.take_append_of_le_length (by omega),
            List.drop_append_of_le_length (by omega), List.map_append]
          rfl
        by_cases hmidp : es.length < s0 + r
        · rw [ite_eq_right, zero_add, hpRnew, ite_eq_left (by omega)]
          rintro ⟨-, hd, hnd⟩
          rw [List.dropLast_concat] at hd
          exact hnd ((hmid L₀' es _ s0 r (hM _) hr hmidp).mpr hd)
        · rw [hpRnew, ite_eq_right (show ¬ (es.length - s0 < r) by omega), add_zero,
            condCount_last D _ _ (by simp; omega), hnew]
      rw [Finset.sum_congr rfl (fun a _ => hterm a), condCount_split D _ _ (by simp; omega)]
      gcongr
      by_cases hfirst : es.length = s0 + 1
      · have htk : es.take (s0 + 1) = es := List.take_of_length_le (by omega)
        have hpre : (es.drop (s0 + 1)).map Prod.snd = [] := by
          rw [List.drop_of_length_le (by omega)]; rfl
        rw [hpre]
        refine le_trans ?_ le_add_self
        refine hround L₀' _ s0 r (by rw [htk]; exact hm) hes0len ?_
        rw [htk, (hspec.sq (s0 + 1) (by omega) (by omega)).2]
      · have hp : pRoundG D L₀' es =
            condCount D L₀' (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) := by
          unfold pRoundG
          rw [(hspec.sq (es.length - 1) (by omega) (by omega)).2]
          simp only
          rw [ite_eq_left (by omega)]
        rw [hp]; exact le_self_add

end Local


/-! ## Part A2: the step law of `μ` from the per-position facts -/

section StepLaw

/-- The knowledge error of the leaf SNARK: `2^-129`. -/
noncomputable def εKS : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 129

/-- The R7 escape bound, the largest per-query term: `(4/5) · 2^-129`. -/
noncomputable def δKS : ℝ≥0 := (4 / 5) / 2 ^ 129

/-- **The error budget** (`eps_budget` with the `2^-256` term): L-K1's bad fraction plus `δ` is at
most `2^-129`. -/
theorem eps_le : (((2 ^ 96 * (3 * 2 ^ 8 + 1) + 1 : ℕ) : ℝ≥0)) / 2 ^ 256 + δKS ≤ εKS := by
  rw [← NNReal.coe_le_coe, εKS, δKS]
  push_cast
  norm_num

theorem single_le_δ : (3 * 2 ^ 64 : ℝ≥0) ≤ 2 ^ 256 * δKS := by
  rw [← NNReal.coe_le_coe, δKS]
  push_cast
  norm_num

theorem pRoundG_seed (D : Log → Log → Prop) (L₀ : Log) (e : ByteArray × Digest) :
    pRoundG D L₀ [e] = 0 := by
  have : rnd (kapOf [e]) 0 = none := by
    unfold rnd
    have := pre8_length (kapOf [e])
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  unfold pRoundG
  simp only [List.length_singleton, Nat.sub_self, this]

open Classical in
/-- **`mu_step` from the per-position facts**: the contract's `step` law with error `2^-129` for
`muG D (pRoundG D)`, given `doom_absorb`, `doom_mid`, `esc_single_le` and the round bounds. -/
theorem muG_step_of {D : Log → Log → Prop}
    (habs : ∀ L₀ es x k l, Matches (es ++ [x]) →
      (shape (kapOf es))[es.length]? = some (.absorb k l) → D L₀ es → D L₀ (es ++ [x]))
    (hmid : ∀ L₀ es x s0 r, Matches (es ++ [x]) → rnd (kapOf es) es.length = some (s0, r) →
      es.length < s0 + r → (D L₀ (es ++ [x]) ↔ D L₀ es))
    (hsingle : ∀ L₀ es, Matches es → (shape (kapOf es))[es.length]? = some .squeeze →
      rnd (kapOf es) es.length = none →
      (Finset.univ.filter fun a => D L₀ es ∧ ¬ D L₀ (ext1 es a)).card ≤ 3 * 2 ^ 64)
    (hround : ∀ L₀ es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (kapOf es₀) (s0 + 1) = some (s0, r) → condCount D L₀ es₀ r [] ≤ δKS)
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D (pRoundG D) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D (pRoundG D) (L ++ [(q, a)]) ≤ (muG D (pRoundG D) L + εKS) * 2 ^ 256 := by
  refine (muG_step δKS (fun L₀ e _ => pRoundG_seed D L₀ e)
    (fun L₀ L₀' es e q hm hlast hL₀ hst =>
      hloc_of δKS single_le_δ habs hmid hsingle hround L₀ L₀' es e q hm hlast hL₀ hst)
    hl hμ hq).trans ?_
  exact mul_le_mul_left (add_le_add_right eps_le _) _

end StepLaw


/-! ## Part D: the positions of the leaf transcript -/

section LeafPositions
open PCS

theorem getElem?_flatten_rep2 {α : Type} (a b : α) (n i : ℕ) :
    ((List.replicate n [a, b]).flatten)[i]? =
      if i < 2 * n then some (if i % 2 = 0 then a else b) else none := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    rcases i with _ | i
    · simp
    rcases i with _ | i
    · simp; omega
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, ih]
      split_ifs <;> first | omega | rfl

theorem length_flatten_rep2 {α : Type} (a b : α) (n : ℕ) :
    ((List.replicate n [a, b]).flatten).length = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; ring

theorem posClass_seed (κ : ℕ) : posClass κ (0) = .seed := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_seed (κ : ℕ) : (shape κ)[0]? = some (.seed) := by
  simp [shape, List.append_assoc]

theorem posClass_root (κ : ℕ) : posClass κ (1) = .root := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_root (κ : ℕ) : (shape κ)[1]? = some (.absorb 0x01 31) := by
  simp [shape, List.append_assoc]

theorem posClass_r0 (κ : ℕ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ rows κ) : posClass κ (1 + j) = .r0 j := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_r0 (κ : ℕ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ rows κ) : (shape κ)[1 + j]? = some (.squeeze) := by
  exact shape_R0 κ (1 + j) (by omega) (by omega)

theorem posClass_ubar (κ : ℕ) : posClass κ (pU κ) = .ubar := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_ubar (κ : ℕ) : (shape κ)[pU κ]? = some (.absorb 0x02 (24 * msgLen κ)) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_tau (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : posClass κ (pTau κ l) = .tau l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_tau (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : (shape κ)[pTau κ l]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_gOut (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : posClass κ (pG κ l) = .gOut l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_gOut (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : (shape κ)[pG κ l]? = some (.absorb 0x03 96) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_rx (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : posClass κ (pG κ l + 1) = .rx l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_rx (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : (shape κ)[pG κ l + 1]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_tri (κ : ℕ) : posClass κ (pTri κ) = .tri := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_tri (κ : ℕ) : (shape κ)[pTri κ]? = some (.absorb 0x04 72) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_rho (κ : ℕ) : posClass κ (pTri κ + 1) = .rho := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_rho (κ : ℕ) : (shape κ)[pTri κ + 1]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_gIn (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : posClass κ (pGi κ l) = .gIn l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_gIn (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : (shape κ)[pGi κ l]? = some (.absorb 0x05 72) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_ry (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : posClass κ (pGi κ l + 1) = .ry l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_ry (κ : ℕ) (l : ℕ) (h : l < 15 + κ) : (shape κ)[pGi κ l + 1]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_sl (κ : ℕ) : posClass κ (pS κ) = .sl := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_sl (κ : ℕ) : (shape κ)[pS κ]? = some (.absorb 0x06 1536) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_f (κ : ℕ) (q : ℕ) (h : q < 6) : posClass κ (pF κ q) = .f q := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_f (κ : ℕ) (q : ℕ) (h : q < 6) : (shape κ)[pF κ q]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_gRs (κ : ℕ) (l : ℕ) (h : l < 8 + κ) : posClass κ (pGr κ l) = .gRs l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_gRs (κ : ℕ) (l : ℕ) (h : l < 8 + κ) : (shape κ)[pGr κ l]? = some (.absorb 0x07 72) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_rr (κ : ℕ) (l : ℕ) (h : l < 8 + κ) : posClass κ (pGr κ l + 1) = .rr l := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_rr (κ : ℕ) (l : ℕ) (h : l < 8 + κ) : (shape κ)[pGr κ l + 1]? = some (.squeeze) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_vabs (κ : ℕ) : posClass κ (pV κ) = .vabs := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]

theorem shape_vabs (κ : ℕ) : (shape κ)[pV κ]? = some (.absorb 0x08 (24 * msgLen κ)) := by
  simp only [shape, List.append_assoc]
  try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]
  simp (disch := first | (simp [length_flatten_rep2]; done) | (simp [length_flatten_rep2]; omega)) only [List.getElem?_append_right,
    List.getElem?_append_left]
  try simp only [List.length_cons, List.length_nil, List.length_replicate, getElem?_flatten_rep2,
    List.getElem?_replicate, length_flatten_rep2]
  try simp only [List.getElem?_cons, List.getElem?_nil]
  first | rfl | (split_ifs <;> first | rfl | omega) | simp

theorem posClass_r7 (κ : ℕ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ nJ κ) : posClass κ (pV κ + j) = .r7 j := by
  unfold posClass
  simp (disch := (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega) only [ite_eq_right, ite_eq_left, ↓reduceIte]
  congr 1; (try simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV]); omega

theorem shape_r7 (κ : ℕ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ nJ κ) : (shape κ)[pV κ + j]? = some (.squeeze) := by
  have := pre8_length κ; have := len_eq κ
  exact shape_R7 κ _ (by simp only [pV, pS, pTri] at *; omega) (by simp only [pV, pS, pTri] at *; omega)


theorem len_pV (κ : ℕ) : len κ = pV κ + nJ κ + 1 := by
  rw [len_eq, pre8_length]; simp only [pV, pS, pTri]; ring

/-- **Every position of the shape is one of §6.2's steps.** -/
theorem pos_cover (κ p : ℕ) (hp : p < len κ) :
    p = 0 ∨ p = 1 ∨ (∃ j, 1 ≤ j ∧ j ≤ rows κ ∧ p = 1 + j) ∨ p = pU κ ∨
    (∃ l < 15 + κ, p = pTau κ l) ∨ (∃ l < 15 + κ, p = pG κ l) ∨
    (∃ l < 15 + κ, p = pG κ l + 1) ∨ p = pTri κ ∨ p = pTri κ + 1 ∨
    (∃ l < 15 + κ, p = pGi κ l) ∨ (∃ l < 15 + κ, p = pGi κ l + 1) ∨ p = pS κ ∨
    (∃ q < 6, p = pF κ q) ∨ (∃ l < 8 + κ, p = pGr κ l) ∨ (∃ l < 8 + κ, p = pGr κ l + 1) ∨
    p = pV κ ∨ (∃ j, 1 ≤ j ∧ j ≤ nJ κ ∧ p = pV κ + j) := by
  rw [len_pV] at hp
  simp only [pU, pTau, pG, pTri, pGi, pS, pF, pGr, pV] at *
  by_cases h0 : p = 0
  · exact Or.inl h0
  right; by_cases h1 : p = 1
  · exact Or.inl h1
  right; by_cases h2 : p ≤ 1 + rows κ
  · exact Or.inl ⟨p - 1, by omega, by omega, by omega⟩
  right; by_cases h3 : p = 2 + rows κ
  · exact Or.inl h3
  right; by_cases h4 : p < 3 + rows κ + (15 + κ)
  · exact Or.inl ⟨p - (3 + rows κ), by omega, by omega⟩
  right; by_cases h5 : p < 3 + rows κ + 3 * (15 + κ)
  · by_cases hm : (p - (3 + rows κ + (15 + κ))) % 2 = 0
    · exact Or.inl ⟨(p - (3 + rows κ + (15 + κ))) / 2, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨(p - (3 + rows κ + (15 + κ))) / 2, by omega, by omega⟩)
  right; right; by_cases h6 : p = 3 + rows κ + 3 * (15 + κ)
  · exact Or.inl h6
  right; by_cases h7 : p = 3 + rows κ + 3 * (15 + κ) + 1
  · exact Or.inl h7
  right; by_cases h8 : p < 3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ)
  · by_cases hm : (p - (3 + rows κ + 3 * (15 + κ) + 2)) % 2 = 0
    · exact Or.inl ⟨(p - (3 + rows κ + 3 * (15 + κ) + 2)) / 2, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨(p - (3 + rows κ + 3 * (15 + κ) + 2)) / 2, by omega, by omega⟩)
  right; right; by_cases h9 : p = 3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ)
  · exact Or.inl h9
  right; by_cases h10 : p < 3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7
  · exact Or.inl ⟨p - (3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 1), by omega, by omega⟩
  right; by_cases h11 : p < 3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7 + 2 * (8 + κ)
  · by_cases hm : (p - (3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7)) % 2 = 0
    · exact Or.inl ⟨(p - (3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7)) / 2, by omega, by omega⟩
    · exact Or.inr (Or.inl
        ⟨(p - (3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7)) / 2, by omega, by omega⟩)
  right; right; by_cases h12 : p = 3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7 + 2 * (8 + κ)
  · exact Or.inl h12
  right
  exact ⟨p - (3 + rows κ + 3 * (15 + κ) + 2 + 2 * (15 + κ) + 7 + 2 * (8 + κ)), by omega, by omega,
    by omega⟩

end LeafPositions


/-! ## Part D: locality of the leaf view -/

section Locality
open PCS Spartan

/-- `es` and `es'` agree on the positions below `n`. -/
def AgreeTo (es es' : Log) (n : ℕ) : Prop := ∀ p < n, entAt es p = entAt es' p

theorem agree_append (es t : Log) : AgreeTo (es ++ t) es es.length := by
  intro p hp
  simp only [entAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]

theorem AgreeTo.mono {es es' : Log} {n m : ℕ} (h : AgreeTo es es' n) (hm : m ≤ n) :
    AgreeTo es es' m := fun p hp => h p (by omega)

theorem AgreeTo.symm {es es' : Log} {n : ℕ} (h : AgreeTo es es' n) : AgreeTo es' es n :=
  fun p hp => (h p hp).symm

theorem map_range_take_congr {α : Type} {N : ℕ} {g g' : ℕ → α} (k : ℕ)
    (h : ∀ l < k, l < N → g l = g' l) :
    ((List.range N).map g).take k = ((List.range N).map g').take k := by
  rw [← List.map_take, ← List.map_take, List.take_range]
  exact List.map_congr_left fun l hl => by
    rw [List.mem_range] at hl; exact h l (by omega) (by omega)

theorem getD_of_take_eq {α : Type} {xs ys : List α} {k l : ℕ} (d : α) (h : xs.take k = ys.take k)
    (hl : l < k) : xs.getD l d = ys.getD l d := by
  have := congrArg (fun zs => zs[l]?) h
  simp only [List.getElem?_take, hl, ite_true] at this
  simp only [List.getD_eq_getElem?_getD, this]

theorem map_range_congr {α : Type} {N : ℕ} {g g' : ℕ → α} (h : ∀ l < N, g l = g' l) :
    (List.range N).map g = (List.range N).map g' :=
  List.map_congr_left fun l hl => h l (List.mem_range.mp hl)

variable {es es' : Log} {n : ℕ} (h : AgreeTo es es' n)
include h

theorem chAt_agree {p : ℕ} (hp : p < n) : chAt es p = chAt es' p := by
  unfold chAt; rw [h p hp]

theorem efsAt_agree {p : ℕ} (c : ℕ) (hp : p < n) : efsAt es p c = efsAt es' p c := by
  unfold efsAt; rw [h p hp]

theorem stmtOf_agree (hn : 0 < n) : stmtOf es = stmtOf es' := by
  unfold stmtOf; rw [h 0 hn]

theorem kapOf_agree (hn : 0 < n) : kapOf es = kapOf es' := by
  unfold kapOf; rw [stmtOf_agree h hn]

theorem rootOf_agree (hn : 1 < n) : rootOf es = rootOf es' := by
  unfold rootOf; rw [h 1 hn]

theorem rVec_agree (κ : ℕ) (hn : 1 + rows κ < n) : rVec κ es = rVec κ es' :=
  map_range_congr fun l hl => chAt_agree h (by omega)

theorem ubarOf_agree (κ : ℕ) (hn : pU κ < n) : ubarOf κ es = ubarOf κ es' :=
  efsAt_agree h _ hn

theorem tauOf_take_agree (κ k : ℕ) (hn : pTau κ 0 + k ≤ n) :
    (tauOf κ es).take k = (tauOf κ es').take k :=
  map_range_take_congr k fun l hl _ => chAt_agree h (by simp only [pTau] at *; omega)

theorem tauOf_agree (κ : ℕ) (hn : pG κ 0 ≤ n) : tauOf κ es = tauOf κ es' :=
  map_range_congr fun l hl => chAt_agree h (by simp only [pTau, pG] at *; omega)

theorem gOut_agree (κ l : ℕ) (hn : pG κ l < n) : gOut κ es l = gOut κ es' l :=
  efsAt_agree h _ hn

theorem rxOf_take_agree (κ k : ℕ) (hn : pG κ 0 + 2 * k ≤ n) :
    (rxOf κ es).take k = (rxOf κ es').take k :=
  map_range_take_congr k fun l hl _ => chAt_agree h (by simp only [pG] at *; omega)

theorem rxOf_agree (κ : ℕ) (hn : pTri κ ≤ n) : rxOf κ es = rxOf κ es' :=
  map_range_congr fun l hl => chAt_agree h (by simp only [pG, pTri] at *; omega)

theorem clOut_agree (κ i : ℕ) (hn : pG κ 0 + 2 * i ≤ n) : clOut κ es i = clOut κ es' i := by
  cases i with
  | zero => rfl
  | succ l =>
    simp only [clOut]
    rw [gOut_agree h κ l (by simp only [pG] at *; omega)]
    rw [getD_of_take_eq 0 (rxOf_take_agree h κ (l + 1) hn) (by omega)]

theorem triOf_agree (κ : ℕ) (hn : pTri κ < n) : triOf κ es = triOf κ es' := by
  unfold triOf; rw [efsAt_agree h _ hn]

theorem rhoOf_agree (κ : ℕ) (hn : pTri κ + 1 < n) : rhoOf κ es = rhoOf κ es' :=
  chAt_agree h hn

theorem gIn_agree (κ l : ℕ) (hn : pGi κ l < n) : gIn κ es l = gIn κ es' l :=
  efsAt_agree h _ hn

theorem ryOf_take_agree (κ k : ℕ) (hn : pGi κ 0 + 2 * k ≤ n) :
    (ryOf κ es).take k = (ryOf κ es').take k :=
  map_range_take_congr k fun l hl _ => chAt_agree h (by simp only [pGi] at *; omega)

theorem ryOf_agree (κ : ℕ) (hn : pS κ ≤ n) : ryOf κ es = ryOf κ es' :=
  map_range_congr fun l hl => chAt_agree h (by simp only [pGi, pS] at *; omega)

theorem clIn_agree (κ i : ℕ) (hn : pGi κ 0 + 2 * i ≤ n) : clIn κ es i = clIn κ es' i := by
  cases i with
  | zero =>
    simp only [clIn]
    rw [triOf_agree h κ (by simp only [pGi] at hn; omega),
      rhoOf_agree h κ (by simp only [pGi] at hn; omega)]
  | succ l =>
    simp only [clIn]
    rw [gIn_agree h κ l (by simp only [pGi] at *; omega)]
    rw [getD_of_take_eq 0 (ryOf_take_agree h κ (l + 1) hn) (by omega)]

theorem slicesOf_agree (κ : ℕ) (hn : pS κ < n) : slicesOf κ es = slicesOf κ es' :=
  efsAt_agree h _ hn

theorem fsOf_take_agree (κ k : ℕ) (hn : pF κ 0 + k ≤ n) :
    (fsOf κ es).take k = (fsOf κ es').take k :=
  map_range_take_congr k fun l hl _ => chAt_agree h (by simp only [pF] at *; omega)

theorem fsOf_agree (κ : ℕ) (hn : pGr κ 0 ≤ n) : fsOf κ es = fsOf κ es' :=
  map_range_congr fun l hl => chAt_agree h (by simp only [pF, pGr] at *; omega)

theorem gRs_agree (κ l : ℕ) (hn : pGr κ l < n) : gRs κ es l = gRs κ es' l :=
  efsAt_agree h _ hn

theorem rrOf_take_agree (κ k : ℕ) (hn : pGr κ 0 + 2 * k ≤ n) :
    (rrOf κ es).take k = (rrOf κ es').take k :=
  map_range_take_congr k fun l hl _ => chAt_agree h (by simp only [pGr] at *; omega)

theorem rrOf_agree (κ : ℕ) (hn : pV κ ≤ n) : rrOf κ es = rrOf κ es' :=
  map_range_congr fun l hl => chAt_agree h (by simp only [pGr, pV] at *; omega)

theorem rhiOf_agree (κ : ℕ) (hn : pS κ ≤ n) : rhiOf κ es = rhiOf κ es' := by
  unfold rhiOf; rw [ryOf_agree h κ hn]

theorem clRs_agree (κ i : ℕ) (hn : pGr κ 0 + 2 * i ≤ n) : clRs κ es i = clRs κ es' i := by
  cases i with
  | zero =>
    simp only [clRs]
    rw [fsOf_agree h κ (by omega), slicesOf_agree h κ (by simp only [pGr] at hn; omega)]
  | succ l =>
    simp only [clRs]
    rw [gRs_agree h κ l (by simp only [pGr] at *; omega)]
    rw [getD_of_take_eq 0 (rrOf_take_agree h κ (l + 1) hn) (by omega)]

theorem vOf_agree (κ : ℕ) (hn : pV κ < n) : vOf κ es = vOf κ es' :=
  efsAt_agree h _ hn

theorem aOf_agree (κ : ℕ) (hn : pV κ ≤ n) : aOf κ es = aOf κ es' := by
  unfold aOf; rw [rrOf_agree h κ hn]

theorem Uof_agree (L₀ : Log) (hn : 1 < n) : HEq (Uof L₀ es) (Uof L₀ es') := by
  unfold Uof; rw [kapOf_agree h (by omega), rootOf_agree h hn]

end Locality


/-! ## Part D: rejection is local and monotone -/

section RejLemmas
open PCS Spartan

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

/-- Every check of `Rej` sits at a position in `[pG κ 0, pV κ]`. -/
theorem rej_pos {es : Log} (H : Rej ev es) :
    pG (kapOf es) 0 ≤ es.length - 1 := by
  simp only [Rej] at H
  rcases H with ⟨l, hl, hc, -⟩ | ⟨hc, -⟩ | ⟨l, hl, hc, -⟩ | ⟨hc, -⟩ | ⟨l, hl, hc, -⟩ | ⟨hc, -⟩ <;>
  · simp only [pG, pTri, pGi, pS, pGr, pV] at *; omega

/-- **Rejection transfers** to a list that agrees on every check position of `es` up to its own. -/
theorem rej_of_agree {es es' : Log} {n : ℕ} (h : AgreeTo es es' n) (hn : 0 < n)
    (hm : min (es.length - 1) (pV (kapOf es)) < n)
    (hm' : min (es.length - 1) (pV (kapOf es)) ≤ es'.length - 1) (H : Rej ev es) :
    Rej ev es' := by
  have hk := kapOf_agree h hn
  have hs := stmtOf_agree h hn
  simp only [Rej] at H ⊢
  rw [← hk, ← hs]
  generalize kapOf es = κ at *
  rcases H with ⟨l, hl, hc, hr⟩ | ⟨hc, hr⟩ | ⟨l, hl, hc, hr⟩ | ⟨hc, hr⟩ | ⟨l, hl, hc, hr⟩ | ⟨hc, hr⟩
  · have hp : pG κ l ≤ pV κ := by simp only [pG, pV, pS, pTri]; omega
    refine Or.inl ⟨l, hl, by omega, ?_⟩
    rwa [← gOut_agree h κ l (by omega), ← clOut_agree h κ l (by simp only [pG] at *; omega)]
  · have hp : pTri κ ≤ pV κ := by simp only [pV, pS]; omega
    refine Or.inr (Or.inl ⟨by omega, ?_⟩)
    rwa [← clOut_agree h κ _ (by simp only [pG, pTri] at *; omega),
      ← tauOf_agree h κ (by simp only [pG, pTri] at *; omega), ← rxOf_agree h κ (by omega),
      ← triOf_agree h κ (by omega)]
  · have hp : pGi κ l ≤ pV κ := by simp only [pGi, pV, pS]; omega
    refine Or.inr (Or.inr (Or.inl ⟨l, hl, by omega, ?_⟩))
    rwa [← gIn_agree h κ l (by omega), ← clIn_agree h κ l (by simp only [pGi] at *; omega)]
  · have hp : pS κ ≤ pV κ := by simp only [pV]; omega
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, ?_⟩)))
    rwa [← clIn_agree h κ _ (by simp only [pGi, pS] at *; omega),
      ← rxOf_agree h κ (by simp only [pS] at *; omega), ← ryOf_agree h κ (by omega),
      ← rhoOf_agree h κ (by simp only [pS] at *; omega), ← slicesOf_agree h κ (by omega)]
  · have hp : pGr κ l ≤ pV κ := by simp only [pGr, pV]; omega
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, by omega, ?_⟩))))
    rwa [← gRs_agree h κ l (by omega), ← clRs_agree h κ l (by simp only [pGr] at *; omega)]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))))
    rwa [← clRs_agree h κ _ (by simp only [pGr, pV] at *; omega),
      ← fsOf_agree h κ (by simp only [pGr, pV] at *; omega),
      ← rhiOf_agree h κ (by simp only [pV] at *; omega), ← rrOf_agree h κ (by omega),
      ← vOf_agree h κ (by omega)]

/-- **`rej_mono`**: rejection persists along a chain. -/
theorem rej_mono {es : Log} (hne : es ≠ []) (t : Log) (H : Rej ev es) : Rej ev (es ++ t) := by
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  exact rej_of_agree ev (agree_append es t).symm hpos (by omega) (by simp; omega) H

/-- Past `absorb(v)` no check is added: rejection is unchanged by more entries. -/
theorem rej_append_iff_full {es : Log} (hne : es ≠ []) (hV : pV (kapOf es) < es.length)
    (t : Log) : Rej ev (es ++ t) ↔ Rej ev es := by
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  refine ⟨fun H => ?_, rej_mono ev hne t⟩
  have hk : kapOf (es ++ t) = kapOf es := kapOf_append hne t
  exact rej_of_agree ev (agree_append es t) hpos (by rw [hk]; omega) (by rw [hk]; simp; omega) H

/-- Before `absorb(g_0)` nothing is checked. -/
theorem not_rej_early {es : Log} (h : es.length - 1 < pG (kapOf es) 0) : ¬ Rej ev es :=
  fun H => absurd (rej_pos ev H) (by omega)

end RejLemmas


/-! ## Part D: the rows of `Alg` are local -/

section AlgLocality
open PCS Spartan SoundnessPCS

variable {es es' : Log} {n : ℕ} (h : AgreeTo es es' n) (hn : 0 < n) (κ : ℕ)
  (U : Fin (rows κ) → Fin (cols κ) → F)
include h hn

theorem FS_agree : FS es ↔ FS es' := by unfold FS; rw [stmtOf_agree h hn]

theorem zOfU_agree : zOfU κ U es = zOfU κ U es' := by unfold zOfU; rw [stmtOf_agree h hn]

theorem matA_agree : matA κ es = matA κ es' := by unfold matA; rw [stmtOf_agree h hn]

theorem fTbl_agree : fTbl κ U es = fTbl κ U es' := by
  unfold fTbl; rw [matA_agree h hn, zOfU_agree h hn]

omit hn in
theorem FarDoom_agree (hr : 1 + rows κ < n) : FarDoom κ U es ↔ FarDoom κ U es' := by
  unfold FarDoom; rw [rVec_agree h κ hr]

theorem oTbls_agree (hp : pG κ 0 ≤ n) : oTbls κ U es = oTbls κ U es' := by
  unfold oTbls; rw [tauOf_agree h κ hp, matA_agree h hn, zOfU_agree h hn]

theorem iTbls_agree (hp : pTri κ + 1 < n) : iTbls κ U es = iTbls κ U es' := by
  unfold iTbls
  rw [rxOf_agree h κ (by omega), rhoOf_agree h κ hp, matA_agree h hn, zOfU_agree h hn]

omit hn in
theorem wTbls_agree (hp : pGr κ 0 ≤ n) : wTbls κ U es = wTbls κ U es' := by
  unfold wTbls
  rw [fsOf_agree h κ hp, rhiOf_agree h κ (by simp only [pGr] at hp; omega)]

omit hn in
theorem deltaOf_agree (hp : pS κ < n) : deltaOf κ U es = deltaOf κ U es' := by
  unfold deltaOf; rw [slicesOf_agree h κ hp, rhiOf_agree h κ (by omega)]

omit hn in
theorem VWrong_agree (hp : pV κ < n) : VWrong κ U es ↔ VWrong κ U es' := by
  unfold VWrong; rw [vOf_agree h κ hp, aOf_agree h κ (by omega)]

omit hn in
theorem Dof_agree (hp : pV κ < n) : Dof κ U es = Dof κ U es' := by
  unfold Dof
  rw [rVec_agree h κ (by simp only [pV, pS, pTri] at hp; omega),
    ubarOf_agree h κ (by simp only [pU, pV, pS, pTri] at *; omega), vOf_agree h κ hp,
    aOf_agree h κ (by omega)]

omit hn in
theorem bOf_agree (hp : pV κ + nJ κ < n) : bOf κ es = bOf κ es' := by
  funext j; unfold bOf; rw [h _ (by omega)]

end AlgLocality


/-- The position of a class. -/
def posOfC (κ : ℕ) : PosClass → ℕ
  | .seed => 0
  | .root => 1
  | .r0 j => 1 + j
  | .ubar => pU κ
  | .tau l => pTau κ l
  | .gOut l => pG κ l
  | .rx l => pG κ l + 1
  | .tri => pTri κ
  | .rho => pTri κ + 1
  | .gIn l => pGi κ l
  | .ry l => pGi κ l + 1
  | .sl => pS κ
  | .f q => pF κ q
  | .gRs l => pGr κ l
  | .rr l => pGr κ l + 1
  | .vabs => pV κ
  | .r7 j => pV κ + j

section AlgLocality2
open PCS Spartan SoundnessPCS

/-- **Every row of §9.2's table reads only positions up to its own.** -/
theorem algRow_agree {es es' : Log} {n : ℕ} (h : AgreeTo es es' n) (κ : ℕ)
    (U : Fin (rows κ) → Fin (cols κ) → F) (c : PosClass) (hc : posOfC κ c < n) :
    AlgRow κ U es c ↔ AlgRow κ U es' c := by
  have hn : 0 < n := by omega
  have hU : ∀ m, pU κ ≤ m → m < n → 1 + rows κ < n := fun m h1 h2 => by
    simp only [pU] at h1; omega
  cases c with
  | seed => exact FS_agree h hn
  | root => exact FS_agree h hn
  | r0 j =>
    simp only [AlgRow, posOfC] at hc ⊢
    split_ifs with hj
    · exact FS_agree h hn
    · rw [FS_agree h hn, FarDoom_agree h κ U (by omega)]
  | ubar =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FS_agree h hn, FarDoom_agree h κ U (hU _ le_rfl hc)]
  | tau l =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pTau κ l) (by simp [pU, pTau]; omega) hc), fTbl_agree h hn,
      tauOf_take_agree h κ (l + 1) (by simp only [pTau] at *; omega)]
  | gOut l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pG κ l) (by simp [pU, pG]; omega) hc),
      oTbls_agree h hn κ U (by simp only [pG] at *; omega),
      clOut_agree h κ l (by simp only [pG] at *; omega),
      rxOf_take_agree h κ l (by simp only [pG] at *; omega)]
  | rx l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pG κ l + 1) (by simp [pU, pG]; omega) hc),
      oTbls_agree h hn κ U (by simp only [pG] at *; omega),
      clOut_agree h κ (l + 1) (by simp only [pG] at *; omega),
      rxOf_take_agree h κ (l + 1) (by simp only [pG] at *; omega)]
  | tri =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pTri κ) (by simp [pU, pTri]; omega) hc), triOf_agree h κ hc,
      rxOf_agree h κ (by omega), matA_agree h hn, zOfU_agree h hn]
  | rho =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pTri κ + 1) (by simp [pU, pTri]; omega) hc),
      iTbls_agree h hn κ U hc, clIn_agree h κ 0 (by simp only [pGi] at *; omega)]
    simp
  | gIn l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pGi κ l) (by simp [pU, pGi, pTri]; omega) hc),
      iTbls_agree h hn κ U (by simp only [pGi] at *; omega),
      clIn_agree h κ l (by simp only [pGi] at *; omega),
      ryOf_take_agree h κ l (by simp only [pGi] at *; omega)]
  | ry l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pGi κ l + 1) (by simp [pU, pGi, pTri]; omega) hc),
      iTbls_agree h hn κ U (by simp only [pGi] at *; omega),
      clIn_agree h κ (l + 1) (by simp only [pGi] at *; omega),
      ryOf_take_agree h κ (l + 1) (by simp only [pGi] at *; omega)]
  | sl =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pS κ) (by simp [pU, pS, pTri]; omega) hc),
      deltaOf_agree h κ U hc]
  | f q =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pF κ q) (by simp [pU, pF, pS, pTri]; omega) hc),
      deltaOf_agree h κ U (by simp only [pF] at hc; omega),
      fsOf_take_agree h κ (q + 1) (by simp only [pF] at *; omega)]
  | gRs l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pGr κ l) (by simp [pU, pGr, pS, pTri]; omega) hc),
      wTbls_agree h κ U (by simp only [pGr] at *; omega),
      clRs_agree h κ l (by simp only [pGr] at *; omega),
      rrOf_take_agree h κ l (by simp only [pGr] at *; omega)]
  | rr l =>
    simp only [AlgRow, posOfC, SumWrong] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pGr κ l + 1) (by simp [pU, pGr, pS, pTri]; omega) hc),
      wTbls_agree h κ U (by simp only [pGr] at *; omega),
      clRs_agree h κ (l + 1) (by simp only [pGr] at *; omega),
      rrOf_take_agree h κ (l + 1) (by simp only [pGr] at *; omega)]
  | vabs =>
    simp only [AlgRow, posOfC] at hc ⊢
    rw [FarDoom_agree h κ U (hU (pV κ) (by simp [pU, pV, pS, pTri]; omega) hc),
      VWrong_agree h κ U hc]
  | r7 j =>
    simp only [AlgRow, posOfC] at hc ⊢
    have h1 := hU (pV κ + j) (by simp [pU, pV, pS, pTri]; omega) hc
    split_ifs with hj
    · rw [FarDoom_agree h κ U h1, VWrong_agree h κ U (by omega)]
    · rw [FarDoom_agree h κ U h1, VWrong_agree h κ U (by omega), Dof_agree h κ U (by omega),
        bOf_agree h κ (by omega)]

end AlgLocality2


/-! ## Part E: the per-position facts for `Doom` -/

section DoomFacts
open PCS Spartan SoundnessPCS

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

theorem doom_iff {L₀ es : Log} {κ : ℕ} (hk : kapOf es = κ) :
    Doom ev L₀ es ↔ Rej ev es ∨ AlgRow κ (filled κ L₀ (rootOf es)) es (posClass κ (es.length - 1)) := by
  subst hk; rfl

theorem pre8_pV (κ : ℕ) : (pre8 κ).length = pV κ + 1 := by
  rw [pre8_length]; simp only [pV, pS, pTri]; ring

/-- The facts of an appended entry: its position is below `len κ`, `κ` and the root are kept. -/
theorem append_facts {es : Log} {x : ByteArray × Digest} (hm : Matches (es ++ [x]))
    (hne : es ≠ []) :
    kapOf (es ++ [x]) = kapOf es ∧ es.length < len (kapOf es) ∧
      (2 ≤ es.length → rootOf (es ++ [x]) = rootOf es) := by
  have hk := kapOf_append hne [x]
  refine ⟨hk, ?_, fun h2 => rootOf_agree (agree_append es [x]) (by omega)⟩
  have := matches_len hm
  rw [hk] at this; simp at this; omega

/-- **`doom_mid`**: inside a multi-answer round, an answer neither dooms nor undooms. -/
theorem doom_mid (L₀ es : Log) (x : ByteArray × Digest) (s0 r : ℕ) (hm : Matches (es ++ [x]))
    (hr : rnd (kapOf es) es.length = some (s0, r)) (hlt : es.length < s0 + r) :
    Doom ev L₀ (es ++ [x]) ↔ Doom ev L₀ es := by
  have hne : es ≠ [] := by
    rintro rfl
    have := pre8_length (kapOf ([] : Log))
    simp only [List.length_nil] at hr
    unfold rnd at hr
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hr
    cases hr
  obtain ⟨hk, hlen, hroot⟩ := append_facts hm hne
  set κ := kapOf es with hκ
  have hl1 : (es ++ [x]).length - 1 = es.length := by simp
  rw [doom_iff ev hk, doom_iff ev hκ.symm, hl1]
  have hpV := pre8_pV κ
  have hlenV := len_pV κ
  have hG := (show pG κ 0 = 3 + rows κ + (15 + κ) by simp [pG])
  unfold rnd at hr
  split_ifs at hr with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [hroot (by omega)]
    have hr1 : ¬ Rej ev (es ++ [x]) := not_rej_early ev (by rw [hk, hl1]; omega)
    have hr2 : ¬ Rej ev es := not_rej_early ev (by rw [← hκ]; omega)
    have e1 : posClass κ es.length = .r0 (es.length - 1) := by
      have := posClass_r0 κ (es.length - 1) (by omega) (by omega)
      rwa [show 1 + (es.length - 1) = es.length by omega] at this
    have hFS := FS_agree (agree_append es [x]) (show 0 < es.length by omega)
    have e2 : AlgRow κ (filled κ L₀ (rootOf es)) es (posClass κ (es.length - 1)) ↔ FS es := by
      rcases Nat.lt_or_ge 2 es.length with h3 | h3
      · have e2 : posClass κ (es.length - 1) = .r0 (es.length - 2) := by
          have := posClass_r0 κ (es.length - 2) (by omega) (by omega)
          rwa [show 1 + (es.length - 2) = es.length - 1 by omega] at this
        rw [e2]
        simp only [AlgRow]
        rw [ite_eq_left (show es.length - 2 < rows κ by omega)]
      · rw [show es.length - 1 = 1 by omega, posClass_root]
        rfl
    rw [e1, e2]
    simp only [AlgRow]
    rw [ite_eq_left (show es.length - 1 < rows κ by omega), hFS]
    simp only [hr1, hr2, false_or]
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hV2 : 2 ≤ pV κ := by simp only [pV, pS, pTri]; omega
    rw [hroot (by omega), rej_append_iff_full ev hne (by rw [← hκ]; omega)]
    have e1 : posClass κ es.length = .r7 (es.length - pV κ) := by
      have := posClass_r7 κ (es.length - pV κ) (by omega) (by omega)
      rwa [show pV κ + (es.length - pV κ) = es.length by omega] at this
    have hold : AlgRow κ (filled κ L₀ (rootOf es)) es (posClass κ (es.length - 1)) ↔
        AlgRow κ (filled κ L₀ (rootOf es)) es .vabs := by
      rcases Nat.lt_or_ge (pV κ + 1) es.length with h3 | h3
      · have e2 : posClass κ (es.length - 1) = .r7 (es.length - 1 - pV κ) := by
          have := posClass_r7 κ (es.length - 1 - pV κ) (by omega) (by omega)
          rwa [show pV κ + (es.length - 1 - pV κ) = es.length - 1 by omega] at this
        rw [e2]
        simp only [AlgRow, show es.length - 1 - pV κ < nJ κ by omega, ite_true]
      · rw [show es.length - 1 = pV κ by omega, posClass_vabs]
    rw [e1, hold]
    simp only [AlgRow, show es.length - pV κ < nJ κ by omega, ite_true]
    have := algRow_agree (agree_append es [x]) κ (filled κ L₀ (rootOf es)) .vabs
      (by simp only [posOfC]; omega)
    simp only [AlgRow] at this
    rw [this]

end DoomFacts


/-! ## Part E: the multi-answer rounds (`r0_esc_le`, `r7_esc_le` instantiated) -/

section Rounds
open PCS Spartan SoundnessPCS RS

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

theorem agree_ext (es₀ : Log) (as : List Digest) : AgreeTo (ext es₀ as) es₀ es₀.length := by
  obtain ⟨t, ht, -⟩ := ext_eq_append es₀ as
  rw [ht]; exact agree_append es₀ t

theorem entAt_ext (es₀ : Log) (as : List Digest) (i : ℕ) (hi : i < as.length) :
    (entAt (ext es₀ as) (es₀.length + i)).2 = as[i] := by
  obtain ⟨t, ht, hs⟩ := ext_eq_append es₀ as
  have hti : i < t.length := by rw [← hs, List.length_map] at hi; exact hi
  rw [ht, entAt, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show es₀.length + i - es₀.length = i by omega, List.getElem?_eq_getElem hti,
    Option.getD_some]
  have := congrArg (fun l => l[i]?) hs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hti, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] at this
  exact this

theorem ext_dropLast (es₀ : Log) {as : List Digest} (h : as ≠ []) :
    (ext es₀ as).dropLast = ext es₀ as.dropLast := by
  conv_lhs => rw [← List.dropLast_append_getLast h, ext_append]
  rw [ext1, List.dropLast_concat]

theorem ne_nil_of_ext {es₀ : Log} (h : es₀ ≠ []) (as : List Digest) : ext es₀ as ≠ [] := by
  obtain ⟨t, ht, -⟩ := ext_eq_append es₀ as
  rw [ht]; simp [h]

theorem kapOf_le {es : Log} (hm : Matches es) : kapOf es ≤ 20 := by
  obtain ⟨s, n, h, h0, h1, h2, -⟩ := (matches_iff' es).mp hm
  rw [kapOf_of h0]
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by unfold chainCap at h2; exact h2)

theorem kapOf_ext {es₀ : Log} (h : es₀ ≠ []) (as : List Digest) : kapOf (ext es₀ as) = kapOf es₀ := by
  obtain ⟨t, ht, -⟩ := ext_eq_append es₀ as
  rw [ht, kapOf_append h]

theorem rootOf_ext {es₀ : Log} (h : 2 ≤ es₀.length) (as : List Digest) :
    rootOf (ext es₀ as) = rootOf es₀ :=
  rootOf_agree (agree_ext es₀ as) (by omega)

theorem extCount_eq_zero {P : List Digest → Prop} {k : ℕ}
    (h : ∀ a : Fin k → Digest, ¬ P (List.ofFn a)) : extCount P [] k = 0 := by
  classical
  unfold extCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  exact h a (by simpa using ha)

/-- **The R0 round**: its escape count from `absorb(root)` is at most `2^-169`. -/
theorem round_r0_le (L₀ es₀ : Log) (hm : Matches es₀) (hlen : es₀.length = 2) :
    condCount (Doom ev) L₀ es₀ (rows (kapOf es₀)) [] ≤ δKS := by
  classical
  have hne := matches_ne_nil hm
  obtain ⟨κ, hκ⟩ : ∃ κ, kapOf es₀ = κ := ⟨_, rfl⟩
  have hκ20 : κ ≤ 20 := hκ ▸ kapOf_le hm
  have hm2 : 2 ≤ rows κ := by
    unfold rows muR; exact le_self_pow₀ (by norm_num) (by omega)
  rw [hκ]
  unfold condCount
  simp only [List.length_nil, Nat.sub_zero]
  refine (r0_esc_le hκ20 (filled κ L₀ (rootOf es₀)) _ fun a ha => ?_).trans ?_
  · obtain ⟨-, hd, hnd⟩ := ha
    have hlas : (List.ofFn a).length = rows κ := List.length_ofFn
    generalize has : List.ofFn a = as at hlas hd hnd
    have hasne : as ≠ [] := by rw [← List.length_pos_iff]; omega
    have hkE : kapOf (ext es₀ as) = κ := (kapOf_ext hne as).trans hκ
    have hrE := rootOf_ext (es₀ := es₀) (by omega) as
    have hLE : (ext es₀ as).length - 1 = 1 + rows κ := by rw [length_ext, hlen, hlas]; omega
    rw [doom_iff ev hkE, hrE, hLE, posClass_r0 κ _ (by omega) le_rfl] at hnd
    simp only [AlgRow] at hnd
    rw [ite_eq_right (lt_irrefl _)] at hnd
    rw [ext_dropLast es₀ hasne] at hd
    have hkE' : kapOf (ext es₀ as.dropLast) = κ := (kapOf_ext hne _).trans hκ
    have hLE' : (ext es₀ as.dropLast).length - 1 = rows κ := by
      rw [length_ext, hlen, List.length_dropLast, hlas]; omega
    have hnr : ¬ Rej ev (ext es₀ as.dropLast) := not_rej_early ev (by
      rw [hkE', hLE']; simp only [pG]; omega)
    rw [doom_iff ev hkE', hLE'] at hd
    have hFS : FS (ext es₀ as.dropLast) := by
      rcases hd with hd | hd
      · exact absurd hd hnr
      rcases Nat.lt_or_ge 1 (rows κ - 1) with h3 | h3
      · rw [show rows κ = 1 + (rows κ - 1) by omega, posClass_r0 κ _ (by omega) (by omega)] at hd
        simp only [AlgRow] at hd
        rwa [ite_eq_left (show rows κ - 1 < rows κ by omega)] at hd
      · rw [show rows κ = 1 + 1 by omega, posClass_r0 κ _ le_rfl (by omega)] at hd
        simp only [AlgRow] at hd
        rwa [ite_eq_left (show 1 < rows κ by omega)] at hd
    have hFS' : FS (ext es₀ as) := by
      rwa [FS_agree (agree_ext es₀ as.dropLast) (by omega),
        ← FS_agree (agree_ext es₀ as) (by omega)] at hFS
    have hfar : Far κ (filled κ L₀ (rootOf es₀)) ∧
        ¬ FarDoom κ (filled κ L₀ (rootOf es₀)) (ext es₀ as) := by
      by_contra hc
      apply hnd
      refine Or.inr ⟨hFS', ?_⟩
      by_cases hF : Far κ (filled κ L₀ (rootOf es₀))
      · exact Or.inl (by by_contra h'; exact hc ⟨hF, h'⟩)
      · exact Or.inr hF
    refine ⟨hfar.1, ?_⟩
    have hc := hfar.2
    simp only [FarDoom, not_and, not_not] at hc
    have hcl := hc hfar.1
    have hr : ∀ i : Fin (rows κ), (rVec κ (ext es₀ as)).getD i 0 = chE (a i) := by
      intro i
      simp only [rVec, chAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt,
        Option.map_some, Option.getD_some, show 2 + (i : ℕ) = es₀.length + i by omega,
        entAt_ext es₀ as i (by rw [hlas]; exact i.isLt)]
      subst has
      simp
    simp only [hr] at hcl
    exact hcl
  · rw [← NNReal.coe_le_coe, δKS]; push_cast; norm_num

theorem rej_ext_iff {es₀ : Log} (hne : es₀ ≠ []) (hV : pV (kapOf es₀) < es₀.length)
    (as : List Digest) : Rej ev (ext es₀ as) ↔ Rej ev es₀ := by
  obtain ⟨t, ht, -⟩ := ext_eq_append es₀ as
  rw [ht]; exact rej_append_iff_full ev hne hV t

/-- **The R7 round**: its escape count from `absorb(v)` is at most `(4/5) · 2^-129`. -/
theorem round_r7_le (L₀ es₀ : Log) (hm : Matches es₀) (hlen : es₀.length = pV (kapOf es₀) + 1)
    (hJ : 1 ≤ nJ (kapOf es₀)) :
    condCount (Doom ev) L₀ es₀ (nJ (kapOf es₀)) [] ≤ δKS := by
  classical
  have hne := matches_ne_nil hm
  obtain ⟨κ, hκ⟩ : ∃ κ, kapOf es₀ = κ := ⟨_, rfl⟩
  have hκ20 : κ ≤ 20 := hκ ▸ kapOf_le hm
  rw [hκ] at hlen hJ ⊢
  have hV2 : 2 ≤ pV κ := by simp only [pV, pS, pTri]; omega
  have hR : 1 + rows κ < es₀.length := by simp only [pV, pS, pTri] at hlen; omega
  unfold condCount
  simp only [List.length_nil, Nat.sub_zero]
  -- facts about an extension by `J` (or `J - 1`) answers
  have hkE : ∀ as, kapOf (ext es₀ as) = κ := fun as => (kapOf_ext hne as).trans hκ
  have hrE : ∀ as, rootOf (ext es₀ as) = rootOf es₀ := fun as => rootOf_ext (by omega) as
  have hrej : ∀ as, Rej ev (ext es₀ as) ↔ Rej ev es₀ := fun as =>
    rej_ext_iff ev hne (by rw [hκ]; omega) as
  have hclose : ∀ as, (FarDoom κ (filled κ L₀ (rootOf es₀)) (ext es₀ as) ∨
      (¬ Far κ (filled κ L₀ (rootOf es₀)) ∧ VWrong κ (filled κ L₀ (rootOf es₀)) (ext es₀ as))) ↔
      (FarDoom κ (filled κ L₀ (rootOf es₀)) es₀ ∨
        (¬ Far κ (filled κ L₀ (rootOf es₀)) ∧ VWrong κ (filled κ L₀ (rootOf es₀)) es₀)) :=
    fun as => by
      rw [FarDoom_agree (agree_ext es₀ as) κ _ hR, VWrong_agree (agree_ext es₀ as) κ _ (by omega)]
  have hlast : ∀ as : List Digest, as.length = nJ κ →
      (Doom ev L₀ (ext es₀ as) ↔ Rej ev es₀ ∨
        ((FarDoom κ (filled κ L₀ (rootOf es₀)) es₀ ∨
          (¬ Far κ (filled κ L₀ (rootOf es₀)) ∧ VWrong κ (filled κ L₀ (rootOf es₀)) es₀)) ∧
          ¬ Miss (lN κ) tQ (nJ κ) (Dof κ (filled κ L₀ (rootOf es₀)) es₀)
            (bOf κ (ext es₀ as)))) := by
    intro as hl
    rw [doom_iff ev (hkE as), hrE, hrej, show (ext es₀ as).length - 1 = pV κ + nJ κ by
      rw [length_ext, hl]; omega, posClass_r7 κ _ hJ le_rfl]
    simp only [AlgRow]
    rw [ite_eq_right (lt_irrefl _), hclose, Dof_agree (agree_ext es₀ as) κ _ (by omega)]
  have hprev : ∀ as : List Digest, as.length + 1 = nJ κ →
      (Doom ev L₀ (ext es₀ as) ↔ Rej ev es₀ ∨
        (FarDoom κ (filled κ L₀ (rootOf es₀)) es₀ ∨
          (¬ Far κ (filled κ L₀ (rootOf es₀)) ∧ VWrong κ (filled κ L₀ (rootOf es₀)) es₀))) := by
    intro as hl
    rw [doom_iff ev (hkE as), hrE, hrej]
    rcases Nat.lt_or_ge 0 as.length with h0 | h0
    · rw [show (ext es₀ as).length - 1 = pV κ + as.length by rw [length_ext]; omega,
        posClass_r7 κ _ h0 (by omega)]
      simp only [AlgRow]
      rw [ite_eq_left (show as.length < nJ κ by omega), hclose]
    · rw [show (ext es₀ as).length - 1 = pV κ by rw [length_ext]; omega, posClass_vabs]
      simp only [AlgRow]
      rw [hclose]
  by_cases hcl : FarDoom κ (filled κ L₀ (rootOf es₀)) es₀ ∨
      (¬ Far κ (filled κ L₀ (rootOf es₀)) ∧ VWrong κ (filled κ L₀ (rootOf es₀)) es₀)
  · have hD : radius κ + 1 ≤ (Dof κ (filled κ L₀ (rootOf es₀)) es₀).card := by
      unfold Dof
      split_ifs with hF
      · exact far_Dset_card _ _ (hcl.resolve_right fun h => h.1 hF).2 _
      · obtain ⟨S, hS⟩ := qDec_spec hκ20 (not_not.mp hF)
        exact (radius_succ_le κ).trans
          (close_Dset_card hκ20 hS _ (hcl.resolve_left fun h => hF h.1).2)
    refine (r7_esc_le hκ20 _ hD _ fun b hb => ?_).trans le_rfl
    obtain ⟨-, -, hnd⟩ := hb
    rw [hlast _ List.length_ofFn] at hnd
    have hb : bOf κ (ext es₀ (List.ofFn b)) = b := by
      funext j
      simp only [bOf]
      rw [show pV κ + 1 + (j : ℕ) = es₀.length + j by omega,
        entAt_ext es₀ _ j (by rw [List.length_ofFn]; exact j.isLt)]
      simp
    rw [hb] at hnd
    by_contra hmiss
    exact hnd (Or.inr ⟨hcl, hmiss⟩)
  · refine le_trans (le_of_eq ?_) zero_le
    rw [extCount_eq_zero fun b hb => ?_]
    · simp
    obtain ⟨-, hd, hnd⟩ := hb
    have hasne : List.ofFn b ≠ [] := by
      rw [← List.length_pos_iff, List.length_ofFn]; omega
    rw [ext_dropLast es₀ hasne, hprev _ (by rw [List.length_dropLast, List.length_ofFn]; omega)]
      at hd
    rw [hlast _ List.length_ofFn] at hnd
    rcases hd with hd | hd
    · exact hnd (Or.inl hd)
    · exact hcl hd

/-- **The round bounds** (`hround` of `muG_step_of`): R0 by `r0_esc_le`, R7 by `r7_esc_le`. -/
theorem round_le (L₀ es₀ : Log) (s0 r : ℕ) (hm : Matches es₀) (hlen : es₀.length = s0 + 1)
    (hr : rnd (kapOf es₀) (s0 + 1) = some (s0, r)) : condCount (Doom ev) L₀ es₀ r [] ≤ δKS := by
  obtain ⟨hs, hsr, -⟩ := rnd_spec hr
  have hpV := pre8_pV (kapOf es₀)
  unfold rnd at hr
  split_ifs at hr with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact round_r0_le ev L₀ es₀ hm hlen
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact round_r7_le ev L₀ es₀ hm (by omega) (by omega)

end Rounds


/-! ## Part E: one more challenge (`ext1`) -/

section Ext1
open PCS Spartan

theorem bindT_snoc {R : Type*} [CommRing R] (t : Array R) (cs : List R) (c : R) :
    SpartanChain.bindT t (cs ++ [c]) = bind0 (SpartanChain.bindT t cs) c := by
  induction cs generalizing t with
  | nil => rfl
  | cons c' cs ih => exact ih _

theorem bindAll_snoc {R : Type*} [CommRing R] (ts : Array (Array R)) (cs : List R) (c : R) :
    bindAll ts (cs ++ [c]) = (bindAll ts cs).map (bind0 · c) := by
  induction cs generalizing ts with
  | nil => rfl
  | cons c' cs ih => exact ih _

theorem bindAll_sizes {R : Type*} [CommRing R] (ts : Array (Array R)) (cs : List R) (m : ℕ)
    (h : ∀ t ∈ ts, t.size = 2 ^ (cs.length + m)) : ∀ t ∈ bindAll ts cs, t.size = 2 ^ m := by
  induction cs generalizing ts with
  | nil => simpa [bindAll] using h
  | cons c cs ih =>
    refine ih _ (map_bind0_size ts c ?_)
    intro t ht; rw [h t ht]; congr 1; simp; omega

theorem entAt_ext1 (es : Log) (a : Digest) : entAt (ext1 es a) es.length =
    (squeezeQ (lastAns es), a) := by
  simp [entAt, ext1, List.getD_eq_getElem?_getD]

theorem chAt_ext1 (es : Log) (a : Digest) : chAt (ext1 es a) es.length = chE a := by
  simp [chAt, entAt_ext1]

theorem agree_ext1 (es : Log) (a : Digest) : AgreeTo (ext1 es a) es es.length :=
  agree_append es _

theorem take_snoc_ch (es : Log) (a : Digest) (N k : ℕ) (P : ℕ → ℕ) (hk : k < N)
    (hP : P k = es.length) (hlt : ∀ l < k, P l < es.length) :
    ((List.range N).map fun l => chAt (ext1 es a) (P l)).take (k + 1) =
      ((List.range N).map fun l => chAt es (P l)).take k ++ [chE a] := by
  rw [List.take_add_one, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.toList_some, hP, chAt_ext1]
  exact congrArg (· ++ [chE a])
    (map_range_take_congr k fun l hl _ => chAt_agree (agree_ext1 es a) (hlt l hl))

theorem getD_snoc_ch (es : Log) (a : Digest) (N k : ℕ) (P : ℕ → ℕ) (hk : k < N)
    (hP : P k = es.length) :
    ((List.range N).map fun l => chAt (ext1 es a) (P l)).getD k 0 = chE a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, hP, chAt_ext1]

end Ext1

end KS

end SpartanChain
