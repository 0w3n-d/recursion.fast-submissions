import SpartanChainTranscript
import SpartanChainPCSBounds
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Objects read off the log, and the log lemmas of the knowledge state (BLUEPRINT-R1 §9.1, §9.3)

The parts of §9.1 and §9.3 that do not depend on the verifier's `leafProg`:

* **L-K1 `bad_step_le`**: on a log without bad events, at most `|L|·(3·2^8 + 1) + 1` of the
  `2^256` answers to a fresh query make the log bad. The terms are: `|L|·2^8` collisions (a label
  has `2^8` preimages, `card_trunc_fiber`); `2|L|·2^8` label hits (a query carries at most two
  labels, `length_labelsIn`); `|L|` state hits on earlier entries; one state hit on the new
  query's own state (`StateHit` with `i ≤ j`); no repeat, since the query is fresh.
  `bad_step_frac` gives the bound at `|L| < logCap = 2^96`.
* **The transcript forest** (§9.1): `predIdx L j` is the index of the entry whose answer is the
  state of entry `j`, and `back L j` is the path of indices that ends at `j` and follows
  `predIdx` down to an entry with no predecessor. A chain of §9.1 is such a path that starts at a
  seed and whose queries match §6.2. The match needs the shape of `n` and is left to the
  verifier's modules.
* **L-K8 `fresh_leaf`**: if `L ++ [(q, a)]` is not bad, the new entry is a leaf of the forest.
  Every old entry keeps its predecessor and its path (`back_append_old`), and the path of the new
  entry is the path of its predecessor in `L` extended by it, or the new entry alone
  (`back_new`).
* **The frontier** (review S9-M2): an entry is on the frontier when the squeeze of its answer has
  not been asked. A fresh query removes at most the entries whose squeeze it is
  (`frontier_append`).
* **L-K2, generic** (`extCount_split`, the review's `roundPot_split`): for any event `P` on the
  answers of a round, the number of completions of `pre` is the sum over the next answer `a` of
  the number of completions of `pre ++ [a]`. This is the martingale step of every multi-answer
  round.
* **Chains** (§9.1, second revision): `Step`, `Step.matches` (tag, length and kind), `shape κ`
  (§6.2 step by step), `len`, `entriesOf`, `Matches` (a seed of `1 ≤ n ≤ chainCap`, then the
  steps of its shape, state-linked; decidable through `matchesB`), `IsChain`, `chains`, `cut`,
  `L₀`; `L₀_append`, `split_at_cut` (the split of L-M3/L-M4 at the chain's `absorb(root)`
  entry), **L-K8 `chains_append`** (old chains are kept, at most the new entry is added) with
  `isChain_new` (a new chain is a seed or extends its predecessor's chain) and its converses
  `isChain_new_of_seed`, `isChain_new_of_extend`.
-/

namespace SpartanChain
open RecursionFast Merkle Transcript

namespace SoundnessLog

/-! ## Label fibers -/

/-- A digest as its last byte and its first 31 bytes. -/
def split31 : Digest ≃ (Fin 1 → Fin 256) × (Fin 31 → Fin 256) :=
  (vecEquiv 32).trans <| (Equiv.arrowCongr (finSumFinEquiv (m := 31) (n := 1)).symm
    (Equiv.refl _)).trans <| (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodComm _ _)

theorem split31_snd (a : Digest) (i : Fin 31) : (split31 a).2 i = a[i.1].toFin := by
  simp [split31, vecEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]
  rfl

theorem trunc_getElem (a : Digest) (i : ℕ) (hi : i < 31) : (trunc a)[i] = a[i] := by
  simp [trunc]

/-- **Every label has `2^8` preimages** among the answers. -/
theorem card_trunc_fiber (lb : Label) :
    (Finset.univ.filter fun a : Digest => trunc a = lb).card = 2 ^ 8 := by
  have : (Finset.univ.filter fun a : Digest => trunc a = lb) =
      Finset.univ.filter fun a => (split31 a).2 = fun i => lb[i.1].toFin := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; funext i; simp [split31_snd, trunc_getElem]
    · intro h; ext i hi
      have := congrFun h ⟨i, hi⟩
      simp only [split31_snd, UInt8.toFin_inj] at this
      rw [trunc_getElem a i hi, this]
  rw [this, card_fiber_snd]
  simp

/-- A node query carries no absorbed root. -/
theorem parseAbsorbRoot_nodeQ (l r : Label) : parseAbsorbRoot (nodeQ l r) = none := by
  simp [parseAbsorbRoot, nodeQ_data]

/-- **A query carries at most two labels.** -/
theorem length_labelsIn (q : ByteArray) : (labelsIn q).length ≤ 2 := by
  unfold labelsIn
  cases hn : parseNode q with
  | none => cases parseAbsorbRoot q <;> simp
  | some ab =>
    rw [parseNode_eq_some (q := q) (l := ab.1) (r := ab.2) (by rw [hn]), parseAbsorbRoot_nodeQ]
    simp

/-! ## L-K1: the bad answers of a fresh query -/

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **L-K1 `bad_step_le`**: on a log without bad events, at most `|L|·(3·2^8 + 1) + 1` answers
to a fresh query make the log bad. -/
theorem bad_step_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤
      L.length * (3 * 2 ^ 8 + 1) + 1 := by
  set fib : Label → Finset Digest := fun lb => Finset.univ.filter fun a => trunc a = lb
  have hfib : ∀ lb, (fib lb).card = 2 ^ 8 := card_trunc_fiber
  set A := L.toFinset.biUnion fun e => fib (trunc e.2)
  set B := L.toFinset.biUnion fun e => (labelsIn e.1).toFinset.biUnion fib
  set C := L.toFinset.biUnion fun e => (stateIn e.1).toFinset
  set D := (stateIn q).toFinset
  have hA : A.card ≤ L.length * 2 ^ 8 :=
    (Finset.card_biUnion_le_card_mul _ _ _ fun e _ => (hfib _).le).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
  have hB : B.card ≤ L.length * (2 * 2 ^ 8) := by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun e _ => ?_).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun lb _ => (hfib lb).le).trans ?_
    exact Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans (length_labelsIn _))
  have hC : C.card ≤ L.length * 1 := by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun e _ => ?_).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
    rw [Option.card_toFinset]; cases stateIn e.1 <;> simp
  have hD : D.card ≤ 1 := by
    rw [Option.card_toFinset]; cases stateIn q <;> simp
  have hsub : (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])) ⊆ A ∪ B ∪ C ∪ D := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_union]
    have hlen : (L ++ [(q, a)]).length = L.length + 1 := by simp
    rcases ha with ⟨e₁, h₁, e₂, h₂, hne, ht⟩ | ⟨i, j, hij, hj, hm⟩ | ⟨i, j, hij, hj, hs⟩ | hr
    · simp only [List.mem_append, List.mem_singleton] at h₁ h₂
      rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | rfl
      · exact absurd (Or.inl ⟨e₁, h₁, e₂, h₂, hne, ht⟩) hb
      · left; left; left
        exact Finset.mem_biUnion.mpr ⟨e₁, List.mem_toFinset.mpr h₁, by simp [fib, ht]⟩
      · left; left; left
        exact Finset.mem_biUnion.mpr ⟨e₂, List.mem_toFinset.mpr h₂, by simp [fib, ht]⟩
      · exact absurd rfl hne
    · rw [hlen] at hj
      by_cases hjL : j < L.length
      · refine absurd (Or.inr (Or.inl ⟨i, j, hij, hjL, ?_⟩)) hb
        rwa [List.getElem_append_left hjL, List.getElem_append_left (hij.trans hjL)] at hm
      · have hj' : j = L.length := by omega
        subst hj'
        rw [List.getElem_concat_length rfl, List.getElem_append_left hij] at hm
        left; left; right
        refine Finset.mem_biUnion.mpr ⟨L[i], List.mem_toFinset.mpr (List.getElem_mem hij), ?_⟩
        exact Finset.mem_biUnion.mpr ⟨trunc a, List.mem_toFinset.mpr hm, by simp [fib]⟩
    · rw [hlen] at hj
      by_cases hjL : j < L.length
      · refine absurd (Or.inr (Or.inr (Or.inl ⟨i, j, hij, hjL, ?_⟩))) hb
        rwa [List.getElem_append_left hjL,
          List.getElem_append_left (Nat.lt_of_le_of_lt hij hjL)] at hs
      · have hj' : j = L.length := by omega
        subst hj'
        rw [List.getElem_concat_length rfl] at hs
        by_cases hiL : i < L.length
        · rw [List.getElem_append_left hiL] at hs
          left; right
          refine Finset.mem_biUnion.mpr ⟨L[i], List.mem_toFinset.mpr (List.getElem_mem hiL), ?_⟩
          simp [hs]
        · have hi' : i = L.length := by omega
          subst hi'
          rw [List.getElem_concat_length rfl] at hs
          right
          simp [D, hs]
    · exfalso
      apply hr
      have hn : (L.map Prod.fst).Nodup := by
        by_contra h; exact hb (Or.inr (Or.inr (Or.inr h)))
      rw [List.map_append, List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy; subst hxy
      exact hq hx
  calc (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card
      ≤ (A ∪ B ∪ C ∪ D).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card + C.card + D.card := by
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
      exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ L.length * (3 * 2 ^ 8 + 1) + 1 := by nlinarith

open Classical in
/-- L-K1 at the contract's length guard: below `logCap = 2^96` entries, fewer than
`2^96·(3·2^8 + 1) + 1` answers are bad. -/
theorem bad_step_frac {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤
      2 ^ 96 * (3 * 2 ^ 8 + 1) + 1 :=
  (bad_step_le hb hq).trans (by unfold logCap at hl; nlinarith)

/-! ## The transcript forest and L-K8 -/

/-- The index of the first entry of `L` whose answer is `st`. -/
def ansIdx (L : Log) (st : Digest) : Option ℕ := L.findIdx? fun e => decide (e.2 = st)

/-- `pred_L`: the index of the entry whose answer is the state of entry `j`. -/
def predIdx (L : Log) (j : ℕ) : Option ℕ := L[j]?.bind fun e => (stateIn e.1).bind (ansIdx L)

/-- The path of indices that ends at `j` and follows `predIdx` down through earlier entries, with
fuel `f`. -/
def back (L : Log) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, j =>
    match predIdx L j with
    | some i => if i < j then back L f i ++ [j] else [j]
    | none => [j]

/-- The forest path ending at entry `j` (its chain, when it starts at a seed and matches §6.2). -/
def pathOf (L : Log) (j : ℕ) : List ℕ := back L (j + 1) j

theorem back_fuel_aux (L : Log) :
    ∀ n f g j, j < n → j < f → j < g → back L f j = back L g j := by
  intro n
  induction n with
  | zero => intro f g j h; omega
  | succ n ih =>
    intro f g j hn hf hg
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [back]
    cases predIdx L j with
    | none => rfl
    | some i =>
      simp only
      split_ifs with h
      · rw [ih f g i (by omega) (by omega) (by omega)]
      · rfl

theorem back_fuel (L : Log) (f j : ℕ) (h : j < f) : back L f j = back L (j + 1) j :=
  back_fuel_aux L (j + 1) f (j + 1) j (by omega) h (by omega)

theorem ansIdx_lt {L : Log} {st : Digest} {i : ℕ} (h : ansIdx L st = some i) :
    ∃ hi : i < L.length, L[i].2 = st := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa using hp⟩

/-- Under `¬ Bad`, the answer index of an entry's state is earlier than the entry. -/
theorem predIdx_lt {L : Log} (hb : ¬ Bad L) {j i : ℕ} (h : predIdx L j = some i) : i < j := by
  simp only [predIdx, Option.bind_eq_some_iff] at h
  obtain ⟨e, he, st, hst, hi⟩ := h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hiL, hia⟩ := ansIdx_lt hi
  exact (pred_unique_lt hb hj hst).2 i hiL hia

/-- An old entry keeps its predecessor when a non-bad entry is appended. -/
theorem predIdx_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) {j : ℕ}
    (hj : j < L.length) : predIdx (L ++ [x]) j = predIdx L j := by
  simp only [predIdx, List.getElem?_append_left hj]
  cases hLj : L[j]? with
  | none => rfl
  | some e =>
    simp only [Option.bind_some]
    cases hst : stateIn e.1 with
    | none => rfl
    | some st =>
      simp only [Option.bind_some, ansIdx, List.findIdx?_append]
      cases hf : L.findIdx? (fun e => decide (e.2 = st)) with
      | some i => rfl
      | none =>
        simp only [Option.none_or]
        cases hx : [x].findIdx? (fun e => decide (e.2 = st)) with
        | none => rfl
        | some k =>
          exfalso
          obtain ⟨hk, hkp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
          have hk0 : k = 0 := by simpa using hk
          subst hk0
          have hxst : x.2 = st := by simpa using hkp
          obtain ⟨hjL, rfl⟩ := List.getElem?_eq_some_iff.mp hLj
          apply hb
          refine Or.inr (Or.inr (Or.inl ⟨j, L.length, by omega, by simp, ?_⟩))
          rw [List.getElem_append_left hjL, List.getElem_concat_length rfl, hst, hxst]

/-- **L-K8, old entries** (`back_append_old`): appending a non-bad entry changes no path that
ends at an old entry. -/
theorem back_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) :
    ∀ f j, j < L.length → back (L ++ [x]) f j = back L f j := by
  intro f
  induction f with
  | zero => intro j _; rfl
  | succ f ih =>
    intro j hj
    simp only [back, predIdx_append_old hb hj]
    cases predIdx L j with
    | none => rfl
    | some i =>
      simp only
      split_ifs with h
      · rw [ih i (by omega)]
      · rfl

/-- The new entry's predecessor is read off `L`, under no bad event. -/
theorem predIdx_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) :
    predIdx (L ++ [(q, a)]) L.length = (stateIn q).bind (ansIdx L) := by
  simp only [predIdx, List.getElem?_concat_length, Option.bind_some]
  cases hst : stateIn q with
  | none => rfl
  | some st =>
    simp only [Option.bind_some, ansIdx, List.findIdx?_append]
    cases hf : L.findIdx? (fun e => decide (e.2 = st)) with
    | some i => rfl
    | none =>
      simp only [Option.none_or]
      cases hx : [(q, a)].findIdx? (fun e => decide (e.2 = st)) with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨hk, hkp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        have hast : a = st := by simpa using hkp
        apply hb
        refine Or.inr (Or.inr (Or.inl ⟨L.length, L.length, le_rfl, by simp, ?_⟩))
        rw [List.getElem_concat_length rfl, hst, hast]

/-- **L-K8 `fresh_leaf`, the new entry** (`back_new`): under no bad event, the path of the new
entry is its predecessor's path in `L` followed by it, or the new entry alone. -/
theorem back_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) :
    pathOf (L ++ [(q, a)]) L.length =
      match (stateIn q).bind (ansIdx L) with
      | some i => pathOf L i ++ [L.length]
      | none => [L.length] := by
  simp only [pathOf]
  rw [back.eq_2, predIdx_new hb]
  cases hp : (stateIn q).bind (ansIdx L) with
  | none => rfl
  | some i =>
    simp only
    have hi : i < L.length := by
      have := predIdx_new hb
      rw [hp] at this
      exact predIdx_lt hb this
    simp only [hi, ↓reduceIte]
    rw [back_append_old hb _ _ hi, back_fuel L L.length i hi]

/-- **L-K8, old paths** (`pathOf_append_old`). -/
theorem pathOf_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) {j : ℕ}
    (hj : j < L.length) : pathOf (L ++ [x]) j = pathOf L j :=
  back_append_old hb _ _ hj

/-! ## The frontier (review S9-M2) -/

/-- An entry is on the frontier of `L` when the squeeze of its answer is not asked in `L`. -/
def OnFrontier (L : Log) (e : ByteArray × Digest) : Prop :=
  e ∈ L ∧ squeezeQ e.2 ∉ L.map Prod.fst

instance (L : Log) (e : ByteArray × Digest) : Decidable (OnFrontier L e) :=
  decidable_of_iff ((L.any fun x => decide (x = e)) && !(L.any fun x => decide (x.1 = squeezeQ e.2)))
    (by
      unfold OnFrontier
      rw [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.any_eq_false]
      simp only [decide_eq_true_eq, List.mem_map]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, h⟩; exact ⟨hx, fun ⟨y, hy, hyq⟩ => h y hy hyq⟩
      · rintro ⟨hx, h⟩; exact ⟨⟨e, hx, rfl⟩, fun y hy hyq => h ⟨y, hy, hyq⟩⟩)

/-- A fresh entry removes from the frontier only the entries whose squeeze it is. -/
theorem frontier_append {L : Log} {q : ByteArray} {a : Digest} {e : ByteArray × Digest}
    (he : e ∈ L) : OnFrontier (L ++ [(q, a)]) e ↔ OnFrontier L e ∧ q ≠ squeezeQ e.2 := by
  simp only [OnFrontier, List.mem_append, List.mem_singleton, he, true_or, true_and,
    List.map_append, List.map_cons, List.map_nil, not_or]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩

/-! ## L-K2: the martingale split of a round's count -/

open Classical in
/-- The number of completions of the answers `pre` by `k` more answers that satisfy `P`. -/
noncomputable def extCount (P : List Digest → Prop) (pre : List Digest) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun rest : Fin k → Digest => P (pre ++ List.ofFn rest)).card

open Classical in
/-- **L-K2 `extCount_split`** (generic, `roundPot_split`): the completions of `pre` by `k + 1`
answers are the sum over the next answer `a` of the completions of `pre ++ [a]` by `k`. Divided
by `2^(256 (k + 1))`, the conditional escape probability is a martingale: `Σ_a p(pre ++ [a]) =
2^256 · p(pre)`. -/
theorem extCount_split (P : List Digest → Prop) (pre : List Digest) (k : ℕ) :
    ∑ a : Digest, extCount P (pre ++ [a]) k = extCount P pre (k + 1) := by
  simp only [extCount]
  rw [Finset.card_equiv (Fin.consEquiv fun _ : Fin (k + 1) => Digest).symm
    (t := Finset.univ.filter fun x : Digest × (Fin k → Digest) =>
      P (pre ++ [x.1] ++ List.ofFn x.2))]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  · intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

/-! ## Chains (§9.1)

The expected transcript of a leaf of shape `κ` is the list of steps `shape κ` (§6.2). A chain of
`L` is an entry index `j` whose forest path, read as entries, starts at a seed and follows the
steps of the seed's shape (`Matches`); it is determined by `j`, so sums over chains are sums over
entries. Its **cut** is the second index of its path (the `absorb(root)` entry) and `L₀ L j` the
log strictly before it.
-/

/-- One step of the transcript (§6.2). -/
inductive Step where
  /-- The seed `0x10 ‖ s ‖ enc64 n ‖ h`. -/
  | seed
  /-- An absorb `0x20 ‖ st ‖ kind ‖ msg` with a `len`-byte message. -/
  | absorb (kind : UInt8) (len : ℕ)
  /-- A squeeze `0x30 ‖ st`. -/
  | squeeze
  deriving DecidableEq, Inhabited

open PCS in
/-- **The transcript of a leaf of shape `κ`**, §6.2 step by step (`m = rows κ`, `k = msgLen κ`,
`ℓ_x = ℓ_y = 15 + κ`, `J = nAns (lN κ) tQ`). -/
def shape (κ : ℕ) : List Step :=
  [.seed, .absorb 0x01 31] ++ List.replicate (rows κ) Step.squeeze ++
    [Step.absorb 0x02 (24 * msgLen κ)] ++ List.replicate (15 + κ) Step.squeeze ++
    (List.replicate (15 + κ) [Step.absorb 0x03 96, .squeeze]).flatten ++
    [Step.absorb 0x04 72, .squeeze] ++
    (List.replicate (15 + κ) [Step.absorb 0x05 72, .squeeze]).flatten ++ [Step.absorb 0x06 1536] ++
    List.replicate 6 Step.squeeze ++ (List.replicate (8 + κ) [Step.absorb 0x07 72, .squeeze]).flatten ++
    [Step.absorb 0x08 (24 * msgLen κ)] ++ List.replicate (nAns (lN κ) tQ) Step.squeeze

/-- The number of steps of the transcript of shape `κ`. -/
def len (κ : ℕ) : ℕ := (shape κ).length

/-- The tag, length and kind check of a step on a query, as a boolean. -/
def Step.check : Step → ByteArray → Bool
  | .seed, q => tagOf q == some 0x10 && q.size == 73
  | .absorb kind l, q => tagOf q == some 0x20 && q.size == 34 + l && q.data[33]? == some kind
  | .squeeze, q => tagOf q == some 0x30 && q.size == 33

/-- A query has the tag, length (seed `73`, absorb `34 + len`, squeeze `33`) and kind of a step. -/
def Step.matches (st : Step) (q : ByteArray) : Prop := st.check q = true

instance (st : Step) (q : ByteArray) : Decidable (st.matches q) :=
  inferInstanceAs (Decidable (_ = true))

/-- The entries of `L` at the indices `is`. -/
def entriesOf (L : Log) (is : List ℕ) : Log := is.map fun i => L[i]!

/-- **A seed, then the steps of its shape, state-linked**: the entries `es` start at a seed of
`(s, n, h)` with `1 ≤ n ≤ chainCap`, are at most `len κ` long (`κ = ⌈log₂ n⌉`), each entry after
the first has the previous answer as its state, and entry `i + 1` matches step `i + 1`. -/
def Matches (es : Log) : Prop :=
  ∃ s n h, (es[0]?.bind fun e => seedOf e.1) = some (s, n, h) ∧ 1 ≤ n ∧ n ≤ chainCap ∧
    ∃ hl : es.length ≤ len (Nat.clog 2 n),
      ∀ i (hi : i + 1 < es.length), stateIn es[i + 1].1 = some es[i].2 ∧
        ((shape (Nat.clog 2 n))[i + 1]'(by unfold len at hl; omega)).matches es[i + 1].1

/-- The shape part of `Matches`, as a boolean, for a given `κ`. -/
def shapeOK (κ : ℕ) (es : Log) : Bool :=
  decide (es.length ≤ len κ) && (List.range (es.length - 1)).all fun i =>
    decide (stateIn es[i + 1]!.1 = some es[i]!.2) && (shape κ)[i + 1]!.check es[i + 1]!.1

/-- `Matches` as a boolean. -/
def matchesB (es : Log) : Bool :=
  match es[0]?.bind fun e => seedOf e.1 with
  | some (_, n, _) => decide (1 ≤ n) && decide (n ≤ chainCap) && shapeOK (Nat.clog 2 n) es
  | none => false

theorem shapeOK_iff (κ : ℕ) (es : Log) : shapeOK κ es = true ↔
    ∃ hl : es.length ≤ len κ, ∀ i (hi : i + 1 < es.length),
      stateIn es[i + 1].1 = some es[i].2 ∧
        ((shape κ)[i + 1]'(by unfold len at hl; omega)).matches es[i + 1].1 := by
  simp only [shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨hl, fun i hi => ?_⟩
    have := h i (by omega)
    rw [getElem!_pos es (i + 1) hi, getElem!_pos es i (by omega),
      getElem!_pos (shape κ) (i + 1) (by unfold len at hl; omega)] at this
    exact this
  · rintro ⟨hl, h⟩
    refine ⟨hl, fun i hi => ?_⟩
    rw [getElem!_pos es (i + 1) (by omega), getElem!_pos es i (by omega),
      getElem!_pos (shape κ) (i + 1) (by unfold len at hl; omega)]
    exact h i (by omega)

theorem matches_iff (es : Log) : Matches es ↔ matchesB es = true := by
  unfold Matches matchesB
  cases h0 : es[0]?.bind fun e => seedOf e.1 with
  | none => simp
  | some x =>
    obtain ⟨s, n, h⟩ := x
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq,
      shapeOK_iff]
    constructor
    · rintro ⟨s', n', h', ⟨rfl, rfl, rfl⟩, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨s, n, h, ⟨rfl, rfl, rfl⟩, h1, h2, h3⟩

instance : DecidablePred Matches := fun es => decidable_of_iff _ (matches_iff es).symm

/-- **A chain of `L`**: an entry index whose forest path, read as entries, `Matches`. -/
def IsChain (L : Log) (j : ℕ) : Prop := j < L.length ∧ Matches (entriesOf L (pathOf L j))

instance (L : Log) : DecidablePred (IsChain L) := fun _ => instDecidableAnd

/-- The indices of `L` that are chains. -/
def chains (L : Log) : List ℕ := (List.range L.length).filter fun j => decide (IsChain L j)

/-- The cut of chain `j`: the second index of its path (its `absorb(root)` entry). -/
def cut (L : Log) (j : ℕ) : ℕ := (pathOf L j)[1]!

/-- The prefix of chain `j`: the log strictly before its cut. -/
def L₀ (L : Log) (j : ℕ) : Log := L.take (cut L j)

/-! ### Path facts -/

theorem mem_back_le (L : Log) : ∀ f j, ∀ x ∈ back L f j, x ≤ j := by
  intro f
  induction f with
  | zero => intro j x hx; simp [back] at hx
  | succ f ih =>
    intro j x hx
    simp only [back] at hx
    cases hp : predIdx L j with
    | none => rw [hp] at hx; simp at hx; omega
    | some i =>
      rw [hp] at hx
      simp only at hx
      split_ifs at hx with h
      · rcases List.mem_append.mp hx with hx | hx
        · exact (ih i x hx).trans h.le
        · simp at hx; omega
      · simp at hx; omega

theorem mem_pathOf_le {L : Log} {j x : ℕ} (hx : x ∈ pathOf L j) : x ≤ j :=
  mem_back_le L _ _ _ hx

theorem back_ne_nil (L : Log) (f j : ℕ) : back L (f + 1) j ≠ [] := by
  simp only [back]
  cases predIdx L j with
  | none => simp
  | some i => simp only; split_ifs <;> simp

theorem pathOf_ne_nil (L : Log) (j : ℕ) : pathOf L j ≠ [] := back_ne_nil L j j

theorem cut_le (L : Log) (j : ℕ) : cut L j ≤ j := by
  unfold cut
  by_cases h : 1 < (pathOf L j).length
  · rw [getElem!_pos (pathOf L j) 1 h]; exact mem_pathOf_le (List.getElem_mem h)
  · rw [getElem!_neg (pathOf L j) 1 h]; exact Nat.zero_le _

theorem entriesOf_append {L : Log} {x : ByteArray × Digest} {is : List ℕ}
    (h : ∀ i ∈ is, i < L.length) : entriesOf (L ++ [x]) is = entriesOf L is := by
  unfold entriesOf
  apply List.map_congr_left
  intro i hi
  have hi' := h i hi
  rw [getElem!_pos (L ++ [x]) i (by simp; omega), getElem!_pos L i hi',
    List.getElem_append_left hi']

/-- **`L₀_append`**: an old chain keeps its prefix when a non-bad entry is appended. -/
theorem L₀_append {L : Log} {x : ByteArray × Digest} {j : ℕ} (hj : j < L.length)
    (hb : ¬ Bad (L ++ [x])) : L₀ (L ++ [x]) j = L₀ L j := by
  unfold L₀ cut
  rw [pathOf_append_old hb hj, List.take_append_of_le_length]
  have := cut_le L j
  unfold cut at this
  omega

/-- An absorb step of kind `0x01` with a 31-byte message is an `absorb(root)` query. -/
theorem parseAbsorbRoot_of_matches {q : ByteArray} (h : (Step.absorb 0x01 31).matches q) :
    ∃ root, parseAbsorbRoot q = some root := by
  simp only [Step.matches, Step.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨htag, hsz⟩, hk⟩ := h
  unfold parseAbsorbRoot
  unfold tagOf at htag
  cases hq : q.data.toList with
  | nil => rw [hq] at htag; cases htag
  | cons b rest =>
    rw [hq] at htag
    simp only [List.head?_cons, Option.some.injEq] at htag
    have hlen : rest.length = 64 := by
      have : q.data.toList.length = 65 := by rw [Array.length_toList]; exact hsz
      rw [hq] at this; simpa using this
    have h33 : rest[32]? = some 0x01 := by
      have : q.data.toList[33]? = some 0x01 := by rw [Array.getElem?_toList]; exact hk
      rw [hq] at this; simpa using this
    simp only [htag, hlen, h33, and_self, ↓reduceDIte]
    exact ⟨_, rfl⟩

theorem entriesOf_getElem (L : Log) (is : List ℕ) (k : ℕ) (hk : k < (entriesOf L is).length) :
    (entriesOf L is)[k] = L[is[k]'(by simpa [entriesOf] using hk)]! := by
  simp [entriesOf]

/-- **`split_at_cut`**: a chain of at least two entries splits the log at its cut, which is an
`absorb(root)` entry — the split of L-M3 (`open_binding_prefix`) and L-M4 (`tree_prefix`). -/
theorem split_at_cut {L : Log} {j : ℕ} (hc : IsChain L j) (h2 : 2 ≤ (pathOf L j).length) :
    ∃ hcut : cut L j < L.length,
      L = L₀ L j ++ L[cut L j] :: L.drop (cut L j + 1) ∧
        ∃ root, parseAbsorbRoot L[cut L j].1 = some root := by
  have hcut : cut L j < L.length := (cut_le L j).trans_lt hc.1
  refine ⟨hcut, ?_, ?_⟩
  · unfold L₀
    rw [← List.drop_eq_getElem_cons hcut, List.take_append_drop]
  · obtain ⟨s, n, h, -, -, -, hl, hm⟩ := hc.2
    have hlen : 0 + 1 < (entriesOf L (pathOf L j)).length := by simp [entriesOf]; omega
    have hstep := (hm 0 hlen).2
    have hsh : (shape (Nat.clog 2 n))[0 + 1]'(by unfold len at hl; omega) = .absorb 0x01 31 := by
      simp [shape]
    rw [hsh] at hstep
    obtain ⟨root, hr⟩ := parseAbsorbRoot_of_matches hstep
    refine ⟨root, ?_⟩
    rw [entriesOf_getElem] at hr
    have hc1 : (pathOf L j)[0 + 1]'(by omega) = cut L j := by
      unfold cut; rw [getElem!_pos (pathOf L j) 1 (by omega)]
    rw [hc1, getElem!_pos L (cut L j) hcut] at hr
    exact hr

/-! ### L-K8: chains of an extended log -/

/-- `Matches` of a longer list gives `Matches` of its nonempty prefix. -/
theorem matches_of_append {es : Log} {x : ByteArray × Digest} (hne : es ≠ [])
    (h : Matches (es ++ [x])) : Matches es := by
  obtain ⟨s, n, hh, h0, h1, h2, hl, hm⟩ := h
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  refine ⟨s, n, hh, ?_, h1, h2, by simp at hl; omega, fun i hi => ?_⟩
  · rwa [List.getElem?_append_left hpos] at h0
  · have := hm i (by simp; omega)
    simp only [List.getElem_append_left hi, List.getElem_append_left (show i < es.length by omega)]
      at this
    exact this

/-- **L-K8 `chains_append`**: appending a non-bad entry keeps every old chain (with its path,
prefix, messages and challenges) and adds at most the new entry. -/
theorem chains_append {L : Log} {e : ByteArray × Digest} (hb : ¬ Bad (L ++ [e])) :
    chains (L ++ [e]) = chains L ++ (if IsChain (L ++ [e]) L.length then [L.length] else []) := by
  unfold chains
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    apply decide_eq_decide.mpr
    unfold IsChain
    rw [List.length_append, List.length_singleton, pathOf_append_old hb hj,
      entriesOf_append fun i hi => (mem_pathOf_le hi).trans_lt hj]
    constructor
    · rintro ⟨-, h⟩; exact ⟨hj, h⟩
    · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · by_cases h : IsChain (L ++ [e]) L.length <;> simp [h]

/-- The entries of an old chain are unchanged by appending a non-bad entry. -/
theorem entriesOf_pathOf_append {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x]))
    {j : ℕ} (hj : j < L.length) :
    entriesOf (L ++ [x]) (pathOf (L ++ [x]) j) = entriesOf L (pathOf L j) := by
  rw [pathOf_append_old hb hj, entriesOf_append fun i hi => (mem_pathOf_le hi).trans_lt hj]

/-- **The new chain** (L-K8): if the appended entry ends a chain, it is a seed with no
predecessor, or it extends a chain `i` of `L` (its predecessor), whose entries it follows. -/
theorem isChain_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)]))
    (hc : IsChain (L ++ [(q, a)]) L.length) :
    ((stateIn q).bind (ansIdx L) = none ∧ ∃ s n h, seedOf q = some (s, n, h) ∧ 1 ≤ n ∧
        n ≤ chainCap) ∨
      ∃ i, (stateIn q).bind (ansIdx L) = some i ∧ IsChain L i ∧
        entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
          entriesOf L (pathOf L i) ++ [(q, a)] := by
  have hpath := back_new hb
  cases hp : (stateIn q).bind (ansIdx L) with
  | none =>
    rw [hp] at hpath
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨s, n, h, h0, h1, h2, -⟩ := hc.2
    rw [hpath] at h0
    refine ⟨s, n, h, ?_, h1, h2⟩
    simpa [entriesOf] using h0
  | some i =>
    rw [hp] at hpath
    have hi : i < L.length := by
      have := predIdx_new hb
      rw [hp] at this
      exact predIdx_lt hb this
    have hes : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
        entriesOf L (pathOf L i) ++ [(q, a)] := by
      rw [hpath]
      unfold entriesOf
      rw [List.map_append]
      congr 1
      · exact entriesOf_append fun x hx => (mem_pathOf_le hx).trans_lt hi
      · simp
    right
    refine ⟨i, rfl, ⟨hi, ?_⟩, hes⟩
    have := hc.2
    rw [hes] at this
    exact matches_of_append (by simpa [entriesOf] using pathOf_ne_nil L i) this

theorem back_getLast? (L : Log) (f j : ℕ) : (back L (f + 1) j).getLast? = some j := by
  simp only [back]
  cases predIdx L j with
  | none => simp
  | some i => simp only; split_ifs <;> simp

theorem pathOf_getLast? (L : Log) (j : ℕ) : (pathOf L j).getLast? = some j := back_getLast? L j j

/-- `Matches` extends by an entry linked to the last answer and matching the next step. -/
theorem matches_append {es : Log} {x : ByteArray × Digest} (h : Matches es)
    (hx : ∀ s n h, (es[0]?.bind fun e => seedOf e.1) = some (s, n, h) →
      ∃ hl : es.length < len (Nat.clog 2 n), (∃ y, es.getLast? = some y ∧ stateIn x.1 = some y.2) ∧
        ((shape (Nat.clog 2 n))[es.length]'(by unfold len at hl; omega)).matches x.1) :
    Matches (es ++ [x]) := by
  obtain ⟨s, n, hh, h0, h1, h2, hl, hm⟩ := h
  obtain ⟨hl', ⟨y, hy, hst⟩, hmatch⟩ := hx s n hh h0
  have hpos : 0 < es.length := by
    rcases es with _ | _
    · simp at h0
    · simp
  refine ⟨s, n, hh, ?_, h1, h2, by simp; omega, fun i hi => ?_⟩
  · rwa [List.getElem?_append_left hpos]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i + 1 < es.length
    · have := hm i hlt
      rwa [List.getElem_append_left hlt, List.getElem_append_left (show i < es.length by omega)]
    · have hie : i + 1 = es.length := by omega
      have hy' : es[i]'(by omega) = y := by
        rw [List.getLast?_eq_getElem?] at hy
        have : es.length - 1 = i := by omega
        rw [this, List.getElem?_eq_getElem (by omega)] at hy
        exact Option.some.inj hy
      rw [List.getElem_append_left (show i < es.length by omega), hy',
        List.getElem_concat_length hie]
      refine ⟨hst, ?_⟩
      have : (shape (Nat.clog 2 n))[i + 1]'(by unfold len at hl'; omega) =
          (shape (Nat.clog 2 n))[es.length]'(by unfold len at hl'; omega) := by
        congr 1
      rw [this]; exact hmatch

/-- A seed query has no state field. -/
theorem stateIn_of_seedOf {q : ByteArray} {x : Digest × ℕ × Digest} (h : seedOf q = some x) :
    stateIn q = none := by
  unfold seedOf at h
  unfold stateIn
  cases hq : q.data.toList with
  | nil => rfl
  | cons b rest =>
    rw [hq] at h
    simp only at h
    split_ifs at h with hb
    simp [hb.1]

/-- **The new chain, converse** (seed case): a fresh seed of a valid length is a chain. -/
theorem isChain_new_of_seed {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)]))
    {s : Digest} {n : ℕ} {h : Digest} (hs : seedOf q = some (s, n, h)) (h1 : 1 ≤ n)
    (h2 : n ≤ chainCap) : IsChain (L ++ [(q, a)]) L.length := by
  refine ⟨by simp, ?_⟩
  have hpath := back_new hb
  rw [stateIn_of_seedOf hs] at hpath
  simp only [Option.bind_none] at hpath
  rw [hpath]
  refine ⟨s, n, h, by simp [entriesOf, hs], h1, h2, ?_, fun i hi => ?_⟩
  · simp [entriesOf, len, shape]
  · simp [entriesOf] at hi

/-- **The new chain, converse** (extension case): an entry whose predecessor ends a chain `i`
and which matches the next step of that chain's shape is a chain. -/
theorem isChain_new_of_extend {L : Log} {q : ByteArray} {a : Digest}
    (hb : ¬ Bad (L ++ [(q, a)])) {i : ℕ} (hp : (stateIn q).bind (ansIdx L) = some i)
    (hc : IsChain L i)
    (hnext : ∀ s n h, ((entriesOf L (pathOf L i))[0]?.bind fun e => seedOf e.1) =
        some (s, n, h) → ∃ hl : (entriesOf L (pathOf L i)).length < len (Nat.clog 2 n),
        ((shape (Nat.clog 2 n))[(entriesOf L (pathOf L i)).length]'(by
          unfold len at hl; omega)).matches q) :
    IsChain (L ++ [(q, a)]) L.length := by
  have hi : i < L.length := hc.1
  refine ⟨by simp, ?_⟩
  have hpath := back_new hb
  rw [hp] at hpath
  simp only at hpath
  have hes : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
      entriesOf L (pathOf L i) ++ [(q, a)] := by
    rw [hpath]
    unfold entriesOf
    rw [List.map_append]
    congr 1
    · exact entriesOf_append fun x hx => (mem_pathOf_le hx).trans_lt hi
    · simp
  rw [hes]
  refine matches_append hc.2 fun s n h h0 => ?_
  obtain ⟨hl, hm⟩ := hnext s n h h0
  refine ⟨hl, ⟨L[i], ?_, ?_⟩, hm⟩
  · unfold entriesOf
    rw [List.getLast?_map, pathOf_getLast?]
    simp [List.getElem?_eq_getElem hi]
  · simp only [Option.bind_eq_some_iff] at hp
    obtain ⟨st, hst, hidx⟩ := hp
    obtain ⟨hi2, hans⟩ := ansIdx_lt hidx
    rw [hst, hans]

end SoundnessLog

end SpartanChain
