import SpartanChainSoundnessFinal
import SpartanChainVerifier

/-!
# L-K4 `runLog_chain`: an accepted SNARK run is a complete chain of the log (BLUEPRINT-R1 §9.1)

For a log `L` without bad events, an accepting run of the leaf SNARK verifier `snarkProg ev s n h π`
on `L` gives `RunChain ev L s n h` (`SpartanChainSoundnessFinal`): a chain `j` of `L` whose
path is complete, whose statement is `(s, n, h)`, none of whose checks (a)–(f) fails, and whose
column phase accepts on `L` with the chain's root, `r`, `a`, `ū`, `v` and index answers
(`runLog_chain`). Two hypotheses besides `¬ Bad`, `1 ≤ n` and acceptance are needed, both
checked by `leafProg` before the SNARK runs: `n ≤ chainCap` (a chain's seed has it, `Matches`)
and `off₃ κ ≤ |π_S|` (fields 1, 2 and 8 have their §7 lengths, so the absorbs match the shape;
`snarkProg` itself reads past the end as zeros). `hchain_of_leafProg` derives them from an
accepting `leafProg`, and `mu_final_leaf_closed` is `SoundnessFinal.mu_final_leaf` with its
`hchain` discharged.

The proof:

1. **Linked entries are a chain path** (`chain_of_linked`): under `¬ Bad`, a list of entries of
   `L` that starts at a query with no state and in which each query's state is the previous
   answer is exactly `entriesOf L (pathOf L j)` for the index `j` of its last entry (answers are
   unique, so `ansIdx` finds the previous entry, which is earlier: `predIdx_lt`).
2. **The verifier's transcript as blocks** under an oracle `H`: `sqBlock` (squeezes), `rdBlock`
   (absorb–squeeze rounds), and the whole Fiat–Shamir entry list `fsEntries` of `snarkProg`, with
   the runs and queries of `squeezeN`, `absorbRounds`, `verify1`, `Spartan.verify` and `verify2`
   in terms of the blocks (`LinkedFrom`, `endSt`).
3. Under `H = logOracle L` (`runLog_eq_some_iff`) the blocks are entries of `L`, linked, of the
   §6.2 kinds and lengths, and the chain's data (`rootOf`, `rVec`, `ubarOf`, `tauOf`, …) are the
   verifier's values; `Spartan.check` and check (f) passing are `¬ Rej`.
-/

namespace SpartanChain.SoundnessChain

open RecursionFast Transcript SoundnessLog KS PCS Merkle

/-! ## 1. Linked entries are a chain path -/

theorem entriesOf_snoc' (L : Log) (p : List ℕ) (j : ℕ) :
    entriesOf L (p ++ [j]) = entriesOf L p ++ [L[j]!] := by
  simp [entriesOf]

theorem pathOf_of_pred_none {L : Log} {j : ℕ} (h : predIdx L j = none) : pathOf L j = [j] := by
  unfold pathOf; rw [back.eq_2, h]

theorem pathOf_of_pred_some {L : Log} {i j : ℕ} (h : predIdx L j = some i) (hij : i < j) :
    pathOf L j = pathOf L i ++ [j] := by
  unfold pathOf; rw [back.eq_2, h]
  simp only [hij, ↓reduceIte]
  rw [back_fuel L j i hij]

/-- Under `¬ Bad`, entries with equal answers are equal (by index). -/
theorem idx_eq_of_ans {L : Log} (hb : ¬ Bad L) {i k : ℕ} (hi : i < L.length) (hk : k < L.length)
    (h : L[i].2 = L[k].2) : i = k := by
  have hq : L[i].1 = L[k].1 := by
    by_contra hne
    exact hb (Or.inl ⟨L[i], List.getElem_mem hi, L[k], List.getElem_mem hk, hne, by rw [h]⟩)
  have hn : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  exact (List.Nodup.getElem_inj_iff hn (i := i) (j := k) (hi := by simpa using hi)
    (hj := by simpa using hk)).mp (by simpa using hq)

theorem ansIdx_eq {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) :
    ansIdx L L[i].2 = some i := by
  cases hf : ansIdx L L[i].2 with
  | none =>
    exfalso
    unfold ansIdx at hf
    rw [List.findIdx?_eq_none_iff] at hf
    exact absurd (hf L[i] (List.getElem_mem hi)) (by simp)
  | some k =>
    obtain ⟨hk, hka⟩ := ansIdx_lt hf
    rw [idx_eq_of_ans hb hk hi hka]

/-- **Linked entries of `L` are the entries of a chain path.** -/
theorem chain_of_linked {L : Log} (hb : ¬ Bad L) :
    ∀ (E : Log) (hne : E ≠ []), (∀ e ∈ E, e ∈ L) → stateIn (E[0]'(by
        rcases E with _ | _ <;> simp_all)).1 = none →
      (∀ i (hi : i + 1 < E.length), stateIn E[i + 1].1 = some E[i].2) →
      ∃ j, ∃ hj : j < L.length, L[j] = E.getLast hne ∧ entriesOf L (pathOf L j) = E := by
  intro E
  induction E using List.reverseRecOn with
  | nil => intro hne; exact absurd rfl hne
  | append_singleton E x ih =>
    intro _ hmem hseed hlink
    obtain ⟨j₁, hj₁, hx⟩ := List.getElem_of_mem (hmem x (by simp))
    by_cases hE : E = []
    · subst hE
      refine ⟨j₁, hj₁, by simpa using hx, ?_⟩
      have hp : predIdx L j₁ = none := by
        simp only [predIdx, List.getElem?_eq_getElem hj₁, Option.bind_some, hx]
        simp only [List.nil_append, List.getElem_singleton] at hseed
        rw [hseed]; rfl
      rw [pathOf_of_pred_none hp]
      simp [entriesOf, List.getElem?_eq_getElem hj₁, hx]
    · have hpos : 0 < E.length := List.length_pos_iff.mpr hE
      obtain ⟨j₀, hj₀, hlast, hpath⟩ := ih hE (fun e he => hmem e (by simp [he]))
        (by rwa [List.getElem_append_left hpos] at hseed)
        (fun i hi => by
          have := hlink i (by simp; omega)
          rwa [List.getElem_append_left hi, List.getElem_append_left (by omega)] at this)
      have hst : stateIn x.1 = some L[j₀].2 := by
        have := hlink (E.length - 1) (by simp; omega)
        rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at this
        simp only [show E.length - 1 + 1 - E.length = 0 by omega, List.getElem_singleton] at this
        rw [this, hlast, List.getLast_eq_getElem]
      have hp : predIdx L j₁ = some j₀ := by
        simp only [predIdx, List.getElem?_eq_getElem hj₁, Option.bind_some, hx, hst]
        exact ansIdx_eq hb hj₀
      have hlt := predIdx_lt hb hp
      refine ⟨j₁, hj₁, by simpa using hx, ?_⟩
      rw [pathOf_of_pred_some hp hlt, entriesOf_snoc', hpath, getElem!_pos L j₁ hj₁, hx]

/-! ## 2. Blocks of the transcript under an oracle -/

/-- A list of entries linked from the state `st`: each query's state is the previous answer. -/
def LinkedFrom : Digest → Log → Prop
  | _, [] => True
  | st, e :: es => stateIn e.1 = some st ∧ LinkedFrom e.2 es

/-- The state after a linked list of entries started at `st`: its last answer. -/
def endSt (st : Digest) (es : Log) : Digest := (es.getLast?.map Prod.snd).getD st

theorem endSt_cons (st : Digest) (e : ByteArray × Digest) (es : Log) :
    endSt st (e :: es) = endSt e.2 es := by
  cases es with
  | nil => rfl
  | cons f fs =>
    show ((e :: f :: fs).getLast?.map Prod.snd).getD st = ((f :: fs).getLast?.map Prod.snd).getD e.2
    rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (by simp)]
    rfl

theorem endSt_append (st : Digest) (A B : Log) : endSt st (A ++ B) = endSt (endSt st A) B := by
  induction A generalizing st with
  | nil => rfl
  | cons e A ih => rw [List.cons_append, endSt_cons, endSt_cons, ih]

theorem linkedFrom_append (st : Digest) (A B : Log) :
    LinkedFrom st (A ++ B) ↔ LinkedFrom st A ∧ LinkedFrom (endSt st A) B := by
  induction A generalizing st with
  | nil => simp [LinkedFrom, endSt]
  | cons e A ih => simp only [List.cons_append, LinkedFrom, ih, endSt_cons, and_assoc]

theorem linkedFrom_getElem {st : Digest} {es : Log} (h : LinkedFrom st es) :
    ∀ i (hi : i + 1 < es.length), stateIn es[i + 1].1 = some es[i].2 := by
  induction es generalizing st with
  | nil => intro i hi; simp at hi
  | cons e es ih =>
    intro i hi
    cases i with
    | zero =>
      cases es with
      | nil => simp at hi
      | cons f fs => exact h.2.1
    | succ i => exact ih h.2 i (by simpa using hi)

section Blocks
variable (H : ByteArray → Digest)

/-- The entry of a query under `H`. -/
def ent (q : ByteArray) : ByteArray × Digest := (q, H q)

/-- `k` squeezes from `st`. -/
def sqBlock : Digest → ℕ → Log
  | _, 0 => []
  | st, k + 1 => ent H (squeezeQ st) :: sqBlock (H (squeezeQ st)) k

/-- The rounds of `absorbRounds kind`: absorb `g`, squeeze, for each `g`. -/
def rdBlock (kind : UInt8) : Digest → List (Array EF) → Log
  | _, [] => []
  | st, g :: gs =>
    ent H (absorbQ st kind (Ligero.efBytes g)) ::
      ent H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g)))) ::
        rdBlock kind (H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g))))) gs

/-- The squeeze answers of the rounds. -/
def rdAns (kind : UInt8) : Digest → List (Array EF) → List Digest
  | _, [] => []
  | st, g :: gs =>
    H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g)))) ::
      rdAns kind (H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g))))) gs

theorem length_sqBlock (st : Digest) (k : ℕ) : (sqBlock H st k).length = k := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => simp [sqBlock, ih]

theorem length_rdBlock (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    (rdBlock H kind st gs).length = 2 * gs.length := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih => simp [rdBlock, ih]; ring

theorem length_rdAns (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    (rdAns H kind st gs).length = gs.length := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih => simp [rdAns, ih]

theorem run_squeezeN' (st : Digest) (k : ℕ) :
    (squeezeN st k).run H = (endSt st (sqBlock H st k), (sqBlock H st k).map Prod.snd) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [squeezeN, squeeze, OProg.run_bind, OProg.run_ask, ih, OProg.run_pure, sqBlock,
      endSt_cons, List.map_cons]
    rfl

theorem queries_squeezeN' (st : Digest) (k : ℕ) :
    (squeezeN st k).queries H = (sqBlock H st k).map Prod.fst := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [squeezeN, squeeze, OProg.queries_bind, OProg.queries_ask, OProg.run_ask, ih,
      OProg.queries_pure, List.append_nil, sqBlock, List.map_cons,
      List.singleton_append]
    rfl

theorem run_absorbRounds (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    (Spartan.absorbRounds kind st gs).run H =
      (endSt st (rdBlock H kind st gs), (rdAns H kind st gs).map chE) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [Spartan.absorbRounds, absorb, squeeze, OProg.run_bind, OProg.run_ask, ih,
      OProg.run_pure, rdBlock, rdAns, endSt_cons, List.map_cons]
    rfl

theorem queries_absorbRounds (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    (Spartan.absorbRounds kind st gs).queries H = (rdBlock H kind st gs).map Prod.fst := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [Spartan.absorbRounds, absorb, squeeze, OProg.queries_bind, OProg.queries_ask,
      OProg.run_ask, ih, OProg.queries_pure, List.append_nil, rdBlock,
      List.map_cons, List.singleton_append]
    rfl

theorem linked_sqBlock (st : Digest) (k : ℕ) : LinkedFrom st (sqBlock H st k) := by
  induction k generalizing st with
  | zero => trivial
  | succ k ih => exact ⟨stateIn_squeezeQ st, ih _⟩

theorem linked_rdBlock (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    LinkedFrom st (rdBlock H kind st gs) := by
  induction gs generalizing st with
  | nil => trivial
  | cons g gs ih => exact ⟨stateIn_absorbQ _ _ _, stateIn_squeezeQ _, ih _⟩

end Blocks

/-! ## 3. Step checks of the queries -/

theorem size_of_toList {q : ByteArray} {n : ℕ} (h : q.data.toList.length = n) : q.size = n := by
  rw [Array.length_toList] at h; exact h

theorem length_toList_data (m : ByteArray) : m.data.toList.length = m.size := by
  rw [Array.length_toList]; rfl

theorem size_absorbQ (st : Digest) (kind : UInt8) (m : ByteArray) :
    (absorbQ st kind m).size = 34 + m.size := by
  apply size_of_toList
  simp only [absorbQ_data, List.length_cons, List.length_append, Vector.length_toList,
    length_toList_data]
  omega

theorem check_seedQ (s : Digest) (n : ℕ) (h : Digest) : Step.seed.matches (seedQ s n h) := by
  have hs : (seedQ s n h).size = 73 := size_of_toList (by
    simp only [seedQ_data, List.length_cons, List.length_append, Vector.length_toList, enc64,
      List.length_ofFn])
  simp [Step.matches, Step.check, hs]

theorem check_squeezeQ (st : Digest) : Step.squeeze.matches (squeezeQ st) := by
  have hs : (squeezeQ st).size = 33 := size_of_toList (by
    simp only [squeezeQ_data, List.length_cons, Vector.length_toList])
  simp [Step.matches, Step.check, hs]

theorem check_absorbQ (st : Digest) (kind : UInt8) (m : ByteArray) {l : ℕ} (hl : m.size = l) :
    (Step.absorb kind l).matches (absorbQ st kind m) := by
  have hs : (absorbQ st kind m).size = 34 + l := by rw [size_absorbQ, hl]
  have hk : (absorbQ st kind m).data[33]? = some kind := by
    rw [← Array.getElem?_toList, absorbQ_data, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp)]
    simp
  simp [Step.matches, Step.check, hs, hk]

/-- The message of an absorb query is the absorbed bytes. -/
theorem msgOf_absorbQ (st : Digest) (kind : UInt8) (m : ByteArray) :
    msgOf (absorbQ st kind m) = m := by
  apply ByteArray.ext_toList
  unfold msgOf
  rw [size_absorbQ, ByteArray.data_extract, Array.toList_extract, absorbQ_data]
  simp only [List.extract]
  rw [List.drop_succ_cons, show 33 = (Vector.toList st).length + 1 by simp, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left, List.drop_one, List.tail_cons, ← length_toList_data,
    List.take_length]

theorem steps_sqBlock (H : ByteArray → Digest) (st : Digest) (k : ℕ) :
    List.Forall₂ (fun s e => Step.matches s e.1) (List.replicate k .squeeze) (sqBlock H st k) := by
  induction k generalizing st with
  | zero => exact List.Forall₂.nil
  | succ k ih => exact List.Forall₂.cons (check_squeezeQ st) (ih _)

theorem steps_rdBlock (H : ByteArray → Digest) (kind : UInt8) (c : ℕ) (st : Digest)
    (gs : List (Array EF)) (hg : ∀ g ∈ gs, g.size = c) :
    List.Forall₂ (fun s e => Step.matches s e.1)
      (List.replicate gs.length [Step.absorb kind (24 * c), .squeeze]).flatten
      (rdBlock H kind st gs) := by
  induction gs generalizing st with
  | nil => exact List.Forall₂.nil
  | cons g gs ih =>
    simp only [List.length_cons, List.replicate_succ, List.flatten_cons, List.cons_append,
      List.nil_append, rdBlock]
    refine List.Forall₂.cons (check_absorbQ _ _ _ ?_) (List.Forall₂.cons (check_squeezeQ _) ?_)
    · rw [Spartan.efBytes_size, hg g (by simp)]
    · exact ih _ fun g' hg' => hg g' (by simp [hg'])

/-! ## 5. Reading entries at positions -/

theorem entAt_mid (P X Q : Log) {i : ℕ} (hi : i < X.length) :
    entAt (P ++ X ++ Q) (P.length + i) = entAt X i := by
  unfold entAt
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi, List.getD_eq_getElem?_getD]

theorem entAt_mid' {E P X Q : Log} {p i : ℕ} (hE : E = P ++ X ++ Q) (hp : p = P.length + i)
    (hi : i < X.length) : entAt E p = entAt X i := by
  subst hE hp; exact entAt_mid P X Q hi

theorem entAt_eq_getElem (X : Log) {i : ℕ} (hi : i < X.length) : entAt X i = X[i] := by
  unfold entAt; rw [List.getD_eq_getElem _ _ hi]

theorem sqBlock_getElem_snd (H : ByteArray → Digest) (st : Digest) (k i : ℕ)
    (hi : i < (sqBlock H st k).length) :
    (sqBlock H st k)[i].2 = ((sqBlock H st k).map Prod.snd)[i]'(by simpa using hi) := by
  simp

theorem rdBlock_msg (H : ByteArray → Digest) (kind : UInt8) :
    ∀ (st : Digest) (gs : List (Array EF)) (l : ℕ) (hl : l < gs.length),
      msgOf (entAt (rdBlock H kind st gs) (2 * l)).1 = Ligero.efBytes gs[l] := by
  intro st gs
  induction gs generalizing st with
  | nil => intro l hl; simp at hl
  | cons g gs ih =>
    intro l hl
    cases l with
    | zero => simp [rdBlock, entAt, ent, msgOf_absorbQ]
    | succ l =>
      have := ih (H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g))))) l (by simpa using hl)
      simpa [rdBlock, entAt, Nat.mul_succ] using this

theorem rdBlock_ans (H : ByteArray → Digest) (kind : UInt8) :
    ∀ (st : Digest) (gs : List (Array EF)) (l : ℕ) (hl : l < gs.length),
      (entAt (rdBlock H kind st gs) (2 * l + 1)).2 =
        (rdAns H kind st gs)[l]'(by rw [length_rdAns]; exact hl) := by
  intro st gs
  induction gs generalizing st with
  | nil => intro l hl; simp at hl
  | cons g gs ih =>
    intro l hl
    cases l with
    | zero => simp [rdBlock, rdAns, entAt, ent]
    | succ l =>
      have := ih (H (squeezeQ (H (absorbQ st kind (Ligero.efBytes g))))) l (by simpa using hl)
      simpa [rdBlock, rdAns, entAt, Nat.mul_succ] using this

/-! ## 4. The verifier's Fiat–Shamir entries -/

section Verifier
open Leaf
variable (H : ByteArray → Digest)

/-- `verify1`'s entries from `st`: `absorb(root)`, `m` squeezes, `absorb(ū)`. -/
def v1Block (κ : ℕ) (st : Digest) (rootB ubarB : ByteArray) : Log :=
  [ent H (absorbQ st 0x01 rootB)] ++ sqBlock H (H (absorbQ st 0x01 rootB)) (rows κ) ++
    [ent H (absorbQ (endSt (H (absorbQ st 0x01 rootB)) (sqBlock H (H (absorbQ st 0x01 rootB))
      (rows κ))) 0x02 ubarB)]

theorem run_verify1 (κ : ℕ) (st : Digest) (rootB ubarB : ByteArray) :
    (Ligero.verify1 κ st rootB ubarB).run H =
      (endSt st (v1Block H κ st rootB ubarB),
        ((sqBlock H (H (absorbQ st 0x01 rootB)) (rows κ)).map Prod.snd).map chE) := by
  simp only [Ligero.verify1, Ligero.rootAndCoeffs, squeezeE, absorb, OProg.run_bind,
    OProg.run_ask, run_squeezeN', OProg.run_pure, v1Block, endSt_append]
  rfl

theorem queries_verify1 (κ : ℕ) (st : Digest) (rootB ubarB : ByteArray) :
    (Ligero.verify1 κ st rootB ubarB).queries H = (v1Block H κ st rootB ubarB).map Prod.fst := by
  simp only [Ligero.verify1, Ligero.rootAndCoeffs, squeezeE, absorb, OProg.queries_bind,
    OProg.queries_ask, OProg.run_ask, OProg.run_bind, queries_squeezeN', run_squeezeN',
    OProg.queries_pure, OProg.run_pure, List.append_nil, v1Block,
    List.map_append, List.map_cons, List.map_nil]
  rfl

/-! The states inside `Spartan.verify`, from the state `st` after `absorb(ū)`. -/

/-- After the `ℓ_x` squeezes of `τ`. -/
def spS1 (κ : ℕ) (st : Digest) : Digest := endSt st (sqBlock H st (Spartan.ly κ))
/-- After the outer rounds. -/
def spS2 (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest :=
  endSt (spS1 H κ st) (rdBlock H 0x03 (spS1 H κ st) m.outer)
/-- The answer to `absorb(v_A ‖ v_B ‖ v_C)`. -/
def spA4 (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest :=
  H (absorbQ (spS2 H κ m st) 0x04 (Ligero.efBytes #[m.vA, m.vB, m.vC]))
/-- The answer of the `ρ` squeeze. -/
def spRho (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest := H (squeezeQ (spA4 H κ m st))
/-- After the inner rounds. -/
def spS5 (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest :=
  endSt (spRho H κ m st) (rdBlock H 0x05 (spRho H κ m st) m.inner)
/-- The answer to `absorb(s_0 ‖ … ‖ s_63)`. -/
def spA6 (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest :=
  H (absorbQ (spS5 H κ m st) 0x06 (Ligero.efBytes m.slices))
/-- After the six squeezes of `f`. -/
def spS6 (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Digest :=
  endSt (spA6 H κ m st) (sqBlock H (spA6 H κ m st) 6)

/-- `Spartan.verify`'s entries from `st` (§6.2 steps 5–10). -/
def spBlock (κ : ℕ) (m : Spartan.Msgs) (st : Digest) : Log :=
  sqBlock H st (Spartan.ly κ) ++ rdBlock H 0x03 (spS1 H κ st) m.outer ++
    [ent H (absorbQ (spS2 H κ m st) 0x04 (Ligero.efBytes #[m.vA, m.vB, m.vC])),
      ent H (squeezeQ (spA4 H κ m st))] ++
    rdBlock H 0x05 (spRho H κ m st) m.inner ++
    [ent H (absorbQ (spS5 H κ m st) 0x06 (Ligero.efBytes m.slices))] ++
    sqBlock H (spA6 H κ m st) 6 ++ rdBlock H 0x07 (spS6 H κ m st) m.ring

theorem queries_spartan (κ : ℕ) (ev : Spartan.Evals) (m : Spartan.Msgs) (st : Digest) :
    (Spartan.verify κ ev m st).queries H = (spBlock H κ m st).map Prod.fst := by
  simp only [Spartan.verify, squeezeE, absorb, squeeze, OProg.queries_bind, OProg.queries_ask,
    OProg.run_ask, OProg.run_bind, queries_squeezeN', run_squeezeN', queries_absorbRounds,
    run_absorbRounds, OProg.queries_pure, OProg.queries_map, OProg.run_pure, OProg.run_map,
    List.append_nil, spBlock, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append, spS1, spS2, spA4, spRho, spS5, spA6, spS6]
  rfl

/-- **What `Spartan.verify` returns** under `H`: `check` on the challenges read off its blocks,
paired with the state after its last entry. -/
theorem run_spartan (κ : ℕ) (ev : Spartan.Evals) (m : Spartan.Msgs) (st : Digest) :
    (Spartan.verify κ ev m st).run H =
      (Spartan.check κ ev m ((sqBlock H st (Spartan.ly κ)).map Prod.snd |>.map chE)
        ((rdAns H 0x03 (spS1 H κ st) m.outer).map chE) (chE (spRho H κ m st))
        ((rdAns H 0x05 (spRho H κ m st) m.inner).map chE)
        (((sqBlock H (spA6 H κ m st) 6).map Prod.snd).map chE)
        ((rdAns H 0x07 (spS6 H κ m st) m.ring).map chE)).map
        fun c => (endSt st (spBlock H κ m st), c) := by
  simp only [Spartan.verify, squeezeE, absorb, squeeze, OProg.run_bind, OProg.run_ask,
    run_squeezeN', run_absorbRounds, OProg.run_pure, spBlock, endSt_append, endSt_cons,
    spS1, spS2, spA4, spRho, spS5, spA6, spS6]
  rfl

/-- `verify2`'s Fiat–Shamir entries: `absorb(v)` and the `J` index squeezes. -/
def v2Block (κ : ℕ) (st : Digest) (vB : ByteArray) : Log :=
  [ent H (absorbQ st 0x08 vB)] ++ sqBlock H (H (absorbQ st 0x08 vB)) (nJ κ)

theorem queries_verify2 (κ : ℕ) (st : Digest) (root : Label) (r a ubar : Array EF)
    (vB opens : ByteArray) : ∃ rest,
    (Ligero.verify2 κ st root r a ubar vB opens).queries H = (v2Block H κ st vB).map Prod.fst ++ rest := by
  simp only [Ligero.verify2, absorb, squeezeIdx, OProg.queries_bind, OProg.queries_ask,
    OProg.run_ask, OProg.run_bind, queries_squeezeN', OProg.queries_pure, List.append_nil,
    v2Block, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append]
  exact ⟨_, rfl⟩

/-- **The Fiat–Shamir entries of the SNARK verifier** under `H`: the seed, `verify1`'s,
`Spartan.verify`'s and `verify2`'s. -/
def fsEntries (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) (m : Spartan.Msgs)
    (vB : ByteArray) : Log :=
  [ent H (seedQ s n h)] ++
    v1Block H κ (H (seedQ s n h)) (π.extract 0 31) (π.extract 31 (Leaf.off₁ κ)) ++
    spBlock H κ m (endSt (H (seedQ s n h))
      (v1Block H κ (H (seedQ s n h)) (π.extract 0 31) (π.extract 31 (Leaf.off₁ κ)))) ++
    v2Block H κ (endSt (endSt (H (seedQ s n h))
      (v1Block H κ (H (seedQ s n h)) (π.extract 0 31) (π.extract 31 (Leaf.off₁ κ))))
      (spBlock H κ m (endSt (H (seedQ s n h))
        (v1Block H κ (H (seedQ s n h)) (π.extract 0 31) (π.extract 31 (Leaf.off₁ κ)))))) vB

/-- The state after `absorb(ū)`. -/
def stU (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) : Digest :=
  endSt (H (seedQ s n h)) (v1Block H κ (H (seedQ s n h)) (π.extract 0 31)
    (π.extract 31 (Leaf.off₁ κ)))

/-- `r` of `verify1`. -/
def rList (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) : List EF :=
  ((sqBlock H (H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))) (rows κ)).map Prod.snd).map chE

open Leaf in
/-- **An accepting SNARK run under `H`**: `check` passes with a claim `pc`, check (f) passes,
`verify2` accepts with the verifier's arguments, and the Fiat–Shamir entries and `verify2`'s
queries are queries of the run. -/
theorem snark_accept (ev : EvalsFor) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray)
    (hacc : (snarkProg ev s n h π).run H = true) :
    ∃ pc, Spartan.check (Leaf.kap n) (ev (Leaf.kap n) n s h) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
        ((sqBlock H (stU H (Leaf.kap n) s n h π) (Spartan.ly (Leaf.kap n))).map Prod.snd |>.map chE)
        ((rdAns H 0x03 (spS1 H (Leaf.kap n) (stU H (Leaf.kap n) s n h π))
          (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))).outer).map chE)
        (chE (spRho H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))) (stU H (Leaf.kap n) s n h π)))
        ((rdAns H 0x05 (spRho H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
          (stU H (Leaf.kap n) s n h π)) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))).inner).map chE)
        (((sqBlock H (spA6 H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
          (stU H (Leaf.kap n) s n h π)) 6).map Prod.snd).map chE)
        ((rdAns H 0x07 (spS6 H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
          (stU H (Leaf.kap n) s n h π)) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))).ring).map chE)
        = some pc ∧
      finalCheck (Leaf.kap n) pc (Ligero.readEFs (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n))) 0
        (msgLen (Leaf.kap n))) = true ∧
      (Ligero.verify2 (Leaf.kap n) (endSt (stU H (Leaf.kap n) s n h π) (spBlock H (Leaf.kap n)
          (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))) (stU H (Leaf.kap n) s n h π)))
        (Ligero.readLabel π 0) (rList H (Leaf.kap n) s n h π).toArray
        (eqTable (pc.point.drop (lk (Leaf.kap n))))
        (Ligero.readEFs (π.extract 31 (off₁ (Leaf.kap n))) 0 (msgLen (Leaf.kap n)))
        (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n))) (π.extract (off₃ (Leaf.kap n)) π.size)).run H = true ∧
      (∀ q ∈ (fsEntries H (Leaf.kap n) s n h π (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
          (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n)))).map Prod.fst,
        q ∈ (snarkProg ev s n h π).queries H) ∧
      (∀ q ∈ (Ligero.verify2 (Leaf.kap n) (endSt (stU H (Leaf.kap n) s n h π) (spBlock H (Leaf.kap n)
          (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))) (stU H (Leaf.kap n) s n h π)))
        (Ligero.readLabel π 0) (rList H (Leaf.kap n) s n h π).toArray
        (eqTable (pc.point.drop (lk (Leaf.kap n))))
        (Ligero.readEFs (π.extract 31 (off₁ (Leaf.kap n))) 0 (msgLen (Leaf.kap n)))
        (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n))) (π.extract (off₃ (Leaf.kap n)) π.size)).queries H,
        q ∈ (snarkProg ev s n h π).queries H) := by
  have hacc' := hacc
  simp only [snarkProg, seed, OProg.run_bind, OProg.run_ask, run_verify1, run_spartan] at hacc'
  split at hacc'
  · simp at hacc'
  · rename_i st' pc heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨pc', hc, hpc⟩ := heq
    simp only [Prod.mk.injEq] at hpc
    obtain ⟨hst', rfl⟩ := hpc
    subst hst'
    simp only [tail] at hacc'
    split_ifs at hacc' with hf
    · have hQ : (snarkProg ev s n h π).queries H = [seedQ s n h] ++
          (v1Block H (Leaf.kap n) (H (seedQ s n h)) (π.extract 0 31)
            (π.extract 31 (off₁ (Leaf.kap n)))).map Prod.fst ++
          (spBlock H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
            (stU H (Leaf.kap n) s n h π)).map Prod.fst ++
          (Ligero.verify2 (Leaf.kap n) (endSt (stU H (Leaf.kap n) s n h π) (spBlock H (Leaf.kap n)
            (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n))) (stU H (Leaf.kap n) s n h π)))
            (Ligero.readLabel π 0) (rList H (Leaf.kap n) s n h π).toArray
            (eqTable (pc'.point.drop (lk (Leaf.kap n))))
            (Ligero.readEFs (π.extract 31 (off₁ (Leaf.kap n))) 0 (msgLen (Leaf.kap n)))
            (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n)))
            (π.extract (off₃ (Leaf.kap n)) π.size)).queries H := by
        simp only [snarkProg, seed, OProg.queries_bind, OProg.queries_ask, OProg.run_ask,
          OProg.run_bind, queries_verify1, run_verify1, queries_spartan, run_spartan]
        rw [hc]
        simp only [Option.map_some, tail, hf, ↓reduceIte, List.append_assoc]
        rfl
      refine ⟨pc', hc, hf, hacc', ?_, ?_⟩
      · intro q hq
        obtain ⟨rest, hrest⟩ := queries_verify2 H (Leaf.kap n) (endSt (stU H (Leaf.kap n) s n h π)
          (spBlock H (Leaf.kap n) (Spartan.parseMsgs (Leaf.kap n) π (off₁ (Leaf.kap n)))
            (stU H (Leaf.kap n) s n h π))) (Ligero.readLabel π 0)
          (rList H (Leaf.kap n) s n h π).toArray (eqTable (pc'.point.drop (lk (Leaf.kap n))))
          (Ligero.readEFs (π.extract 31 (off₁ (Leaf.kap n))) 0 (msgLen (Leaf.kap n)))
          (π.extract (off₂ (Leaf.kap n)) (off₃ (Leaf.kap n))) (π.extract (off₃ (Leaf.kap n)) π.size)
        rw [hQ, hrest]
        simp only [fsEntries, List.map_append, List.mem_append] at hq ⊢
        rcases hq with ((hq | hq) | hq) | hq
        · left; left; left; simpa [ent] using hq
        · left; left; right; exact hq
        · left; right; exact hq
        · right; left; exact hq
      · intro q hq
        rw [hQ]
        exact List.mem_append_right _ hq
    · simp at hacc'

end Verifier

/-! ## 6. The chain's data are the verifier's values -/

theorem chunks_size {α : Type} (k : ℕ) :
    ∀ (c : ℕ) (l : List α), k * c ≤ l.length → ∀ g ∈ Spartan.chunks k c l, g.size = k := by
  intro c
  induction c with
  | zero => intro l _ g hg; simp [Spartan.chunks] at hg
  | succ c ih =>
    intro l hl g hg
    simp only [Spartan.chunks, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp; rw [Nat.mul_succ] at hl; omega
    · exact ih _ (by simp; rw [Nat.mul_succ] at hl; omega) g hg

theorem size_readEFs (b : ByteArray) (o c : ℕ) : (Ligero.readEFs b o c).size = c := by
  simp [Ligero.readEFs]

/-- Parsed messages are well sized. -/
theorem parseMsgs_wellSized (κ : ℕ) (b : ByteArray) (off : ℕ) :
    (Spartan.parseMsgs κ b off).WellSized κ := by
  have hl : (Ligero.readEFs b off (Spartan.nElems κ)).toList.length = Spartan.nElems κ := by
    simp [size_readEFs]
  simp only [Spartan.parseMsgs, Spartan.split, Spartan.Msgs.WellSized, Leaf.chunks_length]
  refine ⟨trivial, chunks_size 4 _ _ (by rw [hl]; unfold Spartan.nElems; omega), trivial,
    chunks_size 3 _ _ (by simp only [List.length_drop, hl]; unfold Spartan.nElems; omega), ?_,
    trivial, chunks_size 3 _ _ (by simp only [List.length_drop, hl]; unfold Spartan.nElems; omega)⟩
  simp only [List.size_toArray, List.length_take, List.length_drop, hl]
  unfold Spartan.nElems; omega

section Data
variable (H : ByteArray → Digest) (κ : ℕ) (m : Spartan.Msgs) (st : Digest)

theorem length_spBlock (hm : m.WellSized κ) :
    (spBlock H κ m st).length = 5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ := by
  obtain ⟨ho, -, hi, -, -, hr, -⟩ := hm
  simp only [spBlock, List.length_append, length_sqBlock, length_rdBlock, ho, hi, hr,
    List.length_cons, List.length_nil]
  omega

/-! The seven blocks of `spBlock`. -/

/-- `τ`. -/
def spT : Log := sqBlock H st (Spartan.ly κ)
/-- The outer rounds. -/
def spO : Log := rdBlock H 0x03 (spS1 H κ st) m.outer
/-- `absorb(v_A ‖ v_B ‖ v_C)` and `ρ`. -/
def spE34 : Log :=
  [ent H (absorbQ (spS2 H κ m st) 0x04 (Ligero.efBytes #[m.vA, m.vB, m.vC])),
    ent H (squeezeQ (spA4 H κ m st))]
/-- The inner rounds. -/
def spI : Log := rdBlock H 0x05 (spRho H κ m st) m.inner
/-- `absorb(s_0 ‖ … ‖ s_63)`. -/
def spE5 : Log := [ent H (absorbQ (spS5 H κ m st) 0x06 (Ligero.efBytes m.slices))]
/-- `f`. -/
def spF : Log := sqBlock H (spA6 H κ m st) 6
/-- The ring-switching rounds. -/
def spR : Log := rdBlock H 0x07 (spS6 H κ m st) m.ring

theorem sp_eq : spBlock H κ m st = spT H κ st ++ spO H κ m st ++ spE34 H κ m st ++
    spI H κ m st ++ spE5 H κ m st ++ spF H κ m st ++ spR H κ m st := rfl

theorem sp_T {i : ℕ} (hi : i < Spartan.ly κ) :
    entAt (spBlock H κ m st) i = entAt (spT H κ st) i :=
  entAt_mid' (P := []) (Q := spO H κ m st ++ spE34 H κ m st ++ spI H κ m st ++ spE5 H κ m st ++
    spF H κ m st ++ spR H κ m st) (by rw [sp_eq]; simp only [List.nil_append, List.append_assoc])
    (by simp) (by simpa [spT, length_sqBlock] using hi)

theorem sp_O (hm : m.WellSized κ) {i : ℕ} (hi : i < 2 * Spartan.ly κ) :
    entAt (spBlock H κ m st) (Spartan.ly κ + i) = entAt (spO H κ m st) i :=
  entAt_mid' (P := spT H κ st) (Q := spE34 H κ m st ++ spI H κ m st ++ spE5 H κ m st ++
    spF H κ m st ++ spR H κ m st) (by rw [sp_eq]; simp only [List.append_assoc])
    (by simp [spT, length_sqBlock]) (by simpa [spO, length_rdBlock, hm.1] using hi)

theorem sp_E34 {i : ℕ} (hm : m.WellSized κ) (hi : i < 2) :
    entAt (spBlock H κ m st) (3 * Spartan.ly κ + i) = entAt (spE34 H κ m st) i :=
  entAt_mid' (P := spT H κ st ++ spO H κ m st) (Q := spI H κ m st ++ spE5 H κ m st ++
    spF H κ m st ++ spR H κ m st) (by rw [sp_eq]; simp only [List.append_assoc])
    (by simp [spT, spO, length_sqBlock, length_rdBlock, hm.1] <;> omega) (by simpa [spE34] using hi)

theorem sp_I (hm : m.WellSized κ) {i : ℕ} (hi : i < 2 * Spartan.ly κ) :
    entAt (spBlock H κ m st) (3 * Spartan.ly κ + 2 + i) = entAt (spI H κ m st) i :=
  entAt_mid' (P := spT H κ st ++ spO H κ m st ++ spE34 H κ m st) (Q := spE5 H κ m st ++
    spF H κ m st ++ spR H κ m st) (by rw [sp_eq]; simp only [List.append_assoc])
    (by simp [spT, spO, spE34, length_sqBlock, length_rdBlock, hm.1] <;> omega)
    (by simpa [spI, length_rdBlock, hm.2.2.1] using hi)

theorem sp_E5 (hm : m.WellSized κ) :
    entAt (spBlock H κ m st) (5 * Spartan.ly κ + 2) = entAt (spE5 H κ m st) 0 :=
  entAt_mid' (P := spT H κ st ++ spO H κ m st ++ spE34 H κ m st ++ spI H κ m st)
    (Q := spF H κ m st ++ spR H κ m st) (by rw [sp_eq]; simp only [List.append_assoc])
    (by simp [spT, spO, spE34, spI, length_sqBlock, length_rdBlock, hm.1, hm.2.2.1] <;> omega)
    (by simp [spE5])

theorem sp_F (hm : m.WellSized κ) {i : ℕ} (hi : i < 6) :
    entAt (spBlock H κ m st) (5 * Spartan.ly κ + 3 + i) = entAt (spF H κ m st) i :=
  entAt_mid' (P := spT H κ st ++ spO H κ m st ++ spE34 H κ m st ++ spI H κ m st ++
    spE5 H κ m st) (Q := spR H κ m st) (by rw [sp_eq])
    (by simp [spT, spO, spE34, spI, spE5, length_sqBlock, length_rdBlock, hm.1, hm.2.2.1] <;> omega)
    (by simpa [spF, length_sqBlock] using hi)

theorem sp_R (hm : m.WellSized κ) {i : ℕ} (hi : i < 2 * Spartan.lq κ) :
    entAt (spBlock H κ m st) (5 * Spartan.ly κ + 9 + i) = entAt (spR H κ m st) i :=
  entAt_mid' (P := spT H κ st ++ spO H κ m st ++ spE34 H κ m st ++ spI H κ m st ++
    spE5 H κ m st ++ spF H κ m st) (Q := []) (by rw [sp_eq]; simp)
    (by simp [spT, spO, spE34, spI, spE5, spF, length_sqBlock, length_rdBlock, hm.1, hm.2.2.1] <;> omega)
    (by simpa [spR, length_rdBlock, hm.2.2.2.2.2.1] using hi)

end Data



/-! ### The whole entry list, block by block -/

section Whole
variable (H : ByteArray → Digest) (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray)
  (m : Spartan.Msgs) (vB : ByteArray)

/-- `verify1`'s block of the entry list. -/
def eV1 : Log := v1Block H κ (H (seedQ s n h)) (π.extract 0 31) (π.extract 31 (Leaf.off₁ κ))
/-- `Spartan.verify`'s block. -/
def eS : Log := spBlock H κ m (stU H κ s n h π)
/-- The state after `Spartan.verify`. -/
def stV : Digest := endSt (stU H κ s n h π) (eS H κ s n h π m)
/-- `verify2`'s block. -/
def eV2 : Log := v2Block H κ (stV H κ s n h π m) vB

theorem fs_eq : fsEntries H κ s n h π m vB =
    [ent H (seedQ s n h)] ++ eV1 H κ s n h π ++ eS H κ s n h π m ++ eV2 H κ s n h π m vB := rfl

theorem length_eV1 : (eV1 H κ s n h π).length = rows κ + 2 := by
  simp [eV1, v1Block, length_sqBlock]

theorem length_eV2 : (eV2 H κ s n h π m vB).length = nJ κ + 1 := by
  simp [eV2, v2Block, length_sqBlock]

theorem E_0 : entAt (fsEntries H κ s n h π m vB) 0 = ent H (seedQ s n h) := by
  simp [fs_eq, entAt]

theorem E_V1 {i : ℕ} (hi : i < rows κ + 2) :
    entAt (fsEntries H κ s n h π m vB) (1 + i) = entAt (eV1 H κ s n h π) i :=
  entAt_mid' (P := [ent H (seedQ s n h)]) (Q := eS H κ s n h π m ++ eV2 H κ s n h π m vB)
    (by rw [fs_eq]; simp only [List.append_assoc]) (by simp)
    (by rw [length_eV1]; exact hi)

theorem E_S {i : ℕ} (hi : i < (eS H κ s n h π m).length) :
    entAt (fsEntries H κ s n h π m vB) (3 + rows κ + i) = entAt (eS H κ s n h π m) i :=
  entAt_mid' (P := [ent H (seedQ s n h)] ++ eV1 H κ s n h π) (Q := eV2 H κ s n h π m vB)
    (by rw [fs_eq]) (by simp [length_eV1]; omega) hi

theorem E_V2 {i : ℕ} (hi : i < nJ κ + 1) :
    entAt (fsEntries H κ s n h π m vB) (3 + rows κ + (eS H κ s n h π m).length + i) =
      entAt (eV2 H κ s n h π m vB) i :=
  entAt_mid' (P := [ent H (seedQ s n h)] ++ eV1 H κ s n h π ++ eS H κ s n h π m) (Q := [])
    (by rw [fs_eq]; simp) (by simp [length_eV1]; omega) (by rw [length_eV2]; exact hi)

theorem length_fs (hm : m.WellSized κ) : (fsEntries H κ s n h π m vB).length =
    3 + rows κ + (5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ) + (nJ κ + 1) := by
  rw [fs_eq]
  simp only [List.length_append, List.length_singleton, length_eV1, length_eV2]
  rw [show (eS H κ s n h π m).length = _ from length_spBlock H κ m _ hm]
  omega

end Whole

/-! ### The chain's fields -/

theorem extract_root (π : ByteArray) (h : 31 ≤ π.size) :
    π.extract 0 31 = bytesOf (Ligero.readLabel π 0) := by
  apply ByteArray.ext_toList
  rw [ByteArray.data_extract, Array.toList_extract]
  simp only [bytesOf, Ligero.readLabel, Vector.toArray_ofFn, Array.toList_ofFn, List.extract]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn, Array.length_toList]
    have : π.data.size = π.size := rfl
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, Array.getElem_toList]
    rw [getElem!_pos π (0 + i) (by simp at h2; omega)]
    simp only [Nat.zero_add]
    rfl

theorem ly_eq (κ : ℕ) : Spartan.ly κ = 15 + κ := by
  simp only [Spartan.ly, Spartan.lu, Spartan.lq]; omega

theorem sq_ans (H : ByteArray → Digest) (st : Digest) (k i : ℕ) (hi : i < k) :
    (entAt (sqBlock H st k) i).2 = ((sqBlock H st k).map Prod.snd).getD i default := by
  unfold entAt
  rw [List.getD_eq_getElem _ _ (by simpa [length_sqBlock] using hi),
    List.getD_eq_getElem _ _ (by simpa [length_sqBlock] using hi), List.getElem_map]

theorem efs_efBytes (g : Array EF) {c : ℕ} (hc : g.size = c) :
    Ligero.readEFs (Ligero.efBytes g) 0 c = g := by
  subst hc; exact Ligero.readEFs_efBytes g

section DataE
variable (H : ByteArray → Digest) (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray)
  (m : Spartan.Msgs) (vB : ByteArray)

/-- The positions of `spBlock` inside the entry list. -/
theorem E_S' (hm : m.WellSized κ) {i : ℕ} (hi : i < 5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ) :
    entAt (fsEntries H κ s n h π m vB) (3 + rows κ + i) = entAt (spBlock H κ m
      (stU H κ s n h π)) i :=
  E_S H κ s n h π m vB (by rw [eS, length_spBlock H κ m _ hm]; exact hi)

theorem stmtOf_fs (hn : n < 2 ^ 64) : stmtOf (fsEntries H κ s n h π m vB) = (s, n, h) := by
  unfold stmtOf
  rw [E_0]
  simp [ent, seedOf_seedQ s hn h]

theorem rootOf_fs (hπ : 31 ≤ π.size) :
    rootOf (fsEntries H κ s n h π m vB) = Ligero.readLabel π 0 := by
  unfold rootOf
  rw [show (1 : ℕ) = 1 + 0 from rfl, E_V1 H κ s n h π m vB (by omega)]
  simp only [eV1, v1Block, entAt, List.cons_append, List.getD_cons_zero, ent]
  rw [extract_root π hπ, parseAbsorbRoot_absorbQ]
  rfl

theorem rVec_fs : rVec κ (fsEntries H κ s n h π m vB) = rList H κ s n h π := by
  unfold rVec rList
  apply List.ext_getElem (by simp [length_sqBlock])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, chAt]
  rw [show 2 + i = 1 + (1 + i) by omega, E_V1 H κ s n h π m vB (by omega)]
  rw [entAt_mid' (E := eV1 H κ s n h π)
    (P := [ent H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))])
    (X := sqBlock H (H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))) (rows κ))
    (Q := _) (i := i) rfl (by simp) (by simpa [length_sqBlock] using h1), sq_ans _ _ _ _ h1,
    List.getD_eq_getElem _ _ (by simpa [length_sqBlock] using h1)]
  simp

theorem ubarOf_fs : ubarOf κ (fsEntries H κ s n h π m vB) =
    Ligero.readEFs (π.extract 31 (Leaf.off₁ κ)) 0 (msgLen κ) := by
  unfold ubarOf efsAt pU
  rw [show 2 + rows κ = 1 + (rows κ + 1) by omega, E_V1 H κ s n h π m vB (by omega)]
  rw [entAt_mid' (E := eV1 H κ s n h π)
    (P := [ent H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))] ++
      sqBlock H (H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))) (rows κ))
    (X := [ent H (absorbQ (endSt (H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31)))
      (sqBlock H (H (absorbQ (H (seedQ s n h)) 0x01 (π.extract 0 31))) (rows κ))) 0x02
      (π.extract 31 (Leaf.off₁ κ)))]) (Q := [])
    (by simp [eV1, v1Block]) (by simp [length_sqBlock]) (i := 0) (by simp)]
  simp [entAt, ent, msgOf_absorbQ]

end DataE

section DataS
variable (H : ByteArray → Digest) (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray)
  (m : Spartan.Msgs) (vB : ByteArray) (hm : m.WellSized κ)
include hm

theorem tauOf_fs : tauOf κ (fsEntries H κ s n h π m vB) =
    ((sqBlock H (stU H κ s n h π) (Spartan.ly κ)).map Prod.snd).map chE := by
  unfold tauOf
  apply List.ext_getElem (by simp [length_sqBlock, ly_eq])
  intro l h1 h2
  simp only [List.length_map, List.length_range] at h1
  have hl : l < Spartan.ly κ := by rw [ly_eq]; exact h1
  simp only [List.getElem_map, List.getElem_range, chAt, pTau]
  rw [show 3 + rows κ + l = 3 + rows κ + l from rfl,
    E_S' H κ s n h π m vB hm (by omega), sp_T H κ m _ hl, spT, sq_ans _ _ _ _ hl,
    List.getD_eq_getElem _ _ (by simpa [length_sqBlock] using hl)]
  simp

theorem gOut_fs {l : ℕ} (hl : l < Spartan.ly κ) :
    gOut κ (fsEntries H κ s n h π m vB) l = m.outer[l]'(by rw [hm.1]; exact hl) := by
  unfold gOut efsAt
  rw [show pG κ l = 3 + rows κ + (Spartan.ly κ + 2 * l) by unfold pG; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_O H κ m _ hm (by omega), spO,
    rdBlock_msg _ _ _ _ _ (by rw [hm.1]; exact hl)]
  exact efs_efBytes _ (hm.2.1 _ (List.getElem_mem _))

theorem rxOf_fs : rxOf κ (fsEntries H κ s n h π m vB) =
    (rdAns H 0x03 (spS1 H κ (stU H κ s n h π)) m.outer).map chE := by
  unfold rxOf
  apply List.ext_getElem (by simp [length_rdAns, hm.1, ly_eq])
  intro l h1 h2
  simp only [List.length_map, List.length_range] at h1
  have hl : l < Spartan.ly κ := by rw [ly_eq]; exact h1
  simp only [List.getElem_map, List.getElem_range, chAt]
  rw [show pG κ l + 1 = 3 + rows κ + (Spartan.ly κ + (2 * l + 1)) by unfold pG; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_O H κ m _ hm (by omega), spO,
    rdBlock_ans _ _ _ _ _ (by rw [hm.1]; exact hl)]

theorem triOf_fs : triOf κ (fsEntries H κ s n h π m vB) = (m.vA, m.vB, m.vC) := by
  unfold triOf efsAt
  rw [show pTri κ = 3 + rows κ + (3 * Spartan.ly κ + 0) by unfold pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_E34 H κ m _ hm (by omega)]
  simp only [spE34, entAt, List.getD_cons_zero, ent, msgOf_absorbQ]
  rw [efs_efBytes _ (show (#[m.vA, m.vB, m.vC] : Array EF).size = 3 from rfl)]
  rfl

theorem rhoOf_fs : rhoOf κ (fsEntries H κ s n h π m vB) =
    chE (spRho H κ m (stU H κ s n h π)) := by
  unfold rhoOf chAt
  rw [show pTri κ + 1 = 3 + rows κ + (3 * Spartan.ly κ + 1) by unfold pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_E34 H κ m _ hm (by omega)]
  rfl

theorem gIn_fs {l : ℕ} (hl : l < Spartan.ly κ) :
    gIn κ (fsEntries H κ s n h π m vB) l = m.inner[l]'(by rw [hm.2.2.1]; exact hl) := by
  unfold gIn efsAt
  rw [show pGi κ l = 3 + rows κ + (3 * Spartan.ly κ + 2 + 2 * l) by
      unfold pGi pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_I H κ m _ hm (by omega), spI,
    rdBlock_msg _ _ _ _ _ (by rw [hm.2.2.1]; exact hl)]
  exact efs_efBytes _ (hm.2.2.2.1 _ (List.getElem_mem _))

theorem ryOf_fs : ryOf κ (fsEntries H κ s n h π m vB) =
    (rdAns H 0x05 (spRho H κ m (stU H κ s n h π)) m.inner).map chE := by
  unfold ryOf
  apply List.ext_getElem (by simp [length_rdAns, hm.2.2.1, ly_eq])
  intro l h1 h2
  simp only [List.length_map, List.length_range] at h1
  have hl : l < Spartan.ly κ := by rw [ly_eq]; exact h1
  simp only [List.getElem_map, List.getElem_range, chAt]
  rw [show pGi κ l + 1 = 3 + rows κ + (3 * Spartan.ly κ + 2 + (2 * l + 1)) by
      unfold pGi pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_I H κ m _ hm (by omega), spI,
    rdBlock_ans _ _ _ _ _ (by rw [hm.2.2.1]; exact hl)]

theorem slicesOf_fs : slicesOf κ (fsEntries H κ s n h π m vB) = m.slices := by
  unfold slicesOf efsAt
  rw [show pS κ = 3 + rows κ + (5 * Spartan.ly κ + 2) by unfold pS pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_E5 H κ m _ hm]
  simp only [spE5, entAt, List.getD_cons_zero, ent, msgOf_absorbQ]
  exact efs_efBytes _ hm.2.2.2.2.1

theorem fsOf_fs : fsOf κ (fsEntries H κ s n h π m vB) =
    ((sqBlock H (spA6 H κ m (stU H κ s n h π)) 6).map Prod.snd).map chE := by
  unfold fsOf
  apply List.ext_getElem (by simp [length_sqBlock])
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, chAt]
  rw [show pF κ p = 3 + rows κ + (5 * Spartan.ly κ + 3 + p) by
      unfold pF pS pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_F H κ m _ hm h1, spF, sq_ans _ _ _ _ h1,
    List.getD_eq_getElem _ _ (by simpa [length_sqBlock] using h1)]
  simp

theorem gRs_fs {l : ℕ} (hl : l < Spartan.lq κ) :
    gRs κ (fsEntries H κ s n h π m vB) l = m.ring[l]'(by rw [hm.2.2.2.2.2.1]; exact hl) := by
  unfold gRs efsAt
  rw [show pGr κ l = 3 + rows κ + (5 * Spartan.ly κ + 9 + 2 * l) by
      unfold pGr pS pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by omega), sp_R H κ m _ hm (by omega), spR,
    rdBlock_msg _ _ _ _ _ (by rw [hm.2.2.2.2.2.1]; exact hl)]
  exact efs_efBytes _ (hm.2.2.2.2.2.2 _ (List.getElem_mem _))

theorem rrOf_fs : rrOf κ (fsEntries H κ s n h π m vB) =
    (rdAns H 0x07 (spS6 H κ m (stU H κ s n h π)) m.ring).map chE := by
  unfold rrOf
  apply List.ext_getElem (by simp [length_rdAns, hm.2.2.2.2.2.1, Spartan.lq])
  intro l h1 h2
  simp only [List.length_map, List.length_range] at h1
  have hl : l < Spartan.lq κ := by unfold Spartan.lq; exact h1
  simp only [List.getElem_map, List.getElem_range, chAt]
  rw [show pGr κ l + 1 = 3 + rows κ + (5 * Spartan.ly κ + 9 + (2 * l + 1)) by
      unfold pGr pS pTri; rw [ly_eq]; omega,
    E_S' H κ s n h π m vB hm (by unfold Spartan.lq at hl ⊢; omega), sp_R H κ m _ hm (by omega), spR,
    rdBlock_ans _ _ _ _ _ (by rw [hm.2.2.2.2.2.1]; exact hl)]

theorem pV_eq : pV κ = 3 + rows κ + (eS H κ s n h π m).length + 0 := by
  rw [eS, length_spBlock H κ m _ hm]
  unfold pV pS pTri; rw [ly_eq]; unfold Spartan.lq; omega

theorem msgV_fs : msgOf (entAt (fsEntries H κ s n h π m vB) (pV κ)).1 = vB := by
  rw [pV_eq H κ s n h π m hm, E_V2 H κ s n h π m vB (by omega)]
  simp [eV2, v2Block, entAt, ent, msgOf_absorbQ]

theorem vOf_fs : vOf κ (fsEntries H κ s n h π m vB) = Ligero.readEFs vB 0 (msgLen κ) := by
  unfold vOf efsAt
  rw [msgV_fs H κ s n h π m vB hm]

theorem bOf_fs (j : Fin (nJ κ)) : bOf κ (fsEntries H κ s n h π m vB) j =
    ((sqBlock H (H (absorbQ (stV H κ s n h π m) 0x08 vB)) (nJ κ)).map Prod.snd).getD j default := by
  unfold bOf
  rw [show pV κ + 1 + j = 3 + rows κ + (eS H κ s n h π m).length + (1 + j) by
      rw [pV_eq H κ s n h π m hm]; omega,
    E_V2 H κ s n h π m vB (by omega)]
  rw [entAt_mid' (E := eV2 H κ s n h π m vB) (P := [ent H (absorbQ (stV H κ s n h π m) 0x08 vB)])
    (X := sqBlock H (H (absorbQ (stV H κ s n h π m) 0x08 vB)) (nJ κ)) (Q := [])
    (by simp [eV2, v2Block]) (i := j) (by simp) (by simp [length_sqBlock])]
  exact sq_ans _ _ _ _ j.2

end DataS

/-! ## 7. The entry list is linked and has the §6.2 shape -/

theorem fa_append {R : Step → ByteArray × Digest → Prop} {a c : List Step} {b d : Log}
    (h₁ : List.Forall₂ R a b) (h₂ : List.Forall₂ R c d) : List.Forall₂ R (a ++ c) (b ++ d) :=
  List.rel_append h₁ h₂

theorem linked_cons_getElem {e : ByteArray × Digest} {rest : Log} (h : LinkedFrom e.2 rest) :
    ∀ i (hi : i + 1 < (e :: rest).length), stateIn (e :: rest)[i + 1].1 = some (e :: rest)[i].2 := by
  intro i hi
  cases i with
  | zero =>
    cases rest with
    | nil => simp at hi
    | cons f fs => exact h.1
  | succ i => exact linkedFrom_getElem h i (by simpa using hi)

section Shape
variable (H : ByteArray → Digest) (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray)
  (m : Spartan.Msgs) (vB : ByteArray)

theorem linked_v1 (st : Digest) (rB uB : ByteArray) : LinkedFrom st (v1Block H κ st rB uB) := by
  unfold v1Block
  rw [linkedFrom_append, linkedFrom_append]
  refine ⟨⟨⟨stateIn_absorbQ _ _ _, trivial⟩, ?_⟩, ?_⟩
  · simpa [endSt, ent] using linked_sqBlock H _ (rows κ)
  · simp only [endSt_append]
    exact ⟨by simp [ent, endSt, stateIn_absorbQ], trivial⟩

theorem linked_sp (st : Digest) : LinkedFrom st (spBlock H κ m st) := by
  rw [sp_eq]
  refine (linkedFrom_append _ _ _).2 ⟨(linkedFrom_append _ _ _).2 ⟨(linkedFrom_append _ _ _).2
    ⟨(linkedFrom_append _ _ _).2 ⟨(linkedFrom_append _ _ _).2 ⟨(linkedFrom_append _ _ _).2
    ⟨linked_sqBlock H _ _, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact linked_rdBlock H _ _ _
  · rw [endSt_append]; exact ⟨stateIn_absorbQ _ _ _, stateIn_squeezeQ _, trivial⟩
  · rw [endSt_append, endSt_append]; exact linked_rdBlock H _ _ _
  · rw [endSt_append, endSt_append, endSt_append]; exact ⟨stateIn_absorbQ _ _ _, trivial⟩
  · rw [endSt_append, endSt_append, endSt_append, endSt_append]; exact linked_sqBlock H _ _
  · rw [endSt_append, endSt_append, endSt_append, endSt_append, endSt_append]
    exact linked_rdBlock H _ _ _

theorem linked_v2 (st : Digest) : LinkedFrom st (v2Block H κ st vB) := by
  unfold v2Block
  rw [linkedFrom_append]
  exact ⟨⟨stateIn_absorbQ _ _ _, trivial⟩, linked_sqBlock H _ _⟩

theorem linked_fs :
    LinkedFrom (H (seedQ s n h)) (eV1 H κ s n h π ++ eS H κ s n h π m ++ eV2 H κ s n h π m vB) := by
  rw [linkedFrom_append, linkedFrom_append, endSt_append]
  have e1 : endSt (H (seedQ s n h)) (eV1 H κ s n h π) = stU H κ s n h π := rfl
  have e2 : endSt (stU H κ s n h π) (eS H κ s n h π m) = stV H κ s n h π m := rfl
  rw [e1, e2]
  exact ⟨⟨linked_v1 H κ _ _ _, linked_sp H κ m _⟩, linked_v2 H κ vB _⟩

/-- **The entry list has the §6.2 shape**, given well-sized messages and fields 1, 2 and 8 of
their §7 lengths. -/
theorem steps_fs (hm : m.WellSized κ) (hπ : Leaf.off₃ κ ≤ π.size)
    (hv : vB.size = 24 * msgLen κ) :
    List.Forall₂ (fun st e => Step.matches st e.1) (shape κ) (fsEntries H κ s n h π m vB) := by
  obtain ⟨ho, hos, hi, his, hsl, hr, hrs⟩ := hm
  have hshape : shape κ = [Step.seed] ++
      ([Step.absorb 0x01 31] ++ List.replicate (rows κ) Step.squeeze ++
        [Step.absorb 0x02 (24 * msgLen κ)]) ++
      (List.replicate (Spartan.ly κ) Step.squeeze ++
        (List.replicate m.outer.length [Step.absorb 0x03 (24 * 4), .squeeze]).flatten ++
        [Step.absorb 0x04 72, .squeeze] ++
        (List.replicate m.inner.length [Step.absorb 0x05 (24 * 3), .squeeze]).flatten ++
        [Step.absorb 0x06 1536] ++ List.replicate 6 Step.squeeze ++
        (List.replicate m.ring.length [Step.absorb 0x07 (24 * 3), .squeeze]).flatten) ++
      ([Step.absorb 0x08 (24 * msgLen κ)] ++ List.replicate (nJ κ) Step.squeeze) := by
    rw [ho, hi, hr, ly_eq]
    simp [shape, Spartan.lq]
  have hoff : Leaf.off₁ κ ≤ Leaf.off₂ κ ∧ Leaf.off₂ κ ≤ Leaf.off₃ κ := by
    unfold Leaf.off₃ Leaf.off₂; omega
  have h1 : Leaf.off₁ κ = 31 + 24 * msgLen κ := rfl
  rw [hshape, fs_eq]
  refine fa_append (fa_append (fa_append ?_ ?_) ?_) ?_
  · exact List.Forall₂.cons (check_seedQ s n h) List.Forall₂.nil
  · unfold eV1 v1Block
    refine fa_append (fa_append ?_ (steps_sqBlock H _ _)) ?_
    · exact List.Forall₂.cons (check_absorbQ _ _ _ (by rw [ByteArray.size_extract]; omega))
        List.Forall₂.nil
    · exact List.Forall₂.cons (check_absorbQ _ _ _ (by rw [ByteArray.size_extract]; omega))
        List.Forall₂.nil
  · unfold eS spBlock
    refine fa_append (fa_append (fa_append (fa_append (fa_append (fa_append
      (steps_sqBlock H _ _) (steps_rdBlock H _ 4 _ _ hos)) ?_) (steps_rdBlock H _ 3 _ _ his)) ?_)
      (steps_sqBlock H _ _)) (steps_rdBlock H _ 3 _ _ hrs)
    · exact List.Forall₂.cons (check_absorbQ _ _ _ (by rw [Spartan.efBytes_size]; rfl))
        (List.Forall₂.cons (check_squeezeQ _) List.Forall₂.nil)
    · exact List.Forall₂.cons (check_absorbQ _ _ _ (by rw [Spartan.efBytes_size, hsl]))
        List.Forall₂.nil
  · unfold eV2 v2Block
    exact fa_append (List.Forall₂.cons (check_absorbQ _ _ _ hv) List.Forall₂.nil)
      (steps_sqBlock H _ _)

end Shape

/-! ## 8. The checks that pass: `¬ Rej` -/

/-- **A passing `verifyRounds`**: every round has `d + 1` coefficients and `g(0) + g(1)` equal to
the running claim `cl l`, and the result is the last claim. -/
theorem verifyRounds_some {d : ℕ} :
    ∀ (gs : List (Array EF)) (rs : List EF) (c₀ c : EF) (cl : ℕ → EF), gs.length = rs.length →
      cl 0 = c₀ → (∀ l (hl : l < gs.length), cl (l + 1) = peval gs[l] (rs.getD l 0)) →
      verifyRounds d c₀ (gs.zip rs) = some c →
      (∀ l (hl : l < gs.length), gs[l].size = d + 1 ∧ peval gs[l] 0 + peval gs[l] 1 = cl l) ∧
        c = cl gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro rs c₀ c cl _ h0 _ hv
    simp only [List.zip_nil_left, verifyRounds, Option.some.injEq] at hv
    exact ⟨fun l hl => by simp at hl, by rw [← hv, ← h0]; rfl⟩
  | cons g gs ih =>
    intro rs c₀ c cl hlen h0 hs hv
    obtain ⟨r, rs, rfl⟩ : ∃ r rs', rs = r :: rs' := by
      cases rs with
      | nil => simp at hlen
      | cons r rs' => exact ⟨r, rs', rfl⟩
    simp only [List.zip_cons_cons, verifyRounds] at hv
    split_ifs at hv with hok
    have h1 : cl 1 = peval g r := hs 0 (by simp)
    obtain ⟨ih1, ih2⟩ := ih rs (peval g r) c (fun l => cl (l + 1)) (by simpa using hlen) h1
      (fun l hl => hs (l + 1) (by simpa using hl)) hv
    refine ⟨fun l hl => ?_, by rw [ih2]; rfl⟩
    cases l with
    | zero => rw [h0]; exact hok
    | succ l => exact ih1 l (by simpa using hl)

/-- What `Spartan.check` returning a claim means. -/
theorem check_some {κ : ℕ} {ev : Spartan.Evals} {m : Spartan.Msgs} {τ rx : List EF} {ρ : EF}
    {ry fs rr : List EF} {pc : Spartan.PcsClaim}
    (h : Spartan.check κ ev m τ rx ρ ry fs rr = some pc) :
    ∃ c₁ c₂ c₃, verifyRounds 3 0 (m.outer.zip rx) = some c₁ ∧
      verifyRounds 2 (m.vA + ρ * m.vB + ρ ^ 2 * m.vC) (m.inner.zip ry) = some c₂ ∧
      verifyRounds 2 (target Spartan.xE fs m.slices) (m.ring.zip rr) = some c₃ ∧
      c₁ = eqPts τ rx * (m.vA * m.vB + m.vC) ∧
      c₂ = ((ev.mats rx ry).1 + ρ * (ev.mats rx ry).2.1 + ρ ^ 2 * (ev.mats rx ry).2.2) *
        Spartan.zV κ ev m.slices ry ∧
      pc = ⟨rr, weightEval fs ((ry.take (Spartan.lu κ)).drop 6) rr, c₃⟩ := by
  unfold Spartan.check at h
  split_ifs at h with hsz
  split at h
  · rename_i c₁ c₂ c₃ h1 h2 h3
    simp only at h
    split_ifs at h with hc
    exact ⟨c₁, c₂, c₃, h1, h2, h3, hc.1, hc.2, (Option.some.inj h).symm⟩
  · cases h

/-- **No check fails on the verifier's chain** (`¬ Rej`): `check` returned a claim and check (f)
passed. -/
theorem not_rej (ev : Leaf.EvalsFor) (H : ByteArray → Digest) (s : Digest) {n : ℕ} (h : Digest)
    (π : ByteArray) (m : Spartan.Msgs) (vB : ByteArray) (hm : m.WellSized (Leaf.kap n))
    (hn : n < 2 ^ 64) {pc : Spartan.PcsClaim}
    (hc : Spartan.check (Leaf.kap n) (ev (Leaf.kap n) n s h) m
        ((sqBlock H (stU H (Leaf.kap n) s n h π) (Spartan.ly (Leaf.kap n))).map Prod.snd |>.map chE)
        ((rdAns H 0x03 (spS1 H (Leaf.kap n) (stU H (Leaf.kap n) s n h π)) m.outer).map chE)
        (chE (spRho H (Leaf.kap n) m (stU H (Leaf.kap n) s n h π)))
        ((rdAns H 0x05 (spRho H (Leaf.kap n) m (stU H (Leaf.kap n) s n h π)) m.inner).map chE)
        (((sqBlock H (spA6 H (Leaf.kap n) m (stU H (Leaf.kap n) s n h π)) 6).map Prod.snd).map chE)
        ((rdAns H 0x07 (spS6 H (Leaf.kap n) m (stU H (Leaf.kap n) s n h π)) m.ring).map chE)
        = some pc)
    (hf : Leaf.finalCheck (Leaf.kap n) pc (Ligero.readEFs vB 0 (msgLen (Leaf.kap n))) = true) :
    ¬ Rej ev (fsEntries H (Leaf.kap n) s n h π m vB) := by
  set κ := Leaf.kap n with hκ
  set E := fsEntries H κ s n h π m vB with hE
  have hst : stmtOf E = (s, n, h) := stmtOf_fs H κ s n h π m vB hn
  have hk : kapOf E = κ := by unfold kapOf; rw [hst]; rfl
  obtain ⟨c₁, c₂, c₃, h1, h2, h3, hc1, hc2, hpc⟩ := check_some hc
  have hly := ly_eq κ
  -- the three sumchecks
  have ho := verifyRounds_some m.outer _ 0 c₁ (clOut κ E) (by simp [length_rdAns])
    rfl (fun l hl => by
      simp only [clOut]
      rw [gOut_fs H κ s n h π m vB hm (by rw [← hm.1]; exact hl), rxOf_fs H κ s n h π m vB hm])
    h1
  have hi := verifyRounds_some m.inner _ _ c₂ (clIn κ E) (by simp [length_rdAns])
    (by simp only [clIn]; rw [triOf_fs H κ s n h π m vB hm, rhoOf_fs H κ s n h π m vB hm])
    (fun l hl => by
      simp only [clIn]
      rw [gIn_fs H κ s n h π m vB hm (by rw [← hm.2.2.1]; exact hl),
        ryOf_fs H κ s n h π m vB hm])
    h2
  have hr := verifyRounds_some m.ring _ _ c₃ (clRs κ E) (by simp [length_rdAns])
    (by simp only [clRs]; rw [fsOf_fs H κ s n h π m vB hm, slicesOf_fs H κ s n h π m vB hm])
    (fun l hl => by
      simp only [clRs]
      rw [gRs_fs H κ s n h π m vB hm (by rw [← hm.2.2.2.2.2.1]; exact hl),
        rrOf_fs H κ s n h π m vB hm])
    h3
  intro hrej
  unfold Rej at hrej
  simp only [hk, hst] at hrej
  rcases hrej with ⟨l, hl, -, hno⟩ | ⟨-, hb⟩ | ⟨l, hl, -, hno⟩ | ⟨-, hd⟩ | ⟨l, hl, -, hno⟩ | ⟨-, hf'⟩
  · have hl' : l < m.outer.length := by rw [hm.1]; omega
    exact hno ⟨by rw [gOut_fs H κ s n h π m vB hm (by omega)]; exact (ho.1 l hl').1,
      by rw [gOut_fs H κ s n h π m vB hm (by omega)]; exact (ho.1 l hl').2⟩
  · apply hb
    rw [show 15 + κ = m.outer.length by rw [hm.1]; omega, ← ho.2, hc1,
      tauOf_fs H κ s n h π m vB hm, rxOf_fs H κ s n h π m vB hm, triOf_fs H κ s n h π m vB hm]
  · have hl' : l < m.inner.length := by rw [hm.2.2.1]; omega
    exact hno ⟨by rw [gIn_fs H κ s n h π m vB hm (by omega)]; exact (hi.1 l hl').1,
      by rw [gIn_fs H κ s n h π m vB hm (by omega)]; exact (hi.1 l hl').2⟩
  · apply hd
    rw [show 15 + κ = m.inner.length by rw [hm.2.2.1]; omega, ← hi.2, hc2,
      rxOf_fs H κ s n h π m vB hm, ryOf_fs H κ s n h π m vB hm, rhoOf_fs H κ s n h π m vB hm,
      slicesOf_fs H κ s n h π m vB hm]
  · have hl' : l < m.ring.length := by rw [hm.2.2.2.2.2.1]; unfold Spartan.lq; omega
    exact hno ⟨by rw [gRs_fs H κ s n h π m vB hm (by unfold Spartan.lq; omega)]; exact (hr.1 l hl').1,
      by rw [gRs_fs H κ s n h π m vB hm (by unfold Spartan.lq; omega)]; exact (hr.1 l hl').2⟩
  · apply hf'
    have hcl : clRs κ E (8 + κ) = c₃ := by
      rw [show 8 + κ = m.ring.length by rw [hm.2.2.2.2.2.1]; rfl, ← hr.2]
    rw [hcl, rhiOf, fsOf_fs H κ s n h π m vB hm, ryOf_fs H κ s n h π m vB hm,
      rrOf_fs H κ s n h π m vB hm, vOf_fs H κ s n h π m vB hm]
    unfold Leaf.finalCheck at hf
    rw [hpc] at hf
    simpa using hf

/-! ## 9. L-K4 -/

/-- Every entry of a list is the entry of its query under `H`. -/
def IsEnt (H : ByteArray → Digest) (es : Log) : Prop := ∀ e ∈ es, e.2 = H e.1

theorem isEnt_append {H : ByteArray → Digest} {A B : Log} (hA : IsEnt H A) (hB : IsEnt H B) :
    IsEnt H (A ++ B) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hA e h
  · exact hB e h

theorem isEnt_ent (H : ByteArray → Digest) (qs : List ByteArray) : IsEnt H (qs.map (ent H)) := by
  intro e he
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp he
  rfl

theorem isEnt_single (H : ByteArray → Digest) (q : ByteArray) : IsEnt H [ent H q] := by
  intro e he; simp at he; subst he; rfl

theorem isEnt_sqBlock (H : ByteArray → Digest) (st : Digest) (k : ℕ) :
    IsEnt H (sqBlock H st k) := by
  induction k generalizing st with
  | zero => intro e he; simp [sqBlock] at he
  | succ k ih =>
    intro e he
    simp only [sqBlock, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

theorem isEnt_rdBlock (H : ByteArray → Digest) (kind : UInt8) (st : Digest)
    (gs : List (Array EF)) : IsEnt H (rdBlock H kind st gs) := by
  induction gs generalizing st with
  | nil => intro e he; simp [rdBlock] at he
  | cons g gs ih =>
    intro e he
    simp only [rdBlock, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · rfl
    · rfl
    · exact ih _ e he

theorem isEnt_fs (H : ByteArray → Digest) (κ : ℕ) (s : Digest) (n : ℕ) (h : Digest)
    (π : ByteArray) (m : Spartan.Msgs) (vB : ByteArray) :
    IsEnt H (fsEntries H κ s n h π m vB) := by
  rw [fs_eq]
  refine isEnt_append (isEnt_append (isEnt_append (isEnt_single _ _) ?_) ?_) ?_
  · exact isEnt_append (isEnt_append (isEnt_single _ _) (isEnt_sqBlock _ _ _)) (isEnt_single _ _)
  · unfold eS spBlock
    exact isEnt_append (isEnt_append (isEnt_append (isEnt_append (isEnt_append (isEnt_append
      (isEnt_sqBlock _ _ _) (isEnt_rdBlock _ _ _ _)) (isEnt_append (isEnt_single _ _)
      (isEnt_single _ _))) (isEnt_rdBlock _ _ _ _)) (isEnt_single _ _)) (isEnt_sqBlock _ _ _))
      (isEnt_rdBlock _ _ _ _)
  · exact isEnt_append (isEnt_single _ _) (isEnt_sqBlock _ _ _)

/-- The column-phase part of `RunChain` (`SpartanChainSoundnessFinal.ColumnsAccepted`, verbatim). -/
def ColumnsOK (L es : Log) : Prop :=
  ∃ st opens,
    (Ligero.verify2 (kapOf es) st (rootOf es) (rVec (kapOf es) es).toArray (aOf (kapOf es) es)
        (ubarOf (kapOf es) es) (msgOf (entAt es (pV (kapOf es))).1) opens).runLog L = some true ∧
      SoundnessPCS.idxTuple L (kapOf es) st (msgOf (entAt es (pV (kapOf es))).1) = bOf (kapOf es) es

/-- **L-K4 `runLog_chain`** (component form of `SoundnessFinal.RunChain`): on a log without bad
events, an accepting run of the leaf SNARK verifier with `1 ≤ n ≤ chainCap` and the §7 bytes
through field 8 present is a complete chain of `L` with the proof's statement, no failed check
and an accepting column phase. -/
theorem runLog_chain' (ev : Leaf.EvalsFor) {L : Log} {s : Digest} {n : ℕ} {h : Digest}
    {π : ByteArray} (hb : ¬ Bad L) (hn : 1 ≤ n) (hcap : n ≤ chainCap)
    (hsz : Leaf.off₃ (Leaf.kap n) ≤ π.size)
    (hacc : (Leaf.snarkProg ev s n h π).runLog L = some true) :
    ∃ j, IsChain L j ∧ (pathOf L j).length = len (kapOf (entriesOf L (pathOf L j))) ∧
      stmtOf (entriesOf L (pathOf L j)) = (s, n, h) ∧ ¬ Rej ev (entriesOf L (pathOf L j)) ∧
      ColumnsOK L (entriesOf L (pathOf L j)) := by
  set O := OProg.logOracle L with hO
  obtain ⟨hq, hrun⟩ := (OProg.runLog_eq_some_iff _ _).mp hacc
  obtain ⟨pc, hc, hf, hv2, hfsq, hv2q⟩ := snark_accept O ev s n h π hrun
  set κ := Leaf.kap n with hκ
  set m := Spartan.parseMsgs κ π (Leaf.off₁ κ) with hmdef
  set vB := π.extract (Leaf.off₂ κ) (Leaf.off₃ κ) with hvB
  set E := fsEntries O κ s n h π m vB with hE
  have hm : m.WellSized κ := parseMsgs_wellSized κ π _
  have hn64 : n < 2 ^ 64 := by unfold chainCap at hcap; omega
  have hst : stmtOf E = (s, n, h) := stmtOf_fs O κ s n h π m vB hn64
  have hk : kapOf E = κ := by unfold kapOf; rw [hst]; rfl
  have hoff : Leaf.off₂ κ ≤ Leaf.off₃ κ := by unfold Leaf.off₃; omega
  have hvsz : vB.size = 24 * msgLen κ := by
    rw [hvB, ByteArray.size_extract]; unfold Leaf.off₃ at hsz ⊢; omega
  -- the entries of `E` are entries of `L`
  have hmemE : ∀ e ∈ E, e ∈ L := by
    intro e he
    have h1 : e.1 ∈ L.map Prod.fst := hq _ (hfsq _ (List.mem_map_of_mem he))
    have h2 : e = (e.1, O e.1) := by
      conv_lhs => rw [← Prod.mk.eta (p := e)]
      rw [isEnt_fs O κ s n h π m vB e he]
    rw [h2]; exact OProg.mem_logOracle h1
  have hE0 : E = ent O (seedQ s n h) :: (eV1 O κ s n h π ++ eS O κ s n h π m ++
      eV2 O κ s n h π m vB) := by
    show fsEntries O κ s n h π m vB = _
    rw [fs_eq]; simp
  have hlinkE : ∀ i (hi : i + 1 < E.length), stateIn E[i + 1].1 = some E[i].2 := by
    intro i hi
    have := linked_cons_getElem (e := ent O (seedQ s n h)) (linked_fs O κ s n h π m vB) i
      (by rw [← hE0]; exact hi)
    simp only [← hE0] at this
    exact this
  have hne : E ≠ [] := by rw [hE0]; simp
  have hseed : stateIn (E[0]'(List.length_pos_iff.mpr hne)).1 = none := by
    simp only [hE0, List.getElem_cons_zero, ent]
    exact stateIn_of_seedOf (seedOf_seedQ s hn64 h)
  obtain ⟨j, hj, -, hpath⟩ := chain_of_linked hb E hne hmemE hseed hlinkE
  have hsteps := steps_fs O κ s n h π m vB hm hsz hvsz
  have hlen : E.length = len κ := by rw [len]; exact hsteps.length_eq.symm
  have hpl : (pathOf L j).length = E.length := by
    rw [← hpath]; simp [entriesOf]
  refine ⟨j, ⟨hj, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> rw [hpath]
  · -- `Matches E`
    refine ⟨s, n, h, ?_, hn, hcap, hlen.le, fun i hi => ⟨hlinkE i hi, ?_⟩⟩
    · rw [hE0]; simp [ent, seedOf_seedQ s hn64 h]
    · have := hsteps.get (i := i + 1) (by rw [hsteps.length_eq]; exact hi) hi
      simp only [List.get_eq_getElem] at this
      exact this
  · rw [hpl, hk, hlen]
  · exact hst
  · exact not_rej ev O s h π m vB hm hn64 hc hf
  · -- the column phase
    obtain ⟨c₁, c₂, c₃, -, -, -, -, -, hpc⟩ := check_some hc
    refine ⟨stV O κ s n h π m, π.extract (Leaf.off₃ κ) π.size, ?_, ?_⟩
    · rw [hk, rootOf_fs O κ s n h π m vB (by unfold Leaf.off₃ Leaf.off₂ Leaf.off₁ Ligero.size1 at hsz; omega),
        rVec_fs, ubarOf_fs, msgV_fs O κ s n h π m vB hm]
      have ha : aOf κ E = eqTable (pc.point.drop (lk κ)) := by
        unfold aOf; rw [rrOf_fs O κ s n h π m vB hm, hpc]
      rw [ha]
      exact (OProg.runLog_eq_some_iff _ _).mpr ⟨fun q hq' => hq q (hv2q q hq'), hv2⟩
    · rw [hk, msgV_fs O κ s n h π m vB hm]
      funext i
      rw [bOf_fs O κ s n h π m vB hm]
      simp only [SoundnessPCS.idxTuple, SoundnessPCS.idxAnswers, absorb, OProg.run_ask,
        run_squeezeN']
      rw [List.getD_eq_getElem _ _ (by simp [length_sqBlock])]

/-- **L-K4 `runLog_chain`** in the form `SoundnessFinal.RunChain` takes. -/
theorem runLog_chain (ev : Leaf.EvalsFor) {L : Log} {s : Digest} {n : ℕ} {h : Digest}
    {π : ByteArray} (hb : ¬ Bad L) (hn : 1 ≤ n) (hcap : n ≤ chainCap)
    (hsz : Leaf.off₃ (Leaf.kap n) ≤ π.size)
    (hacc : (Leaf.snarkProg ev s n h π).runLog L = some true) :
    SoundnessFinal.RunChain ev L s n h :=
  runLog_chain' ev hb hn hcap hsz hacc

/-- **The hypothesis `hchain` of `SoundnessFinal.mu_final_leaf`**, for the entry's leaf verifier,
from an accepting leaf run (whose header check gives `n ≤ chainCap` and the exact size). -/
theorem hchain_of_leafProg (ev : Leaf.EvalsFor) {L : Log} {c : Digest} {π : Proof}
    (hacc : (leafProg (Leaf.leafVerifier ev) c π).runLog L = some true) :
    ¬ Bad L → leafN π ≠ 0 →
      ((Leaf.leafVerifier ev).prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L =
        some true →
      SoundnessFinal.RunChain ev L (leafS π) (leafN π) (leafH π) := by
  intro hb hn hrun
  obtain ⟨hcap, hsize, -, -, -⟩ := SoundnessFinal.leafProg_accept (Leaf.leafVerifier ev) hacc
  have hsz : Leaf.off₃ (Leaf.kap (leafN π)) ≤ (leafSnark π).size := by
    have : π.size = 80 + Leaf.snarkSize (Leaf.kap (leafN π)) := by
      rw [hsize]; simp [Leaf.leafVerifier, Leaf.leafSize, hn]
    rw [leafSnark, ByteArray.size_extract, min_self, this]
    unfold Leaf.snarkSize Leaf.off₃ Leaf.off₂ Leaf.off₁ Ligero.size2
    omega
  exact runLog_chain ev hb (Nat.one_le_iff_ne_zero.mpr hn) hcap hsz hrun

/-- **`final` for the leaf branch, closed** (§9.3): if `μ L < 1` and the entry's `leafProg`
accepts on `L`, the parsed statement is true. -/
theorem mu_final_leaf_closed (ev : Leaf.EvalsFor) {L : Log} {c : Digest} {π : Proof}
    (hμ : μ ev L < 1) (hacc : (leafProg (Leaf.leafVerifier ev) c π).runLog L = some true) :
    leafN π ≤ chainCap ∧ c = leafStmt (leafH π) (leafN π) ∧
      chainEnd (leafS π) (leafN π) = leafH π :=
  SoundnessFinal.mu_final_leaf (Leaf.leafVerifier ev) ev hμ hacc (hchain_of_leafProg ev hacc)

end SpartanChain.SoundnessChain
