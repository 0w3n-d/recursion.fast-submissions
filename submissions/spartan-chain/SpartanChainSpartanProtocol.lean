import SpartanChainTranscript
import SpartanChainSoundnessSpartan
import SpartanChainRingSwitchField
import SpartanChainLigero

/-!
# The algebraic protocol layer: Spartan, slices, ring switching (blueprint §3, §4, §6.2 steps 5–10,
§7 fields 3–7, §8)

The layer runs between the PCS's first phase (§6.2 steps 1–4: the state after `absorb(ū)`) and its
second (steps 11–13). Sizes: `ℓ_x = ℓ_y = ly κ = 6 + (8 + κ) + 1` (`= 15 + κ`), `ℓ_q = lq κ = 8 + κ`
variables of the packed witness, `ℓ_u = lu κ = 6 + ℓ_q`.

* **Messages** (`Msgs`): the outer round polynomials (4 coefficients each), `v_A, v_B, v_C`, the
  inner round polynomials (3), the 64 slices, the ring-switching round polynomials (3). Bytes
  (`encodeMsgs`, `parseMsgs`): every `EF` element as its 24 bytes (`EF.toBytes`), fields in order,
  no padding (§7 fields 3–7); `parseMsgs_encodeMsgs` is the round trip.
* **Verifier** (`verify`): replays the transcript (squeeze `τ`; per round absorb `g_l` then squeeze;
  absorb `v_A ‖ v_B ‖ v_C`, squeeze `ρ`; inner rounds; absorb the slices, squeeze `f_0 … f_5`;
  ring-switching rounds), then `check`: the three sumchecks (`verifyRounds`), the outer final
  check `eq(τ, r_x)·(v_A v_B + v_C)`, the inner final check `M̃_ρ(r_x, r_y)·z̃_V` with
  `z̃_V = (1 + r_top)·Σ_i eq(r_lo, i) s_i + r_top·p̃ub(r_u)` (`Ã, B̃, C̃` and `p̃ub` from the
  argument `Evals`, which `Chain.lean` supplies), and `T = Σ_i x^i Φ(s_i)` as the ring-switching
  claim. Output: the final state and the **PCS claim** `(r'', W̃(r''), c)`, meaning
  `q̃(r'') · W̃(r'') = c` (checked by the PCS against `v' = Σ_j b_j v_j`, no division).
* **Prover** (`prove`): the same transcript, the honest round polynomials (`proveRounds`, with the
  tables bound after each challenge), `v_M` as the bound tables' entries, the slices
  `s_i = Q̃_i(r_hi)` (one `eq` table, 64 strided dot products), the weight table
  `W = Φ(eq(r_hi, ·))`.
* **Completeness** (`complete`): for every oracle, the verifier run on the honest messages accepts,
  ends in the prover's final state, and hands on a true PCS claim
  `c = W̃(r'') · q̃(r'')` (L-S4 three times, L-R3, L-R4).
-/

namespace SpartanChain

namespace Spartan

open RecursionFast Transcript Finset

/-! ## Sizes, messages and bytes -/

/-- Variables of the packed witness: `8 + κ`. -/
def lq (κ : ℕ) : ℕ := 8 + κ

/-- Variables of `w`: `6 + ℓ_q`. -/
def lu (κ : ℕ) : ℕ := 6 + lq κ

/-- Variables of `z = (w ‖ pub)` and rows: `ℓ_u + 1 = 15 + κ`. -/
def ly (κ : ℕ) : ℕ := lu κ + 1

/-- The algebraic messages, §7 fields 3–7. -/
structure Msgs where
  outer : List (Array EF)
  vA : EF
  vB : EF
  vC : EF
  inner : List (Array EF)
  slices : Array EF
  ring : List (Array EF)

/-- The sizes of §7: `ℓ_y` outer polynomials of 4 coefficients, `ℓ_y` inner and `ℓ_q`
ring-switching polynomials of 3, 64 slices. -/
def Msgs.WellSized (κ : ℕ) (m : Msgs) : Prop :=
  m.outer.length = ly κ ∧ (∀ g ∈ m.outer, g.size = 4) ∧ m.inner.length = ly κ ∧
    (∀ g ∈ m.inner, g.size = 3) ∧ m.slices.size = 64 ∧ m.ring.length = lq κ ∧
    ∀ g ∈ m.ring, g.size = 3

/-- The messages as one list of field elements, in §7's order. -/
def Msgs.flat (m : Msgs) : List EF :=
  m.outer.flatMap Array.toList ++ ([m.vA, m.vB, m.vC] ++ (m.inner.flatMap Array.toList ++
    (m.slices.toList ++ m.ring.flatMap Array.toList)))

/-- Number of field elements of the messages. -/
def nElems (κ : ℕ) : ℕ := 4 * ly κ + 3 + 3 * ly κ + 64 + 3 * lq κ

/-- Bytes of §7 fields 3–7: `96 ℓ_x + 72 + 72 ℓ_y + 1536 + 72 (8 + κ)`. -/
def msgsBytes (κ : ℕ) : ℕ := 24 * nElems κ

/-- The bytes of the messages. -/
def encodeMsgs (m : Msgs) : ByteArray := Ligero.efBytes m.flat.toArray

/-- `c` chunks of `k` elements. -/
def chunks {α : Type} (k : ℕ) : ℕ → List α → List (Array α)
  | 0, _ => []
  | c + 1, l => (l.take k).toArray :: chunks k c (l.drop k)

/-- The messages from their list of field elements. -/
def split (κ : ℕ) (l : List EF) : Msgs :=
  let l₁ := l.drop (4 * ly κ)
  let l₂ := l₁.drop 3
  let l₃ := l₂.drop (3 * ly κ)
  { outer := chunks 4 (ly κ) l
    vA := l₁.getD 0 0, vB := l₁.getD 1 0, vC := l₁.getD 2 0
    inner := chunks 3 (ly κ) l₂
    slices := (l₃.take 64).toArray
    ring := chunks 3 (lq κ) (l₃.drop 64) }

/-- The messages read at byte offset `off` (total: every byte string parses; the size is checked
by the caller). -/
def parseMsgs (κ : ℕ) (b : ByteArray) (off : ℕ) : Msgs :=
  split κ (Ligero.readEFs b off (nElems κ)).toList

/-! ## Transcript loops -/

/-- The verifier's rounds: absorb each polynomial (kind `kind`), squeeze a challenge. -/
def absorbRounds (kind : UInt8) : Digest → List (Array EF) → OProg (Digest × List EF)
  | st, [] => pure (st, [])
  | st, g :: gs => do
    let st ← absorb st kind (Ligero.efBytes g)
    let a ← squeeze st
    let r ← absorbRounds kind a gs
    pure (r.1, chE a :: r.2)

/-- The prover's rounds: the honest polynomial, absorbed; the challenge; the tables bound.
Returns the final state, the polynomials, the challenges and the bound tables. -/
def proveRounds (e : Expr) (kind : UInt8) :
    Digest → Array (Array EF) → ℕ → OProg (Digest × List (Array EF) × List EF × Array (Array EF))
  | st, ts, 0 => pure (st, [], [], ts)
  | st, ts, n + 1 => do
    let g := roundPoly e ts (2 ^ n)
    let st ← absorb st kind (Ligero.efBytes g)
    let a ← squeeze st
    let r ← proveRounds e kind a (ts.map (bind0 · (chE a))) n
    pure (r.1, g :: r.2.1, chE a :: r.2.2.1, r.2.2.2)

/-! ## The verifier -/

/-- What `Chain.lean` supplies: `(Ã, B̃, C̃)(r_x, r_y)` and `p̃ub(r_u)`. -/
structure Evals where
  mats : List EF → List EF → EF × EF × EF
  pub : List EF → EF

/-- The claim handed to the PCS: `q̃(point) · weight = value`. -/
structure PcsClaim where
  point : List EF
  weight : EF
  value : EF

/-- The generator `x ∈ F` in `EF`. -/
def xE : EF := algebraMap F EF F.x

/-- `z̃_V(r_y)` from the slices: `(1 + r_top)·Σ_i eq(r_lo, i) s_i + r_top·p̃ub(r_u)` (check (d) of
§9.2, literally). -/
def zV (κ : ℕ) (ev : Evals) (slices : Array EF) (ry : List EF) : EF :=
  let ru := ry.take (lu κ)
  let rtop := ry.getD (lu κ) 0
  (1 + rtop) * dot (eqTable (ru.take 6)) slices + rtop * ev.pub ru

/-- The checks after the transcript, given the challenges. -/
def check (κ : ℕ) (ev : Evals) (m : Msgs) (τ rx : List EF) (ρ : EF) (ry fs rr : List EF) :
    Option PcsClaim :=
  if m.outer.length = ly κ ∧ m.inner.length = ly κ ∧ m.slices.size = 64 ∧
      m.ring.length = lq κ then
    match verifyRounds 3 0 (m.outer.zip rx),
      verifyRounds 2 (m.vA + ρ * m.vB + ρ ^ 2 * m.vC) (m.inner.zip ry),
      verifyRounds 2 (target xE fs m.slices) (m.ring.zip rr) with
    | some c₁, some c₂, some c₃ =>
      let M := ev.mats rx ry
      if c₁ = eqPts τ rx * (m.vA * m.vB + m.vC) ∧
          c₂ = (M.1 + ρ * M.2.1 + ρ ^ 2 * M.2.2) * zV κ ev m.slices ry then
        some ⟨rr, weightEval fs (((ry.take (lu κ)).drop 6)) rr, c₃⟩
      else none
    | _, _, _ => none
  else none

/-- **The verifier of the algebraic layer** (§6.2 steps 5–10), from the state after `absorb(ū)`:
the final state and the PCS claim, or `none`. -/
def verify (κ : ℕ) (ev : Evals) (m : Msgs) (st : Digest) :
    OProg (Option (Digest × PcsClaim)) := do
  let p₁ ← squeezeE st (ly κ)
  let p₂ ← absorbRounds 0x03 p₁.1 m.outer
  let st₃ ← absorb p₂.1 0x04 (Ligero.efBytes #[m.vA, m.vB, m.vC])
  let a ← squeeze st₃
  let p₄ ← absorbRounds 0x05 a m.inner
  let st₅ ← absorb p₄.1 0x06 (Ligero.efBytes m.slices)
  let p₆ ← squeezeE st₅ 6
  let p₇ ← absorbRounds 0x07 p₆.1 m.ring
  pure ((check κ ev m p₁.2 p₂.2 (chE a) p₄.2 p₆.2 p₇.2).map fun c ↦ (p₇.1, c))

/-! ## The prover -/

/-- The prover's tables. -/
structure Witness where
  /-- `Az, Bz, Cz` on the `2^ℓ_x` rows. -/
  az : Array EF
  bz : Array EF
  cz : Array EF
  /-- `z = (w ‖ pub)`, Boolean, `2^ℓ_y` entries. -/
  z : Array F
  /-- The packed witness, `2^ℓ_q` entries: `q(u') = Σ_i z(i + 64 u') x^i`. -/
  q : Array F
  /-- The table of `M̃_ρ(r_x, ·) = Ã + ρ B̃ + ρ² C̃` on the cube (from the sparse matrices). -/
  innerTab : List EF → EF → Array EF

/-- The slices `s_i = Q̃_i(r_hi) = Σ_{u'} eq(r_hi, u') z(i + 64 u')`, `i < 64`. -/
def sliceVals (zE : Array EF) (rhi : List EF) : Array EF :=
  let e := eqTable rhi
  Array.ofFn (n := 2 ^ 6) fun i ↦ sumTo e.size fun u ↦ e.getD u 0 * zE.getD (2 ^ 6 * u + i) 0

/-- **The honest prover of the algebraic layer**: the final state, the messages and the PCS point
`r''`. -/
def prove (κ : ℕ) (w : Witness) (st : Digest) : OProg (Digest × Msgs × List EF) := do
  let p₁ ← squeezeE st (ly κ)
  let p₂ ← proveRounds outerExpr 0x03 p₁.1 #[eqTable p₁.2, w.az, w.bz, w.cz] (ly κ)
  let ts := p₂.2.2.2
  let vA := (ts.getD 1 #[]).getD 0 0
  let vB := (ts.getD 2 #[]).getD 0 0
  let vC := (ts.getD 3 #[]).getD 0 0
  let st₃ ← absorb p₂.1 0x04 (Ligero.efBytes #[vA, vB, vC])
  let a ← squeeze st₃
  let zE := w.z.map (algebraMap F EF)
  let p₄ ← proveRounds innerExpr 0x05 a #[w.innerTab p₂.2.2.1 (chE a), zE] (ly κ)
  let rhi := (p₄.2.2.1.take (lu κ)).drop 6
  let slices := sliceVals zE rhi
  let st₅ ← absorb p₄.1 0x06 (Ligero.efBytes slices)
  let p₆ ← squeezeE st₅ 6
  let p₇ ← proveRounds innerExpr 0x07 p₆.1
    #[weightTable p₆.2 rhi, w.q.map (algebraMap F EF)] (lq κ)
  pure (p₇.1, ⟨p₂.2.1, vA, vB, vC, p₄.2.1, slices, p₇.2.1⟩, p₇.2.2.1)


/-! ## Lemmas: the loops -/

section Loops

variable (H : ByteArray → Digest)

/-- **The two loops agree.** The verifier absorbing the prover's polynomials gets the prover's
states and challenges; the polynomials are the honest ones for those challenges (`honest`), one
per round, and the prover's final tables are the tables bound at them. -/
theorem run_proveRounds (e : Expr) (kind : UInt8) (n : ℕ) (st : Digest) (ts : Array (Array EF)) :
    (absorbRounds kind st ((proveRounds e kind st ts n).run H).2.1).run H =
        (((proveRounds e kind st ts n).run H).1, ((proveRounds e kind st ts n).run H).2.2.1) ∧
      ((proveRounds e kind st ts n).run H).2.1 =
        honest e ts ((proveRounds e kind st ts n).run H).2.2.1 ∧
      ((proveRounds e kind st ts n).run H).2.2.1.length = n ∧
      ((proveRounds e kind st ts n).run H).2.2.2 =
        bindAll ts ((proveRounds e kind st ts n).run H).2.2.1 := by
  induction n generalizing st ts with
  | zero => simp [proveRounds, absorbRounds, honest, bindAll]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ :=
      ih (H (squeezeQ (H (absorbQ st kind (Ligero.efBytes (roundPoly e ts (2 ^ n)))))))
        (ts.map (bind0 · (chE (H (squeezeQ (H (absorbQ st kind
          (Ligero.efBytes (roundPoly e ts (2 ^ n))))))))))
    simp only [proveRounds, absorb, squeeze, OProg.run_bind, OProg.run_ask, OProg.run_pure,
      absorbRounds] at h1 h2 h3 h4 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1]
    · rw [honest, ← h2, h3]
    · rw [List.length_cons, h3]
    · rw [bindAll, h4]

theorem proveRounds_sizes (e : Expr) (kind : UInt8) (n : ℕ) (st : Digest)
    (ts : Array (Array EF)) :
    ∀ g ∈ ((proveRounds e kind st ts n).run H).2.1, g.size = e.deg + 1 := by
  induction n generalizing st ts with
  | zero => simp [proveRounds]
  | succ n ih =>
    simp only [proveRounds, absorb, squeeze, OProg.run_bind, OProg.run_ask, OProg.run_pure,
      List.mem_cons, forall_eq_or_imp]
    exact ⟨(roundPoly_spec e ts _ 0).2, ih _ _⟩

end Loops

/-! ## Lemmas: tables, points, slices -/

/-- The true sum depends on the tables only through their views. -/
theorem trueSum_congr {e : Expr} {ts ts' : Array (Array EF)} {m : ℕ}
    (h : ∀ i, tbl m (ts.getD i #[]) = tbl m (ts'.getD i #[])) :
    trueSum e ts m = trueSum e ts' m := by
  simp only [trueSum, h]

/-- After every variable is bound, entry `0` of table `i` is its extension at the challenges. -/
theorem bindAll_entry (rs : List EF) (ts : Array (Array EF))
    (hts : ∀ t ∈ ts, t.size = 2 ^ rs.length) (i : ℕ) :
    ((bindAll ts rs).getD i #[]).getD 0 0 = mle (tbl rs.length (ts.getD i #[])) (pt rs) := by
  have := trueSum_bindAll (.var i) rs ts hts
  rw [trueSum, sum_cube_zero] at this
  exact this

theorem ptOf_append {a b : ℕ} (l₁ l₂ : List EF) (h₁ : l₁.length = a) :
    ptOf (a + b) (l₁ ++ l₂) = Fin.append (ptOf a l₁) (ptOf b l₂) := by
  funext l
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) l
  · simp [ptOf, Fin.append_left, List.getElem?_append_left (by omega : i.val < l₁.length)]
  · simp [ptOf, Fin.append_right, List.getElem?_append_right (by omega : l₁.length ≤ a + i.val),
      h₁]

/-- The slices are the extensions of the bit-planes `u' ↦ z(i + 64 u')` at `r_hi`. -/
theorem sliceVals_getD (zE : Array EF) (rhi : List EF) {ℓ : ℕ} (hr : rhi.length = ℓ)
    (i : Fin (2 ^ 6)) :
    (sliceVals zE rhi).getD i 0 =
      mle (fun u' : Fin (2 ^ ℓ) ↦ zE.getD (2 ^ 6 * u'.val + i) 0) (ptOf ℓ rhi) := by
  rw [sliceVals, getD_ofFn, dite_eq_left i.isLt, eqTable_size, hr, sumTo_eq_fin, mle]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← congrFun (tbl_eqTable' rhi hr) u]
  rfl

/-- `dot (eqTable r_lo) s = Σ_i eq(r_lo, i) s_i` over the `2^6` indices. -/
theorem dot_eqTable (rlo : List EF) (hr : rlo.length = 6) (s : Array EF) :
    dot (eqTable rlo) s = ∑ i : Fin (2 ^ 6), eq (ptOf 6 rlo) (cube i) * s.getD i 0 := by
  rw [dot, eqTable_size, hr, sumTo_eq_fin]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← congrFun (tbl_eqTable' rlo hr) u]
  rfl

theorem honest_length (e : Expr) (ts : Array (Array EF)) (rs : List EF) :
    (honest e ts rs).length = rs.length := by
  induction rs generalizing ts with
  | nil => rfl
  | cons r rs ih => simp [honest, ih]

/-- An extension at a list point of a known length. -/
theorem mle_len (t : Array EF) (r : List EF) {n : ℕ} (h : r.length = n) :
    mle (tbl r.length t) (pt r) = mle (tbl n t) (ptOf n r) := by
  subst h
  rw [pt_eq_ptOf]

theorem getD_map_alg (z : Array F) (j : ℕ) :
    (z.map (algebraMap F EF)).getD j 0 = algebraMap F EF (z.getD j 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases z[j]? <;> simp

/-! ## Lemmas: bytes -/

theorem array_getD_toList {α : Type} (a : Array α) (k : ℕ) (d : α) :
    a.getD k d = a.toList.getD k d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem flatMap_getD (xs : List EF) {j i : ℕ} (hj : j < xs.length) (hi : i < 24) :
    (xs.flatMap fun x ↦ (EF.toBytes x).toList).getD (24 * j + i) 0 = (EF.toBytes xs[j])[i] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
        List.getD_append _ _ _ _ (by rw [Vector.length_toList]; exact hi),
        List.getD_eq_getElem _ _ (by rw [Vector.length_toList]; exact hi), Vector.getElem_toList]
      rfl
    | succ j =>
      rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [Vector.length_toList]; omega),
        Vector.length_toList, show 24 * (j + 1) + i - 24 = 24 * j + i by omega]
      exact ih (Nat.lt_of_succ_lt_succ hj)

theorem flatMap_length (xs : List EF) :
    (xs.flatMap fun x ↦ (EF.toBytes x).toList).length = 24 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, List.length_append, ih, Vector.length_toList,
      List.length_cons]; ring

theorem efBytes_toList (xs : Array EF) :
    (Ligero.efBytes xs).data.toList = xs.toList.flatMap fun x ↦ (EF.toBytes x).toList := by
  rw [Ligero.efBytes_data]
  rfl

theorem efBytes_size (xs : Array EF) : (Ligero.efBytes xs).size = 24 * xs.size := by
  change (Ligero.efBytes xs).data.toList.length = _
  rw [efBytes_toList, flatMap_length, Array.length_toList]

/-- **Round trip of the field elements**: read back at their offset inside any byte string. -/
theorem readEFs_append (pre post : ByteArray) (xs : Array EF) :
    Ligero.readEFs (pre ++ Ligero.efBytes xs ++ post) pre.size xs.size = xs := by
  refine Array.ext (by simp [Ligero.readEFs]) fun j _ hj ↦ ?_
  rw [Ligero.readEFs_getElem]
  have hp : pre.data.toList.length = pre.size := by rw [Array.length_toList]; rfl
  have hv : (Vector.ofFn fun i : Fin 24 ↦
      (pre ++ Ligero.efBytes xs ++ post)[pre.size + 24 * j + i]!) = EF.toBytes xs[j] := by
    refine Vector.ext fun i hi ↦ ?_
    rw [Vector.getElem_ofFn, Ligero.getElem!_ba, ByteArray.data_append, ByteArray.data_append,
      Array.toList_append, Array.toList_append, List.append_assoc,
      List.getD_append_right _ _ _ _ (by rw [hp]; omega), hp,
      show pre.size + 24 * j + i - pre.size = 24 * j + i by omega, efBytes_toList,
      List.getD_append _ _ _ _ (by rw [flatMap_length, Array.length_toList]; nlinarith)]
    rw [flatMap_getD xs.toList (by simpa using hj) hi, Array.getElem_toList]
  rw [Ligero.readEF, hv, EF.ofBytes_toBytes]

theorem chunks_flat {α : Type} (k : ℕ) (gs : List (Array α)) (hk : ∀ g ∈ gs, g.size = k)
    (rest : List α) :
    chunks k gs.length (gs.flatMap Array.toList ++ rest) = gs ∧
      (gs.flatMap Array.toList ++ rest).drop (k * gs.length) = rest := by
  induction gs with
  | nil => simp [chunks]
  | cons g gs ih =>
    have hg : g.toList.length = k := by rw [Array.length_toList, hk g (by simp)]
    obtain ⟨ih₁, ih₂⟩ := ih fun g' hg' ↦ hk g' (by simp [hg'])
    rw [List.flatMap_cons, List.append_assoc, List.length_cons]
    refine ⟨?_, ?_⟩
    · rw [chunks, List.take_left' hg, List.drop_left' hg, ih₁, Array.toArray_toList]
    · rw [Nat.mul_succ, add_comm, ← List.drop_drop, List.drop_left' hg, ih₂]

theorem length_flat {α : Type} (k : ℕ) (gs : List (Array α)) (hk : ∀ g ∈ gs, g.size = k) :
    (gs.flatMap Array.toList).length = k * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.flatMap_cons, List.length_append, ih fun g' hg' ↦ hk g' (by simp [hg']),
      Array.length_toList, hk g (by simp), List.length_cons, Nat.mul_succ, add_comm]

/-- `split` inverts `flat` on well-sized messages. -/
theorem split_flat (κ : ℕ) (m : Msgs) (hm : m.WellSized κ) : split κ m.flat = m := by
  obtain ⟨ho, hos, hi, his, hs, hr, hrs⟩ := hm
  have o := chunks_flat 4 m.outer hos ([m.vA, m.vB, m.vC] ++ (m.inner.flatMap Array.toList ++
    (m.slices.toList ++ m.ring.flatMap Array.toList)))
  have i := chunks_flat 3 m.inner his (m.slices.toList ++ m.ring.flatMap Array.toList)
  have r := chunks_flat 3 m.ring hrs []
  rw [ho] at o
  rw [hi] at i
  rw [hr, List.append_nil] at r
  have hsl : m.slices.toList.length = 64 := by rw [Array.length_toList, hs]
  have hl₂ : ∀ X : List EF, ([m.vA, m.vB, m.vC] ++ X).drop 3 = X := fun _ ↦ rfl
  have g₀ : ∀ X : List EF, ([m.vA, m.vB, m.vC] ++ X).getD 0 0 = m.vA := fun _ ↦ rfl
  have g₁ : ∀ X : List EF, ([m.vA, m.vB, m.vC] ++ X).getD 1 0 = m.vB := fun _ ↦ rfl
  have g₂ : ∀ X : List EF, ([m.vA, m.vB, m.vC] ++ X).getD 2 0 = m.vC := fun _ ↦ rfl
  simp only [split, Msgs.flat, o.1, o.2, hl₂, g₀, g₁, g₂, i.1, i.2, List.drop_left' hsl,
    List.take_left' hsl, r.1, Array.toArray_toList]

theorem flat_length (κ : ℕ) (m : Msgs) (hm : m.WellSized κ) : m.flat.length = nElems κ := by
  obtain ⟨ho, hos, hi, his, hs, hr, hrs⟩ := hm
  simp only [Msgs.flat, List.length_append, length_flat 4 _ hos, length_flat 3 _ his,
    length_flat 3 _ hrs, ho, hi, hr, Array.length_toList, hs, nElems]
  simp
  ring

/-- **Byte round trip** (§7 fields 3–7): well-sized messages are read back from their bytes at
their offset inside the proof. -/
theorem parseMsgs_encodeMsgs (κ : ℕ) (m : Msgs) (hm : m.WellSized κ) (pre post : ByteArray) :
    parseMsgs κ (pre ++ encodeMsgs m ++ post) pre.size = m := by
  have h := readEFs_append pre post m.flat.toArray
  rw [List.size_toArray, flat_length κ m hm] at h
  rw [parseMsgs, encodeMsgs, h, List.toList_toArray, split_flat κ m hm]

theorem encodeMsgs_size (κ : ℕ) (m : Msgs) (hm : m.WellSized κ) :
    (encodeMsgs m).size = msgsBytes κ := by
  rw [encodeMsgs, efBytes_size, List.size_toArray, flat_length κ m hm, msgsBytes]

/-! ## Completeness -/

/-- The extended witness on the cube, in `EF`. -/
def zT (κ : ℕ) (w : Witness) : Fin (2 ^ ly κ) → EF := tbl (ly κ) (w.z.map (algebraMap F EF))

/-- The prover's tables are honest for the R1CS `A, B, C` (matrices on the cube of `ℓ_y`
variables, the matrices of `Chain.lean`) and the evaluators compute its extensions. -/
structure Honest (κ : ℕ) (w : Witness) (ev : Evals)
    (A B C : Fin (2 ^ ly κ) → Fin (2 ^ ly κ) → EF) : Prop where
  z_size : w.z.size = 2 ^ ly κ
  z_bool : ∀ j, w.z.getD j 0 = 0 ∨ w.z.getD j 0 = 1
  az : w.az.size = 2 ^ ly κ ∧ tbl (ly κ) w.az = matVec A (zT κ w)
  bz : w.bz.size = 2 ^ ly κ ∧ tbl (ly κ) w.bz = matVec B (zT κ w)
  cz : w.cz.size = 2 ^ ly κ ∧ tbl (ly κ) w.cz = matVec C (zT κ w)
  sat : Sat A B C (zT κ w)
  inner : ∀ rx ρ, rx.length = ly κ → (w.innerTab rx ρ).size = 2 ^ ly κ ∧
    tbl (ly κ) (w.innerTab rx ρ) = fun y ↦ matMle A (ptOf _ rx) (cube y) +
      ρ * matMle B (ptOf _ rx) (cube y) + ρ ^ 2 * matMle C (ptOf _ rx) (cube y)
  mats : ∀ rx ry, rx.length = ly κ → ry.length = ly κ → ev.mats rx ry =
    (matMle A (ptOf _ rx) (ptOf _ ry), matMle B (ptOf _ rx) (ptOf _ ry),
      matMle C (ptOf _ rx) (ptOf _ ry))
  pub : ∀ ru, ru.length = lu κ →
    ev.pub ru = mle (fun u ↦ zT κ w (join u (1 : Fin (2 ^ 1)))) (ptOf (lu κ) ru)
  q_size : w.q.size = 2 ^ lq κ
  q_pack : ∀ u : Fin (2 ^ lq κ),
    w.q.getD u 0 = ∑ i : Fin (2 ^ 6), w.z.getD (2 ^ 6 * u.val + i) 0 * F.x ^ (i : ℕ)

section Facts

variable {κ : ℕ} {w : Witness} {ev : Evals} {A B C : Fin (2 ^ ly κ) → Fin (2 ^ ly κ) → EF}

/-- The outer claim `0` is true: `Σ_x eq(τ, x) F(x) = 0` when the R1CS holds. -/
theorem outer_claim (h : Honest κ w ev A B C) (τ : List EF) (hτ : τ.length = ly κ) :
    trueSum outerExpr #[eqTable τ, w.az, w.bz, w.cz] (ly κ) = 0 := by
  rw [trueSum_congr (ts' := outerTables τ A B C (zT κ w)) ?_, outer_trueSum τ hτ]
  · have hr : residual A B C (zT κ w) = 0 := funext fun x ↦ by
      simp only [residual, Pi.zero_apply, h.sat x, CharTwo.add_self_eq_zero]
    simp [hr, mle]
  · intro i
    rcases i with _ | _ | _ | _ | i
    · rfl
    · simp [outerTables, tbl_ofFn, h.az.2]
    · simp [outerTables, tbl_ofFn, h.bz.2]
    · simp [outerTables, tbl_ofFn, h.cz.2]
    · simp [outerTables]

/-- The inner claim is true when `v_A, v_B, v_C` are honest. -/
theorem inner_claim (h : Honest κ w ev A B C) (rx : List EF) (hx : rx.length = ly κ) (ρ : EF) :
    mle (tbl (ly κ) w.az) (ptOf _ rx) + ρ * mle (tbl (ly κ) w.bz) (ptOf _ rx) +
        ρ ^ 2 * mle (tbl (ly κ) w.cz) (ptOf _ rx) =
      trueSum innerExpr #[w.innerTab rx ρ, w.z.map (algebraMap F EF)] (ly κ) := by
  rw [trueSum_congr (ts' := innerTables (ptOf _ rx) ρ A B C (zT κ w)) ?_, inner_trueSum, h.az.2,
    h.bz.2, h.cz.2]
  intro i
  rcases i with _ | _ | i
  · simp [innerTables, tbl_ofFn, (h.inner rx ρ hx).2]
  · simp [innerTables, tbl_ofFn, zT]
  · simp [innerTables]

/-- **The verifier's `z̃_V` from honest slices is `z̃(r_y)`.** -/
theorem zV_eq (h : Honest κ w ev A B C) (ry : List EF) (hy : ry.length = ly κ) :
    zV κ ev (sliceVals (w.z.map (algebraMap F EF)) ((ry.take (lu κ)).drop 6)) ry =
      mle (zT κ w) (ptOf (ly κ) ry) := by
  obtain ⟨ru, rtop, rfl, hu⟩ : ∃ ru rtop, ry = ru ++ [rtop] ∧ ru.length = lu κ := by
    have hne : ry ≠ [] := fun he ↦ by simp [he, ly] at hy
    exact ⟨ry.dropLast, ry.getLast hne, (List.dropLast_append_getLast hne).symm,
      by simp [hy, ly]⟩
  obtain ⟨rlo, rhi, rfl, hlo⟩ : ∃ a b, ru = a ++ b ∧ a.length = 6 :=
    ⟨ru.take 6, ru.drop 6, (List.take_append_drop _ _).symm, by simp [hu, lu]⟩
  have hhi : rhi.length = lq κ := by simp [lu] at hu; omega
  have htake : (rlo ++ rhi ++ [rtop]).take (lu κ) = rlo ++ rhi := List.take_left' hu
  have htop : (rlo ++ rhi ++ [rtop]).getD (lu κ) 0 = rtop := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hu]
  have hpt : ptOf (ly κ) (rlo ++ rhi ++ [rtop]) =
      Fin.append (Fin.append (ptOf 6 rlo) (ptOf (lq κ) rhi)) fun _ ↦ rtop := by
    change ptOf (6 + lq κ + 1) _ = _
    rw [ptOf_append _ _ (by simp [hlo, hhi]), ptOf_append _ _ hlo]
    congr 1
    funext l
    simp [ptOf, Fin.fin_one_eq_zero l]
  rw [zV, htake, htop, List.take_left' hlo, List.drop_left' hlo, hpt]
  have hz := z_mle_slices (lo := 6) (hi := lq κ) (fun u ↦ zT κ w (join u 0))
    (fun u ↦ zT κ w (join u 1)) (zT κ w)
    (fun u c ↦ by rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl <;> rfl)
    (ptOf 6 rlo) (ptOf (lq κ) rhi) rtop
  refine Eq.trans ?_ hz.symm
  rw [show (1 : EF) + rtop = 1 - rtop from (CharTwo.sub_eq_add 1 rtop).symm]
  rw [h.pub _ hu, ← ptOf_append _ _ hlo, dot_eqTable _ hlo]
  have hs : ∀ i : Fin (2 ^ 6), (sliceVals (w.z.map (algebraMap F EF)) rhi).getD i 0 =
      mle (fun u' ↦ zT κ w (join (join i u') 0)) (ptOf (lq κ) rhi) := fun i ↦ by
    rw [sliceVals_getD _ _ hhi]
    congr 1
    funext u
    simp [zT, tbl, join]
  simp only [hs]
  rfl

theorem sliceVals_size (zE : Array EF) (rhi : List EF) : (sliceVals zE rhi).size = 2 ^ 6 :=
  Array.size_ofFn

/-- **The ring-switching claim `T` is true for honest slices** (L-R3). -/
theorem ring_claim (h : Honest κ w ev A B C) (fs rhi : List EF) (hr : rhi.length = lq κ) :
    target xE fs (sliceVals (w.z.map (algebraMap F EF)) rhi) =
      trueSum innerExpr #[weightTable fs rhi, w.q.map (algebraMap F EF)] (lq κ) := by
  let Q : Fin (2 ^ 6) → Fin (2 ^ lq κ) → F := fun i u ↦ w.z.getD (2 ^ 6 * u.val + i) 0
  have hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1 := fun i u ↦ h.z_bool _
  rw [trueSum_congr (ts' := #[Array.ofFn fun u ↦ Phi fs (eq (ptOf (lq κ) rhi) (cube u)),
      Array.ofFn fun u ↦ algebraMap F EF (∑ i : Fin (2 ^ 6), Q i u * F.x ^ (i : ℕ))]) ?_,
    prod_trueSum]
  · refine Eq.trans ?_
      (ring_complete (frobMapHom (stages (fs.length - 1) fs)) F.x Q hQ (ptOf (lq κ) rhi)).symm
    rw [target_eq, sliceVals_size, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [xE, ← map_pow, sliceVals_getD _ _ hr]
    simp only [getD_map_alg]
    rfl
  · intro i
    rcases i with _ | _ | i
    · funext u
      have hu : u.val < (eqTable rhi).size := by rw [eqTable_size, hr]; exact u.isLt
      have he := congrFun (tbl_eqTable' rhi hr) u
      simp only [tbl] at he
      simp [tbl, weightTable, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem hu, ← phiApply_eq] at he ⊢
      rw [← he]
    · funext u
      change tbl (lq κ) (w.q.map (algebraMap F EF)) u = tbl (lq κ) (Array.ofFn _) u
      rw [tbl_ofFn]
      simp only [tbl]
      rw [getD_map_alg, h.q_pack]
    · simp

/-- The honest messages for given challenges. -/
def honestMsgs (κ : ℕ) (w : Witness) (τ rx : List EF) (ρ : EF) (ry fs rr : List EF) : Msgs :=
  let ts₀ : Array (Array EF) := #[eqTable τ, w.az, w.bz, w.cz]
  let tb := bindAll ts₀ rx
  let zE := w.z.map (algebraMap F EF)
  let rhi := (ry.take (lu κ)).drop 6
  ⟨honest outerExpr ts₀ rx, (tb.getD 1 #[]).getD 0 0, (tb.getD 2 #[]).getD 0 0,
    (tb.getD 3 #[]).getD 0 0, honest innerExpr #[w.innerTab rx ρ, zE] ry, sliceVals zE rhi,
    honest innerExpr #[weightTable fs rhi, w.q.map (algebraMap F EF)] rr⟩

/-- **The checks pass on honest messages, for every challenge**, and the PCS claim is true:
`c = W̃(r'') · q̃(r'')`. -/
theorem check_honest (h : Honest κ w ev A B C) (τ rx : List EF) (ρ : EF) (ry fs rr : List EF)
    (hτ : τ.length = ly κ) (hx : rx.length = ly κ) (hy : ry.length = ly κ)
    (hr : rr.length = lq κ) :
    check κ ev (honestMsgs κ w τ rx ρ ry fs rr) τ rx ρ ry fs rr =
      some ⟨rr, weightEval fs ((ry.take (lu κ)).drop 6) rr,
        weightEval fs ((ry.take (lu κ)).drop 6) rr * mleEval (w.q.map (algebraMap F EF)) rr⟩ := by
  have hrhi : ((ry.take (lu κ)).drop 6).length = lq κ := by simp [hy, lu, ly]
  have hs₀ : ∀ t ∈ (#[eqTable τ, w.az, w.bz, w.cz] : Array (Array EF)), t.size = 2 ^ rx.length := by
    simp [eqTable_size, hτ, hx, h.az.1, h.bz.1, h.cz.1]
  have hs₁ : ∀ t ∈ (#[w.innerTab rx ρ, w.z.map (algebraMap F EF)] : Array (Array EF)),
      t.size = 2 ^ ry.length := by
    simp [(h.inner rx ρ hx).1, hy, h.z_size]
  have hs₂ : ∀ t ∈ (#[weightTable fs ((ry.take (lu κ)).drop 6), w.q.map (algebraMap F EF)] :
      Array (Array EF)), t.size = 2 ^ rr.length := by
    simp [weightTable, eqTable_size, hrhi, hr, h.q_size]
  have hv : ∀ i, ((bindAll #[eqTable τ, w.az, w.bz, w.cz] rx).getD i #[]).getD 0 0 =
      mle (tbl (ly κ) ((#[eqTable τ, w.az, w.bz, w.cz] : Array (Array EF)).getD i #[]))
        (ptOf (ly κ) rx) := fun i ↦ by
    rw [bindAll_entry rx _ hs₀, mle_len _ _ hx]
  have hvA : ((bindAll #[eqTable τ, w.az, w.bz, w.cz] rx).getD 1 #[]).getD 0 0 =
      mle (tbl (ly κ) w.az) (ptOf (ly κ) rx) := hv 1
  have hvB : ((bindAll #[eqTable τ, w.az, w.bz, w.cz] rx).getD 2 #[]).getD 0 0 =
      mle (tbl (ly κ) w.bz) (ptOf (ly κ) rx) := hv 2
  have hvC : ((bindAll #[eqTable τ, w.az, w.bz, w.cz] rx).getD 3 #[]).getD 0 0 =
      mle (tbl (ly κ) w.cz) (ptOf (ly κ) rx) := hv 3
  have e₁ := verifyRounds_honest outerExpr rx _ hs₀
  rw [hx, outer_claim h τ hτ, trueSum_bindAll _ _ _ hs₀, outerExpr_deg] at e₁
  have e₂ := verifyRounds_honest innerExpr ry _ hs₁
  rw [hy, ← inner_claim h rx hx ρ, trueSum_bindAll _ _ _ hs₁, innerExpr_deg] at e₂
  have e₃ := verifyRounds_honest innerExpr rr _ hs₂
  rw [hr, ← ring_claim h fs _ hrhi, trueSum_bindAll _ _ _ hs₂, innerExpr_deg] at e₃
  have hc₁ : Expr.eval (fun i ↦ mle (tbl rx.length
      ((#[eqTable τ, w.az, w.bz, w.cz] : Array (Array EF)).getD i #[])) (pt rx)) outerExpr =
      eqPts τ rx * (mle (tbl (ly κ) w.az) (ptOf (ly κ) rx) * mle (tbl (ly κ) w.bz) (ptOf (ly κ) rx)
        + mle (tbl (ly κ) w.cz) (ptOf (ly κ) rx)) := by
    simp only [outerExpr, Expr.eval, mle_len _ _ hx]
    rw [eqPts_eq τ rx hτ hx]
    congr 1
    change mle (tbl (ly κ) (eqTable τ)) _ = _
    rw [tbl_eqTable' τ hτ, mle_eqPt]
  have hc₂ : Expr.eval (fun i ↦ mle (tbl ry.length
      ((#[w.innerTab rx ρ, w.z.map (algebraMap F EF)] : Array (Array EF)).getD i #[])) (pt ry))
        innerExpr =
      ((ev.mats rx ry).1 + ρ * (ev.mats rx ry).2.1 + ρ ^ 2 * (ev.mats rx ry).2.2) *
        zV κ ev (sliceVals (w.z.map (algebraMap F EF)) ((ry.take (lu κ)).drop 6)) ry := by
    simp only [innerExpr, Expr.eval, mle_len _ _ hy]
    rw [zV_eq h ry hy, h.mats rx ry hx hy]
    congr 1
    change mle (tbl (ly κ) (w.innerTab rx ρ)) _ = _
    rw [(h.inner rx ρ hx).2, mle_comb, mle_matMle, mle_matMle, mle_matMle]
  have hc₃ : Expr.eval (fun i ↦ mle (tbl rr.length
      ((#[weightTable fs ((ry.take (lu κ)).drop 6), w.q.map (algebraMap F EF)] :
        Array (Array EF)).getD i #[])) (pt rr)) innerExpr =
      weightEval fs ((ry.take (lu κ)).drop 6) rr * mleEval (w.q.map (algebraMap F EF)) rr := by
    simp only [innerExpr, Expr.eval]
    rw [← mleEval_weightTable fs _ rr hrhi hr, mleEval_eq, mleEval_eq]
    rfl
  unfold check honestMsgs
  dsimp only
  rw [ite_eq_left ⟨by rw [honest_length, hx], by rw [honest_length, hy], sliceVals_size _ _,
    by rw [honest_length, hr]⟩]
  simp only [hvA, hvB, hvC]
  simp only [e₁, e₂, e₃]
  rw [ite_eq_left ⟨hc₁, hc₂⟩, hc₃]

end Facts

theorem squeezeE_length (H : ByteArray → Digest) (st : Digest) (k : ℕ) :
    ((squeezeE st k).run H).2.length = k := by
  simp [squeezeE]

/-- **Completeness of the algebraic layer** (§8): for every oracle, the verifier run on the honest
messages accepts, ends in the prover's final state, and hands on a true PCS claim
`c = W̃(r'') · q̃(r'')` at a point of `ℓ_q` coordinates. No challenge value is excluded. -/
theorem complete (H : ByteArray → Digest) {κ : ℕ} {w : Witness} {ev : Evals}
    {A B C : Fin (2 ^ ly κ) → Fin (2 ^ ly κ) → EF} (h : Honest κ w ev A B C) (st : Digest) :
    ∃ c : PcsClaim, (verify κ ev ((prove κ w st).run H).2.1 st).run H =
        some (((prove κ w st).run H).1, c) ∧ c.point = ((prove κ w st).run H).2.2 ∧
      c.point.length = lq κ ∧
      c.value = c.weight * mleEval (w.q.map (algebraMap F EF)) c.point := by
  simp only [prove, verify, OProg.run_bind, OProg.run_pure, absorb, squeeze, OProg.run_ask]
  have hτ := squeezeE_length H st (ly κ)
  generalize (squeezeE st (ly κ)).run H = p₁ at hτ ⊢
  obtain ⟨a₂, b₂, c₂, d₂⟩ :=
    run_proveRounds H outerExpr 0x03 (ly κ) p₁.1 #[eqTable p₁.2, w.az, w.bz, w.cz]
  rw [a₂]
  generalize (proveRounds outerExpr 0x03 p₁.1 #[eqTable p₁.2, w.az, w.bz, w.cz] (ly κ)).run H = R₂
    at b₂ c₂ d₂ ⊢
  generalize H (squeezeQ (H (absorbQ R₂.1 0x04 (Ligero.efBytes #[(R₂.2.2.2.getD 1 #[]).getD 0 0,
    (R₂.2.2.2.getD 2 #[]).getD 0 0, (R₂.2.2.2.getD 3 #[]).getD 0 0])))) = a
  obtain ⟨a₄, b₄, c₄, d₄⟩ := run_proveRounds H innerExpr 0x05 (ly κ) a
    #[w.innerTab R₂.2.2.1 (chE a), w.z.map (algebraMap F EF)]
  rw [a₄]
  generalize (proveRounds innerExpr 0x05 a
    #[w.innerTab R₂.2.2.1 (chE a), w.z.map (algebraMap F EF)] (ly κ)).run H = R₄ at b₄ c₄ d₄ ⊢
  generalize (squeezeE (H (absorbQ R₄.1 0x06 (Ligero.efBytes (sliceVals (w.z.map (algebraMap F EF))
    ((R₄.2.2.1.take (lu κ)).drop 6))))) 6).run H = p₆
  obtain ⟨a₇, b₇, c₇, d₇⟩ := run_proveRounds H innerExpr 0x07 (lq κ) p₆.1
    #[weightTable p₆.2 ((R₄.2.2.1.take (lu κ)).drop 6), w.q.map (algebraMap F EF)]
  rw [a₇]
  generalize (proveRounds innerExpr 0x07 p₆.1
    #[weightTable p₆.2 ((R₄.2.2.1.take (lu κ)).drop 6), w.q.map (algebraMap F EF)]
    (lq κ)).run H = R₇ at b₇ c₇ d₇ ⊢
  have hc := check_honest h p₁.2 R₂.2.2.1 (chE a) R₄.2.2.1 p₆.2 R₇.2.2.1 hτ c₂ c₄ c₇
  refine ⟨⟨R₇.2.2.1, weightEval p₆.2 ((R₄.2.2.1.take (lu κ)).drop 6) R₇.2.2.1,
    weightEval p₆.2 ((R₄.2.2.1.take (lu κ)).drop 6) R₇.2.2.1 *
      mleEval (w.q.map (algebraMap F EF)) R₇.2.2.1⟩, ?_, rfl, c₇, rfl⟩
  rw [b₂, d₂, b₄, b₇]
  exact congrArg (Option.map _) hc

/-- The honest messages are well-sized. -/
theorem prove_wellSized (H : ByteArray → Digest) (κ : ℕ) (w : Witness) (st : Digest) :
    ((prove κ w st).run H).2.1.WellSized κ := by
  simp only [prove, OProg.run_bind, OProg.run_pure, absorb, squeeze, OProg.run_ask]
  have hl : ∀ (e : Expr) (kind : UInt8) (n : ℕ) (st : Digest) (ts : Array (Array EF)),
      ((proveRounds e kind st ts n).run H).2.1.length = n := fun e kind n st ts ↦ by
    rw [(run_proveRounds H e kind n st ts).2.1, honest_length,
      (run_proveRounds H e kind n st ts).2.2.1]
  exact ⟨hl _ _ _ _ _, proveRounds_sizes H _ _ _ _ _, hl _ _ _ _ _, proveRounds_sizes H _ _ _ _ _,
    sliceVals_size _ _, hl _ _ _ _ _, proveRounds_sizes H _ _ _ _ _⟩

/-- Negative control: messages of the wrong shape (63 slices) are rejected, whatever the
challenges. -/
theorem check_wrong_size (κ : ℕ) (ev : Evals) (m : Msgs) (hs : m.slices.size = 63)
    (τ rx : List EF) (ρ : EF) (ry fs rr : List EF) : check κ ev m τ rx ρ ry fs rr = none := by
  simp [check, hs]

end Spartan

end SpartanChain
