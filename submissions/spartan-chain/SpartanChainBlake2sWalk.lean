import SpartanChainBlake2sGeneric
import SpartanChainBlake2sR1CS

/-!
# The block walk: `A0̃`, `B0̃` of the chain block in `O(|circuit|)` (L-C4, `walk_eq_sum`)

BLUEPRINT-R1 §2.4.2. For row weights `e` and column weights `wt` (in the verifier, the tables
`eq(r_k, ·)` and `eq(r_j, ·)`), the bilinear forms of the chain block's matrices,
`Σ_k e(k) · Σ_j A(k, j) · wt(j)` and the same for `B`, are computed by one forward walk of the
gadget code (`walkAB`), never from the matrices. **Row `512` is skipped** (BLUEPRINT-R1 review
BP-m5): the chain R1CS replaces the constant's row by `(pub₀, pub₀, w(t, 512))`, so the block
part `A0`, `B0` of §2.4 is the chain block with row `512` cleared.

The walk interprets the generic gadgets (`SpartanChainBlake2sGeneric.lean`) with `α = R`:
`zero = 0`, `xor = +`, `var k = wt k`, and a product gate at `k` adds `e(k) · a` and `e(k) · b` to
the two accumulators and returns `wt(k)`. The rows that are not gates of the compression are
summed directly: constant rows `e(k) · wt(512)` (bit `1`) or nothing (bit `0`), output rows
`e(k) · val(outForm)` and `e(k) · wt(512)`, input rows `e(k) · wt(k)` and `e(k) · wt(512)`.

`walk_eq_sum` is proved by the simulation of the bitset gadgets (`Generic.sim_compressW`) with
`φ L = Σ_j L_j · wt(j)`, which is linear in characteristic two, and by `sum_rows`, which splits
`Σ_k` over a bounded circuit's rows into its gates and its input rows.

Cost: about `2 · 14 720 + 2 · (640 + 256 + 256)` multiplications in `R`, independent of `n`.
-/

namespace SpartanChain

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## Rows of a bounded circuit -/

section Rows

variable {m : ℕ} {R : Type} [CommRing R]

theorem nodup_keys_of_boundedFrom {avail : Form m} {L : List (Pos m × Gate m)}
    (h : BoundedFrom avail L) : (L.map Prod.fst).Nodup := by
  induction L generalizing avail with
  | nil => exact List.nodup_nil
  | cons kg rest ih =>
    obtain ⟨k, g⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨-, -, -, hrest⟩ := h
    refine List.nodup_cons.mpr ⟨fun hm ↦ ?_, ih hrest⟩
    have := boundedFrom_fresh hrest hm
    simp [Form.var] at this

/-- A sum over the rows of a bounded circuit, the constant's row skipped, splits into its gates and
its input rows (zero rows contribute nothing). -/
theorem sum_rows {c : ProductCircuit m} (hc : c.Bounded) (hcin : c.inputs.getLsbD c.cpos = false)
    (F : Pos m → Gate m → R) (h0 : ∀ k, F k ⟨0, 0⟩ = 0) :
    (∑ k, if k = c.cpos then 0 else F k (c.rowOf k)) =
      (c.gates.toList.map fun kg ↦ F kg.1 kg.2).sum +
        ∑ k : Pos m, if c.inputs.getLsbD k then F k ⟨Form.var k, Form.var c.cpos⟩ else 0 := by
  classical
  set keys := c.gates.toList.map Prod.fst with hkeys
  have hnd : keys.Nodup := nodup_keys_of_boundedFrom hc
  have hfresh : ∀ k ∈ keys, (c.inputs ||| Form.var c.cpos).getLsbD k = false :=
    fun k hk ↦ boundedFrom_fresh hc hk
  have hterm : ∀ k : Pos m, (if k = c.cpos then 0 else F k (c.rowOf k)) =
      (if k ∈ keys.toFinset then F k (c.rowOf k) else 0) +
        (if c.inputs.getLsbD k then F k ⟨Form.var k, Form.var c.cpos⟩ else 0) := by
    intro k
    by_cases hk : k ∈ keys
    · have hf := hfresh k hk
      rw [BitVec.getLsbD_or, Bool.or_eq_false_iff] at hf
      have hkc : k ≠ c.cpos := fun h ↦ by
        have := hf.2; rw [getLsbD_var, h] at this; simp at this
      rw [ite_eq_right hkc, ite_eq_left (List.mem_toFinset.mpr hk), hf.1]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    · have hl : c.gates.toList.lookup k = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        exact hk (List.mem_map_of_mem hp)
      have hrow : c.rowOf k = c.rowOfList [] k := by simp only [rowOf, rowOfList, hl]; rfl
      rw [ite_eq_right (fun h ↦ hk (List.mem_toFinset.mp h)), zero_add]
      by_cases hkc : k = c.cpos
      · subst hkc
        rw [ite_eq_left rfl, hcin]
        simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [ite_eq_right hkc, hrow]
        unfold rowOfList
        simp only [List.lookup_nil]
        rw [ite_eq_right hkc]
        by_cases hin : c.inputs.getLsbD k = true
        · rw [ite_eq_left hin, ite_eq_left hin]
        · rw [ite_eq_right hin, ite_eq_right hin, h0]
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.univ_inter, List.sum_toFinset _ hnd, hkeys, List.map_map]
  congr 2
  refine List.map_congr_left fun kg hkg ↦ ?_
  simp only [Function.comp_apply, rowOf, rowOfList, lookup_of_mem hc hkg]

end Rows

/-! ## The walk interpretation -/

section Walk

variable {R : Type} [CommRing R]

/-- The value of a form against the column weights `wt`: `Σ_j L_j · wt(j)`. -/
def formVal {m : ℕ} (wt : Pos m → R) (L : Form m) : R :=
  ∑ j : Pos m, if L.getLsbD j then wt j else 0

/-- The walk: forms are values in `R`, a product gate at `k` adds `e(k) · a`, `e(k) · b` to the
accumulators and returns `wt(k)`. -/
def walkOps {m : ℕ} (e wt : Pos m → R) : GOps m R (R × R) where
  zero := 0
  xor := (· + ·)
  var := wt
  res k _ _ := wt k
  upd s k a b := (s.1 + e k * a, s.2 + e k * b)

theorem formVal_var {m : ℕ} (wt : Pos m → R) (k : Pos m) : formVal wt (Form.var k) = wt k := by
  simp only [formVal, getLsbD_var, Fin.val_inj, decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp

theorem formVal_zero {m : ℕ} (wt : Pos m → R) : formVal wt (0 : Form m) = 0 := by
  simp [formVal]

theorem linear_walk [CharP R 2] {m : ℕ} (e wt : Pos m → R) :
    Generic.Linear (walkOps e wt) (formVal wt) where
  zero := formVal_zero wt
  xor a b := by
    simp only [formVal, walkOps, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [BitVec.getLsbD_xor]
    cases a.getLsbD j <;> cases b.getLsbD j <;> simp [CharTwo.add_self_eq_zero]

/-- The positions and generic values of the output rows, in the order of `outRows`. -/
def outPairs {β : Type} (outs : Vector (Vector β 32) 8) : List (Pos Blake2sCircuit.m × β) :=
  (List.finRange 8).flatMap fun w ↦
    (List.finRange 32).map fun i ↦ (pos (256 + 32 * w.val + i.val), outs[w][i])

/-- The walk of the chain block, row `512` skipped: `(Σ_k e(k) (A0 wt)(k), Σ_k e(k) (B0 wt)(k))`. -/
def walkAB (e wt : Pos Blake2sCircuit.m → R) : R × R :=
  let o := walkOps e wt
  let c := wt constPos
  let s₁ := constPositions.foldl
    (fun s k ↦ o.upd s (pos k) (if constBit k then c else 0) (if constBit k then c else 0)) (0, 0)
  let r := o.compressW.run ⟨gateBase, s₁⟩
  let s₂ := (outPairs r.1).foldl (fun s p ↦ o.upd s p.1 p.2 c) r.2.acc
  (s₂.1 + ∑ k : Pos Blake2sCircuit.m, if 648 ≤ k.val ∧ k.val < 904 then e k * wt k else 0,
    s₂.2 + ∑ k : Pos Blake2sCircuit.m, if 648 ≤ k.val ∧ k.val < 904 then e k * c else 0)

/-! ## `walk_eq_sum` -/

variable [CharP R 2] (e wt : Pos Blake2sCircuit.m → R)

omit [CharP R 2] in
private theorem accOf_walk (s : R × R) (L : List (Pos Blake2sCircuit.m × Gate Blake2sCircuit.m)) :
    Generic.accOf (walkOps e wt) (formVal wt) s L =
      (s.1 + (L.map fun kg ↦ e kg.1 * formVal wt kg.2.a).sum,
        s.2 + (L.map fun kg ↦ e kg.1 * formVal wt kg.2.b).sum) := by
  induction L generalizing s with
  | nil => simp [Generic.accOf]
  | cons kg L ih =>
    simp only [Generic.accOf, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [walkOps, List.map_cons, List.sum_cons, add_assoc]

omit [CharP R 2] in
private theorem const_acc :
    constPositions.foldl (fun s k ↦ (walkOps e wt).upd s (pos k)
      (if constBit k then wt constPos else 0) (if constBit k then wt constPos else 0)) (0, 0) =
      Generic.accOf (walkOps e wt) (formVal wt) (0, 0) constGates := by
  simp only [Generic.accOf, constGates, List.foldl_map]
  refine List.foldl_ext _ _ _ fun s k _ ↦ ?_
  unfold constGate
  split
  · simp only [formVal_var]
  · simp [formVal]

private theorem outRows_b (outs : Vector (Word Blake2sCircuit.m) 8) :
    ∀ kg ∈ outRows outs, kg.2.b = Form.var constPos := by
  intro kg hkg
  simp only [outRows, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at hkg
  obtain ⟨w, i, rfl⟩ := hkg
  rfl

omit [CharP R 2] in
private theorem out_acc {outs : Vector (Word Blake2sCircuit.m) 8} {outs' : Vector (Vector R 32) 8}
    (h : Generic.VR (formVal wt) outs outs') (s : R × R) :
    (outPairs outs').foldl (fun s p ↦ (walkOps e wt).upd s p.1 p.2 (wt constPos)) s =
      Generic.accOf (walkOps e wt) (formVal wt) s (outRows outs) := by
  have : outPairs outs' = (outRows outs).map fun kg ↦ (kg.1, formVal wt kg.2.a) := by
    simp only [outPairs, outRows, List.map_flatMap, List.map_map]
    refine List.flatMap_congr fun w _ ↦ List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have := h w i
    simpa only [Fin.getElem_fin] using this
  rw [this, List.foldl_map, Generic.accOf]
  refine List.foldl_ext _ _ _ fun s kg hkg ↦ ?_
  simp only [outRows_b outs kg hkg, formVal_var]

/-- **L-C4 (`walk_eq_sum`).** The walk computes the bilinear forms of the chain block's matrices
with row `512` skipped: `walkA = Σ_{k ≠ 512} e(k) · Σ_j A(k, j) · wt(j)`, and `walkB` alike. -/
theorem walk_eq_sum :
    walkAB e wt =
      (∑ k, if k = constPos then 0 else e k * BlockR1CS.mulVec chainBlock.toBlockR1CS.A wt k,
        ∑ k, if k = constPos then 0 else e k * BlockR1CS.mulVec chainBlock.toBlockR1CS.B wt k) := by
  have hcin : chainBlock.inputs.getLsbD chainBlock.cpos = false := by
    rw [chainBlock_inputs, chainBlock_cpos, getLsbD_chainInputs]; decide
  have hA := sum_rows bounded_chainBlock hcin (fun k g ↦ e k * formVal wt g.a)
    (fun k ↦ by simp [formVal])
  have hB := sum_rows bounded_chainBlock hcin (fun k g ↦ e k * formVal wt g.b)
    (fun k ↦ by simp [formVal])
  rw [chainBlock_cpos] at hA hB
  simp only [formVal_var] at hA hB
  have hmA : ∀ k, BlockR1CS.mulVec chainBlock.toBlockR1CS.A wt k =
      formVal wt (chainBlock.rowOf k).a := fun _ ↦ rfl
  have hmB : ∀ k, BlockR1CS.mulVec chainBlock.toBlockR1CS.B wt k =
      formVal wt (chainBlock.rowOf k).b := fun _ ↦ rfl
  simp only [hmA, hmB, hA, hB]
  simp only [walkAB, const_acc]
  generalize hs₁ : Generic.accOf (walkOps e wt) (formVal wt) (0, 0) constGates = s₁
  -- the simulation of the compression
  have hsim := Generic.sim_compressW (o := walkOps e wt) (φ := formVal wt) (s₀ := s₁)
    (linear_walk e wt) (fun k _ ↦ (formVal_var wt k).symm) ⟨gateBase, #[]⟩ ⟨gateBase, s₁⟩
    ⟨rfl, rfl⟩ (fun kg _ ↦ (formVal_var wt kg.1).symm)
  obtain ⟨⟨-, hacc⟩, hvr⟩ := hsim
  -- the gates of the chain block
  have hgates : chainBlock.gates.toList = constGates ++
      ((compressW.run ⟨gateBase, #[]⟩).2.gates.toList ++ outRows (compressW.run ⟨gateBase, #[]⟩).1)
      := by
    rw [chainBlock_gates, blake2sCircuit_gates]; simp
  have hall : Generic.accOf (walkOps e wt) (formVal wt) (0, 0) chainBlock.gates.toList =
      (outPairs ((walkOps e wt).compressW.run ⟨gateBase, s₁⟩).1).foldl
        (fun s p ↦ (walkOps e wt).upd s p.1 p.2 (wt constPos))
        ((walkOps e wt).compressW.run ⟨gateBase, s₁⟩).2.acc := by
    rw [out_acc e wt hvr, hacc, hgates, ← hs₁]
    simp only [Generic.accOf, List.foldl_append]
  rw [accOf_walk] at hall
  rw [← hall]
  simp only [zero_add, chainBlock_inputs, getLsbD_chainInputs, decide_eq_true_eq]

end Walk

end SpartanChain
