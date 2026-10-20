import SpartanChainBlake2sWalk

/-!
# Witness generation for the chain block, and the circuit dump

* `fastTrace d`: the honest block of a chain step from `d` as an `Array Bool` of `2 ^ 14` bits,
  computed by the generic gadgets with Boolean values (`evalOps`: `xor` is `^^`, a product gate
  stores `a && b`), i.e. `O(|circuit|)` Boolean operations, not the bitset trace.
  `fastTrace_eq`: it is `chainTrace d` at every position (by the simulation of
  `SpartanChainBlake2sGeneric.lean` with `φ L = L.eval (chainTrace d)`).
* `circuitLine`, `dumpCircuit`: the row list of the chain block for the known-answer harness
  (BLUEPRINT-R1 §11.3 (2)): one line per position `k < 2 ^ 14`,
  `k <a-form> <b-form>`, each form as 256 chunks of 64 bits, lowest chunk first, each chunk as
  16 lowercase hex digits (most significant first). The rows are `rowOf` of the chain block
  (`chainBlockC () = chainBlock`), row `512` included as `(var 512, var 512)`.
-/

namespace SpartanChain

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## The evaluation interpretation -/

/-- Forms are their Boolean values on the honest block; a product gate at `k` returns `a && b`
and stores it at `k`. -/
def evalOps {m : ℕ} (inp : Pos m → Bool) : GOps m Bool (Array Bool) where
  zero := false
  xor a b := a ^^ b
  var := inp
  res _ a b := a && b
  upd arr k a b := arr.set! k (a && b)

theorem evalOps_res {m : ℕ} (inp : Pos m → Bool) (k : Pos m) (a b : Bool) :
    (evalOps inp).res k a b = (a && b) := rfl

theorem evalOps_upd {m : ℕ} (inp : Pos m → Bool) (arr : Array Bool) (k : Pos m) (a b : Bool) :
    (evalOps inp).upd arr k a b = arr.set! k (a && b) := rfl

theorem linear_eval {m : ℕ} (inp z : Pos m → Bool) :
    Generic.Linear (evalOps inp) (fun L : Form m ↦ L.eval z) where
  zero := eval_zero z
  xor a b := eval_xor a b z

/-- The block before the compression's gates: `1` at `512`, the digest bits at `648 … 903`, the
constants at the constant positions, `0` elsewhere. -/
def chainInit (d : Digest) (k : Pos Blake2sCircuit.m) : Bool :=
  if k.val = 512 then true
  else if 648 ≤ k.val ∧ k.val < 904 then chainInp d k
  else if k.val < 256 ∨ (640 ≤ k.val ∧ k.val < 648) ∨ (904 ≤ k.val ∧ k.val < 1280) then
    constBit k.val
  else false

/-- The honest block of a chain step from `d`, computed with Boolean values. -/
def fastTrace (d : Digest) : Array Bool :=
  let inp := chainInit d
  let r := (evalOps inp).compressW.run ⟨gateBase, Array.ofFn inp⟩
  (outPairs r.1).foldl (fun a p ↦ a.set! p.1 p.2) r.2.acc

/-! ## Correctness -/

-- No unification may evaluate the compression.
attribute [local irreducible] compressW GOps.compressW

private theorem foldl_set {m : ℕ} (z : Pos m → Bool) (L : List (Pos m × Bool))
    (hL : ∀ p ∈ L, p.2 = z p.1) :
    ∀ (a : Array Bool), a.size = 2 ^ m → (L.foldl (fun a p ↦ a.set! p.1 p.2) a).size = 2 ^ m ∧
      ∀ j : Pos m, (L.foldl (fun a p ↦ a.set! p.1 p.2) a)[j.val]? =
        if j ∈ L.map Prod.fst then some (z j) else a[j.val]? := by
  induction L with
  | nil => intro a ha; simp [ha]
  | cons p L ih =>
    intro a ha
    have hs : (a.set! p.1 p.2).size = 2 ^ m := by simp [ha]
    obtain ⟨h1, h2⟩ := ih (fun q hq ↦ hL q (List.mem_cons_of_mem _ hq)) _ hs
    refine ⟨h1, fun j ↦ ?_⟩
    rw [List.foldl_cons, h2 j]
    by_cases hj : j ∈ L.map Prod.fst
    · simp [hj]
    · have hp := hL p List.mem_cons_self
      by_cases hpj : p.1 = j
      · subst hpj
        simp [hj, ha, hp]
      · have : (p.1 : ℕ) ≠ j := fun h ↦ hpj (Fin.ext h)
        simp [hj, this, Ne.symm hpj]

/-- The gates of the compression sit in `[1280, 16000)`. -/
theorem compress_keys {kg : Pos Blake2sCircuit.m × Gate Blake2sCircuit.m}
    (h : kg ∈ (compressW.run ⟨gateBase, #[]⟩).2.gates.toList) :
    1280 ≤ kg.1.val ∧ kg.1.val < 16000 := by
  have hok := ok_compressW ⟨gateBase, #[]⟩ Start.inv_init le_rfl (by decide)
  have hav := hok.1.avail kg.1
  rw [hok.2.1, availAfter_getLsbD] at hav
  have hany : ((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.any
      fun kg' ↦ decide ((kg'.1 : ℕ) = kg.1)) = true := List.any_eq_true.mpr ⟨kg, h, by simp⟩
  rw [hany, Bool.or_true] at hav
  have hfresh := boundedFrom_fresh hok.1.bounded (List.mem_map_of_mem (f := Prod.fst) h)
  have := (start_availAt _ _).mp hav.symm
  rw [start_avail] at hfresh
  simp only [decide_eq_false_iff_not] at hfresh
  simp only [gateBase] at this
  omega

section

variable (d : Digest)

private theorem trace_gates :
    ∀ kg ∈ chainBlock.gates, chainTrace d kg.1 =
      (kg.2.a.eval (chainTrace d) && kg.2.b.eval (chainTrace d)) :=
  gates_of_rows bounded_chainBlock _ (trace_holds bounded_chainBlock (chainInp d))

private theorem trace_one : chainTrace d constPos = true := by
  rw [chainTrace, ← chainBlock_cpos]; exact traceF_cpos bounded_chainBlock _

private theorem pos_val' {k : ℕ} (h : k < 16384) : ((pos k : Pos Blake2sCircuit.m) : ℕ) = k :=
  pos_val h

/-- The initial block agrees with the honest block outside the compression's gates and the output
rows. -/
private theorem init_eq (k : Pos Blake2sCircuit.m)
    (hk1 : k ∉ (compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map Prod.fst)
    (hk2 : k ∉ (outRows (compressW.run ⟨gateBase, #[]⟩).1).map Prod.fst) :
    chainInit d k = chainTrace d k := by
  have hkv : k = pos k.val := Fin.ext (pos_val' k.isLt).symm
  unfold chainInit
  split_ifs with h512 hin hc
  · rw [show k = constPos from Fin.ext h512, trace_one]
  · rw [chainTrace, traceF_input bounded_chainBlock _
      (by rw [chainBlock_inputs, getLsbD_chainInputs]; simp; omega)
      (by rw [chainBlock_cpos]; intro h; exact h512 (congrArg Fin.val h))]
  · rw [hkv, const_of_gates (trace_gates d) (trace_one d) (mem_constPositions.mpr hc), ← hkv]
  · -- padding: the zero row
    have hnm : k ∉ chainBlock.gates.toList.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
      rw [chainBlock_gates, Array.toList_append, List.mem_append, List.toList_toArray] at hp
      rcases hp with hp | hp
      · unfold constGates at hp
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
        have := mem_constPositions.mp hj
        have hv := congrArg Fin.val hpk
        simp only [constGate] at hv
        rw [pos_val' (by omega)] at hv
        omega
      · rw [blake2sCircuit_gates, Array.toList_append, List.mem_append,
          List.toList_toArray] at hp
        rcases hp with hp | hp
        · exact hk1 (hpk ▸ List.mem_map_of_mem hp)
        · exact hk2 (hpk ▸ List.mem_map_of_mem hp)
    rw [chainTrace, traceF_of_not_mem _ _ hnm, initF, chainBlock_cpos, chainBlock_inputs,
      getLsbD_chainInputs]
    have e1 : decide (k = constPos) = false := decide_eq_false fun h ↦ h512 (congrArg Fin.val h)
    have e2 : decide (648 ≤ k.val ∧ k.val < 904) = false := decide_eq_false hin
    rw [e1, e2]
    rfl

/-- **Witness generation.** The Boolean evaluation of the generic gadgets computes the honest
block of a chain step at every position. -/
theorem fastTrace_eq (k : Pos Blake2sCircuit.m) : (fastTrace d)[k.val]? = some (chainTrace d k) := by
  set z := chainTrace d
  have hlin := linear_eval (chainInit d) z
  have hsz : (Array.ofFn (chainInit d)).size = 2 ^ Blake2sCircuit.m := Array.size_ofFn
  have hget : (Array.ofFn (chainInit d))[k.val]? = some (chainInit d k) := by
    rw [Array.getElem?_ofFn, dite_eq_left k.isLt]
  unfold fastTrace
  dsimp only
  generalize Array.ofFn (chainInit d) = A at hsz hget ⊢
  have hgates : ∀ kg ∈ (compressW.run ⟨gateBase, #[]⟩).2.gates,
      z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) := fun kg h ↦ trace_gates d kg (by
    rw [chainBlock_gates, blake2sCircuit_gates]
    exact Array.mem_append_right _ (Array.mem_append_left _ h))
  have hsim := Generic.sim_compressW (o := evalOps (chainInit d)) (φ := fun L ↦ L.eval z)
    (s₀ := A) hlin (fun k hk ↦ by
      simp only [evalOps, eval_var]
      rw [start_avail] at hk
      simp only [decide_eq_true_eq] at hk
      refine init_eq d k (fun h ↦ ?_) (fun h ↦ ?_)
      · obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp h
        have := compress_keys hkg
        omega
      · obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp h
        simp only [outRows, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at hkg
        obtain ⟨w, i, rfl⟩ := hkg
        have := pos_out_val w i
        dsimp only at hk
        omega)
    ⟨gateBase, #[]⟩ ⟨gateBase, A⟩ ⟨rfl, rfl⟩
    (fun kg h ↦ by
      rw [evalOps_res]
      beta_reduce
      rw [eval_var]
      exact (hgates kg h).symm)
  obtain ⟨⟨-, hacc⟩, hvr⟩ := hsim
  -- the compression's gates, as stores of the honest values
  have hc : (Generic.accOf (evalOps (chainInit d)) (fun L ↦ L.eval z) A
      (compressW.run ⟨gateBase, #[]⟩).2.gates.toList) =
      (((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map fun kg ↦ (kg.1, z kg.1)).foldl
        (fun a p ↦ a.set! p.1 p.2) A) := by
    rw [List.foldl_map, Generic.accOf]
    refine List.foldl_ext _ _ _ fun a kg hkg ↦ ?_
    rw [evalOps_upd]
    rw [hgates kg (Array.mem_toList_iff.mp hkg)]
  -- the output rows, as stores of the honest values
  set r := (evalOps (chainInit d)).compressW.run ⟨gateBase, A⟩
  have hout : outPairs r.1 = (outRows (compressW.run ⟨gateBase, #[]⟩).1).map
      fun kg ↦ (kg.1, z kg.1) := by
    simp only [outPairs, outRows, List.map_flatMap, List.map_map]
    refine List.flatMap_congr fun w _ ↦ List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have h1 := hvr w i
    simp only [Fin.getElem_fin] at h1 ⊢
    rw [h1]
    have hrow := trace_gates d (pos (256 + 32 * w.val + i.val),
      ⟨(compressW.run ⟨gateBase, #[]⟩).1[w][i], Form.var constPos⟩) (by
        rw [chainBlock_gates, blake2sCircuit_gates]
        refine Array.mem_append_right _ (Array.mem_append_right _ (List.mem_toArray.mpr ?_))
        exact List.mem_flatMap.mpr ⟨w, List.mem_finRange w,
          List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩)
    simp only [eval_var, trace_one d, Bool.and_true] at hrow
    exact hrow.symm
  obtain ⟨hs1, hg1⟩ := foldl_set z ((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map
    fun kg ↦ (kg.1, z kg.1)) (fun p hp ↦ by obtain ⟨kg, -, rfl⟩ := List.mem_map.mp hp; rfl) _ hsz
  obtain ⟨-, hg2⟩ := foldl_set z ((outRows (compressW.run ⟨gateBase, #[]⟩).1).map
    fun kg ↦ (kg.1, z kg.1)) (fun p hp ↦ by obtain ⟨kg, -, rfl⟩ := List.mem_map.mp hp; rfl) _ hs1
  rw [hacc, hc, hout, hg2, hg1, hget]
  have hf : ∀ L : List (Pos Blake2sCircuit.m × Gate Blake2sCircuit.m),
      (L.map fun kg ↦ (kg.1, z kg.1)).map Prod.fst = L.map Prod.fst := fun L ↦ by
    rw [List.map_map]; rfl
  rw [hf, hf]
  split_ifs with ho hg
  · rfl
  · rfl
  · exact congrArg some (init_eq d k hg ho)

end

/-! ## The circuit dump (known-answer harness) -/

/-- The chain block with its compression gates recorded from `base`; `chainBlockAt gateBase` is
`chainBlock` (`chainBlockAt_eq`). The argument keeps the compression out of the compiler's
closed-term extraction (it would otherwise run when an executable starts); `never_extract`
keeps the closed call `chainBlockAt gateBase` from being extracted. -/
@[never_extract] def chainBlockAt (base : ℕ) : ProductCircuit Blake2sCircuit.m :=
  let r := compressW.run ⟨base, #[]⟩
  { cpos := constPos, inputs := chainInputs,
    gates := constGates.toArray ++ (r.2.gates ++ (outRows r.1).toArray) }

theorem chainBlockAt_eq : chainBlockAt gateBase = chainBlock := by
  unfold chainBlockAt chainBlock blake2sCircuit
  rfl

/-- 64 bits as 16 lowercase hex digits, most significant first. -/
def hex64 (x : ℕ) : String :=
  String.ofList ((List.range 16).reverse.map fun j ↦ Nat.digitChar ((x >>> (4 * j)) % 16))

/-- A form as 256 chunks of 64 bits, lowest chunk first, each as 16 hex digits. -/
def hexForm (L : Form Blake2sCircuit.m) : String :=
  String.join ((List.range 256).map fun i ↦ hex64 ((L.toNat >>> (64 * i)) % 2 ^ 64))

/-- The dump line of a row: `k <a-form> <b-form>`. -/
def rowLine (k : ℕ) (g : Gate Blake2sCircuit.m) : String :=
  toString k ++ " " ++ hexForm g.a ++ " " ++ hexForm g.b

/-- The rows of the chain block (`rowOf`), position by position. -/
def circuitRows (base : ℕ) : List (Gate Blake2sCircuit.m) :=
  let c := chainBlockAt base
  let l := c.gates.toList
  (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦ c.rowOfList l k

/-- The rows dumped are the chain block's `rowOf`, position by position. -/
theorem circuitRows_eq :
    circuitRows gateBase = (List.finRange (2 ^ Blake2sCircuit.m)).map chainBlock.rowOf := by
  unfold circuitRows
  rw [chainBlockAt_eq]
  rfl

/-- Write the row list of the chain block, one `rowLine` per position (BLUEPRINT-R1 §11.3 (2)). -/
def dumpCircuit (h : IO.FS.Stream) : IO Unit := do
  let rows := circuitRows gateBase
  let mut k := 0
  for g in rows do
    h.putStrLn (rowLine k g)
    k := k + 1

/-- Write the honest block of the chain step from `d`: one line of `2 ^ 14` digits `0`/`1`, position
`0` first. -/
def dumpTrace (h : IO.FS.Stream) (d : Digest) : IO Unit :=
  h.putStrLn (String.ofList ((fastTrace d).toList.map fun b ↦ if b then '1' else '0'))

end SpartanChain
