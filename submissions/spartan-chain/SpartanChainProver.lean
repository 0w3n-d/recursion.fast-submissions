import SpartanChainVerifier

/-!
# The leaf SNARK prover and its completeness (BLUEPRINT-R1 §1.4, §6.2, §7, §8)

`proveSnark wf s n` writes the SNARK bytes of a leaf `(s, n)` with `n ≥ 1` (§7 fields 1–9):
the seed `(s, n, chainEnd s n)`, Ligero's commitment and fields 1–2 (`Ligero.commit`,
`Ligero.prove1`), the algebraic layer's fields 3–7 (`Spartan.prove`), Ligero's fields 8–9 for the
row weights `a_i = eq(r''_hi, i)` (`Ligero.prove2`). `proveLeaf` prepends the 80-byte header
`enc64 0 ‖ s ‖ enc64 n ‖ h`.

The chain's prover tables (`Az, Bz, Cz`, `z`, the packed `q`, the table of `M̃_ρ(r_x, ·)`) are the
parameter `wf : WitFor`, supplied by `SpartanChainChain` (`chainWitness` and the sparse matrices).

**Completeness** (`snark_complete`): if the tables and the evaluators are honest for some R1CS
(`HonestOps`, which `SpartanChainChain` proves from L-C3 and `matrix_mle_eq`), then for every
oracle the verifier `snarkProg ev` accepts the honest SNARK bytes, of exactly `snarkSize κ`
bytes. It composes `Ligero.prove1_verify1`, `Spartan.complete` (L-S4, L-R3, L-R4),
`evalClaim_eq` (the PCS evaluation `Σ_j b_j v_j = q̃(r'')`, check (f)) and
`Ligero.verify2_complete`.
-/

namespace SpartanChain

namespace Leaf

open RecursionFast Transcript PCS

/-! ## Bytes -/

theorem data_extract_size (a : ByteArray) (e : ℕ) : a.data.extract a.size e = #[] := by
  rw [Array.extract_eq_empty_iff, ByteArray.size_data]; omega

theorem extract_mid (a b c : ByteArray) : (a ++ b ++ c).extract a.size (a.size + b.size) = b := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_append, Array.extract_append,
    Array.extract_append, data_extract_size]
  simp only [ByteArray.size_data, Array.empty_append, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [Array.extract_eq_self_of_le (by rw [ByteArray.size_data]),
    Array.extract_eq_empty_iff.mpr (by simp), Array.append_empty]

theorem extract_suf (a c : ByteArray) : (a ++ c).extract a.size (a ++ c).size = c := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, Array.extract_append, ByteArray.size_append,
    data_extract_size]
  simp only [ByteArray.size_data, Array.empty_append, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [Array.extract_eq_self_of_le (by rw [ByteArray.size_data])]

theorem extract_pre (a c : ByteArray) : (a ++ c).extract 0 a.size = a := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  simp only [ByteArray.size_data, Nat.sub_self, Nat.zero_sub]
  rw [Array.extract_eq_self_of_le (by rw [ByteArray.size_data]),
    Array.extract_eq_empty_iff.mpr (by simp), Array.append_empty]

/-- The label read at byte `0` of `bytesOf λ ++ rest` is `λ`. -/
theorem readLabel_bytesOf (l : Label) (rest : ByteArray) :
    Ligero.readLabel (bytesOf l ++ rest) 0 = l := by
  refine Vector.ext fun i hi ↦ ?_
  rw [Ligero.readLabel, Vector.getElem_ofFn, Ligero.getElem!_ba, ByteArray.data_append,
    Array.toList_append, Nat.zero_add, List.getD_append _ _ _ _ (by simp [bytesOf]; omega)]
  simp [bytesOf, List.getD_eq_getElem?_getD, hi]

/-! ## The evaluation claim (check (f)) -/

theorem matrixRows_getD (κ : ℕ) (q : Array F) {i j : ℕ} (hi : i < rows κ)
    (hj : j < msgLen κ) (hq : (i + 1) * msgLen κ ≤ q.size) :
    ((Ligero.matrixRows κ q).map fun row ↦ row.getD j 0).getD i 0 =
      q.getD (i * msgLen κ + j) 0 := by
  have hlt : i < (Ligero.matrixRows κ q).size := by simp [Ligero.matrixRows, hi]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some]
  simp only [Ligero.matrixRows, Array.getElem_map, Array.getElem_range]
  have hc : j < min ((i + 1) * msgLen κ) q.size - i * msgLen κ := by
    rw [Nat.min_eq_left hq, Nat.add_mul, one_mul]; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_extract, ite_eq_left hc,
    Array.getD_eq_getD_getElem?]

theorem combRows_getD (m k : ℕ) (w : Array EF) (Q : Array (Array F)) {j : ℕ} (hj : j < k) :
    (Ligero.combRows m k w Q).getD j 0 =
      ∑ i : Fin m, EF.ofF ((Q.map fun row ↦ row.getD j 0).getD i 0) * w.getD i 0 := by
  have hlt : j < (Ligero.combRows m k w Q).size := by simp [Ligero.combRows, hj]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  simp only [Ligero.combRows, Array.getElem_map, Array.getElem_range, Ligero.comb_eq]

/-- The extension of the packed witness, split into the `ℓ_k` column bits and the `μ_r` row bits:
`q̃(r) = Σ_j eq(r_lo, j) Σ_i eq(r_hi, i) q(i·k + j)`. -/
theorem mleEval_split (q : Array F) (r : List EF) {ℓ₁ ℓ₂ : ℕ} (hr : r.length = ℓ₁ + ℓ₂) :
    mleEval (q.map (algebraMap F EF)) r =
      ∑ j : Fin (2 ^ ℓ₁), eq (ptOf ℓ₁ (r.take ℓ₁)) (cube j) *
        ∑ i : Fin (2 ^ ℓ₂), eq (ptOf ℓ₂ (r.drop ℓ₁)) (cube i) *
          algebraMap F EF (q.getD (2 ^ ℓ₁ * i.val + j) 0) := by
  have hpt : ptOf (ℓ₁ + ℓ₂) r = Fin.append (ptOf ℓ₁ (r.take ℓ₁)) (ptOf ℓ₂ (r.drop ℓ₁)) := by
    conv_lhs => rw [← List.take_append_drop ℓ₁ r]
    exact Spartan.ptOf_append _ _ (by simp [hr])
  rw [mleEval_eq' _ _ hr, hpt, mle_split]
  simp only [mle]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ (Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_)
  exact Spartan.getD_map_alg q _

theorem muR_le (κ : ℕ) : muR κ ≤ 8 + κ := by unfold muR; omega

/-- **Check (f) is true for the honest `v`**: with `v = Σ_i a_i Q[i]`, `a_i = eq(r''_hi, i)` and
`b_j = eq(r''_lo, j)`, `Σ_j b_j v_j = q̃(r'')`. -/
theorem evalClaim_eq (κ : ℕ) (q : Array F) (hq : q.size = 2 ^ Spartan.lq κ) (r : List EF)
    (hr : r.length = Spartan.lq κ) :
    dot (eqTable (r.take (lk κ)))
        (Ligero.combRows (rows κ) (msgLen κ) (eqTable (r.drop (lk κ))) (Ligero.matrixRows κ q)) =
      mleEval (q.map (algebraMap F EF)) r := by
  have hsplit : r.length = lk κ + muR κ := by
    rw [hr, Spartan.lq, lk]; have := muR_le κ; omega
  have hlo : (r.take (lk κ)).length = lk κ := by simp [hsplit]
  have hhi : (r.drop (lk κ)).length = muR κ := by simp [hsplit]
  have hqs : q.size = rows κ * msgLen κ := by
    rw [hq, rows, msgLen, ← pow_add, Spartan.lq, lk]; congr 1; have := muR_le κ; omega
  rw [mleEval_split q r hsplit, dot, eqTable_size, hlo, sumTo_eq_fin]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← congrFun (tbl_eqTable' _ hlo) j]
  congr 1
  have hj : j.val < msgLen κ := j.isLt
  rw [combRows_getD _ _ _ _ hj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : i.val < rows κ := i.isLt
  have hle : (i.val + 1) * msgLen κ ≤ q.size := by
    rw [hqs]; exact Nat.mul_le_mul_right _ hi
  rw [matrixRows_getD κ q hi hj hle, ← congrFun (tbl_eqTable' _ hhi) i, EF.algebraMap_eq_ofF,
    mul_comm (EF.ofF _)]
  rw [show i.val * msgLen κ + j.val = 2 ^ lk κ * i.val + j.val by rw [msgLen]; ring]
  rfl

/-! ## The prover -/

/-- The chain's prover tables for `(κ, n, s)`. -/
abbrev WitFor := ℕ → ℕ → Digest → Spartan.Witness

/-- **The SNARK prover** of a leaf `(s, n)`, `n ≥ 1` (§7 fields 1–9). -/
def proveSnark (wf : WitFor) (s : Digest) (n : ℕ) : OProg ByteArray := do
  let κ := kap n
  let w := wf κ n s
  let st ← seed s n (chainEnd s n)
  let cm ← Ligero.commit κ w.q
  let p₁ ← Ligero.prove1 κ st cm
  let p₂ ← Spartan.prove κ w p₁.1
  let p₃ ← Ligero.prove2 κ p₂.1 cm (eqTable (p₂.2.2.drop (lk κ)))
  pure (p₁.2.2.1 ++ p₁.2.2.2 ++ Spartan.encodeMsgs p₂.2.1 ++ p₃.1 ++ p₃.2)

/-- The tables and the evaluators are honest for some R1CS, for every true leaf statement
(`SpartanChainChain` proves it for the chain R1CS from L-C3 and `matrix_mle_eq`). -/
def HonestOps (ev : EvalsFor) (wf : WitFor) : Prop :=
  ∀ s n, 1 ≤ n → n ≤ chainCap → ∃ A B C,
    Spartan.Honest (kap n) (wf (kap n) n s) (ev (kap n) n s (chainEnd s n)) A B C

theorem size1_eq (κ : ℕ) : Ligero.size1 κ = 31 + 24 * msgLen κ := rfl

theorem readEFs_efBytes' (xs : Array EF) (k : ℕ) (h : xs.size = k) :
    Ligero.readEFs (Ligero.efBytes xs) 0 k = xs := by
  subst h; exact Ligero.readEFs_efBytes xs

theorem combRows_size (m k : ℕ) (w : Array EF) (Q : Array (Array F)) :
    (Ligero.combRows m k w Q).size = k := by simp [Ligero.combRows]

/-- **Leaf completeness** (§8): for every oracle, the SNARK verifier accepts the honest SNARK bytes
of a true leaf statement. -/
theorem snark_complete (ev : EvalsFor) (wf : WitFor) (hon : HonestOps ev wf)
    (H : ByteArray → Digest) (s : Digest) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ chainCap) :
    (snarkProg ev s n (chainEnd s n) ((proveSnark wf s n).run H)).run H = true := by
  obtain ⟨A, B, C, hh⟩ := hon s n h1 h2
  simp only [proveSnark, snarkProg, seed, OProg.run_bind, OProg.run_ask, OProg.run_pure]
  generalize wf (kap n) n s = w at hh ⊢
  generalize H (seedQ s n (chainEnd s n)) = st
  generalize hcm : (Ligero.commit (kap n) w.q).run H = cm
  have hroot : ((Ligero.prove1 (kap n) st cm).run H).2.2.1 = bytesOf (cm.root (kap n)) := by
    simp [Ligero.prove1]
  have hubar : ((Ligero.prove1 (kap n) st cm).run H).2.2.2 = Ligero.efBytes (Ligero.combRows
      (rows (kap n)) (msgLen (kap n)) ((Ligero.prove1 (kap n) st cm).run H).2.1.toArray cm.Q) := by
    simp [Ligero.prove1]
  have hv1 := Ligero.prove1_verify1 H (kap n) st cm
  dsimp only at hv1
  generalize (Ligero.prove1 (kap n) st cm).run H = p₁ at hroot hubar hv1 ⊢
  obtain ⟨c, hc, hpt, hlen, hval⟩ := Spartan.complete H hh p₁.1
  have hws := Spartan.prove_wellSized H (kap n) w p₁.1
  generalize (Spartan.prove (kap n) w p₁.1).run H = p₂ at hc hpt hws ⊢
  have h2c := Ligero.verify2_complete H (kap n) p₂.1 w.q p₁.2.1.toArray
    (eqTable (p₂.2.2.drop (lk (kap n))))
  dsimp only at h2c
  rw [hcm] at h2c
  have hvB : ((Ligero.prove2 (kap n) p₂.1 cm (eqTable (p₂.2.2.drop (lk (kap n))))).run H).1 =
      Ligero.efBytes (Ligero.combRows (rows (kap n)) (msgLen (kap n))
        (eqTable (p₂.2.2.drop (lk (kap n)))) cm.Q) := by
    simp [Ligero.prove2]
  generalize (Ligero.prove2 (kap n) p₂.1 cm (eqTable (p₂.2.2.drop (lk (kap n))))).run H = p₃
    at h2c hvB ⊢
  have hQ : cm.Q = Ligero.matrixRows (kap n) w.q := by rw [← hcm, Ligero.run_commit]
  -- sizes
  have s_a : p₁.2.2.1.size = 31 := by rw [hroot, size_bytesOf]
  have s_b : p₁.2.2.2.size = 24 * msgLen (kap n) := by
    rw [hubar, Spartan.efBytes_size, combRows_size]
  have s_M : (Spartan.encodeMsgs p₂.2.1).size = Spartan.msgsBytes (kap n) :=
    Spartan.encodeMsgs_size _ _ hws
  have s_v : p₃.1.size = 24 * msgLen (kap n) := by rw [hvB, Spartan.efBytes_size, combRows_size]
  have hparse : ∀ pre post : ByteArray, pre.size = off₁ (kap n) →
      Spartan.parseMsgs (kap n) (pre ++ Spartan.encodeMsgs p₂.2.1 ++ post) (off₁ (kap n)) =
        p₂.2.1 := fun pre post hp ↦ by
    rw [← hp]; exact Spartan.parseMsgs_encodeMsgs _ _ hws pre post
  generalize p₁.2.2.1 = a at hroot s_a hv1 ⊢
  generalize p₁.2.2.2 = b at hubar s_b hv1 ⊢
  generalize Spartan.encodeMsgs p₂.2.1 = M at s_M hparse ⊢
  have e₀ : (a ++ b ++ M ++ p₃.1 ++ p₃.2).extract 0 31 = a := by
    rw [show a ++ b ++ M ++ p₃.1 ++ p₃.2 = a ++ (b ++ M ++ p₃.1 ++ p₃.2) by
      simp only [ByteArray.append_assoc], ← s_a, extract_pre]
  have e₁ : (a ++ b ++ M ++ p₃.1 ++ p₃.2).extract 31 (off₁ (kap n)) = b := by
    rw [show a ++ b ++ M ++ p₃.1 ++ p₃.2 = a ++ b ++ (M ++ p₃.1 ++ p₃.2) by
      simp only [ByteArray.append_assoc], show off₁ (kap n) = a.size + b.size by
      rw [s_a, s_b]; rfl, ← s_a, extract_mid]
  have e₂ : Spartan.parseMsgs (kap n) (a ++ b ++ M ++ p₃.1 ++ p₃.2) (off₁ (kap n)) = p₂.2.1 := by
    rw [show a ++ b ++ M ++ p₃.1 ++ p₃.2 = a ++ b ++ M ++ (p₃.1 ++ p₃.2) by
      simp only [ByteArray.append_assoc]]
    exact hparse _ _ (by rw [ByteArray.size_append, s_a, s_b]; rfl)
  have e₃ : (a ++ b ++ M ++ p₃.1 ++ p₃.2).extract (off₂ (kap n)) (off₃ (kap n)) = p₃.1 := by
    rw [show off₂ (kap n) = (a ++ b ++ M).size by
      rw [ByteArray.size_append, ByteArray.size_append, s_a, s_b, s_M]; rfl,
      show off₃ (kap n) = (a ++ b ++ M).size + p₃.1.size by
      rw [ByteArray.size_append, ByteArray.size_append, s_a, s_b, s_M, s_v]; rfl, extract_mid]
  have e₄ : (a ++ b ++ M ++ p₃.1 ++ p₃.2).extract (off₃ (kap n))
      (a ++ b ++ M ++ p₃.1 ++ p₃.2).size = p₃.2 := by
    rw [show off₃ (kap n) = (a ++ b ++ M ++ p₃.1).size by
      simp only [ByteArray.size_append, s_a, s_b, s_M, s_v]; rfl, extract_suf]
  have e₅ : Ligero.readLabel (a ++ b ++ M ++ p₃.1 ++ p₃.2) 0 = cm.root (kap n) := by
    rw [show a ++ b ++ M ++ p₃.1 ++ p₃.2 = a ++ (b ++ M ++ p₃.1 ++ p₃.2) by
      simp only [ByteArray.append_assoc], hroot, readLabel_bytesOf]
  simp only [e₀, e₁, e₂]
  rw [hv1]
  dsimp only
  rw [hc]
  simp only [tail, e₁, e₃, e₄, e₅]
  have hf : finalCheck (kap n) c (Ligero.readEFs p₃.1 0 (msgLen (kap n))) = true := by
    have hr : Ligero.readEFs p₃.1 0 (msgLen (kap n)) = Ligero.combRows (rows (kap n))
        (msgLen (kap n)) (eqTable (p₂.2.2.drop (lk (kap n)))) cm.Q := by
      rw [hvB]
      exact readEFs_efBytes' _ _ (combRows_size _ _ _ _)
    rw [finalCheck, hr, hQ, ← hpt, evalClaim_eq (kap n) w.q hh.q_size c.point hlen, ← hval]
    simp
  rw [ite_eq_left hf, hpt]
  have hb : Ligero.readEFs b 0 (msgLen (kap n)) =
      Ligero.combRows (rows (kap n)) (msgLen (kap n)) p₁.2.1.toArray cm.Q := by
    rw [hubar]
    exact readEFs_efBytes' _ _ (combRows_size _ _ _ _)
  rw [hb]
  exact h2c

/-- The 80-byte leaf header `enc64 0 ‖ s ‖ enc64 n ‖ h` (§1.1). -/
def leafHeader (s : Digest) (n : ℕ) (h : Digest) : ByteArray :=
  ⟨(enc64 0 ++ s.toList ++ enc64 n ++ h.toList).toArray⟩

/-- **The leaf prover** (§1.4): the header, and the SNARK for `n ≥ 1` (`h = chainEnd s n`). -/
def proveLeaf (wf : WitFor) (s : Digest) (n : ℕ) : OProg ByteArray :=
  if n = 0 then pure (leafHeader s 0 s)
  else do
    let π ← proveSnark wf s n
    pure (leafHeader s n (chainEnd s n) ++ π)

/-! ## Size (§7) -/

/-- The openings of the honest prover: `tQ` openings of `openW κ` bytes each. -/
theorem openings_size (H : ByteArray → Digest) (κ : ℕ) (q : Array F) (st : Digest)
    (a : Array EF) :
    ((Ligero.prove2 κ st ((Ligero.commit κ q).run H) a).run H).2.size = tQ * Ligero.openW κ := by
  set cm := (Ligero.commit κ q).run H with hcm
  set idx := ((squeezeIdx ((absorb st 0x08 (Ligero.efBytes (Ligero.combRows (rows κ) (msgLen κ)
    a cm.Q))).run H) (lN κ) tQ).run H).2 with hidx
  set cs := (List.range tQ).map fun j ↦ idx.getD j 0 with hcs
  have hout : ((Ligero.prove2 κ st cm a).run H).2 =
      cs.foldl (fun acc c ↦ acc ++ Ligero.openingBytes κ cm c) ByteArray.empty := by
    simp [Ligero.prove2, hcs, hidx]
  have hlt : ∀ c ∈ cs, c < cols κ := by
    intro c hc
    simp only [hcs, List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    simp only [hidx, squeezeIdx, OProg.run_bind, OProg.run_pure]
    exact Ligero.indices_getD_lt _ _ _ _
  have hQ : cm.Q.size = rows κ := by simp [cm, Ligero.run_commit, Ligero.matrixRows]
  have hcolF : ∀ c < cols κ, cm.colsF[c]! =
      Ligero.columnAt (Ligero.kapArr (lk κ)) (lk κ) cm.Q (Ligero.ptOf c) := by
    intro c hc; simp [cm, Ligero.run_commit, getElem!_pos, hc]
  have hcolB : ∀ c < cols κ, cm.colsB[c]! = Ligero.fBytes cm.colsF[c]! := by
    intro c hc; simp [cm, Ligero.run_commit, getElem!_pos, hc]
  have hsizeB : ∀ c < cols κ, cm.colsB[c]!.size = 8 * rows κ := by
    intro c hc; rw [hcolB c hc, Ligero.size_fBytes, hcolF c hc]; simp [Ligero.columnAt, hQ]
  have hplen : ∀ c, (Merkle.path cm.levels (lN κ) c).length = lN κ := by simp [Merkle.path]
  have hw : ∀ c ∈ cs, (Ligero.openingBytes κ cm c).data.toList.length = Ligero.openW κ := by
    intro c hc
    rw [Ligero.openingBytes, ByteArray.data_append, Array.toList_append, List.length_append,
      Ligero.length_labelsBytes, hplen, Array.length_toList, ← ByteArray.size, hsizeB c (hlt c hc)]
    rfl
  rw [hout, ByteArray.size, ← Array.length_toList, Ligero.foldl_data_empty,
    Ligero.length_flatMap_const _ _ _ hw]
  simp [hcs, mul_comm]

/-- **The honest SNARK has exactly `snarkSize κ` bytes** (§7), so the honest leaf proof has
`leafSize n` bytes. -/
theorem snark_size (wf : WitFor) (H : ByteArray → Digest) (s : Digest) (n : ℕ) :
    ((proveSnark wf s n).run H).size = snarkSize (kap n) := by
  simp only [proveSnark, seed, OProg.run_bind, OProg.run_ask, OProg.run_pure]
  have hws := Spartan.prove_wellSized H (kap n) (wf (kap n) n s)
    ((Ligero.prove1 (kap n) (H (seedQ s n (chainEnd s n)))
      ((Ligero.commit (kap n) (wf (kap n) n s).q).run H)).run H).1
  simp only [ByteArray.size_append, Spartan.encodeMsgs_size _ _ hws]
  rw [openings_size]
  simp [Ligero.prove1, Ligero.prove2, Spartan.efBytes_size, combRows_size, snarkSize,
    Ligero.size1, Ligero.size2]
  ring

/-- The honest leaf proof has exactly `leafSize n` bytes. -/
theorem proveLeaf_size (wf : WitFor) (H : ByteArray → Digest) (s : Digest) (n : ℕ) :
    ((proveLeaf wf s n).run H).size = leafSize n := by
  unfold proveLeaf leafSize
  split_ifs with h
  · simp [leafHeader, ByteArray.size, enc64]
  · simp only [OProg.run_bind, OProg.run_pure, ByteArray.size_append, snark_size]
    simp [leafHeader, ByteArray.size, enc64]

/-- §7's sizes, equal to the Rust prover's leaf files: `leafSize 16 = 143 711`,
`leafSize 2 = 100 119`, `leafSize 1 = 95 719`, `leafSize 0 = 80`. -/
theorem leafSize_table :
    leafSize 16 = 143711 ∧ leafSize 2 = 100119 ∧ leafSize 1 = 95719 ∧ leafSize 0 = 80 := by
  decide

end Leaf

end SpartanChain
