import SpartanChainChain

/-!
# The chain R1CS, both directions (L-C2 `chain_sound`, L-C3 `chain_complete`)

BLUEPRINT-R1 §2.3. Over a field `E` of characteristic two, with `1 ≤ n ≤ 2 ^ κ`:

* **L-C2** `chain_sound`: a witness with `0/1` entries such that `ChainSat n κ w s h` has
  `chainEnd s n = h`. Row `512` of each block forces its constant to `1`; then the block satisfies
  the chain block's R1CS, and `block_sound` gives `out_t = chainStep msg_t`; the wiring rows give
  `msg_0 = s`, `msg_t = out_{t−1}`; the tail rows give `out_{n−1} = h`.
* **L-C3** `chain_complete`: `chainWitness s κ` (block `t` is `chainTrace (chainEnd s t)`)
  satisfies `ChainSat n κ _ s (chainEnd s n)`, and is `0/1` (`chainWitness_isBool`).
* `chainWitnessBits s κ`: the witness bits, computed with `fastTrace`, block after block
  (`chainWitnessBits_eq`).
-/

namespace SpartanChain

open RecursionFast ProductCircuit Blake2sCircuit Finset

/-! ## Digest bits -/

theorem dbit_eq (d : Digest) {e i : ℕ} (he : e < 32) (hi : i < 8) :
    dbit d (8 * e + i) = d[e].toBitVec.getLsbD i := by
  have h1 : (8 * e + i) / 8 = e := by omega
  have h2 : (8 * e + i) % 8 = i := by omega
  simp only [dbit, show 8 * e + i < 256 by omega, ↓reduceDIte, h1, h2]

theorem dbit_readDigest (z : Pos Blake2sCircuit.m → Bool) (b : ℕ) {j : ℕ} (hj : j < 256) :
    dbit (readDigest z b) j = z (pos (b + j)) := by
  have := dbit_eq (readDigest z b) (e := j / 8) (i := j % 8) (by omega) (Nat.mod_lt _ (by omega))
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  rw [this, readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))]
  congr 2
  omega

theorem digest_eq_of_dbit {d d' : Digest} (h : ∀ j < 256, dbit d j = dbit d' j) : d = d' :=
  digest_ext fun e he i hi ↦ by
    rw [← dbit_eq d he hi, ← dbit_eq d' he hi]
    exact h _ (by omega)

/-! ## Reading the extended witness -/

variable {E : Type} [Field E]

theorem zN_zOf_w {κ : ℕ} (w : Fin (wLen κ) → E) (s h : Digest) {v : ℕ} (hv : v < wLen κ) :
    zN (zOf w s h) v = w ⟨v, hv⟩ := by
  have : v < 2 ^ (14 + κ + 1) := by rw [ixLen_eq]; rw [wLen_eq] at hv; omega
  simp [zN, zOf, this, hv]

theorem zN_zOf_pub {κ : ℕ} (w : Fin (wLen κ) → E) (s h : Digest) {u : ℕ} (hu : u < wLen κ) :
    zN (zOf w s h) (wLen κ + u) = pubVal s h u := by
  have : wLen κ + u < 2 ^ (14 + κ + 1) := by rw [ixLen_eq]; rw [wLen_eq] at hu ⊢; omega
  simp [zN, zOf, this]

theorem pubVal_zero (s h : Digest) : pubVal (E := E) s h 0 = 1 := by simp [pubVal]

theorem pubVal_s (s h : Digest) {j : ℕ} (hj : j < 256) :
    pubVal (E := E) s h (1 + j) = ofBool E (dbit s j) := by
  simp only [pubVal, show 1 + j ≠ 0 by omega, show 1 + j < 257 by omega, ↓reduceIte,
    show 1 + j - 1 = j by omega]

theorem pubVal_h (s h : Digest) {j : ℕ} (hj : j < 256) :
    pubVal (E := E) s h (257 + j) = ofBool E (dbit h j) := by
  simp only [pubVal, show 257 + j ≠ 0 by omega, show ¬ 257 + j < 257 by omega,
    show 257 + j < 513 by omega, ↓reduceIte, show 257 + j - 257 = j by omega]

/-! ## The chain block's row 512 -/

/-- The row of the constant of a circuit whose gates avoid it. -/
theorem rowOf_cpos_of {m : ℕ} (c : ProductCircuit m) (h : c.gates.toList.lookup c.cpos = none) :
    c.rowOf c.cpos = ⟨Form.var c.cpos, Form.var c.cpos⟩ := by
  simp [rowOf, rowOfList, h]

theorem rowOf_cpos_a_eval (z : Pos Blake2sCircuit.m → Bool) :
    (chainBlock.rowOf constPos).a.eval z = z constPos ∧
      (chainBlock.rowOf constPos).b.eval z = z constPos := by
  have hl : chainBlock.gates.toList.lookup chainBlock.cpos = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    simp only [bne_iff_ne, ne_eq]
    intro he
    have := boundedFrom_fresh bounded_chainBlock (List.mem_map_of_mem (f := Prod.fst) hp)
    rw [← he, BitVec.getLsbD_or, getLsbD_var,
      show decide ((chainBlock.cpos : ℕ) = chainBlock.cpos) = true from decide_eq_true rfl,
      Bool.or_true] at this
    exact Bool.noConfusion this
  have hrow := rowOf_cpos_of chainBlock hl
  rw [chainBlock_cpos] at hrow
  rw [hrow]
  exact ⟨eval_var _ _, eval_var _ _⟩

theorem blockA_eq {k : Pos Blake2sCircuit.m} (hk : k ≠ constPos) (j : Pos Blake2sCircuit.m) :
    blockA k j = (chainBlock.rowOf k).a.getLsbD j := by simp [blockA, hk]

theorem blockB_eq {k : Pos Blake2sCircuit.m} (hk : k ≠ constPos) (j : Pos Blake2sCircuit.m) :
    blockB k j = (chainBlock.rowOf k).b.getLsbD j := by simp [blockB, hk]

theorem pos_val14 (k : Pos Blake2sCircuit.m) : (pos k.val : Pos Blake2sCircuit.m) = k :=
  Fin.ext (pos_val k.isLt)

theorem constPos_val14 : (constPos : ℕ) = 512 := rfl

/-! ## L-C2 -/

section Sound

variable {n κ : ℕ}

/-- The rows of a satisfied chain R1CS, read on the natural numbers. -/
private theorem rowEq {w : Fin (wLen κ) → E} {s h : Digest} (hsat : ChainSat n κ w s h) {v : ℕ}
    (hv : v < 2 ^ (14 + κ + 1)) :
    rowA n κ (zN (zOf w s h)) v * rowB κ (zN (zOf w s h)) v = rowC κ (zN (zOf w s h)) v := by
  have := hsat ⟨v, hv⟩
  rwa [matVec_chainA, matVec_chainB, matVec_chainC] at this

open Classical in
/-- Block `t` of a witness, as bits. -/
noncomputable def blk {κ : ℕ} (w : Fin (wLen κ) → E) (t : ℕ) : Pos Blake2sCircuit.m → Bool :=
  fun k ↦ decide ((if h : k.val + 16384 * t < wLen κ then w ⟨_, h⟩ else 0) = 1)

private theorem zN_blk {w : Fin (wLen κ) → E} (hw : ∀ u, BlockR1CS.IsBool (w u)) (s h : Digest)
    {t : ℕ} (ht : t < 2 ^ κ) (k : Pos Blake2sCircuit.m) :
    zN (zOf w s h) (k.val + 16384 * t) = ofBool E (blk w t k) := by
  have hk : k.val < 16384 := k.isLt
  have hv : k.val + 16384 * t < wLen κ := by rw [wLen_eq]; omega
  simp only [blk, zN_zOf_w w s h hv]
  rw [dite_eq_left hv]
  rcases hw ⟨_, hv⟩ with h0 | h1
  · rw [h0]; simp [ofBool]
  · rw [h1]; simp [ofBool]

variable [CharP E 2]

/-- A block of a satisfied chain R1CS satisfies the chain block, with `1` at `512`. -/
private theorem block_holds {w : Fin (wLen κ) → E} (hw : ∀ u, BlockR1CS.IsBool (w u))
    {s h : Digest} (hsat : ChainSat n κ w s h) {t : ℕ} (ht : t < 2 ^ κ) :
    chainBlock.toBlockR1CS.Holds (liftBlock E (blk w t)) ∧ blk w t constPos = true := by
  have hw' := wLen_eq κ
  have hL := ixLen_eq κ
  have hpub0 : zN (zOf w s h) (wLen κ) = 1 := by
    have := zN_zOf_pub w s h (u := 0) (by omega)
    rwa [add_zero, pubVal_zero] at this
  -- row 512 of block t
  have h512 : blk w t constPos = true := by
    have := rowEq hsat (v := 512 + 16384 * t) (by omega)
    unfold rowA rowB rowC at this
    simp only [show 512 + 16384 * t < wLen κ by omega, ↓reduceIte,
      show (512 + 16384 * t) % 16384 = 512 by omega, hpub0, mul_one] at this
    have hz := zN_blk hw s h ht constPos
    rw [constPos_val14, ← this] at hz
    cases hb : blk w t constPos
    · rw [hb] at hz; simp [ofBool] at hz
    · rfl
  refine ⟨fun k ↦ ?_, h512⟩
  have hlift : ∀ j : Pos Blake2sCircuit.m,
      liftBlock E (blk w t) j = zN (zOf w s h) (j.val + 16384 * t) :=
    fun j ↦ (zN_blk hw s h ht j).symm
  by_cases hk : k = constPos
  · subst hk
    rw [mulVec_A_liftBlock, mulVec_B_liftBlock, (rowOf_cpos_a_eval _).1,
      (rowOf_cpos_a_eval _).2, h512]
    simp [liftBlock, ofBool, h512]
  · have hkv : k.val ≠ 512 := fun he ↦ hk (Fin.ext he)
    have hk16 : k.val < 16384 := k.isLt
    have := rowEq hsat (v := k.val + 16384 * t) (by omega)
    unfold rowA rowB rowC at this
    simp only [show k.val + 16384 * t < wLen κ by omega, ↓reduceIte,
      show (k.val + 16384 * t) % 16384 = k.val by omega,
      show (k.val + 16384 * t) / 16384 = t by omega, hkv, pos_val14, blockA_eq hk,
      blockB_eq hk] at this
    rw [hlift k, ← this]
    simp only [BlockR1CS.mulVec, toBlockR1CS, hlift]

/-- **L-C2 (`chain_sound`).** A `0/1` witness satisfying the chain R1CS with public input
`(s, h)` proves `chainEnd s n = h`. -/
theorem chain_sound (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) {w : Fin (wLen κ) → E}
    (hw : ∀ u, BlockR1CS.IsBool (w u)) {s h : Digest} (hsat : ChainSat n κ w s h) :
    chainEnd s n = h := by
  have hw' := wLen_eq κ
  have hL := ixLen_eq κ
  have h8 := pow8_eq κ
  have hpub0 : zN (zOf w s h) (wLen κ) = 1 := by
    have := zN_zOf_pub w s h (u := 0) (by omega)
    rwa [add_zero, pubVal_zero] at this
  have hbit : ∀ t : ℕ, t < 2 ^ κ → ∀ k : ℕ, k < 16384 →
      zN (zOf w s h) (k + 16384 * t) = ofBool E (blk w t (pos k)) := fun t ht k hk ↦ by
    have := zN_blk hw s h ht (pos k)
    rwa [pos_val (show k < 2 ^ Blake2sCircuit.m from hk)] at this
  -- each block is one chain step
  have hstep : ∀ t : ℕ, t < 2 ^ κ →
      readDigest (blk w t) 256 = chainStep (readDigest (blk w t) 648) := fun t ht ↦ by
    obtain ⟨hh, h1⟩ := block_holds hw hsat ht
    exact block_sound _ hh h1
  -- the wiring: block 0 reads `s`
  have hin0 : readDigest (blk w 0) 648 = s := by
    refine digest_eq_of_dbit fun j hj ↦ ?_
    rw [dbit_readDigest _ _ hj]
    have := rowEq hsat (v := wLen κ + j) (by omega)
    unfold rowA rowB rowC at this
    simp only [show ¬ wLen κ + j < wLen κ by omega, ↓reduceIte, show wLen κ + j - wLen κ = j by omega,
      hj, show j < 2 ^ (8 + κ) by omega, show j < 2 ^ (8 + κ) + 256 by omega, hpub0, mul_one,
      show j % 256 = j by omega, show j / 256 = 0 by omega, mul_zero, add_zero] at this
    rw [show wLen κ + 1 + j = wLen κ + (1 + j) by omega, zN_zOf_pub w s h (by omega),
      pubVal_s s h hj, show 648 + j = (648 + j) + 16384 * 0 by omega,
      hbit 0 (by positivity) (648 + j) (by omega)] at this
    exact (ofBool_injective this).symm
  -- the wiring: block `t` reads block `t - 1`'s output
  have hin : ∀ t : ℕ, 1 ≤ t → t < 2 ^ κ →
      readDigest (blk w t) 648 = readDigest (blk w (t - 1)) 256 := fun t h1 ht ↦ by
    refine digest_eq_of_dbit fun j hj ↦ ?_
    rw [dbit_readDigest _ _ hj, dbit_readDigest _ _ hj]
    have := rowEq hsat (v := wLen κ + 256 * t + j) (by omega)
    unfold rowA rowB rowC at this
    simp only [show ¬ wLen κ + 256 * t + j < wLen κ by omega, ↓reduceIte,
      show wLen κ + 256 * t + j - wLen κ = 256 * t + j by omega,
      show ¬ 256 * t + j < 256 by omega, show 256 * t + j < 2 ^ (8 + κ) by omega,
      show 256 * t + j < 2 ^ (8 + κ) + 256 by omega, hpub0, mul_one,
      show (256 * t + j) % 256 = j by omega, show (256 * t + j) / 256 = t by omega] at this
    rw [show 256 + j + 16384 * (t - 1) = (256 + j) + 16384 * (t - 1) by omega,
      hbit (t - 1) (by omega) (256 + j) (by omega), hbit t ht (648 + j) (by omega)] at this
    exact (ofBool_injective this).symm
  -- the tail: block `n - 1`'s output is `h`
  have hout : readDigest (blk w (n - 1)) 256 = h := by
    refine digest_eq_of_dbit fun j hj ↦ ?_
    rw [dbit_readDigest _ _ hj]
    have := rowEq hsat (v := wLen κ + 2 ^ (8 + κ) + j) (by omega)
    unfold rowA rowB rowC at this
    simp only [show ¬ wLen κ + 2 ^ (8 + κ) + j < wLen κ by omega, ↓reduceIte,
      show wLen κ + 2 ^ (8 + κ) + j - wLen κ = 2 ^ (8 + κ) + j by omega,
      show ¬ 2 ^ (8 + κ) + j < 256 by omega, show ¬ 2 ^ (8 + κ) + j < 2 ^ (8 + κ) by omega,
      show 2 ^ (8 + κ) + j < 2 ^ (8 + κ) + 256 by omega, hpub0, mul_one,
      show 2 ^ (8 + κ) + j - 2 ^ (8 + κ) = j by omega] at this
    rw [hbit (n - 1) (by omega) (256 + j) (by omega), show wLen κ + 257 + j = wLen κ + (257 + j) by omega,
      zN_zOf_pub w s h (by omega), pubVal_h s h hj] at this
    exact ofBool_injective this
  -- induction along the chain
  have hchain : ∀ t, t < 2 ^ κ → readDigest (blk w t) 256 = chainEnd s (t + 1) := by
    intro t
    induction t with
    | zero => intro ht; rw [hstep 0 ht, hin0]; rfl
    | succ t ih =>
      intro ht
      rw [hstep (t + 1) ht, hin (t + 1) (by omega) ht, Nat.add_sub_cancel, ih (by omega), chainEnd, chainEnd,
        Function.iterate_succ_apply' chainStep (t + 1)]
  rw [← hout, hchain (n - 1) (by omega), Nat.sub_add_cancel hn]

end Sound

theorem mulVecA_def {m : ℕ} {R : Type} [CommRing R] (c : ProductCircuit m) (z : Pos m → R)
    (k : Pos m) : BlockR1CS.mulVec c.toBlockR1CS.A z k =
      ∑ j : Pos m, if (c.rowOf k).a.getLsbD j = true then z j else 0 := rfl

theorem mulVecB_def {m : ℕ} {R : Type} [CommRing R] (c : ProductCircuit m) (z : Pos m → R)
    (k : Pos m) : BlockR1CS.mulVec c.toBlockR1CS.B z k =
      ∑ j : Pos m, if (c.rowOf k).b.getLsbD j = true then z j else 0 := rfl

/-! ## L-C3 -/

section Complete

variable {n κ : ℕ}

/-- The honest witness: block `t` is the honest block of the chain step from `chainEnd s t`
(BLUEPRINT-R1 §2.3 `chainWitness`; padding blocks `t ≥ n` continue the chain). -/
noncomputable def chainWitness (s : Digest) (κ : ℕ) : Fin (wLen κ) → E :=
  fun u ↦ ofBool E (chainTrace (chainEnd s (u.val / 16384)) (pos (u.val % 16384)))

theorem chainWitness_isBool (s : Digest) (u : Fin (wLen κ)) :
    BlockR1CS.IsBool (chainWitness (E := E) s κ u) := by
  unfold chainWitness ofBool
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem chainTrace_in (d : Digest) {j : ℕ} (hj : j < 256) :
    chainTrace d (pos (648 + j)) = dbit d j := by
  rw [← dbit_readDigest (chainTrace d) 648 hj, readDigest_chainTrace]

theorem chainTrace_out (d : Digest) {j : ℕ} (hj : j < 256) :
    chainTrace d (pos (256 + j)) = dbit (chainStep d) j := by
  rw [← dbit_readDigest (chainTrace d) 256 hj, (block_complete (R := ZMod 2) d).2.2.2]

theorem chainEnd_succ' (s : Digest) {t : ℕ} (ht : 1 ≤ t) :
    chainStep (chainEnd s (t - 1)) = chainEnd s t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, chainEnd, chainEnd, Function.iterate_succ_apply']

variable [CharP E 2]

/-- **L-C3 (`chain_complete`).** The honest witness satisfies the chain R1CS with public input
`(s, chainEnd s n)`. -/
theorem chain_complete (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) (s : Digest) :
    ChainSat n κ (chainWitness (E := E) s κ) s (chainEnd s n) := by
  have hw' := wLen_eq κ
  have hL := ixLen_eq κ
  have h8 := pow8_eq κ
  intro x
  rw [matVec_chainA, matVec_chainB, matVec_chainC]
  have hv := x.isLt
  set Z := zOf (chainWitness (E := E) s κ) s (chainEnd s n)
  have hpub0 : zN Z (wLen κ) = 1 := by
    have := zN_zOf_pub (chainWitness (E := E) s κ) s (chainEnd s n) (u := 0) (by omega)
    rwa [add_zero, pubVal_zero] at this
  have hz : ∀ t, t < 2 ^ κ → ∀ k, k < 16384 →
      zN Z (k + 16384 * t) = ofBool E (chainTrace (chainEnd s t) (pos k)) := fun t ht k hk ↦ by
    rw [zN_zOf_w _ _ _ (by omega)]
    simp only [chainWitness, show (k + 16384 * t) / 16384 = t by omega,
      show (k + 16384 * t) % 16384 = k by omega]
  unfold rowA rowB rowC
  by_cases h0 : x.val < wLen κ
  · simp only [h0, ↓reduceIte]
    have ht : x.val / 16384 < 2 ^ κ := by omega
    have hxv : x.val = x.val % 16384 + 16384 * (x.val / 16384) := by omega
    by_cases h512 : x.val % 16384 = 512
    · rw [ite_eq_left h512, ite_eq_left h512, hpub0, mul_one, hxv, hz _ ht _ (by omega), h512,
        show (pos 512 : Pos Blake2sCircuit.m) = constPos from Fin.ext (pos_val (by decide))]
      have := (block_complete (R := E) (chainEnd s (x.val / 16384))).2.1
      rw [chainTrace] at this ⊢
      simp [this, ofBool]
    · rw [ite_eq_right h512, ite_eq_right h512]
      set k : Pos Blake2sCircuit.m := pos (x.val % 16384)
      have hkv : k.val = x.val % 16384 := pos_val (show x.val % 16384 < 2 ^ Blake2sCircuit.m by
        show _ < 16384; omega)
      have hk : k ≠ constPos := fun he ↦ h512 (by rw [← hkv, he]; rfl)
      have hlift : ∀ j : Pos Blake2sCircuit.m, zN Z (j.val + 16384 * (x.val / 16384)) =
          liftBlock E (chainTrace (chainEnd s (x.val / 16384))) j := fun j ↦ by
        rw [hz _ ht _ j.isLt, pos_val14]; rfl
      have hhold := (block_complete (R := E) (chainEnd s (x.val / 16384))).1 k
      have hc : zN Z x.val =
          ofBool E (chainTrace (chainEnd s (x.val / 16384)) (pos (x.val % 16384))) := by
        have := hz _ ht (x.val % 16384) (by omega)
        rwa [← hxv] at this
      simp only [blockA_eq hk, blockB_eq hk, hlift]
      rw [hc]
      rw [mulVecA_def, mulVecB_def,
        show liftBlock E (chainTrace (chainEnd s (x.val / 16384))) k =
          ofBool E (chainTrace (chainEnd s (x.val / 16384)) k) from rfl] at hhold
      rw [show (pos (x.val % 16384) : Pos Blake2sCircuit.m) = k from rfl]
      exact hhold
  · simp only [h0, ↓reduceIte]
    by_cases h1 : x.val - wLen κ < 256
    · rw [ite_eq_left h1, ite_eq_left (by omega : x.val - wLen κ < 2 ^ (8 + κ)),
        ite_eq_left (by omega : x.val - wLen κ < 2 ^ (8 + κ) + 256), hpub0, mul_one,
        show wLen κ + 1 + (x.val - wLen κ) = wLen κ + (1 + (x.val - wLen κ)) by omega,
        zN_zOf_pub _ _ _ (by omega), pubVal_s _ _ h1,
        show 648 + (x.val - wLen κ) % 256 + 16384 * ((x.val - wLen κ) / 256) =
          (648 + (x.val - wLen κ)) + 16384 * 0 by omega,
        hz 0 (by positivity) _ (by omega), chainTrace_in _ h1]
      rfl
    · rw [ite_eq_right h1]
      by_cases h2 : x.val - wLen κ < 2 ^ (8 + κ)
      · set i := x.val - wLen κ
        have ht : i / 256 < 2 ^ κ := by omega
        rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left (by omega : i < 2 ^ (8 + κ) + 256), hpub0, mul_one,
          show 256 + i % 256 + 16384 * (i / 256 - 1) = (256 + i % 256) + 16384 * (i / 256 - 1)
            by omega, hz _ (by omega) _ (by omega), chainTrace_out _ (Nat.mod_lt _ (by omega)),
          chainEnd_succ' s (by omega),
          show 648 + i % 256 + 16384 * (i / 256) = (648 + i % 256) + 16384 * (i / 256) by omega,
          hz _ ht _ (by omega), chainTrace_in _ (Nat.mod_lt _ (by omega))]
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : x.val - wLen κ < 2 ^ (8 + κ) + 256
        · set i := x.val - wLen κ
          rw [ite_eq_left h3, ite_eq_left h3, ite_eq_left h3, hpub0, mul_one,
            show 256 + (i - 2 ^ (8 + κ)) + 16384 * (n - 1) =
              (256 + (i - 2 ^ (8 + κ))) + 16384 * (n - 1) by omega,
            hz _ (by omega) _ (by omega), chainTrace_out _ (by omega), chainEnd_succ' s hn,
            show wLen κ + 257 + (i - 2 ^ (8 + κ)) = wLen κ + (257 + (i - 2 ^ (8 + κ))) by omega,
            zN_zOf_pub _ _ _ (by omega), pubVal_h _ _ (by omega)]
        · rw [ite_eq_right h3, ite_eq_right h3, ite_eq_right h3, zero_mul]

end Complete

/-! ## The witness bits, computed -/

/-- The witness bits of one block: the honest block of the step from `d`, `2 ^ 14` bits. -/
@[irreducible] def blockBits (d : Digest) : Array Bool :=
  Array.ofFn fun k : Fin 16384 ↦ (fastTrace d).getD k.val false

theorem blockBits_size (d : Digest) : (blockBits d).size = 16384 := by
  unfold blockBits; exact Array.size_ofFn

theorem blockBits_get (d : Digest) {k : ℕ} (hk : k < 16384) :
    (blockBits d)[k]? = some (chainTrace d (pos k)) := by
  unfold blockBits
  rw [Array.getElem?_ofFn, dite_eq_left hk]
  have := fastTrace_eq d (pos k)
  rw [pos_val (show k < 2 ^ Blake2sCircuit.m from hk)] at this
  rw [Array.getD_eq_getD_getElem?, this, Option.getD_some]

/-- The bits of the first `b` blocks from `s`, and the digest after them. -/
def chainBitsUpTo (s : Digest) (b : ℕ) : Array Bool × Digest :=
  Nat.fold b (fun _ _ p ↦ (p.1 ++ blockBits p.2, chainStep p.2)) (#[], s)

theorem chainBitsUpTo_succ (s : Digest) (b : ℕ) : chainBitsUpTo s (b + 1) =
    ((chainBitsUpTo s b).1 ++ blockBits (chainBitsUpTo s b).2, chainStep (chainBitsUpTo s b).2) := by
  unfold chainBitsUpTo
  rw [Nat.fold_succ]

theorem chainBitsUpTo_spec (s : Digest) (b : ℕ) :
    (chainBitsUpTo s b).2 = chainEnd s b ∧ (chainBitsUpTo s b).1.size = 16384 * b ∧
    ∀ u, u < 16384 * b → (chainBitsUpTo s b).1[u]? =
      some (chainTrace (chainEnd s (u / 16384)) (pos (u % 16384))) := by
  induction b with
  | zero =>
    refine ⟨rfl, rfl, fun u hu ↦ absurd hu (by omega)⟩
  | succ b ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [chainBitsUpTo_succ, h1]
    refine ⟨?_, ?_, fun u hu ↦ ?_⟩
    · rw [chainEnd, chainEnd, Function.iterate_succ_apply']
    · rw [Array.size_append, h2, blockBits_size]; ring
    · by_cases hu' : u < 16384 * b
      · rw [Array.getElem?_append_left (by rw [h2]; exact hu'), h3 u hu']
      · rw [Array.getElem?_append_right (by rw [h2]; omega), h2,
          blockBits_get _ (by omega), show u / 16384 = b by omega,
          show u % 16384 = u - 16384 * b by omega]

/-- The honest witness as bits, block after block (the prover's computation; `fastTrace` per
block). -/
def chainWitnessBits (s : Digest) (κ : ℕ) : Array Bool := (chainBitsUpTo s (2 ^ κ)).1

theorem chainWitnessBits_size (s : Digest) (κ : ℕ) : (chainWitnessBits s κ).size = wLen κ := by
  rw [chainWitnessBits, (chainBitsUpTo_spec s _).2.1, wLen_eq]

/-- **The computed witness is the honest witness**, bit by bit. -/
theorem chainWitnessBits_eq (s : Digest) (κ : ℕ) (u : Fin (wLen κ)) :
    (chainWitnessBits s κ)[u.val]? =
      some (chainTrace (chainEnd s (u.val / 16384)) (pos (u.val % 16384))) :=
  (chainBitsUpTo_spec s _).2.2 u.val (by have := u.isLt; have := wLen_eq κ; omega)

end SpartanChain
