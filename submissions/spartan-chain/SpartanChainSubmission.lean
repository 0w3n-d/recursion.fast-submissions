/-
# The submission and its certificate (BLUEPRINT-R1 §1.4, §10 `Submission.lean`)

The assembly of the entry, parametrised by the parts other modules supply, so that the final
instantiation is one line once they exist:

* `LV : LeafVerifier`, the leaf size and the SNARK verifier (`Verifier.lean`);
* `proveLeaf s n h : OProg ByteArray`, the SNARK prover for `n ≥ 1` (`Prover.lean`);
* `Facts LV proveLeaf`, the facts proved elsewhere:
  * `size_zero`: `leafSize 0 = 80`;
  * `leaf_complete`: for every oracle, the honest SNARK has the right size and is accepted
    (`Completeness.lean`);
  * `ks`: a knowledge state with error `2^-129` for `Rel (vb LV)` (`Soundness/KS.lean`);
  * `queries`: the SNARK verifier asks at most `2^14` queries (L-Q1).

What this module proves, for every such instantiation:
* `Vb_eq`: the instantiated verifier is `vb LV` (`SpartanChainVerifierTop`);
* `fits_of_rel`: every witness of the relation fits the extractor's output format;
* `complete`: perfect completeness, from `leaf_complete` and node completeness;
* `V_queries`: at most `2^14` queries on every input;
* `certificate`: the contract's `Certificate` (the amended `KS`, with `ε` a parameter of
  `KState`). `E`, `img`, `fuel` and `computes` are the library's, as in the S2a baseline;
* `certificateR_of`: `CertificateR` against any rendered claim within the declared numbers.
The honest prover (§1.4) is `P`: a leaf is its 80-byte header (`enc64 0 ‖ s ‖ enc64 n ‖ h`,
`h = chainEnd s n` recomputed) followed by the SNARK, which is absent when `n = 0`; a node is its
canonical encoding.
-/
import SpartanChainVerifierTop
import SpartanChainOracle

open scoped NNReal

namespace SpartanChain
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

/-! ## The honest prover (§1.4) -/

/-- The bytes of a leaf proof: the header `encode (.leaf s n) ‖ h` (80 bytes), then the SNARK. -/
def leafBytes (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) : Proof :=
  encodeF (.leaf s n) ++ ⟨h.toArray⟩ ++ πS

/-- **The honest prover.** A leaf: the header with `h = chainEnd s n`, and `proveLeaf`'s SNARK when
`n ≥ 1`. A node: its canonical encoding. -/
def P (proveLeaf : Digest → ℕ → Digest → OProg ByteArray) (_ : Digest) : Wit → OProg Proof
  | .leaf s n =>
    if n = 0 then .ret (leafBytes s 0 s ByteArray.empty)
    else proveLeaf s n (chainEnd s n) >>= fun πS => .ret (leafBytes s n (chainEnd s n) πS)
  | .node c₁ c₂ π₁ π₂ => .ret (encodeF (.node c₁ c₂ π₁ π₂))

/-! ## Parsing the honest leaf proof -/

private theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem leafBytes_toList (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) :
    (leafBytes s n h πS).data.toList =
      (encode (.leaf s n)).data.toList ++ h.toList ++ πS.data.toList := by
  rw [leafBytes, toList_append, toList_append, encodeF_eq]; rfl

theorem leafBytes_size (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) :
    (leafBytes s n h πS).size = 80 + πS.size := by
  rw [size_eq_length, leafBytes_toList, List.length_append, List.length_append,
    ← size_eq_length, ← size_eq_length, WitnessSending.size_encode_leaf]
  simp

/-- The honest leaf proof parses back to its parts. -/
theorem leafBytes_parse (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) (h : Digest) (πS : ByteArray) :
    tagWord (leafBytes s n h πS) = 0 ∧ leafN (leafBytes s n h πS) = n ∧
      leafS (leafBytes s n h πS) = s ∧ leafH (leafBytes s n h πS) = h ∧
      leafSnark (leafBytes s n h πS) = πS := by
  set π := leafBytes s n h πS
  set e := encode (.leaf s n)
  have he : e.data.toList.length = 48 := by
    rw [← size_eq_length]; exact WitnessSending.size_encode_leaf s n
  have h48 : π.data.toList.take 48 = e.data.toList.take 48 := by
    rw [leafBytes_toList, List.append_assoc, List.take_append_of_le_length (le_of_eq he.symm)]
  have hte : tagWord e = 0 := by
    rw [tagWord_eq, take8_encode, ofLE_wordBytes]; rfl
  have hde := decode_leaf (show 48 ≤ e.size by rw [WitnessSending.size_encode_leaf]) hte
  rw [decode_encode _ (show (Wit.leaf s n).Fits from hn)] at hde
  obtain ⟨hsE, hnE⟩ : s = leafS e ∧ n = leafN e := by
    injection hde with hw; injection hw with h1 h2; exact ⟨h1, h2⟩
  obtain ⟨ht, hN, hS⟩ := parse48_congr h48
  refine ⟨ht.trans hte, hN.trans hnE.symm, hS.trans hsE.symm, ?_, ?_⟩
  · ext i hi
    have he' : (encode (Wit.leaf s n)).data.toList.length = 48 := he
    simp only [leafH, digestFrom, Vector.getElem_ofFn, proof_getD_eq, π, leafBytes_toList]
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), he',
      List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · have h80 : (encodeF (.leaf s n) ++ (⟨h.toArray⟩ : ByteArray)).size = 80 := by
      have := leafBytes_size s n h ByteArray.empty
      rwa [leafBytes, ByteArray.append_empty, ByteArray.size_empty] at this
    rw [leafSnark, show π.size = 80 + πS.size from leafBytes_size s n h πS]
    exact ByteArray.extract_append_eq_right h80.symm (by rw [h80])

/-! ## The submission -/

/-- The proved knowledge error, `2^-129` (§5.5, §9.4). -/
noncomputable def εR1 : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 129

/-- The verifier query bound, `2^14` (§6.3, L-Q1). -/
def qVR1 : ℕ := 2 ^ 14

/-- **The submission** for a leaf verifier and a SNARK prover: `V` (`SpartanChainVerifierTop`),
the honest prover `P`, and the library's extractor, image and fuel. -/
noncomputable def submission (LV : LeafVerifier)
    (proveLeaf : Digest → ℕ → Digest → OProg ByteArray) : Submission where
  V := V LV
  P := P proveLeaf
  E := WitnessSending.E
  img := WitnessSending.img
  ε := εR1
  qV := qVR1
  fuel := WitnessSending.fuel

/-- **The facts the other modules prove**, as hypotheses of the certificate. -/
structure Facts (LV : LeafVerifier) (proveLeaf : Digest → ℕ → Digest → OProg ByteArray) : Prop where
  /-- `leafSize 0 = 80`: the zero-step leaf is its header (§7). -/
  size_zero : LV.size 0 = 80
  /-- Leaf completeness, for every oracle: the honest SNARK of a chain of `1 ≤ n ≤ chainCap` steps
  has `leafSize n − 80` bytes and is accepted. -/
  leaf_complete : ∀ (H : ByteArray → Digest) (s : Digest) (n : ℕ), 1 ≤ n → n ≤ chainCap →
    80 + ((proveLeaf s n (chainEnd s n)).run H).size = LV.size n ∧
      (LV.prog s n (chainEnd s n) ((proveLeaf s n (chainEnd s n)).run H)).run H = true
  /-- A knowledge state with error `2^-129` (`Soundness/KS.lean`). -/
  ks : Nonempty (KState (Rel (vb LV)) (V LV) WitnessSending.E εR1)
  /-- L-Q1: the SNARK verifier asks at most `2^14` queries. -/
  queries : ∀ (H : ByteArray → Digest) s n h sn, ((LV.prog s n h sn).queries H).length ≤ qVR1

variable (LV : LeafVerifier) (proveLeaf : Digest → ℕ → Digest → OProg ByteArray)

theorem Vb_eq : (submission LV proveLeaf).Vb = vb LV := Vb_eq_vb LV _ rfl

/-- Every witness of the relation fits the extractor's output format. -/
theorem fits_of_rel {c : Digest} {w : Wit} (h : Rel (submission LV proveLeaf).Vb c w) : w.Fits := by
  rw [Vb_eq] at h
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ π₁ π₂ => exact ⟨size_le_of_vb LV h.2.1, size_le_of_vb LV h.2.2⟩

/-- **Perfect completeness**, for every oracle function. -/
theorem complete (F : Facts LV proveLeaf) :
    Complete (Rel (submission LV proveLeaf).Vb) (submission LV proveLeaf).P
      (submission LV proveLeaf).V := by
  intro H c w hR
  rw [Vb_eq] at hR
  show (V LV c ((P proveLeaf c w).run H)).run H = true
  cases w with
  | node c₁ c₂ π₁ π₂ =>
    have hπ : (P proveLeaf c (.node c₁ c₂ π₁ π₂)).run H = encode (.node c₁ c₂ π₁ π₂) := by
      simp [P, OProg.run, encodeF_eq]
    rw [hπ, V_eq_ret LV (by rw [tagWord_encode_node]; omega)]
    exact check_encode_node LV hR
  | leaf s n =>
    obtain ⟨hn, hc⟩ := hR
    have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
    by_cases h0 : n = 0
    · subst h0
      have hπ : (P proveLeaf c (.leaf s 0)).run H = leafBytes s 0 s ByteArray.empty := by
        simp [P, OProg.run]
      obtain ⟨ht, hN, hS, hH, -⟩ := leafBytes_parse s (show 0 < 2 ^ 64 by decide) s .empty
      have hsz := leafBytes_size s 0 s .empty
      rw [hπ, V, ite_eq_right (by rw [hsz]; simp), ite_eq_left ht, leafProg]
      have hh : leafHeaderOK LV c (leafBytes s 0 s .empty) = true :=
        (leafHeaderOK_iff LV).mpr ⟨by rw [hN]; exact Nat.zero_le _,
          by rw [hsz, hN, F.size_zero]; rfl, by rw [hH, hN, hc]; rfl⟩
      rw [ite_eq_left hh, ite_eq_left hN]
      simp [OProg.run, hS, hH]
    · set πS := (proveLeaf s n (chainEnd s n)).run H
      have hπ : (P proveLeaf c (.leaf s n)).run H = leafBytes s n (chainEnd s n) πS := by
        simp [P, h0, OProg.run_bind, πS]; rfl
      obtain ⟨ht, hN, hS, hH, hSn⟩ := leafBytes_parse s hn64 (chainEnd s n) πS
      obtain ⟨hsize, hacc⟩ := F.leaf_complete H s n (Nat.one_le_iff_ne_zero.mpr h0) hn
      have hsz := leafBytes_size s n (chainEnd s n) πS
      rw [hπ, V, ite_eq_right (by omega), ite_eq_left ht, leafProg]
      have hh : leafHeaderOK LV c (leafBytes s n (chainEnd s n) πS) = true :=
        (leafHeaderOK_iff LV).mpr ⟨by rw [hN]; exact hn, by rw [hsz, hN, hsize], by rw [hH, hN, hc]⟩
      rw [ite_eq_left hh, ite_eq_right (by rw [hN]; exact h0), hS, hN, hH, hSn]
      exact hacc

/-- **The query bound**: at most `2^14` queries on every input and oracle. -/
theorem V_queries (F : Facts LV proveLeaf) (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((V LV c π).queries H).length ≤ qVR1 := by
  by_cases hl : 8 ≤ π.size ∧ tagWord π = 0
  · rw [V, ite_eq_right (by omega), ite_eq_left hl.2, leafProg_queries]
    split_ifs
    · exact F.queries ..
    · simp
  · rw [V_queries_of_not_leaf LV H hl]; simp

theorem εR1_le_errorCap : εR1 ≤ errorCap := by
  unfold εR1 errorCap
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by norm_num)) (by norm_num)

/-- **The certificate** of the amended contract. -/
theorem certificate (F : Facts LV proveLeaf) : Certificate (submission LV proveLeaf) where
  secure := by
    show KS (Rel (submission LV proveLeaf).Vb) (V LV) WitnessSending.E εR1 qVR1
    rw [Vb_eq]
    exact ⟨F.ks, V_queries LV proveLeaf F⟩
  complete := complete LV proveLeaf F
  computes := WitnessSending.computes
  cap := ⟨εR1_le_errorCap, show qVR1 ≤ 2 ^ 16 by decide,
    fun _ => Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40),
    show WitnessSending.img.byteSize ≤ imageCap by decide⟩

/-- **The certificate against a rendered claim** whose numbers are at least the submission's and
whose fuel is within the budget. -/
theorem certificateR_of (F : Facts LV proveLeaf) (D : Declared) (hi : WitnessSending.img = D.img)
    (hε : εR1 ≤ D.ε) (hq : qVR1 ≤ D.qV)
    (hf : ∀ t, 8 ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t) :
    CertificateR D (submission LV proveLeaf) :=
  ⟨certificate LV proveLeaf F, hi, hε, hq, hf⟩

/-- The declared error of the claim, `1 / 2^128` as rendered, bounds the proved `2^-129`. -/
theorem εR1_le_declared : εR1 ≤ (1 : ℝ≥0) / 340282366920938463463374607431768211456 := by
  unfold εR1
  rw [one_div, inv_pow]
  exact inv_anti₀ (by positivity) (by norm_num)

/-! ## Controls: the claim binding (negative; no fact needed) -/

/-- The claim of `claim.json` as a `Declared` literal (the image of `extractor.bin`). -/
noncomputable def claimR1 : Declared where
  img := ⟨[0x00100313, 0x03f31313, 0x02033583, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
    0x00000073], []⟩
  ε := (1 : ℝ≥0) / 340282366920938463463374607431768211456
  qV := 16384
  fuel t := 8 + 0 * t

/-- **Positive**: given the facts, the claim of `claim.json` is certified. -/
theorem certificateR_claim (F : Facts LV proveLeaf) :
    CertificateR claimR1 (submission LV proveLeaf) :=
  certificateR_of LV proveLeaf F claimR1 rfl εR1_le_declared (show qVR1 ≤ 16384 by decide)
    fun t => ⟨show 8 ≤ 8 + 0 * t by omega, show 8 + 0 * t ≤ 2 ^ 40 + 2 ^ 8 * t by omega⟩

/-- **Negative**: one image bit flipped, a declared fuel of 7, or a declared query bound of
`2^14 − 1`, is not certified, whatever the facts. -/
theorem claim_negatives :
    ¬ CertificateR { claimR1 with
        img := ⟨[0x00100313, 0x03f31313, 0x02033582, 0x00758593, 0x0035d593, 0x02830513,
          0x00000293, 0x00000073], []⟩ } (submission LV proveLeaf) ∧
    ¬ CertificateR { claimR1 with fuel := fun _ => 7 } (submission LV proveLeaf) ∧
    ¬ CertificateR { claimR1 with qV := 16383 } (submission LV proveLeaf) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simpa [submission, WitnessSending.img] using h.img
  · exact absurd (h.bounds.2.2 0).1 (by simp [submission, WitnessSending.fuel])
  · exact absurd h.bounds.2.1 (by simp [submission, qVR1])

end SpartanChain
