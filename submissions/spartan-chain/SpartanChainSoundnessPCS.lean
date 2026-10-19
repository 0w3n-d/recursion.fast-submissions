import SpartanChainLigero
import SpartanChainSoundnessLog
import SpartanChainChain
import Mathlib.Basic.NNReal.Basic

/-!
# PCS-level soundness facts (blueprint §9.1–§9.2: R0, R7, the far and close modes, decoding)

Everything here is about a committed matrix `U ∈ F^{m×N}` (in the protocol, the filled matrix
`U_T` read off the log prefix, `filled`) and the transcript's answers, independent of how the
potential `μ` is assembled. `κ ≤ 20` throughout (`n ≤ chainCap`).

* `filled`, `filled_of_colL`: the filled matrix of §9.1 (column `c` decoded from `colOr`, and the
  column a verified path opens, by `Merkle.open_binding(_prefix)`).
* **R0, far mode** (`r0_answers`): if `U` is not `e`-close, at most a `2^-169` fraction of the
  `m`-tuples of 32-byte answers make `Σ_i chE(a_i)·U_i` `e`-close (L-RS2 composed with the exact
  `2^64`-to-one map `chE`).
* **Close mode** (`Decodes`, `decode_exists`, `decode_unique`, `qDec`, `qDec_spec`): an `e`-close
  `U` has exactly one decoded message matrix, with entries in `F` (L-RS4).
* **The difference sets** `Dset κ U w msg = {c : Enc(msg)_c ≠ Σ_i w_i U[i][c]}`: `far_Dset_card`
  (`> e` in far mode, for every `ū`), `close_Dset_card` (`≥ d − e` for a `v` other than the
  decoded combination), `accept_not_mem` (an accepted opening of `U`'s column lies outside both).
* **R7** (`r7_count`, `r7_far`, `r7_close`): the `J`-tuples of index answers whose `t = 260`
  indices all miss `D` are exactly `(N − |D|)^t · 2^{256 J} / N^t` (`card_idx_fiber` per answer);
  hence `≤ (4/5)·2^-129` of all tuples when `|D| > e` and `≤ 2^-328` when `|D| ≥ d − e`.
* `eval_of_correct`: with the decoded `v`, `Σ_j b_j v_j = Σ_{i,j} a_i b_j Q[i][j]`.
-/

namespace SpartanChain.SoundnessPCS

open RecursionFast RS PCS Transcript Ligero Finset

/-- The matrix over `EF`. -/
def UE (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) : Fin (rows κ) → Fin (cols κ) → EF :=
  fun i c => EF.ofF (U i c)

theorem UE_sum_apply (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (w : Fin (rows κ) → EF)
    (c : Fin (cols κ)) : (∑ i, w i • UE κ U i) c = ∑ i, w i * EF.ofF (U i c) := by
  simp [UE, Finset.sum_apply]

theorem ofF_injective : Function.Injective EF.ofF := by
  intro a b h
  exact (algebraMap F EF).injective (by simpa [EF.algebraMap_eq_ofF] using h)

theorem msgLen_le_cols (κ : ℕ) : 2 ^ lk κ ≤ Fintype.card (Fin (cols κ)) := by
  rw [Fintype.card_fin, cols_eq]; unfold msgLen; omega

theorem dom_inj (κ : ℕ) (hκ : κ ≤ 20) : Function.Injective (dom (cols κ)) :=
  dom_injective ((cols_le κ hκ).trans (by norm_num))

/-! ### The filled matrix (§9.1) -/

/-- `U_L(root)`: column `c` is the column read off `L₀` under `root`, decoded to `m` elements of
`F` (a missing column reads as the empty byte string). -/
def filled (κ : ℕ) (L₀ : Log) (root : Label) (i : Fin (rows κ)) (c : Fin (cols κ)) : F :=
  (readFs (Merkle.colOr L₀ (8 * rows κ) root (lN κ) ByteArray.empty c) 0 (rows κ)).getD i 0

/-- A column read off the log is the filled matrix's column. -/
theorem filled_of_colL {κ : ℕ} {L₀ : Log} {root : Label} {c : Fin (cols κ)} {col : ByteArray}
    (h : Merkle.colL L₀ (8 * rows κ) root (lN κ) c = some col) (i : Fin (rows κ)) :
    filled κ L₀ root i c = (readFs col 0 (rows κ)).getD i 0 := by
  simp [filled, Merkle.colOr, h]

/-! ### R0: the far mode -/

theorem card_chE_vec (m : ℕ) (r : Fin m → EF) :
    (univ.filter fun a : Fin m → Digest => (fun i => chE (a i)) = r).card = (2 ^ 64) ^ m := by
  classical
  rw [← Fintype.card_subtype]
  have : Fintype.card {a : Fin m → Digest // (fun i => chE (a i)) = r} =
      Fintype.card {a : Fin m → Digest // ∀ i, chE (a i) = r i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun a => funext_iff)
  rw [this, Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun i (x : Digest) => chE x = r i)),
    Fintype.card_pi]
  simp only [Fintype.card_subtype, card_chE_fiber, prod_const, card_univ, Fintype.card_fin]

/-- **R0 in answers** (far mode): if `U` is not `e`-close, the `m`-tuples of answers whose
challenges `r_i = chE(a_i)` make `Σ_i r_i U_i` `e`-close are at most a `2^-169` fraction. -/
theorem r0_answers {κ : ℕ} (hκ : κ ≤ 20) (U : Fin (rows κ) → Fin (cols κ) → F)
    (hfar : ¬ eClose (code κ) (UE κ U) (radius κ)) :
    Nat.card {a : Fin (rows κ) → Digest //
        Close (code κ) (radius κ) (∑ i, chE (a i) • UE κ U i)} * 2 ^ 169 ≤
      (2 ^ 256) ^ rows κ := by
  classical
  have hr := r0_far_bad κ hκ (UE κ U) hfar
  set S := univ.filter fun r : Fin (rows κ) → EF => Close (code κ) (radius κ) (∑ i, r i • UE κ U i)
  have hS : Nat.card {r : Fin (rows κ) → EF // Close (code κ) (radius κ)
      (∑ i, r i • UE κ U i)} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount := card_mem_of_fiber (fun (a : Fin (rows κ) → Digest) i => chE (a i)) _
    (card_chE_vec (rows κ)) S
  have ha : Nat.card {a : Fin (rows κ) → Digest //
      Close (code κ) (radius κ) (∑ i, chE (a i) • UE κ U i)} =
      (univ.filter fun a : Fin (rows κ) → Digest => (fun i => chE (a i)) ∈ S).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext a; simp [S]
  rw [ha, hcount]
  rw [hS] at hr
  have e1 : (2 : ℕ) ^ 256 = 2 ^ 192 * 2 ^ 64 := by rw [← pow_add]
  calc S.card * (2 ^ 64) ^ rows κ * 2 ^ 169 = S.card * 2 ^ 169 * (2 ^ 64) ^ rows κ :=
        Nat.mul_right_comm _ _ _
    _ ≤ (2 ^ 192) ^ rows κ * (2 ^ 64) ^ rows κ := Nat.mul_le_mul_right _ hr
    _ = (2 ^ 256) ^ rows κ := by rw [e1, mul_pow]

/-! ### The close mode: unique decoding -/

/-- `Q` (a message matrix over `F`) decodes `U` off the set `S` of at most `e` columns. -/
def Decodes (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (Q : Fin (rows κ) → Fin (2 ^ lk κ) → F)
    (S : Finset (Fin (cols κ))) : Prop :=
  IsDecomp (code κ) (UE κ U) (radius κ) S fun i =>
    enc (kap (lk κ)) (lk κ) (dom (cols κ)) fun j => EF.ofF (Q i j)

/-- **Decoding exists** in the close mode, with the messages in `F` (`close_in_K`, `msg_in_K`). -/
theorem decode_exists {κ : ℕ} (hκ : κ ≤ 20) {U : Fin (rows κ) → Fin (cols κ) → F}
    (h : eClose (code κ) (UE κ U) (radius κ)) : ∃ Q S, Decodes κ U Q S := by
  obtain ⟨S, c, hS, hc, hag⟩ := h
  have hK : ∀ i x, c i x ∈ Set.range (algebraMap F EF) :=
    close_in_K (rsCode_kRational _ _ _) (code_minDist κ hκ)
      (by have := three_radius_lt κ; omega)
      (fun i x => ⟨U i x, by simp [UE, EF.algebraMap_eq_ofF]⟩) ⟨hS, hc, hag⟩
  have hmsg : ∀ i, ∃ q : Fin (2 ^ lk κ) → F,
      enc (kap (lk κ)) (lk κ) (dom (cols κ)) (fun j => EF.ofF (q j)) = c i := by
    intro i
    obtain ⟨msg, hmsg⟩ := hc i
    have hm := msg_in_K (kap (lk κ)) (lk κ) (dom_inj κ hκ) (msgLen_le_cols κ) (msg := msg)
      (fun x => by rw [show enc (kap (lk κ)) (lk κ) (dom (cols κ)) msg = c i from hmsg]
                   exact hK i x)
    choose q hq using hm
    refine ⟨q, ?_⟩
    rw [← show enc (kap (lk κ)) (lk κ) (dom (cols κ)) msg = c i from hmsg]
    congr 1; funext j; rw [← hq j, EF.algebraMap_eq_ofF]
  choose Q hQ using hmsg
  exact ⟨Q, S, hS, fun i => by beta_reduce; rw [hQ i]; exact hc i,
    fun i x hx => by beta_reduce; rw [hQ i]; exact hag i x hx⟩

/-- **Decoding is unique** (`close_unique`, `enc_injective`). -/
theorem decode_unique {κ : ℕ} (hκ : κ ≤ 20) {U : Fin (rows κ) → Fin (cols κ) → F}
    {Q Q' : Fin (rows κ) → Fin (2 ^ lk κ) → F} {S S' : Finset (Fin (cols κ))}
    (h : Decodes κ U Q S) (h' : Decodes κ U Q' S') : Q = Q' := by
  have hc := close_unique (code_minDist κ hκ) (by have := three_radius_lt κ; omega) h h'
  funext i j
  have hi := enc_injective (E := EF) (kap (lk κ)) (lk κ) (dom_inj κ hκ) (msgLen_le_cols κ)
    (congrFun hc i)
  exact ofF_injective (congrFun hi j)

/-- Non-vacuity: the honestly encoded matrix of any `Q` decodes to `Q` with `S = ∅`. -/
theorem decodes_honest (κ : ℕ) (Q : Fin (rows κ) → Fin (2 ^ lk κ) → F) :
    Decodes κ (fun i c => enc (kap (lk κ)) (lk κ) (dom (cols κ)) (Q i) c) Q ∅ := by
  refine ⟨by simp, fun i => enc_mem_rsCode _ _ _ _, fun i x _ => ?_⟩
  simp only [UE, ← EF.algebraMap_eq_ofF]
  exact (enc_algebraMap _ _ _ (Q i) x).symm

open Classical in
/-- **The decoded message matrix** `q_dec` (non-constructive; `0` when `U` is far). -/
noncomputable def qDec (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) :
    Fin (rows κ) → Fin (2 ^ lk κ) → F :=
  if h : ∃ Q S, Decodes κ U Q S then Classical.choose h else 0

theorem qDec_spec {κ : ℕ} (hκ : κ ≤ 20) {U : Fin (rows κ) → Fin (cols κ) → F}
    (h : eClose (code κ) (UE κ U) (radius κ)) : ∃ S, Decodes κ U (qDec κ U) S := by
  have he := decode_exists hκ h
  rw [qDec]
  split
  · exact Classical.choose_spec ‹_›
  · contradiction

/-- Any decoding is `q_dec`. -/
theorem qDec_eq {κ : ℕ} (hκ : κ ≤ 20) {U : Fin (rows κ) → Fin (cols κ) → F}
    {Q : Fin (rows κ) → Fin (2 ^ lk κ) → F} {S : Finset (Fin (cols κ))} (h : Decodes κ U Q S) :
    qDec κ U = Q := by
  obtain ⟨S', h'⟩ := qDec_spec hκ ⟨S, _, h⟩
  exact decode_unique hκ h' h

/-! ### The difference sets -/

/-- `{c : Enc(msg)_c ≠ Σ_i w_i U[i][c]}`: `D_far` with `(w, msg) = (r, ū)`, `D_close` with
`(a, v)`. -/
def Dset (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (w : Fin (rows κ) → EF)
    (msg : Fin (2 ^ lk κ) → EF) : Finset (Fin (cols κ)) :=
  univ.filter fun c => enc (kap (lk κ)) (lk κ) (dom (cols κ)) msg c ≠ ∑ i, w i * EF.ofF (U i c)

/-- **Far mode**: if `Σ_i r_i U_i` is not `e`-close, every `ū` leaves more than `e` columns in
`D_far`. -/
theorem far_Dset_card {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F) (r : Fin (rows κ) → EF)
    (hfar : ¬ Close (code κ) (radius κ) (∑ i, r i • UE κ U i)) (msg : Fin (2 ^ lk κ) → EF) :
    radius κ + 1 ≤ (Dset κ U r msg).card := by
  by_contra hlt
  apply hfar
  refine close_iff_agree.2 ⟨_, enc_mem_rsCode _ _ _ msg, Dset κ U r msg, by omega, fun x hx => ?_⟩
  rw [UE_sum_apply]
  simp only [Dset, mem_filter, mem_univ, true_and, not_not] at hx
  exact hx.symm

/-- **Close mode**: a `v` other than the decoded combination `Σ_i a_i q_dec[i]` leaves at least
`d − e` columns in `D_close`. -/
theorem close_Dset_card {κ : ℕ} (hκ : κ ≤ 20) {U : Fin (rows κ) → Fin (cols κ) → F}
    {Q : Fin (rows κ) → Fin (2 ^ lk κ) → F} {S : Finset (Fin (cols κ))} (h : Decodes κ U Q S)
    (a : Fin (rows κ) → EF) {msg : Fin (2 ^ lk κ) → EF}
    (hne : msg ≠ fun j => ∑ i, a i * EF.ofF (Q i j)) :
    dist κ - radius κ ≤ (Dset κ U a msg).card := by
  classical
  obtain ⟨hc', hag⟩ := IsDecomp.comb h a
  set cw : Fin (rows κ) → Fin (cols κ) → EF := fun i =>
    enc (kap (lk κ)) (lk κ) (dom (cols κ)) fun j => EF.ofF (Q i j)
  have hlin : ∑ i, a i • cw i = enc (kap (lk κ)) (lk κ) (dom (cols κ))
      (fun j => ∑ i, a i * EF.ofF (Q i j)) := by
    rw [show (fun j => ∑ i, a i * EF.ofF (Q i j)) = ∑ i, a i • fun j => EF.ofF (Q i j) by
      funext j; simp [Finset.sum_apply]]
    exact (encode_complete _ _ _ a _).symm
  have hne' : enc (kap (lk κ)) (lk κ) (dom (cols κ)) msg ≠ ∑ i, a i • cw i := by
    rw [hlin]; intro h'
    exact hne (enc_injective _ _ (dom_inj κ hκ) (msgLen_le_cols κ) h')
  have hd := dist_ge_of_agree (code_minDist κ hκ) (enc_mem_rsCode _ _ _ msg) hc' hne' hag
  have hS := h.1
  have hdist : hammingDist (enc (kap (lk κ)) (lk κ) (dom (cols κ)) msg)
      (∑ i, a i • UE κ U i) = (Dset κ U a msg).card := by
    unfold hammingDist Dset
    congr 1; ext x; simp [UE]
  omega

/-- **An accepted opening of `U`'s column** lies outside both difference sets (`colCheck_iff`). -/
theorem accept_not_mem {κ : ℕ} (U : Fin (rows κ) → Fin (cols κ) → F) (r a ubar v : Array EF)
    (c : Fin (cols κ)) (col : Array F)
    (hcheck : colCheck κ (kapArr (lk κ)) r a ubar v c col = true)
    (hcol : ∀ i : Fin (rows κ), col.getD i 0 = U i c) :
    c ∉ Dset κ U (fun i => r.getD i 0) (fun j => ubar.getD j 0) ∧
      c ∉ Dset κ U (fun i => a.getD i 0) (fun j => v.getD j 0) := by
  rw [colCheck_iff, kapFn_kapArr] at hcheck
  simp only [Dset, mem_filter, mem_univ, true_and, not_not]
  refine ⟨hcheck.1.trans ?_, hcheck.2.trans ?_⟩ <;>
    exact Finset.sum_congr rfl fun i _ => by rw [hcol i, mul_comm]

/-- With the decoded `v = Σ_i a_i q_dec[i]`, the evaluation claim `Σ_j b_j v_j` is the decoded
matrix's tensor evaluation `Σ_{i,j} a_i b_j q_dec[i][j]`. -/
theorem eval_of_correct {κ : ℕ} (Q : Fin (rows κ) → Fin (2 ^ lk κ) → F) (a : Fin (rows κ) → EF)
    (b : Fin (2 ^ lk κ) → EF) :
    ∑ j, b j * (∑ i, a i * EF.ofF (Q i j)) = ∑ i, ∑ j, a i * b j * EF.ofF (Q i j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The evaluation-test link (§9.2, rows "after `v`" and R7, with L-M3) -/

/-- **An opening that verifies on the log** opens the filled matrix's column (`open_binding_prefix`),
so an accepted opening at `c` puts `c` outside both difference sets of `U_T = filled L₀ root`. -/
theorem opened_not_mem {κ : ℕ} {L₀ L₁ : Log} {e : ByteArray × Digest} {root : Label}
    (hc : ¬ Merkle.Collision (L₀ ++ e :: L₁)) (hb : ¬ Merkle.Hit (L₀ ++ e :: L₁))
    (he : Merkle.parseAbsorbRoot e.1 = some root) {c : Fin (cols κ)} {col : ByteArray}
    {ss : List Label} (hw : col.size = 8 * rows κ) (hlen : ss.length = lN κ)
    (hv : (Merkle.verify root c col ss).runLog (L₀ ++ e :: L₁) = some true)
    {r a ubar v : Array EF}
    (hcheck : colCheck κ (kapArr (lk κ)) r a ubar v c (readFs col 0 (rows κ)) = true) :
    c ∉ Dset κ (filled κ L₀ root) (fun i => r.getD i 0) (fun j => ubar.getD j 0) ∧
      c ∉ Dset κ (filled κ L₀ root) (fun i => a.getD i 0) (fun j => v.getD j 0) :=
  accept_not_mem _ r a ubar v c _ hcheck fun i =>
    (filled_of_colL (Merkle.open_binding_prefix hc hb he hw hlen hv) i).symm

/-- **`verify2` accepting on a log**: every opening's path verifies on the log and both column
equations hold (`run_verify2` under the log oracle, with the queries read off the log). -/
theorem verify2_runLog (L : Log) (κ : ℕ) (st : Digest) (root : Label) (r a ubar : Array EF)
    (vB opens : ByteArray) (h : (verify2 κ st root r a ubar vB opens).runLog L = some true) :
    ∀ j < tQ,
      (Merkle.verify root
          ((((squeezeIdx ((absorb st 0x08 vB).run (OProg.logOracle L)) (lN κ) tQ).run
            (OProg.logOracle L)).2).getD j 0)
          (readCol κ opens (j * openW κ)) (readPath κ opens (j * openW κ))).runLog L = some true ∧
        colCheck κ (kapArr (lk κ)) r a ubar (readEFs vB 0 (msgLen κ))
          ((((squeezeIdx ((absorb st 0x08 vB).run (OProg.logOracle L)) (lN κ) tQ).run
            (OProg.logOracle L)).2).getD j 0)
          (readFs (readCol κ opens (j * openW κ)) 0 (rows κ)) = true := by
  obtain ⟨hq, hrun⟩ := (OProg.runLog_eq_some_iff _ _).1 h
  intro j hj
  obtain ⟨h1, h2⟩ := (run_verify2 _ κ st root r a ubar vB opens).1 hrun j hj
  refine ⟨(OProg.runLog_eq_some_iff _ _).2 ⟨fun q hq' => hq q ?_, h1⟩, h2⟩
  simp only [verify2, openOne, OProg.queries_bind, OProg.queries_mapM,
    OProg.queries_pure, List.mem_append, List.mem_flatMap, List.mem_range]
  right; right; left
  exact ⟨j, hj, Or.inl hq'⟩

/-! ### R7: the column-index answers -/

set_option exponentiation.threshold 600

/-- All indices of `J` answers: `J` tuples of `c` indices of `ℓ` bits. -/
def idxAll (ℓ c J : ℕ) (b : Fin J → Digest) : Fin J → Fin c → Fin (2 ^ ℓ) :=
  fun i => idxVec ℓ c (b i)

theorem card_idxAll_fiber (ℓ c J : ℕ) (h : ℓ * c ≤ 256) (τ : Fin J → Fin c → Fin (2 ^ ℓ)) :
    (univ.filter fun b : Fin J → Digest => idxAll ℓ c J b = τ).card = (2 ^ (256 - ℓ * c)) ^ J := by
  classical
  rw [← Fintype.card_subtype]
  have : Fintype.card {b : Fin J → Digest // idxAll ℓ c J b = τ} =
      Fintype.card {b : Fin J → Digest // ∀ i, idxVec ℓ c (b i) = τ i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun b => funext_iff)
  rw [this, Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun i (x : Digest) =>
    idxVec ℓ c x = τ i)), Fintype.card_pi]
  simp only [Fintype.card_subtype, card_idx_fiber ℓ c h, prod_const, card_univ, Fintype.card_fin]

/-- Tuples avoiding `A` on the first `t` positions (position of `(i, r)`: `i c + r`). -/
theorem card_avoid (J c t : ℕ) {X : Type} [Fintype X] [DecidableEq X] (A : Finset X)
    (ht : t ≤ J * c) :
    (univ.filter fun τ : Fin J → Fin c → X =>
      ∀ (i : Fin J) (r : Fin c), (i : ℕ) * c + r < t → τ i r ∈ A).card =
      A.card ^ t * Fintype.card X ^ (J * c - t) := by
  classical
  rw [← Fintype.card_subtype]
  have e1 := Equiv.subtypePiEquivPi (p := fun (i : Fin J) (f : Fin c → X) =>
    ∀ r : Fin c, (i : ℕ) * c + r < t → f r ∈ A)
  rw [Fintype.card_congr e1, Fintype.card_pi]
  have hinner : ∀ i : Fin J, Fintype.card {f : Fin c → X // ∀ r : Fin c, (i : ℕ) * c + r < t →
      f r ∈ A} = ∏ r : Fin c, if (i : ℕ) * c + r < t then A.card else Fintype.card X := by
    intro i
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (r : Fin c) (x : X) =>
      (i : ℕ) * c + r < t → x ∈ A)), Fintype.card_pi]
    refine prod_congr rfl fun r _ => ?_
    split_ifs with hr
    · simp [hr, Fintype.card_subtype]
    · simp [hr]
  simp only [hinner]
  rw [← Fintype.prod_prod_type (fun p : Fin J × Fin c =>
    if (p.1 : ℕ) * c + p.2 < t then A.card else Fintype.card X), prod_ite, prod_const, prod_const]
  have hcnt : (univ.filter fun p : Fin J × Fin c => (p.1 : ℕ) * c + p.2 < t).card = t := by
    rw [← card_map finProdFinEquiv.toEmbedding]
    have : (univ.filter fun p : Fin J × Fin c => (p.1 : ℕ) * c + p.2 < t).map
        finProdFinEquiv.toEmbedding = univ.filter fun q : Fin (J * c) => (q : ℕ) < t := by
      ext q
      simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨p, hp, rfl⟩; rw [finProdFinEquiv_apply_val]; linarith
      · intro hq
        refine ⟨finProdFinEquiv.symm q, ?_, Equiv.apply_symm_apply _ _⟩
        have := finProdFinEquiv_apply_val (finProdFinEquiv.symm q)
        rw [Equiv.apply_symm_apply] at this
        linarith
    rw [this, Fin.card_filter_val_lt]; omega
  have hcnt' : (univ.filter fun p : Fin J × Fin c => ¬ ((p.1 : ℕ) * c + p.2 < t)).card =
      J * c - t := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin J × Fin c)))
      (fun p : Fin J × Fin c => (p.1 : ℕ) * c + p.2 < t)
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hcnt] at this
    omega
  rw [hcnt, hcnt']

/-- The miss event of `t` indices read off `J` answers (`Transcript.indices`, as `verify2`). -/
def Miss (ℓ t J : ℕ) (D : Finset (Fin (2 ^ ℓ))) (b : Fin J → Digest) : Prop :=
  ∀ j < t, ∀ x ∈ D, (x : ℕ) ≠ (indices ℓ t (List.ofFn b)).getD j 0

theorem miss_iff (ℓ t J : ℕ) (hc : 0 < cnt ℓ) (ht : t ≤ J * cnt ℓ) (D : Finset (Fin (2 ^ ℓ)))
    (b : Fin J → Digest) :
    Miss ℓ t J D b ↔
      ∀ (i : Fin J) (r : Fin (cnt ℓ)), (i : ℕ) * cnt ℓ + r < t → idxAll ℓ (cnt ℓ) J b i r ∈ Dᶜ := by
  have hidx : ∀ j (hj : j < t), (indices ℓ t (List.ofFn b)).getD j 0 =
      idxOf ℓ (b ⟨j / cnt ℓ, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact lt_of_lt_of_le hj ht)⟩)
        (j % cnt ℓ) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp [length_indices, hj])]
    simp only [indices, List.getElem_map, List.getElem_range]
    rw [getElem!_pos (List.ofFn b) _ (by
      simp; exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact lt_of_lt_of_le hj ht)),
      List.getElem_ofFn]
  constructor
  · intro h i r hir
    rw [mem_compl]
    intro hmem
    have hj := h _ hir _ hmem
    rw [hidx _ hir] at hj
    apply hj
    have h1 : ((i : ℕ) * cnt ℓ + r) / cnt ℓ = i := by
      rw [add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt r.2, zero_add]
    have h2 : ((i : ℕ) * cnt ℓ + r) % cnt ℓ = r := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2]
    simp only [idxAll, idxVec, h1, h2]
  · intro h j hj x hx heq
    have hjd : j / cnt ℓ < J := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact lt_of_lt_of_le hj ht)
    have := h ⟨j / cnt ℓ, hjd⟩ ⟨j % cnt ℓ, Nat.mod_lt _ hc⟩
      (by simp only; rw [mul_comm]; have := Nat.div_add_mod j (cnt ℓ); omega)
    rw [mem_compl] at this
    apply this
    rw [hidx j hj] at heq
    convert hx
    exact Fin.ext (by simp [idxAll, idxVec, heq])

/-- **R7, exact count**: `#{b : all t indices miss D} · N^t = (N − |D|)^t · 2^{256 J}`. -/
theorem r7_count (ℓ t J : ℕ) (hc : 0 < cnt ℓ) (hℓ : ℓ * cnt ℓ ≤ 256) (ht : t ≤ J * cnt ℓ)
    (D : Finset (Fin (2 ^ ℓ))) :
    Nat.card {b : Fin J → Digest // Miss ℓ t J D b} * (2 ^ ℓ) ^ t =
      (2 ^ ℓ - D.card) ^ t * (2 ^ 256) ^ J := by
  classical
  have hM : Nat.card {b : Fin J → Digest // Miss ℓ t J D b} =
      (univ.filter fun b => idxAll ℓ (cnt ℓ) J b ∈ univ.filter fun τ : Fin J → Fin (cnt ℓ) →
        Fin (2 ^ ℓ) => ∀ (i : Fin J) (r : Fin (cnt ℓ)), (i : ℕ) * cnt ℓ + r < t →
          τ i r ∈ Dᶜ).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext b; simp [miss_iff ℓ t J hc ht D b]
  rw [hM, card_mem_of_fiber _ _ (card_idxAll_fiber ℓ (cnt ℓ) J hℓ), card_avoid J _ t _ ht,
    card_compl, Fintype.card_fin]
  have e1 : ((2 : ℕ) ^ ℓ) ^ (J * cnt ℓ - t) * (2 ^ ℓ) ^ t = (2 ^ (ℓ * cnt ℓ)) ^ J := by
    rw [← pow_add, Nat.sub_add_cancel ht, ← pow_mul, ← pow_mul]; ring_nf
  have e2 : ((2 : ℕ) ^ (ℓ * cnt ℓ)) ^ J * (2 ^ (256 - ℓ * cnt ℓ)) ^ J = (2 ^ 256) ^ J := by
    rw [← mul_pow, ← pow_add, Nat.add_sub_cancel' hℓ]
  calc (2 ^ ℓ - D.card) ^ t * (2 ^ ℓ) ^ (J * cnt ℓ - t) * (2 ^ (256 - ℓ * cnt ℓ)) ^ J * (2 ^ ℓ) ^ t
      = (2 ^ ℓ - D.card) ^ t * (((2 ^ ℓ) ^ (J * cnt ℓ - t) * (2 ^ ℓ) ^ t) *
          (2 ^ (256 - ℓ * cnt ℓ)) ^ J) := by ring
    _ = _ := by rw [e1, e2]

/-- The index layout is well formed for every `κ ≤ 20`. -/
theorem layout_ok : ∀ κ ≤ 20, 0 < cnt (lN κ) ∧ lN κ * cnt (lN κ) ≤ 256 ∧
    tQ ≤ nAns (lN κ) tQ * cnt (lN κ) := by decide

/-- **R7, far mode**: if `|D| > e`, the index answers missing `D` are at most a `(4/5)·2^-129`
fraction. -/
theorem r7_far (κ : ℕ) (hκ : κ ≤ 20) (D : Finset (Fin (2 ^ lN κ)))
    (hD : radius κ + 1 ≤ D.card) :
    Nat.card {b : Fin (nAns (lN κ) tQ) → Digest // Miss (lN κ) tQ _ D b} * 2 ^ 129 * 5 ≤
      4 * (2 ^ 256) ^ nAns (lN κ) tQ := by
  obtain ⟨hc, hℓ, ht⟩ := layout_ok κ hκ
  have hcount := r7_count (lN κ) tQ _ hc hℓ ht D
  have hmiss := miss_pow (N := cols κ) (s := radius κ + 1) (t := tQ) (b := 24) (a' := 17) le_rfl
    (far_ratio κ)
  have hcol : cols κ = 2 ^ lN κ := rfl
  rw [hcol] at hmiss
  have hsub : (2 ^ lN κ - D.card) ^ tQ ≤ (2 ^ lN κ - (radius κ + 1)) ^ tQ :=
    Nat.pow_le_pow_left (by omega) _
  set M := Nat.card {b : Fin (nAns (lN κ) tQ) → Digest // Miss (lN κ) tQ _ D b}
  have hN : 0 < (2 ^ lN κ) ^ tQ * 24 ^ tQ := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hN
  calc M * 2 ^ 129 * 5 * ((2 ^ lN κ) ^ tQ * 24 ^ tQ) =
        (M * (2 ^ lN κ) ^ tQ) * 24 ^ tQ * (2 ^ 129 * 5) := by ring
    _ = (2 ^ lN κ - D.card) ^ tQ * 24 ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * (2 ^ 129 * 5) := by
        rw [hcount]; ring
    _ ≤ (2 ^ lN κ - (radius κ + 1)) ^ tQ * 24 ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * (2 ^ 129 * 5) := by
        gcongr
    _ ≤ 17 ^ tQ * (2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * (2 ^ 129 * 5) := by gcongr
    _ = (17 ^ 260 * 2 ^ 129 * 5) * ((2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ) := by
        unfold tQ; ring
    _ ≤ (24 ^ 260 * 4) * ((2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ) :=
        Nat.mul_le_mul_right _ pow17_le
    _ = 4 * (2 ^ 256) ^ nAns (lN κ) tQ * ((2 ^ lN κ) ^ tQ * 24 ^ tQ) := by unfold tQ; ring

/-- **R7, close mode**: if `|D| ≥ d − e`, the index answers missing `D` are at most a `2^-328`
fraction. -/
theorem r7_close (κ : ℕ) (hκ : κ ≤ 20) (D : Finset (Fin (2 ^ lN κ)))
    (hD : dist κ - radius κ ≤ D.card) :
    Nat.card {b : Fin (nAns (lN κ) tQ) → Digest // Miss (lN κ) tQ _ D b} * 2 ^ 328 ≤
      (2 ^ 256) ^ nAns (lN κ) tQ := by
  obtain ⟨hc, hℓ, ht⟩ := layout_ok κ hκ
  have hcount := r7_count (lN κ) tQ _ hc hℓ ht D
  have hmiss := miss_pow (N := cols κ) (s := dist κ - radius κ) (t := tQ) (b := 12) (a' := 5)
    le_rfl (close_ratio κ)
  have hcol : cols κ = 2 ^ lN κ := rfl
  rw [hcol] at hmiss
  have hsub : (2 ^ lN κ - D.card) ^ tQ ≤ (2 ^ lN κ - (dist κ - radius κ)) ^ tQ :=
    Nat.pow_le_pow_left (by omega) _
  set M := Nat.card {b : Fin (nAns (lN κ) tQ) → Digest // Miss (lN κ) tQ _ D b}
  have hN : 0 < (2 ^ lN κ) ^ tQ * 12 ^ tQ := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hN
  calc M * 2 ^ 328 * ((2 ^ lN κ) ^ tQ * 12 ^ tQ) =
        (M * (2 ^ lN κ) ^ tQ) * 12 ^ tQ * 2 ^ 328 := by ring
    _ = (2 ^ lN κ - D.card) ^ tQ * 12 ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * 2 ^ 328 := by
        rw [hcount]; ring
    _ ≤ (2 ^ lN κ - (dist κ - radius κ)) ^ tQ * 12 ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * 2 ^ 328 := by
        gcongr
    _ ≤ 5 ^ tQ * (2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ * 2 ^ 328 := by gcongr
    _ = (5 ^ 260 * 2 ^ 328) * ((2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ) := by unfold tQ; ring
    _ ≤ 12 ^ 260 * ((2 ^ lN κ) ^ tQ * (2 ^ 256) ^ nAns (lN κ) tQ) := Nat.mul_le_mul_right _ pow5_le
    _ = (2 ^ 256) ^ nAns (lN κ) tQ * ((2 ^ lN κ) ^ tQ * 12 ^ tQ) := by unfold tQ; ring

/-! ### The decoded witness (§4.1 packing, §2.3 layout) -/

theorem wDec_row_lt (κ : ℕ) (u : Fin (2 ^ (14 + κ))) : u.val / 64 / 2 ^ lk κ < rows κ := by
  have h1 : u.val / 64 < 2 ^ (8 + κ) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    have := u.2
    calc u.val < 2 ^ (14 + κ) := this
      _ = 2 ^ (8 + κ) * 64 := by rw [show 14 + κ = (8 + κ) + 6 by omega, pow_add]; norm_num
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have := rows_mul κ
  unfold msgLen at this
  omega

/-- **The decoded witness** `w_dec`: position `u = i + 64 u'` is bit `i` of the decoded packed
element `q_dec(u') = Q_dec[u' / k][u' mod k]` (§4.1: bit `i` of the word is `Q_i`). -/
noncomputable def wDec (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F)
    (u : Fin (2 ^ (14 + κ))) : F :=
  if (qDec κ U ⟨u.val / 64 / 2 ^ lk κ, wDec_row_lt κ u⟩
      ⟨u.val / 64 % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩).val.toNat.testBit (u.val % 64)
  then 1 else 0

/-- `w_dec` is Boolean. -/
theorem wDec_bool (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (14 + κ))) :
    wDec κ U u = 0 ∨ wDec κ U u = 1 := by
  unfold wDec; split <;> simp

/-- **The decoded extended witness** `z_dec = (w_dec ‖ pub(s, h))` in the §2.3 layout
(`SpartanChainChain.zOf`), over `EF`. -/
noncomputable def zDec (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (s h : Digest) :
    Ix κ → EF :=
  zOf (fun u => EF.ofF (wDec κ U u)) s h


/-! ### Bit-plane packing (§4.1; review S2b-M4) -/

theorem F_add_val (x y : F) : (x + y).val = x.val ^^^ y.val := rfl
theorem F_zero_val : (0 : F).val = 0 := rfl

/-- The word `2^i` (`i < 64`) is `x^i` (bit `i` of the word is the coefficient of `x^i`). -/
theorem x_pow_word : ∀ i : Fin 64, F.x ^ (i : ℕ) = ⟨(1 : UInt64) <<< (i.val.toUInt64)⟩ := by
  decide +kernel

/-- The term of bit `i` of `a`: the word `2^i` if the bit is set, else `0`. -/
def bitTerm (a : F) (i : ℕ) : F := if a.val.toNat.testBit i then ⟨(1 : UInt64) <<< i.toUInt64⟩ else 0

theorem bitTerm_toNat (a : F) {i : ℕ} (hi : i < 64) :
    (bitTerm a i).val.toNat = if a.val.toNat.testBit i then 2 ^ i else 0 := by
  unfold bitTerm
  split_ifs
  · simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hi]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hi) (by norm_num)
  · rfl

theorem sum_bitTerm (a : F) : ∀ k ≤ 64,
    (∑ i ∈ range k, bitTerm a i).val.toNat = a.val.toNat % 2 ^ k := by
  intro k
  induction k with
  | zero => intro _; simp [F_zero_val, Nat.mod_one]
  | succ k ih =>
    intro hk
    rw [sum_range_succ, F_add_val, UInt64.toNat_xor, ih (by omega), bitTerm_toNat a (by omega)]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    split_ifs with hb
    · rw [Nat.testBit_two_pow]
      rcases lt_trichotomy j k with h | rfl | h
      · simp [h, show j < k + 1 by omega, show k ≠ j by omega]
      · simp [hb]
      · simp [show ¬ j < k by omega, show ¬ j < k + 1 by omega, show k ≠ j by omega]
    · simp only [Nat.zero_testBit, Bool.xor_false]
      by_cases h : j = k
      · subst h; simp [hb]
      · by_cases h' : j < k
        · simp [h', show j < k + 1 by omega]
        · simp [h', show ¬ j < k + 1 by omega]

/-- **Bit-plane packing over `F`**: a word is the sum of its bits times `x^i`. -/
theorem word_bits (a : F) :
    a = ∑ i ∈ range 64, (if a.val.toNat.testBit i then 1 else 0) * F.x ^ i := by
  have h := sum_bitTerm a 64 le_rfl
  rw [Nat.mod_eq_of_lt a.val.toNat_lt] at h
  have hs : ∑ i ∈ range 64, bitTerm a i =
      ∑ i ∈ range 64, (if a.val.toNat.testBit i then 1 else 0) * F.x ^ i := by
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have := x_pow_word ⟨i, hi⟩
    simp only at this
    unfold bitTerm
    split_ifs <;> simp [this]
  rw [← hs]
  cases a with
  | mk v =>
    congr 1
    exact (UInt64.toNat_inj.1 h).symm


theorem wDec_eq_bit (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ)))
    (h1 : u.val / 2 ^ lk κ < rows κ) {i : ℕ} (hi : i < 64) (v : Fin (2 ^ (14 + κ)))
    (hv : v.val = 64 * u.val + i) :
    wDec κ U v = if (qDec κ U ⟨u.val / 2 ^ lk κ, h1⟩
      ⟨u.val % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩).val.toNat.testBit i then 1 else 0 := by
  have e1 : v.val / 64 = u.val := by omega
  have e2 : v.val % 64 = i := by omega
  unfold wDec
  have hq : qDec κ U ⟨v.val / 64 / 2 ^ lk κ, wDec_row_lt κ v⟩
      ⟨v.val / 64 % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩ =
      qDec κ U ⟨u.val / 2 ^ lk κ, h1⟩ ⟨u.val % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩ := by
    congr 1 <;> exact Fin.ext (by simp only [e1])
  rw [hq, e2]

/-- **Bit-plane packing lemma** (S2b-M4), over `F`: the decoded packed element
`q_dec(u) = Q_dec[u / k][u mod k]` is `Σ_{i<64} Q_i(u) · x^i`, where `Q_i(u) = w_dec(i + 64 u)` is
bit-plane `i` (`planes i` is any index of value `64 u + i`, e.g. `Fin.cast _ (join i u)`). -/
theorem qDec_bitplanes (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ)))
    (h1 : u.val / 2 ^ lk κ < rows κ) (planes : Fin (2 ^ 6) → Fin (2 ^ (14 + κ)))
    (hp : ∀ i, (planes i).val = 64 * u.val + i.val) :
    qDec κ U ⟨u.val / 2 ^ lk κ, h1⟩ ⟨u.val % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩ =
      ∑ i : Fin (2 ^ 6), wDec κ U (planes i) * F.x ^ (i : ℕ) := by
  conv_lhs => rw [word_bits (qDec κ U _ _)]
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by
    rw [wDec_eq_bit κ U u h1 (by simp) (planes i) (hp i)]

/-- **Bit-plane packing lemma** over `EF` (the form of ring switching: `wX i = ι(x^i)`,
`qPlane κ U i u = EF.ofF (w_dec(…))`): `EF.ofF (q_dec(u)) = Σ_i ι(x^i) · EF.ofF (Q_i(u))`. -/
theorem qDec_bitplanes_EF (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ)))
    (h1 : u.val / 2 ^ lk κ < rows κ) (planes : Fin (2 ^ 6) → Fin (2 ^ (14 + κ)))
    (hp : ∀ i, (planes i).val = 64 * u.val + i.val) :
    EF.ofF (qDec κ U ⟨u.val / 2 ^ lk κ, h1⟩ ⟨u.val % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩) =
      ∑ i : Fin (2 ^ 6), algebraMap F EF (F.x ^ (i : ℕ)) * EF.ofF (wDec κ U (planes i)) := by
  rw [qDec_bitplanes κ U u h1 planes hp, ← EF.algebraMap_eq_ofF, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, EF.algebraMap_eq_ofF, mul_comm]

/-! ### The multi-answer escape counts (§9.2) -/

open NNReal in
/-- **`r0_esc_le`** (§9.2): for any event `P` on the `m` R0 answers that implies `far` and
`Σ_i chE(a_i) U_i` `e`-close (the R0 escape), the conditional escape count from the start of the
round is at most `2^-169`. (`condCount U es [] = extCount (P es) [] m / 2^(256 m)`.) -/
theorem r0_esc_le {κ : ℕ} (hκ : κ ≤ 20) (U : Fin (rows κ) → Fin (cols κ) → F)
    (P : List Digest → Prop)
    (hP : ∀ a : Fin (rows κ) → Digest, P (List.ofFn a) →
      ¬ eClose (code κ) (UE κ U) (radius κ) ∧
        Close (code κ) (radius κ) (∑ i, chE (a i) • UE κ U i)) :
    (SoundnessLog.extCount P [] (rows κ) : ℝ≥0) / 2 ^ (256 * rows κ) ≤ 1 / 2 ^ 169 := by
  classical
  have hcnt : SoundnessLog.extCount P [] (rows κ) * 2 ^ 169 ≤ (2 ^ 256) ^ rows κ := by
    by_cases hfar : eClose (code κ) (UE κ U) (radius κ)
    · have : SoundnessLog.extCount P [] (rows κ) = 0 := by
        unfold SoundnessLog.extCount
        rw [card_eq_zero, filter_eq_empty_iff]
        intro a _ ha
        exact (hP a (by simpa using ha)).1 hfar
      rw [this]; positivity
    · refine le_trans (Nat.mul_le_mul_right _ ?_) (r0_answers hκ U hfar)
      unfold SoundnessLog.extCount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact card_le_card fun a ha => by
        simp only [mem_filter, mem_univ, true_and, List.nil_append] at ha ⊢
        exact (hP a ha).2
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_mul]
  exact_mod_cast hcnt

open NNReal in
/-- **`r7_esc_le`** (§9.2): for any event `P` on the `J` R7 answers that implies the miss event
of a difference set with `|D| > e` (far mode by `far_Dset_card`; close mode by
`close_Dset_card`, `d − e > e`), the conditional escape count from the start of the round is at
most `(4/5)·2^-129`. -/
theorem r7_esc_le {κ : ℕ} (hκ : κ ≤ 20) (D : Finset (Fin (2 ^ lN κ)))
    (hD : radius κ + 1 ≤ D.card) (P : List Digest → Prop)
    (hP : ∀ b : Fin (nAns (lN κ) tQ) → Digest, P (List.ofFn b) → Miss (lN κ) tQ _ D b) :
    (SoundnessLog.extCount P [] (nAns (lN κ) tQ) : ℝ≥0) / 2 ^ (256 * nAns (lN κ) tQ) ≤
      (4 / 5) / 2 ^ 129 := by
  classical
  have hcnt : SoundnessLog.extCount P [] (nAns (lN κ) tQ) * 2 ^ 129 * 5 ≤
      4 * (2 ^ 256) ^ nAns (lN κ) tQ := by
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)) (r7_far κ hκ D hD)
    unfold SoundnessLog.extCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_le_card fun b hb => by
      simp only [mem_filter, mem_univ, true_and, List.nil_append] at hb ⊢
      exact hP b hb
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_mul]
  have : ((SoundnessLog.extCount P [] (nAns (lN κ) tQ) : ℝ≥0)) * 2 ^ 129 * 5 ≤
      4 * (2 ^ 256) ^ nAns (lN κ) tQ := by exact_mod_cast hcnt
  calc (SoundnessLog.extCount P [] (nAns (lN κ) tQ) : ℝ≥0) * 2 ^ 129
      = (SoundnessLog.extCount P [] (nAns (lN κ) tQ) * 2 ^ 129 * 5) / 5 := by
        field_simp
    _ ≤ (4 * (2 ^ 256) ^ nAns (lN κ) tQ) / 5 := by gcongr
    _ = 4 / 5 * (2 ^ 256) ^ nAns (lN κ) tQ := by ring

/-- Close mode gives `|D_close| > e` too (`d − e > e`), so `r7_esc_le` covers both modes. -/
theorem radius_succ_le (κ : ℕ) : radius κ + 1 ≤ dist κ - radius κ := by
  have := three_radius_lt κ; omega

/-! ### The column phase on a log, as a miss event (for `final`, L-K3) -/

/-- The `J` index answers of `verify2`'s column phase, under the log oracle. -/
def idxAnswers (L : Log) (κ : ℕ) (st : Digest) (vB : ByteArray) : List Digest :=
  ((squeezeN ((absorb st 0x08 vB).run (OProg.logOracle L)) (nAns (lN κ) tQ)).run
    (OProg.logOracle L)).2

theorem length_idxAnswers (L : Log) (κ : ℕ) (st : Digest) (vB : ByteArray) :
    (idxAnswers L κ st vB).length = nAns (lN κ) tQ := by
  simp [idxAnswers]

theorem size_readCol (κ : ℕ) (b : ByteArray) (o : ℕ) : (readCol κ b o).size = 8 * rows κ := by
  show (Array.ofFn _).size = _
  simp

/-- The answers as a tuple. -/
def idxTuple (L : Log) (κ : ℕ) (st : Digest) (vB : ByteArray) :
    Fin (nAns (lN κ) tQ) → Digest :=
  fun i => (idxAnswers L κ st vB)[i.val]'(by rw [length_idxAnswers]; exact i.2)

theorem ofFn_idxTuple (L : Log) (κ : ℕ) (st : Digest) (vB : ByteArray) :
    List.ofFn (idxTuple L κ st vB) = idxAnswers L κ st vB := by
  apply List.ext_getElem (by simp [length_idxAnswers])
  intro i h1 h2; simp [idxTuple]

/-- **The column phase accepted on the log misses both difference sets** of the committed
matrix `U_T = filled L₀ root` (L-M3 through `opened_not_mem`): on `L = L₀ ++ e :: L₁` with `e`
the `absorb(root)` entry and no collision or label hit, if `verify2` accepts on `L` then every
opened index lies outside `Dset U_T r ū` and `Dset U_T a v`, i.e. the R7 answers satisfy `Miss`
for both. -/
theorem verify2_miss {κ : ℕ} {L₀ L₁ : Log} {e : ByteArray × Digest} {root : Label}
    (hc : ¬ Merkle.Collision (L₀ ++ e :: L₁)) (hb : ¬ Merkle.Hit (L₀ ++ e :: L₁))
    (he : Merkle.parseAbsorbRoot e.1 = some root) (st : Digest) (r a ubar : Array EF)
    (vB opens : ByteArray)
    (h : (verify2 κ st root r a ubar vB opens).runLog (L₀ ++ e :: L₁) = some true) :
    Miss (lN κ) tQ (nAns (lN κ) tQ)
        (Dset κ (filled κ L₀ root) (fun i => r.getD i 0) (fun j => ubar.getD j 0))
        (idxTuple (L₀ ++ e :: L₁) κ st vB) ∧
      Miss (lN κ) tQ (nAns (lN κ) tQ)
        (Dset κ (filled κ L₀ root) (fun i => a.getD i 0)
          (fun j => (readEFs vB 0 (msgLen κ)).getD j 0))
        (idxTuple (L₀ ++ e :: L₁) κ st vB) := by
  have hacc := verify2_runLog _ κ st root r a ubar vB opens h
  have hidx : ((squeezeIdx ((absorb st 0x08 vB).run (OProg.logOracle (L₀ ++ e :: L₁))) (lN κ)
      tQ).run (OProg.logOracle (L₀ ++ e :: L₁))).2 =
      indices (lN κ) tQ (List.ofFn (idxTuple (L₀ ++ e :: L₁) κ st vB)) := by
    rw [ofFn_idxTuple]; simp [squeezeIdx, idxAnswers]
  rw [hidx] at hacc
  have key : ∀ j < tQ, ∀ (x : Fin (cols κ)),
      (x : ℕ) = (indices (lN κ) tQ (List.ofFn (idxTuple (L₀ ++ e :: L₁) κ st vB))).getD j 0 →
      x ∉ Dset κ (filled κ L₀ root) (fun i => r.getD i 0) (fun j => ubar.getD j 0) ∧
        x ∉ Dset κ (filled κ L₀ root) (fun i => a.getD i 0)
          (fun j => (readEFs vB 0 (msgLen κ)).getD j 0) := by
    intro j hj x hx
    obtain ⟨h1, h2⟩ := hacc j hj
    rw [← hx] at h1 h2
    exact opened_not_mem hc hb he (c := x) (size_readCol κ _ _) (by simp [readPath]) h1 h2
  exact ⟨fun j hj x hxD hx => (key j hj x hx).1 hxD, fun j hj x hxD hx => (key j hj x hx).2 hxD⟩

end SpartanChain.SoundnessPCS
