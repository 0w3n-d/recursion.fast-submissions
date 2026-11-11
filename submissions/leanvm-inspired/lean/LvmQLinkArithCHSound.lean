import LvmQLinkArithCH
import LvmMaskF

/-!
# QA1 links: the `CH` link gadget and its soundness against `F`

`chLinkGadget n D Q gate`: block A, the shift sumcheck (`2^D ≥ n` iterations), block B, the two-round
sumcheck, block C. **`chLink_sound`**: in every memory where the gadget's rows hold, whose input lanes
are the stream's (`Streamed`), with the phase starting at position `P` (`P + 40 = 8Q`) and gate `1`:
if the gadget's assertion holds, then `chLink0`'s check on what `F` reads in phase 5
(`chLinkView`, `LvmQLinkArithRead`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Small facts -/

theorem lnk_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  cases x; cases y
  show ((_ == _ && _ == _) && _ == _) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem lnk_scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp [scSpec, lnk_scSpec_length v count _ _ es]

theorem take_range_map (f : Nat → FE) {n N : Nat} (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_range_map (f : Nat → FE) (n N : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun i => f (n + i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_drop, List.getElem_map, List.getElem_range]

/-! ## The gadget -/

/-- The shift sumcheck's first message lane. -/
def chQ1 (n Q : Nat) : Nat := Q + 9 * (n + 9)
/-- The `in` slices' first lane. -/
def chQB (n Q : Nat) : Nat := chQ1 n Q + 15 * n
/-- The two-round sumcheck's first message lane. -/
def chQ2 (n Q : Nat) : Nat := chQB n Q + 246
/-- The `Y` slices' first lane. -/
def chQC (n Q : Nat) : Nat := chQ2 n Q + 30

/-- `ρ`'s cells (block A's loads `0 … n − 1`). -/
def rhoC (oA : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => oA.cell i 0
/-- `ρ'`'s cells (the shift sumcheck's challenges). -/
def rho'C (sh : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => sh.cell 2 i
/-- `eq(ζ, ·)`'s cells. -/
def eZC (oA : LoopOut) (n : Nat) : List Cell := (List.range 64).map fun k => oA.cell (n + 96 + k) 0
/-- `eq(λ, ·)`'s cells. -/
def eLC (oA : LoopOut) (n : Nat) : List Cell := (List.range 8).map fun k => oA.cell (n + 20 + k) 0

/-- **The `CH` link gadget** (phase 5's arithmetic). -/
def chLinkGadget (n D Q : Nat) (gate : Cell) : BM Unit := do
  let oA ← loop [] (tplOf (chGlueA n Q))
  let sh ← scGadget D 2 (chQ1 n Q) .plain (oA.cell (2 * n + 165) 0)
  let oB ← loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))))
  let sc2 ← scGadget 1 2 (chQ2 n Q) .plain (oB.cell (8 * n + 130) 0)
  let _ ← loop [] (tplOf (chGlueC (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate))
  pure ()

/-! ## Soundness -/

theorem chGlueC_last (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).getD (151 + rho'.length) default =
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩ := by
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  rw [show 151 + rho'.length = (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length - 1 by omega,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
  simp [chGlueC, List.getLast?_append, List.getLast?_cons]

theorem cell_iterV {M : Mem} (o : LoopOut) {t len : Nat} (ht : t < len) :
    (o.cell t 0).val M = (iterV M o len 0).getD t 0 := (iterV_getD M o ht).symm

/-! ## S1: the gated gadget and its soundness -/

/-- **The gated shift sumcheck's claim** in closed form. -/
theorem chShiftTargetG_eq (p : Params) (N : Nat) (chal : List FE) (hc : chal.length = p.logN + 9) :
    chShiftTargetG p N chal =
      (eqW ((chal.drop p.logN).take 3) 0 * (eqW (chal.drop (p.logN + 3)) 0 + eqW (chal.drop (p.logN + 3)) 1 +
        eqW (chal.drop (p.logN + 3)) 6) + eqW ((chal.drop p.logN).take 3) 4 * eqW (chal.drop (p.logN + 3)) 8) *
      ltSum (chal.take p.logN) (N - 1) := by
  unfold chShiftTargetG chSplit
  simp only []
  rw [padConst_eq _ _ (by simp; omega) (by simp; omega)]

/-- The gated two-round sumcheck's claim: `f₁ + S̃_m(ρ, ρ')·Σ_p eq(ζ, p)·inS_p`. -/
theorem chSc2TargetG_eq (p : Params) (N : Nat) (chal : List FE) (shift : List FE × FE) (inS : List FE)
    (hc : chal.length = p.logN + 9) (hi : inS.length = 64) :
    chSc2TargetG p N chal shift inS = shift.2 + preSum shift.1 (chal.take p.logN) (N - 1) *
      ∑ q ∈ Finset.range 64, eqW (chal.drop (p.logN + 3)) q * inS.getD q 0 := by
  unfold chSc2TargetG chSplit
  simp only []
  have hz : (chal.drop (p.logN + 3)).length = 6 := by simp; omega
  rw [dot_range _ _ (by rw [eqKernel_length_lk, hz, hi]; rfl), eqKernel_length_lk, hz, show (2 : Nat) ^ 6 = 64 from rfl]
  congr 2
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [eqKernel_getD _ (by rw [hz]; exact Finset.mem_range.mp hq)]

/-- `m`'s bit cells (block A's borrow rows). -/
def mbC (oA : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => oA.cell (n + 164 + 2 * i) 0

/-- **The gated `CH` link gadget** (phase 5's arithmetic, S1): block A with the borrow chain on `N`'s bits at
the `K` cells `nb + i` and `C·lt_m(ρ)`, the shift sumcheck, block B with `S̃_m`, `Ẽ'_m`, the two-round
sumcheck, block C. -/
def chLinkGadgetG (n D Q nb : Nat) (gate : Cell) : BM Unit := do
  let oA ← loop [] (tplOf (chGlueAG n Q nb))
  let sh ← scGadget D 2 (chQ1 n Q) .plain (oA.cell (8 * n + 164) 0)
  let oB ← loop [] (tplOf (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n) (sh.cell 5 (n - 1))))
  let sc2 ← scGadget 1 2 (chQ2 n Q) .plain (oB.cell (14 * n + 130) 0)
  let _ ← loop [] (tplOf (chGlueCG (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n)
    (oB.cell (14 * n + 126) 0) (sc2.cell 5 1) gate))
  pure ()

theorem chGlueCG_last (QC : Nat) (mu eL eZ : List Cell) (eS f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueCG QC mu eL eZ eS f2 gate).getD 150 default = ⟨.assert0, .K, [.loc 149, cellSrc gate]⟩ := by
  have hlen := chGlueCG_length QC mu eL eZ eS f2 gate hm
  rw [show 150 = (chGlueCG QC mu eL eZ eS f2 gate).length - 1 by omega,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
  simp [chGlueCG, List.getLast?_append, List.getLast?_cons]

/-- **The gated `CH` link circuit is sound** (BLUEPRINT2 §2.1): in every memory where the gadget's rows hold,
whose input lanes are the stream's, with the phase starting at `P` (`P + 40 = 8Q`), gate `1`, and the `K`
cells `nb + i` holding the bits of the child's chain length `N` (`1 ≤ N ≤ 2^logN`): if the gadget's
assertion holds, the gated link's check (`chLinkCheckG`, `m = N − 1`) holds on what phase 5 reads with the
gated targets. -/
theorem chLinkG_sound (p : Params) (D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr}
    {sig : ByteArray} {T P Q nb N : Nat} (r w : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.logN) (hD : p.logN ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hokA : SLok (chGlueAG p.logN Q nb) = true)
    (hokB : ∀ oA sh : LoopOut, SLok (chGlueBG (chQB p.logN Q) (rhoC oA p.logN) (rho'C sh p.logN) (eZC oA p.logN)
      (mbC oA p.logN) (sh.cell 5 (p.logN - 1))) = true)
    (hokC : ∀ oA sc2 oB : LoopOut, SLok (chGlueCG (chQC p.logN Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA p.logN)
      (eZC oA p.logN) (oB.cell (14 * p.logN + 126) 0) (sc2.cell 5 1) gate) = true)
    (hS : Streamed M sig T) (hT : chQC p.logN Q + 3 * 64 + 3 ≤ T) (hg : gate.val M = 1)
    (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ p.logN) (hbits : ∀ i < p.logN, FE.ofK (M.k (nb + i)) = bitQ N i)
    (h : SegsHold c M ptr (chLinkGadgetG p.logN D Q nb gate ptr).2)
    (hA : SegsAssert M ptr (chLinkGadgetG p.logN D Q nb gate ptr).2) :
    chLinkCheckG p N
      (chLinkViewT p (chShiftTargetG p N) (chSc2TargetG p N) (feAt sig) P r w pub) = true := by
  set n := p.logN with hndef
  -- decomposition
  simp only [chLinkGadgetG] at h hA
  rw [hold_bind] at h; obtain ⟨hhA, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhS, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhB, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hh2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhC, -⟩ := h
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨haC, -⟩ := hA
  -- block A
  generalize hoA : (loop [] (tplOf (chGlueAG n Q nb)) ptr).1 = oA at hhS hhB hh2 hhC haC
  have hFA : Fix (iterXv M oA 0) (chGlueAG n Q nb) (iterV M oA (chGlueAG n Q nb).length 0) := by
    rw [← hoA]; exact fix_of_loop hokA hhA (by simp)
  generalize hVA : iterV M oA (chGlueAG n Q nb).length 0 = VA at hFA
  have hlA := chGlueAG_length n Q nb
  have hcA : ∀ t < 8 * n + 165, (oA.cell t 0).val M = VA.getD t 0 := by
    intro t ht; rw [← hVA, cell_iterV (len := (chGlueAG n Q nb).length) oA (by rw [hlA]; exact ht)]
  have hbitsX : ∀ i < n, iterXv M oA 0 (kS (nb + i)) = bitQ N i := by
    intro i hi; rw [kS, iterXv_fixed]; exact hbits i hi
  obtain ⟨A1, -, -, AL, AZ, AB, AT⟩ := chGlueAG_val hS hFA hn
    (by simp [chQC, chQ2, chQB, chQ1] at hT; omega) hN1 hN2 hbitsX
  -- F's challenges
  set f : Nat → FE := fun i => feAt sig (P + 40 + 72 * i) with hf
  have hchal : samplesAt (feAt sig) P (n + 3 + 6) = (List.range (n + 9)).map f := rfl
  have hVf : ∀ i < n + 9, VA.getD i 0 = f i := by
    intro i hi; rw [A1 i hi, hf]; congr 1; omega
  have hrhoF : (samplesAt (feAt sig) P (n + 3 + 6)).take n = (List.range n).map f := by
    rw [hchal, take_range_map _ (by omega)]
  have hlamF : ((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3 = [f n, f (n + 1), f (n + 2)] := by
    rw [hchal, drop_range_map, show n + 9 - n = 9 by omega, take_range_map _ (by omega)]
    simp [List.range_succ]
  have hzetaF : (samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3) = (List.range 6).map fun i => f (n + 3 + i) := by
    rw [hchal, drop_range_map, show n + 9 - (n + 3) = 6 by omega]
  have hlamV : [VA.getD n 0, VA.getD (n + 1) 0, VA.getD (n + 2) 0] = [f n, f (n + 1), f (n + 2)] := by
    rw [hVf n (by omega), hVf (n + 1) (by omega), hVf (n + 2) (by omega)]
  have hzetaV : ((List.range 6).map fun i => VA.getD (n + 3 + i) 0) = (List.range 6).map fun i => f (n + 3 + i) := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  have hrhoV : ((List.range n).map fun i => VA.getD i 0) = (List.range n).map f := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  rw [hlamV, hzetaV, hrhoV] at AT
  -- the shift sumcheck's claim is the gated target
  have hclaimA : (oA.cell (8 * n + 164) 0).val M =
      chShiftTargetG p N (samplesAt (feAt sig) P (n + 3 + 6)) := by
    rw [hcA _ (by omega), AT, chShiftTargetG_eq p _ _ (by simp [samplesAt, hndef]), hrhoF, hlamF, hzetaF]
  -- the shift sumcheck
  have hq1 : 8 * chQ1 n Q - 40 = chP1 p P := by simp only [chQ1, chP1, ← hndef]; omega
  have hSC := sc_spec_plain (R := n) (by omega) (scTpl_ok_2 _) hD (by simp [chQ1]; omega) hS
    (by simp [chQC, chQ2, chQB, chQ1, roundLanes] at hT ⊢; omega) hhS
  set pS := ptr.adv (loop [] (tplOf (chGlueAG n Q nb)) ptr).2 with hpS
  generalize hsh : (scGadget D 2 (chQ1 n Q) .plain (oA.cell (8 * n + 164) 0) pS).1 = sh at hSC hhB hh2 hhC haC
  rw [hq1, hclaimA] at hSC
  set shiftF := scSpec (feAt sig) 3 (chP1 p P) (chShiftTargetG p N (samplesAt (feAt sig) P (n + 3 + 6)))
    (List.replicate n none) with hshiftF
  have hSlen : shiftF.1.length = n := by rw [hshiftF, lnk_scSpec_length]; simp
  have S1 : (rho'C sh n).map (Cell.val M) = shiftF.1 := by
    apply List.ext_getElem
    · simp [rho'C, hSlen]
    · intro i h1 h2
      have hi : i < n := by simpa [rho'C] using h1
      simp only [rho'C, List.getElem_map, List.getElem_range]
      rw [(hSC i hi).1, List.getD_eq_getElem _ _ h2]
  have S2 : (sh.cell 5 (n - 1)).val M = shiftF.2 := by
    rw [(hSC (n - 1) (by omega)).2, show n - 1 + 1 = n by omega, List.take_of_length_le (by simp)]
  -- block B
  have hrhoC : (rhoC oA n).map (Cell.val M) = (samplesAt (feAt sig) P (n + 3 + 6)).take n := by
    rw [hrhoF, rhoC, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.mp hi
    show (oA.cell i 0).val M = f i
    rw [hcA i (by omega), hVf i (by omega)]
  have hmbC : (mbC oA n).map (Cell.val M) = (List.range (mbC oA n).length).map (bitQ (N - 1)) := by
    simp only [mbC, List.map_map, List.length_map, List.length_range]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.mp hi
    show (oA.cell (n + 164 + 2 * i) 0).val M = _
    rw [hcA _ (by omega), AB i hi']
  have heZ : ∀ k < 64, ((eZC oA n).getD k default).val M =
      eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) k := by
    intro k hk
    have : (eZC oA n).getD k default = oA.cell (n + 96 + k) 0 := by
      simp [eZC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hzetaF, ← hzetaV, ← AZ k hk, eZs_eq n k hk, val_loc]
  have heL : ∀ k < 8, ((eLC oA n).getD k default).val M =
      eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) k := by
    intro k hk
    have : (eLC oA n).getD k default = oA.cell (n + 20 + k) 0 := by
      simp [eLC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hlamF, ← hlamV, ← AL k hk, eLs_eq n k hk, val_loc]
  have hFB := fix_of_loop (hokB oA sh) hhB (jf := 0) (by simp)
  have hrl : (rhoC oA n).length = n := by simp [rhoC]
  obtain ⟨-, B2, B3⟩ := chGlueBG_val hS hFB (by rw [hrl]; omega) (by simp [rhoC, rho'C]) (by simp [rhoC, mbC])
    (by simp only [chQC, chQ2] at hT; omega) (m := N - 1) (by rw [hrl]; omega) hmbC
  set pB := pS.adv (scGadget D 2 (chQ1 n Q) Mode.plain (oA.cell (8 * n + 164) 0) pS).2 with hpB
  generalize hoB : (loop [] (tplOf (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n)
    (sh.cell 5 (n - 1)))) pB).1 = oB at hFB B2 B3 hh2 hhC haC
  have hlenB : (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n) (sh.cell 5 (n - 1))).length =
      14 * n + 131 := by
    rw [chGlueBG_length _ _ _ _ _ _ (by simp [rhoC, rho'C]) (by simp [rhoC, mbC]), hrl]
  rw [hrl, hrhoC, S1] at B2 B3
  rw [S2] at B3
  set inSF := scalarsAt (feAt sig) (chP2 p P + 40) kBits with hinSF
  have hinS : ∀ k < 64, feAt sig (8 * (chQB n Q + 3 * k)) = inSF.getD k 0 := by
    intro k hk
    rw [hinSF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    exact congrArg (feAt sig) (by simp only [chQB, chQ1, chP2, chP1, roundLen, ← hndef]; omega)
  have hclaimB : (oB.cell (14 * n + 130) 0).val M =
      chSc2TargetG p N (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF := by
    have hsum : ∑ k ∈ Finset.range 64, ((eZC oA n).getD k default).val M * feAt sig (8 * (chQB n Q + 3 * k)) =
        ∑ q ∈ Finset.range 64, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * inSF.getD q 0 :=
      Finset.sum_congr rfl fun k hk => by
        have hk' := Finset.mem_range.mp hk
        rw [heZ k hk', hinS k hk']
    rw [cell_iterV (len := (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n)
      (sh.cell 5 (n - 1))).length) oB (by rw [hlenB]; omega), B3, chSc2TargetG_eq p _ _ _ _ (by simp [samplesAt, hndef])
      (by simp [hinSF, kBits, scalarsAt]), hsum]
    ring
  -- the two-round sumcheck
  have hq2 : 8 * chQ2 n Q - 40 = chP3 p P := by
    simp only [chQ2, chQB, chQ1, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega
  have hSC2 := sc_spec_plain (R := 2) (D := 1) (by omega) (scTpl_ok_2 _) (by norm_num) (by simp [chQ2, chQB, chQ1] <;> omega) hS
    (by simp [chQC, roundLanes] at hT ⊢ <;> omega) hh2
  set p2 := pB.adv (loop [] (tplOf (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n)
    (sh.cell 5 (n - 1)))) pB).2 with hp2
  generalize hsc2 : (scGadget 1 2 (chQ2 n Q) .plain (oB.cell (14 * n + 130) 0) p2).1 = sc2 at hSC2 hhC haC
  rw [hq2, hclaimB] at hSC2
  set sc2F := scSpec (feAt sig) 3 (chP3 p P) (chSc2TargetG p N (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
    [none, none] with hsc2F
  change ∀ i < 2, Cell.val M (sc2.cell 2 i) = sc2F.1.getD i 0 ∧ Cell.val M (sc2.cell 5 i) =
    (scSpec (feAt sig) 3 (chP3 p P) (chSc2TargetG p N (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
      (([none, none] : List (Option FE)).take (i + 1))).2 at hSC2
  have hmu : [sc2.cell 2 0, sc2.cell 2 1].map (Cell.val M) = sc2F.1 := by
    have hl : sc2F.1.length = 2 := by rw [hsc2F, lnk_scSpec_length]; rfl
    have h2 : sc2F.1 = [sc2F.1.getD 0 0, sc2F.1.getD 1 0] := by
      match hm : sc2F.1, hl with
      | [a, b], _ => rfl
    rw [h2, ← (hSC2 0 (by omega)).1, ← (hSC2 1 (by omega)).1]
    rfl
  have hf2 : (sc2.cell 5 1).val M = sc2F.2 := by
    rw [(hSC2 1 (by omega)).2]; rfl
  -- block C
  have hokC' := hokC oA sc2 oB
  have hFC := fix_of_loop hokC' hhC (jf := 0) (by simp)
  have hlast := chGlueCG_last (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n)
    (oB.cell (14 * n + 126) 0) (sc2.cell 5 1) gate rfl
  have hlenC := chGlueCG_length (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n)
    (oB.cell (14 * n + 126) 0) (sc2.cell 5 1) gate rfl
  have hAs := assert_of_loop hokC' haC (jf := 0) (by simp) (t := 150) (by rw [hlenC]; omega) (by rw [hlast])
  rw [hlast] at hAs
  simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
  have C := chGlueCG_sound hS hFC rfl (by omega) hAs hg
  rw [hf2, hmu] at C
  have heS : (oB.cell (14 * n + 126) 0).val M =
      eSum shiftF.1 ((samplesAt (feAt sig) P (n + 3 + 6)).take n) (N - 1) := by
    rw [cell_iterV (len := (chGlueBG (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (mbC oA n)
      (sh.cell 5 (n - 1))).length) oB (by rw [hlenB]; omega), B2]
  rw [heS] at C
  set ySF := scalarsAt (feAt sig) (chP4 p P + 40) kBits with hySF
  have hyS : ∀ q < 64, feAt sig (8 * (chQC n Q + 3 * q)) = ySF.getD q 0 := by
    intro q hq
    rw [hySF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hq, Option.map_some, Option.getD_some]
    exact congrArg (feAt sig)
      (by simp only [chQC, chQ2, chQB, chQ1, chP4, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega)
  have hα : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD m default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) m :=
    Finset.sum_congr rfl fun m hm => by rw [heL m (by have := Finset.mem_range.mp hm; omega)]
  have hβ : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD (m + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) (m + 1) :=
    Finset.sum_congr rfl fun m hm => by rw [heL (m + 1) (by have := Finset.mem_range.mp hm; omega)]
  have hS1 : ∑ q ∈ Finset.range 56, ((eZC oA n).getD (q + 8) default).val M * feAt sig (8 * (chQC n Q + 3 * q)) =
      ∑ q ∈ Finset.range 56, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) (q + 8) * ySF.getD q 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ (q + 8) (by omega), hyS q (by omega)]
  have hS2 : ∑ q ∈ Finset.range 8, ((eZC oA n).getD q default).val M * feAt sig (8 * (chQC n Q + 3 * (q + 56))) =
      ∑ q ∈ Finset.range 8, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * ySF.getD (q + 56) 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ q (by omega), hyS (q + 56) (by omega)]
  rw [hα, hβ, hS1, hS2] at C
  -- the gated check
  have hok : chLinkCheckG p N
      (chLinkViewT p (chShiftTargetG p N) (chSc2TargetG p N) (feAt sig) P r w pub) =
      (sc2F.2 == eSum shiftF.1 ((samplesAt (feAt sig) P (n + 3 + 6)).take n) (N - 1) *
        sumE ((List.range 64).map fun q => sumE ((List.range 4).map fun m =>
          (eqKernel sc2F.1).getD m 0 * padWeight (omegaCH (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3)
            ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3))) m q) * ySF.getD q 0)) := by
    rfl
  rw [hok, lnk_fe_beq, chLink_sum_eq _ _ _ _ (by simp [samplesAt] <;> omega) (by simp [samplesAt] <;> omega)
    (by rw [hsc2F, lnk_scSpec_length]; rfl), C]

/-- **`c₁₆·lt_N(ρ')` as a loop's cell** (`ltNIns` as a one-iteration loop). -/
theorem ltN_cell {c : Ctx} {M : Mem} {nb N : Nat} {l : List Cell} {q : Ptr} (hok : SLok (ltNIns nb l) = true)
    (h : SegsHold c M q (loop [] (tplOf (ltNIns nb l)) q).2) (hn : 1 ≤ l.length) (hN1 : 1 ≤ N)
    (hN2 : N ≤ 2 ^ l.length) (hbits : ∀ i < l.length, FE.ofK (M.k (nb + i)) = bitQ N i) :
    ((loop [] (tplOf (ltNIns nb l)) q).1.cell (7 * l.length + 4) 0).val M =
      FE.ofK c80K * ltSum (l.map (Cell.val M)) N := by
  have hF := fix_of_loop hok h (jf := 0) (by simp)
  rw [cell_iterV (len := (ltNIns nb l).length) _ (by rw [ltNIns_length]; omega)]
  exact ltNIns_val hF hn hN1 hN2 fun i hi => by rw [kS, iterXv_fixed]; exact hbits i hi

/-! ## S1: the bridge to `F` (S1-V's `chLink0`, `chShiftTarget0`, `chSc2Target0`; `LvmMaskF`'s sums) -/

theorem chLinkViewT_congr (p : Params) (tA tA' : List FE → FE) (tB tB' : List FE → List FE × FE → List FE → FE)
    (v : Nat → FE) (P : Nat) (r w : List FE) (pub : Pub)
    (hA : tA (samplesAt v P (p.logN + 3 + 6)) = tA' (samplesAt v P (p.logN + 3 + 6)))
    (hB : ∀ s : List FE × FE, s.1.length = p.logN →
      tB (samplesAt v P (p.logN + 3 + 6)) s (scalarsAt v (chP2 p P + 40) kBits) =
        tB' (samplesAt v P (p.logN + 3 + 6)) s (scalarsAt v (chP2 p P + 40) kBits)) :
    chLinkViewT p tA tB v P r w pub = chLinkViewT p tA' tB' v P r w pub := by
  unfold chLinkViewT
  simp only [hA]
  rw [hB _ (by rw [lnk_scSpec_length]; simp)]

/-- `F`'s gated shift target is `chShiftTargetG` (`ltEvalF_eq_sum`). -/
theorem chShiftTarget0_G (p : Params) (pub : Pub) (chal : List FE) (hc : chal.length = p.logN + 9)
    (hN : pub.n ≤ 2 ^ p.logN) : chShiftTarget0 p pub chal = chShiftTargetG p pub.n chal := by
  unfold chShiftTarget0 chShiftTargetG chSplit
  simp only []
  rw [ltEvalF_eq_sum _ (by rw [List.length_take, hc, Nat.min_eq_left (by omega)]; omega)]
  rfl

/-- `F`'s gated two-round target is `chSc2TargetG` (`gShiftEvalF_eq_sum`). -/
theorem chSc2Target0_G (p : Params) (pub : Pub) (chal : List FE) (shift : List FE × FE) (inS : List FE)
    (hc : chal.length = p.logN + 9) (hs : shift.1.length = p.logN) (h1 : 1 ≤ pub.n) (hN : pub.n ≤ 2 ^ p.logN) :
    chSc2Target0 p pub chal shift inS = chSc2TargetG p pub.n chal shift inS := by
  unfold chSc2Target0 chSc2TargetG chSplit
  simp only []
  rw [gShiftEvalF_eq_sum _ _ (by rw [List.length_take, hc, hs]; omega)
    (by rw [List.length_take, hc, Nat.min_eq_left (by omega)]; omega)]
  rfl

/-- `F`'s gated check is `chLinkCheckG` (`gMaskEvalF_eq_sum`). -/
theorem chLink0_check_G (p : Params) (blk : Placement) (ySlot : Nat) (i : ChLinkIn)
    (hc : i.chal.length = p.logN + 9) (hs : i.shift.1.length = p.logN) (hN : i.pub.n ≤ 2 ^ p.logN) :
    (chLink0 p blk ySlot i).1 = chLinkCheckG p i.pub.n i := by
  unfold chLink0 chLinkCheckG chSplit
  simp only []
  rw [gMaskEvalF_eq_sum _ _ (by rw [List.length_take, hc, hs]; omega)
    (by rw [List.length_take, hc, Nat.min_eq_left (by omega)]; omega)]
  rfl

/-- `F`'s gated claims are `chLinkClaimsG` (`ltEvalF_eq_sum`). -/
theorem chLink0_claims_G (p : Params) (blk : Placement) (ySlot : Nat) (i : ChLinkIn)
    (hs : i.shift.1.length = p.logN) (hN : i.pub.n ≤ 2 ^ p.logN) :
    (chLink0 p blk ySlot i).2 = chLinkClaimsG p blk ySlot i.pub.n i := by
  unfold chLink0 chLinkClaimsG chSplit
  simp only []
  rw [ltEvalF_eq_sum _ (by rw [hs]; exact hN)]
  rfl

/-- **The gated `CH` link circuit is sound for `F`'s phase-5 check** (S1-V's `chLink0` on `chLinkView`, for
`m = M3.ofParts p …`): `chLinkG_sound` with `N = pub.n`. -/
theorem chLinkG_sound0 (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    (blk : Placement) (ySlot D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr}
    {sig : ByteArray} {T P Q nb : Nat} (r w : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.logN) (hD : p.logN ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hokA : SLok (chGlueAG p.logN Q nb) = true)
    (hokB : ∀ oA sh : LoopOut, SLok (chGlueBG (chQB p.logN Q) (rhoC oA p.logN) (rho'C sh p.logN) (eZC oA p.logN)
      (mbC oA p.logN) (sh.cell 5 (p.logN - 1))) = true)
    (hokC : ∀ oA sc2 oB : LoopOut, SLok (chGlueCG (chQC p.logN Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA p.logN)
      (eZC oA p.logN) (oB.cell (14 * p.logN + 126) 0) (sc2.cell 5 1) gate) = true)
    (hS : Streamed M sig T) (hT : chQC p.logN Q + 3 * 64 + 3 ≤ T) (hg : gate.val M = 1)
    (hN1 : 1 ≤ pub.n) (hN2 : pub.n ≤ 2 ^ p.logN) (hbits : ∀ i < p.logN, FE.ofK (M.k (nb + i)) = bitQ pub.n i)
    (h : SegsHold c M ptr (chLinkGadgetG p.logN D Q nb gate ptr).2)
    (hA : SegsAssert M ptr (chLinkGadgetG p.logN D Q nb gate ptr).2) :
    (chLink0 p blk ySlot (chLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P r w pub)).1 = true := by
  have hG := chLinkG_sound p D r w pub gate hn hD hPQ hokA hokB hokC hS hT hg hN1 hN2 hbits h hA
  have hc : (samplesAt (feAt sig) P (p.logN + 3 + 6)).length = p.logN + 9 := by simp [samplesAt]
  rw [chLinkView_eq, chLinkViewT_congr p ((M3.ofParts p bf tb tcl tfv tfs tpc).chShiftTarget pub) (chShiftTargetG p pub.n)
    ((M3.ofParts p bf tb tcl tfv tfs tpc).chSc2Target pub) (chSc2TargetG p pub.n) (feAt sig) P r w pub
    (chShiftTarget0_G p pub _ hc hN2) (fun s hs => chSc2Target0_G p pub _ s _ hc hs hN1 hN2),
    chLink0_check_G p blk ySlot _ hc (by simp only [chLinkViewT]; rw [lnk_scSpec_length]; simp) hN2]
  exact hG

end Lvm.Q1
