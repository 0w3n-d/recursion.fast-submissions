-- New for lvm (HAR; WP-16b: the checks through WP-16a2's one-pass `SLokF`, moved here from `LvmFinDec`):
-- QA1's link soundness at `P20` (`logN = 20`, `ksLog = 15`, `recRowsLog = 14`; lvm2 S1-INT: S1-Q's gated
-- CH-link templates, from S1-Q's `SLokG`):
-- the template checks (`SLok`) decided as for `P8` (QA1's `LvmQLinkArithP8`), the KS template
-- (`okE`) after the re-freeze.
import LvmQLinkArithP8
import LvmQLinkArithCHSound

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1

/-! ## `SLok` in one pass (WP-16a2, moved here from `LvmFinDec` for the `P20` glue checks)

`SLok` looks every operand's row up from the template's head (quadratic: 16 s of kernel at the
600-row block E); `SLokF` walks the template once and looks the assertions up in a short list. -/

/-- The positions of a template's assertions. -/
def assertPos (ins : List Ins) : List ℕ :=
  (ins.zipIdx.filter fun x => !(x.1.op != .assert0)).map Prod.snd

/-- **`SLok` in one pass**: the reads of earlier results look the assertions up in `assertPos`. -/
def SLokF (ins : List Ins) : Bool :=
  ins.zipIdx.all fun x => (match x.1.op with
    | .muladd | .lin .. | .loadE | .assert0 => true
    | _ => false) &&
    x.1.args.all fun s => match s with
      | .loc k' => decide (k' < x.2) && !((assertPos ins).contains k')
      | .prev k' => decide (k' < ins.length) && !((assertPos ins).contains k')
      | .ext _ => true

/-- A row is no assertion iff its position is not in `assertPos`. -/
theorem bne_assert {ins : List Ins} {k : ℕ} (hk : k < ins.length) :
    ((ins.getD k default).op != .assert0) = !((assertPos ins).contains k) := by
  rw [List.getD_eq_getElem _ _ hk]
  cases hc : (assertPos ins).contains k
  · have hn : ¬ k ∈ assertPos ins := by simpa using hc
    simp only [Bool.not_false]
    by_contra hb
    apply hn
    simp only [assertPos, List.mem_map, List.mem_filter]
    exact ⟨(ins[k], k), ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]), by simpa using hb⟩, rfl⟩
  · have hm : k ∈ assertPos ins := by simpa using hc
    simp only [assertPos, List.mem_map, List.mem_filter] at hm
    obtain ⟨⟨i, k'⟩, ⟨hz, hb⟩, rfl⟩ := hm
    have := List.mem_zipIdx_iff_getElem?.mp hz
    simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [← this] at hb
    simpa using hb

/-- **`SLokF` decides `SLok`** (one direction suffices). -/
theorem SLok_of_F {ins : List Ins} (h : SLokF ins = true) : SLok ins = true := by
  unfold SLok
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  unfold SLokF at h
  rw [List.all_eq_true] at h
  have hx := h (ins[k], k) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
  rw [List.getD_eq_getElem _ _ hk]
  unfold Ins.locOk
  simp only [Bool.and_eq_true, List.all_eq_true] at hx ⊢
  refine ⟨hx.1, fun s hs => ?_⟩
  have hs' := hx.2 s hs
  cases s with
  | loc k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert (by omega)]
    exact hs'.2
  | prev k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert hs'.1]
    exact hs'.2
  | ext a => rfl

end Lvm.Fin

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ### The gated `CH` link's templates (lvm2 S1-Q: `chGlueAG/BG/CG`, `ltNIns`; v1's `chGlueA/B/C` checks
are gone with v1's gadget) -/

theorem borrowIns_shape (nb : Nat) : ∀ (a j k : Nat) (cy : Src),
    (borrowIns nb a j k cy).map Ins.shape = (borrowIns 0 a j k cy.shape).map Ins.shape
  | _, _, 0, _ => rfl
  | a, j, k + 1, cy => by
    simp only [borrowIns, List.map_append, List.map_cons, List.map_nil, shape_mulI, shape_addI, shape_shape,
      borrowIns_shape nb (a + 2) (j + 1) k (.loc (a + 1)), shape_loc]
    rfl

theorem ltRecL_shape (n : Nat) : ∀ (ys bs : List Src) (L0 : Src),
    (ltRecL n (ys.map Src.shape) (bs.map Src.shape) L0.shape).shape = (ltRecL n ys bs L0).shape
  | _ :: _, _ :: _, _ => by simp [ltRecL, shape_loc]
  | [], _, _ => by simp [ltRecL, shape_shape]
  | _ :: _, [], _ => by simp [ltRecL, shape_shape]

theorem ltRecP_shape (n : Nat) : ∀ (ys bs : List Src) (P0 : Src),
    (ltRecP n (ys.map Src.shape) (bs.map Src.shape) P0.shape).shape = (ltRecP n ys bs P0).shape
  | _ :: _, _ :: _, _ => by simp [ltRecP, shape_loc]
  | [], _, _ => by simp [ltRecP, shape_shape]
  | _ :: _, [], _ => by simp [ltRecP, shape_shape]

theorem ltRecIns_shape (z : Src) (n : Nat) : ∀ (ys bs : List Src) (L0 P0 : Src),
    (ltRecIns z n ys bs L0 P0).map Ins.shape =
      (ltRecIns z.shape n (ys.map Src.shape) (bs.map Src.shape) L0.shape P0.shape).map Ins.shape
  | y0 :: y, b0 :: bs, L0, P0 => by
    simp only [List.map_cons, ltRecIns, List.map_append, ltRecIns_shape z n y bs L0 P0, List.length_map]
    congr 1
    simp only [ltLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_shape, shape_loc,
      ltRecL_shape, ltRecP_shape]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem okAG_P20 (Q nb : Nat) : SLok (chGlueAG 20 Q nb) = true := by
  rw [← SLok_shape, show (chGlueAG 20 Q nb).map Ins.shape = (chGlueAG 20 0 0).map Ins.shape from rfl, SLok_shape]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem preRecDOut_shape (n : Nat) : ∀ (xs bs : List Src) (base : Src × Src × Src),
    preRecDOut n (xs.map Src.shape) (bs.map Src.shape) (base.1.shape, base.2.1.shape, base.2.2.shape) =
      ((preRecDOut n xs bs base).1.shape, (preRecDOut n xs bs base).2.1.shape, (preRecDOut n xs bs base).2.2.shape)
  | _ :: _, _ :: _, _ => by simp [preRecDOut, shape_loc]
  | [], _, _ => by simp [preRecDOut]
  | _ :: _, [], _ => by simp [preRecDOut]

theorem preRecDIns_shape (z : Src) (n : Nat) : ∀ (xs ys bs : List Src) (base : Src × Src × Src),
    (preRecDIns z n xs ys bs base).map Ins.shape =
      (preRecDIns z.shape n (xs.map Src.shape) (ys.map Src.shape) (bs.map Src.shape)
        (base.1.shape, base.2.1.shape, base.2.2.shape)).map Ins.shape
  | x0 :: x, y0 :: y, b0 :: bs, base => by
    simp only [List.map_cons, preRecDIns, List.map_append, preRecDIns_shape z n x y bs base, List.length_map,
      preRecDOut_shape]
    congr 1
    simp only [preLevelD, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_addI, shape_shape, shape_loc]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl

theorem okBG_P20 (Q : Nat) (oA sh : LoopOut) :
    SLok (chGlueBG (chQB 20 Q) (rhoC oA 20) (rho'C sh 20) (eZC oA 20) (mbC oA 20) (sh.cell 5 (20 - 1))) = true := by
  rw [← SLok_shape]
  simp only [chGlueBG, List.map_append]
  rw [loadsAt_shape, dotIns_shape, preRecDIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc,
    shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, mbC,
    List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okCG_P20 (Q : Nat) (gate : Cell) (oA sc2 oB : LoopOut) :
    SLok (chGlueCG (chQC 20 Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA 20) (eZC oA 20)
      (oB.cell (14 * 20 + 126) 0) (sc2.cell 5 1) gate) = true := by
  rw [← SLok_shape]
  simp only [chGlueCG, List.map_append]
  rw [loadsAt_shape, eqTabGo_shape, dotIns_shape, dotIns_shape (n := 78), dotIns_shape (n := 82),
    dotIns_shape (n := 138)]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc,
    shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, eZC, eLC,
    List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okN (nb : Nat) (l : List Cell) :
    (ltNIns nb l).map Ins.shape = (ltNIns 0 (List.replicate l.length default)).map Ins.shape := by
  simp only [ltNIns, List.map_append, List.map_cons, List.map_nil, List.length_replicate]
  rw [borrowIns_shape, borrowIns_shape 0 2 0 l.length, ltRecIns_shape, ltRecIns_shape (n := 2 * l.length + 2)
    (ys := (List.replicate l.length default).map cellSrc)]
  simp only [List.length_replicate, List.map_map, Function.comp_def, shape_cellSrc, List.map_const',
    List.map_replicate]
  rfl

theorem okN_P20 (nb : Nat) (l : List Cell) (hl : l.length = 20) : SLok (ltNIns nb l) = true := by
  rw [← SLok_shape, okN, hl, SLok_shape]
  apply Lvm.Fin.SLok_of_F
  decide +kernel


-- `okE` at `P20` depends on the sponge-block count literally (`preRecIns` walks its bits): decided after the
-- re-freeze, as `okE_P8`.

end Lvm.Q1
