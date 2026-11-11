import LvmQLinkArithRows
import LvmQLinkArithRead

/-!
# QA1 links: the `CH` link circuit (phase 5)

Three straight-line blocks around two sumcheck gadgets (`scGadget`):

* **A** (`chGlueA`, `2n + 166` rows, `n = logN`): load the `n + 9` challenges `ρ, λ, ζ`; `eq(λ, ·)` (8) and
  `eq(ζ, ·)` (64) as `eqKernel`; `Pad43`'s constant bits; `Πρ`; the shift sumcheck's claim
  `C·(1 + Πρ)` (= `chShiftTarget0`, `chGlueA_target`).
* the shift sumcheck (`n` rounds, degree 2);
* **B** (`chGlueB`): the 64 `in` slices, `Σ_p eq(ζ,p)·inS_p`, `(eqEval, shiftEval)(ρ, ρ')`, the second
  sumcheck's claim (= `chSc2Target0`);
* the two-round sumcheck;
* **C** (`chGlueC`): the 64 `Y` slices, `eq(μ, ·)`, `α`, `β`, the two halves of `Σ_q W̃(μ,q)·yS_q`,
  `eqMasked`, and the gated assertion `gate·(f₂ − eqMasked·Σ) = 0` (`chLink0`'s check).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Helpers -/

/-- A cell as an operand of a template. -/
def cellSrc (c : Cell) : Src := .ext c.addr

theorem iterXv_cell (M : Mem) (o : LoopOut) (jf : Nat) (c : Cell) : iterXv M o jf (cellSrc c) = c.val M := by
  simp only [iterXv, cellSrc, Src.toOpd, Opd.val_abs, Cell.addr, Addr.at, dot_nil, Nat.add_zero]
  rfl

theorem iterXv_fixed (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem seg_whole (ins : List Ins) : Seg ins 0 ins := by intro i _; simp

/-- A load of the fixed lanes `q, q + 1, q + 2` is the stream's scalar at byte `8q`. -/
theorem load_fixed {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf : Nat)
    (V : List FE) {q : Nat} (hq : q + 2 < T) :
    (loadI q []).eval (iterXv M o jf) V = feAt sig (8 * q) := by
  show iterXv M o jf (.ext ⟨.K, q, []⟩) + FE.y * iterXv M o jf (.ext ⟨.K, q + 1, []⟩) +
    FE.y * FE.y * iterXv M o jf (.ext ⟨.K, q + 2, []⟩) = _
  rw [iterXv_fixed, iterXv_fixed, iterXv_fixed]
  exact load_feAt hS hq

/-- The loads of `N` scalars at lanes `q + s·i`. -/
def loadsAt (q s N : Nat) : List Ins := (List.range N).map fun i => loadI (q + s * i) []

theorem loadsAt_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {ins : List Ins} {V : List FE} (hF : Fix (iterXv M o jf) ins V) {n q s N : Nat}
    (hseg : Seg ins n (loadsAt q s N)) (hlen : n + N ≤ ins.length) (hT : q + s * N + 2 < T + s) {i : Nat}
    (hi : i < N) : V.getD (n + i) 0 = feAt sig (8 * (q + s * i)) := by
  have hrow : (loadsAt q s N).getD i default = loadI (q + s * i) [] := by
    simp [loadsAt, List.getD_eq_getElem?_getD, hi]
  rw [fix_seg hF hseg (by simpa [loadsAt] using hlen) (by simpa [loadsAt] using hi)
    (by rw [hrow]; simp [loadI]), hrow]
  apply load_fixed hS
  have : s * i + s ≤ s * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

/-! ## Block A: the shift sumcheck's claim -/

/-- `λ`'s sources (challenges `n … n + 2`). -/
def lamS (n : Nat) : List Src := [.loc n, .loc (n + 1), .loc (n + 2)]
/-- `ζ`'s sources (challenges `n + 3 … n + 8`). -/
def zetaS (n : Nat) : List Src := (List.range 6).map fun i => .loc (n + 3 + i)
/-- `ρ`'s sources (challenges `0 … n − 1`). -/
def rhoS (n : Nat) : List Src := (List.range n).map Src.loc

/-- `eq(λ, k)`'s source. -/
def eLs (n k : Nat) : Src := (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).getD k default
/-- `eq(ζ, k)`'s source. -/
def eZs (n k : Nat) : Src := (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).getD k default

/-- `Pad43`'s constant bits `eq(λ,0)(eq(ζ,0) + eq(ζ,1) + eq(ζ,6)) + eq(λ,4)eq(ζ,8)` at `n + 160 … n + 163`. -/
def padRows (n : Nat) : List Ins :=
  [addI (eZs n 0) (eZs n 1), addI (.loc (n + 160)) (eZs n 6), mulI (eLs n 0) (.loc (n + 161)) (.loc (n + 9)),
    mulI (eLs n 4) (eZs n 8) (.loc (n + 162))]

/-- **Block A**: loads (`0 … n + 8`, lanes `Q + 9i`), zero (`n + 9`), one (`n + 10`), `eq(λ,·)`
(`n + 11`, 17 rows), `eq(ζ,·)` (`n + 28`, 132 rows), `Pad43`'s bits (`n + 160`), `Πρ` (`n + 164`,
`n` rows), `1 + Πρ` (`2n + 164`), the claim (`2n + 165`). -/
def chGlueA (n Q : Nat) : List Ins :=
  loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))

theorem eqTab3_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 3) :
    (eqTabGo z m [o] l).length = 17 := by
  match l, hl with
  | [a, b, c], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem eqTab6_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 6) :
    (eqTabGo z m [o] l).length = 132 := by
  match l, hl with
  | [a, b, c, d, e, f], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueA_length (n Q : Nat) : (chGlueA n Q).length = 2 * n + 166 := by
  simp only [chGlueA, List.length_append, loadsAt, List.length_map, List.length_range,
    eqTab3_length _ _ _ _ (rfl : (lamS n).length = 3),
    eqTab6_length _ _ _ _ (by simp [zetaS] : (zetaS n).length = 6), padRows, mulChainIns_length, rhoS,
    List.length_cons, List.length_nil]
  omega

theorem seg_split {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) :
    Seg ins n A ∧ Seg ins (n + A.length) B := ⟨seg_append_left h, seg_append_right h⟩

theorem seg_at {ins : List Ins} {n m : Nat} {seg : List Ins} (h : Seg ins n seg) (e : n = m) : Seg ins m seg :=
  e ▸ h

theorem eqKernel_map_getD (l : List FE) {k : Nat} (hk : k < 2 ^ l.length) :
    (eqKernel l).getD k 0 = eqW l k := eqKernel_getD l hk

/-- Block A's values, on any fixed point of its rows over a streamed memory. -/
theorem chGlueA_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n Q : Nat} {V : List FE} (hF : Fix (iterXv M o jf) (chGlueA n Q) V) (hn : 1 ≤ n)
    (hT : Q + 9 * (n + 9) + 2 < T + 9) :
    (∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i))) ∧
    V.getD (n + 9) 0 = 0 ∧ V.getD (n + 10) 0 = 1 ∧
    (∀ k < 8, (eLs n k).val (iterXv M o jf) V =
      eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k) ∧
    (∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k) ∧
    V.getD (2 * n + 163) 0 = ((List.range n).map fun i => V.getD i 0).prod ∧
    V.getD (2 * n + 165) 0 =
      (eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 0 *
        (eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 0 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 1 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 6) +
        eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 4 *
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 8) *
      (1 + ((List.range n).map fun i => V.getD i 0).prod) := by
  have hlen := chGlueA_length n Q
  have hs : Seg (chGlueA n Q) 0 (loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))) :=
    seg_whole _
  have lL : (loadsAt Q 9 (n + 9)).length = n + 9 := by simp [loadsAt]
  have lEL : (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n)).length = 17 := eqTab3_length _ _ _ _ rfl
  have lEZ : (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n)).length = 132 :=
    eqTab6_length _ _ _ _ (by simp [zetaS])
  have lM : (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n)).length = n := by
    rw [mulChainIns_length]; simp [rhoS]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEL, s3⟩ := seg_split s2
  obtain ⟨sEZ, s4⟩ := seg_split s3
  obtain ⟨sP, s5⟩ := seg_split s4
  obtain ⟨sM, sF⟩ := seg_split s5
  replace sZ := seg_at (m := n + 9) sZ (by simp [lL])
  replace sEL := seg_at (m := n + 11) sEL (by simp [lL] <;> omega)
  replace sEZ := seg_at (m := n + 28) sEZ (by simp [lL, lEL] <;> omega)
  replace sP := seg_at (m := n + 160) sP (by simp [lL, lEL, lEZ] <;> omega)
  replace sM := seg_at (m := n + 164) sM (by simp [lL, lEL, lEZ, padRows] <;> omega)
  replace sF := seg_at (m := 2 * n + 164) sF (by simp [lL, lEL, lEZ, lM, padRows] <;> omega)
  -- loads
  have hL : ∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hi
    rwa [Nat.zero_add] at this
  -- zero and one
  have hz : V.getD (n + 9) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 10) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [linI])
    rw [show n + 9 + 1 = n + 10 by omega] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 9)).val (iterXv M o jf) V = 0 := hz
  -- eq tables
  have hEL := eqTab_val hF hzs (lamS n) (n + 11) [.loc (n + 10)] sEL
    (by rw [eqTab3_length _ _ _ _ rfl, hlen]; omega)
  have hEZ := eqTab_val hF hzs (zetaS n) (n + 28) [.loc (n + 10)] sEZ
    (by rw [eqTab6_length _ _ _ _ (by simp [zetaS]), hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1] at hEL hEZ
  have hlam : (lamS n).map (Src.val (iterXv M o jf) V) = [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] := by
    simp [lamS]
  have hzeta : (zetaS n).map (Src.val (iterXv M o jf) V) = (List.range 6).map fun i => V.getD (n + 3 + i) 0 := by
    simp [zetaS]
  rw [hlam] at hEL
  rw [hzeta] at hEZ
  have eL : ∀ k < 8, (eLs n k).val (iterXv M o jf) V = eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).length := by
      have := congrArg List.length hEL
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eLs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEL, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  have eZ : ∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).length := by
      have := congrArg List.length hEZ
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eZs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEZ, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  -- Pad43's bits
  have p0 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 0) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p1 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 1) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p2 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 2) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p3 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 3) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  simp only [padRows, List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_mulI, val_loc, hz, add_zero,
    Nat.add_zero] at p0 p1 p2 p3
  rw [show n + 160 + 1 = n + 161 by omega] at p1
  rw [show n + 160 + 2 = n + 162 by omega, p1, p0] at p2
  rw [show n + 160 + 3 = n + 163 by omega, p2] at p3
  rw [eL 0 (by omega), eL 4 (by omega), eZ 0 (by omega), eZ 1 (by omega), eZ 6 (by omega),
    eZ 8 (by omega)] at p3
  -- Πρ
  have hM := mulChain_val hF hzs (rhoS n) (n + 164) (.loc (n + 10))
    sM (by rw [hlen]; simp [rhoS]; omega)
  have hsrc : sumSrc (n + 164) (.loc (n + 10)) (rhoS n) = .loc (2 * n + 163) := by
    simp only [sumSrc, rhoS, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by omega), show n + 164 + n - 1 = 2 * n + 163 by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul] at hM
  have hrho : (rhoS n).map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => V.getD i 0 := by
    simp [rhoS]
  rw [hrho] at hM
  -- the claim
  have f0 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
  have f1 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', eval_mulI, val_loc, Nat.add_zero] at f0 f1
  rw [show 2 * n + 164 + 1 = 2 * n + 165 by omega, f0, hz, p3, hM] at f1
  refine ⟨hL, hz, h1, eL, eZ, hM, ?_⟩
  rw [f1, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]
  ring

/-! ## Block B: the second sumcheck's claim -/

/-- **Block B**: the 64 `in` slices (lanes `QB + 3k`), zero (64), one (65), `Σ_k eq(ζ,k)·inS_k` (66, 64 rows,
at 129), `(eqEval, shiftEval)(ρ, ρ')` (130, `8n` rows), the claim `S·dot + f₁` (`8n + 130`). -/
def chGlueB (QB : Nat) (rho rho' eZ : List Cell) (f1 : Cell) : List Ins :=
  loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))

theorem chGlueB_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QB : Nat} {rho rho' eZ : List Cell} {f1 : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueB QB rho rho' eZ f1) V) (hn : 1 ≤ rho.length) (hl : rho.length = rho'.length)
    (hT : QB + 3 * 64 + 2 < T + 3) :
    (∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k))) ∧
    V.getD (8 * rho.length + 123) 0 = eqEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) ∧
    V.getD (8 * rho.length + 130) 0 = shiftEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) *
      (∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k))) + f1.val M := by
  have hs : Seg (chGlueB QB rho rho' eZ f1) 0 (loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))) := seg_whole _
  have lS := shiftRecIns_length (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl)
  have hlen : (chGlueB QB rho rho' eZ f1).length = 8 * rho.length + 131 := by
    simp only [chGlueB, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length, lS,
      List.length_cons, List.length_nil]; omega
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sD, s3⟩ := seg_split s2
  obtain ⟨sR, sF⟩ := seg_split s3
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sD := seg_at (m := 66) sD (by simp [loadsAt])
  replace sR := seg_at (m := 130) sR (by simp [loadsAt, dotIns_length])
  replace sF := seg_at (m := 8 * rho.length + 130) sF (by simp [loadsAt, dotIns_length, lS]; omega)
  have hL : ∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k)) := by
    intro k hk
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hk
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hD := dot_val hF ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) 66 (.loc 64) sD
    (by rw [hlen]; simp <;> omega)
  have hDs : dotSrc 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) = .loc 129 := by
    simp [dotSrc]
  rw [hDs, val_loc, val_loc, hz, zero_add] at hD
  have hR := shiftRec_val hF (zero := .loc 64) hz 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl) h1 hz sR (by rw [hlen]; simp <;> omega)
  have hE : shiftRecE 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) = .loc (8 * rho.length + 123) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecE] <;> omega
  have hSs : shiftRecS 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 64) = .loc (8 * rho.length + 129) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecS] <;> omega
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  rw [hE, hSs, val_loc, val_loc, hmap, hmap] at hR
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, eval_mulI, val_loc, Nat.add_zero] at f0
  have hsum : (List.map (fun ab => ab.1.val (iterXv M o jf) V * ab.2.val (iterXv M o jf) V)
      (List.map (fun k => (cellSrc (eZ.getD k default), Src.loc k)) (List.range 64))).sum =
      ∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k)) := by
    rw [List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    show iterXv M o jf (cellSrc (eZ.getD k default)) * V.getD k 0 = _
    rw [iterXv_cell, hL k hk']
  refine ⟨hL, hR.1, ?_⟩
  rw [f0, hR.2, hD, hsum]
  show _ + iterXv M o jf (cellSrc f1) = _
  rw [iterXv_cell]

/-! ## Block C: the `CH` link's check -/

/-- `eq(μ, m)`'s source in block C. -/
def eMus (mu : List Cell) (m : Nat) : Src := (eqTabOut 66 [.loc 65] (mu.map cellSrc)).getD m default

/-- **Block C**: the 64 `Y` slices (lanes `QC + 3q`), zero (64), one (65), `eq(μ,·)` (66, 8 rows),
`α` (74, at 77), `β` (78, at 81), `S₁ = Σ_{q<56} eq(ζ,q+8)·yS_q` (82, at 137), `S₂` (138, at 145),
`β S₂` (146), `α S₁ + β S₂` (147), `Πρ'` (148, `n` rows), `eqMasked = Πρ·Πρ' + eqEval` (`148 + n`),
the target (`149 + n`), `f₂ + target` (`150 + n`), the gated assertion (`151 + n`). -/
def chGlueC (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) : List Ins :=
  loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + rho'.length)) (cellSrc eqE),
      mulI (.loc (148 + rho'.length)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + rho'.length)),
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩]))))))))

theorem eqTab2_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 2) :
    (eqTabGo z m [o] l).length = 8 := by
  match l, hl with
  | [a, b], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueC_length (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length = 152 + rho'.length := by
  simp only [chGlueC, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
    mulChainIns_length, eqTab2_length _ _ _ _ (by simpa using hm : (mu.map cellSrc).length = 2),
    List.length_cons, List.length_nil]
  omega

/-- **Block C's assertion**: with gate `1`, `f₂ = (Πρ·Πρ' + eqEval)·(α S₁ + β S₂)`. -/
theorem chGlueC_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QC : Nat} {mu eL eZ rho' : List Cell} {prodRho eqE f2 gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) V) (hm : mu.length = 2)
    (hT : QC + 3 * 64 + 2 < T + 3)
    (hn : 1 ≤ rho'.length)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (150 + rho'.length) 0 = 0) (hg : gate.val M = 1) :
    f2.val M = (prodRho.val M * (rho'.map (Cell.val M)).prod + eqE.val M) *
      ((∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M) *
          (∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q))) +
        (∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M) *
          (∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))))) := by
  set n := rho'.length with hndef
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  have hs : Seg (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) 0
    (loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + n)) (cellSrc eqE),
      mulI (.loc (148 + n)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + n)),
      ⟨.assert0, .K, [.loc (150 + n), cellSrc gate]⟩]))))))))) := seg_whole _
  have lEM : (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc)).length = 8 := eqTab2_length _ _ _ _ (by simpa using hm)
  have lMC : (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc)).length = n := by
    rw [mulChainIns_length]; simp [hndef]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEM, s3⟩ := seg_split s2
  obtain ⟨sDA, s4⟩ := seg_split s3
  obtain ⟨sDB, s5⟩ := seg_split s4
  obtain ⟨sD1, s6⟩ := seg_split s5
  obtain ⟨sD2, s7⟩ := seg_split s6
  obtain ⟨sMM, s8⟩ := seg_split s7
  obtain ⟨sMC, sF⟩ := seg_split s8
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sEM := seg_at (m := 66) sEM (by simp [loadsAt])
  replace sDA := seg_at (m := 74) sDA (by simp [loadsAt, lEM])
  replace sDB := seg_at (m := 78) sDB (by simp [loadsAt, lEM, dotIns_length])
  replace sD1 := seg_at (m := 82) sD1 (by simp [loadsAt, lEM, dotIns_length])
  replace sD2 := seg_at (m := 138) sD2 (by simp [loadsAt, lEM, dotIns_length])
  replace sMM := seg_at (m := 146) sMM (by simp [loadsAt, lEM, dotIns_length])
  replace sMC := seg_at (m := 148) sMC (by simp [loadsAt, lEM, dotIns_length])
  replace sF := seg_at (m := 148 + n) sF (by simp [loadsAt, lEM, dotIns_length, lMC] <;> omega)
  have hL : ∀ q < 64, V.getD q 0 = feAt sig (8 * (QC + 3 * q)) := by
    intro q hq
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hq
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc 64).val (iterXv M o jf) V = 0 := hz
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  -- eq(μ, ·)
  have hEM := eqTab_val hF hzs (mu.map cellSrc) 66 [.loc 65] sEM (by rw [lEM, hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1, hmap] at hEM
  have eMu : ∀ m < 4, (eMus mu m).val (iterXv M o jf) V = eqW (mu.map (Cell.val M)) m := by
    intro m hm4
    have hlo : m < (eqTabOut 66 [.loc 65] (mu.map cellSrc)).length := by
      have := congrArg List.length hEM
      rw [List.length_map, foldl_eqStep_length] at this; simp [hm] at this; omega
    rw [eMus, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlo, hEM, ← eqKernel_foldl,
      eqKernel_getD _ (by simp [hm]; omega)]
  -- the dot products
  have hDA := dot_val hF _ 74 (.loc 64) sDA (by rw [hlen]; simp <;> omega)
  have hDB := dot_val hF _ 78 (.loc 64) sDB (by rw [hlen]; simp <;> omega)
  have hD1 := dot_val hF _ 82 (.loc 64) sD1 (by rw [hlen]; simp <;> omega)
  have hD2 := dot_val hF _ 138 (.loc 64) sD2 (by rw [hlen]; simp <;> omega)
  simp only [dotSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range,
    OfNat.ofNat_ne_zero, if_false, val_loc, hz, zero_add, List.map_map] at hDA hDB hD1 hD2
  rw [list_sum_range] at hDA hDB hD1 hD2
  simp only [Function.comp_def, hcell, val_loc] at hDA hDB hD1 hD2
  have hA4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD x default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have hB4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD (x + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have h56 : ∑ x ∈ Finset.range 56, (eZ.getD (x + 8) default).val M * V.getD x 0 =
      ∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q)) :=
    Finset.sum_congr rfl fun q hq => by rw [hL q (by have := Finset.mem_range.mp hq; omega)]
  have h8 : ∑ x ∈ Finset.range 8, (eZ.getD x default).val M * V.getD (x + 56) 0 =
      ∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))) :=
    Finset.sum_congr rfl fun q hq => by rw [hL (q + 56) (by have := Finset.mem_range.mp hq; omega)]
  rw [hA4] at hDA
  rw [hB4] at hDB
  rw [h56] at hD1
  rw [h8] at hD2
  -- the products and the check
  have m0 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have m1 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, val_loc, hz, add_zero, Nat.add_zero] at m0 m1
  have hMC := mulChain_val hF hzs (rho'.map cellSrc) 148 (.loc 65) sMC (by rw [hlen]; simp <;> omega)
  have hsrc : sumSrc 148 (.loc 65) (rho'.map cellSrc) = .loc (147 + n) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.length_map]
    rw [if_neg (by intro h; rw [h] at hndef; simp at hndef; omega), show 148 + rho'.length - 1 = 147 + n by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul, hmap] at hMC
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  have f2' := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 2) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_addI, val_loc, hz, add_zero,
    Nat.add_zero, hcell] at f0 f1 f2'
  rw [show 148 + n + 1 = 149 + n by omega] at f1
  rw [show 148 + n + 2 = 150 + n by omega] at f2'
  rw [hcell, hg, one_mul, f2', f1, f0, hMC, m1, m0, hDA, hDB, hD1, hD2] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination hA

/-! ## Where the tables are -/

theorem getD_range_loc (b k N : Nat) (hk : k < N) :
    ((List.range N).map fun i => Src.loc (b + i)).getD k default = .loc (b + k) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem eLs_eq (n k : Nat) (hk : k < 8) : eLs n k = .loc (n + 20 + k) := by
  simp only [eLs, lamS, eqTabOut, eqLevelOut, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show n + 11 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 = n + 20 by omega, getD_range_loc _ _ _ (by omega)]

theorem eZs_eq (n k : Nat) (hk : k < 64) : eZs n k = .loc (n + 96 + k) := by
  have hz : zetaS n = [.loc (n + 3 + 0), .loc (n + 3 + 1), .loc (n + 3 + 2), .loc (n + 3 + 3), .loc (n + 3 + 4),
      .loc (n + 3 + 5)] := rfl
  simp only [eZs, hz, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show n + 28 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 + 2 * (2 * (2 * (0 + 1))) + 1 +
      2 * (2 * (2 * (2 * (0 + 1)))) + 1 + 2 * (2 * (2 * (2 * (2 * (0 + 1))))) + 1 = n + 96 by omega,
    getD_range_loc _ _ _ (by omega)]

theorem eMus_eq (c₀ c₁ : Cell) (m : Nat) (hm : m < 4) : eMus [c₀, c₁] m = .loc (70 + m) := by
  simp only [eMus, List.map_cons, List.map_nil, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show 66 + 1 + 2 * (0 + 1) + 1 = 70 by omega, getD_range_loc _ _ _ (by omega)]

/-! ## S1: the gated link (lvm2 BLUEPRINT2 §2.1)

The link constrains rows `k ≤ m` only, `m = N − 1` for the child's chain length `N` (`1 ≤ N ≤ 2^n`):
the shift sumcheck's target is `C·lt_m(ρ)`, its kernel `S̃ = Σ_{k<m} eq(ρ,k)·eq(ρ',k+1)` (`preSum ρ' ρ m`),
the final's `Ẽ' = Σ_{k<m} eq(ρ,k)·eq(ρ',k)` (`eSum ρ' ρ m`), and the constant lanes' claims carry
`lt_N(ρ') = lt_m(ρ') + eq(ρ', m)`. The circuit gets `m`'s bits from `N`'s `BITS` bits by a borrow chain
(`borrowIns`) and evaluates the closed forms by low-bit recursions whose bit is a cell (`ltRecIns`,
`preRecDIns`; the static `preRecIns` of the `KS` link with `H`'s bits as cells). -/

/-! ### Closed forms (`F`'s side, exact sums) -/

/-- `lt_H(y) = Σ_{k<H} eq(y, k)`. -/
def ltSum (y : List FE) (H : Nat) : FE := ∑ k ∈ Finset.range H, eqW y k

/-- Bit `j` of `N` as `0`/`1` (`Lvm.Har.bitE`). -/
def bitQ (N j : Nat) : FE := if N.testBit j then 1 else 0

/-- The borrow of `N − 1` into bit `j` (`Lvm.Har.carryE`). -/
def carryQ (N j : Nat) : FE := if N % 2 ^ j = 0 then 1 else 0

theorem fe_two_q : (1 : FE) + 1 = 0 := CharTwo.add_self_eq_zero 1

-- adapted from LvmQAsmArith2Claim (`mod_two_pow_succ_eq_zero`, `testBit_pred`, `carry_succ`, `pred_bit`;
-- lvm/base 8e1f5d70): that module's closure contains this one.
theorem mod_two_pow_succ_eq_zeroQ (n j : Nat) :
    n % 2 ^ (j + 1) = 0 ↔ (n % 2 ^ j = 0 ∧ n.testBit j = false) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> rw [h] <;> simp

theorem testBit_predQ (n j : Nat) (hn : 1 ≤ n) :
    (n - 1).testBit j = (n.testBit j ^^ decide (n % 2 ^ j = 0)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdm := Nat.div_add_mod n (2 ^ j)
  have hr := Nat.mod_lt n hP
  generalize n / 2 ^ j = q at hdm
  generalize n % 2 ^ j = r at hdm hr ⊢
  subst hdm
  by_cases h0 : r = 0
  · subst h0
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hn
      · omega⟩
    have e : 2 ^ j * (q' + 1) + 0 - 1 = 2 ^ j * q' + (2 ^ j - 1) := by
      rw [Nat.mul_succ]; omega
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rcases Nat.mod_two_eq_zero_or_one q' with h | h <;> simp [h, Nat.add_mod]
  · have e : 2 ^ j * q + r - 1 = 2 ^ j * q + (r - 1) := by omega
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    simp [h0]

theorem carryQ_succ (N j : Nat) : carryQ N (j + 1) = carryQ N j * bitQ N j + carryQ N j := by
  simp only [carryQ, bitQ]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;>
    simp [h1, h2, mod_two_pow_succ_eq_zeroQ, fe_two_q]

theorem bitQ_pred (N j : Nat) (hN : 1 ≤ N) : bitQ (N - 1) j = bitQ N j + carryQ N j := by
  simp only [bitQ, carryQ, testBit_predQ N j hN]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;> simp [h1, h2, fe_two_q]

theorem carryQ_zero (N : Nat) : carryQ N 0 = 1 := by simp [carryQ, Nat.mod_one]

theorem bitQ_zero (H : Nat) : bitQ H 0 = if H % 2 = 1 then 1 else 0 := by
  simp only [bitQ, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one H with h | h <;> simp [h]

theorem bitQ_succ (H i : Nat) : bitQ H (i + 1) = bitQ (H / 2) i := by
  simp only [bitQ, Nat.testBit_succ]

theorem eqW_cons (r : FE) (rs : List FE) (x : Nat) :
    eqW (r :: rs) x = (if x % 2 = 1 then r else 1 + r) * eqW rs (x / 2) := by
  simp only [eqW, sub_eq_add']

theorem ltSum_cons (y0 : FE) (y : List FE) (H : Nat) :
    ltSum (y0 :: y) H = ltSum y (H / 2) + (1 + y0) * bitQ H 0 * eqW y (H / 2) := by
  unfold ltSum
  rw [sum_range_parity (fun k => eqW (y0 :: y) k) H]
  simp only [eqW_even', eqW_odd']
  rw [← Finset.mul_sum, ← Finset.mul_sum, bitQ_zero]
  rcases Nat.mod_two_eq_zero_or_one H with h | h
  · rw [h, Nat.add_zero, if_neg (by decide), mul_zero, zero_mul, add_zero]
    linear_combination (y0 * ∑ k ∈ Finset.range (H / 2), eqW y k) * fe_two_q
  · rw [h, if_pos rfl, mul_one, Finset.sum_range_succ]
    linear_combination (y0 * ∑ k ∈ Finset.range (H / 2), eqW y k) * fe_two_q

/-- `eq(y, H)` with bit `H % 2` as `b ∈ {0, 1}`: `(1 + b + y₀)·eq(y', H/2)`. -/
theorem eqW_cons_bit (y0 : FE) (y : List FE) (H : Nat) :
    eqW (y0 :: y) H = (1 + bitQ H 0 + y0) * eqW y (H / 2) := by
  rw [eqW_cons, bitQ_zero]
  rcases Nat.mod_two_eq_zero_or_one H with h | h
  · rw [h, if_neg (by decide), if_neg (by decide), add_zero]
  · rw [h, if_pos rfl, if_pos rfl, fe_two_q, zero_add]

/-- **The gated shift sumcheck's target** `C·lt_m(ρ)`, `m = N − 1` for the chain length `N` (v1
`chShiftTarget0`: `C·(1 + eq(ρ, 1ⁿ))`, the case `N = 2ⁿ`). -/
def chShiftTargetG (p : Params) (N : Nat) (chal : List FE) : FE :=
  let (rho, lam, zeta) := chSplit p chal
  padConst (omegaCH lam zeta) * ltSum rho (N - 1)

/-- **The gated two-round sumcheck's claim** `f₁ + S̃_m(ρ, ρ')·Σ_p eq(ζ, p) inS_p`. -/
def chSc2TargetG (p : Params) (N : Nat) (chal : List FE) (shift : List FE × FE) (inS : List FE) : FE :=
  let (rho, _, zeta) := chSplit p chal
  shift.2 + preSum shift.1 rho (N - 1) * dot (eqKernel zeta) inS

/-- **The gated `CH` link's check** (v1 `chLink0`'s `ok` with `eqMasked` replaced by `Ẽ'_m(ρ, ρ')`). -/
def chLinkCheckG (p : Params) (N : Nat) (i : ChLinkIn) : Bool :=
  let (rho, lam, zeta) := chSplit p i.chal
  let om := omegaCH lam zeta
  let rho' := i.shift.1
  let eMu := eqKernel i.sc2.1
  let wt (q : Nat) : FE := sumE ((List.range 4).map fun m => eMu.getD m 0 * padWeight om m q)
  i.sc2.2 == eSum rho' rho (N - 1) * sumE ((List.range 64).map fun q => wt q * i.ySlices.getD q 0)

/-- **The gated `CH` link's claims** (v1 `chLink0`'s with the constant lanes' values `c_l·lt_N(ρ')`). -/
def chLinkClaimsG (p : Params) (blk : Placement) (ySlot N : Nat) (i : ChLinkIn) : List (Com × BlockClaim) :=
  let (_, lam, _) := chSplit p i.chal
  let rho' := i.shift.1
  let mu := i.sc2.1
  let inPt := rho' ++ lam ++ [0, 0, 0]
  let yPt := rho' ++ mu ++ selectorPoint (ySlot >>> 2) (slotLog - 2)
  let ring (pt : List FE) (r : FE × List FE) : BlockClaim := ⟨blk, fun x => ringWeight pt x r.2, r.1⟩
  let consts := (List.range 17).map fun j =>
    let l := 8 + j
    BlockClaim.point blk (rho' ++ selectorPoint l slotLog)
      (FE.ofK (if l = 16 then ⟨(0x80 : UInt64) <<< 56⟩ else 0) * ltSum rho' N)
  ([ring inPt i.ringIn, ring yPt i.ringY] ++ consts).map (.main, ·)

/-- **What phase 5 reads** with the two sumchecks' targets given (`chLinkView p m = chLinkViewT p
(m.chShiftTarget pub) (m.chSc2Target pub)`, `chLinkView_eq`). -/
def chLinkViewT (p : Params) (tA : List FE → FE) (tB : List FE → List FE × FE → List FE → FE) (v : Nat → FE)
    (P : Nat) (r w : List FE) (pub : Pub) : ChLinkIn :=
  let chal := samplesAt v P (p.logN + 3 + 6)
  let shift := scSpec v 3 (chP1 p P) (tA chal) (List.replicate p.logN none)
  let inS := scalarsAt v (chP2 p P + 40) kBits
  let ringIn := ringOf inS (samplesAt v (chP2 p P + 24 * kBits) ringStages)
  let sc2 := scSpec v 3 (chP3 p P) (tB chal shift inS) [none, none]
  let yS := scalarsAt v (chP4 p P + 40) kBits
  let ringY := ringOf yS (samplesAt v (chP4 p P + 24 * kBits) ringStages)
  ⟨chal, shift, inS, ringIn, sc2, yS, ringY, samplesAt v (chP5 p P) laneBits, r, w, pub⟩

theorem chLinkView_eq (p : Params) (m : M3) (v : Nat → FE) (P : Nat) (r w : List FE) (pub : Pub) :
    chLinkView p m v P r w pub = chLinkViewT p (m.chShiftTarget pub) (m.chSc2Target pub) v P r w pub := rfl

/-! ### Templates: the borrow chain and the two recursions with bit cells -/

/-- A `K` cell as an operand. -/
def kS (q : Nat) : Src := .ext ⟨.K, q, []⟩

/-- **The borrow chain** from bit `j` (`k` bits) at row `a`: row `a + 2i` is bit `j + i` of `N − 1`
(`N`'s bit plus the borrow), row `a + 2i + 1` the borrow into bit `j + i + 1` (`cy·b + cy`);
`N`'s bits are the `K` cells `nb + j + i`, `cy` the borrow into bit `j`. -/
def borrowIns (nb : Nat) : Nat → Nat → Nat → Src → List Ins
  | _, _, 0, _ => []
  | a, j, k + 1, cy => [addI (kS (nb + j)) cy, mulI cy (kS (nb + j)) cy] ++ borrowIns nb (a + 2) (j + 1) k (.loc (a + 1))

theorem borrowIns_length (nb : Nat) : ∀ (a j k : Nat) (cy : Src), (borrowIns nb a j k cy).length = 2 * k
  | _, _, 0, _ => rfl
  | a, j, k + 1, cy => by
    simp only [borrowIns, List.length_append, List.length_cons, List.length_nil, borrowIns_length nb (a + 2) (j + 1) k]
    ring

theorem borrow_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) (nb N : Nat)
    (hN : 1 ≤ N) : ∀ (k a j : Nat) (cy : Src), Seg ins a (borrowIns nb a j k cy) → a + 2 * k ≤ ins.length →
    cy.val xv V = carryQ N j → (∀ i < k, xv (kS (nb + j + i)) = bitQ N (j + i)) →
    ∀ i < k, V.getD (a + 2 * i) 0 = bitQ (N - 1) (j + i) ∧ V.getD (a + 2 * i + 1) 0 = carryQ N (j + i + 1)
  | 0, _, _, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, a, j, cy, hseg, hlen, hcy, hb, i, hi => by
    simp only [borrowIns] at hseg
    have s0 := seg_append_left hseg
    have s1 := seg_append_right hseg
    simp only [List.length_cons, List.length_nil] at s1
    have v0 := fix_seg hF s0 (by simp; omega) (i := 0) (by simp) (by simp [addI, linI])
    have v1 := fix_seg hF s0 (by simp; omega) (i := 1) (by simp) (by simp [mulI])
    simp only [List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_mulI, Nat.add_zero] at v0 v1
    have hb0 := hb 0 (by omega)
    simp only [Nat.add_zero] at hb0
    have e0 : V.getD a 0 = bitQ (N - 1) j := by
      rw [v0, show (kS (nb + j)).val xv V = xv (kS (nb + j)) from rfl, hb0, hcy, bitQ_pred N j hN]
    have e1 : V.getD (a + 1) 0 = carryQ N (j + 1) := by
      rw [v1, show (kS (nb + j)).val xv V = xv (kS (nb + j)) from rfl, hb0, hcy, carryQ_succ]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp only [Nat.mul_zero, Nat.add_zero]; exact ⟨e0, e1⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have ih := borrow_val hF nb N hN k (a + 2) (j + 1) (.loc (a + 1)) (by simpa [Nat.add_comm] using s1)
        (by omega) (by rw [val_loc, e1]) (fun i hi => by
          rw [show nb + (j + 1) + i = nb + j + (i + 1) by omega, hb (i + 1) (by omega)]; congr 1; omega)
        i' (by omega)
      rw [show a + 2 * (i' + 1) = a + 2 + 2 * i' by ring, show j + (i' + 1) = j + 1 + i' by ring]
      exact ih

/-- One coordinate of `lt`: rows `m … m + 4` from the tail's `L = lt_{H/2}(y')`, `P = eq(y', H/2)` and the
bit `b = H % 2`: `1 + b + y₀`, `P' = (1 + b + y₀)·P`, `1 + y₀`, `b·P`, `L' = (1 + y₀)·b·P + L`. -/
def ltLevel (zero : Src) (m : Nat) (y0 b L P : Src) : List Ins :=
  [linI 1 1 y0 b, mulI (.loc m) P zero, linI 0 1 y0 y0, mulI b P zero, mulI (.loc (m + 2)) (.loc (m + 3)) L]

/-- `lt`'s source after the coordinates `ys` (`L0` before any). -/
def ltRecL (n : Nat) : List Src → List Src → Src → Src
  | _ :: y, _ :: _, _ => .loc (n + 5 * y.length + 4)
  | _, _, L0 => L0

/-- `eq(y, H)`'s source. -/
def ltRecP (n : Nat) : List Src → List Src → Src → Src
  | _ :: y, _ :: _, _ => .loc (n + 5 * y.length + 1)
  | _, _, P0 => P0

/-- **`(lt_H(y), eq(y, H))`**, the last coordinate first, 5 rows per coordinate, `H`'s bits the cells `bs`. -/
def ltRecIns (zero : Src) (n : Nat) : List Src → List Src → Src → Src → List Ins
  | y0 :: y, b0 :: bs, L0, P0 => ltRecIns zero n y bs L0 P0 ++
      ltLevel zero (n + 5 * y.length) y0 b0 (ltRecL n y bs L0) (ltRecP n y bs P0)
  | _, _, _, _ => []

theorem ltRecIns_length (zero : Src) (n : Nat) : ∀ (ys bs : List Src) (L0 P0 : Src),
    ys.length = bs.length → (ltRecIns zero n ys bs L0 P0).length = 5 * ys.length
  | [], [], _, _, _ => rfl
  | y0 :: y, b0 :: bs, L0, P0, h => by
    simp only [ltRecIns, List.length_append, ltLevel, List.length_cons, List.length_nil]
    rw [ltRecIns_length zero n y bs L0 P0 (by simpa using h)]; ring
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem ltRec_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (ys bs : List Src) (L0 P0 : Src) (H : Nat), ys.length = bs.length →
    H < 2 ^ ys.length → bs.map (Src.val xv V) = (List.range bs.length).map (bitQ H) →
    L0.val xv V = 0 → P0.val xv V = 1 →
    Seg ins n (ltRecIns zero n ys bs L0 P0) → n + 5 * ys.length ≤ ins.length →
    (ltRecL n ys bs L0).val xv V = ltSum (ys.map (Src.val xv V)) H ∧
      (ltRecP n ys bs P0).val xv V = eqW (ys.map (Src.val xv V)) H
  | [], [], L0, P0, H, _, hH, _, hL, hP, _, _ => by
    simp only [List.length_nil, pow_zero] at hH
    have : H = 0 := by omega
    subst this
    simp [ltRecL, ltRecP, hL, hP, ltSum, eqW]
  | y0 :: y, b0 :: bs, L0, P0, H, h, hH, hb, hL, hP, hseg, hlen => by
    have hl : y.length = bs.length := by simpa using h
    have hT := ltRecIns_length zero n y bs L0 P0 hl
    simp only [ltRecIns] at hseg
    simp only [List.map_cons, List.length_cons, List.range_succ_eq_map, List.cons.injEq, List.map_map] at hb
    obtain ⟨hb0, hbs⟩ := hb
    have hbs' : bs.map (Src.val xv V) = (List.range bs.length).map (bitQ (H / 2)) := by
      rw [hbs]; refine List.map_congr_left fun i _ => ?_; simp [Function.comp_def, bitQ_succ]
    have ih := ltRec_val hF hz n y bs L0 P0 (H / 2) hl
      (by simp only [List.length_cons, pow_succ] at hH; omega) hbs' hL hP (seg_append_left hseg)
      (by simp at hlen; omega)
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 5 * y.length with hm
    have hlen' : m + (ltLevel zero m y0 b0 (ltRecL n y bs L0) (ltRecP n y bs P0)).length ≤ ins.length := by
      simp [ltLevel]; simp at hlen; omega
    have v : ∀ i, i < 5 → V.getD (m + i) 0 =
        ((ltLevel zero m y0 b0 (ltRecL n y bs L0) (ltRecP n y bs P0)).getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [ltLevel]; omega) (by
        interval_cases i <;> simp [ltLevel, linI, mulI])
    have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
    have v3 := v 3 (by omega); have v4 := v 4 (by omega)
    simp only [ltLevel, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', Nat.add_zero] at v0 v1 v2 v3 v4
    simp only [val_loc, ih.1, ih.2, hz, add_zero] at v1 v3 v4
    simp only [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at v0 v2
    simp only [ltRecL, ltRecP, List.map_cons, val_loc]
    rw [show n + 5 * y.length + 4 = m + 4 by omega, show n + 5 * y.length + 1 = m + 1 by omega,
      ltSum_cons, eqW_cons_bit, v4, v1, v3, v2, v0, hb0]
    constructor <;> ring

/-- One coordinate of the gated shift kernel: rows `m … m + 13` from the tail's `P = pre`, `E`, `Pt` and
the bit `b`: `preStep x₀ y₀ b` with `E₁ = E + b·Pt` and `Pt' = (b·y₀x₀ + (1 + b)(1 + y₀)(1 + x₀))·Pt`. -/
def preLevelD (zero : Src) (m : Nat) (b x0 y0 P E Pt : Src) : List Ins :=
  [linI 0 1 y0 y0, linI 0 1 x0 x0,
    mulI (.loc m) x0 zero, mulI y0 (.loc (m + 1)) zero, mulI (.loc m) (.loc (m + 1)) zero, mulI y0 x0 zero,
    mulI b Pt E,
    mulI (.loc (m + 3)) P zero, mulI (.loc (m + 2)) (.loc (m + 6)) (.loc (m + 7)),
    mulI (.loc (m + 5)) E zero, mulI (.loc (m + 4)) (.loc (m + 6)) (.loc (m + 9)),
    addI (.loc (m + 5)) (.loc (m + 4)), mulI b (.loc (m + 11)) (.loc (m + 4)), mulI (.loc (m + 12)) Pt zero]

/-- The sources of `(pre, E, Pt)` after the coordinates (`base` before any). -/
def preRecDOut (n : Nat) : List Src → List Src → Src × Src × Src → Src × Src × Src
  | _ :: x, _ :: _, _ => (.loc (n + 14 * x.length + 8), .loc (n + 14 * x.length + 10), .loc (n + 14 * x.length + 13))
  | _, _, base => base

/-- **`preCF xs ys H` with `H`'s bits the cells `bs`**, the last coordinate first, 14 rows per coordinate. -/
def preRecDIns (zero : Src) (n : Nat) : List Src → List Src → List Src → Src × Src × Src → List Ins
  | x0 :: x, y0 :: y, b0 :: bs, base => preRecDIns zero n x y bs base ++
      preLevelD zero (n + 14 * x.length) b0 x0 y0 (preRecDOut n x bs base).1 (preRecDOut n x bs base).2.1
        (preRecDOut n x bs base).2.2
  | _, _, _, _ => []

theorem preRecDIns_length (zero : Src) (n : Nat) : ∀ (xs ys bs : List Src) (base : Src × Src × Src),
    xs.length = ys.length → xs.length = bs.length → (preRecDIns zero n xs ys bs base).length = 14 * xs.length
  | [], _, _, _, _, _ => by simp [preRecDIns]
  | x0 :: x, y0 :: y, b0 :: bs, base, h, h' => by
    simp only [preRecDIns, List.length_append, preLevelD, List.length_cons, List.length_nil]
    rw [preRecDIns_length zero n x y bs base (by simpa using h) (by simpa using h')]; ring
  | _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h => by simp at h

theorem preRecDOut_cons (n : Nat) (x0 b0 : Src) (x bs : List Src) (base : Src × Src × Src) :
    preRecDOut n (x0 :: x) (b0 :: bs) base =
      (.loc (n + 14 * x.length + 8), .loc (n + 14 * x.length + 10), .loc (n + 14 * x.length + 13)) := rfl

theorem preRecD_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (xs ys bs : List Src) (H : Nat) (base : Src × Src × Src),
    xs.length = ys.length → xs.length = bs.length → H < 2 ^ xs.length →
    bs.map (Src.val xv V) = (List.range bs.length).map (bitQ H) →
    base.1.val xv V = 0 → base.2.1.val xv V = 0 → base.2.2.val xv V = 1 →
    Seg ins n (preRecDIns zero n xs ys bs base) → n + 14 * xs.length ≤ ins.length →
    ((preRecDOut n xs bs base).1.val xv V, (preRecDOut n xs bs base).2.1.val xv V,
      (preRecDOut n xs bs base).2.2.val xv V) = preCF (xs.map (Src.val xv V)) (ys.map (Src.val xv V)) H
  | [], [], [], H, base, _, _, hH, _, h1, h2, h3, _, _ => by
    simp only [List.length_nil, pow_zero] at hH
    have : H = 0 := by omega
    subst this
    simp [preRecDOut, preCF, h1, h2, h3]
  | x0 :: x, y0 :: y, b0 :: bs, H, base, h, h', hH, hb, h1, h2, h3, hseg, hlen => by
    have hl : x.length = y.length := by simpa using h
    have hl' : x.length = bs.length := by simpa using h'
    have hT := preRecDIns_length zero n x y bs base hl hl'
    simp only [preRecDIns] at hseg
    simp only [List.map_cons, List.length_cons, List.range_succ_eq_map, List.cons.injEq, List.map_map] at hb
    obtain ⟨hb0, hbs⟩ := hb
    have hbs' : bs.map (Src.val xv V) = (List.range bs.length).map (bitQ (H / 2)) := by
      rw [hbs]; refine List.map_congr_left fun i _ => ?_; simp [Function.comp_def, bitQ_succ]
    have ih := preRecD_val hF hz n x y bs (H / 2) base hl hl'
      (by simp only [List.length_cons, pow_succ] at hH; omega) hbs' h1 h2 h3 (seg_append_left hseg)
      (by simp at hlen; omega)
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 14 * x.length with hm
    set L := preLevelD zero m b0 x0 y0 (preRecDOut n x bs base).1 (preRecDOut n x bs base).2.1
        (preRecDOut n x bs base).2.2 with hL
    have hlen' : m + L.length ≤ ins.length := by
      simp [hL, preLevelD]; simp at hlen; omega
    have v : ∀ i, i < 14 → V.getD (m + i) 0 = (L.getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [hL, preLevelD]; omega) (by
        interval_cases i <;> simp [hL, preLevelD, linI, mulI, addI])
    have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
    have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
    have v6 := v 6 (by omega); have v7 := v 7 (by omega); have v8 := v 8 (by omega)
    have v9 := v 9 (by omega); have v10 := v 10 (by omega); have v11 := v 11 (by omega)
    have v12 := v 12 (by omega); have v13 := v 13 (by omega)
    simp only [hL, preLevelD, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', eval_addI,
      Nat.add_zero, val_loc, hz, add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at v0 v1
    have hpre : preCF ((x0 :: x).map (Src.val xv V)) ((y0 :: y).map (Src.val xv V)) H =
        preStep (x0.val xv V) (y0.val xv V) (H % 2 = 1)
          (preCF (x.map (Src.val xv V)) (y.map (Src.val xv V)) (H / 2)) := rfl
    have i1 := congrArg Prod.fst ih
    have i2 := congrArg (fun t => t.2.1) ih
    have i3 := congrArg (fun t => t.2.2) ih
    simp only at i1 i2 i3
    rw [hpre, preRecDOut_cons]
    simp only [val_loc]
    rw [show n + 14 * x.length + 8 = m + 8 by omega, show n + 14 * x.length + 10 = m + 10 by omega,
      show n + 14 * x.length + 13 = m + 13 by omega]
    simp only [Function.comp_apply, bitQ_zero] at hb0
    unfold preStep
    rw [v8, v10, v13, v12, v11, v7, v9, v6, v2, v3, v4, v5, v0, v1, hb0, i1, i2, i3]
    rcases Nat.mod_two_eq_zero_or_one H with hh | hh
    · simp only [hh, show decide ((0 : Nat) = 1) = false from rfl, if_neg (show ¬ ((0 : Nat) = 1) by decide),
        Bool.false_eq_true, if_false, zero_mul, zero_add]
      simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
    · simp only [hh, show decide ((1 : Nat) = 1) = true from rfl, show decide True = true from rfl, if_pos rfl, if_true, one_mul]
      simp only [Prod.mk.injEq]
      refine ⟨by ring, by ring, ?_⟩
      linear_combination ((1 + y0.val xv V) * (1 + x0.val xv V)) *
        (preCF (x.map (Src.val xv V)) (y.map (Src.val xv V)) (H / 2)).2.2 * fe_two_q
  | [], _ :: _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _, _, _, _, _, _, _ => by simp at h
  | [], [], _ :: _, _, _, _, h, _, _, _, _, _, _, _ => by simp at h

/-! ### The gated blocks -/

theorem ltRecL_len (a : Nat) (ys bs : List Src) (L0 : Src) (h : ys.length = bs.length) (h1 : 1 ≤ ys.length) :
    ltRecL a ys bs L0 = .loc (a + 5 * ys.length - 1) := by
  match ys, bs, h with
  | _ :: y, _ :: _, _ => simp only [ltRecL, List.length_cons]; congr 1
  | [], _, _ => simp at h1

theorem ltRecP_len (a : Nat) (ys bs : List Src) (P0 : Src) (h : ys.length = bs.length) (h1 : 1 ≤ ys.length) :
    ltRecP a ys bs P0 = .loc (a + 5 * ys.length - 4) := by
  match ys, bs, h with
  | _ :: y, _ :: _, _ => simp only [ltRecP, List.length_cons]; congr 1
  | [], _, _ => simp at h1

theorem preRecDOut_len (a : Nat) (xs bs : List Src) (base : Src × Src × Src) (h : xs.length = bs.length)
    (h1 : 1 ≤ xs.length) :
    preRecDOut a xs bs base = (.loc (a + 14 * xs.length - 6), .loc (a + 14 * xs.length - 4),
      .loc (a + 14 * xs.length - 1)) := by
  match xs, bs, h with
  | _ :: x, _ :: _, _ =>
    simp only [preRecDOut, List.length_cons, Prod.mk.injEq, Src.loc.injEq]; omega
  | [], _, _ => simp at h1

/-- `m`'s bit sources in block A (the borrow chain's rows `n + 164 + 2i`). -/
def mBitS (n : Nat) : List Src := (List.range n).map fun i => .loc (n + 164 + 2 * i)

/-- **Block A, gated** (S1): as v1's `chGlueA` up to `Pad43`'s bits (`n + 163`), then the borrow chain on
`N`'s bits at the `K` cells `nb + i` (`n + 164`, `2n` rows), `(lt_m(ρ), eq(ρ, m))` (`3n + 164`, `5n` rows;
`lt` at `8n + 163`), the claim `C·lt_m(ρ)` (`8n + 164`). -/
def chGlueAG (n Q nb : Nat) : List Ins :=
  loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (borrowIns nb (n + 164) 0 n (.loc (n + 10)) ++
    (ltRecIns (.loc (n + 9)) (3 * n + 164) (rhoS n) (mBitS n) (.loc (n + 9)) (.loc (n + 10)) ++
    [mulI (.loc (n + 163)) (.loc (8 * n + 163)) (.loc (n + 9))]))))))

theorem chGlueAG_length (n Q nb : Nat) : (chGlueAG n Q nb).length = 8 * n + 165 := by
  have lR : (ltRecIns (.loc (n + 9)) (3 * n + 164) (rhoS n) (mBitS n) (.loc (n + 9)) (.loc (n + 10))).length =
      5 * n := by rw [ltRecIns_length _ _ _ _ _ _ (by simp [rhoS, mBitS])]; simp [rhoS]
  simp only [chGlueAG, List.length_append, loadsAt, List.length_map, List.length_range,
    eqTab3_length _ _ _ _ (rfl : (lamS n).length = 3),
    eqTab6_length _ _ _ _ (by simp [zetaS] : (zetaS n).length = 6), padRows, borrowIns_length, lR,
    List.length_cons, List.length_nil]
  omega

/-- Block A's (gated) values, on any fixed point of its rows over a streamed memory, `N`'s bits at the `K`
cells `nb + i`, `1 ≤ N ≤ 2^n`. -/
theorem chGlueAG_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n Q nb N : Nat} {V : List FE} (hF : Fix (iterXv M o jf) (chGlueAG n Q nb) V) (hn : 1 ≤ n)
    (hT : Q + 9 * (n + 9) + 2 < T + 9) (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ n)
    (hbits : ∀ i < n, iterXv M o jf (kS (nb + i)) = bitQ N i) :
    (∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i))) ∧
    V.getD (n + 9) 0 = 0 ∧ V.getD (n + 10) 0 = 1 ∧
    (∀ k < 8, (eLs n k).val (iterXv M o jf) V =
      eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k) ∧
    (∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k) ∧
    (∀ i < n, V.getD (n + 164 + 2 * i) 0 = bitQ (N - 1) i) ∧
    V.getD (8 * n + 164) 0 =
      (eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 0 *
        (eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 0 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 1 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 6) +
        eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 4 *
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 8) *
      ltSum ((List.range n).map fun i => V.getD i 0) (N - 1) := by
  have hlen := chGlueAG_length n Q nb
  have hs : Seg (chGlueAG n Q nb) 0 (loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (borrowIns nb (n + 164) 0 n (.loc (n + 10)) ++
    (ltRecIns (.loc (n + 9)) (3 * n + 164) (rhoS n) (mBitS n) (.loc (n + 9)) (.loc (n + 10)) ++
    [mulI (.loc (n + 163)) (.loc (8 * n + 163)) (.loc (n + 9))]))))))) :=
    seg_whole _
  have lL : (loadsAt Q 9 (n + 9)).length = n + 9 := by simp [loadsAt]
  have lEL : (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n)).length = 17 := eqTab3_length _ _ _ _ rfl
  have lEZ : (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n)).length = 132 :=
    eqTab6_length _ _ _ _ (by simp [zetaS])
  have hlb : (rhoS n).length = (mBitS n).length := by simp [rhoS, mBitS]
  have lB : (borrowIns nb (n + 164) 0 n (.loc (n + 10))).length = 2 * n := borrowIns_length _ _ _ _ _
  have lR : (ltRecIns (.loc (n + 9)) (3 * n + 164) (rhoS n) (mBitS n) (.loc (n + 9)) (.loc (n + 10))).length =
      5 * n := by rw [ltRecIns_length _ _ _ _ _ _ hlb]; simp [rhoS]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEL, s3⟩ := seg_split s2
  obtain ⟨sEZ, s4⟩ := seg_split s3
  obtain ⟨sP, s5⟩ := seg_split s4
  obtain ⟨sB, s6⟩ := seg_split s5
  obtain ⟨sR, sF⟩ := seg_split s6
  replace sZ := seg_at (m := n + 9) sZ (by simp [lL])
  replace sEL := seg_at (m := n + 11) sEL (by simp [lL] <;> omega)
  replace sEZ := seg_at (m := n + 28) sEZ (by simp [lL, lEL] <;> omega)
  replace sP := seg_at (m := n + 160) sP (by simp [lL, lEL, lEZ] <;> omega)
  replace sB := seg_at (m := n + 164) sB (by simp [lL, lEL, lEZ, padRows] <;> omega)
  replace sR := seg_at (m := 3 * n + 164) sR (by simp [lL, lEL, lEZ, lB, padRows] <;> omega)
  replace sF := seg_at (m := 8 * n + 164) sF (by simp [lL, lEL, lEZ, lB, lR, padRows] <;> omega)
  -- loads
  have hL : ∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hi
    rwa [Nat.zero_add] at this
  -- zero and one
  have hz : V.getD (n + 9) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 10) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [linI])
    rw [show n + 9 + 1 = n + 10 by omega] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 9)).val (iterXv M o jf) V = 0 := hz
  -- eq tables
  have hEL := eqTab_val hF hzs (lamS n) (n + 11) [.loc (n + 10)] sEL
    (by rw [eqTab3_length _ _ _ _ rfl, hlen]; omega)
  have hEZ := eqTab_val hF hzs (zetaS n) (n + 28) [.loc (n + 10)] sEZ
    (by rw [eqTab6_length _ _ _ _ (by simp [zetaS]), hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1] at hEL hEZ
  have hlam : (lamS n).map (Src.val (iterXv M o jf) V) = [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] := by
    simp [lamS]
  have hzeta : (zetaS n).map (Src.val (iterXv M o jf) V) = (List.range 6).map fun i => V.getD (n + 3 + i) 0 := by
    simp [zetaS]
  rw [hlam] at hEL
  rw [hzeta] at hEZ
  have eL : ∀ k < 8, (eLs n k).val (iterXv M o jf) V = eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).length := by
      have := congrArg List.length hEL
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eLs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEL, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  have eZ : ∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).length := by
      have := congrArg List.length hEZ
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eZs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEZ, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  -- Pad43's bits
  have p0 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 0) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p1 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 1) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p2 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 2) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p3 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 3) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  simp only [padRows, List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_mulI, val_loc, hz, add_zero,
    Nat.add_zero] at p0 p1 p2 p3
  rw [show n + 160 + 1 = n + 161 by omega] at p1
  rw [show n + 160 + 2 = n + 162 by omega, p1, p0] at p2
  rw [show n + 160 + 3 = n + 163 by omega, p2] at p3
  rw [eL 0 (by omega), eL 4 (by omega), eZ 0 (by omega), eZ 1 (by omega), eZ 6 (by omega),
    eZ 8 (by omega)] at p3
  -- the borrow chain
  have hBr := borrow_val hF nb N hN1 n (n + 164) 0 (.loc (n + 10)) sB (by rw [hlen]; omega)
    (by rw [val_loc, h1, carryQ_zero]) (fun i hi => by rw [Nat.add_zero, Nat.zero_add]; exact hbits i hi)
  have hmb : ∀ i < n, V.getD (n + 164 + 2 * i) 0 = bitQ (N - 1) i := fun i hi => by
    rw [(hBr i hi).1, Nat.zero_add]
  -- lt_m(ρ)
  have hbm : (mBitS n).map (Src.val (iterXv M o jf) V) = (List.range (mBitS n).length).map (bitQ (N - 1)) := by
    simp only [mBitS, List.map_map, List.length_map, List.length_range]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, val_loc]
    exact hmb i (List.mem_range.mp hi)
  have hR := ltRec_val hF hzs (3 * n + 164) (rhoS n) (mBitS n) (.loc (n + 9)) (.loc (n + 10)) (N - 1) hlb
    (by simp only [rhoS, List.length_map, List.length_range]; omega) hbm hz h1 sR (by rw [hlen]; simp [rhoS]; omega)
  rw [ltRecL_len _ _ _ _ hlb (by simp [rhoS]; omega)] at hR
  have hrho : (rhoS n).map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => V.getD i 0 := by
    simp [rhoS]
  rw [hrho, val_loc, show 3 * n + 164 + 5 * (rhoS n).length - 1 = 8 * n + 163 by simp [rhoS]; omega] at hR
  -- the claim
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, eval_mulI, val_loc, Nat.add_zero, hz, add_zero] at f0
  refine ⟨hL, hz, h1, eL, eZ, hmb, ?_⟩
  rw [f0, hR.1, p3]; ring

/-- **Block B, gated**: the 64 `in` slices (`QB + 3k`), zero (64), one (65), `Σ_k eq(ζ,k)·inS_k` (66, at 129),
`(S̃_m, Ẽ'_m, ·)(ρ, ρ')` with `m`'s bits the cells `mb` (130, `14n` rows; `S̃` at `14n + 124`, `Ẽ'` at
`14n + 126`), the claim `S̃·dot + f₁` (`14n + 130`). -/
def chGlueBG (QB : Nat) (rho rho' eZ mb : List Cell) (f1 : Cell) : List Ins :=
  loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (preRecDIns (.loc 64) 130 (rho'.map cellSrc) (rho.map cellSrc) (mb.map cellSrc) (.loc 64, .loc 64, .loc 65) ++
    [mulI (.loc (14 * rho.length + 124)) (.loc 129) (cellSrc f1)])))

theorem chGlueBG_length (QB : Nat) (rho rho' eZ mb : List Cell) (f1 : Cell) (hl : rho.length = rho'.length)
    (hlm : rho.length = mb.length) : (chGlueBG QB rho rho' eZ mb f1).length = 14 * rho.length + 131 := by
  simp only [chGlueBG, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
    List.length_cons, List.length_nil]
  rw [preRecDIns_length _ _ _ _ _ _ (by simp [hl]) (by simp; omega)]; simp; omega

theorem chGlueBG_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QB : Nat} {rho rho' eZ mb : List Cell} {f1 : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueBG QB rho rho' eZ mb f1) V) (hn : 1 ≤ rho.length)
    (hl : rho.length = rho'.length) (hlm : rho.length = mb.length) (hT : QB + 3 * 64 + 2 < T + 3) {m : Nat}
    (hm : m < 2 ^ rho.length) (hmb : mb.map (Cell.val M) = (List.range mb.length).map (bitQ m)) :
    (∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k))) ∧
    V.getD (14 * rho.length + 126) 0 = eSum (rho'.map (Cell.val M)) (rho.map (Cell.val M)) m ∧
    V.getD (14 * rho.length + 130) 0 = preSum (rho'.map (Cell.val M)) (rho.map (Cell.val M)) m *
      (∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k))) + f1.val M := by
  have hs : Seg (chGlueBG QB rho rho' eZ mb f1) 0 (loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (preRecDIns (.loc 64) 130 (rho'.map cellSrc) (rho.map cellSrc) (mb.map cellSrc) (.loc 64, .loc 64, .loc 65) ++
    [mulI (.loc (14 * rho.length + 124)) (.loc 129) (cellSrc f1)])))) := seg_whole _
  have lS := preRecDIns_length (.loc 64) 130 (rho'.map cellSrc) (rho.map cellSrc) (mb.map cellSrc)
    (.loc 64, .loc 64, .loc 65) (by simp [hl]) (by simp; omega)
  have hlen := chGlueBG_length QB rho rho' eZ mb f1 hl hlm
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sD, s3⟩ := seg_split s2
  obtain ⟨sR, sF⟩ := seg_split s3
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sD := seg_at (m := 66) sD (by simp [loadsAt])
  replace sR := seg_at (m := 130) sR (by simp [loadsAt, dotIns_length])
  replace sF := seg_at (m := 14 * rho.length + 130) sF (by simp [loadsAt, dotIns_length, lS]; omega)
  have hL : ∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k)) := by
    intro k hk
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hk
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hD := dot_val hF ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) 66 (.loc 64) sD
    (by rw [hlen]; simp <;> omega)
  have hDs : dotSrc 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) = .loc 129 := by
    simp [dotSrc]
  rw [hDs, val_loc, val_loc, hz, zero_add] at hD
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  have hR := preRecD_val hF (zero := .loc 64) hz 130 (rho'.map cellSrc) (rho.map cellSrc) (mb.map cellSrc) m
    (.loc 64, .loc 64, .loc 65) (by simp [hl]) (by simp; omega) (by simp only [List.length_map]; rw [← hl]; exact hm)
    (by rw [hmap, hmb]; simp) hz hz h1 sR (by rw [hlen]; simp; omega)
  rw [preRecDOut_len _ _ _ _ (by simp; omega) (by simp; omega), hmap, hmap,
    preCF_eq _ _ _ (by simp [hl])] at hR
  simp only [val_loc, List.length_map, Prod.mk.injEq] at hR
  obtain ⟨hpre, hE, -⟩ := hR
  rw [show 130 + 14 * rho'.length - 6 = 14 * rho.length + 124 by omega] at hpre
  rw [show 130 + 14 * rho'.length - 4 = 14 * rho.length + 126 by omega] at hE
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, eval_mulI, val_loc, Nat.add_zero] at f0
  have hsum : (List.map (fun ab => ab.1.val (iterXv M o jf) V * ab.2.val (iterXv M o jf) V)
      (List.map (fun k => (cellSrc (eZ.getD k default), Src.loc k)) (List.range 64))).sum =
      ∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k)) := by
    rw [List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    show iterXv M o jf (cellSrc (eZ.getD k default)) * V.getD k 0 = _
    rw [iterXv_cell, hL k hk']
  refine ⟨hL, hE, ?_⟩
  rw [f0, hpre, hD, hsum]
  show _ + iterXv M o jf (cellSrc f1) = _
  rw [iterXv_cell]

/-- **Block C, gated**: v1's `chGlueC` with `Ẽ'_m(ρ, ρ')` a cell (`eS`, block B's) instead of
`eqMasked = Πρ·Πρ' + eqEval`: the target (148), `f₂ + target` (149), the gated assertion (150). -/
def chGlueCG (QC : Nat) (mu eL eZ : List Cell) (eS f2 gate : Cell) : List Ins :=
  loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    [mulI (cellSrc eS) (.loc 147) (.loc 64), addI (cellSrc f2) (.loc 148),
      ⟨.assert0, .K, [.loc 149, cellSrc gate]⟩])))))))

theorem chGlueCG_length (QC : Nat) (mu eL eZ : List Cell) (eS f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueCG QC mu eL eZ eS f2 gate).length = 151 := by
  simp only [chGlueCG, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
    eqTab2_length _ _ _ _ (by simpa using hm : (mu.map cellSrc).length = 2),
    List.length_cons, List.length_nil]

/-- **Block C's assertion, gated**: with gate `1`, `f₂ = Ẽ'·(α S₁ + β S₂)`. -/
theorem chGlueCG_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QC : Nat} {mu eL eZ : List Cell} {eS f2 gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueCG QC mu eL eZ eS f2 gate) V) (hm : mu.length = 2)
    (hT : QC + 3 * 64 + 2 < T + 3)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD 149 0 = 0) (hg : gate.val M = 1) :
    f2.val M = eS.val M *
      ((∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M) *
          (∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q))) +
        (∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M) *
          (∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))))) := by
  have hlen := chGlueCG_length QC mu eL eZ eS f2 gate hm
  have hs : Seg (chGlueCG QC mu eL eZ eS f2 gate) 0
    (loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    [mulI (cellSrc eS) (.loc 147) (.loc 64), addI (cellSrc f2) (.loc 148),
      ⟨.assert0, .K, [.loc 149, cellSrc gate]⟩])))))))) := seg_whole _
  have lEM : (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc)).length = 8 := eqTab2_length _ _ _ _ (by simpa using hm)
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEM, s3⟩ := seg_split s2
  obtain ⟨sDA, s4⟩ := seg_split s3
  obtain ⟨sDB, s5⟩ := seg_split s4
  obtain ⟨sD1, s6⟩ := seg_split s5
  obtain ⟨sD2, s7⟩ := seg_split s6
  obtain ⟨sMM, sF⟩ := seg_split s7
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sEM := seg_at (m := 66) sEM (by simp [loadsAt])
  replace sDA := seg_at (m := 74) sDA (by simp [loadsAt, lEM])
  replace sDB := seg_at (m := 78) sDB (by simp [loadsAt, lEM, dotIns_length])
  replace sD1 := seg_at (m := 82) sD1 (by simp [loadsAt, lEM, dotIns_length])
  replace sD2 := seg_at (m := 138) sD2 (by simp [loadsAt, lEM, dotIns_length])
  replace sMM := seg_at (m := 146) sMM (by simp [loadsAt, lEM, dotIns_length])
  replace sF := seg_at (m := 148) sF (by simp [loadsAt, lEM, dotIns_length])
  have hL : ∀ q < 64, V.getD q 0 = feAt sig (8 * (QC + 3 * q)) := by
    intro q hq
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hq
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc 64).val (iterXv M o jf) V = 0 := hz
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  have hEM := eqTab_val hF hzs (mu.map cellSrc) 66 [.loc 65] sEM (by rw [lEM, hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1, hmap] at hEM
  have eMu : ∀ m < 4, (eMus mu m).val (iterXv M o jf) V = eqW (mu.map (Cell.val M)) m := by
    intro m hm4
    have hlo : m < (eqTabOut 66 [.loc 65] (mu.map cellSrc)).length := by
      have := congrArg List.length hEM
      rw [List.length_map, foldl_eqStep_length] at this; simp [hm] at this; omega
    rw [eMus, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlo, hEM, ← eqKernel_foldl,
      eqKernel_getD _ (by simp [hm]; omega)]
  have hDA := dot_val hF _ 74 (.loc 64) sDA (by rw [hlen]; simp)
  have hDB := dot_val hF _ 78 (.loc 64) sDB (by rw [hlen]; simp)
  have hD1 := dot_val hF _ 82 (.loc 64) sD1 (by rw [hlen]; simp)
  have hD2 := dot_val hF _ 138 (.loc 64) sD2 (by rw [hlen]; simp)
  simp only [dotSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range,
    OfNat.ofNat_ne_zero, if_false, val_loc, hz, zero_add, List.map_map] at hDA hDB hD1 hD2
  rw [list_sum_range] at hDA hDB hD1 hD2
  simp only [Function.comp_def, hcell, val_loc] at hDA hDB hD1 hD2
  have hA4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD x default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have hB4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD (x + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have h56 : ∑ x ∈ Finset.range 56, (eZ.getD (x + 8) default).val M * V.getD x 0 =
      ∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q)) :=
    Finset.sum_congr rfl fun q hq => by rw [hL q (by have := Finset.mem_range.mp hq; omega)]
  have h8 : ∑ x ∈ Finset.range 8, (eZ.getD x default).val M * V.getD (x + 56) 0 =
      ∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))) :=
    Finset.sum_congr rfl fun q hq => by rw [hL (q + 56) (by have := Finset.mem_range.mp hq; omega)]
  rw [hA4] at hDA
  rw [hB4] at hDB
  rw [h56] at hD1
  rw [h8] at hD2
  have m0 := fix_seg hF sMM (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  have m1 := fix_seg hF sMM (by rw [hlen]; simp) (i := 1) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, val_loc, hz, add_zero, Nat.add_zero] at m0 m1
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp) (i := 1) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_addI, val_loc, hz, add_zero,
    Nat.add_zero, hcell] at f0 f1
  rw [hcell, hg, one_mul, f1, f0, m1, m0, hDA, hDB, hD1, hD2] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination hA

/-! ### `lt_N(ρ')` for the constant lanes' claims -/

/-- The constant lane `0x80 << 56` (lane 16 of `Pad43`). -/
def c80K : FK := ⟨(0x80 : UInt64) <<< 56⟩

/-- **`c₁₆·lt_N(ρ')`** from `N`'s bits at the `K` cells `nb + i`: zero (0), one (1), the borrow chain
(2, `2n` rows), `(lt_m(ρ'), eq(ρ', m))` (`2n + 2`, `5n` rows), `lt_N = lt_m + eq(ρ', m)` (`7n + 2`),
`c₁₆` (`7n + 3`), the product (`7n + 4`). -/
def ltNIns (nb : Nat) (rho' : List Cell) : List Ins :=
  [linI 1 0 (kS nb) (kS nb), linI 1 1 (.loc 0) (.loc 0)] ++
    (borrowIns nb 2 0 rho'.length (.loc 1) ++
    (ltRecIns (.loc 0) (2 * rho'.length + 2) (rho'.map cellSrc)
        ((List.range rho'.length).map fun i => .loc (2 + 2 * i)) (.loc 0) (.loc 1) ++
    [addI (.loc (7 * rho'.length + 1)) (.loc (7 * rho'.length - 2)), linI 0 c80K (.loc 0) (.loc 0),
      mulI (.loc (7 * rho'.length + 3)) (.loc (7 * rho'.length + 2)) (.loc 0)]))

theorem ltNIns_length (nb : Nat) (rho' : List Cell) : (ltNIns nb rho').length = 7 * rho'.length + 5 := by
  simp only [ltNIns, List.length_append, List.length_cons, List.length_nil, borrowIns_length]
  rw [ltRecIns_length _ _ _ _ _ _ (by simp)]; simp; omega

theorem ltNIns_val {M : Mem} {o : LoopOut} {jf : Nat} {nb N : Nat} {rho' : List Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (ltNIns nb rho') V) (hn : 1 ≤ rho'.length) (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ rho'.length)
    (hbits : ∀ i < rho'.length, iterXv M o jf (kS (nb + i)) = bitQ N i) :
    V.getD (7 * rho'.length + 4) 0 = FE.ofK c80K * ltSum (rho'.map (Cell.val M)) N := by
  set n := rho'.length with hndef
  have hlen := ltNIns_length nb rho'
  have hs : Seg (ltNIns nb rho') 0 ([linI 1 0 (kS nb) (kS nb), linI 1 1 (.loc 0) (.loc 0)] ++
    (borrowIns nb 2 0 n (.loc 1) ++
    (ltRecIns (.loc 0) (2 * n + 2) (rho'.map cellSrc) ((List.range n).map fun i => .loc (2 + 2 * i)) (.loc 0) (.loc 1) ++
    [addI (.loc (7 * n + 1)) (.loc (7 * n - 2)), linI 0 c80K (.loc 0) (.loc 0),
      mulI (.loc (7 * n + 3)) (.loc (7 * n + 2)) (.loc 0)]))) := seg_whole _
  have hlb : (rho'.map cellSrc).length = ((List.range n).map fun i => Src.loc (2 + 2 * i)).length := by simp [hndef]
  have lB : (borrowIns nb 2 0 n (.loc 1)).length = 2 * n := borrowIns_length _ _ _ _ _
  have lR : (ltRecIns (.loc 0) (2 * n + 2) (rho'.map cellSrc) ((List.range n).map fun i => .loc (2 + 2 * i))
      (.loc 0) (.loc 1)).length = 5 * n := by rw [ltRecIns_length _ _ _ _ _ _ hlb]; simp [hndef]
  obtain ⟨sZ, s1⟩ := seg_split hs
  obtain ⟨sB, s2⟩ := seg_split s1
  obtain ⟨sR, sF⟩ := seg_split s2
  replace sB := seg_at (m := 2) sB (by simp)
  replace sR := seg_at (m := 2 * n + 2) sR (by simp [lB]; omega)
  replace sF := seg_at (m := 7 * n + 2) sF (by simp [lB, lR]; omega)
  have z0 := fix_seg hF sZ (by rw [hlen]; simp) (i := 0) (by simp) (by simp [linI])
  have z1 := fix_seg hF sZ (by rw [hlen]; simp) (i := 1) (by simp) (by simp [linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', Nat.zero_add, val_loc] at z0 z1
  have hz : V.getD 0 0 = 0 := by
    rw [z0, show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 1 0 = 1 := by
    rw [z1, hz, show FE.ofK 1 = 1 from rfl, one_mul, add_zero, zero_add]
  have hzs : (Src.loc 0).val (iterXv M o jf) V = 0 := hz
  have hBr := borrow_val hF nb N hN1 n 2 0 (.loc 1) sB (by rw [hlen]; omega)
    (by rw [val_loc, h1, carryQ_zero]) (fun i hi => by rw [Nat.add_zero, Nat.zero_add]; exact hbits i hi)
  have hbm : ((List.range n).map fun i => Src.loc (2 + 2 * i)).map (Src.val (iterXv M o jf) V) =
      (List.range ((List.range n).map fun i => Src.loc (2 + 2 * i)).length).map (bitQ (N - 1)) := by
    simp only [List.map_map, List.length_map, List.length_range]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, val_loc]
    rw [(hBr i (List.mem_range.mp hi)).1, Nat.zero_add]
  have hR := ltRec_val hF hzs (2 * n + 2) (rho'.map cellSrc) ((List.range n).map fun i => .loc (2 + 2 * i))
    (.loc 0) (.loc 1) (N - 1) hlb (by simp only [List.length_map, ← hndef]; omega) hbm hz h1 sR
    (by rw [hlen]; simp only [List.length_map, ← hndef]; omega)
  rw [ltRecL_len _ _ _ _ hlb (by simp; omega), ltRecP_len _ _ _ _ hlb (by simp; omega)] at hR
  have hmap : (rho'.map cellSrc).map (Src.val (iterXv M o jf) V) = rho'.map (Cell.val M) := by
    simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  simp only [hmap, val_loc, List.length_map, ← hndef] at hR
  rw [show 2 * n + 2 + 5 * n - 1 = 7 * n + 1 by omega, show 2 * n + 2 + 5 * n - 4 = 7 * n - 2 by omega] at hR
  have f0 := fix_seg hF sF (by rw [hlen]; simp; omega) (i := 0) (by simp) (by simp [addI, linI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp; omega) (i := 1) (by simp) (by simp [linI])
  have f2 := fix_seg hF sF (by rw [hlen]; simp; omega) (i := 2) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_linI', eval_mulI, val_loc, Nat.add_zero,
    hz] at f0 f1 f2
  rw [show 7 * n + 2 + 1 = 7 * n + 3 by omega] at f1
  rw [show 7 * n + 2 + 2 = 7 * n + 4 by omega, f1, f0, hR.1, hR.2] at f2
  rw [f2]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp only [ltSum, Finset.sum_range_succ]
  ring

end Lvm.Q1
