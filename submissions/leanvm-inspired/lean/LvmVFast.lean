-- New for lvm (V-PERF): the shipped `V_S` with its header-independent tables built once.
import LvmSubmissionS
import LvmVFastQ

/-!
# A fast `V_S` at `P20`, equal to `VS20`

`VS20 = VSL P20 M3.tabsP20` builds the node program's tables `M3.tabsP20 pub` five times per check
(`M3.real`'s fields), and every build recomputes Q_link's static table `qltData` (≈ 4.5 s); the
closed forms of the 12 position `BITS` classes call `posCell`/`ansLane` per cell, which walk the
schedule each time (≈ 67 s per sweep). Here:

* `posCellF`: `posCell` with its schedule-derived bases passed in (`posCellF_eq`);
* `tabA S W O`: a `BITS` table whose address columns read cached powers (`W` for the word's cell,
  `O[j]` for output `j`'s), equal to `S.tab` when the caches hold `x^cell` on the real rows
  (`tabA_eq`: `S.row x < max S.n 1`, so the columns are the same functions);
* `Pre`: the header-independent parts of `QAsm.tabs C G D pub` (groups, the input arrays but `PUB`,
  the aux tables with cached position classes); `tabsPre (pre C G D) C D pub = QAsm.tabs C G D pub`
  (`tabsPre_eq`);
* `pre20` (a top-level constant: compiled Lean evaluates it once, at initialisation), `tabs20F`,
  **`VS20F`** and **`VS20F_eq : VS20F = VS20`**; `T.submissionF` (`V := VS20F`) equals
  `T.submission` (`submissionF_eq`), so the certificate transfers by rewriting.
-/

set_option autoImplicit false

namespace Lvm.VF

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.SigBits Lvm.QAsm

/-! ## Cached `BITS` tables -/

/-- An address column read from a cache `A` of powers (row `x` uses `A[S.row x]`). -/
def adrColA (S : BSpec) (A : Array FK) : ColSrc :=
  .fix (fun x => A.getD (S.row x) 0) fun r => mleF r fun x => FE.ofK (A.getD (S.row x) 0)

/-- Column `c` of the cached table (`BSpec.col` with the caches). -/
def colA (S : BSpec) (W : Array FK) (O : Array (Array FK)) (c : Nat) : ColSrc :=
  if c = 66 then adrColA S W
  else if 68 ≤ c ∧ c % 2 = 0 then adrColA S (O.getD ((c - 68) / 2) #[])
  else .com (S.pl c).1 (S.pl c).2

/-- **The cached `BITS` table** (`BSpec.tab` with `colA`). -/
def tabA (S : BSpec) (W : Array FK) (O : Array (Array FK)) : Tab where
  τ := S.τ
  cols := (List.range S.width).map (colA S W O)
  cons := cons
  reads := S.reads
  seeds := []
  deg := S.tab.deg

theorem row_lt (S : BSpec) (x : Nat) : S.row x < max S.n 1 := by
  unfold BSpec.row; split <;> omega

theorem adrColA_eq (S : BSpec) (A : Array FK) (a : Nat → Nat)
    (h : ∀ x < max S.n 1, A.getD x 0 = FK.x ^ a x) : adrColA S A = S.adrCol a := by
  have h' : ∀ x, A.getD (S.row x) 0 = FK.x ^ a (S.row x) := fun x => h _ (row_lt S x)
  unfold adrColA BSpec.adrCol
  simp only [h', mleF_eq]

/-- **The cached table is the table** when the caches hold the powers of the real rows' cells. -/
theorem tabA_eq (S : BSpec) (W : Array FK) (O : Array (Array FK))
    (hW : ∀ x < max S.n 1, W.getD x 0 = FK.x ^ S.wc x)
    (hO : ∀ j < S.outs.length, ∀ x < max S.n 1, (O.getD j #[]).getD x 0 = FK.x ^ S.oc j x) :
    tabA S W O = S.tab := by
  have hc : (List.range S.width).map (colA S W O) = (List.range S.width).map S.col := by
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    unfold colA BSpec.col
    by_cases h1 : c = 66
    · rw [if_pos h1, if_pos h1]; exact adrColA_eq S W S.wc hW
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : 68 ≤ c ∧ c % 2 = 0
      · rw [if_pos h2, if_pos h2]
        refine adrColA_eq S _ _ fun x hx => hO _ ?_ x hx
        unfold BSpec.width at hc; omega
      · rw [if_neg h2, if_neg h2]
  unfold tabA BSpec.tab
  rw [hc]

theorem getD_map_toArray {α β : Type} (f : α → β) (l : List α) (j : Nat) (d : β) (h : j < l.length) :
    (l.map f).toArray.getD j d = f l[j] := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_range {α : Type} (g : Nat → α) (m x : Nat) (d : α) (h : x < m) :
    ((List.range m).map g).toArray.getD x d = g x := by
  simp [Array.getD, h]

/-! ## `posCell` with its bases passed in -/

/-- `posCell C k o x` with `bb = bitBase`, `sb = spB C + spBefore`, `fl = flB C`, `pa2 = 2^pa`,
`px = posIdx … k 0` (`H`, `t`, `pT`, `nR` the opening's height, `t`, `padT t`, `nRows`). -/
def posCellF (H t pT nR bb sb fl pa2 px x : Nat) : BOut × Nat × Nat → Nat
  | (_, 0, n) =>
    let j := 8 * x + n / H
    if j < pT then bb + H * j + n % H else sb + 2 * (8 * nR - t) + H * (j - pT) + n % H
  | (_, kind, i) =>
    let j := 8 * x + i
    if j < t then fl + (if kind = 1 then 0 else pa2) + (px + j) else sb + 2 * (j - t) + (kind - 1)

theorem posCellF_eq (C : QCfg) (k : Nat) (o : OpenInfo) (x : Nat) (u : BOut × Nat × Nat) :
    posCellF o.L.height o.L.t (padT o.L.t) (nRows o) (bitBase C.p (lay C) k)
      (spB C + spBefore C.p k) (flB C) (2 ^ C.pa) (posIdx C.p k 0) x u = posCell C k o x u := by
  obtain ⟨b, kind, n⟩ := u
  cases kind with
  | zero => rfl
  | succ kind =>
    have hp : posIdx C.p k (8 * x + n) = posIdx C.p k 0 + (8 * x + n) := by unfold posIdx; omega
    simp only [posCellF, posCell]
    rw [hp]

/-- **The position classes' tables, cached** (`posSpecs`' classes; caches over `max n 1` rows). -/
def posTabsA (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List Tab :=
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let cls := (List.range (opens C.p).length).flatMap fun k =>
    let o := (opens C.p).getD k default
    (List.range (nLanes o.L.height)).map fun l => (k, o, l)
  cls.zipIdx.map fun ((k, o, l), c) =>
    let outs := laneOuts o.L.height l
    let m := max (nRows o) 1
    let bb := bitBase C.p (lay C) k
    let sb := spB C + spBefore C.p k
    let fl := flB C
    let px := posIdx C.p k 0
    let W := ((List.range m).map fun x => FK.x ^ (ansLaneF O0 PA C.p (o.pe + x) + l)).toArray
    let O := (outs.map fun u => ((List.range m).map fun x =>
      FK.x ^ posCellF o.L.height o.L.t (padT o.L.t) (nRows o) bb sb fl (2 ^ C.pa) px x u).toArray).toArray
    tabA ⟨clog2 (nRows o), nRows o, outs.map (·.1), true, fun x => ansLane C.p (o.pe + x) + l,
      fun j x => posCell C k o x (outs.getD j (.bit 0, 0, 0)), bpl c⟩ W O

theorem posTabsA_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) :
    posTabsA C bpl = (posSpecs C bpl).map BSpec.tab := by
  unfold posTabsA posSpecs
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨⟨k, o, l⟩, c⟩ -
  simp only [Function.comp, ansLaneF_eq']
  apply tabA_eq
  · intro x hx; exact getD_range _ _ _ _ hx
  · intro j hj x hx
    simp only [List.length_map] at hj
    dsimp only
    rw [getD_map_toArray _ _ j _ hj, getD_range _ _ _ _ hx, posCellF_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]

/-- The aux tables with the position classes cached (then the `s'` byte-shift class, `sSpec`). -/
def auxF (C : QCfg) (D : QData) : List Tab :=
  (sigSpecs (sigIn C) (sigOut C) (bplOf D)).map BSpec.tab ++ posTabsA C (fun c => bplOf D (6 + c)) ++
    [(sSpec C (bplOf D (6 + nPosCls C))).tab]

theorem auxF_eq (C : QCfg) (D : QData) : auxF C D = aux C D := by
  unfold auxF aux bspecs
  rw [List.map_append, List.map_append, posTabsA_eq]
  rfl

/-! ## Group closed forms with a box memo

A piece's `res`/`arg` closed form is `Σ_i eq(r_I, i)·coef_i·boxEval(dims, s_i, r_J)`; in the node
program every row of a column has the same strides `s_i` (QA1's Keccak layer: 1,024 rows), so the box
value is computed once per column (`boxMemo`, at most 8 stride lists) and looked up per row. -/

/-- Up to 8 stride lists with their box values at `rJ`. -/
def boxMemo (dims : List Nat) (rJ : List FE) (ss : List (List Nat)) : List (List Nat × FE) :=
  ss.foldl (fun acc s => if acc.length < 8 && !(acc.any (·.1 == s)) then (s, boxEval dims s rJ) :: acc else acc) []

theorem boxMemo_ok (dims : List Nat) (rJ : List FE) :
    ∀ (ss : List (List Nat)) (acc : List (List Nat × FE)), (∀ e ∈ acc, e.2 = boxEval dims e.1 rJ) →
      ∀ e ∈ ss.foldl (fun acc s => if acc.length < 8 && !(acc.any (·.1 == s)) then
        (s, boxEval dims s rJ) :: acc else acc) acc, e.2 = boxEval dims e.1 rJ
  | [], _, h => h
  | s :: ss, acc, h => by
    simp only [List.foldl_cons]
    apply boxMemo_ok dims rJ ss
    split
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact h e he
    · exact h

/-- The box value of `s` from the memo (computed when absent). -/
def boxLook (M : List (List Nat × FE)) (dims s : List Nat) (rJ : List FE) : FE :=
  match M.find? (fun e => e.1 == s) with
  | some e => e.2
  | none => boxEval dims s rJ

theorem boxLook_eq (M : List (List Nat × FE)) (dims s : List Nat) (rJ : List FE)
    (h : ∀ e ∈ M, e.2 = boxEval dims e.1 rJ) : boxLook M dims s rJ = boxEval dims s rJ := by
  unfold boxLook
  split
  · rename_i e he
    have hs : e.1 = s := by simpa using List.find?_some he
    rw [h e (List.mem_of_find?_eq_some he), hs]
  · rfl

/-- `boxMul` with the memo. -/
def boxMulM (M : List (List Nat × FE)) (a : FE) (dims s : List Nat) (r : List FE) : FE :=
  match dims with
  | [] => a
  | _ :: _ => a * boxLook M dims s r

theorem boxMulM_memo (dims : List Nat) (rJ : List FE) (ss : List (List Nat)) (a : FE) (s : List Nat) :
    boxMulM (boxMemo dims rJ ss) a dims s rJ = boxMul a dims s rJ := by
  cases dims with
  | nil => rfl
  | cons d ds =>
    simp only [boxMulM, boxMul]
    rw [boxLook_eq _ _ _ _ (by unfold boxMemo; exact boxMemo_ok (d :: ds) rJ ss [] (by simp))]

/-- `pieceEvalG` with the box memo. -/
def pieceEvalGM (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  let bc := G.C.bc pe.p.blk
  let rJ := r.take bc.B.lsize
  let rI := r.drop bc.B.lsize
  match c with
  | .res | .arg _ =>
    let M := boxMemo bc.B.dims rJ ((List.range pe.ts.size).map fun i => (colAffineF bc c (pe.ts.getD i 0)).2)
    mleF rI fun i => boxMulM M (coefF bc pe c i) bc.B.dims (colAffineF bc c (pe.ts.getD i 0)).2 rJ
  | .k | .k' => mleF rI (coefF bc pe c)
  | .F => 0

theorem pieceEvalGM_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : pieceEvalGM G pe c r = pieceEvalG G pe c r := by
  cases c <;> simp only [pieceEvalGM, pieceEvalG, boxMulM_memo]

/-- `pieceFixEvalG` with the box memo. -/
def pieceFixEvalGM (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGM G pe c r

theorem pieceFixEvalGM_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) :
    pieceFixEvalGM G pe c r = pieceFixEvalG G pe c r := by
  cases c <;> simp only [pieceFixEvalGM, pieceFixEvalG, pieceEvalGM_eq]

/-- **`grpEvalG` with the box memo.** -/
def grpEvalGM (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGM G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGM_eq (G : PG) (g : Grp) : grpEvalGM G g = grpEvalG G g := by
  funext c r
  unfold grpEvalGM grpEvalG
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  simp only [pieceFixEvalGM_eq]

/-! ## Uniform strides: one `mleF` over the coefficients

When every template row of a piece has the same strides `s₀` in a column, its closed form is
`boxMul (mleF r_I coef) dims s₀ r_J` (`mleF` is linear). `unifS` decides it once per piece and
column (a table built with the parts, `unifT`). -/

theorem mleF_mul (B : FE) : ∀ (r : List FE) (f : Nat → FE), mleF r (fun i => f i * B) = mleF r f * B
  | [], _ => rfl
  | r :: rs, f => by
    simp only [mleF]
    rw [mleF_mul B rs (fun x => f (2 * x)), mleF_mul B rs (fun x => f (2 * x + 1))]
    ring

theorem mleF_boxMul (r rJ : List FE) (f : Nat → FE) (dims s : List Nat) :
    mleF r (fun i => boxMul (f i) dims s rJ) = boxMul (mleF r f) dims s rJ := by
  cases dims with
  | nil => rfl
  | cons d ds => exact mleF_mul _ r f

/-- A column's strides when every template row of the piece has the same ones. -/
def unifS (G : PG) (pe : M3.PE) (c : FCol) : Option (List Nat) :=
  match (List.range pe.ts.size).map (fun i => (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2) with
  | [] => none
  | s0 :: ss =>
    if ss.all (· == s0) && (colAffineF (G.C.bc pe.p.blk) c 0).2 == s0 then some s0 else none

theorem unifS_spec (G : PG) (pe : M3.PE) (c : FCol) (s0 : List Nat) (h : unifS G pe c = some s0) (i : Nat) :
    (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2 = s0 := by
  unfold unifS at h
  generalize hl : (List.range pe.ts.size).map (fun i => (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2) = l at h
  cases l with
  | nil => simp at h
  | cons a ss =>
    simp only at h
    split at h
    · rename_i hall'
      obtain rfl := Option.some.inj h
      have hall : (ss.all fun x => x == a) = true := by simp only [Bool.and_eq_true] at hall'; exact hall'.1
      have h0' : (colAffineF (G.C.bc pe.p.blk) c 0).2 = a := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hall'; exact hall'.2
      have hpos : 0 < pe.ts.size := by
        have := congrArg List.length hl; simp at this; omega
      -- every listed row's strides are `a`
      have hrow : ∀ j < pe.ts.size, (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD j 0)).2 = a := by
        intro j hj
        have hm : (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD j 0)).2 ∈ a :: ss := by
          rw [← hl]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
        rcases List.mem_cons.mp hm with he | he
        · exact he
        · have := List.all_eq_true.mp hall _ he; simpa using this
      by_cases hi : i < pe.ts.size
      · exact hrow i hi
      · have h0 : pe.ts.getD i 0 = 0 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
        rw [h0]; exact h0'
    · simp at h

/-- `pieceEvalGM` with a uniform-stride hint `u` (`unifS`, or `none`). -/
def pieceEvalGU (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c, u with
  | .res, some s0 | .arg _, some s0 =>
    let bc := G.C.bc pe.p.blk
    boxMul (mleF (r.drop bc.B.lsize) (coefF bc pe c)) bc.B.dims s0 (r.take bc.B.lsize)
  | c, _ => pieceEvalGM G pe c r

theorem pieceEvalGU_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) (u : Option (List Nat))
    (hu : ∀ s0, u = some s0 → unifS G pe c = some s0) : pieceEvalGU u G pe c r = pieceEvalG G pe c r := by
  cases u with
  | none => cases c <;> simp only [pieceEvalGU, pieceEvalGM_eq]
  | some s0 =>
    have hs := unifS_spec G pe c s0 (hu s0 rfl)
    cases c with
    | res => simp only [pieceEvalGU, pieceEvalG, hs, mleF_boxMul]
    | arg o => simp only [pieceEvalGU, pieceEvalG, hs, mleF_boxMul]
    | k => simp only [pieceEvalGU, pieceEvalGM_eq]
    | k' => simp only [pieceEvalGU, pieceEvalGM_eq]
    | F => simp only [pieceEvalGU, pieceEvalGM_eq]

/-- A row's strides for column `c`: `colAffineF`'s second part without its first (whose `BC.rank` takes
the template list's length: quadratic over a glue piece, ≈ 5 s of `pre20`). -/
def stridesOf (bc : BC) (c : FCol) (t : Nat) : List Nat :=
  let r := bc.tpl.getD t default
  match c with
  | .res => Loop.scaledStrides bc.B.dims (bc.tw r.ty)
  | .arg o => (r.args.getD o default).strides
  | _ => []

theorem stridesOf_eq (bc : BC) (c : FCol) (t : Nat) : stridesOf bc c t = (colAffineF bc c t).2 := by
  unfold stridesOf colAffineF; cases c <;> rfl

/-- `unifS` on `stridesOf`. -/
def unifSF (G : PG) (pe : M3.PE) (c : FCol) : Option (List Nat) :=
  match (List.range pe.ts.size).map (fun i => stridesOf (G.C.bc pe.p.blk) c (pe.ts.getD i 0)) with
  | [] => none
  | s0 :: ss =>
    if ss.all (· == s0) && stridesOf (G.C.bc pe.p.blk) c 0 == s0 then some s0 else none

theorem unifSF_eq : unifSF = unifS := by
  funext G pe c
  unfold unifSF unifS
  simp only [stridesOf_eq]

/-- Per piece, the uniform strides of its columns (`unifS`), built once. -/
def unifT (G : PG) : Array (List (FCol × Option (List Nat))) :=
  G.pes.map fun pe => [.res, .arg 0, .arg 1, .arg 2].map fun c => (c, unifSF G pe c)

/-- The hint for piece `n`, column `c`. -/
def unifH (U : Array (List (FCol × Option (List Nat)))) (n : Nat) (c : FCol) : Option (List Nat) :=
  match (U.getD n []).find? (fun x => x.1 == c) with
  | some x => x.2
  | none => none

theorem unifH_spec (G : PG) (n : Nat) (c : FCol) (s0 : List Nat) (h : unifH (unifT G) n c = some s0) :
    unifS G (G.pe n) c = some s0 := by
  unfold unifH at h
  split at h
  · rename_i x hx
    have hm := List.mem_of_find?_eq_some hx
    have hc : x.1 = c := by simpa using List.find?_some hx
    by_cases hn : n < G.pes.size
    · have hU : (unifT G).getD n [] = [.res, .arg 0, .arg 1, .arg 2].map fun c => (c, unifS G G.pes[n] c) := by
        simp [unifT, Array.getD_eq_getD_getElem?, hn, unifSF_eq]
      rw [hU] at hm
      obtain ⟨c', -, rfl⟩ := List.mem_map.mp hm
      simp only at hc h; subst hc
      have hpe : G.pe n = G.pes[n] := by unfold PG.pe; rw [dif_pos hn]
      rw [hpe]; exact h
    · have hU : (unifT G).getD n [] = [] := by
        simp [unifT, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)]
      rw [hU] at hm; simp at hm
  · simp at h

/-- `pieceFixEvalGM` with the hints. -/
def pieceFixEvalGU (U : Array (List (FCol × Option (List Nat)))) (n : Nat) (G : PG) (pe : M3.PE) (c : FCol)
    (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGU (unifH U n c) G pe c r

/-- **`grpEvalG` with the uniform-stride hints.** -/
def grpEvalGU (U : Array (List (FCol × Option (List Nat)))) (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGU U n G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGU_eq (G : PG) (g : Grp) : grpEvalGU (unifT G) G g = grpEvalG G g := by
  funext c r
  unfold grpEvalGU grpEvalG
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  have hp : ∀ r', pieceFixEvalGU (unifT G) n G (G.pe n) c r' = pieceFixEvalG G (G.pe n) c r' := by
    intro r'
    cases c <;> simp only [pieceFixEvalGU, pieceFixEvalG] <;>
      exact pieceEvalGU_eq G _ _ r' _ (unifH_spec G n _)
  simp only [hp]

/-! ## The header-independent tables -/

/-- The input arrays before `PUB`. -/
def arrsHead (C : QCfg) (D : QData) : List InArr :=
  let R := 2 ^ C.rl
  (List.range 17).map (fun l => ⟨.K, C.rl, l, 17, [(true, l * R)], fin D l, none⟩) ++
  [⟨.K, 10, sgB C, 1, [(true, 17 * R)], fin D 17, none⟩] ++
  (List.range 17).map (fun l => ⟨.K, 9, xsB C + l, 17, [(false, xOff C + l * R)], fin D (18 + l), none⟩) ++
  (List.range 4).map (fun l => ⟨.K, 9, ysB C + l, 4, [(false, ksY C l + R)], fin D (35 + l), none⟩) ++
  (List.range 4).map (fun l =>
    ⟨.K, 0, mdB C + l, 4, [(false, ksY C l + (spongeBlocks C.p - 1))], fin D (39 + l), none⟩)

/-- `PUB`, the one header-dependent array. -/
def pubA (C : QCfg) (D : QData) (P : Pub) : InArr := pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P)

/-- The input arrays after `PUB` (`QLT`, the `BITS` outputs). -/
def arrsTail (C : QCfg) (D : QData) : List InArr :=
  [pubArr C.aQT (qtB C) 1 (false, 0) (fin D 44) (qltDataF C.p (lay C)),
   ⟨.K, C.bo, obB C, 1, [(false, D.aval)], fin D 45, none⟩]

theorem arrs_split (C : QCfg) (D : QData) (P : Pub) :
    arrs C D P = arrsHead C D ++ [pubA C D P] ++ arrsTail C D := by
  unfold arrs arrsHead pubA arrsTail
  simp only [List.append_assoc, List.cons_append, List.nil_append, qltDataF_eq]

/-- The header-independent parts of the tables. -/
structure Pre where
  /-- The uniform-stride hints (kept so that they are built once with the parts). -/
  unif : Array (List (FCol × Option (List Nat)))
  /-- The groups' tables. -/
  grps : List Tab
  /-- The input arrays' tables before `PUB`. -/
  head : List Tab
  /-- The input arrays' tables after `PUB`. -/
  tail : List Tab
  /-- The aux tables. -/
  aux : List Tab

/-- **The parts** of `QAsm.tabs C G D`. -/
def pre (C : QCfg) (G : PG) (D : QData) : Pre :=
  let U := unifT G
  { unif := U
    grps := (List.range D.groups.length).map fun i =>
    shapeTab (D.groups.getD i default).σ (D.groups.getD i default).τ (grpFix G.C.Q (D.groups.getD i default))
      (grpEvalGU U G (D.groups.getD i default)) (plOf D i)
    head := (arrsHead C D).map InArr.tab
    tail := (arrsTail C D).map InArr.tab
    aux := auxF C D }

/-- The tables from the parts and the header. -/
def tabsPre (R : Pre) (C : QCfg) (D : QData) (P : Pub) : List Tab :=
  R.grps ++ (R.head ++ [InArr.tab (pubA C D P)] ++ R.tail) ++ R.aux

/-- **The parts make the tables.** -/
theorem tabsPre_eq (C : QCfg) (G : PG) (D : QData) (P : Pub) :
    tabsPre (pre C G D) C D P = QAsm.tabs C G D P := by
  unfold tabsPre pre QAsm.tabs lvmTabsC
  rw [arrs_split, auxF_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, grpEvalGU_eq]

/-! ## `V_S` at `P20` -/

/-- The parts at `P20` (a top-level constant: evaluated once per process). -/
def pre20 : Pre := pre cfg20 M3.G20 data20

/-- **The `P20` tables**, header-independent parts shared. -/
def tabs20F (P : Pub) : List Tab := tabsPre pre20 cfg20 data20 P

theorem tabs20F_eq : tabs20F = M3.tabsP20 := funext fun P => tabsPre_eq cfg20 M3.G20 data20 P

/-! ## The bus decomposition with linear stacking -/

/-- `stackBlocks` with the offsets consed and reversed (no repeated append). -/
def stackBlocksF (bs : List NBlock) : List (NBlock × Nat) :=
  let sorted := bs.mergeSort fun a b => decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (NBlock × Nat) × Nat) b => ((b, acc.2) :: acc.1, acc.2 + 2 ^ b.κ))
    ([], 0)).1.reverse

theorem stack_fold : ∀ (l : List NBlock) (acc : List (NBlock × Nat)) (off : Nat),
    (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => (a.1 ++ [(b, a.2)], a.2 + 2 ^ b.κ)) (acc, off)).1 =
      acc ++ (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) ([], off)).1.reverse
  | [], acc, off => by simp
  | b :: l, acc, off => by
    simp only [List.foldl_cons]
    rw [stack_fold l (acc ++ [(b, off)]) (off + 2 ^ b.κ), stack_fold' l [(b, off)] (off + 2 ^ b.κ)]
    simp
where
  stack_fold' : ∀ (l : List NBlock) (acc : List (NBlock × Nat)) (off : Nat),
      (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) (acc, off)).1 =
        (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) ([], off)).1 ++ acc
    | [], acc, off => by simp
    | b :: l, acc, off => by
      simp only [List.foldl_cons]
      rw [stack_fold' l ((b, off) :: acc), stack_fold' l [(b, off)]]
      simp

theorem stackBlocksF_eq (bs : List NBlock) : stackBlocksF bs = stackBlocks bs := by
  unfold stackBlocksF stackBlocks
  rw [stack_fold _ [] 0]
  simp

/-- `busFinalR` with `stackBlocksF`. -/
def busFinalRF (tabs : List Tab) (i : BusIn) : BusOut :=
  let eqα := eqKernel i.alphas
  let sides := (sideBlocks tabs eqα i.beta).map fun bs =>
    (stackBlocksF bs).map fun (b, off) => (b, blockWeight i.point b.κ off)
  let bucket (s : List (NBlock × FE)) : Array (List (List Nat × FE)) :=
    s.foldl (fun acc (b, w) => acc.modify b.tab fun ts =>
      b.form.terms.map (fun t => (t.1, w * t.2)) ++ ts) (Array.replicate tabs.length [])
  let bs := sides.map bucket
  let forms := (List.range tabs.length).map fun j => bs.map fun a => (⟨a.getD j []⟩ : Form)
  let totals := (List.range 3).map fun k =>
    i.values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))
  ⟨i.values.length == 3 && i.leafdec == [0], [], forms, totals⟩

theorem busFinalRF_eq : busFinalRF = busFinalR := by
  funext tabs i
  unfold busFinalRF busFinalR
  simp only [stackBlocksF_eq]

/-- **The `P20` M3 instance**: `M3.real P20 tabs20F` with `busFinalRF`. -/
def m20F : M3 :=
  M3.ofParts P20 (fun i => busFinalRF (sumcheckTabs (tabs20F i.pub)) i)
    (fun pub => (sumcheckTabs (tabs20F pub)).map nativeTable)
    (fun pub => tableClaimsR (sumcheckTabs (tabs20F pub)))
    (fun pub => fixValsR (sumcheckTabs (tabs20F pub)) P20.pubTab)
    (fun pub => fixSentR (sumcheckTabs (tabs20F pub)) P20.pubTab)
    (fun pub => pubCheckR P20.pubTab pub)

theorem m20F_eq : m20F = M3.real P20 M3.tabsP20 := by
  unfold m20F M3.real
  rw [busFinalRF_eq, tabs20F_eq]

/-- **`V_S` at `P20`**, compiled with the shared tables. -/
def VS20F (vk c : Digest) (π : Proof) : OProg Bool := VS P20 m20F vk c π

/-- **It is `VS20`.** -/
theorem VS20F_eq : VS20F = VS20 := by
  funext vk c π
  unfold VS20F VS20 VSL
  rw [m20F_eq]

end Lvm.VF

namespace Lvm.T

open RecursionFast

/-- **The shipped submission**: `submission` with `V_S = VS20F`. -/
def submissionF : Submission := subWith Lvm.VF.VS20F EX20 Lvm.X.extX

/-- **It is the certified one.** -/
theorem submissionF_eq : submissionF = submission := by
  unfold submissionF submission
  rw [Lvm.VF.VS20F_eq]

end Lvm.T
