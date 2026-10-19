import SpartanChainChainCols
import SpartanChainChainTables

/-!
# The prover's inner table `M̃_ρ(r_x, ·)` of the chain R1CS (Rust `Circuit::transpose`)

* `setBits L`: the set positions of a form, word by word (`mem_setBits`, `nodup_setBits`).
* `transposeArr sel e`: `(M0ᵀ e)(j) = Σ_{k ≠ 512} e(k) [j ∈ sel(rowOf k)]` for the block matrix
  with rows `sel (rowOf k)`, by scattering `e(k)` over the set bits of every row
  (`transposeArr_get`).
* `innerTab n κ r_x ρ`: the table `y ↦ Ã(r_x, y) + ρ B̃(r_x, y) + ρ² C̃(r_x, y)` over the
  `2^(15+κ)` columns, from `colA`, `colB`, `colC` with the tables `eq(r_x, ·)` and the transposes
  (`innerTab_eq`).
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast Spartan

/-! ## Set bits -/

/-- The set positions `base + b` of a 32-bit chunk `w`. -/
def chunkBits (w base : ℕ) : List ℕ :=
  if w = 0 then [] else (List.range 32).filterMap fun b ↦ if w.testBit b then some (base + b) else none

/-- The set positions `base + j` of `n < 2^(32·2^l)`, by halving (`2^l` chunks of 32 bits;
empty halves are skipped). -/
def setBitsRec : ℕ → ℕ → ℕ → List ℕ
  | 0, base, n => chunkBits n base
  | l + 1, base, n =>
    if n = 0 then []
    else setBitsRec l base (n % 2 ^ (32 * 2 ^ l)) ++
      setBitsRec l (base + 32 * 2 ^ l) (n >>> (32 * 2 ^ l))

/-- The set positions of a form, increasing. -/
def setBits (L : Form Blake2sCircuit.m) : List ℕ := setBitsRec 9 0 L.toNat

theorem mem_chunkBits (w base j : ℕ) :
    j ∈ chunkBits w base ↔ base ≤ j ∧ j < base + 32 ∧ w.testBit (j - base) = true := by
  unfold chunkBits
  split_ifs with hw
  · subst hw; simp
  · simp only [List.mem_filterMap, List.mem_range, Option.ite_none_right_eq_some,
      Option.some.injEq]
    constructor
    · rintro ⟨b, hb, hbit, rfl⟩
      exact ⟨by omega, by omega, by rwa [show base + b - base = b by omega]⟩
    · rintro ⟨h1, h2, hbit⟩
      exact ⟨j - base, by omega, hbit, by omega⟩

theorem nodup_chunkBits (w base : ℕ) : (chunkBits w base).Nodup := by
  unfold chunkBits
  split_ifs
  · exact List.nodup_nil
  · refine (List.nodup_range).filterMap fun a a' b ha ha' ↦ ?_
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at ha ha'
    omega

theorem mem_setBitsRec (l : ℕ) : ∀ (base n j : ℕ), n < 2 ^ (32 * 2 ^ l) →
    (j ∈ setBitsRec l base n ↔ base ≤ j ∧ j < base + 32 * 2 ^ l ∧ n.testBit (j - base) = true) := by
  induction l with
  | zero => intro base n j _; rw [setBitsRec]; simpa using mem_chunkBits n base j
  | succ l ih =>
    intro base n j hn
    have hp : 2 ^ (32 * 2 ^ (l + 1)) = 2 ^ (32 * 2 ^ l) * 2 ^ (32 * 2 ^ l) := by
      rw [← pow_add]; congr 1; rw [pow_succ]; ring
    have hP : 32 * 2 ^ (l + 1) = 32 * 2 ^ l + 32 * 2 ^ l := by rw [pow_succ]; ring
    rw [setBitsRec]
    split_ifs with h0
    · subst h0; simp
    · have hlo : n % 2 ^ (32 * 2 ^ l) < 2 ^ (32 * 2 ^ l) := Nat.mod_lt _ (by positivity)
      have hhi : n >>> (32 * 2 ^ l) < 2 ^ (32 * 2 ^ l) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← hp]; exact hn
      rw [List.mem_append, ih _ _ _ hlo, ih _ _ _ hhi, Nat.testBit_mod_two_pow,
        Nat.testBit_shiftRight, hP]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
          exact ⟨h1, by omega, h3.2⟩
        · refine ⟨by omega, by omega, ?_⟩
          rwa [show 32 * 2 ^ l + (j - (base + 32 * 2 ^ l)) = j - base by omega] at h3
      · rintro ⟨h1, h2, h3⟩
        by_cases hj : j < base + 32 * 2 ^ l
        · left
          refine ⟨h1, hj, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, h3⟩
        · right
          refine ⟨by omega, by omega, ?_⟩
          rwa [show 32 * 2 ^ l + (j - (base + 32 * 2 ^ l)) = j - base by omega]

theorem nodup_setBitsRec (l : ℕ) : ∀ base n, n < 2 ^ (32 * 2 ^ l) → (setBitsRec l base n).Nodup := by
  induction l with
  | zero => intro base n _; exact nodup_chunkBits _ _
  | succ l ih =>
    intro base n hn
    have hp : 2 ^ (32 * 2 ^ (l + 1)) = 2 ^ (32 * 2 ^ l) * 2 ^ (32 * 2 ^ l) := by
      rw [← pow_add]; congr 1; rw [pow_succ]; ring
    rw [setBitsRec]
    split_ifs
    · exact List.nodup_nil
    · have hlo : n % 2 ^ (32 * 2 ^ l) < 2 ^ (32 * 2 ^ l) := Nat.mod_lt _ (by positivity)
      have hhi : n >>> (32 * 2 ^ l) < 2 ^ (32 * 2 ^ l) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← hp]; exact hn
      rw [List.nodup_append]
      refine ⟨ih _ _ hlo, ih _ _ hhi, fun a ha b hb ↦ ?_⟩
      rw [mem_setBitsRec _ _ _ _ hlo] at ha
      rw [mem_setBitsRec _ _ _ _ hhi] at hb
      omega

private theorem toNat_lt (L : Form Blake2sCircuit.m) : L.toNat < 2 ^ (32 * 2 ^ 9) := L.isLt

theorem mem_setBits (L : Form Blake2sCircuit.m) (j : ℕ) :
    j ∈ setBits L ↔ j < 16384 ∧ L.getLsbD j = true := by
  rw [setBits, mem_setBitsRec _ _ _ _ (toNat_lt L)]
  simp only [Nat.zero_le, true_and, zero_add, Nat.sub_zero, BitVec.getLsbD]
  norm_num

theorem nodup_setBits (L : Form Blake2sCircuit.m) : (setBits L).Nodup :=
  nodup_setBitsRec _ _ _ (toNat_lt L)

theorem sum_list_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-! ## Scattering -/

/-- Add `c` at every position of `l`. -/
def scatter (l : List ℕ) (c : EF) (a : Array EF) : Array EF :=
  l.foldl (fun a j ↦ a.modify j (· + c)) a

theorem scatter_cons (i : ℕ) (l : List ℕ) (c : EF) (a : Array EF) :
    scatter (i :: l) c a = scatter l c (a.modify i (· + c)) := rfl

theorem scatter_size (l : List ℕ) (c : EF) (a : Array EF) : (scatter l c a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih => rw [scatter_cons, ih, Array.size_modify]

theorem scatter_get (l : List ℕ) (hl : l.Nodup) (c : EF) (a : Array EF) {j : ℕ} (hj : j < a.size) :
    (scatter l c a).getD j 0 = a.getD j 0 + if j ∈ l then c else 0 := by
  induction l generalizing a with
  | nil => simp [scatter]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [scatter_cons, ih hl.2 _ (by simp [hj])]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
    by_cases hij : i = j
    · subst hij
      simp [hl.1, Array.getElem?_eq_getElem hj, add_comm]
    · simp only [hij, ↓reduceIte, List.mem_cons, Ne.symm hij, false_or]

/-- The transpose of a block matrix with rows `sel (rows k)` (row 512 cleared) against `e`. -/
def transposeArr (rows : Array (Gate Blake2sCircuit.m)) (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m)
    (e : Array EF) : Array EF :=
  (List.range 16384).foldl (fun a k ↦
    if k = 512 then a else scatter (setBits (sel (rows.getD k default))) (e.getD k 0) a)
    (Array.replicate 16384 0)

private theorem transpose_fold (rows : Array (Gate Blake2sCircuit.m))
    (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m) (e : Array EF) (ks : List ℕ)
    (a : Array EF) (ha : a.size = 16384) :
    (ks.foldl (fun a k ↦ if k = 512 then a else scatter (setBits (sel (rows.getD k default)))
      (e.getD k 0) a) a).size = 16384 ∧
    ∀ j, j < 16384 → (ks.foldl (fun a k ↦ if k = 512 then a else
      scatter (setBits (sel (rows.getD k default))) (e.getD k 0) a) a).getD j 0 =
      a.getD j 0 + (ks.map fun k ↦ if k ≠ 512 ∧ (sel (rows.getD k default)).getLsbD j = true
        then e.getD k 0 else 0).sum := by
  induction ks generalizing a with
  | nil => simp [ha]
  | cons k ks ih =>
    simp only [List.foldl_cons]
    by_cases hk : k = 512
    · simp only [hk, ↓reduceIte]
      obtain ⟨h1, h2⟩ := ih a ha
      refine ⟨h1, fun j hj ↦ ?_⟩
      rw [h2 j hj]; simp
    · simp only [hk, ↓reduceIte]
      have hs : (scatter (setBits (sel (rows.getD k default))) (e.getD k 0) a).size = 16384 := by
        rw [scatter_size, ha]
      obtain ⟨h1, h2⟩ := ih _ hs
      refine ⟨h1, fun j hj ↦ ?_⟩
      rw [h2 j hj, scatter_get _ (nodup_setBits _) _ _ (by omega)]
      simp only [mem_setBits, hj, true_and, List.map_cons, List.sum_cons, ne_eq, hk,
        not_false_eq_true]
      ring

theorem transposeArr_size (rows : Array (Gate Blake2sCircuit.m))
    (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m) (e : Array EF) :
    (transposeArr rows sel e).size = 16384 :=
  (transpose_fold rows sel e _ _ (by simp)).1

theorem transposeArr_get (rows : Array (Gate Blake2sCircuit.m))
    (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m) (e : Array EF) {j : ℕ} (hj : j < 16384) :
    (transposeArr rows sel e).getD j 0 =
      ∑ k : Pos Blake2sCircuit.m, if k.val ≠ 512 ∧ (sel (rows.getD k.val default)).getLsbD j = true
        then e.getD k.val 0 else 0 := by
  rw [transposeArr, (transpose_fold rows sel e _ _ (by simp)).2 j hj]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hj, ↓reduceIte,
    Option.getD_some, zero_add]
  rw [sum_list_range]
  exact (Fin.sum_univ_eq_sum_range (fun k ↦ if k ≠ 512 ∧
    (sel (rows[k]?.getD default)).getLsbD j = true then e[k]?.getD 0 else 0) 16384).symm

/-! ## The inner table -/

/-- **The prover's inner table** `y ↦ M̃_ρ(r_x, y)` of the chain R1CS (`2^(15+κ)` entries). -/
def innerTab (n κ : ℕ) (rx : List EF) (ρ : EF) : Array EF :=
  let L := 14 + κ + 1
  let Et := eqTable rx
  let eT := eqTable ((rx.drop 14).take κ)
  let e := eqTable (rx.take 14)
  let rows := rowArray gateBase
  let bA := transposeArr rows (fun g ↦ g.a) e
  let bB := transposeArr rows (fun g ↦ g.b) e
  let Q : ℕ → EF := fun x ↦ Et.getD (x % 2 ^ L) 0
  let QT : ℕ → EF := fun t ↦ eT.getD (t % 2 ^ κ) 0
  let rtop := ptN L rx (14 + κ)
  let fA : ℕ → EF := fun j ↦ bA.getD (j % 16384) 0
  let fB : ℕ → EF := fun j ↦ bB.getD (j % 16384) 0
  Array.ofFn (n := 2 ^ ly κ) fun y ↦
    colA n κ Q QT rtop fA y.val + ρ * colB κ Q QT rtop fB y.val + ρ ^ 2 * colC κ Q y.val

section Correct

variable {κ : ℕ} (rx : List EF) (hx : rx.length = ly κ)
include hx

theorem Q_eq : (fun x ↦ (eqTable rx).getD (x % 2 ^ (14 + κ + 1)) 0) =
    eqv (ptN (14 + κ + 1) rx) (14 + κ + 1) := by
  funext x
  rw [← eqv_mod]
  have hl : rx.length = 14 + κ + 1 := by rw [hx, ly_eq]
  have := eqTable_take_getD rx (14 + κ + 1) (by omega) (le_refl _)
    ⟨x % 2 ^ (14 + κ + 1), Nat.mod_lt _ (by positivity)⟩
  rwa [List.take_of_length_le (by omega)] at this

theorem QT_eq : (fun t ↦ (eqTable ((rx.drop 14).take κ)).getD (t % 2 ^ κ) 0) =
    eqv (shiftPt (ptN (14 + κ + 1) rx) 14) κ := by
  funext t
  rw [← eqv_mod]
  have hl : rx.length = 14 + κ + 1 := by rw [hx, ly_eq]
  have := congrFun (tbl_eqTable' ((rx.drop 14).take κ) (by simp; omega))
    ⟨t % 2 ^ κ, Nat.mod_lt _ (by positivity)⟩
  simp only [tbl] at this
  rw [this, eqv_eq_eq _ κ ⟨t % 2 ^ κ, Nat.mod_lt _ (by positivity)⟩]
  congr 1
  funext l
  have := l.isLt
  simp [ptOf, ptN, shiftPt, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    l.isLt, show 14 + (l : ℕ) < 14 + κ + 1 by omega]

theorem transpose_eq (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m)
    (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool)
    (hbk : ∀ k j, bk k j = (decide (k ≠ constPos) && (sel (chainBlock.rowOf k)).getLsbD j)) :
    (fun j ↦ (transposeArr (rowArray gateBase) sel (eqTable (rx.take 14))).getD (j % 16384) 0) =
      bsum bk (ptN (14 + κ + 1) rx) := by
  have hl : rx.length = 14 + κ + 1 := by rw [hx, ly_eq]
  funext j
  rw [transposeArr_get _ _ _ (Nat.mod_lt _ (by omega)), bsum]
  refine sum_congr rfl fun k _ ↦ ?_
  have hpj : ((pos j : Pos Blake2sCircuit.m) : ℕ) = j % 16384 := rfl
  rw [hbk, rowArray_get, hpj, eqTable_take_getD rx 14 (by omega) (L := 14 + κ + 1) (by omega) k]
  have hk : (k.val ≠ 512) ↔ (k ≠ constPos) := ⟨fun h e ↦ h (by rw [e]; rfl),
    fun h e ↦ h (Fin.ext e)⟩
  by_cases hc : k ≠ constPos
  · simp [hc, hk.mpr hc]
  · simp only [ne_eq, Decidable.not_not] at hc
    simp [hc, show (constPos : Pos Blake2sCircuit.m).val = 512 from rfl]

end Correct

/-- Sums over the protocol's cube, read on the chain's. -/
theorem sum_cube_cast {E : Type} [Field E] {L L' : ℕ} (h : L' = L) (r : Fin L' → E)
    (f : Fin (2 ^ L) → E) :
    ∑ x : Fin (2 ^ L'), eq r (cube x) * f (Fin.cast (by rw [h]) x) =
      ∑ x : Fin (2 ^ L), eq (fun l ↦ r (Fin.cast h.symm l)) (cube x) * f x := by
  subst h; rfl

/-- **The inner table is honest**: entry `y` is `M̃_ρ(r_x, y)` of the chain matrices. -/
theorem innerTab_eq {n κ : ℕ} (rx : List EF) (hx : rx.length = ly κ) (ρ : EF) :
    (innerTab n κ rx ρ).size = 2 ^ ly κ ∧
    tbl (ly κ) (innerTab n κ rx ρ) = fun y ↦ matMle (chainA' n κ) (ptOf _ rx) (cube y) +
      ρ * matMle (chainB' κ) (ptOf _ rx) (cube y) + ρ ^ 2 * matMle (chainC' κ) (ptOf _ rx) (cube y) := by
  have hl := ly_eq κ
  refine ⟨Array.size_ofFn, ?_⟩
  funext y
  show (innerTab n κ rx ρ).getD y.val 0 = _
  unfold innerTab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left y.isLt, Option.getD_some]
  dsimp only
  rw [Q_eq rx hx, QT_eq rx hx, transpose_eq rx hx (fun g ↦ g.a) blockA (fun _ _ ↦ rfl),
    transpose_eq rx hx (fun g ↦ g.b) blockB (fun _ _ ↦ rfl)]
  simp only [matMle_cube]
  unfold chainA' chainB' chainC' castIx
  rw [sum_cube_cast hl (ptOf _ rx) (fun x ↦ chainA n κ x _),
    sum_cube_cast hl (ptOf _ rx) (fun x ↦ chainB κ x _),
    sum_cube_cast hl (ptOf _ rx) (fun x ↦ chainC κ x _),
    col_chainA, col_chainB, col_chainC, extPt_ptOf hl, Fin.val_cast]

end SpartanChain
