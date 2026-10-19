import SpartanChainChainEval
import SpartanChainChainSound

/-!
# The prover's tables of the chain R1CS: `z`, `Az`, `Bz`, `Cz` (Rust `chain::witness`)

For a leaf `(s, n)` laid out in `2 ^ κ` blocks, with `h = chainEnd s n`:

* `chainDigests s b`: the digests `chainEnd s t`, `t < b`;
* `blockForm d`: the honest block of the step from `d` as a bitset (`fastTrace`);
* `zBits`: `(w ‖ pub(s, h))` as bits, `2 ^ (15 + κ)`; `azBit`, `bzBit`, `czBit`: the rows of
  `A z`, `B z`, `C z` as bits. Region 0 evaluates the chain block's row forms on the block
  (`Form.evalB`; row 512 is `pub(0) = 1`); region 2 reads the digest bits.

`zBits_eq`, `rowA_honest`, `rowB_honest`, `rowC_honest`: they are the honest extended witness and
its products with the chain matrices (`rowA` … of `SpartanChainChain.lean`).
-/

namespace SpartanChain

open Finset ProductCircuit Blake2sCircuit RecursionFast

/-! ## The digests and the blocks -/

/-- The digests of the chain: `chainEnd s t` for `t < b`. -/
def chainDigests (s : Digest) (b : ℕ) : Array Digest :=
  (Nat.fold b (fun _ _ p ↦ (p.1.push p.2, chainStep p.2)) ((#[] : Array Digest), s)).1

private theorem chainDigests_spec (s : Digest) (b : ℕ) :
    (Nat.fold b (fun _ _ p ↦ (p.1.push p.2, chainStep p.2)) ((#[] : Array Digest), s)).2 =
      chainEnd s b ∧
    (Nat.fold b (fun _ _ p ↦ (p.1.push p.2, chainStep p.2)) ((#[] : Array Digest), s)).1.size = b ∧
    ∀ t, t < b → (Nat.fold b (fun _ _ p ↦ (p.1.push p.2, chainStep p.2))
      ((#[] : Array Digest), s)).1[t]? = some (chainEnd s t) := by
  induction b with
  | zero => exact ⟨rfl, rfl, fun t ht ↦ absurd ht (by omega)⟩
  | succ b ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Nat.fold_succ]
    refine ⟨?_, ?_, fun t ht ↦ ?_⟩
    · simp only; rw [h1, chainEnd, chainEnd, Function.iterate_succ_apply']
    · simp only [Array.size_push, h2]
    · simp only [Array.getElem?_push, h2]
      by_cases htb : t < b
      · rw [ite_eq_right (by omega), h3 t htb]
      · rw [ite_eq_left (by omega), h1, show t = b by omega]

theorem chainDigests_get (s : Digest) {b t : ℕ} (ht : t < b) :
    (chainDigests s b)[t]? = some (chainEnd s t) := (chainDigests_spec s b).2.2 t ht

theorem chainDigests_getD (s : Digest) {b t : ℕ} (ht : t < b) :
    (chainDigests s b).getD t default = chainEnd s t := by
  rw [Array.getD_eq_getD_getElem?, chainDigests_get s ht, Option.getD_some]

/-- The honest block of the step from `d`, as a bitset (built bit by bit, little-endian). -/
def blockForm (d : Digest) : Form Blake2sCircuit.m :=
  let t := fastTrace d
  BitVec.ofNatLT (Nat.ofBits fun k : Fin (2 ^ Blake2sCircuit.m) ↦ t.getD k.val false)
    (Nat.ofBits_lt_two_pow _)

theorem blockForm_getLsbD (d : Digest) (k : Pos Blake2sCircuit.m) :
    (blockForm d).getLsbD k.val = chainTrace d k := by
  rw [blockForm, BitVec.getLsbD, BitVec.toNat_ofNatLT, Nat.testBit_ofBits_lt _ _ k.isLt]
  have := fastTrace_eq d k
  rw [Array.getD_eq_getD_getElem?, this, Option.getD_some]

/-- The rows of a circuit, position by position: the defaults, then each gate set at its
position (one pass over the gates; `rowTable_get`). -/
def rowTable {m : ℕ} (c : ProductCircuit m) : Array (Gate m) :=
  c.gates.foldl (fun t kg ↦ t.set! kg.1.val kg.2) (Array.ofFn fun k ↦ c.rowOfList [] k)

private theorem foldl_setRows {m : ℕ} (L : List (Pos m × Gate m)) (hL : (L.map Prod.fst).Nodup)
    (t₀ : Array (Gate m)) (ht : t₀.size = 2 ^ m) (k : Pos m) :
    (L.foldl (fun t kg ↦ t.set! kg.1.val kg.2) t₀).getD k.val default =
      match L.lookup k with
      | some g => g
      | none => t₀.getD k.val default := by
  induction L generalizing t₀ with
  | nil => rfl
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [List.map_cons, List.nodup_cons] at hL
    rw [List.foldl_cons, ih hL.2 _ (by simp [ht]), List.lookup_cons]
    by_cases hk : k = k'
    · subst hk
      have hnone : rest.lookup k = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        intro he
        have hm := List.mem_map_of_mem (f := Prod.fst) hp
        rw [← he] at hm
        exact hL.1 hm
      simp only [hnone, beq_self_eq_true]
      simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds, ht, k.isLt]
    · have hb : (k == k') = false := by simpa using hk
      rw [hb]
      cases rest.lookup k with
      | some g => rfl
      | none =>
        have : (k'.val ≠ k.val) := fun h ↦ hk (Fin.ext h.symm)
        simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds, this]

theorem rowTable_get {m : ℕ} (c : ProductCircuit m) (hc : c.Bounded) (k : Pos m) :
    (rowTable c).getD k.val default = c.rowOf k := by
  rw [rowTable, ← Array.foldl_toList,
    foldl_setRows _ (nodup_keys_of_boundedFrom hc) _ Array.size_ofFn k]
  simp only [rowOf, rowOfList]
  cases c.gates.toList.lookup k with
  | some g => rfl
  | none =>
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, k.isLt, rowOfList]

/-- The rows of the chain block (`rowOf`), as an array. -/
def rowArray (base : ℕ) : Array (Gate Blake2sCircuit.m) := rowTable (chainBlockAt base)

theorem rowArray_get (k : Pos Blake2sCircuit.m) :
    (rowArray gateBase).getD k.val default = chainBlock.rowOf k := by
  rw [rowArray, chainBlockAt_eq]
  exact rowTable_get chainBlock bounded_chainBlock k

/-! ## The bits of the tables -/

/-- Bit `x` of `z = (w ‖ pub)`, given the honest blocks. -/
def zBit (κ : ℕ) (s h : Digest) (forms : Array (Form Blake2sCircuit.m)) (x : ℕ) : Bool :=
  if x < wLen κ then (forms.getD (x / 16384) 0).getLsbD (x % 16384)
  else pubBit s h (x - wLen κ)

/-- Bit `x` of `A z`. -/
def azBit (n κ : ℕ) (msgs : Array Digest) (forms : Array (Form Blake2sCircuit.m))
    (rows : Array (Gate Blake2sCircuit.m)) (x : ℕ) : Bool :=
  if x < wLen κ then
    if x % 16384 = 512 then true
    else (rows.getD (x % 16384) default).a.evalB (forms.getD (x / 16384) 0)
  else if x - wLen κ < 2 ^ (8 + κ) then
    dbit (msgs.getD ((x - wLen κ) / 256) default) ((x - wLen κ) % 256)
  else if x - wLen κ < 2 ^ (8 + κ) + 256 then
    dbit (msgs.getD n default) (x - wLen κ - 2 ^ (8 + κ))
  else false

/-- Bit `x` of `B z`. -/
def bzBit (κ : ℕ) (forms : Array (Form Blake2sCircuit.m)) (rows : Array (Gate Blake2sCircuit.m))
    (x : ℕ) : Bool :=
  if x < wLen κ then
    if x % 16384 = 512 then true
    else (rows.getD (x % 16384) default).b.evalB (forms.getD (x / 16384) 0)
  else decide (x - wLen κ < 2 ^ (8 + κ) + 256)

/-- Bit `x` of `C z`. -/
def czBit (n κ : ℕ) (msgs : Array Digest) (forms : Array (Form Blake2sCircuit.m)) (x : ℕ) : Bool :=
  if x < wLen κ then (forms.getD (x / 16384) 0).getLsbD (x % 16384)
  else if x - wLen κ < 2 ^ (8 + κ) then
    dbit (msgs.getD ((x - wLen κ) / 256) default) ((x - wLen κ) % 256)
  else if x - wLen κ < 2 ^ (8 + κ) + 256 then
    dbit (msgs.getD n default) (x - wLen κ - 2 ^ (8 + κ))
  else false

/-- The honest blocks of a leaf with `2 ^ κ` blocks. -/
def chainForms (s : Digest) (κ : ℕ) : Array (Form Blake2sCircuit.m) :=
  (chainDigests s (2 ^ κ)).map blockForm

theorem chainForms_get (s : Digest) {κ t : ℕ} (ht : t < 2 ^ κ) (k : Pos Blake2sCircuit.m) :
    ((chainForms s κ).getD t 0).getLsbD k.val = chainTrace (chainEnd s t) k := by
  rw [chainForms, Array.getD_eq_getD_getElem?, Array.getElem?_map, chainDigests_get s ht,
    Option.map_some, Option.getD_some, blockForm_getLsbD]

/-! ## Correctness -/

variable {E : Type} [Field E] [CharP E 2] {n κ : ℕ} (s : Digest)

/-- The honest extended witness `(w ‖ pub(s, chainEnd s n))`. -/
noncomputable def zHonest (n κ : ℕ) : Ix κ → E :=
  zOf (chainWitness (E := E) s κ) s (chainEnd s n)

theorem zN_honest_w {t k : ℕ} (ht : t < 2 ^ κ) (hk : k < 16384) :
    zN (zHonest (E := E) s n κ) (k + 16384 * t) =
      ofBool E (chainTrace (chainEnd s t) (pos k)) := by
  have := wLen_eq κ
  rw [zHonest, zN_zOf_w _ _ _ (by omega)]
  simp only [chainWitness, show (k + 16384 * t) / 16384 = t by omega,
    show (k + 16384 * t) % 16384 = k by omega]

theorem pubBit_val (s h : Digest) (u : ℕ) :
    pubVal (E := E) s h u = ofBool E (pubBit s h u) := by
  unfold pubVal pubBit ofBool
  split_ifs <;> simp_all

theorem zN_honest_pub {u : ℕ} (hu : u < wLen κ) :
    zN (zHonest (E := E) s n κ) (wLen κ + u) = ofBool E (pubBit s (chainEnd s n) u) := by
  rw [zHonest, zN_zOf_pub _ _ _ hu, pubBit_val]

/-- **The bits of `z`.** -/
theorem zBits_eq {v : ℕ} (hv : v < 2 ^ (14 + κ + 1)) :
    zN (zHonest (E := E) s n κ) v = ofBool E (zBit κ s (chainEnd s n) (chainForms s κ) v) := by
  have hw := wLen_eq κ
  have hL := ixLen_eq κ
  unfold zBit
  by_cases h0 : v < wLen κ
  · rw [ite_eq_left h0, show v = v % 16384 + 16384 * (v / 16384) by omega,
      zN_honest_w s (by omega) (by omega)]
    rw [show (v % 16384 + 16384 * (v / 16384)) / 16384 = v / 16384 by omega,
      show (v % 16384 + 16384 * (v / 16384)) % 16384 = v % 16384 by omega]
    have := chainForms_get s (κ := κ) (t := v / 16384) (by omega) (pos (v % 16384))
    rw [pos_val (show v % 16384 < 2 ^ Blake2sCircuit.m by show _ < 16384; omega)] at this
    rw [this]
  · rw [ite_eq_right h0, show v = wLen κ + (v - wLen κ) by omega,
      zN_honest_pub s (by omega), show wLen κ + (v - wLen κ) - wLen κ = v - wLen κ by omega]

theorem pubBit_zero (s h : Digest) : pubBit s h 0 = true := rfl

theorem pubBit_s (s h : Digest) {j : ℕ} (hj : j < 256) : pubBit s h (1 + j) = dbit s j := by
  simp only [pubBit, show 1 + j ≠ 0 by omega, show 1 + j < 257 by omega, ↓reduceIte,
    show 1 + j - 1 = j by omega]

theorem pubBit_h (s h : Digest) {j : ℕ} (hj : j < 256) : pubBit s h (257 + j) = dbit h j := by
  simp only [pubBit, show 257 + j ≠ 0 by omega, show ¬ 257 + j < 257 by omega,
    show 257 + j < 513 by omega, ↓reduceIte, show 257 + j - 257 = j by omega]

private theorem msgs_get {κ t : ℕ} (ht : t ≤ 2 ^ κ) :
    (chainDigests s (2 ^ κ + 1)).getD t default = chainEnd s t :=
  chainDigests_getD s (by omega)

private theorem zpub0 : zN (zHonest (E := E) s n κ) (wLen κ) = 1 := by
  have := zN_honest_pub (E := E) (n := n) (κ := κ) s (u := 0) (by rw [wLen_eq]; positivity)
  rwa [add_zero, pubBit_zero] at this

/-- A region-0 row of a block matrix, on the honest witness. -/
private theorem block_row (sel : Gate Blake2sCircuit.m → Form Blake2sCircuit.m)
    (bk : Pos Blake2sCircuit.m → Pos Blake2sCircuit.m → Bool)
    (hbk : ∀ k j, k ≠ constPos → bk k j = (sel (chainBlock.rowOf k)).getLsbD j)
    {t k : ℕ} (ht : t < 2 ^ κ) (hk : k < 16384) (hk5 : k ≠ 512) :
    (∑ j : Pos Blake2sCircuit.m, if bk (pos k) j = true then
      zN (zHonest (E := E) s n κ) (j.val + 16384 * t) else 0) =
      ofBool E ((sel ((rowArray gateBase).getD k default)).evalB ((chainForms s κ).getD t 0)) := by
  have hpk : ((pos k : Pos Blake2sCircuit.m) : ℕ) = k := pos_val (show k < 2 ^ Blake2sCircuit.m from hk)
  have hne : (pos k : Pos Blake2sCircuit.m) ≠ constPos := fun h ↦ hk5 (by rw [← hpk, h]; rfl)
  have hr : (rowArray gateBase).getD k default = chainBlock.rowOf (pos k) := by
    have := rowArray_get (pos k : Pos Blake2sCircuit.m); rwa [hpk] at this
  rw [hr, evalB_eq_eval]
  have hf : (fun j : Pos Blake2sCircuit.m ↦ ((chainForms s κ).getD t 0).getLsbD j.val) =
      chainTrace (chainEnd s t) := funext fun j ↦ chainForms_get s ht j
  rw [hf, ← sum_liftBlock]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [hbk _ _ hne, zN_honest_w s ht j.isLt, pos_val14]
  rfl

/-- **Row `v` of `A z`** on the honest witness is `azBit`. -/
theorem rowA_honest (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ) {v : ℕ} (hv : v < 2 ^ (14 + κ + 1)) :
    rowA n κ (zN (zHonest (E := E) s n κ)) v = ofBool E
      (azBit n κ (chainDigests s (2 ^ κ + 1)) (chainForms s κ) (rowArray gateBase) v) := by
  have hw := wLen_eq κ
  have hL := ixLen_eq κ
  have h8 := pow8_eq κ
  unfold rowA azBit
  by_cases h0 : v < wLen κ
  · rw [ite_eq_left h0, ite_eq_left h0]
    by_cases h5 : v % 16384 = 512
    · rw [ite_eq_left h5, ite_eq_left h5, zpub0]; rfl
    · rw [ite_eq_right h5, ite_eq_right h5]
      exact block_row s (fun g ↦ g.a) blockA (fun k j hk ↦ blockA_eq hk j) (by omega) (by omega) h5
  · rw [ite_eq_right h0, ite_eq_right h0]
    set i := v - wLen κ
    by_cases h1 : i < 256
    · rw [ite_eq_left h1, ite_eq_left (by omega : i < 2 ^ (8 + κ)),
        show wLen κ + 1 + i = wLen κ + (1 + i) by ring, zN_honest_pub s (by omega),
        pubBit_s _ _ h1, msgs_get s (by omega), show i / 256 = 0 by omega,
        show i % 256 = i by omega]
      rfl
    · rw [ite_eq_right h1]
      by_cases h2 : i < 2 ^ (8 + κ)
      · rw [ite_eq_left h2, ite_eq_left h2,
          show 256 + i % 256 + 16384 * (i / 256 - 1) = (256 + i % 256) + 16384 * (i / 256 - 1)
            by ring, zN_honest_w s (by omega) (by omega), chainTrace_out _ (Nat.mod_lt _ (by omega)),
          chainEnd_succ' s (by omega), msgs_get s (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : i < 2 ^ (8 + κ) + 256
        · rw [ite_eq_left h3, ite_eq_left h3,
            show 256 + (i - 2 ^ (8 + κ)) + 16384 * (n - 1) =
              (256 + (i - 2 ^ (8 + κ))) + 16384 * (n - 1) by ring,
            zN_honest_w s (by omega) (by omega), chainTrace_out _ (by omega), chainEnd_succ' s hn,
            msgs_get s hnκ]
        · rw [ite_eq_right h3, ite_eq_right h3]; rfl

/-- **Row `v` of `B z`** on the honest witness is `bzBit`. -/
theorem rowB_honest {v : ℕ} (hv : v < 2 ^ (14 + κ + 1)) :
    rowB κ (zN (zHonest (E := E) s n κ)) v =
      ofBool E (bzBit κ (chainForms s κ) (rowArray gateBase) v) := by
  have hw := wLen_eq κ
  unfold rowB bzBit
  by_cases h0 : v < wLen κ
  · rw [ite_eq_left h0, ite_eq_left h0]
    by_cases h5 : v % 16384 = 512
    · rw [ite_eq_left h5, ite_eq_left h5, zpub0]; rfl
    · rw [ite_eq_right h5, ite_eq_right h5]
      exact block_row s (fun g ↦ g.b) blockB (fun k j hk ↦ blockB_eq hk j) (by omega) (by omega) h5
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h3 : v - wLen κ < 2 ^ (8 + κ) + 256
    · rw [ite_eq_left h3, zpub0, decide_eq_true h3]; rfl
    · rw [ite_eq_right h3, decide_eq_false h3]; rfl

/-- **Row `v` of `C z`** on the honest witness is `czBit`. -/
theorem rowC_honest (hnκ : n ≤ 2 ^ κ) {v : ℕ} (hv : v < 2 ^ (14 + κ + 1)) :
    rowC κ (zN (zHonest (E := E) s n κ)) v =
      ofBool E (czBit n κ (chainDigests s (2 ^ κ + 1)) (chainForms s κ) v) := by
  have hw := wLen_eq κ
  have hL := ixLen_eq κ
  have h8 := pow8_eq κ
  unfold rowC czBit
  by_cases h0 : v < wLen κ
  · rw [ite_eq_left h0, ite_eq_left h0, zBits_eq s hv, zBit, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    set i := v - wLen κ
    by_cases h2 : i < 2 ^ (8 + κ)
    · rw [ite_eq_left h2, ite_eq_left h2,
        show 648 + i % 256 + 16384 * (i / 256) = (648 + i % 256) + 16384 * (i / 256) by ring,
        zN_honest_w s (by omega) (by omega), chainTrace_in _ (Nat.mod_lt _ (by omega)),
        msgs_get s (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : i < 2 ^ (8 + κ) + 256
      · rw [ite_eq_left h3, ite_eq_left h3,
          show wLen κ + 257 + (i - 2 ^ (8 + κ)) = wLen κ + (257 + (i - 2 ^ (8 + κ))) by ring,
          zN_honest_pub s (by omega), pubBit_h _ _ (by omega), msgs_get s hnκ]
      · rw [ite_eq_right h3, ite_eq_right h3]; rfl

end SpartanChain
