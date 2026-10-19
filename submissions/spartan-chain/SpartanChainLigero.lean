import SpartanChainPCSBounds
import SpartanChainTranscript

/-!
# The Ligero PCS over the packed witness (blueprint §5.2–§5.4, §6.2 steps 2–4 and 11–13, §7)

The shape is `PCS.rows κ × PCS.msgLen κ`, encoded to `PCS.cols κ` columns (`SpartanChainPCSBounds`).

* **Field kernels**, monomorphic in `F`/`EF` (compiled code): `tensorF` (the tensor
  `(X_j(a))_j`), `encAtE` (`Enc(msg)_a` for an `EF` message, three `F` products per term),
  `columnAt` (one column of `U` for the prover), `comb` and `combRows` (`Σ_i w_i·col_i` and
  `Σ_i w_i·Q[i]`). `encAtE_eq`, `columnAt_getD` tie them to `RS.enc`.
* **Bytes** (§7): `efBytes`, `fBytes`, `labelsBytes`; `readEF(s)`, `readF(s)`, `readLabel`.
* **Verifier**: `verify1` (steps 2–4: absorb `root`, squeeze `r`, absorb `ū`) and `verify2`
  (steps 11–13: absorb `v`, squeeze the indices, check `t` openings: Merkle path and the two
  column equations `colCheck`). `run_verify2` and `colCheck_iff` state what acceptance means.
* **Prover**: `commit` (rows, columns, Merkle tree), `prove1`, `prove2`; `prove1_verify1`
  (same transcript) and `colCheck_honest` (the honest columns satisfy both equations, for every
  coefficient vector).
* **Sizes**: `size1 κ = 31 + 24k` (fields 1–2 of §7), `size2 κ = 24k + t(8m + 31ℓ_N)`
  (fields 8–9).
-/

namespace SpartanChain.Ligero

open RecursionFast RS PCS Transcript

/-! ### Field kernels -/

/-- §5.1's constants for message length `2^ℓ`. -/
def kapArr (ℓ : ℕ) : Array F := kappaArr pt ℓ

/-- An array of constants as a function (default `0`). -/
def kapFn (ks : Array F) (i : ℕ) : F := ks.getD i 0

theorem kapFn_kapArr (ℓ : ℕ) : kapFn (kapArr ℓ) = kap ℓ := rfl

/-- The point `ω_c` of column `c`. -/
def ptOf (c : ℕ) : F := F.ofUInt64 (UInt64.ofNat c)

theorem dom_eq_ptOf {N : ℕ} (c : Fin N) : dom N c = ptOf c := rfl

/-- `((X_j(a))_{j<2^ℓ}, W_ℓ(a))` over `F`. -/
def tensorF (ks : Array F) (a : F) : ℕ → Array F × F
  | 0 => (#[1], a)
  | ℓ + 1 =>
    let p := tensorF ks a ℓ
    (p.1 ++ p.1.map (· * p.2), p.2 * (p.2 + ks.getD ℓ 0))

theorem tensorF_eq (ks : Array F) (a : F) (ℓ : ℕ) : tensorF ks a ℓ = tensorAux (kapFn ks) a ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp only [tensorF, tensorAux, ih]; rfl

/-- `Enc(msg)_a` for an `EF` message: the tensor at `a`, then `Σ_j X_j(a)·msg_j`. -/
def encAtE (ks : Array F) (ℓ : ℕ) (msg : Array EF) (a : F) : EF :=
  let t := (tensorF ks a ℓ).1
  Fin.foldl (2 ^ ℓ) (fun acc j => acc + EF.smulBase (t.getD j 0) (msg.getD j 0)) 0

theorem smulBase_eq_smul (c : F) (x : EF) : EF.smulBase c x = c • x := by
  rw [EF.smulBase_eq_mul, Algebra.smul_def, EF.algebraMap_eq_ofF]

/-- `encAtE` is the encoding of §5.1 at the column's point. -/
theorem encAtE_eq (ks : Array F) (ℓ : ℕ) {N : ℕ} (msg : Array EF) (c : Fin N) :
    encAtE ks ℓ msg (ptOf c) = enc (kapFn ks) ℓ (dom N) (fun j => msg.getD j 0) c := by
  rw [← dom_eq_ptOf, ← encAt_eq]
  simp only [encAtE, encAt, tensor, tensorF_eq, smulBase_eq_smul]

/-- `Σ_{i<m} w_i · col_i` (`col` over `F`, `w` over `EF`). -/
def comb (m : ℕ) (w : Array EF) (col : Array F) : EF :=
  Fin.foldl m (fun acc i => acc + EF.smulBase (col.getD i 0) (w.getD i 0)) 0

/-- `Σ_{i<m} w_i · Q[i] ∈ EF^k` (the prover's `ū` and `v`). -/
def combRows (m k : ℕ) (w : Array EF) (Q : Array (Array F)) : Array EF :=
  (Array.range k).map fun j => comb m w (Q.map fun row => row.getD j 0)

/-- The column of `U = (Enc(Q[i]))_i` at the point `a`: one tensor, `m` dot products. -/
def columnAt (ks : Array F) (ℓ : ℕ) (Q : Array (Array F)) (a : F) : Array F :=
  let t := (tensorF ks a ℓ).1
  Q.map fun row => Fin.foldl (2 ^ ℓ) (fun acc j => acc + t.getD j 0 * row.getD j 0) 0

theorem comb_eq (m : ℕ) (w : Array EF) (col : Array F) :
    comb m w (col) = ∑ i : Fin m, EF.ofF (col.getD i 0) * w.getD i 0 := by
  rw [comb, foldl_add_eq_sum]; simp only [EF.smulBase_eq_mul]

theorem getD_map_getD {α β : Type} (f : α → β) (xs : Array α) (d : α) {d' : β} (i : ℕ)
    (h : f d = d') :
    (xs.map f).getD i d' = f (xs.getD i d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases xs[i]? <;> simp [h]

theorem foldl_const {α : Type} (n : ℕ) (x : α) : Fin.foldl n (fun acc _ => acc) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.foldl_succ_last, ih]

/-- The honest column entry `i` is `Enc_F(Q[i])` at the column's point. -/
theorem columnAt_getD (ks : Array F) (ℓ : ℕ) (Q : Array (Array F)) {N : ℕ} (c : Fin N) (i : ℕ) :
    (columnAt ks ℓ Q (ptOf c)).getD i 0 =
      enc (kapFn ks) ℓ (dom N) (fun j => (Q.getD i #[]).getD j 0) c := by
  rw [← dom_eq_ptOf, ← encAt_eq, columnAt, getD_map_getD _ _ #[] _
    (by simp [foldl_const])]
  simp only [encAt, tensor, tensorF_eq, smul_eq_mul]

/-! ### The column check -/

/-- **The two column equations** at index `c` (§5.4): `Enc(ū)_c = Σ_i r_i U[i][c]` and
`Enc(v)_c = Σ_i a_i U[i][c]`. -/
def colCheck (κ : ℕ) (ks : Array F) (r a ubar v : Array EF) (c : ℕ) (col : Array F) : Bool :=
  decide (encAtE ks (lk κ) ubar (ptOf c) = comb (rows κ) r col) &&
    decide (encAtE ks (lk κ) v (ptOf c) = comb (rows κ) a col)

theorem colCheck_iff (κ : ℕ) (ks : Array F) (r a ubar v : Array EF) {N : ℕ} (c : Fin N)
    (col : Array F) :
    colCheck κ ks r a ubar v c col = true ↔
      enc (kapFn ks) (lk κ) (dom N) (fun j => ubar.getD j 0) c =
          ∑ i : Fin (rows κ), EF.ofF (col.getD i 0) * r.getD i 0 ∧
        enc (kapFn ks) (lk κ) (dom N) (fun j => v.getD j 0) c =
          ∑ i : Fin (rows κ), EF.ofF (col.getD i 0) * a.getD i 0 := by
  simp [colCheck, encAtE_eq, comb_eq]

/-- **Column completeness** (L-RS5 at one column): for the honest matrix, `w`'s combination of
the rows encodes to `w`'s combination of the column, for every `w`. -/
theorem enc_combRows (κ : ℕ) (ks : Array F) (w : Array EF) (Q : Array (Array F)) {N : ℕ}
    (c : Fin N) :
    encAtE ks (lk κ) (combRows (rows κ) (msgLen κ) w Q) (ptOf c) =
      comb (rows κ) w (columnAt ks (lk κ) Q (ptOf c)) := by
  rw [encAtE_eq, comb_eq]
  simp only [columnAt_getD]
  have hrow : ∀ j : Fin (2 ^ lk κ), (combRows (rows κ) (msgLen κ) w Q).getD j 0 =
      ∑ i : Fin (rows κ), EF.ofF ((Q.getD i #[]).getD j 0) * w.getD i 0 := by
    intro j
    have hj : (j : ℕ) < msgLen κ := j.2
    simp only [combRows, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
      hj, ite_true, Option.map_some, Option.getD_some, comb_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    cases Q[(i : ℕ)]? <;> simp
  simp only [enc, hrow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← EF.algebraMap_eq_ofF, map_sum, map_mul, Algebra.algebraMap_self, RingHom.id_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The honest prover's columns pass both column equations. -/
theorem colCheck_honest (κ : ℕ) (ks : Array F) (r a : Array EF) (Q : Array (Array F)) {N : ℕ}
    (c : Fin N) :
    colCheck κ ks r a (combRows (rows κ) (msgLen κ) r Q) (combRows (rows κ) (msgLen κ) a Q) c
      (columnAt ks (lk κ) Q (ptOf c)) = true := by
  simp [colCheck, enc_combRows]

/-! ### Bytes (§7) -/

/-- `EF` elements, 24 bytes each, in order. -/
def efBytes (xs : Array EF) : ByteArray :=
  xs.foldl (fun acc x => acc ++ bytesOf x.toBytes) ByteArray.empty

/-- `F` elements, 8 bytes each, in order. -/
def fBytes (xs : Array F) : ByteArray :=
  xs.foldl (fun acc x => acc ++ bytesOf x.toBytes) ByteArray.empty

/-- Labels, 31 bytes each, in order. -/
def labelsBytes (ls : List Label) : ByteArray :=
  ls.foldl (fun acc l => acc ++ bytesOf l) ByteArray.empty

/-- The `EF` element at byte offset `o`. -/
def readEF (b : ByteArray) (o : ℕ) : EF := EF.ofBytes (Vector.ofFn fun i : Fin 24 => b[o + i]!)

/-- `cnt` `EF` elements from byte offset `o`. -/
def readEFs (b : ByteArray) (o cnt : ℕ) : Array EF :=
  (Array.range cnt).map fun j => readEF b (o + 24 * j)

/-- The `F` element at byte offset `o`. -/
def readF (b : ByteArray) (o : ℕ) : F := F.ofBytes (Vector.ofFn fun i : Fin 8 => b[o + i]!)

/-- `cnt` `F` elements from byte offset `o`. -/
def readFs (b : ByteArray) (o cnt : ℕ) : Array F :=
  (Array.range cnt).map fun j => readF b (o + 8 * j)

/-- The label at byte offset `o`. -/
def readLabel (b : ByteArray) (o : ℕ) : Label := Vector.ofFn fun i : Fin 31 => b[o + i]!

/-! ### Sizes -/

/-- Bytes of one opening: the column (`8m`) and the path (`31ℓ_N`). -/
def openW (κ : ℕ) : ℕ := 8 * rows κ + 31 * lN κ

/-- Fields 1–2 of §7: `root`, `ū`. -/
def size1 (κ : ℕ) : ℕ := 31 + 24 * msgLen κ

/-- Fields 8–9 of §7: `v` and the `t` openings. -/
def size2 (κ : ℕ) : ℕ := 24 * msgLen κ + tQ * openW κ

/-- §7's table: the openings take `113 360` bytes at `n = 16` and `84 760` at `n = 1`. -/
theorem size_table : tQ * openW 4 = 113360 ∧ tQ * openW 0 = 84760 ∧ size1 4 = 12319 := by
  decide

/-! ### Verifier -/

/-- Steps 2–3: absorb the root (kind `0x01`), squeeze `r_0 … r_{m−1}`. -/
def rootAndCoeffs (st : Digest) (m : ℕ) (rootB : ByteArray) : OProg (Digest × List EF) := do
  let st ← absorb st 0x01 rootB
  squeezeE st m

/-- **Verifier, steps 2–4**: returns the state after `absorb(ū)` (kind `0x02`) and `r`. -/
def verify1 (κ : ℕ) (st : Digest) (rootB ubarB : ByteArray) : OProg (Digest × List EF) := do
  let p ← rootAndCoeffs st (rows κ) rootB
  let st ← absorb p.1 0x02 ubarB
  pure (st, p.2)

/-- The path of the opening at byte offset `o`. -/
def readPath (κ : ℕ) (b : ByteArray) (o : ℕ) : List Label :=
  (List.range (lN κ)).map fun l => readLabel b (o + 8 * rows κ + 31 * l)

/-- The column bytes of the opening at byte offset `o`. -/
def readCol (κ : ℕ) (b : ByteArray) (o : ℕ) : ByteArray :=
  ⟨Array.ofFn fun i : Fin (8 * rows κ) => b[o + i]!⟩

/-- One opening: the Merkle path of column `c` against `root`, then the column equations. -/
def openOne (κ : ℕ) (ks : Array F) (root : Label) (r a ubar v : Array EF) (b : ByteArray)
    (o c : ℕ) : OProg Bool := do
  let colB := readCol κ b o
  let ok ← Merkle.verify root c colB (readPath κ b o)
  pure (ok && colCheck κ ks r a ubar v c (readFs colB 0 (rows κ)))

/-- **Verifier, steps 11–13**: absorb `v` (kind `0x08`), squeeze the `t` indices, check every
opening (`opens` holds the `t` openings in index order, `openW κ` bytes each). -/
def verify2 (κ : ℕ) (st : Digest) (root : Label) (r a ubar : Array EF) (vB opens : ByteArray) :
    OProg Bool := do
  let st ← absorb st 0x08 vB
  let p ← squeezeIdx st (lN κ) tQ
  let v := readEFs vB 0 (msgLen κ)
  let ks := kapArr (lk κ)
  let oks ← (List.range tQ).mapM fun j =>
    openOne κ ks root r a ubar v opens (j * openW κ) (p.2.getD j 0)
  pure (oks.all id)

/-- **What `verify2` accepting means**, under any oracle: with `idx` the squeezed indices, every
opening's path verifies and both column equations hold. -/
theorem run_verify2 (H : ByteArray → Digest) (κ : ℕ) (st : Digest) (root : Label)
    (r a ubar : Array EF) (vB opens : ByteArray) :
    (verify2 κ st root r a ubar vB opens).run H = true ↔
      ∀ j < tQ,
        (Merkle.verify root
            ((((squeezeIdx ((absorb st 0x08 vB).run H) (lN κ) tQ).run H).2).getD j 0)
            (readCol κ opens (j * openW κ)) (readPath κ opens (j * openW κ))).run H = true ∧
          colCheck κ (kapArr (lk κ)) r a ubar (readEFs vB 0 (msgLen κ))
            ((((squeezeIdx ((absorb st 0x08 vB).run H) (lN κ) tQ).run H).2).getD j 0)
            (readFs (readCol κ opens (j * openW κ)) 0 (rows κ)) = true := by
  simp [verify2, openOne, List.all_eq_true]

/-! ### Prover -/

/-- The packed witness as `m` rows of `k` (`q(j + k i) = Q[i][j]`, §5.2). -/
def matrixRows (κ : ℕ) (q : Array F) : Array (Array F) :=
  (Array.range (rows κ)).map fun i => q.extract (i * msgLen κ) ((i + 1) * msgLen κ)

/-- The prover's commitment. -/
structure Commitment where
  /-- The message rows `Q[i]`. -/
  Q : Array (Array F)
  /-- The columns of `U`, `m` entries each. -/
  colsF : Array (Array F)
  /-- The column bytes (the Merkle leaves). -/
  colsB : Array ByteArray
  /-- The Merkle levels, leaves first. -/
  levels : Array (Array Label)

/-- **Commit** (§5.3): encode the rows (column by column), hash the columns into the tree. -/
def commit (κ : ℕ) (q : Array F) : OProg Commitment := do
  let Q := matrixRows κ q
  let ks := kapArr (lk κ)
  let cs := (Array.range (cols κ)).map fun c => columnAt ks (lk κ) Q (ptOf c)
  let cb := cs.map fBytes
  let lv ← Merkle.build cb (lN κ)
  pure ⟨Q, cs, cb, lv⟩

/-- The root of a commitment. -/
def Commitment.root (cm : Commitment) (κ : ℕ) : Label := Merkle.root cm.levels (lN κ)

/-- **Prover, steps 2–4**: the state, `r`, and the bytes of fields 1–2 (`root`, `ū`). -/
def prove1 (κ : ℕ) (st : Digest) (cm : Commitment) :
    OProg (Digest × List EF × ByteArray × ByteArray) := do
  let rootB := bytesOf (cm.root κ)
  let p ← rootAndCoeffs st (rows κ) rootB
  let ubarB := efBytes (combRows (rows κ) (msgLen κ) p.2.toArray cm.Q)
  let st ← absorb p.1 0x02 ubarB
  pure (st, p.2, rootB, ubarB)

/-- The bytes of the opening of column `c`: the column, then its path. -/
def openingBytes (κ : ℕ) (cm : Commitment) (c : ℕ) : ByteArray :=
  cm.colsB[c]! ++ labelsBytes (Merkle.path cm.levels (lN κ) c)

/-- **Prover, steps 11–13**: the bytes of fields 8–9 (`v`, then the openings in index order),
for the row weights `a`. -/
def prove2 (κ : ℕ) (st : Digest) (cm : Commitment) (a : Array EF) :
    OProg (ByteArray × ByteArray) := do
  let vB := efBytes (combRows (rows κ) (msgLen κ) a cm.Q)
  let st ← absorb st 0x08 vB
  let p ← squeezeIdx st (lN κ) tQ
  let opens := ((List.range tQ).map fun j => p.2.getD j 0).foldl
    (fun acc c => acc ++ openingBytes κ cm c) ByteArray.empty
  pure (vB, opens)

/-- Steps 2–4 are the same transcript for the prover and the verifier. -/
theorem prove1_verify1 (H : ByteArray → Digest) (κ : ℕ) (st : Digest) (cm : Commitment) :
    let p := (prove1 κ st cm).run H
    (verify1 κ st p.2.2.1 p.2.2.2).run H = (p.1, p.2.1) := by
  simp [prove1, verify1]

/-! ### Reading back what the prover wrote -/

theorem getElem!_ba (b : ByteArray) (i : ℕ) : b[i]! = b.data.toList.getD i 0 := by
  by_cases h : i < b.size
  · rw [getElem!_pos b i h, List.getD_eq_getElem _ _ (by simpa using h)]
    rfl
  · rw [getElem!_neg b i h, List.getD_eq_default _ _ (by simp; omega)]; rfl

theorem foldl_data {α : Type} (g : α → ByteArray) (xs : List α) (init : ByteArray) :
    (xs.foldl (fun acc x => acc ++ g x) init).data.toList =
      init.data.toList ++ xs.flatMap fun x => (g x).data.toList := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih => simp [ih, ByteArray.data_append]

/-- Byte `w j + i` of a concatenation of `w`-byte chunks is byte `i` of chunk `j`. -/
theorem chunk_getD {α : Type} (f : α → List UInt8) (w : ℕ) (xs : List α)
    (hf : ∀ x ∈ xs, (f x).length = w) (j i : ℕ) (hj : j < xs.length) (hi : i < w) :
    (xs.flatMap f).getD (w * j + i) 0 = (f xs[j]).getD i 0 := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    have hx := hf x (by simp)
    cases j with
    | zero =>
      simp only [List.flatMap_cons, List.getElem_cons_zero, Nat.mul_zero, Nat.zero_add]
      exact List.getD_append _ _ _ _ (by rw [hx]; omega)
    | succ j =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by rw [hx]; nlinarith), hx]
      rw [show w * (j + 1) + i - w = w * j + i by rw [Nat.mul_succ]; omega]
      exact ih (fun y hy => hf y (by simp [hy])) j (by simpa using hj)

theorem bytesOf_getD {n : ℕ} (v : Vector UInt8 n) {i : ℕ} (hi : i < n) :
    (bytesOf v).data.toList.getD i 0 = v[i] := by
  simp [bytesOf, List.getD_eq_getElem?_getD, hi]

theorem foldl_data_empty {α : Type} (g : α → ByteArray) (xs : List α) :
    (xs.foldl (fun acc x => acc ++ g x) ByteArray.empty).data.toList =
      xs.flatMap fun x => (g x).data.toList := by
  rw [foldl_data]; rfl

theorem efBytes_data (xs : Array EF) :
    (efBytes xs).data.toList = xs.toList.flatMap fun x => (bytesOf x.toBytes).data.toList := by
  rw [efBytes, ← Array.foldl_toList, foldl_data_empty]

theorem fBytes_data (xs : Array F) :
    (fBytes xs).data.toList = xs.toList.flatMap fun x => (bytesOf x.toBytes).data.toList := by
  rw [fBytes, ← Array.foldl_toList, foldl_data_empty]

theorem readEF_efBytes (xs : Array EF) {j : ℕ} (hj : j < xs.size) :
    readEF (efBytes xs) (24 * j) = xs[j] := by
  have hv : (Vector.ofFn fun i : Fin 24 => (efBytes xs)[24 * j + i]!) = xs[j].toBytes := by
    refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_ofFn, getElem!_ba, efBytes_data,
      chunk_getD (fun x : EF => (bytesOf x.toBytes).data.toList) 24 xs.toList
        (fun x _ => by simp) j i (by simpa using hj) hi, bytesOf_getD _ hi, Array.getElem_toList]
  rw [readEF, hv, EF.ofBytes_toBytes]

theorem readEFs_getElem (b : ByteArray) (o cnt j : ℕ) (h : j < (readEFs b o cnt).size) :
    (readEFs b o cnt)[j] = readEF b (o + 24 * j) := by
  simp only [readEFs, Array.getElem_map, Array.getElem_range]

theorem readEFs_efBytes (xs : Array EF) : readEFs (efBytes xs) 0 xs.size = xs := by
  apply Array.ext
  · simp only [readEFs, Array.size_map, Array.size_range]
  · intro j _ h2
    rw [readEFs_getElem, Nat.zero_add]
    exact readEF_efBytes xs h2

theorem readF_fBytes (xs : Array F) {j : ℕ} (hj : j < xs.size) :
    readF (fBytes xs) (8 * j) = xs[j] := by
  have hv : (Vector.ofFn fun i : Fin 8 => (fBytes xs)[8 * j + i]!) = xs[j].toBytes := by
    refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_ofFn, getElem!_ba, fBytes_data,
      chunk_getD (fun x : F => (bytesOf x.toBytes).data.toList) 8 xs.toList
        (fun x _ => by simp) j i (by simpa using hj) hi, bytesOf_getD _ hi, Array.getElem_toList]
  rw [readF, hv, F.ofBytes_toBytes]

theorem readFs_getElem (b : ByteArray) (o cnt j : ℕ) (h : j < (readFs b o cnt).size) :
    (readFs b o cnt)[j] = readF b (o + 8 * j) := by
  simp only [readFs, Array.getElem_map, Array.getElem_range]

theorem readFs_fBytes (xs : Array F) : readFs (fBytes xs) 0 xs.size = xs := by
  apply Array.ext
  · simp only [readFs, Array.size_map, Array.size_range]
  · intro j _ h2
    rw [readFs_getElem, Nat.zero_add]
    exact readF_fBytes xs h2

theorem length_flatMap_const {α : Type} (f : α → List UInt8) (w : ℕ) (xs : List α)
    (hf : ∀ x ∈ xs, (f x).length = w) : (xs.flatMap f).length = w * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, hf x (by simp),
      ih fun y hy => hf y (by simp [hy]), List.length_cons]; ring

theorem size_fBytes (xs : Array F) : (fBytes xs).size = 8 * xs.size := by
  rw [ByteArray.size, ← Array.length_toList, fBytes_data,
    length_flatMap_const _ 8 _ fun x _ => by simp, Array.length_toList]

theorem labelsBytes_data (ls : List Label) :
    (labelsBytes ls).data.toList = ls.flatMap fun l => (bytesOf l).data.toList := by
  rw [labelsBytes, foldl_data_empty]

theorem length_labelsBytes (ls : List Label) : (labelsBytes ls).data.toList.length = 31 * ls.length := by
  rw [labelsBytes_data, length_flatMap_const _ 31 _ fun x _ => by simp]

/-- The opening `j` of the prover's openings is the opening of index `cs[j]`. -/
theorem openings_getD (κ : ℕ) (cm : Commitment) (cs : List ℕ)
    (hw : ∀ c ∈ cs, (openingBytes κ cm c).data.toList.length = openW κ) {j i : ℕ}
    (hj : j < cs.length) (hi : i < openW κ) :
    (cs.foldl (fun acc c => acc ++ openingBytes κ cm c) ByteArray.empty)[j * openW κ + i]! =
      (openingBytes κ cm cs[j]).data.toList.getD i 0 := by
  rw [getElem!_ba, foldl_data_empty, mul_comm, chunk_getD _ _ cs hw j i hj hi]

theorem readCol_openings (κ : ℕ) (cm : Commitment) (cs : List ℕ)
    (hw : ∀ c ∈ cs, (openingBytes κ cm c).data.toList.length = openW κ) {j : ℕ}
    (hj : j < cs.length) (hcol : cm.colsB[cs[j]]!.size = 8 * rows κ) :
    readCol κ (cs.foldl (fun acc c => acc ++ openingBytes κ cm c) ByteArray.empty)
      (j * openW κ) = cm.colsB[cs[j]]! := by
  apply ByteArray.ext_toList
  apply List.ext_getElem
  · simp [readCol, hcol]
  · intro i h1 h2
    simp only [readCol, Array.toList_ofFn, List.getElem_ofFn]
    rw [openings_getD κ cm cs hw hj (by simp [readCol] at h1; unfold openW; omega),
      openingBytes, ByteArray.data_append, Array.toList_append,
      List.getD_append _ _ _ _ (by simpa using h2), List.getD_eq_getElem _ _ h2]

theorem readPath_openings (κ : ℕ) (cm : Commitment) (cs : List ℕ)
    (hw : ∀ c ∈ cs, (openingBytes κ cm c).data.toList.length = openW κ) {j : ℕ}
    (hj : j < cs.length) (hcol : cm.colsB[cs[j]]!.size = 8 * rows κ)
    (hp : (Merkle.path cm.levels (lN κ) cs[j]).length = lN κ) :
    readPath κ (cs.foldl (fun acc c => acc ++ openingBytes κ cm c) ByteArray.empty)
      (j * openW κ) = Merkle.path cm.levels (lN κ) cs[j] := by
  apply List.ext_getElem
  · simp [readPath, hp]
  · intro l h1 h2
    simp only [readPath, List.getElem_map, List.getElem_range]
    ext i hi
    rw [readLabel, Vector.getElem_ofFn, show j * openW κ + 8 * rows κ + 31 * l + i =
      j * openW κ + (8 * rows κ + (31 * l + i)) by ring,
      openings_getD κ cm cs hw hj (by simp [readPath] at h1; unfold openW; nlinarith),
      openingBytes, ByteArray.data_append, Array.toList_append,
      List.getD_append_right _ _ _ _ (by simp [hcol]), Array.length_toList,
      show cm.colsB[cs[j]]!.data.size = 8 * rows κ from hcol, Nat.add_sub_cancel_left,
      labelsBytes_data, chunk_getD _ 31 _ (fun x _ => by simp) l i h2 hi, bytesOf_getD _ hi]

theorem indices_getD_lt (ℓ t : ℕ) (ans : List Digest) (j : ℕ) :
    (indices ℓ t ans).getD j 0 < 2 ^ ℓ := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (indices ℓ t ans)[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
    simp [indices, idxOf, Nat.mod_lt]

theorem run_commit (H : ByteArray → Digest) (κ : ℕ) (q : Array F) :
    (commit κ q).run H =
      let Q := matrixRows κ q
      let cs := (Array.range (cols κ)).map fun c => columnAt (kapArr (lk κ)) (lk κ) Q (ptOf c)
      ⟨Q, cs, cs.map fBytes, (Merkle.build (cs.map fBytes) (lN κ)).run H⟩ := by
  simp [commit]

/-- **Steps 11–13 are complete**: for every oracle, every packed witness, every `r` and every
row weights `a`, the verifier accepts the honest prover's `v` and openings, with the honest
`ū = Σ r_i Q[i]`. -/
theorem verify2_complete (H : ByteArray → Digest) (κ : ℕ) (st : Digest) (q : Array F)
    (r a : Array EF) :
    let cm := (commit κ q).run H
    let out := (prove2 κ st cm a).run H
    (verify2 κ st (cm.root κ) r a (combRows (rows κ) (msgLen κ) r cm.Q) out.1 out.2).run H =
      true := by
  intro cm out
  rw [run_verify2]
  intro j hj
  set idx := ((squeezeIdx ((absorb st 0x08 out.1).run H) (lN κ) tQ).run H).2 with hidx
  set cs := (List.range tQ).map fun j => idx.getD j 0 with hcs
  have hout : out = (efBytes (combRows (rows κ) (msgLen κ) a cm.Q),
      cs.foldl (fun acc c => acc ++ openingBytes κ cm c) ByteArray.empty) := by
    simp [out, prove2, hcs, hidx]
  have hlen : cs.length = tQ := by simp [hcs]
  have hcsj : cs[j]'(by omega) = idx.getD j 0 := by simp [hcs]
  have hlt : ∀ c ∈ cs, c < cols κ := by
    intro c hc
    simp only [hcs, List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    simp only [hidx, squeezeIdx, OProg.run_bind, OProg.run_pure]
    exact indices_getD_lt _ _ _ _
  have hQ : cm.Q.size = rows κ := by simp [cm, run_commit, matrixRows]
  have hcolF : ∀ c < cols κ, cm.colsF[c]! = columnAt (kapArr (lk κ)) (lk κ) cm.Q (ptOf c) := by
    intro c hc; simp [cm, run_commit, getElem!_pos, hc]
  have hcolB : ∀ c < cols κ, cm.colsB[c]! = fBytes cm.colsF[c]! := by
    intro c hc; simp [cm, run_commit, getElem!_pos, hc]
  have hsizeB : ∀ c < cols κ, cm.colsB[c]!.size = 8 * rows κ := by
    intro c hc; rw [hcolB c hc, size_fBytes, hcolF c hc]; simp [columnAt, hQ]
  have hlevels : cm.levels = (Merkle.build cm.colsB (lN κ)).run H := by simp [cm, run_commit]
  have hBsize : cm.colsB.size = 2 ^ lN κ := by simp [cm, run_commit, cols]
  have hplen : ∀ c, (Merkle.path cm.levels (lN κ) c).length = lN κ := by simp [Merkle.path]
  have hw : ∀ c ∈ cs, (openingBytes κ cm c).data.toList.length = openW κ := by
    intro c hc
    rw [openingBytes, ByteArray.data_append, Array.toList_append, List.length_append,
      length_labelsBytes, hplen, Array.length_toList, ← ByteArray.size, hsizeB c (hlt c hc)]
    rfl
  have hcj := hlt _ (List.getElem_mem (l := cs) (by omega : j < cs.length))
  rw [hcsj] at hcj
  rw [hout]
  simp only
  rw [← hcsj, readCol_openings κ cm cs hw (by omega) (by rw [hcsj]; exact hsizeB _ hcj),
    readPath_openings κ cm cs hw (by omega) (by rw [hcsj]; exact hsizeB _ hcj) (hplen _), hcsj]
  constructor
  · have := Merkle.path_complete H hBsize hcj
    rw [← hlevels] at this
    rwa [getElem!_pos cm.colsB _ (by rw [hBsize]; exact hcj)]
  · have hv : readEFs (efBytes (combRows (rows κ) (msgLen κ) a cm.Q)) 0 (msgLen κ) =
        combRows (rows κ) (msgLen κ) a cm.Q := by
      have hs : (combRows (rows κ) (msgLen κ) a cm.Q).size = msgLen κ := by
        simp only [combRows, Array.size_map, Array.size_range]
      calc _ = readEFs (efBytes (combRows (rows κ) (msgLen κ) a cm.Q)) 0
            (combRows (rows κ) (msgLen κ) a cm.Q).size := by rw [hs]
        _ = _ := readEFs_efBytes _
    have hc : readFs cm.colsB[idx.getD j 0]! 0 (rows κ) =
        columnAt (kapArr (lk κ)) (lk κ) cm.Q (ptOf (idx.getD j 0)) := by
      have hs : cm.colsF[idx.getD j 0]!.size = rows κ := by
        rw [hcolF _ hcj]; simp only [columnAt, Array.size_map, hQ]
      rw [hcolB _ hcj, ← hcolF _ hcj]
      calc _ = readFs (fBytes cm.colsF[idx.getD j 0]!) 0 cm.colsF[idx.getD j 0]!.size := by
            rw [hs]
        _ = _ := readFs_fBytes _
    rw [hv, hc]
    exact colCheck_honest κ _ r a cm.Q (N := cols κ) ⟨_, hcj⟩

end SpartanChain.Ligero
