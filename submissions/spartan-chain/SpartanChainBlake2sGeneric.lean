import SpartanChainBlake2sCompress

/-!
# The compression gadgets over an abstract form type, and their simulation of the bitset gadgets

BLUEPRINT-R1 §2.4.2. The word gadgets of `SpartanChainBlake2sWords.lean` and the compression of
`SpartanChainBlake2sCompress.lean` build linear forms as bitsets: XOR is `^^^` on `BitVec 2^14`,
and a product gate records its two forms. A verifier never builds the forms (the chain block's
matrices have about `8.9·10^7` nonzeros); it runs the same program on *values* of the forms.
This file writes the gadget program once more over an abstract interpretation `GOps m α S`:

* `zero`, `xor`, `var`: the linear operations on `α`;
* `mul a b` at position `k`: returns `res k a b` and updates an accumulator `upd s k a b : S`.

Each generic gadget is the bitset gadget with `0`, `^^^`, `Form.var` and `mul` replaced by these,
statement for statement (same gates, same order, same positions). The **simulation theorem**
`sim_compressW` relates the two programs: for a map `φ : Form m → α` that sends `0` to `zero` and
`^^^` to `xor`, run from related states, if every gate `(k, a, b)` the bitset program records
satisfies `res k (φ a) (φ b) = φ (var k)` (a property of the interpretation, `GHyp`), then the
generic program returns `φ` of the bitset program's forms and its accumulator is the fold of `upd`
over the recorded gates. Two interpretations use it (`SpartanChainBlake2sWalk.lean`):

* the **walk** (`α = R`, `φ L = Σ_j L_j · wt_j`): `walk_eq_sum`, the verifier's `A0̃`, `B0̃`;
* the **evaluation** (`α = Bool`, `φ L = L.eval z`): the prover's fast witness generation.

Nothing here transcribes a source; the generic gadgets mirror the copied leanerVM gadgets.
-/

namespace SpartanChain

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-- An interpretation of the gadget language on positions `Pos m`: linear operations on `α`, and
the product gate at position `k` returning `res k a b` and updating the accumulator with
`upd s k a b`. -/
structure GOps (m : ℕ) (α S : Type) where
  /-- The zero form. -/
  zero : α
  /-- The sum (XOR) of two forms. -/
  xor : α → α → α
  /-- The form of one input position. -/
  var : Pos m → α
  /-- The value of the product gate at position `k` with forms `a`, `b`. -/
  res : Pos m → α → α → α
  /-- The accumulator after the product gate at position `k` with forms `a`, `b`. -/
  upd : S → Pos m → α → α → S

/-- The state of a generic run: the next gate position and the accumulator. -/
structure GState (S : Type) where
  /-- The next gate position. -/
  next : ℕ
  /-- The accumulator. -/
  acc : S

/-- A generic gadget program. -/
abbrev GB (S : Type) := StateM (GState S)

namespace GOps

variable {m : ℕ} {α S : Type} (o : GOps m α S)

/-- The product gate at the next position. -/
def mul (a b : α) : GB S α :=
  modifyGet fun s ↦ (o.res (pos s.next) a b, ⟨s.next + 1, o.upd s.acc (pos s.next) a b⟩)

/-- `xorW`. -/
def xorW (x y : Vector α 32) : Vector α 32 := Vector.ofFn fun i ↦ o.xor x[i] y[i]

/-- `rotrW`. -/
def rotrW (w : Vector α 32) (n : ℕ) : Vector α 32 :=
  Vector.ofFn fun i ↦ w[(i.val + n) % 32]'(Nat.mod_lt _ (by decide))

/-- `litW`. -/
def litW (cpos : Pos m) (c : UInt32) : Vector α 32 :=
  Vector.ofFn fun i ↦ if c.toNat.testBit i then o.var cpos else o.zero

/-- `inW`. -/
def inW (b : ℕ) : Vector α 32 := Vector.ofFn fun i ↦ o.var (pos (b + i))

/-- `addCarries`. -/
def addCarries (x y : Vector α 32) : (n : ℕ) → α → GB S (List α)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← o.mul (o.xor (x[i]'(by omega)) c) (o.xor (y[i]'(by omega)) c)
    let rest ← addCarries x y n (o.xor c g)
    pure (c :: rest)

/-- `sumW`. -/
def sumW (p q : Vector α 32) (cs : List α) : Vector α 32 :=
  Vector.ofFn fun i ↦ o.xor (o.xor p[i] q[i]) (cs.getD i o.zero)

/-- `addW`. -/
def addW (x y : Vector α 32) : GB S (Vector α 32) := o.sumW x y <$> o.addCarries x y 31 o.zero

/-- `majorities`. -/
def majorities (x y z : Vector α 32) : (n : ℕ) → GB S (List α)
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← o.mul (o.xor (x[i]'(by omega)) (z[i]'(by omega)))
      (o.xor (y[i]'(by omega)) (z[i]'(by omega)))
    let rest ← majorities x y z n
    pure (o.xor g (z[i]'(by omega)) :: rest)

/-- `rippleCarries`. -/
def rippleCarries (p q : Vector α 32) : (n : ℕ) → α → GB S (List α)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← o.mul (o.xor (p[i]'(by omega)) c) (o.xor (q[i]'(by omega)) c)
      let rest ← rippleCarries p q n (o.xor c g)
      pure (c :: rest)
    else
      let rest ← rippleCarries p q n c
      pure (c :: rest)

/-- `xor3W`. -/
def xor3W (x y z : Vector α 32) : Vector α 32 :=
  Vector.ofFn fun i ↦ o.xor (o.xor x[i] y[i]) z[i]

/-- `shiftW`. -/
def shiftW (ms : List α) : Vector α 32 :=
  Vector.ofFn fun i ↦ if i.val = 0 then o.zero else ms.getD (i.val - 1) o.zero

/-- `add3W`. -/
def add3W (x y z : Vector α 32) : GB S (Vector α 32) :=
  o.majorities x y z 31 >>= fun ms ↦
    o.sumW (o.xor3W x y z) (o.shiftW ms) <$> o.rippleCarries (o.xor3W x y z) (o.shiftW ms) 31 o.zero

/-- `gW`. -/
def gW (v : Vector (Vector α 32) 16) (a b c d : Fin 16) (mx my : Vector α 32) :
    GB S (Vector (Vector α 32) 16) := do
  let a1 ← o.add3W v[a] v[b] mx
  let d1 := GOps.rotrW (o.xorW v[d] a1) 16
  let c1 ← o.addW v[c] d1
  let b1 := GOps.rotrW (o.xorW v[b] c1) 12
  let a2 ← o.add3W a1 b1 my
  let d2 := GOps.rotrW (o.xorW d1 a2) 8
  let c2 ← o.addW c1 d2
  let b2 := GOps.rotrW (o.xorW b1 c2) 7
  pure ((((v.set a a2).set b b2).set c c2).set d d2)

/-- `roundW`. -/
def roundW (v m' : Vector (Vector α 32) 16) (s : Vector (Fin 16) 16) :
    GB S (Vector (Vector α 32) 16) := do
  let v ← o.gW v 0 4 8 12 m'[s[0]] m'[s[1]]
  let v ← o.gW v 1 5 9 13 m'[s[2]] m'[s[3]]
  let v ← o.gW v 2 6 10 14 m'[s[4]] m'[s[5]]
  let v ← o.gW v 3 7 11 15 m'[s[6]] m'[s[7]]
  let v ← o.gW v 0 5 10 15 m'[s[8]] m'[s[9]]
  let v ← o.gW v 1 6 11 12 m'[s[10]] m'[s[11]]
  let v ← o.gW v 2 7 8 13 m'[s[12]] m'[s[13]]
  o.gW v 3 4 9 14 m'[s[14]] m'[s[15]]

end GOps

namespace GOps

variable {α S : Type} (o : GOps Blake2sCircuit.m α S)

/-- `initW`. -/
def initW : Vector (Vector α 32) 16 :=
  Vector.ofFn fun w : Fin 16 ↦
    if w.val < 8 then o.inW (32 * w)
    else if w.val < 12 then o.litW constPos iv[w.val - 8]
    else o.xorW (o.litW constPos iv[w.val - 8]) (o.inW (counterLo + 32 * (w.val - 12)))

/-- `compressW`. -/
def compressW : GB S (Vector (Vector α 32) 8) := do
  let msg : Vector (Vector α 32) 16 := Vector.ofFn fun w ↦ o.inW (msgBase + 32 * w)
  let v ← sigma.foldlM (fun v s ↦ o.roundW v msg s) o.initW
  pure (Vector.ofFn fun w : Fin 8 ↦ o.xorW (o.xorW v[w] v[w.val + 8]) (o.inW (32 * w)))

end GOps

/-! ## The simulation -/

namespace Generic

variable {m : ℕ} {α S : Type} (o : GOps m α S) (φ : Form m → α)

/-- `φ` is linear: it sends `0` to `zero` and `^^^` to `xor`. -/
structure Linear : Prop where
  zero : φ 0 = o.zero
  xor : ∀ a b, φ (a ^^^ b) = o.xor (φ a) (φ b)

/-- Every recorded gate `(k, a, b)` satisfies `res k (φ a) (φ b) = φ (var k)`. -/
def GHyp (σ : BuildState m) : Prop :=
  ∀ kg ∈ σ.gates, o.res kg.1 (φ kg.2.a) (φ kg.2.b) = φ (Form.var kg.1)

/-- The accumulator `upd` folded over a gate list. -/
def accOf (s₀ : S) (L : List (Pos m × Gate m)) : S :=
  L.foldl (fun s kg ↦ o.upd s kg.1 (φ kg.2.a) (φ kg.2.b)) s₀

/-- Related states: the same next position, and the generic accumulator is the fold of `upd` from
`s₀` over the bitset state's gates. -/
def SR (s₀ : S) (σ : BuildState m) (g : GState S) : Prop :=
  g.next = σ.next ∧ g.acc = accOf o φ s₀ σ.gates.toList

/-- The generic program `mg` simulates the bitset program `mb` with result relation `R`: from
related states, if every gate of the bitset run satisfies `GHyp`, the final states are related
and so are the results. -/
def Sim (s₀ : S) {β γ : Type} (mb : Builder m β) (mg : GB S γ) (R : β → γ → Prop) : Prop :=
  ∀ σ g, SR o φ s₀ σ g → GHyp o φ (mb.run σ).2 → SR o φ s₀ (mb.run σ).2 (mg.run g).2 ∧
    R (mb.run σ).1 (mg.run g).1

variable {o φ} {s₀ : S}

theorem sim_pure {β γ : Type} {b : β} {c : γ} {R : β → γ → Prop} (h : R b c) :
    Sim o φ s₀ (pure b) (pure c) R := fun _ _ hs _ ↦ ⟨hs, h⟩

theorem sim_bind {β γ β' γ' : Type} {mb : Builder m β} {mg : GB S γ} {R : β → γ → Prop}
    {f : β → Builder m β'} {h : γ → GB S γ'} {Q : β' → γ' → Prop} (hm : Sim o φ s₀ mb mg R)
    (hg : ∀ b, Grows (f b)) (hf : ∀ b c, R b c → Sim o φ s₀ (f b) (h c) Q) :
    Sim o φ s₀ (mb >>= f) (mg >>= h) Q := by
  intro σ g hs hh
  rw [StateT.run_bind] at hh ⊢
  rw [StateT.run_bind]
  obtain ⟨hs1, hr1⟩ := hm σ g hs fun kg hkg ↦ hh kg (hg _ _ kg hkg)
  exact hf _ _ hr1 _ _ hs1 hh

theorem sim_map {β γ β' γ' : Type} {mb : Builder m β} {mg : GB S γ} {R : β → γ → Prop}
    {f : β → β'} {h : γ → γ'} {Q : β' → γ' → Prop} (hm : Sim o φ s₀ mb mg R)
    (hf : ∀ b c, R b c → Q (f b) (h c)) : Sim o φ s₀ (f <$> mb) (h <$> mg) Q := by
  intro σ g hs hh
  rw [run_map'] at hh ⊢
  have : (h <$> mg).run g = (h (mg.run g).1, (mg.run g).2) := rfl
  rw [this]
  obtain ⟨hs1, hr1⟩ := hm σ g hs hh
  exact ⟨hs1, hf _ _ hr1⟩

theorem sim_mul {a b : Form m} {va vb : α} (ha : va = φ a) (hb : vb = φ b) :
    Sim o φ s₀ (mul a b) (o.mul va vb) (fun L v ↦ v = φ L) := by
  intro σ g hs hh
  rw [run_mul] at hh ⊢
  have hgate := hh _ (Array.mem_push_self ..)
  have hrun : (o.mul va vb).run g =
      (o.res (pos g.next) va vb, ⟨g.next + 1, o.upd g.acc (pos g.next) va vb⟩) := rfl
  rw [hrun, hs.1]
  refine ⟨⟨by simp [hs.1], ?_⟩, ?_⟩
  · simp only [accOf, Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hs.2, ha, hb]; rfl
  · rw [ha, hb]; exact hgate

/-! ## Words -/

/-- A generic word holds the images of a bitset word. -/
def WR (φ : Form m → α) (x : Word m) (y : Vector α 32) : Prop := ∀ i : Fin 32, y[i] = φ x[i]

/-- A generic list holds the images of a bitset list. -/
def LR (φ : Form m → α) (x : List (Form m)) (y : List α) : Prop := y = x.map φ

variable (hφ : Linear o φ)
include hφ

theorem wr_xorW {x y : Word m} {x' y' : Vector α 32} (hx : WR φ x x') (hy : WR φ y y') :
    WR φ (xorW x y) (o.xorW x' y') := fun i ↦ by
  simp only [xorW, GOps.xorW, Fin.getElem_fin, Vector.getElem_ofFn, hφ.xor]
  rw [← Fin.getElem_fin, hx i, ← Fin.getElem_fin, hy i]; rfl

omit hφ in
theorem wr_rotrW {x : Word m} {x' : Vector α 32} (hx : WR φ x x') (n : ℕ) :
    WR φ (rotrW x n) (GOps.rotrW x' n) := fun i ↦ by
  simp only [rotrW, GOps.rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact hx ⟨_, Nat.mod_lt _ (by decide)⟩

theorem getD_lr {x : List (Form m)} {y : List α} (h : LR φ x y) (i : ℕ) :
    y.getD i o.zero = φ (x.getD i 0) := by
  rw [h, ← hφ.zero, List.getD_map]

theorem wr_sumW {p q : Word m} {p' q' : Vector α 32} {cs : List (Form m)} {cs' : List α}
    (hp : WR φ p p') (hq : WR φ q q') (hc : LR φ cs cs') :
    WR φ (sumW p q cs) (o.sumW p' q' cs') := fun i ↦ by
  simp only [sumW, GOps.sumW, Fin.getElem_fin, Vector.getElem_ofFn, hφ.xor, getD_lr hφ hc]
  rw [← Fin.getElem_fin, hp i, ← Fin.getElem_fin, hq i]; rfl

theorem wr_xor3W {x y z : Word m} {x' y' z' : Vector α 32} (hx : WR φ x x') (hy : WR φ y y')
    (hz : WR φ z z') : WR φ (xor3W x y z) (o.xor3W x' y' z') := fun i ↦ by
  simp only [xor3W, GOps.xor3W, Fin.getElem_fin, Vector.getElem_ofFn, hφ.xor]
  rw [← Fin.getElem_fin, hx i, ← Fin.getElem_fin, hy i, ← Fin.getElem_fin, hz i]; rfl

theorem wr_shiftW {ms : List (Form m)} {ms' : List α} (h : LR φ ms ms') :
    WR φ (shiftW ms) (o.shiftW ms') := fun i ↦ by
  simp only [shiftW, GOps.shiftW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · exact hφ.zero.symm
  · exact getD_lr hφ h _

/-! ## The adders -/

theorem sim_addCarries (x y : Word m) (x' y' : Vector α 32) (hx : WR φ x x') (hy : WR φ y y')
    (n : ℕ) : ∀ (c : Form m) (c' : α), c' = φ c →
      Sim o φ s₀ (addCarries x y n c) (o.addCarries x' y' n c') (LR φ) := by
  induction n with
  | zero => intro c c' hc; exact sim_pure (by simp [LR, hc])
  | succ n ih =>
    intro c c' hc
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi
    refine sim_bind (sim_mul (by rw [hφ.xor, hxi, hc]) (by rw [hφ.xor, hyi, hc]))
      (fun _ ↦ grows_bind (addCarries_grows _ _ _ _) fun _ ↦ grows_pure _) fun g g' hg ↦ ?_
    refine sim_bind (ih _ _ (by rw [hφ.xor, hc, hg])) (fun _ ↦ grows_pure _)
      fun r r' hr ↦ sim_pure ?_
    simp only [LR, List.map_cons] at hr ⊢
    rw [hr, hc]

theorem sim_addW {x y : Word m} {x' y' : Vector α 32} (hx : WR φ x x') (hy : WR φ y y') :
    Sim o φ s₀ (addW x y) (o.addW x' y') (WR φ) :=
  sim_map (sim_addCarries hφ x y x' y' hx hy 31 0 o.zero hφ.zero.symm) fun _ _ h ↦
    wr_sumW hφ hx hy h

theorem sim_majorities (x y z : Word m) (x' y' z' : Vector α 32) (hx : WR φ x x') (hy : WR φ y y')
    (hz : WR φ z z') (n : ℕ) :
    Sim o φ s₀ (majorities x y z n) (o.majorities x' y' z' n) (LR φ) := by
  induction n with
  | zero => exact sim_pure (by simp [LR])
  | succ n ih =>
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    have hzi := hz ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi hzi
    refine sim_bind (sim_mul (by rw [hφ.xor, hxi, hzi]) (by rw [hφ.xor, hyi, hzi]))
      (fun _ ↦ grows_bind (majorities_grows _ _ _ _) fun _ ↦ grows_pure _) fun g g' hg ↦ ?_
    refine sim_bind ih (fun _ ↦ grows_pure _) fun r r' hr ↦ sim_pure ?_
    simp only [LR, List.map_cons] at hr ⊢
    rw [hr, hφ.xor, hg, hzi]

theorem sim_rippleCarries (p q : Word m) (p' q' : Vector α 32) (hp : WR φ p p') (hq : WR φ q q')
    (n : ℕ) : ∀ (c : Form m) (c' : α), c' = φ c →
      Sim o φ s₀ (rippleCarries p q n c) (o.rippleCarries p' q' n c') (LR φ) := by
  induction n with
  | zero => intro c c' hc; exact sim_pure (by simp [LR, hc])
  | succ n ih =>
    intro c c' hc
    by_cases hi : 1 ≤ 30 - n
    · simp only [rippleCarries, GOps.rippleCarries, hi, ↓reduceIte]
      have hpi := hp ⟨30 - n, by omega⟩
      have hqi := hq ⟨30 - n, by omega⟩
      simp only [Fin.getElem_fin] at hpi hqi
      refine sim_bind (sim_mul (by rw [hφ.xor, hpi, hc]) (by rw [hφ.xor, hqi, hc]))
        (fun _ ↦ grows_bind (rippleCarries_grows _ _ _ _) fun _ ↦ grows_pure _) fun g g' hg ↦ ?_
      refine sim_bind (ih _ _ (by rw [hφ.xor, hc, hg])) (fun _ ↦ grows_pure _)
        fun r r' hr ↦ sim_pure ?_
      simp only [LR, List.map_cons] at hr ⊢
      rw [hr, hc]
    · simp only [rippleCarries, GOps.rippleCarries, hi, ↓reduceIte]
      refine sim_bind (ih _ _ hc) (fun _ ↦ grows_pure _) fun r r' hr ↦ sim_pure ?_
      simp only [LR, List.map_cons] at hr ⊢
      rw [hr, hc]

theorem sim_add3W {x y z : Word m} {x' y' z' : Vector α 32} (hx : WR φ x x') (hy : WR φ y y')
    (hz : WR φ z z') : Sim o φ s₀ (add3W x y z) (o.add3W x' y' z') (WR φ) :=
  sim_bind (sim_majorities hφ x y z x' y' z' hx hy hz 31)
    (fun _ ↦ grows_map _ (rippleCarries_grows _ _ _ _)) fun _ _ hms ↦
      sim_map (sim_rippleCarries hφ _ _ _ _ (wr_xor3W hφ hx hy hz) (wr_shiftW hφ hms) 31 0 o.zero
        hφ.zero.symm) fun _ _ h ↦ wr_sumW hφ (wr_xor3W hφ hx hy hz) (wr_shiftW hφ hms) h

/-! ## The compression -/

end Generic

namespace Generic

variable {α S : Type} {o : GOps Blake2sCircuit.m α S} {φ : Form Blake2sCircuit.m → α} {s₀ : S}

/-- Generic vectors of words hold the images of bitset ones. -/
def VR (φ : Form Blake2sCircuit.m → α) {k : ℕ} (v : Vector (Word Blake2sCircuit.m) k)
    (v' : Vector (Vector α 32) k) : Prop := ∀ j : Fin k, WR φ v[j] v'[j]

theorem vr_set {k : ℕ} {v : Vector (Word Blake2sCircuit.m) k} {v' : Vector (Vector α 32) k}
    (hv : VR φ v v') (a : Fin k) {x : Word Blake2sCircuit.m} {x' : Vector α 32} (hx : WR φ x x') :
    VR φ (v.set a x) (v'.set a x') := fun j ↦ by
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · exact hx
  · exact hv j

variable (hφ : Linear o φ)
include hφ

theorem sim_gW {v : Vector (Word Blake2sCircuit.m) 16} {v' : Vector (Vector α 32) 16}
    (hv : VR φ v v') (a b c d : Fin 16) {mx my : Word Blake2sCircuit.m} {mx' my' : Vector α 32}
    (hmx : WR φ mx mx') (hmy : WR φ my my') :
    Sim o φ s₀ (gW v a b c d mx my) (o.gW v' a b c d mx' my') (VR φ) := by
  unfold gW GOps.gW
  refine sim_bind (sim_add3W hφ (hv a) (hv b) hmx) (fun _ ↦ ?_) fun a1 a1' ha1 ↦ ?_
  · exact grows_bind (grows_addW _ _) fun _ ↦ grows_bind (grows_add3W _ _ _) fun _ ↦
      grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hd1 := wr_rotrW (wr_xorW hφ (hv d) ha1) 16
  refine sim_bind (sim_addW hφ (hv c) hd1) (fun _ ↦ ?_) fun c1 c1' hc1 ↦ ?_
  · exact grows_bind (grows_add3W _ _ _) fun _ ↦ grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hb1 := wr_rotrW (wr_xorW hφ (hv b) hc1) 12
  refine sim_bind (sim_add3W hφ ha1 hb1 hmy) (fun _ ↦ ?_) fun a2 a2' ha2 ↦ ?_
  · exact grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hd2 := wr_rotrW (wr_xorW hφ hd1 ha2) 8
  refine sim_bind (sim_addW hφ hc1 hd2) (fun _ ↦ grows_pure _) fun c2 c2' hc2 ↦ ?_
  have hb2 := wr_rotrW (wr_xorW hφ hb1 hc2) 7
  exact sim_pure (vr_set (vr_set (vr_set (vr_set hv a ha2) b hb2) c hc2) d hd2)

-- From here on the gadgets are opaque to unification (as in `SpartanChainBlake2sCompress.lean`).
attribute [local irreducible] gW addW add3W GOps.gW GOps.addW GOps.add3W

theorem sim_roundW {v m' : Vector (Word Blake2sCircuit.m) 16} {v'' m'' : Vector (Vector α 32) 16}
    (s : Vector (Fin 16) 16) (hv : VR φ v v'') (hm : VR φ m' m'') :
    Sim o φ s₀ (roundW v m' s) (o.roundW v'' m'' s) (VR φ) := by
  unfold roundW GOps.roundW
  refine sim_bind (sim_gW hφ hv 0 4 8 12 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v1 v1' h1 ↦ ?_
  refine sim_bind (sim_gW hφ h1 1 5 9 13 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v2 v2' h2 ↦ ?_
  refine sim_bind (sim_gW hφ h2 2 6 10 14 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v3 v3' h3 ↦ ?_
  refine sim_bind (sim_gW hφ h3 3 7 11 15 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v4 v4' h4 ↦ ?_
  refine sim_bind (sim_gW hφ h4 0 5 10 15 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v5 v5' h5 ↦ ?_
  refine sim_bind (sim_gW hφ h5 1 6 11 12 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v6 v6' h6 ↦ ?_
  refine sim_bind (sim_gW hφ h6 2 7 8 13 (hm _) (hm _)) (fun _ ↦ by
    repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
      exact grows_gW _ _ _ _ _ _ _)) fun v7 v7' h7 ↦ ?_
  exact sim_gW hφ h7 3 4 9 14 (hm _) (hm _)

attribute [local irreducible] roundW GOps.roundW

theorem sim_rounds {msg : Vector (Word Blake2sCircuit.m) 16} {msg' : Vector (Vector α 32) 16}
    (hm : VR φ msg msg') (l : List (Vector (Fin 16) 16)) :
    ∀ (v : Vector (Word Blake2sCircuit.m) 16) (v' : Vector (Vector α 32) 16), VR φ v v' →
      Sim o φ s₀ (l.foldlM (fun v s ↦ roundW v msg s) v)
        (l.foldlM (fun v s ↦ o.roundW v msg' s) v') (VR φ) := by
  induction l with
  | nil => intro v v' hv; exact sim_pure hv
  | cons s l ih =>
    intro v v' hv
    rw [List.foldlM_cons, List.foldlM_cons]
    exact sim_bind (sim_roundW hφ s hv hm) (grows_rounds msg l) fun w w' hw ↦ ih w w' hw

/-- The generic compression simulates the bitset one, given that `φ` of an input position (or the
constant) is the interpretation's `var`. -/
theorem sim_compressW
    (hvar : ∀ k : Pos Blake2sCircuit.m, start.avail.getLsbD k = true →
      o.var k = φ (Form.var k)) :
    Sim o φ s₀ compressW o.compressW (VR φ) := by
  have hin : ∀ b, (b + 32 ≤ 256 ∨ (640 ≤ b ∧ b + 32 ≤ 1280)) → WR φ (inW b) (o.inW b) :=
    fun b hb i ↦ by
      simp only [inW, GOps.inW, Fin.getElem_fin, Vector.getElem_ofFn]
      exact hvar _ (by rw [start_avail, pos_val (by show _ < 16384; omega)]; simp; omega)
  have hlit : ∀ c : UInt32, WR φ (litW constPos c) (o.litW constPos c) := fun c i ↦ by
    simp only [litW, GOps.litW, Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs
    · exact hvar _ (by rw [start_avail]; decide)
    · exact hφ.zero.symm
  have hinit : VR φ initW o.initW := fun w ↦ by
    simp only [initW, GOps.initW, Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs with h1 h2
    · exact hin _ (by omega)
    · exact hlit _
    · exact wr_xorW hφ (hlit _) (hin _ (by simp only [counterLo]; omega))
  have hmsg : VR φ (Vector.ofFn fun w : Fin 16 ↦ msgW w)
      (Vector.ofFn fun w : Fin 16 ↦ o.inW (msgBase + 32 * w)) := fun w ↦ by
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, msgW]
    exact hin _ (by simp only [msgBase]; omega)
  unfold compressW GOps.compressW
  dsimp only
  rw [← Vector.foldlM_toList, ← Vector.foldlM_toList]
  refine sim_bind (sim_rounds hφ hmsg sigma.toList initW o.initW hinit) (fun _ ↦ grows_pure _)
    fun v v' hv ↦ sim_pure fun w ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact wr_xorW hφ (wr_xorW hφ (hv ⟨w, by omega⟩) (hv ⟨w + 8, by omega⟩)) (hin _ (by omega))

end Generic

end SpartanChain
