import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Bitwise
import SpartanChainBlake2sCircuit

/-!
# Building product-gate circuits, and the 32-bit word gadgets

Provenance: copied from leanerVM (Apache-2.0, github.com/Verified-zkEVM/leanerVM, `main` at
`95957214d42b6d5e21d7066f760e5ec256514cf8`; identical at `e715c49` and on the branch
`docs/protocol-headline-theorems` at `532ebb4`): `LeanerVM/Protocol/ToArkLib/Flock/Builder.lean`
and `LeanerVM/Protocol/ToArkLib/Flock/Words.lean`, concatenated. Modified (Apache-2.0 §4(b)):
the module-system annotations are dropped, the namespace is `SpartanChain`, and the `private`
lemmas of the adders are public (the walk's simulation, `SpartanChainBlake2sWalk.lean`, uses
them). No statement and no definition is changed.

**The builder.** A gadget is a program in `Builder m`, a state monad over the next free position
and the gates recorded so far. Its one effect, `mul a b`, records the gate `(a, b)` at the next
position and returns that position's form. Linear operations need no effect: they are XORs of
forms. Two contracts compose through `bind`: `Sound w mb P` (whenever the gates a run of `mb`
records hold at the block `w`, its result satisfies `P`) and `Ok S n₀ mb k P` (run from a good
state, `mb` keeps it good, records exactly `k` gates, and returns a result satisfying `P`).

**Words.** A word is 32 forms, bit `i` at index `i`. `Den w x u` says the word `x` denotes the
value `u` on the block `w`. XOR, rotation, literals (`litW`, through the constant position) and
input words (`inW`) are linear: no gate. The ripple-carry adder `addW` records 31 gates, the fused
three-operand adder `add3W` 61; `sound_addW`, `sound_add3W` state their specifications against
`UInt32` arithmetic, `ok_addW`, `ok_add3W` their gate counts.
-/

namespace SpartanChain

namespace ProductCircuit

variable {m : ℕ}

/-! ## The builder -/

/-- The builder's state: the next free position and the gates recorded so far. -/
structure BuildState (m : ℕ) where
  /-- The next gate position. -/
  next : ℕ
  /-- The gates recorded so far, in evaluation order. -/
  gates : Array (Pos m × Gate m)

/-- A circuit-building program. -/
abbrev Builder (m : ℕ) := StateM (BuildState m)

/-- Record the gate `(a, b)` at the next position and return that position's form. -/
def mul (a b : Form m) : Builder m (Form m) :=
  modifyGet fun s ↦
    (Form.var (pos s.next), { next := s.next + 1, gates := s.gates.push (pos s.next, ⟨a, b⟩) })

/-- One `mul`: the gate at `next`, and `next` advanced. -/
theorem run_mul (a b : Form m) (σ : BuildState m) :
    (mul a b).run σ =
      (Form.var (pos σ.next), { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) }) :=
  rfl

theorem run_bind' {α β : Type} (mb : Builder m α) (f : α → Builder m β) (σ : BuildState m) :
    (mb >>= f).run σ = (f (mb.run σ).1).run (mb.run σ).2 := rfl

theorem run_map' {α β : Type} (mb : Builder m α) (f : α → β) (σ : BuildState m) :
    (f <$> mb).run σ = (f (mb.run σ).1, (mb.run σ).2) := rfl

/-! ## Soundness -/

/-- Every gate recorded in the state holds at `z`. -/
def GatesHold (σ : BuildState m) (z : Pos m → Bool) : Prop :=
  ∀ kg ∈ σ.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z)

/-- A program only appends gates. -/
def Grows {α : Type} (mb : Builder m α) : Prop :=
  ∀ σ : BuildState m, ∀ kg ∈ σ.gates, kg ∈ (mb.run σ).2.gates

/-- Whenever the gates of a run of `mb` hold at `w`, its result satisfies `P`. -/
def Sound {α : Type} (w : Pos m → Bool) (mb : Builder m α) (P : α → Prop) : Prop :=
  ∀ σ : BuildState m, GatesHold (mb.run σ).2 w → P (mb.run σ).1

theorem grows_bind {α β : Type} {mb : Builder m α} {f : α → Builder m β} (hm : Grows mb)
    (hf : ∀ a, Grows (f a)) : Grows (mb >>= f) := by
  intro σ kg h
  rw [StateT.run_bind]
  exact hf _ _ _ (hm σ kg h)

theorem grows_pure {α : Type} (a : α) : Grows (pure a : Builder m α) := fun _ _ h ↦ h

theorem grows_map {α β : Type} {mb : Builder m α} (f : α → β) (hm : Grows mb) :
    Grows (f <$> mb) := fun σ kg h ↦ by rw [run_map']; exact hm σ kg h

theorem grows_mul (a b : Form m) : Grows (mul a b) := fun σ kg h ↦ by
  rw [run_mul]; exact Array.mem_push_of_mem _ h

theorem sound_bind {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → Builder m β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hg : ∀ a, Grows (f a))
    (hf : ∀ a, P a → Sound w (f a) Q) : Sound w (mb >>= f) Q := by
  intro σ h
  rw [StateT.run_bind] at h ⊢
  exact hf _ (hm σ fun kg hkg ↦ h kg (hg _ _ kg hkg)) _ h

theorem sound_pure {α : Type} {w : Pos m → Bool} {a : α} {P : α → Prop} (h : P a) :
    Sound w (pure a : Builder m α) P := fun _ _ ↦ h

theorem sound_map {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hf : ∀ a, P a → Q (f a)) :
    Sound w (f <$> mb) Q := fun σ h ↦ by
  rw [run_map'] at h ⊢
  exact hf _ (hm σ h)

/-- The gate `mul` records holds: its result evaluates to the product of its forms. -/
theorem sound_mul {w : Pos m → Bool} (a b : Form m) :
    Sound w (mul a b) (fun o ↦ o.eval w = (a.eval w && b.eval w)) := fun σ h ↦ by
  rw [run_mul] at h ⊢
  rw [eval_var]
  exact h _ (Array.mem_push_self ..)

/-! ## Well-formedness -/

/-- Where a build starts: the positions available before any gate (the inputs and the
constant) and the first gate position, past every available one. -/
structure Start (m : ℕ) where
  /-- The positions available before any gate. -/
  avail : Form m
  /-- The first gate position. -/
  base : ℕ
  /-- No position from `base` on is available at the start. -/
  fresh : ∀ j, base ≤ j → avail.getLsbD j = false

namespace Start

variable (S : Start m)

/-- Position `j` is available once the gates below `n` are recorded. -/
def AvailAt (n j : ℕ) : Bool := S.avail.getLsbD j || (decide (S.base ≤ j) && decide (j < n))

/-- `L` mentions only positions available at `n`. -/
def SubN (L : Form m) (n : ℕ) : Prop := ∀ j, L.getLsbD j = true → S.AvailAt n j = true

/-- A good state: `next` is past the start, the recorded gates are bounded from the start
availability, and after them exactly the start availability and `[base, next)` are
available. -/
structure Inv (σ : BuildState m) : Prop where
  /-- Gate positions start at `base`. -/
  le : S.base ≤ σ.next
  /-- The recorded gates are bounded from the start availability. -/
  bounded : BoundedFrom S.avail σ.gates.toList
  /-- After them, exactly the start availability and `[base, next)` are available. -/
  avail : ∀ j, (availAfter S.avail σ.gates.toList).getLsbD j = S.AvailAt σ.next j

/-- Run from a good state at or after `n₀` with room for `k` gates, `mb` keeps the state good,
records exactly `k` gates, and returns a result satisfying `P` at the new `next`. -/
def Ok {α : Type} (n₀ : ℕ) (mb : Builder m α) (k : ℕ) (P : α → ℕ → Prop) : Prop :=
  ∀ σ : BuildState m, S.Inv σ → n₀ ≤ σ.next → σ.next + k ≤ 2 ^ m →
    S.Inv (mb.run σ).2 ∧ (mb.run σ).2.next = σ.next + k ∧ P (mb.run σ).1 (mb.run σ).2.next

variable {S}

theorem availAt_iff (n j : ℕ) :
    S.AvailAt n j = true ↔ S.avail.getLsbD j = true ∨ (S.base ≤ j ∧ j < n) := by
  simp [AvailAt]

theorem SubN.mono {L : Form m} {n n' : ℕ} (h : S.SubN L n) (hn : n ≤ n') : S.SubN L n' := by
  intro j hj
  rcases (availAt_iff n j).mp (h j hj) with h' | h'
  · exact (availAt_iff n' j).mpr (Or.inl h')
  · exact (availAt_iff n' j).mpr (Or.inr ⟨h'.1, by omega⟩)

theorem SubN.xor {L M : Form m} {n : ℕ} (hL : S.SubN L n) (hM : S.SubN M n) :
    S.SubN (L ^^^ M) n := by
  intro j hj
  rw [BitVec.getLsbD_xor] at hj
  cases hl : L.getLsbD j
  · rw [hl, Bool.false_xor] at hj; exact hM j hj
  · exact hL j hl

theorem subN_zero (n : ℕ) : S.SubN 0 n := by
  intro j hj
  simp at hj

theorem subN_var {k : Pos m} {n : ℕ} (h : S.AvailAt n k = true) : S.SubN (Form.var k) n := by
  intro j hj
  rw [getLsbD_var, decide_eq_true_eq] at hj
  rwa [← hj]

/-- A start position is available at every stage. -/
theorem subN_start {k : Pos m} (h : S.avail.getLsbD k = true) (n : ℕ) :
    S.SubN (Form.var k) n :=
  subN_var ((availAt_iff _ _).mpr (Or.inl h))

theorem sub_of_subN {L a : Form m} {n : ℕ} (ha : ∀ j, a.getLsbD j = S.AvailAt n j)
    (h : S.SubN L n) : Sub L a :=
  sub_iff.mpr fun j hj ↦ (ha j).trans (h j hj)

theorem inv_init : S.Inv ⟨S.base, #[]⟩ where
  le := le_rfl
  bounded := trivial
  avail j := by simp [availAfter, AvailAt]

/-- Recording one gate at `next`, with forms available at `next`, keeps the state good. -/
theorem inv_push {σ : BuildState m} (hσ : S.Inv σ) (hlt : σ.next < 2 ^ m) {a b : Form m}
    (ha : S.SubN a σ.next) (hb : S.SubN b σ.next) :
    S.Inv { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) } where
  le := by dsimp only; have := hσ.le; omega
  bounded := by
    rw [Array.toList_push, boundedFrom_append]
    refine ⟨hσ.bounded, sub_of_subN hσ.avail ha, sub_of_subN hσ.avail hb, ?_, trivial⟩
    rw [hσ.avail, pos_val hlt, Bool.eq_false_iff, ne_eq, availAt_iff]
    have := hσ.le
    have := S.fresh σ.next hσ.le
    simp only [this, Bool.false_eq_true, false_or]
    omega
  avail j := by
    rw [Array.toList_push, availAfter_append_singleton, BitVec.getLsbD_or, hσ.avail,
      getLsbD_var, pos_val hlt, Bool.eq_iff_iff, Bool.or_eq_true, availAt_iff, availAt_iff,
      decide_eq_true_eq]
    have := hσ.le
    dsimp only
    constructor
    · rintro ((h | h) | h) <;> [exact Or.inl h; exact Or.inr ⟨h.1, by omega⟩;
        exact Or.inr ⟨by omega, by omega⟩]
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hj : j < σ.next
        · exact Or.inl (Or.inr ⟨h.1, hj⟩)
        · exact Or.inr (by omega)

/-- The gate count of a contract, up to equality. -/
theorem Ok.cast {α : Type} {n₀ k k' : ℕ} {mb : Builder m α} {P : α → ℕ → Prop}
    (h : S.Ok n₀ mb k P) (hk : k = k') : S.Ok n₀ mb k' P := hk ▸ h

theorem ok_bind {α β : Type} {n₀ k₁ k : ℕ} {mb : Builder m α} {f : α → Builder m β}
    {P : α → ℕ → Prop} {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k₁ P) (hk : k₁ ≤ k)
    (hf : ∀ a n, n₀ ≤ n → P a n → S.Ok n (f a) (k - k₁) Q) : S.Ok n₀ (mb >>= f) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn (by omega)
  rw [run_bind']
  obtain ⟨h1', h2', h3'⟩ := hf _ _ (by omega) h3 _ h1 le_rfl (by omega)
  exact ⟨h1', by omega, h3'⟩

theorem ok_pure {α : Type} {n₀ k : ℕ} {a : α} {P : α → ℕ → Prop} (h : ∀ n, n₀ ≤ n → P a n)
    (hk : k = 0) : S.Ok n₀ (pure a : Builder m α) k P := by
  intro σ hσ hn _
  subst hk
  exact ⟨hσ, rfl, h _ hn⟩

theorem ok_map {α β : Type} {n₀ k : ℕ} {mb : Builder m α} {f : α → β} {P : α → ℕ → Prop}
    {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k P) (hf : ∀ a n, n₀ ≤ n → P a n → Q (f a) n) :
    S.Ok n₀ (f <$> mb) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn hle
  rw [run_map']
  exact ⟨h1, h2, hf _ (mb.run σ).2.next (by omega) h3⟩

/-- `mul` records one gate, and its result is available after it. -/
theorem ok_mul {n₀ : ℕ} {a b : Form m} (ha : S.SubN a n₀) (hb : S.SubN b n₀) :
    S.Ok n₀ (mul a b) 1 (fun o n ↦ S.SubN o n) := by
  intro σ hσ hn hle
  rw [run_mul]
  refine ⟨inv_push hσ (by omega) (ha.mono hn) (hb.mono hn), rfl, subN_var ?_⟩
  rw [pos_val (by omega), availAt_iff]
  have := hσ.le
  dsimp only
  omega

/-- The schedule of a good state is bounded from the start availability. -/
theorem Inv.boundedFrom {σ : BuildState m} (h : S.Inv σ) : BoundedFrom S.avail σ.gates.toList :=
  h.bounded

/-- A circuit whose gates are those of a run from `base`, for a program with the contract, and
whose inputs and constant are the start availability, is bounded. -/
theorem bounded_of_ok {α : Type} {c : ProductCircuit m} {mb : Builder m α} {k : ℕ}
    {P : α → ℕ → Prop} (hav : c.inputs ||| Form.var c.cpos = S.avail) (h : S.Ok S.base mb k P)
    (hk : S.base + k ≤ 2 ^ m) (hg : c.gates = (mb.run ⟨S.base, #[]⟩).2.gates) : c.Bounded := by
  rw [Bounded, hav, hg]
  exact (h _ inv_init le_rfl hk).1.bounded

end Start

end ProductCircuit

namespace ProductCircuit

variable {m : ℕ}

/-! ## Words -/

/-- A 32-bit word of forms, bit `i` at index `i`. -/
abbrev Word (m : ℕ) := Vector (Form m) 32

/-- Bitwise XOR of words. -/
def xorW (x y : Word m) : Word m := Vector.ofFn fun i ↦ x[i] ^^^ y[i]

/-- Rotate right by `n`: bit `i` is bit `(i + n) mod 32`. -/
def rotrW (w : Word m) (n : ℕ) : Word m :=
  Vector.ofFn fun i ↦ w[(i.val + n) % 32]'(Nat.mod_lt _ (by decide))

/-- A literal word, through the constant position `cpos`: bit `i` is `cpos` if set, else `0`. -/
def litW (cpos : Pos m) (c : UInt32) : Word m :=
  Vector.ofFn fun i ↦ if c.toNat.testBit i then Form.var cpos else 0

/-- The input word at the positions `b, …, b + 31`, reduced modulo the block size (`subW_inW`
requires them in range). -/
def inW (b : ℕ) : Word m := Vector.ofFn fun i ↦ Form.var (pos (b + i))

/-- The carries of `x + y` from bit `31 - n` with carry `c`: carry `i + 1` is `c + g` with the gate
`g = (x_i + c)(y_i + c)`. Returns the carries `c_{31-n}, …, c_31`. -/
def addCarries (x y : Word m) : (n : ℕ) → Form m → Builder m (List (Form m))
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← mul (x[i]'(by omega) ^^^ c) (y[i]'(by omega) ^^^ c)
    let rest ← addCarries x y n (c ^^^ g)
    pure (c :: rest)

/-- The sum of a ripple: bit `i` is `p_i + q_i + c_i`. -/
def sumW (p q : Word m) (cs : List (Form m)) : Word m :=
  Vector.ofFn fun i ↦ p[i] ^^^ q[i] ^^^ cs.getD i 0

/-- `x + y`, one gate per carry into bits `1, …, 31`. -/
def addW (x y : Word m) : Builder m (Word m) := sumW x y <$> addCarries x y 31 0

/-- The majority gates of `add3W` from bit `31 - n`: `g_i = (x_i + z_i)(y_i + z_i)`, returning the
majorities `g_i + z_i`. -/
def majorities (x y z : Word m) : (n : ℕ) → Builder m (List (Form m))
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← mul (x[i]'(by omega) ^^^ z[i]'(by omega)) (y[i]'(by omega) ^^^ z[i]'(by omega))
    let rest ← majorities x y z n
    pure ((g ^^^ z[i]'(by omega)) :: rest)

/-- The ripple of `add3W` from bit `31 - n` with carry `c`: a gate for each of bits `1, …, 30`;
bit `0` of `q` is `0`, so bit `0` carries nothing and needs none. -/
def rippleCarries (p q : Word m) : (n : ℕ) → Form m → Builder m (List (Form m))
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← mul (p[i]'(by omega) ^^^ c) (q[i]'(by omega) ^^^ c)
      let rest ← rippleCarries p q n (c ^^^ g)
      pure (c :: rest)
    else
      let rest ← rippleCarries p q n c
      pure (c :: rest)

/-- The XOR word `x ⊕ y ⊕ z`. -/
def xor3W (x y z : Word m) : Word m := Vector.ofFn fun i ↦ x[i] ^^^ y[i] ^^^ z[i]

/-- The majorities shifted up by one: bit `0` is `0`, bit `i ≥ 1` is majority `i - 1`. -/
def shiftW (ms : List (Form m)) : Word m :=
  Vector.ofFn fun i ↦ if i.val = 0 then 0 else ms.getD (i.val - 1) 0

/-- `x + y + z`: 31 majority gates, then 30 ripple gates adding `xor3W` and `shiftW`. -/
def add3W (x y z : Word m) : Builder m (Word m) :=
  majorities x y z 31 >>= fun ms ↦
    sumW (xor3W x y z) (shiftW ms) <$> rippleCarries (xor3W x y z) (shiftW ms) 31 0

/-! ## Denotation -/

/-- The word `x` denotes the value `u` on the block `w`. -/
def Den (w : Pos m → Bool) (x : Word m) (u : UInt32) : Prop :=
  ∀ i : Fin 32, x[i].eval w = u.toBitVec.getLsbD i

/-- A denotation, transported along an equality of values. -/
theorem den_congr {w : Pos m → Bool} {x : Word m} {u u' : UInt32} (h : Den w x u)
    (e : u = u') : Den w x u' := e ▸ h

/-- A word denotes at most one value. -/
theorem den_unique {w : Pos m → Bool} {x : Word m} {u u' : UInt32} (h : Den w x u)
    (h' : Den w x u') : u = u' := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (h ⟨i, hi⟩).symm.trans (h' ⟨i, hi⟩)

theorem den_xorW {w : Pos m → Bool} {x y : Word m} {xu yu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) : Den w (xorW x y) (xu ^^^ yu) := by
  intro i
  rw [xorW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, hx, hy]
  simp

theorem den_rotrW {w : Pos m → Bool} {x : Word m} {xu : UInt32} (hx : Den w x xu) {n : ℕ}
    (hn : n < 32) : Den w (rotrW x n) ⟨xu.toBitVec.rotateRight n⟩ := by
  intro i
  rw [rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  have := hx ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.getElem_fin] at this
  rw [this, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hn]
  split_ifs with h
  · rw [show ((i : ℕ) + n) % 32 = n + i by omega]
  · rw [show ((i : ℕ) + n) % 32 = i - (32 - n) by omega]
    simp only [i.isLt, decide_true, Bool.true_and]

theorem den_litW {w : Pos m → Bool} {cpos : Pos m} (hc : w cpos = true) (u : UInt32) :
    Den w (litW cpos u) u := by
  intro i
  rw [litW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs with h
  · rw [eval_var, hc]; exact h.symm
  · rw [eval_zero]
    exact (Bool.eq_false_iff.mpr h).symm

/-- An input word denotes the value whose bits the block holds at its positions. -/
theorem den_inW {w : Pos m → Bool} {b : ℕ} {u : UInt32}
    (h : ∀ i : Fin 32, w (pos (b + i)) = u.toBitVec.getLsbD i) : Den w (inW b) u := by
  intro i
  rw [inW, Fin.getElem_fin, Vector.getElem_ofFn, eval_var]
  exact h i

/-- The word a block holds at the positions `b, …, b + 31`, low bit first. -/
def readWord (w : Pos m → Bool) (b : ℕ) : UInt32 := ⟨BitVec.ofFnLE fun i : Fin 32 ↦ w (pos (b + i))⟩

/-- The input word at `b` denotes the word the block holds there. -/
theorem den_readWord (w : Pos m → Bool) (b : ℕ) : Den w (inW b) (readWord w b) :=
  den_inW fun i ↦ by simp [readWord]

/-! ## The ripple adder -/

theorem run_addCarries_zero (x y : Word m) (c : Form m) (σ : BuildState m) :
    (addCarries x y 0 c).run σ = ([c], σ) := rfl

theorem run_addCarries_succ (x y : Word m) (n : ℕ) (c : Form m) (σ : BuildState m) :
    (addCarries x y (n + 1) c).run σ =
      let r := (addCarries x y n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := rfl

theorem addCarries_grows (x y : Word m) (n : ℕ) (c : Form m) :
    Grows (addCarries x y n c) := by
  induction n generalizing c with
  | zero => intro σ kg h; rw [run_addCarries_zero]; exact h
  | succ n ih =>
    intro σ kg h
    rw [run_addCarries_succ]
    exact ih _ _ kg (Array.mem_push_of_mem _ h)

/-- The carry recursion: from bit `31 - n` with the right carry, the carry forms evaluate to the
carries of `xv + yv`, if the recorded gates hold. -/
theorem addCarries_spec (x y : Word m) (z : Pos m → Bool) (xv yv : BitVec 32)
    (hx : ∀ i : Fin 32, x[i].eval z = xv.getLsbD i) (hy : ∀ i : Fin 32, y[i].eval z = yv.getLsbD i)
    (n : ℕ) (c : Form m) (σ : BuildState m) (hn : n ≤ 31)
    (hc : c.eval z = BitVec.carry (31 - n) xv yv false)
    (hz : GatesHold ((addCarries x y n c).run σ).2 z) (j : ℕ) (hj : j ≤ n) :
    (((addCarries x y n c).run σ).1.getD j 0).eval z = BitVec.carry (31 - n + j) xv yv false := by
  induction n generalizing c σ j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [run_addCarries_zero]
    exact hc
  | succ n ih =>
    rw [run_addCarries_succ] at hz ⊢
    have hg := hz _ (addCarries_grows x y n _ _ _ (Array.mem_push_self ..))
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi
    rw [eval_xor, eval_xor, hxi, hyi, hc, show 31 - (n + 1) = 30 - n by omega] at hg
    have hc' : (c ^^^ Form.var (pos σ.next)).eval z = BitVec.carry (31 - n) xv yv false := by
      rw [eval_xor, eval_var, hg, hc, show 31 - n = (30 - n) + 1 by omega, BitVec.carry_succ,
        show 31 - (n + 1) = 30 - n by omega]
      cases xv.getLsbD (30 - n) <;> cases yv.getLsbD (30 - n) <;>
        cases BitVec.carry (30 - n) xv yv false <;> rfl
    rcases j with _ | j
    · exact hc
    · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hz j (by omega),
        show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_addW (x y : Word m) (σ : BuildState m) :
    (addW x y).run σ =
      (sumW x y ((addCarries x y 31 0).run σ).1, ((addCarries x y 31 0).run σ).2) := by
  rw [addW, StateT.run_map]
  rfl

theorem grows_addW (x y : Word m) : Grows (addW x y) := by
  intro σ kg h
  rw [run_addW]
  dsimp only
  exact addCarries_grows x y 31 0 σ kg h

/-- The ripple adder is sound: if its gates hold, its output denotes the sum of its inputs. -/
theorem sound_addW {w : Pos m → Bool} {x y : Word m} {xu yu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) : Sound w (addW x y) (fun o ↦ Den w o (xu + yu)) := by
  intro σ hz i
  rw [run_addW] at hz ⊢
  dsimp only at hz ⊢
  have h0 : (0 : Form m).eval w = BitVec.carry (31 - 31) xu.toBitVec yu.toBitVec false := by
    rw [eval_zero, Nat.sub_self, BitVec.carry_zero]
  have hcarry := addCarries_spec x y w _ _ hx hy 31 0 σ le_rfl h0 hz i (by omega)
  rw [Nat.sub_self, Nat.zero_add] at hcarry
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hcarry, UInt32.toBitVec_add,
    BitVec.getLsbD_add i.isLt, ← hx, ← hy, Bool.xor_assoc]

/-! ## The fused three-operand adder -/

/-- Carry-save over the naturals: `a + b + c = (a ⊕ b ⊕ c) + 2 maj(a, b, c)`. -/
theorem nat_carry_save (k : ℕ) (a b c : ℕ) (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (hc : c < 2 ^ k) : a + b + c = (a ^^^ b ^^^ c) + 2 * (a &&& b ||| a &&& c ||| b &&& c) := by
  induction k generalizing a b c with
  | zero => simp_all
  | succ k ih =>
    obtain ⟨a0, a', rfl⟩ : ∃ a0 a', a = Nat.bit a0 a' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one a).symm⟩
    obtain ⟨b0, b', rfl⟩ : ∃ b0 b', b = Nat.bit b0 b' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one b).symm⟩
    obtain ⟨c0, c', rfl⟩ : ∃ c0 c', c = Nat.bit c0 c' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one c).symm⟩
    simp only [Nat.bit_lt_two_pow_succ_iff] at ha hb hc
    have := ih a' b' c' ha hb hc
    simp only [Nat.xor_bit, Nat.land_bit, Nat.lor_bit]
    simp only [Nat.bit_val]
    cases a0 <;> cases b0 <;> cases c0 <;> simp <;> omega

/-- Carry-save on words: `x + y + z = (x ⊕ y ⊕ z) + (maj(x, y, z) ≪ 1)`. -/
theorem carry_save (x y z : BitVec 32) :
    x + y + z = (x ^^^ y ^^^ z) + ((x &&& y ||| x &&& z ||| y &&& z) <<< 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one]
  rw [Nat.mod_add_mod, nat_carry_save 32 _ _ _ x.isLt y.isLt z.isLt, Nat.mul_comm 2,
    Nat.add_mod_mod]

theorem run_majorities_zero (x y z : Word m) (σ : BuildState m) :
    (majorities x y z 0).run σ = ([], σ) := rfl

theorem run_majorities_succ (x y z : Word m) (n : ℕ) (σ : BuildState m) :
    (majorities x y z (n + 1)).run σ =
      let r := (majorities x y z n).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next,
            ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega),
              y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }
      ((Form.var (pos σ.next) ^^^ z[30 - n]'(by omega)) :: r.1, r.2) := rfl

theorem majorities_grows (x y z : Word m) (n : ℕ) : Grows (majorities x y z n) := by
  induction n with
  | zero => intro σ kg h; rw [run_majorities_zero]; exact h
  | succ n ih =>
    intro σ kg h
    rw [run_majorities_succ]
    exact ih _ kg (Array.mem_push_of_mem _ h)

/-- The majority gates: from bit `31 - n`, entry `j` evaluates to the majority of bit
`31 - n + j`, if the recorded gates hold. -/
theorem majorities_spec (x y z : Word m) (w : Pos m → Bool) (xv yv zv : BitVec 32)
    (hx : ∀ i : Fin 32, x[i].eval w = xv.getLsbD i) (hy : ∀ i : Fin 32, y[i].eval w = yv.getLsbD i)
    (hz : ∀ i : Fin 32, z[i].eval w = zv.getLsbD i)
    (n : ℕ) (σ : BuildState m) (hn : n ≤ 31) (hw : GatesHold ((majorities x y z n).run σ).2 w)
    (j : ℕ) (hj : j < n) :
    (((majorities x y z n).run σ).1.getD j 0).eval w =
      (xv &&& yv ||| xv &&& zv ||| yv &&& zv).getLsbD (31 - n + j) := by
  induction n generalizing σ j with
  | zero => omega
  | succ n ih =>
    rw [run_majorities_succ] at hw ⊢
    have hg := hw _ (majorities_grows x y z n _ _ (Array.mem_push_self ..))
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    have hzi := hz ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi hzi
    rcases j with _ | j
    · rw [List.getD_cons_zero, eval_xor, eval_var, hg, eval_xor, eval_xor, hxi, hyi, hzi,
        show 31 - (n + 1) + 0 = 30 - n by omega]
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
      cases xv.getLsbD (30 - n) <;> cases yv.getLsbD (30 - n) <;> cases zv.getLsbD (30 - n) <;> rfl
    · rw [List.getD_cons_succ, ih _ (by omega) hw j (by omega),
        show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_rippleCarries_zero (p q : Word m) (c : Form m) (σ : BuildState m) :
    (rippleCarries p q 0 c).run σ = ([c], σ) := rfl

theorem run_rippleCarries_gate (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem run_rippleCarries_skip (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : ¬ 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n c).run σ
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem rippleCarries_grows (p q : Word m) (n : ℕ) (c : Form m) :
    Grows (rippleCarries p q n c) := by
  induction n generalizing c with
  | zero => intro σ kg h; rw [run_rippleCarries_zero]; exact h
  | succ n ih =>
    intro σ kg h
    by_cases hi : 1 ≤ 30 - n
    · rw [run_rippleCarries_gate _ _ _ _ _ hi]
      exact ih _ _ kg (Array.mem_push_of_mem _ h)
    · rw [run_rippleCarries_skip _ _ _ _ _ hi]
      exact ih _ _ kg h

/-- The ripple: from bit `31 - n` with the right carry, the carry forms evaluate to the carries of
`pv + qv`, if the recorded gates hold and bit `0` of `qv` is clear. -/
theorem rippleCarries_spec (p q : Word m) (w : Pos m → Bool) (pv qv : BitVec 32)
    (hp : ∀ i : Fin 32, p[i].eval w = pv.getLsbD i) (hq : ∀ i : Fin 32, q[i].eval w = qv.getLsbD i)
    (hq0 : qv.getLsbD 0 = false) (hc0 : BitVec.carry 0 pv qv false = false)
    (n : ℕ) (c : Form m) (σ : BuildState m) (hn : n ≤ 31)
    (hc : c.eval w = BitVec.carry (31 - n) pv qv false)
    (hw : GatesHold ((rippleCarries p q n c).run σ).2 w) (j : ℕ) (hj : j ≤ n) :
    (((rippleCarries p q n c).run σ).1.getD j 0).eval w =
      BitVec.carry (31 - n + j) pv qv false := by
  induction n generalizing c σ j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [run_rippleCarries_zero]
    exact hc
  | succ n ih =>
    by_cases hi : 1 ≤ 30 - n
    · rw [run_rippleCarries_gate _ _ _ _ _ hi] at hw ⊢
      have hg := hw _ (rippleCarries_grows p q n _ _ _ (Array.mem_push_self ..))
      have hpi := hp ⟨30 - n, by omega⟩
      have hqi := hq ⟨30 - n, by omega⟩
      simp only [Fin.getElem_fin] at hpi hqi
      rw [eval_xor, eval_xor, hpi, hqi, hc, show 31 - (n + 1) = 30 - n by omega] at hg
      have hc' : (c ^^^ Form.var (pos σ.next)).eval w = BitVec.carry (31 - n) pv qv false := by
        rw [eval_xor, eval_var, hg, hc, show 31 - n = (30 - n) + 1 by omega, BitVec.carry_succ,
          show 31 - (n + 1) = 30 - n by omega]
        cases pv.getLsbD (30 - n) <;> cases qv.getLsbD (30 - n) <;>
          cases BitVec.carry (30 - n) pv qv false <;> rfl
      rcases j with _ | j
      · exact hc
      · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hw j (by omega),
          show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]
    · -- bit `0`: no gate, and the carry into bit `1` is the carry into bit `0`
      rw [run_rippleCarries_skip _ _ _ _ _ hi] at hw ⊢
      have hc' : c.eval w = BitVec.carry (31 - n) pv qv false := by
        rw [hc, show 31 - (n + 1) = 0 by omega, show 31 - n = 0 + 1 by omega, BitVec.carry_succ,
          hq0, hc0]
        cases pv.getLsbD 0 <;> rfl
      rcases j with _ | j
      · exact hc
      · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hw j (by omega),
          show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_add3W (x y z : Word m) (σ : BuildState m) :
    (add3W x y z).run σ =
      let r1 := (majorities x y z 31).run σ
      let r2 := (rippleCarries (xor3W x y z) (shiftW r1.1) 31 0).run r1.2
      (sumW (xor3W x y z) (shiftW r1.1) r2.1, r2.2) := by
  rw [add3W, StateT.run_bind]
  simp only [StateT.run_map]
  rfl

theorem grows_add3W (x y z : Word m) : Grows (add3W x y z) := by
  intro σ kg h
  rw [run_add3W]
  dsimp only
  exact rippleCarries_grows _ _ _ _ _ kg (majorities_grows x y z 31 σ kg h)

/-- The fused three-operand adder is sound: if its gates hold, its output denotes the sum of its
three inputs. -/
theorem sound_add3W {w : Pos m → Bool} {x y z : Word m} {xu yu zu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) (hz : Den w z zu) :
    Sound w (add3W x y z) (fun o ↦ Den w o (xu + yu + zu)) := by
  intro σ hw i
  rw [run_add3W] at hw ⊢
  dsimp only at hw ⊢
  generalize hr1 : (majorities x y z 31).run σ = r1 at hw ⊢
  -- the majority gates hold: they are a prefix of the gates
  have hw1 : GatesHold r1.2 w := fun kg hkg ↦ hw kg (rippleCarries_grows _ _ _ _ _ _ hkg)
  rw [UInt32.toBitVec_add, UInt32.toBitVec_add, carry_save]
  set xv := xu.toBitVec
  set yv := yu.toBitVec
  set zv := zu.toBitVec
  set mv := xv &&& yv ||| xv &&& zv ||| yv &&& zv
  have hp : ∀ i : Fin 32, (xor3W x y z)[i].eval w = (xv ^^^ yv ^^^ zv).getLsbD i := by
    intro i
    rw [xor3W, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hx, hy, hz]
    simp [xv, yv, zv]
  have hq : ∀ i : Fin 32, (shiftW r1.1)[i].eval w = (mv <<< 1).getLsbD i := by
    intro i
    rw [shiftW, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.getLsbD_shiftLeft]
    split_ifs with h0
    · rw [eval_zero]
      simp only at h0
      simp [h0]
    · simp only at h0
      have := majorities_spec x y z w xv yv zv hx hy hz 31 σ le_rfl (hr1 ▸ hw1) (i - 1)
        (by omega)
      rw [hr1] at this
      rw [this]
      simp [mv, i.isLt, show ¬ (i : ℕ) < 1 by omega]
  have h0 : (0 : Form m).eval w = BitVec.carry (31 - 31) (xv ^^^ yv ^^^ zv) (mv <<< 1) false := by
    rw [eval_zero, Nat.sub_self, BitVec.carry_zero]
  have hcarry := rippleCarries_spec _ _ w _ _ hp hq (by simp) (by simp) 31 0 r1.2 le_rfl h0 hw i
    (by omega)
  rw [Nat.sub_self, Nat.zero_add] at hcarry
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hcarry, hp, hq,
    BitVec.getLsbD_add i.isLt, Bool.xor_assoc]

/-! ## Gate counts and availability -/

namespace Start

variable {S : Start m}

/-- Every bit of `x` reads only positions available at `n`. -/
def SubW (S : Start m) (x : Word m) (n : ℕ) : Prop := ∀ i : Fin 32, S.SubN x[i] n

theorem SubW.mono {x : Word m} {n n' : ℕ} (h : S.SubW x n) (hn : n ≤ n') : S.SubW x n' :=
  fun i ↦ (h i).mono hn

theorem subW_xorW {x y : Word m} {n : ℕ} (hx : S.SubW x n) (hy : S.SubW y n) :
    S.SubW (xorW x y) n := by
  intro i
  rw [xorW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (hx i).xor (hy i)

theorem subW_rotrW {x : Word m} {n : ℕ} (hx : S.SubW x n) (r : ℕ) : S.SubW (rotrW x r) n := by
  intro i
  rw [rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact hx ⟨_, Nat.mod_lt _ (by decide)⟩

theorem subW_litW {cpos : Pos m} (hc : S.avail.getLsbD cpos = true) (c : UInt32) (n : ℕ) :
    S.SubW (litW cpos c) n := by
  intro i
  rw [litW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · exact subN_start hc n
  · exact subN_zero n

/-- An input word reads only start positions. -/
theorem subW_inW {b : ℕ} (hb : b + 32 ≤ 2 ^ m) (h : ∀ i < 32, S.avail.getLsbD (b + i) = true)
    (n : ℕ) : S.SubW (inW b) n := by
  intro i
  rw [inW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact subN_start (by rw [pos_val (by omega)]; exact h i i.isLt) n

/-- The forms of a list read only positions available at `n`. -/
def SubL (S : Start m) (l : List (Form m)) (n : ℕ) : Prop := ∀ f ∈ l, S.SubN f n

theorem subN_getD {l : List (Form m)} {n : ℕ} (h : S.SubL l n) (i : ℕ) :
    S.SubN (l.getD i 0) n := by
  induction l generalizing i with
  | nil => exact subN_zero n
  | cons f l ih =>
    cases i with
    | zero => rw [List.getD_cons_zero]; exact h f List.mem_cons_self
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun g hg ↦ h g (List.mem_cons_of_mem _ hg)) i

theorem subW_sumW {p q : Word m} {cs : List (Form m)} {n : ℕ} (hp : S.SubW p n)
    (hq : S.SubW q n) (hc : S.SubL cs n) : S.SubW (sumW p q cs) n := by
  intro i
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact ((hp i).xor (hq i)).xor (subN_getD hc i)

theorem ok_addCarries (x y : Word m) (n : ℕ) :
    ∀ (c : Form m) (n₀ : ℕ), S.SubW x n₀ → S.SubW y n₀ → S.SubN c n₀ →
      S.Ok n₀ (addCarries x y n c) n S.SubL := by
  induction n with
  | zero =>
    intro c n₀ _ _ hc
    rw [addCarries]
    exact ok_pure (fun n hn f hf ↦ by rw [List.mem_singleton.mp hf]; exact hc.mono hn) rfl
  | succ n ih =>
    intro c n₀ hx hy hc
    rw [addCarries]
    refine ok_bind (ok_mul ((hx ⟨30 - n, by omega⟩).xor hc) ((hy ⟨30 - n, by omega⟩).xor hc))
      (by omega) fun g n₁ hn₁ hg ↦ ?_
    refine ok_bind (ih _ _ (hx.mono hn₁) (hy.mono hn₁) ((hc.mono hn₁).xor hg)) (by omega)
      fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hc.mono (by omega)
    · exact (hrest f hf).mono hn₃

/-- The ripple adder records `31` gates and its output reads only available positions. -/
theorem ok_addW {n₀ : ℕ} {x y : Word m} (hx : S.SubW x n₀) (hy : S.SubW y n₀) :
    S.Ok n₀ (addW x y) 31 S.SubW := by
  rw [addW]
  exact ok_map (ok_addCarries x y 31 0 n₀ hx hy (subN_zero _)) fun _ _ hn hcs ↦
    subW_sumW (hx.mono hn) (hy.mono hn) hcs

theorem ok_majorities (x y z : Word m) (n : ℕ) :
    ∀ n₀ : ℕ, S.SubW x n₀ → S.SubW y n₀ → S.SubW z n₀ → S.Ok n₀ (majorities x y z n) n S.SubL := by
  induction n with
  | zero =>
    intro n₀ _ _ _
    rw [majorities]
    exact ok_pure (fun _ _ f hf ↦ by simp at hf) rfl
  | succ n ih =>
    intro n₀ hx hy hz
    rw [majorities]
    have hi : 30 - n < 32 := by omega
    refine ok_bind (ok_mul ((hx ⟨30 - n, hi⟩).xor (hz ⟨30 - n, hi⟩))
      ((hy ⟨30 - n, hi⟩).xor (hz ⟨30 - n, hi⟩))) (by omega) fun g n₁ hn₁ hg ↦ ?_
    refine ok_bind (ih _ (hx.mono hn₁) (hy.mono hn₁) (hz.mono hn₁)) (by omega)
      fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (hg.mono (by omega)).xor ((hz ⟨30 - n, hi⟩).mono (by omega))
    · exact (hrest f hf).mono hn₃

theorem ok_rippleCarries (p q : Word m) (n : ℕ) :
    ∀ (c : Form m) (n₀ : ℕ), S.SubW p n₀ → S.SubW q n₀ → S.SubN c n₀ →
      S.Ok n₀ (rippleCarries p q n c) (min n 30) S.SubL := by
  induction n with
  | zero =>
    intro c n₀ _ _ hc
    rw [rippleCarries]
    exact ok_pure (fun n hn f hf ↦ by rw [List.mem_singleton.mp hf]; exact hc.mono hn) rfl
  | succ n ih =>
    intro c n₀ hp hq hc
    rw [rippleCarries]
    split
    · refine ok_bind (ok_mul ((hp ⟨30 - n, by omega⟩).xor hc) ((hq ⟨30 - n, by omega⟩).xor hc))
        (by omega) fun g n₁ hn₁ hg ↦ ?_
      refine ok_bind (ih _ _ (hp.mono hn₁) (hq.mono hn₁) ((hc.mono hn₁).xor hg)) (by omega)
        fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hc.mono (by omega)
      · exact (hrest f hf).mono hn₃
    · refine ok_bind (ih _ _ hp hq hc) (by omega)
        fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hc.mono (by omega)
      · exact (hrest f hf).mono hn₃

theorem subW_xor3W {x y z : Word m} {n : ℕ} (hx : S.SubW x n) (hy : S.SubW y n)
    (hz : S.SubW z n) : S.SubW (xor3W x y z) n := by
  intro i
  rw [xor3W, Fin.getElem_fin, Vector.getElem_ofFn]
  exact ((hx i).xor (hy i)).xor (hz i)

theorem subW_shiftW {ms : List (Form m)} {n : ℕ} (h : S.SubL ms n) : S.SubW (shiftW ms) n := by
  intro i
  rw [shiftW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · exact subN_zero n
  · exact subN_getD h _

/-- The fused three-operand adder records `61` gates and its output reads only available
positions. -/
theorem ok_add3W {n₀ : ℕ} {x y z : Word m} (hx : S.SubW x n₀) (hy : S.SubW y n₀)
    (hz : S.SubW z n₀) : S.Ok n₀ (add3W x y z) 61 S.SubW := by
  rw [add3W]
  refine ok_bind (ok_majorities x y z 31 n₀ hx hy hz) (by omega) fun ms n₁ hn₁ hms ↦ ?_
  have hp := subW_xor3W (hx.mono hn₁) (hy.mono hn₁) (hz.mono hn₁)
  exact ok_map ((ok_rippleCarries _ _ 31 0 n₁ hp (subW_shiftW hms) (subN_zero _)).cast rfl)
    fun _ _ hn hcs ↦ subW_sumW (hp.mono hn) ((subW_shiftW hms).mono hn) hcs

end Start

end ProductCircuit

end SpartanChain
