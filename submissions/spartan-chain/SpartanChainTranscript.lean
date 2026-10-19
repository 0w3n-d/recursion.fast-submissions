import SpartanChainMerkle
import SpartanChainFieldExtCorrect
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Fiat–Shamir transcript over the oracle (BLUEPRINT-R1 §6)

* The state is one full answer (32 bytes). `seed s n h` asks `0x10 ‖ s ‖ enc64 n ‖ h`;
  `absorb st kind msg` asks `0x20 ‖ st ‖ kind ‖ msg`; `squeeze st` asks `0x30 ‖ st`. Each returns
  the answer, which is the new state (and, for a squeeze, the challenge source).
* `chE a`: the `EF` element of the first 24 bytes of an answer (three little-endian words,
  coefficient `0` first).
* Column indices: `cnt ℓ = ⌊256 / ℓ⌋` indices of `ℓ` bits per answer; index `i` of the answer `a`
  is bits `[i ℓ, (i + 1) ℓ)` of `a` read little-endian (`idxOf`, `idxOf_testBit`); `t` indices
  take `⌈t / cnt ℓ⌉` squeezes (`squeezeIdx`).

**The fiber-count lemmas** (exact uniformity, §6.1):
* `card_chE_fiber`: every `x : EF` has exactly `2^64` answers `a` with `chE a = x`;
* `card_idx_fiber`: for `ℓ c ≤ 256`, every tuple of `c` indices below `2^ℓ` is the first `c`
  indices of exactly `2^(256 − ℓ c)` answers (uniform and independent);
* `card_chE_mem`, `card_idx_mem`: the same for a set of values (`|S|` times the fiber).
The decoder is abstract in `card_fiber_dec24`: any bijection `Vector UInt8 24 → β`.

**The log side** (§9.1 as revised after review BP-M2): the query fields `stateIn` and `seedOf`
(with `labelsIn` in `SpartanChainMerkle`), the bad events `Bad = Collision ∨ Hit ∨ StateHit ∨
Repeated`, monotone under appending (`bad_append`), and **L-K7** `pred_unique_lt`: under `¬ Bad`,
the entry answering the state of an absorb or squeeze entry is unique and earlier.
-/

namespace SpartanChain
open RecursionFast

namespace Transcript

/-! ## The operations -/

/-- The initial state: the answer to `0x10 ‖ s ‖ enc64 n ‖ h`. -/
def seed (s : Digest) (n : ℕ) (h : Digest) : OProg Digest := OProg.ask (seedQ s n h)

/-- Absorb a prover message: the answer to `0x20 ‖ st ‖ kind ‖ msg`. -/
def absorb (st : Digest) (kind : UInt8) (msg : ByteArray) : OProg Digest :=
  OProg.ask (absorbQ st kind msg)

/-- Squeeze: the answer to `0x30 ‖ st`, the new state and the challenge source. -/
def squeeze (st : Digest) : OProg Digest := OProg.ask (squeezeQ st)

/-- `k` squeezes in a row: the final state and the `k` answers. -/
def squeezeN : Digest → ℕ → OProg (Digest × List Digest)
  | st, 0 => pure (st, [])
  | st, k + 1 => do
    let a ← squeeze st
    let r ← squeezeN a k
    pure (r.1, a :: r.2)

/-- The field challenge of an answer: bytes `0..24` as `c₀ + c₁ y + c₂ y²`. -/
def chE (a : Digest) : EF := EF.ofBytes (Vector.ofFn fun i : Fin 24 => a[i.1])

/-- `k` field challenges, one per squeeze: the final state and the challenges. -/
def squeezeE (st : Digest) (k : ℕ) : OProg (Digest × List EF) := do
  let r ← squeezeN st k
  pure (r.1, r.2.map chE)

/-- The little-endian integer of an answer. -/
def natLE (a : Digest) : ℕ := ∑ i : Fin 32, a[i.1].toNat * 256 ^ i.1

/-- Index `i` of `ℓ` bits of the answer `a`: bits `[i ℓ, (i + 1) ℓ)` of `natLE a`. -/
def idxOf (ℓ : ℕ) (a : Digest) (i : ℕ) : ℕ := natLE a / 2 ^ (i * ℓ) % 2 ^ ℓ

/-- Indices per answer: `⌊256 / ℓ⌋`. -/
def cnt (ℓ : ℕ) : ℕ := 256 / ℓ

/-- Answers for `t` indices: `⌈t / cnt ℓ⌉`. -/
def nAns (ℓ t : ℕ) : ℕ := (t + cnt ℓ - 1) / cnt ℓ

/-- The `t` indices read off the answers `ans`, `cnt ℓ` per answer, in order. -/
def indices (ℓ t : ℕ) (ans : List Digest) : List ℕ :=
  (List.range t).map fun i => idxOf ℓ ans[i / cnt ℓ]! (i % cnt ℓ)

/-- Squeeze the column indices: `nAns ℓ t` squeezes, `t` indices of `ℓ` bits. -/
def squeezeIdx (st : Digest) (ℓ t : ℕ) : OProg (Digest × List ℕ) := do
  let r ← squeezeN st (nAns ℓ t)
  pure (r.1, indices ℓ t r.2)

/-! ## Runs and queries -/

section run
variable (H : ByteArray → Digest)

@[simp] theorem run_squeezeN_fst (st : Digest) (k : ℕ) :
    ((squeezeN st k).run H).2.length = k := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => simp [squeezeN, squeeze, ih]

/-- The answers of `k` squeezes are the iterates of `H ∘ squeezeQ`. -/
theorem run_squeezeN (st : Digest) (k : ℕ) :
    (squeezeN st k).run H =
      ((fun d => H (squeezeQ d))^[k] st,
        (List.range k).map fun i => (fun d => H (squeezeQ d))^[i + 1] st) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [squeezeN, squeeze, OProg.run_bind, OProg.run_ask, ih, OProg.run_pure,
      Function.iterate_succ_apply, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, Function.iterate_zero_apply]

/-- The queries of `k` squeezes: `squeezeQ` of each state in turn. -/
theorem queries_squeezeN (st : Digest) (k : ℕ) :
    (squeezeN st k).queries H =
      (List.range k).map fun i => squeezeQ ((fun d => H (squeezeQ d))^[i] st) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [squeezeN, squeeze, OProg.queries_bind, OProg.queries_ask, OProg.run_ask, ih,
      OProg.queries_pure, List.append_nil, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, Function.iterate_succ_apply, Function.iterate_zero_apply,
      List.singleton_append]

theorem length_indices (ℓ t : ℕ) (ans : List Digest) : (indices ℓ t ans).length = t := by
  simp [indices]

end run

/-! ## The fiber-count lemmas -/

/-- An equivalence onto a product has fibers of the size of the other factor. -/
theorem card_fiber_snd {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (e : α ≃ β × γ) (c : γ) :
    (Finset.univ.filter fun a => (e a).2 = c).card = Fintype.card β := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun a => (e a.1).1
      invFun := fun b => ⟨e.symm (b, c), by simp⟩
      left_inv := fun ⟨a, ha⟩ => by subst ha; simp
      right_inv := fun b => by simp }

/-- A byte vector as a function to `Fin 256`. -/
def vecEquiv (n : ℕ) : Vector UInt8 n ≃ (Fin n → Fin 256) where
  toFun a i := a[i.1].toFin
  invFun f := Vector.ofFn fun i => UInt8.ofFin (f i)
  left_inv a := by ext i hi; simp
  right_inv f := by funext i; simp

/-- A digest as its first 24 and last 8 bytes. -/
def split24 : Digest ≃ (Fin 8 → Fin 256) × (Fin 24 → Fin 256) :=
  (vecEquiv 32).trans <| (Equiv.arrowCongr (finSumFinEquiv (m := 24) (n := 8)).symm
    (Equiv.refl _)).trans <| (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodComm _ _)

theorem split24_snd (a : Digest) (i : Fin 24) : (split24 a).2 i = a[i.1].toFin := by
  simp [split24, vecEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]
  rfl

/-- **Fiber count for a 24-byte decoder** (abstract): if `dec` is a bijection from 24 bytes,
every value has exactly `2^64` answers whose first 24 bytes decode to it. -/
theorem card_fiber_dec24 {β : Type} [DecidableEq β] (dec : Vector UInt8 24 → β) (hdec : Function.Bijective dec)
    (x : β) :
    (Finset.univ.filter fun a : Digest => dec (Vector.ofFn fun i : Fin 24 => a[i.1]) = x).card
      = 2 ^ 64 := by
  obtain ⟨v, rfl⟩ := hdec.2 x
  have : (Finset.univ.filter fun a : Digest => dec (Vector.ofFn fun i : Fin 24 => a[i.1]) = dec v)
      = Finset.univ.filter fun a => (split24 a).2 = fun i => v[i.1].toFin := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdec.1.eq_iff]
    constructor
    · rintro rfl; funext i; simp [split24_snd]
    · intro h; ext i hi
      have := congrFun h ⟨i, hi⟩
      simp only [split24_snd, UInt8.toFin_inj] at this
      simp [this]
  rw [this, card_fiber_snd]
  simp

/-- `EF.ofBytes` is a bijection (it is onto, and both sides have `2^192` elements). -/
theorem ofBytes_bijective : Function.Bijective EF.ofBytes := by
  have : Finite (Vector UInt8 24) := Finite.of_equiv _ (vecEquiv 24).symm
  apply Function.Surjective.bijective_of_nat_card_le
  · intro x; exact ⟨EF.toBytes x, EF.ofBytes_toBytes x⟩
  · rw [EF.nat_card_EF, Nat.card_congr (vecEquiv 24), Nat.card_eq_fintype_card]
    simp

/-- **Fiber count of `chE`**: every field element is the challenge of exactly `2^64` answers;
`chE` of a uniform answer is uniform on `EF`. -/
theorem card_chE_fiber (x : EF) :
    (Finset.univ.filter fun a : Digest => chE a = x).card = 2 ^ 64 :=
  card_fiber_dec24 EF.ofBytes ofBytes_bijective x

/-- A function with all fibers of size `k` takes values in `S` on `|S| k` points. -/
theorem card_mem_of_fiber {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (k : ℕ)
    (hf : ∀ b, (Finset.univ.filter fun a => f a = b).card = k) (S : Finset β) :
    (Finset.univ.filter fun a => f a ∈ S).card = S.card * k := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S) (fun a ha => by simpa using ha)]
  have hS : ∀ b ∈ S, ((Finset.univ.filter fun a => f a ∈ S).filter fun a => f a = b).card = k := by
    intro b hb
    rw [Finset.filter_filter, ← hf b]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact hb
  rw [Finset.sum_congr rfl hS, Finset.sum_const, smul_eq_mul]

/-- `chE` lands in `S` on exactly `|S| · 2^64` answers. -/
theorem card_chE_mem (S : Finset EF) :
    (Finset.univ.filter fun a : Digest => chE a ∈ S).card = S.card * 2 ^ 64 :=
  card_mem_of_fiber chE _ card_chE_fiber S

/-- A digest as a number below `2^256`, little-endian. -/
def natEquiv : Digest ≃ Fin (2 ^ 256) :=
  (vecEquiv 32).trans <| finFunctionFinEquiv.trans (finCongr (by norm_num))

theorem natEquiv_val (a : Digest) : (natEquiv a : ℕ) = natLE a := by
  simp only [natEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rw [finFunctionFinEquiv_apply]
  simp [natLE, vecEquiv]

/-- `natLE a / 2^(i ℓ) % 2^ℓ` is digit `i` of `natLE a mod 2^(ℓ c)` in base `2^ℓ`, for `i < c`. -/
theorem digit_eq (x ℓ c i : ℕ) (hi : i < c) :
    x % (2 ^ ℓ) ^ c / (2 ^ ℓ) ^ i % 2 ^ ℓ = x / 2 ^ (i * ℓ) % 2 ^ ℓ := by
  have hc : (2 ^ ℓ) ^ c = (2 ^ ℓ) ^ i * (2 ^ ℓ) ^ (c - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hc, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self _ (by omega)),
    ← pow_mul, mul_comm ℓ i]

/-- A digest as its high part and its first `c` indices of `ℓ` bits. -/
def idxEquiv (ℓ c : ℕ) (h : ℓ * c ≤ 256) :
    Digest ≃ Fin (2 ^ (256 - ℓ * c)) × (Fin c → Fin (2 ^ ℓ)) :=
  natEquiv.trans <| (finCongr (by rw [← pow_mul, ← pow_add]; congr 1; omega)).trans <|
    finProdFinEquiv.symm.trans <| Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv.symm

theorem idxEquiv_snd (ℓ c : ℕ) (h : ℓ * c ≤ 256) (a : Digest) (i : Fin c) :
    ((idxEquiv ℓ c h a).2 i : ℕ) = idxOf ℓ a i := by
  simp only [idxEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
    finProdFinEquiv_symm_apply, finFunctionFinEquiv_symm_apply_val, Fin.coe_modNat,
    finCongr_apply, Fin.val_cast, natEquiv_val, idxOf]
  exact digit_eq _ _ _ _ i.2

/-- The first `c` indices of `ℓ` bits of an answer, as a tuple. -/
def idxVec (ℓ c : ℕ) (a : Digest) : Fin c → Fin (2 ^ ℓ) :=
  fun i => ⟨idxOf ℓ a i, Nat.mod_lt _ (by positivity)⟩

/-- **Fiber count of the indices**: for `ℓ c ≤ 256`, every tuple of `c` indices below `2^ℓ` is
the first `c` indices of exactly `2^(256 − ℓ c)` answers; the indices of a uniform answer are
uniform and independent. -/
theorem card_idx_fiber (ℓ c : ℕ) (h : ℓ * c ≤ 256) (t : Fin c → Fin (2 ^ ℓ)) :
    (Finset.univ.filter fun a : Digest => idxVec ℓ c a = t).card = 2 ^ (256 - ℓ * c) := by
  have : (Finset.univ.filter fun a : Digest => idxVec ℓ c a = t) =
      Finset.univ.filter fun a => (idxEquiv ℓ c h a).2 = t := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h' <;> funext i <;> have := congrFun h' i <;> apply Fin.ext <;>
      simp only [idxVec, Fin.ext_iff, idxEquiv_snd] at this ⊢ <;> exact this
  rw [this, card_fiber_snd]
  simp

/-- The index tuple lands in `S` on exactly `|S| · 2^(256 − ℓ c)` answers. -/
theorem card_idx_mem (ℓ c : ℕ) (h : ℓ * c ≤ 256) (S : Finset (Fin c → Fin (2 ^ ℓ))) :
    (Finset.univ.filter fun a : Digest => idxVec ℓ c a ∈ S).card = S.card * 2 ^ (256 - ℓ * c) :=
  card_mem_of_fiber (idxVec ℓ c) _ (card_idx_fiber ℓ c h) S

/-- **The bit layout of an index** (§6.1): bit `j < ℓ` of index `i` is bit `(i ℓ + j) mod 8` of
byte `⌊(i ℓ + j) / 8⌋` of the answer, when that byte exists. -/
theorem idxOf_testBit (ℓ : ℕ) (a : Digest) (i j : ℕ) (hj : j < ℓ) (hb : i * ℓ + j < 256) :
    (idxOf ℓ a i).testBit j = a[(i * ℓ + j) / 8].toNat.testBit ((i * ℓ + j) % 8) := by
  have hdig : ∀ k (hk : k < 32), natLE a / 256 ^ k % 256 = a[k].toNat := by
    intro k hk
    have h := finFunctionFinEquiv_symm_apply_val (m := 256) (n := 32)
      (finFunctionFinEquiv fun i : Fin 32 => a[i.1].toFin) ⟨k, hk⟩
    rw [Equiv.symm_apply_apply, finFunctionFinEquiv_apply] at h
    simpa [natLE] using h.symm
  set b := i * ℓ + j
  have hk : b / 8 < 32 := by omega
  rw [idxOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hj, Bool.true_and,
    ← hdig _ hk, show (256 : ℕ) ^ (b / 8) = 2 ^ (8 * (b / 8)) by rw [pow_mul]; norm_num,
    show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    decide_eq_true (Nat.mod_lt _ (by norm_num)), Bool.true_and]
  congr 1
  omega

/-! ## The bad events of the log (§9.1, with BP-M2)

`Bad L` is a collision of labels, a label hit (both in `SpartanChainMerkle`), a **state hit**
(an answer equal to the state field of an absorb or squeeze query asked before it or by the same
entry) or a **repeated query**. Under `¬ Bad L`, the entry whose answer is the state of an
absorb or squeeze query comes strictly earlier in the log (`pred_before`), answers determine
queries (`query_eq_of_answer`), and every query has one entry (`entry_unique`).
-/

/-- The state field of an absorb (`0x20 ‖ st ‖ kind ‖ msg`) or squeeze (`0x30 ‖ st`) query. -/
def stateIn (q : ByteArray) : Option Digest :=
  match q.data.toList with
  | b :: rest =>
    if h : (b = 0x20 ∧ 33 ≤ rest.length) ∨ (b = 0x30 ∧ rest.length = 32) then
      some ⟨(rest.take 32).toArray, by simp; omega⟩
    else none
  | [] => none

theorem stateIn_absorbQ (st : Digest) (kind : UInt8) (msg : ByteArray) :
    stateIn (absorbQ st kind msg) = some st := by
  simp only [stateIn, absorbQ_data]
  split
  · congr 1; apply Vector.toArray_inj.mp; simp [Vector.toList]
  · rename_i h; exact absurd (Or.inl ⟨trivial, by simp; omega⟩) h

theorem stateIn_squeezeQ (st : Digest) : stateIn (squeezeQ st) = some st := by
  simp only [stateIn, squeezeQ_data]
  split
  · congr 1; apply Vector.toArray_inj.mp; simp [Vector.toList, List.take_of_length_le]
  · rename_i h; exact absurd (Or.inr ⟨trivial, by simp⟩) h

/-- *State hit*: an answer equal to the state field of a query asked before it **or by the same
entry** (`i ≤ j`; §9.1 (iii) has `i < j`, which leaves an entry answering its own state, so that
`pred_L(e) = e`; the extra case costs one answer per step). -/
def StateHit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i ≤ j) (hj : j < L.length),
    stateIn (L[i]'(Nat.lt_of_le_of_lt hij hj)).1 = some L[j].2

/-- *Repeated query*: two entries with the same query. -/
def Repeated (L : Log) : Prop := ¬ (L.map Prod.fst).Nodup

/-- **The bad events of a log** (§9.1 (i)–(iv): collision, label hit, state hit, repeat). -/
def Bad (L : Log) : Prop :=
  Merkle.Collision L ∨ Merkle.Hit L ∨ StateHit L ∨ Repeated L

/-- The seed `(s, n, h)` of a seed query `0x10 ‖ s ‖ enc64 n ‖ h` (73 bytes). -/
def seedOf (q : ByteArray) : Option (Digest × ℕ × Digest) :=
  match q.data.toList with
  | b :: rest =>
    if h : b = 0x10 ∧ rest.length = 72 then
      some (⟨(rest.take 32).toArray, by simp; omega⟩,
        ((rest.drop 32).take 8).foldr (fun x acc => x.toNat + 256 * acc) 0,
        ⟨(rest.drop 40).toArray, by simp; omega⟩)
    else none
  | [] => none

theorem foldr_enc (k n : ℕ) :
    (List.ofFn fun i : Fin k => (n / 256 ^ i.1).toUInt8).foldr
      (fun x acc => x.toNat + 256 * acc) 0 = n % 256 ^ k := by
  induction k generalizing n with
  | zero => rw [pow_zero, Nat.mod_one]; rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.foldr_cons]
    have : (fun i : Fin k => (n / 256 ^ (i.succ : ℕ)).toUInt8) =
        fun i : Fin k => (n / 256 / 256 ^ i.1).toUInt8 := by
      funext i; rw [Nat.div_div_eq_div_mul, Fin.val_succ, pow_succ']
    rw [this, ih, pow_succ', Nat.mod_mul]
    simp [Nat.toUInt8]

theorem seedOf_seedQ (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) (h : Digest) :
    seedOf (seedQ s n h) = some (s, n, h) := by
  simp only [seedOf, seedQ_data]
  split
  · refine congrArg some (Prod.ext ?_ (Prod.ext ?_ ?_))
    · apply Vector.toArray_inj.mp; simp [Vector.toList, enc64]
    · simp only [List.append_assoc, List.drop_left' (show s.toList.length = 32 by simp)]
      rw [List.take_left' (by simp [enc64]), enc64, foldr_enc, Nat.mod_eq_of_lt (by simpa using hn)]
    · apply Vector.toArray_inj.mp
      simp [Vector.toList, enc64, List.drop_append,
        List.drop_eq_nil_of_le (as := s.toArray.toList) (i := 40) (by simp)]
  · rename_i hc; exact absurd ⟨trivial, by simp [enc64]⟩ hc

/-- Under no state hit, the entry answering the state of an absorb or squeeze entry is earlier. -/
theorem pred_before {L : Log} (hb : ¬ StateHit L) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) {st : Digest} (hst : stateIn L[j].1 = some st) (ha : L[i].2 = st) :
    i < j := by
  by_contra hji
  exact hb ⟨j, i, by omega, hi, by rw [hst, ha]⟩

theorem stateHit_append {L : Log} (L' : Log) (h : StateHit L) : StateHit (L ++ L') := by
  obtain ⟨i, j, hij, hj, hm⟩ := h
  refine ⟨i, j, hij, by simp; omega, ?_⟩
  rwa [List.getElem_append_left hj, List.getElem_append_left (Nat.lt_of_le_of_lt hij hj)]

/-- `Bad` is monotone under appending. -/
theorem bad_append {L : Log} (L' : Log) (h : Bad L) : Bad (L ++ L') := by
  rcases h with h | h | h | h
  · exact Or.inl (Merkle.collision_append L' h)
  · exact Or.inr (Or.inl (Merkle.hit_append L' h))
  · exact Or.inr (Or.inr (Or.inl (stateHit_append L' h)))
  · refine Or.inr (Or.inr (Or.inr fun hn => h ?_))
    rw [List.map_append] at hn
    exact hn.sublist (List.sublist_append_left _ _)

/-- **L-K7 `pred_unique_lt`**: under `¬ Bad`, at most one entry answers the state of an absorb
or squeeze entry, and it is earlier. -/
theorem pred_unique_lt {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) {st : Digest}
    (hst : stateIn L[j].1 = some st) :
    (∀ i i' (hi : i < L.length) (hi' : i' < L.length), L[i].2 = st → L[i'].2 = st → i = i') ∧
      ∀ i (hi : i < L.length), L[i].2 = st → i < j := by
  refine ⟨fun i i' hi hi' h h' => ?_, fun i hi h => ?_⟩
  · have hq : L[i].1 = L[i'].1 := by
      by_contra hne
      exact hb (Or.inl ⟨L[i], List.getElem_mem hi, L[i'], List.getElem_mem hi', hne,
        by rw [h, h']⟩)
    have hn : (L.map Prod.fst).Nodup := by
      by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
    exact (List.Nodup.getElem_inj_iff hn (i := i) (j := i') (hi := by simpa using hi)
      (hj := by simpa using hi')).mp (by simpa using hq)
  · by_contra hji
    exact hb (Or.inr (Or.inr (Or.inl ⟨j, i, by omega, hi, by rw [hst, h]⟩)))

/-- Under no collision, equal answers come from equal queries. -/
theorem query_eq_of_answer {L : Log} (hc : ¬ Merkle.Collision L) {e₁ e₂ : ByteArray × Digest}
    (h₁ : e₁ ∈ L) (h₂ : e₂ ∈ L) (h : e₁.2 = e₂.2) : e₁.1 = e₂.1 := by
  by_contra hne
  exact hc ⟨e₁, h₁, e₂, h₂, hne, by rw [h]⟩

/-- Without repeated queries, an entry of the log is the first entry for its query. -/
theorem entry_unique {L : Log} (hr : ¬ Repeated L) {e : ByteArray × Digest} (he : e ∈ L) :
    L.find? (fun x => decide (x.1 = e.1)) = some e := by
  have hn : (L.map Prod.fst).Nodup := not_not.mp hr
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp⟩ : (L.find? fun x => decide (x.1 = e.1)).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have hq : e'.1 = e.1 := by simpa using List.find?_some he'
  rw [he']
  congr 1
  exact (List.inj_on_of_nodup_map hn hm he hq)

end Transcript

end SpartanChain
