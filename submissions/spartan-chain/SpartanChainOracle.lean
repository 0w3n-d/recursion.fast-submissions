import RecursionFast.Contract.Security
import RecursionFast.Library.Oracle

/-!
# Query programs: composition, the log view, and the query byte formats

The contract's `OProg` (`Contract/Oracle.lean`) has only `ret` and `query`. This module adds:

* `OProg.bind` and a lawful `Monad OProg` instance, so the verifier and the prover are written in
  `do` notation; the run, query-list and log-run lemmas of `bind`, `map` and `mapM`
  (`run_bind`, `queries_bind`, `runLog_bind`, …);
* `ask q`, the single query;
* **the log view** (`logOracle`, `runLog_eq_some_iff`): a program run on a log `L` returns `b`
  exactly when every query it asks under the oracle `logOracle L` (the first answer of `L` for each
  query) is in `L` and its run under that oracle returns `b`. A run on a log is therefore a run
  under one oracle function, whose queries, in order, are entries of the log (L-K4 reads the
  verifier's Fiat–Shamir chain off this);
* the byte helpers and **every query format** of the entry (BLUEPRINT-R1 §5.3, §6.1), in one
  place: Merkle leaves `0x00 ‖ column`, nodes `0x01 ‖ λₗ ‖ λᵣ`, the transcript seed `0x10 ‖ s ‖
  enc64 n ‖ h`, absorbs `0x20 ‖ st ‖ kind ‖ msg` and squeezes `0x30 ‖ st`; 31-byte labels.
-/

namespace SpartanChain
open RecursionFast

namespace OProg
variable {α β γ : Type}

/-- Sequential composition: run `p`, then `f` on its result. -/
def bind : OProg α → (α → OProg β) → OProg β
  | .ret a, f => f a
  | .query q k, f => .query q fun d => bind (k d) f

instance : Monad OProg where
  pure := .ret
  bind := bind

@[simp] theorem ret_bind (a : α) (f : α → OProg β) : (OProg.ret a >>= f) = f a := rfl

@[simp] theorem query_bind (q : ByteArray) (k : Digest → OProg α) (f : α → OProg β) :
    (OProg.query q k >>= f) = .query q fun d => k d >>= f := rfl

theorem pure_eq_ret (a : α) : (pure a : OProg α) = .ret a := rfl

instance : LawfulMonad OProg := LawfulMonad.mk' OProg
  (fun x => by
    induction x with
    | ret a => rfl
    | query q k ih => exact congrArg (OProg.query q) (funext ih))
  (fun _ _ => rfl)
  (fun x f g => by
    induction x with
    | ret a => rfl
    | query q k ih => exact congrArg (OProg.query q) (funext ih))

/-- One query: ask `q`, return its answer. -/
def ask (q : ByteArray) : OProg Digest := .query q .ret

/-! ## Runs under an oracle -/

section run
variable (H : ByteArray → Digest)

@[simp] theorem run_pure (a : α) : (pure a : OProg α).run H = a := rfl

@[simp] theorem run_bind (p : OProg α) (f : α → OProg β) :
    (p >>= f).run H = (f (p.run H)).run H := by
  induction p with
  | ret a => rfl
  | query q k ih => exact ih (H q)

@[simp] theorem run_map (p : OProg α) (f : α → β) : (f <$> p).run H = f (p.run H) := by
  rw [← bind_pure_comp, run_bind]; rfl

@[simp] theorem run_ask (q : ByteArray) : (ask q).run H = H q := rfl

@[simp] theorem queries_pure (a : α) : (pure a : OProg α).queries H = [] := rfl

@[simp] theorem queries_bind (p : OProg α) (f : α → OProg β) :
    (p >>= f).queries H = p.queries H ++ (f (p.run H)).queries H := by
  induction p with
  | ret a => rfl
  | query q k ih => simp only [query_bind, RecursionFast.OProg.queries, RecursionFast.OProg.run, ih,
      List.cons_append]

@[simp] theorem queries_map (p : OProg α) (f : α → β) : (f <$> p).queries H = p.queries H := by
  rw [← bind_pure_comp, queries_bind]; simp

@[simp] theorem queries_ask (q : ByteArray) : (ask q).queries H = [q] := rfl

@[simp] theorem run_mapM (f : α → OProg β) (xs : List α) :
    (xs.mapM f).run H = xs.map fun x => (f x).run H := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

@[simp] theorem queries_mapM (f : α → OProg β) (xs : List α) :
    (xs.mapM f).queries H = xs.flatMap fun x => (f x).queries H := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

@[simp] theorem run_arrayMapM (f : α → OProg β) (xs : Array α) :
    (xs.mapM f).run H = xs.map fun x => (f x).run H := by
  rw [Array.mapM_eq_mapM_toList, run_map, run_mapM]
  cases xs; simp

@[simp] theorem queries_arrayMapM (f : α → OProg β) (xs : Array α) :
    (xs.mapM f).queries H = xs.toList.flatMap fun x => (f x).queries H := by
  rw [Array.mapM_eq_mapM_toList, queries_map, queries_mapM]

end run

/-! ## Runs on a log -/

section runLog
variable (L : Log)

@[simp] theorem runLog_pure (a : α) : (pure a : OProg α).runLog L = some a := rfl

@[simp] theorem runLog_bind (p : OProg α) (f : α → OProg β) :
    (p >>= f).runLog L = (p.runLog L).bind fun a => (f a).runLog L := by
  induction p with
  | ret a => rfl
  | query q k ih =>
    simp only [query_bind, RecursionFast.OProg.runLog]
    cases L.find? (fun e => decide (e.1 = q)) <;> simp [ih]

@[simp] theorem runLog_map (p : OProg α) (f : α → β) :
    (f <$> p).runLog L = (p.runLog L).map f := by
  rw [← bind_pure_comp, runLog_bind]; cases p.runLog L <;> rfl

@[simp] theorem runLog_ask (q : ByteArray) :
    (ask q).runLog L = (L.find? fun e => decide (e.1 = q)).map Prod.snd := by
  simp only [ask, RecursionFast.OProg.runLog]; cases L.find? (fun e => decide (e.1 = q)) <;> rfl

/-- **The log as an oracle**: the answer of the first entry of `L` for `q` (an arbitrary digest
if there is none). -/
def logOracle (q : ByteArray) : Digest :=
  ((L.find? fun e => decide (e.1 = q)).map Prod.snd).getD default

variable {L}

/-- A query of the log is answered by `logOracle` from its first entry. -/
theorem find?_logOracle {q : ByteArray} (hq : q ∈ L.map Prod.fst) :
    L.find? (fun e => decide (e.1 = q)) = some (q, logOracle L q) := by
  cases hf : L.find? (fun e => decide (e.1 = q)) with
  | none =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    simpa using List.find?_eq_none.mp hf e he
  | some e =>
    have h1 : e.1 = q := by simpa using List.find?_some hf
    subst h1
    simp [logOracle, hf]

/-- The entry `(q, logOracle L q)` is in the log when `q` is. -/
theorem mem_logOracle {q : ByteArray} (hq : q ∈ L.map Prod.fst) : (q, logOracle L q) ∈ L :=
  List.mem_of_find?_eq_some (find?_logOracle hq)

/-- On a log consistent with `H`, `logOracle` agrees with `H` on the log's queries. -/
theorem logOracle_eq {H : ByteArray → Digest} (hc : ∀ e ∈ L, e.2 = H e.1) {q : ByteArray}
    (hq : q ∈ L.map Prod.fst) : logOracle L q = H q :=
  hc _ (mem_logOracle hq)

/-- **The log view of a run.** A program returns `b` on the log `L` iff every query it asks
under `logOracle L` is in `L` and its run under `logOracle L` returns `b`. -/
theorem runLog_eq_some_iff (p : OProg α) (b : α) :
    p.runLog L = some b ↔
      (∀ q ∈ p.queries (logOracle L), q ∈ L.map Prod.fst) ∧ p.run (logOracle L) = b := by
  induction p with
  | ret a => simp [RecursionFast.OProg.runLog, RecursionFast.OProg.queries, RecursionFast.OProg.run]
  | query q k ih =>
    by_cases hq : q ∈ L.map Prod.fst
    · simp only [RecursionFast.OProg.runLog, find?_logOracle hq, Option.bind_some, ih,
        RecursionFast.OProg.queries, RecursionFast.OProg.run,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨fun h => ⟨⟨hq, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    · have hn : L.find? (fun e => decide (e.1 = q)) = none := by
        rw [List.find?_eq_none]
        intro e he h
        exact hq (List.mem_map.mpr ⟨e, he, by simpa using h⟩)
      simp only [RecursionFast.OProg.runLog, hn, Option.bind_none, RecursionFast.OProg.queries,
        List.mem_cons, forall_eq_or_imp]
      simp [hq]

/-- A run on a log is unchanged by appending entries. -/
theorem runLog_append {p : OProg α} {b : α} (L' : Log) (h : p.runLog L = some b) :
    p.runLog (L ++ L') = some b := by
  induction p with
  | ret a => exact h
  | query q k ih =>
    simp only [RecursionFast.OProg.runLog] at h ⊢
    cases hf : L.find? (fun e => decide (e.1 = q)) with
    | none => simp [hf] at h
    | some e =>
      rw [hf, Option.bind_some] at h
      rw [List.find?_append, hf]
      exact ih e.2 h

end runLog

end OProg

/-! ## Bytes, labels and the query formats (BLUEPRINT-R1 §5.3, §6.1) -/

/-- The bytes of a byte vector. -/
def bytesOf {n : ℕ} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

@[simp] theorem size_bytesOf {n : ℕ} (v : Vector UInt8 n) : (bytesOf v).size = n := by
  simp [bytesOf, ByteArray.size]

/-- A Merkle label: the first 31 bytes of an answer (`[D-8]`). -/
abbrev Label := Vector UInt8 31

/-- `[a]₃₁`: the label of an answer, its first 31 bytes. -/
def trunc (a : Digest) : Label := ⟨a.toArray.extract 0 31, by simp⟩

/-- The query of a Merkle leaf: `0x00 ‖ column bytes`. -/
def leafQ (col : ByteArray) : ByteArray := ⟨#[0x00]⟩ ++ col

/-- The query of a Merkle node: `0x01 ‖ λₗ ‖ λᵣ` (63 bytes). -/
def nodeQ (l r : Label) : ByteArray := ⟨#[0x01] ++ l.toArray ++ r.toArray⟩

/-- The transcript seed: `0x10 ‖ s ‖ enc64 n ‖ h` (73 bytes). -/
def seedQ (s : Digest) (n : ℕ) (h : Digest) : ByteArray :=
  ⟨#[0x10] ++ s.toArray ++ (enc64 n).toArray ++ h.toArray⟩

/-- An absorb: `0x20 ‖ st ‖ kind ‖ msg`. -/
def absorbQ (st : Digest) (kind : UInt8) (msg : ByteArray) : ByteArray :=
  ⟨#[0x20] ++ st.toArray ++ #[kind]⟩ ++ msg

/-- A squeeze: `0x30 ‖ st` (33 bytes). -/
def squeezeQ (st : Digest) : ByteArray := ⟨#[0x30] ++ st.toArray⟩

@[simp] theorem leafQ_data (col : ByteArray) : (leafQ col).data.toList = 0x00 :: col.data.toList := by
  simp [leafQ, ByteArray.data_append]

@[simp] theorem nodeQ_data (l r : Label) :
    (nodeQ l r).data.toList = 0x01 :: (l.toList ++ r.toList) := by
  simp [nodeQ, Vector.toList]

@[simp] theorem seedQ_data (s : Digest) (n : ℕ) (h : Digest) :
    (seedQ s n h).data.toList = 0x10 :: (s.toList ++ enc64 n ++ h.toList) := by
  simp [seedQ, Vector.toList]

@[simp] theorem absorbQ_data (st : Digest) (kind : UInt8) (msg : ByteArray) :
    (absorbQ st kind msg).data.toList = 0x20 :: (st.toList ++ kind :: msg.data.toList) := by
  simp [absorbQ, ByteArray.data_append, Vector.toList]

@[simp] theorem squeezeQ_data (st : Digest) : (squeezeQ st).data.toList = 0x30 :: st.toList := by
  simp [squeezeQ, Vector.toList]

/-- Byte arrays are equal when their byte lists are. -/
theorem ByteArray.ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

/-- The first byte of a query, its domain tag. -/
def tagOf (q : ByteArray) : Option UInt8 := q.data.toList.head?

@[simp] theorem tagOf_leafQ (c : ByteArray) : tagOf (leafQ c) = some 0x00 := by simp [tagOf]
@[simp] theorem tagOf_nodeQ (l r : Label) : tagOf (nodeQ l r) = some 0x01 := by simp [tagOf]
@[simp] theorem tagOf_seedQ (s : Digest) (n : ℕ) (h : Digest) : tagOf (seedQ s n h) = some 0x10 := by
  simp [tagOf]
@[simp] theorem tagOf_absorbQ (st : Digest) (k : UInt8) (m : ByteArray) :
    tagOf (absorbQ st k m) = some 0x20 := by simp [tagOf]
@[simp] theorem tagOf_squeezeQ (st : Digest) : tagOf (squeezeQ st) = some 0x30 := by simp [tagOf]

end SpartanChain
