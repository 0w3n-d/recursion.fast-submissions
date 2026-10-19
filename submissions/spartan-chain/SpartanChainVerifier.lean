import SpartanChainSpartanProtocol
import SpartanChainVerifierTop

/-!
# The leaf SNARK verifier (BLUEPRINT-R1 §1.3 step 3, §6.2, §7, §9.2 checks (a)–(f), L-Q1)

`snarkProg ev s n h π_S` is the whole §6.2 sequence on the SNARK bytes `π_S` of a leaf with
`n ≥ 1` steps, `κ = ⌈log₂ n⌉` (`kap`):

1. `st ← seed s n h` (`Transcript.seed`, binding `s`, `n`, `h`);
2. steps 2–4: `Ligero.verify1` (absorb the root, squeeze `r`, absorb `ū`);
3. steps 5–10: `Spartan.verify` (checks (a)–(e) of §9.2), which hands on the PCS claim
   `(r'', W̃(r''), c)`;
4. check (f): `c = W̃(r'') · Σ_j b_j v_j`, `b_j = eq(r''_lo, j)`, `v` read from field 8;
5. steps 11–13: `Ligero.verify2` (absorb `v`, squeeze the column indices, the Merkle paths and the
   two column equations) with the row weights `a_i = eq(r''_hi, i)`.

Every oracle query goes through `Transcript.seed/absorb/squeeze/squeezeN` and `Merkle.verify`.

The byte layout (§7): fields 1–2 (`Ligero.size1 κ` bytes: `root`, `ū`), fields 3–7
(`Spartan.msgsBytes κ`), fields 8–9 (`Ligero.size2 κ`: `v`, the openings). `leafSize n =
80 + snarkSize κ` for `n ≥ 1`, `80` for `n = 0`.

The matrix and `p̃ub` evaluators are a parameter `ev` (`Spartan.Evals` for each `(κ, n, s, h)`),
supplied by `SpartanChainChain` (§2.4). `leafVerifier ev` is the `LeafVerifier` of
`SpartanChainVerifierTop`.

**L-Q1** `queries_le`: for `n ≤ 2^20` (`κ ≤ 20`) the SNARK asks at most `2^14` queries, under
every oracle and for every `π_S`.
-/

namespace SpartanChain

namespace Leaf

open RecursionFast Transcript PCS

/-- `κ = ⌈log₂ n⌉`. -/
def kap (n : ℕ) : ℕ := Nat.clog 2 n

/-- The SNARK bytes of §7 (fields 1–9). -/
def snarkSize (κ : ℕ) : ℕ := Ligero.size1 κ + Spartan.msgsBytes κ + Ligero.size2 κ

/-- `leafSize n` (§7): the 80-byte header, and the SNARK for `n ≥ 1`. -/
def leafSize (n : ℕ) : ℕ := if n = 0 then 80 else 80 + snarkSize (kap n)

theorem leafSize_ge (n : ℕ) : 80 ≤ leafSize n := by
  unfold leafSize; split_ifs <;> omega

/-- The evaluators of the chain R1CS, for each `(κ, n, s, h)`. -/
abbrev EvalsFor := ℕ → ℕ → Digest → Digest → Spartan.Evals

/-- **Check (f)** of §9.2: `c = W̃(r'') · Σ_j eq(r''_lo, j) v_j`. -/
def finalCheck (κ : ℕ) (pc : Spartan.PcsClaim) (v : Array EF) : Bool :=
  decide (pc.value = pc.weight * dot (eqTable (pc.point.take (lk κ))) v)

/-- Byte offsets of §7 inside `π_S`: the end of fields 1–2, of 3–7, and of field 8. -/
def off₁ (κ : ℕ) : ℕ := Ligero.size1 κ
def off₂ (κ : ℕ) : ℕ := off₁ κ + Spartan.msgsBytes κ
def off₃ (κ : ℕ) : ℕ := off₂ κ + 24 * msgLen κ

/-- The column phase and check (f), after the algebraic layer. -/
def tail (κ : ℕ) (π : ByteArray) (r : List EF) (st : Digest) (pc : Spartan.PcsClaim) :
    OProg Bool :=
  let vB := π.extract (off₂ κ) (off₃ κ)
  if finalCheck κ pc (Ligero.readEFs vB 0 (msgLen κ)) then
    Ligero.verify2 κ st (Ligero.readLabel π 0) r.toArray (eqTable (pc.point.drop (lk κ)))
      (Ligero.readEFs (π.extract 31 (off₁ κ)) 0 (msgLen κ)) vB (π.extract (off₃ κ) π.size)
  else pure false

/-- **The SNARK verifier** of a leaf `(s, n, h)` with `n ≥ 1` (§6.2 steps 1–13). -/
def snarkProg (ev : EvalsFor) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) : OProg Bool := do
  let κ := kap n
  let st ← seed s n h
  let p ← Ligero.verify1 κ st (π.extract 0 31) (π.extract 31 (off₁ κ))
  let res ← Spartan.verify κ (ev κ n s h) (Spartan.parseMsgs κ π (off₁ κ)) p.1
  match res with
  | none => pure false
  | some (st', pc) => tail κ π p.2 st' pc

/-- The leaf verifier of the entry, for the evaluators `ev`. -/
def leafVerifier (ev : EvalsFor) : LeafVerifier where
  size := leafSize
  size_ge := leafSize_ge
  prog := snarkProg ev

/-! ## L-Q1: the query count -/

section Queries

variable (H : ByteArray → Digest)

theorem len_squeezeE (st : Digest) (k : ℕ) : ((squeezeE st k).queries H).length = k := by
  simp [squeezeE, queries_squeezeN]

theorem len_climb (cur : Label) (c : ℕ) (ss : List Label) :
    ((Merkle.climb cur c ss).queries H).length = ss.length := by
  induction ss generalizing cur c with
  | nil => rfl
  | cons s ss ih => simp [Merkle.climb, Merkle.hashL, ih, add_comm]

theorem len_mverify (root : Label) (c : ℕ) (col : ByteArray) (ss : List Label) :
    ((Merkle.verify root c col ss).queries H).length = 1 + ss.length := by
  simp [Merkle.verify, Merkle.hashL, len_climb, add_comm]

theorem len_absorbRounds (kind : UInt8) (st : Digest) (gs : List (Array EF)) :
    ((Spartan.absorbRounds kind st gs).queries H).length = 2 * gs.length := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp [Spartan.absorbRounds, absorb, squeeze, ih]
    ring

theorem len_verify1 (κ : ℕ) (st : Digest) (a b : ByteArray) :
    ((Ligero.verify1 κ st a b).queries H).length = 2 + rows κ := by
  simp [Ligero.verify1, Ligero.rootAndCoeffs, absorb, len_squeezeE]
  ring

theorem len_verify2 (κ : ℕ) (st : Digest) (root : Label) (r a ubar : Array EF)
    (vB opens : ByteArray) :
    ((Ligero.verify2 κ st root r a ubar vB opens).queries H).length =
      1 + nAns (lN κ) tQ + tQ * (1 + lN κ) := by
  simp [Ligero.verify2, Ligero.openOne, absorb, squeezeIdx, queries_squeezeN, len_mverify,
    Ligero.readPath, List.length_flatMap, List.sum_replicate]
  ring

theorem chunks_length {α : Type} (k c : ℕ) (l : List α) : (Spartan.chunks k c l).length = c := by
  induction c generalizing l with
  | zero => rfl
  | succ c ih => simp [Spartan.chunks, ih]

/-- The algebraic layer's queries on parsed messages: `5 ℓ_y + 9 + 2 ℓ_q`. -/
theorem len_spartan (κ : ℕ) (ev : Spartan.Evals) (st : Digest) (π : ByteArray) (o : ℕ) :
    ((Spartan.verify κ ev (Spartan.parseMsgs κ π o) st).queries H).length =
      5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ := by
  simp [Spartan.verify, absorb, squeeze, len_squeezeE, len_absorbRounds, Spartan.parseMsgs,
    Spartan.split, chunks_length]
  ring

/-- The query bound of a leaf SNARK with parameter `κ`. -/
def qBound (κ : ℕ) : ℕ :=
  1 + (2 + rows κ) + (5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ) +
    (1 + nAns (lN κ) tQ + tQ * (1 + lN κ))

theorem len_snarkProg (ev : EvalsFor) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) :
    ((snarkProg ev s n h π).queries H).length ≤ qBound (kap n) := by
  simp only [snarkProg, seed, OProg.queries_bind, OProg.run_ask, OProg.queries_ask,
    List.length_append, List.length_singleton, len_verify1, len_spartan, qBound]
  generalize (Spartan.verify _ _ _ _).run H = res
  cases res with
  | none => simp; omega
  | some x =>
    obtain ⟨st', pc⟩ := x
    simp only [tail]
    split_ifs
    · simp only [len_verify2]; omega
    · simp; omega

/-- `qBound κ ≤ 2^14` for every `κ ≤ 20` (§6.3: `7 774` at `κ = 20`). -/
theorem qBound_le : ∀ κ ≤ 20, qBound κ ≤ 2 ^ 14 := by decide

/-- `κ = ⌈log₂ n⌉ ≤ 20` for `n ≤ 2^20`. -/
theorem kap_le {n : ℕ} (hn : n ≤ 2 ^ 20) : kap n ≤ 20 :=
  Nat.clog_le_of_le_pow hn

/-- **L-Q1.** For `n ≤ 2^20`, the SNARK verifier asks at most `2^14` queries, under every oracle
and for every proof. -/
theorem queries_le (ev : EvalsFor) (s : Digest) {n : ℕ} (hn : n ≤ 2 ^ 20) (h : Digest)
    (π : ByteArray) : ((snarkProg ev s n h π).queries H).length ≤ 2 ^ 14 :=
  (len_snarkProg H ev s n h π).trans (qBound_le _ (kap_le hn))

end Queries

end Leaf

end SpartanChain
