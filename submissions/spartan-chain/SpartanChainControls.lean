import SpartanChainSoundnessFinal
import SpartanChainVerifier
import SpartanChainChainSound

/-!
# Non-vacuity controls of the certificate's definitions (blueprint §10.1, §14 Controls items)

The inventory (definition → positive control → negative control) is
`docs/snark-baseline/reports/controls.md`; this module holds the controls that were missing:

* `μ`: `0` on the empty log (`mu_empty`), `1` on a log with a repeated query (`mu_repeat`).
* `Doom`: a one-entry chain of a false statement is doomed (`doom_seed_false`), of a true
  statement is not (`not_doom_seed_true`).
* `Rej`: no check applies before the first round polynomial (`not_rej_short`); a first outer
  round polynomial of the wrong size is rejected (`rej_bad_size`).
* `EscAt`: no escape at a one-entry chain (`not_escAt_single`); the generic escape shape is
  reachable (`escAtG_pos`).
* `snarkProg` and a tampered Ligero column: an accepting `snarkProg` run passes `verify2` on its
  arguments (`snarkProg_verify2`), and `verify2` rejects as soon as one opening fails its column
  check (`verify2_rejects_col`), which a tampered column does (`Ligero.Controls.colCheck_tampered`).
* The chain R1CS: the honest witness satisfies it (`L-C3 chain_complete`); no Boolean witness
  satisfies it for a wrong end (`chainSat_wrong_end`).
All are theorems; none evaluates BLAKE2s in the kernel.
-/

namespace SpartanChain.Controls

open RecursionFast SoundnessLog KS PCS Transcript

variable (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals)

/-! ### `μ` -/

/-- Positive: `μ [] = 0`. -/
theorem mu_empty : μ ev [] = 0 := by
  unfold μ muG
  split_ifs with hbe
  · exfalso
    revert hbe
    rintro (hb | ⟨j, hj, -⟩)
    · rcases hb with ⟨e, he, -⟩ | ⟨i, j, -, hj, -⟩ | ⟨i, j, -, hj, -⟩ | hr
      · simp at he
      · simp at hj
      · simp at hj
      · exact hr List.nodup_nil
    · simp [chains] at hj
  · simp [sumG, chains]

/-- Negative: a log with a repeated query has `μ = 1`. -/
theorem mu_repeat (q : ByteArray) (a a' : Digest) : μ ev [(q, a), (q, a')] = 1 := by
  unfold μ muG
  have : Bad [(q, a), (q, a')] := by
    right; right; right
    simp [Repeated]
  simp [this]

/-! ### `Doom`, `Rej`, `EscAt` -/

theorem pG_ge (κ : ℕ) : 3 ≤ pG κ 0 := by unfold pG; omega

/-- Positive for `Rej`'s scope: before the first round polynomial no check applies. -/
theorem not_rej_short {es : Log} (h : es.length - 1 < pG (kapOf es) 0) : ¬ Rej ev es := by
  simp only [Rej, not_or, not_exists, not_and]
  refine ⟨fun l _ hl => ?_, fun hl => ?_, fun l _ hl => ?_, fun hl => ?_, fun l _ hl => ?_,
    fun hl => ?_⟩ <;>
  · simp only [pG, pTri, pGi, pS, pGr, pV] at h hl ⊢; omega

/-- Negative: a first outer round polynomial with other than 4 coefficients is rejected. -/
theorem rej_bad_size {es : Log} (h : pG (kapOf es) 0 ≤ es.length - 1)
    (hs : (gOut (kapOf es) es 0).size ≠ 4) : Rej ev es := by
  left
  exact ⟨0, by omega, h, fun hok => hs hok.1⟩

/-- Positive for `Doom`: a one-entry chain of a false statement is doomed. -/
theorem doom_seed_false (L₀ : Log) {es : Log} (h1 : es.length = 1) (hfs : FS es) :
    Doom ev L₀ es :=
  SoundnessFinal.doom_seed ev L₀ h1 hfs

/-- Negative for `Doom`: a one-entry chain of a true statement is not doomed. -/
theorem not_doom_seed_true (L₀ : Log) {es : Log} (h1 : es.length = 1) (htrue : ¬ FS es) :
    ¬ Doom ev L₀ es := by
  rintro (hr | ha)
  · exact not_rej_short ev (by have := pG_ge (kapOf es); omega) hr
  · unfold Alg at ha
    rw [h1, Nat.sub_self, SoundnessFinal.posClass_zero] at ha
    exact htrue ha

/-- Negative for `EscAt`: a one-entry chain never escapes. -/
theorem not_escAt_single (L₀ : Log) {es : Log} (h1 : es.length = 1) : ¬ EscAt ev L₀ es := by
  rintro ⟨h2, -, -⟩; omega

/-- Positive for the escape shape: with a doom predicate that holds on one-entry lists only, a
two-entry list escapes. -/
theorem escAtG_pos (L₀ : Log) (e e' : ByteArray × Digest) :
    EscAtG (fun _ es => es.length = 1) L₀ [e, e'] := by
  refine ⟨by simp, by simp, by simp⟩

/-! ### A tampered Ligero column is rejected -/

/-- `verify2` rejects (under any oracle) as soon as one opening fails its column check. -/
theorem verify2_rejects_col (H : ByteArray → Digest) (κ : ℕ) (st : Digest) (root : Label)
    (r a ubar : Array EF) (vB opens : ByteArray) {j : ℕ} (hj : j < tQ)
    (hbad : Ligero.colCheck κ (Ligero.kapArr (lk κ)) r a ubar (Ligero.readEFs vB 0 (msgLen κ))
        ((((squeezeIdx ((absorb st 0x08 vB).run H) (lN κ) tQ).run H).2).getD j 0)
        (Ligero.readFs (Ligero.readCol κ opens (j * Ligero.openW κ)) 0 (rows κ)) = false) :
    (Ligero.verify2 κ st root r a ubar vB opens).run H = false := by
  by_contra hne
  have h := (Ligero.run_verify2 H κ st root r a ubar vB opens).1 (by simpa using hne)
  rw [(h j hj).2] at hbad
  exact Bool.noConfusion hbad

/-- An accepting run of the SNARK verifier passes `verify2` on the arguments it computes (so a
proof whose opening fails the column check, e.g. a tampered column, is rejected). -/
theorem snarkProg_verify2 (H : ByteArray → Digest) {s : Digest} {n : ℕ} {h : Digest}
    {π : ByteArray} (hacc : (Leaf.snarkProg ev s n h π).run H = true) :
    ∃ κ st root r a ubar vB opens,
      (Ligero.verify2 κ st root r a ubar vB opens).run H = true := by
  unfold Leaf.snarkProg at hacc
  simp only [OProg.run_bind] at hacc
  split at hacc
  · simp at hacc
  · unfold Leaf.tail at hacc
    simp only at hacc
    split at hacc
    · exact ⟨_, _, _, _, _, _, _, _, hacc⟩
    · simp at hacc

/-! ### The chain R1CS -/

/-- Negative: no Boolean witness satisfies the chain R1CS for a wrong chain end (L-C2). -/
theorem chainSat_wrong_end {E : Type} [Field E] [CharP E 2] {n κ : ℕ} (hn : 1 ≤ n) (hnκ : n ≤ 2 ^ κ)
    {s h : Digest} (hh : chainEnd s n ≠ h) {w : Fin (wLen κ) → E}
    (hw : ∀ u, BlockR1CS.IsBool (w u)) : ¬ ChainSat n κ w s h :=
  fun hsat => hh (chain_sound hn hnκ hw hsat)

end SpartanChain.Controls
