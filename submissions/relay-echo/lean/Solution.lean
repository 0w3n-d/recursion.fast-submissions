/-
  The relay-echo entry: the core library's witness-sending submission with its verifier
  replaced by `FastCheck.V'` (`FastDefs.lean`), proved equal to the library's (`FastSpec.lean`),
  so the library's certificate transfers. `declared` is the rendered challenge's, copied verbatim,
  as the comparator requires.
-/
import FastSpec

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((0 : ℝ≥0) / 1)
  δ := ((0 : ℝ≥0) / 1)
  qV := 0
  fuel t := 0 + 8 * t

/-- The submission: the witness-sending argument, with the verifier `FastCheck.V'`. -/
def submission : Submission := { WitnessSending.submission with V := FastCheck.V' }

/-- **The certificate against the rendered claim**: the library's, since the submission is the
library's (its verifier is, `FastCheck.V'_eq`). -/
theorem certified : CertificateR declared submission := by
  have h : submission = WitnessSending.submission := by
    rw [submission, FastCheck.V'_eq]
    rfl
  rw [h]
  exact ⟨WitnessSending.certificate, by simp [declared, WitnessSending.submission],
    by simp [declared, WitnessSending.submission], le_rfl, fun t =>
      ⟨by simp [declared, WitnessSending.submission, WitnessSending.fuel],
       by simp only [declared, extractorBudget]; omega⟩⟩

end RecursionFast.Challenge
