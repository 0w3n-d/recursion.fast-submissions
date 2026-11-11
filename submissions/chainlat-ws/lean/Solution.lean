/-
  The smoke entry's solution: the library's witness-sending submission (`Library/WitnessSending`)
  against the challenge rendered from `claim.json` (both errors 0, no query, fuel `0 + 8 · t`).
  `declared` is the rendered challenge's, copied verbatim, as the comparator requires.
-/
import RecursionFast.Library.WitnessSending

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

/-- The submission: the witness-sending argument. -/
def submission : Submission := WitnessSending.submission

/-- **The certificate against the rendered claim.** -/
theorem certified : CertificateR declared submission :=
  ⟨WitnessSending.certificate, by simp [declared, submission, WitnessSending.submission],
    by simp [declared, submission, WitnessSending.submission], le_rfl, fun t =>
      ⟨by simp [declared, submission, WitnessSending.submission, WitnessSending.fuel],
       by simp only [declared, extractorBudget]; omega⟩⟩

end RecursionFast.Challenge
