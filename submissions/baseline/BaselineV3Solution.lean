/-
  Challenge stub, v3 (INTERIM, organiser-side: written by stage S2a against the contract at the
  pin 15e4ae5, on the scratch branch `v3/s2-interim-harness`; stage S3 owns the v3 stub and takes
  this one over). Rendered by
  `python3 -I scripts/render-challenge.py RecursionFast/Challenge/V3.lean.in claim.json OUT.lean`.
  Everything except `submission` and `certified` is organiser data: the declared claim (`Declared`,
  DESIGN-v3 §3.2: the extractor image rendered from the submitted raw `.code`/`.data` files, the
  declared error, verifier query bound and affine fuel). A solution fills exactly the two `sorry`
  placeholders; the comparator checks that it proves exactly `certified` with `submission` its
  only definition.
-/
import RecursionFast.Contract
import BaselineV3

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

def image_code_0 : ℕ := 0x7300000293028305130035d593007585930203358303f3131300100313
/-- Chunks of the submitted file (8 words), 256 words each but the last. -/
def image_code_chunks : List (List ℕ) := [unpack 32 8 image_code_0]
/-- Rendered from the submitted file. -/
def image_code : List (BitVec 32) := image_code_chunks.flatten.map (BitVec.ofNat 32)
/-- Chunks of the submitted file (0 words), 256 words each but the last. -/
def image_data_chunks : List (List ℕ) := []
/-- Rendered from the submitted file. -/
def image_data : List (Word) := image_data_chunks.flatten.map (BitVec.ofNat 64)
/-- The submitted extractor image (rendered challenge data). -/
def image : Image := { code := image_code, data := image_data }

/-- The declared claim (rendered): the image, the error, the verifier query bound and the fuel
`fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  img := image
  ε := ((0 : ℝ≥0) / 1)
  qV := 0
  fuel t := 8 + 0 * t

/-- The submission (provided by the solution). -/
def submission : Submission := BaselineV3.submission

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission :=
  ⟨BaselineV3.certificate, rfl, zero_le, le_rfl,
    fun t => ⟨show 8 ≤ 8 + 0 * t by omega, show 8 + 0 * t ≤ 2 ^ 40 + 2 ^ 8 * t by omega⟩⟩

end RecursionFast.Challenge
