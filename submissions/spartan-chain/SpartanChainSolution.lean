/-
  Challenge stub, v3 (INTERIM, organiser-side: written by stage S2a against the contract at the
  pin 15e4ae5 and carried unchanged onto the amended contract of `v3/ks-potential` at 05fde28
  (`KState` a potential; `Certificate`, `CertificateR` and `Declared` unchanged), on the scratch
  branch `v3/ks-interim-harness`; stage S3 owns the v3 stub and takes this one over). Rendered by
  `python3 -I scripts/render-challenge.py RecursionFast/Challenge/V3.lean.in claim.json OUT.lean`.
  Everything except `submission` and `certified` is organiser data: the declared claim (`Declared`,
  DESIGN-v3 §3.2: the extractor image rendered from the submitted raw `.code`/`.data` files, the
  declared error, verifier query bound and affine fuel). A solution fills exactly the two `sorry`
  placeholders; the comparator checks that it proves exactly `certified` with `submission` its
  only definition.
-/
import RecursionFast.Contract
import SpartanChainFinal

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
  ε := ((1 : ℝ≥0) / 340282366920938463463374607431768211456)
  qV := 16384
  fuel t := 8 + 0 * t

/-- The submission (provided by the solution). -/
noncomputable def submission : Submission :=
  SpartanChain.submission SpartanChain.leafVerifier SpartanChain.proveLeafR1

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission :=
  SpartanChain.certificateR_of _ _ SpartanChain.facts declared rfl SpartanChain.εR1_le_declared
    (show SpartanChain.qVR1 ≤ 16384 by decide)
    fun t => ⟨show 8 ≤ 8 + 0 * t by omega, show 8 + 0 * t ≤ 2 ^ 40 + 2 ^ 8 * t by omega⟩

end RecursionFast.Challenge
