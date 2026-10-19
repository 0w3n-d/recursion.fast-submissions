import SpartanChainProver
import SpartanChainSubmission
import SpartanChainChainEval

/-!
# The compiled runner's functions (BLUEPRINT-R1 §10 `Run.lean`, §11.3)

Plain functions for a compiled executable (which lives outside the root). They call **exactly the
certified objects** (review S2b-m2): the verifier is `Submission.Vb` of
`submission runLV (proveLeafR wf)` written out (`verifyProof_eq`, by `rfl`), with `V`
of `SpartanChainVerifierTop` and the leaf SNARK `Leaf.leafVerifier chainEvals`; the prover is the
submission's `P` with the SNARK prover `Leaf.proveSnark` (`proveLeafBytes_eq`, by `rfl`). The
prover's tables `wf` (`Leaf.WitFor`) are an argument until `SpartanChainChain` supplies them.
No `main` and no elaboration-time code here.
-/

namespace SpartanChain

namespace Run

open RecursionFast

/-- The leaf verifier of the entry: the SNARK with the chain's evaluators (`chainEvals`). -/
def runLV : LeafVerifier := Leaf.leafVerifier chainEvals

/-- The SNARK prover in the shape `Submission.P` takes (`h` is `chainEnd s n` there). -/
def proveLeafR (wf : Leaf.WitFor) (s : Digest) (n : ℕ) (_ : Digest) : OProg ByteArray :=
  Leaf.proveSnark wf s n

/-- The instantiated verifier on a proof (`Submission.Vb`, written out). -/
def verifyProof (c : Digest) (π : ByteArray) : Bool :=
  if π.size ≤ proofCap then (V runLV c π).run blake2sOracle else false

/-- `verifyProof` is the submission's `Vb`, for every prover argument. -/
theorem verifyProof_eq (wf : Leaf.WitFor) (c : Digest) (π : ByteArray) :
    verifyProof c π = (submission runLV (proveLeafR wf)).Vb c π := rfl

/-- The leaf SNARK verifier alone, on `(s, n, h, π_S)`. -/
def verifySnark (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) : Bool :=
  (runLV.prog s n h π).run blake2sOracle

/-- The honest leaf proof of `(s, n)`: the submission's `P` under the BLAKE2s oracle. -/
def proveLeafBytes (wf : Leaf.WitFor) (s : Digest) (n : ℕ) : ByteArray :=
  (P (proveLeafR wf) s (.leaf s n)).run blake2sOracle

/-- `proveLeafBytes` is the submission's `P`, for every statement argument. -/
theorem proveLeafBytes_eq (wf : Leaf.WitFor) (c s : Digest) (n : ℕ) :
    proveLeafBytes wf s n = ((submission runLV (proveLeafR wf)).P c (.leaf s n)).run blake2sOracle :=
  rfl

/-- Read a proof file and verify it under the statement `c`. -/
def verifyFile (c : Digest) (path : System.FilePath) : IO Bool := do
  let π ← IO.FS.readBinFile path
  pure (verifyProof c π)

end Run

end SpartanChain
