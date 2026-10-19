import SpartanChainProver

/-!
# The compiled runner's functions (BLUEPRINT-R1 §10 `Run.lean`, §11.3)

Plain functions for a compiled executable (which lives outside the root): the Lean verifier on a
proof's bytes and the Lean leaf prover, both under the contract's BLAKE2s oracle, for the chain
operations `Ops` (the evaluators of §2.4 and the prover's tables, supplied by
`SpartanChainChain`). No `main` and no elaboration-time code here.
-/

namespace SpartanChain

namespace Run

open RecursionFast

/-- The chain operations: the verifier's evaluators and the prover's tables. -/
structure Ops where
  ev : Leaf.EvalsFor
  wf : Leaf.WitFor

/-- The instantiated verifier on a proof: `vb` of `SpartanChainVerifierTop` with the leaf SNARK. -/
def verifyProof (ops : Ops) (c : Digest) (π : ByteArray) : Bool :=
  vb (Leaf.leafVerifier ops.ev) c π

/-- The leaf SNARK verifier alone, on `(s, n, h, π_S)`. -/
def verifySnark (ops : Ops) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) : Bool :=
  (Leaf.snarkProg ops.ev s n h π).run blake2sOracle

/-- The honest leaf proof of `(s, n)`. -/
def proveLeafBytes (ops : Ops) (s : Digest) (n : ℕ) : ByteArray :=
  (Leaf.proveLeaf ops.wf s n).run blake2sOracle

/-- Read a proof file and verify it under the statement `c`. -/
def verifyFile (ops : Ops) (c : Digest) (path : System.FilePath) : IO Bool := do
  let π ← IO.FS.readBinFile path
  pure (verifyProof ops c π)

end Run

end SpartanChain
