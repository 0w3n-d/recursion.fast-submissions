import SpartanChainSubmission
import SpartanChainSoundnessKState
import SpartanChainChainHonest

/-!
# The final instantiation of the entry (BLUEPRINT-R1 §1.4, §10)

The parameters of `SpartanChainSubmission`:

* `leafVerifier := Leaf.leafVerifier chainEvals`: the leaf SNARK verifier with the chain R1CS's
  evaluators (`SpartanChainVerifier`, `SpartanChainChainEval`);
* `proveLeafR1 s n _ := Leaf.proveSnark chainWf s n`: the SNARK prover with the chain's tables
  (`SpartanChainProver`, `SpartanChainChainHonest`);
* `facts : Facts leafVerifier proveLeafR1`:
  * `size_zero`: `leafSize 0 = 80`;
  * `leaf_complete`: `snark_size` and `snark_complete` with `chainHonest : HonestOps chainEvals
    chainWf`;
  * `ks`: L-K5 `KS.kstate` (`ε = 2^-129`);
  * `queries`: L-Q1 `Leaf.queries_le`.
-/

namespace SpartanChain

open RecursionFast

/-- The entry's leaf verifier. -/
abbrev leafVerifier : LeafVerifier := Leaf.leafVerifier chainEvals

/-- The entry's SNARK prover (`h = chainEnd s n` is recomputed by `proveSnark`). -/
def proveLeafR1 (s : Digest) (n : ℕ) (_h : Digest) : OProg ByteArray := Leaf.proveSnark chainWf s n

/-- **The facts** the certificate needs. -/
theorem facts : Facts leafVerifier proveLeafR1 where
  size_zero := rfl
  leaf_complete H s n h1 h2 := by
    refine ⟨?_, ?_⟩
    · show 80 + ((Leaf.proveSnark chainWf s n).run H).size = Leaf.leafSize n
      rw [Leaf.snark_size, Leaf.leafSize, ite_eq_right (by omega)]
    · exact Leaf.snark_complete chainEv chainWf chainHonest H s h1 h2
  ks := ⟨KS.kstate⟩
  queries H s n h sn hn := Leaf.queries_le H chainEvals s hn h sn

end SpartanChain
