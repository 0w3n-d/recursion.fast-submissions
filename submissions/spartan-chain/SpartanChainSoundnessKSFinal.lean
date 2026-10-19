import SpartanChainSoundnessChain
import SpartanChainChainEval

/-!
# The `final` law of the knowledge state (BLUEPRINT-R1 §9.3 `final`, L-K5)

`mu_final` is the contract's `KState.final` for the entry. The pieces are:

* the verifier `V LV`, with `LV := Leaf.leafVerifier chainEvals`;
* the library's extractor `WitnessSending.E` (`decode π`);
* the relation `Rel (vb LV)`;
* the potential `KS.μ chainEvals`.

It holds for every log with `μ L < 1` and every proof the verifier accepts reading its answers
from the log.

* **Node branch, and every proof off the leaf branch**: `VerifierTop.final_of_not_leaf`. These
  proofs make no query, and `checkNode_rel` decides `Rel` through `vb` on the children.
* **Leaf branch**:
  * `final_of_leaf` gives the decoding `.leaf s n`;
  * `SoundnessChain.mu_final_leaf_closed` gives `n ≤ chainCap`, `c = leafStmt h n` and
    `chainEnd s n = h`. That is L-K4 `runLog_chain`, L-K3 `accept_not_doomed` and
    `doom_of_not_esc` under `¬ Bad`, `¬ Esc`.

The log-length guard of the contract's `final` is not needed.
-/

namespace SpartanChain.SoundnessKSFinal

open RecursionFast SoundnessChain

/-- The entry's leaf verifier: the SNARK with the chain R1CS's evaluators. -/
abbrev LV : LeafVerifier := Leaf.leafVerifier chainEvals

/-- **`mu_final`** (the contract's `KState.final` for the entry): on a log with `μ L < 1`, every
proof the verifier accepts reading its answers from the log is extracted by the library's
extractor to a witness of `Rel (vb LV)`. -/
theorem mu_final (L : Log) (c : Digest) (π : Proof) (_hl : L.length ≤ logCap)
    (hμ : KS.μ chainEvals L < 1) (hacc : (V LV c π).runLog L = some true) :
    ∃ w, WitnessSending.E c π L = some w ∧ Rel (vb LV) c w := by
  by_cases hleaf : 8 ≤ π.size ∧ tagWord π = 0
  · obtain ⟨hdec, -, -, -, -⟩ := final_of_leaf LV hacc hleaf.1 hleaf.2
    have hlp : (leafProg LV c π).runLog L = some true := by
      rwa [V, ite_eq_right (by omega), ite_eq_left hleaf.2] at hacc
    obtain ⟨hcap, hc, hend⟩ := mu_final_leaf_closed chainEvals hμ hlp
    refine ⟨.leaf (leafS π) (leafN π), hdec, hcap, ?_⟩
    rw [hend]; exact hc
  · obtain ⟨w, hdec, hrel⟩ := final_of_not_leaf LV hacc hleaf
    exact ⟨w, hdec, hrel⟩

/-- `mu_final` with the binders in the order of `KState.final`. -/
theorem final_law : ∀ L c π, L.length ≤ logCap → KS.μ chainEvals L < 1 →
    (V LV c π).runLog L = some true →
    ∃ w, WitnessSending.E c π L = some w ∧ Rel (vb LV) c w :=
  fun L c π hl hμ hacc => mu_final L c π hl hμ hacc

end SpartanChain.SoundnessKSFinal
