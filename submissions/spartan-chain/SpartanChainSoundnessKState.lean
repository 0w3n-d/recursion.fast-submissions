import SpartanChainSoundnessKS
import SpartanChainSoundnessKSFinal

/-!
# The knowledge state and knowledge soundness of the entry (BLUEPRINT-R1 §9.3, L-K5, L-K6)

* **L-K5 `kstate`**: `KState (Rel (vb LV)) (V LV) WitnessSending.E 2^-129` with the potential
  `KS.μ chainEvals`, the laws `empty` (`KS.mu_empty`), `step` (`KS.mu_step_chain`, from
  `SpartanChainSoundnessKS`) and `final` (`SoundnessKSFinal.final_law`).
* **L-K6 `ks`**: `KS (Rel (vb LV)) (V LV) WitnessSending.E 2^-129 2^14`: the knowledge state, and
  L-Q1 (`Leaf.queries_le`: the SNARK asks at most `2^14` queries; every other branch asks none).

`LV = Leaf.leafVerifier chainEvals`, `ε = 2^-129` (`KS.εKS`).
-/

namespace SpartanChain.KS

open RecursionFast SoundnessKSFinal

/-- **L-K5 `kstate`**: the knowledge state of the entry with error `2^-129`. -/
noncomputable def kstate : KState (Rel (vb LV)) (V LV) WitnessSending.E εKS where
  μ := μ chainEvals
  empty := mu_empty chainEvals
  step := fun _ _ hl hμ hq => mu_step_chain hl hμ hq
  final := final_law

/-- **L-Q1 at the top level**: `V LV` asks at most `2^14` queries on every input and oracle. -/
theorem V_queries_le (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((V LV c π).queries H).length ≤ 2 ^ 14 := by
  by_cases hleaf : 8 ≤ π.size ∧ tagWord π = 0
  · have hV : V LV c π = leafProg LV c π := by
      rw [V, ite_eq_right (by omega), ite_eq_left hleaf.2]
    rw [hV, leafProg_queries]
    split_ifs with hh
    · obtain ⟨hcap, -, -⟩ := (leafHeaderOK_iff LV).mp hh.1
      exact Leaf.queries_le H chainEvals _ hcap _ _
    · simp
  · rw [V_queries_of_not_leaf LV H hleaf]; simp

/-- **L-K6 `ks`**: knowledge soundness of the entry, `KS (Rel (vb LV)) (V LV) E 2^-129 2^14`. -/
theorem ks : RecursionFast.KS (Rel (vb LV)) (V LV) WitnessSending.E εKS (2 ^ 14) :=
  ⟨⟨kstate⟩, V_queries_le⟩

end SpartanChain.KS
