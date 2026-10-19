import SpartanChainSoundnessLog

/-!
# Controls for the chains of the log (BLUEPRINT-R1 §9.1, §10.1)

`honest1` is the transcript of a leaf of shape `κ = 0` (`n = 1`), 117 entries, one per step of
`shape 0`, each query built from the previous answer (any answers do: chains are about the
links and the formats, not about the oracle).

* `honest1_chain`: its last entry is a chain (positive, `Matches`/`IsChain`);
* `broken_not_chain`: with one byte of one state field changed the last entry is not a chain
  (negative);
* `short_not_chain`: a log of a seed with `n = 0` is not a chain (negative: `1 ≤ n`);
* `honest1_frontier`, `honest1_not_frontier`: the last entry is on the frontier; the entry before
  it is not, since the squeeze of its answer is in the log (`OnFrontier`).
-/

namespace SpartanChain
open RecursionFast Transcript SoundnessLog

namespace SoundnessLogControls

/-- The answer of entry `j`: distinct for distinct `j < 2^16`. -/
def ansOf (j : ℕ) : Digest :=
  Vector.ofFn fun i => if i.1 = 0 then j.toUInt8 else if i.1 = 1 then (j / 256).toUInt8 else 0x77

/-- The query of a step from the previous answer (an absorb of zero bytes is built with `Array`
append, which is `absorbQ`'s byte string and cheap for the kernel). -/
def qOf (prev : Digest) : Step → ByteArray
  | .seed => seedQ (ansOf 1000) 1 (ansOf 1001)
  | .absorb k l => ⟨Array.mk (0x20 :: prev.toList ++ k :: List.replicate l 0)⟩
  | .squeeze => squeezeQ prev

theorem qOf_absorb (prev : Digest) (k : UInt8) (l : ℕ) :
    qOf prev (.absorb k l) = absorbQ prev k ⟨Array.replicate l 0⟩ := by
  apply ByteArray.ext_toList
  simp [qOf]

/-- The log of the steps `sts`, entry `j` answering `ansOf j`. -/
def mkLog : List Step → ℕ → Digest → Log
  | [], _, _ => []
  | st :: sts, j, prev => (qOf prev st, ansOf j) :: mkLog sts (j + 1) (ansOf j)

/-- The transcript of a leaf of shape `0`. -/
def honest1 : Log := mkLog (shape 0) 0 (ansOf 1000)

theorem honest1_length : honest1.length = 117 := by decide +kernel

/-- **Positive**: the honest transcript of a 1-leaf is a chain. -/
theorem honest1_chain : IsChain honest1 116 := by
  refine ⟨by rw [honest1_length]; omega, ?_⟩
  have hes : entriesOf honest1 (pathOf honest1 116) = honest1 := by decide +kernel
  rw [hes, matches_iff]
  unfold matchesB
  have h0 : (honest1[0]?.bind fun e => seedOf e.1) = some (ansOf 1000, 1, ansOf 1001) := by
    have : honest1[0]? = some (seedQ (ansOf 1000) 1 (ansOf 1001), ansOf 0) := rfl
    rw [this, Option.bind_some, seedOf_seedQ _ (by norm_num)]
  rw [h0]
  simp only [Nat.clog_one_right]
  decide +kernel

/-- The honest transcript with byte `0` of the state field of entry `60` changed. -/
def broken : Log :=
  honest1.set 60 (squeezeQ ((ansOf 59).set 0 0xFF), ansOf 60)

/-- **Negative**: a changed state byte breaks the chain. -/
theorem broken_not_chain : ¬ IsChain broken 116 := by decide +kernel

/-- **Negative**: a seed with `n = 0` starts no chain. -/
theorem short_not_chain : ¬ IsChain [(seedQ (ansOf 1000) 0 (ansOf 1001), ansOf 0)] 0 := by
  decide +kernel

/-- **Positive**: the last entry is on the frontier. -/
theorem honest1_frontier : OnFrontier honest1 honest1[116]! := by decide +kernel

/-- **Negative**: the squeeze of entry `115`'s answer is in the log. -/
theorem honest1_not_frontier : ¬ OnFrontier honest1 honest1[115]! := by decide +kernel

end SoundnessLogControls

end SpartanChain
