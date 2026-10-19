import SpartanChainSoundnessChain

/-!
# Controls for the chains of the log (BLUEPRINT-R1 §9.1, §10.1)

`honest1` is the transcript of a leaf of shape `κ = 0` (`n = 1`): 117 entries, one per step of
`shape 0`, each query built from the previous answer. Any answers do, because chains are about
the links and the formats, not about the oracle; entry `j` answers `ansOf j`, distinct for
`j < 256`.

The controls are proved from the construction rather than by `decide`. Deciding them on the
117-entry log costs minutes of kernel time and gigabytes of memory, measured in
`logs/spartan-chain/oracle-merkle-transcript/`.

* `honest1_chain` (positive, `Matches`/`IsChain`): the last entry of `honest1` is a chain, and
  its path is the whole log (`pathOf_honest1`).
* `broken_not_chain` (negative): with byte `0` of the state field of the last entry changed, the
  last entry is not a chain. Its state is no answer of the log, so its path is itself, and that
  is not a seed.
* `short_not_chain` (negative, `1 ≤ n`): a seed with `n = 0` starts no chain.
* `honest1_frontier`, `honest1_not_frontier` (`OnFrontier`): the last entry is on the frontier.
  The entry before it is not, because the squeeze of its answer is in the log.
-/

namespace SpartanChain
open RecursionFast Transcript SoundnessLog SoundnessChain

namespace SoundnessLogControls

/-- The answer of entry `j`: byte `0` is `j mod 256`. -/
def ansOf (j : ℕ) : Digest :=
  Vector.ofFn fun i => if i.1 = 0 then j.toUInt8 else if i.1 = 1 then (j / 256).toUInt8 else 0x77

/-- The query of a step from the previous answer. -/
def qOf (prev : Digest) : Step → ByteArray
  | .seed => seedQ (ansOf 1000) 1 (ansOf 1001)
  | .absorb k l => absorbQ prev k ⟨Array.replicate l 0⟩
  | .squeeze => squeezeQ prev

/-- The log of the steps `sts`, entry `j` answering `ansOf j`. -/
def mkLog : List Step → ℕ → Digest → Log
  | [], _, _ => []
  | st :: sts, j, prev => (qOf prev st, ansOf j) :: mkLog sts (j + 1) (ansOf j)

/-- The transcript of a leaf of shape `0`. -/
def honest1 : Log := mkLog (shape 0) 0 (ansOf 1000)

/-! ### Facts about the construction -/

theorem ansOf_zero (j : ℕ) : (ansOf j)[0] = j.toUInt8 := by simp [ansOf]

theorem ansOf_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : ansOf a = ansOf b) : a = b := by
  have := congrArg (fun d : Digest => d[0].toNat) h
  simp only [ansOf_zero] at this
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem length_mkLog (sts : List Step) (j : ℕ) (p : Digest) :
    (mkLog sts j p).length = sts.length := by
  induction sts generalizing j p with
  | nil => rfl
  | cons st sts ih => simp [mkLog, ih]

theorem mkLog_getElem (sts : List Step) :
    ∀ (j : ℕ) (p : Digest) (k : ℕ) (hk : k < (mkLog sts j p).length),
      (mkLog sts j p)[k] =
        (qOf (if k = 0 then p else ansOf (j + k - 1)) (sts[k]'(by
          rwa [length_mkLog] at hk)), ansOf (j + k)) := by
  induction sts with
  | nil => intro j p k hk; simp [mkLog] at hk
  | cons st sts ih =>
    intro j p k hk
    cases k with
    | zero => simp [mkLog]
    | succ k =>
      simp only [mkLog, List.getElem_cons_succ]
      rw [ih (j + 1) (ansOf j) k (by simpa [mkLog] using hk)]
      cases k with
      | zero => simp
      | succ k =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, List.getElem_cons_succ]
        rw [show j + 1 + (k + 1) - 1 = j + (k + 1 + 1) - 1 by omega,
          show j + 1 + (k + 1) = j + (k + 1 + 1) by omega]

theorem shape0_length : (shape 0).length = 117 := by decide +kernel

theorem honest1_length : honest1.length = 117 := by
  rw [honest1, length_mkLog, shape0_length]

theorem shape0_zero : (shape 0)[0]'(by rw [shape0_length]; omega) = .seed := by decide +kernel

theorem shape0_last : (shape 0)[116]'(by rw [shape0_length]; omega) = .squeeze := by
  decide +kernel

theorem seedOf_squeezeQ (x : Digest) : seedOf (squeezeQ x) = none := by
  simp [seedOf, squeezeQ_data]

theorem shape0_tail : ((shape 0).tail.all fun x => x != .seed) = true := by decide +kernel

theorem shape0_ne_seed : ∀ i (hi : i < (shape 0).length), 0 < i → (shape 0)[i] ≠ .seed := by
  intro i hi h0
  have hmem : (shape 0)[i] ∈ (shape 0).tail := by
    have : (shape 0).tail[i - 1]'(by simp; omega) = (shape 0)[i] := by
      rw [List.getElem_tail]; congr 1; omega
    rw [← this]; exact List.getElem_mem _
  simpa using List.all_eq_true.mp shape0_tail _ hmem

theorem qOf_eq_squeezeQ {p x : Digest} {st : Step} (h : qOf p st = squeezeQ x) :
    p = x ∨ st = .seed := by
  cases st with
  | seed => exact Or.inr rfl
  | absorb k l =>
    have := congrArg tagOf h
    simp [qOf] at this
  | squeeze =>
    left
    have := congrArg stateIn h
    simpa [qOf, stateIn_squeezeQ] using this

theorem honest1_get (k : ℕ) (hk : k < honest1.length) :
    honest1[k] = (qOf (if k = 0 then ansOf 1000 else ansOf (k - 1)) ((shape 0)[k]'(by
      rwa [honest1, length_mkLog] at hk)), ansOf k) := by
  have := mkLog_getElem (shape 0) 0 (ansOf 1000) k hk
  simp only [Nat.zero_add] at this
  exact this

theorem stateIn_qOf {p : Digest} {st : Step} (h : st ≠ .seed) : stateIn (qOf p st) = some p := by
  cases st with
  | seed => exact absurd rfl h
  | absorb k l => exact stateIn_absorbQ _ _ _
  | squeeze => exact stateIn_squeezeQ _

theorem stateIn_seed : stateIn (qOf (ansOf 1000) .seed) = none :=
  stateIn_of_seedOf (seedOf_seedQ (ansOf 1000) (by norm_num) (ansOf 1001))

theorem matches_qOf (p : Digest) (st : Step) : st.matches (qOf p st) := by
  cases st with
  | seed => exact check_seedQ _ _ _
  | absorb k l => exact check_absorbQ _ _ _ (show (Array.replicate l (0 : UInt8)).size = l by simp)
  | squeeze => exact check_squeezeQ _

theorem ansIdx_honest1 {k : ℕ} (hk : k < 117) : ansIdx honest1 (ansOf k) = some k := by
  unfold ansIdx
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by rw [honest1_length]; exact hk, by rw [honest1_get]; simp, fun j hj => ?_⟩
  rw [honest1_get _ (by rw [honest1_length]; omega)]
  simp only [decide_eq_true_eq]
  intro h
  have := ansOf_inj (by omega) (by omega) h
  omega

theorem predIdx_honest1 (k : ℕ) (hk : k + 1 < 117) : predIdx honest1 (k + 1) = some k := by
  unfold predIdx
  rw [List.getElem?_eq_getElem (by rw [honest1_length]; exact hk), Option.bind_some,
    honest1_get _ (by rw [honest1_length]; exact hk)]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [stateIn_qOf (shape0_ne_seed _ (by rw [shape0_length]; exact hk) (by omega)),
    Option.bind_some, ansIdx_honest1 (by omega)]

theorem pathOf_honest1 : ∀ k, k < 117 → pathOf honest1 k = List.range (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    apply pathOf_of_pred_none
    unfold predIdx
    rw [List.getElem?_eq_getElem (by rw [honest1_length]; omega), Option.bind_some,
      honest1_get _ (by rw [honest1_length]; omega)]
    simp only [↓reduceIte]
    rw [shape0_zero, stateIn_seed]
    rfl
  | succ k ih =>
    intro hk
    rw [pathOf_of_pred_some (predIdx_honest1 k hk) (by omega), ih (by omega),
      List.range_succ (n := k + 1)]

theorem entriesOf_honest1 : entriesOf honest1 (List.range 117) = honest1 := by
  apply List.ext_getElem (by simp [entriesOf, honest1_length])
  intro i h1 h2
  simp only [entriesOf, List.getElem_map, List.getElem_range]
  exact getElem!_pos honest1 i h2

/-! ### The controls -/

/-- **Positive**: the honest transcript of a 1-leaf is a chain. -/
theorem honest1_chain : IsChain honest1 116 := by
  refine ⟨by rw [honest1_length]; omega, ?_⟩
  rw [pathOf_honest1 116 (by omega), entriesOf_honest1]
  refine ⟨ansOf 1000, 1, ansOf 1001, ?_, le_rfl, by decide, ?_, fun i hi => ⟨?_, ?_⟩⟩
  · rw [List.getElem?_eq_getElem (by rw [honest1_length]; omega), Option.bind_some,
      honest1_get _ (by rw [honest1_length]; omega)]
    simp only [↓reduceIte]
    rw [shape0_zero]
    exact seedOf_seedQ _ (by norm_num) _
  · rw [Nat.clog_one_right, honest1_length, len, shape0_length]
  · rw [honest1_get, honest1_get]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact stateIn_qOf (shape0_ne_seed _ (by rw [shape0_length]; rw [honest1_length] at hi; omega)
      (by omega))
  · rw [honest1_get]
    have : (shape (Nat.clog 2 1))[i + 1]'(by
        rw [Nat.clog_one_right, shape0_length]; rw [honest1_length] at hi; omega) =
        (shape 0)[i + 1]'(by rw [shape0_length]; rw [honest1_length] at hi; omega) := by
      congr 1
    rw [this]
    exact matches_qOf _ _

/-- The honest transcript with byte `0` of the state field of its last entry changed. -/
def broken : Log := honest1.set 116 (squeezeQ ((ansOf 115).set 0 0xFF), ansOf 116)

theorem broken_length : broken.length = 117 := by simp [broken, honest1_length]

/-- **Negative**: a changed state byte breaks the chain. -/
theorem broken_not_chain : ¬ IsChain broken 116 := by
  have hpred : predIdx broken 116 = none := by
    unfold predIdx
    rw [List.getElem?_eq_getElem (by rw [broken_length]; omega), Option.bind_some]
    have h116 : broken[116]'(by rw [broken_length]; omega) =
        (squeezeQ ((ansOf 115).set 0 0xFF), ansOf 116) := by
      simp [broken]
    rw [h116, stateIn_squeezeQ, Option.bind_some]
    unfold ansIdx
    rw [List.findIdx?_eq_none_iff]
    intro e he
    rw [decide_eq_false_iff_not]
    intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hj' : j < 117 := by rwa [broken_length] at hj
    have h0 := congrArg (fun d : Digest => d[0]) h
    simp only [Vector.getElem_set_self] at h0
    have hbj : (broken[j]'hj).2 = ansOf j := by
      by_cases hj116 : j = 116
      · subst hj116; rw [h116]
      · have : broken[j]'hj = honest1[j]'(by rw [honest1_length]; exact hj') := by
          simp only [broken]; rw [List.getElem_set_ne (Ne.symm hj116)]
        rw [this, honest1_get _ (by rw [honest1_length]; exact hj')]
    rw [hbj, ansOf_zero] at h0
    have := congrArg UInt8.toNat h0
    simp at this
    omega
  have hb116 : broken[116]! = (squeezeQ ((ansOf 115).set 0 0xFF), ansOf 116) := by
    rw [getElem!_pos broken 116 (by rw [broken_length]; omega)]
    simp [broken]
  rintro ⟨-, s, n, h, h0, -⟩
  rw [pathOf_of_pred_none hpred] at h0
  simp only [entriesOf, List.map_cons, List.map_nil, hb116, List.getElem?_cons_zero,
    Option.bind_some, seedOf_squeezeQ] at h0
  cases h0

/-- **Negative**: a seed with `n = 0` starts no chain. -/
theorem short_not_chain : ¬ IsChain [(seedQ (ansOf 1000) 0 (ansOf 1001), ansOf 0)] 0 := by
  have hs := seedOf_seedQ (ansOf 1000) (n := 0) (by norm_num) (ansOf 1001)
  rintro ⟨-, s, n, h, h0, h1, -⟩
  have : predIdx [(seedQ (ansOf 1000) 0 (ansOf 1001), ansOf 0)] 0 = none := by
    simp [predIdx, stateIn_of_seedOf hs]
  rw [pathOf_of_pred_none this] at h0
  have he : entriesOf [(seedQ (ansOf 1000) 0 (ansOf 1001), ansOf 0)] [0] =
      [(seedQ (ansOf 1000) 0 (ansOf 1001), ansOf 0)] := rfl
  rw [he] at h0
  simp only [List.getElem?_cons_zero, Option.bind_some, hs, Option.some.injEq,
    Prod.mk.injEq] at h0
  omega

/-- **Positive**: the last entry is on the frontier. -/
theorem honest1_frontier : OnFrontier honest1 honest1[116]! := by
  refine ⟨getElem!_pos honest1 116 (by rw [honest1_length]; omega) ▸
    List.getElem_mem (by rw [honest1_length]; omega), ?_⟩
  intro hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hj' : j < 117 := by rwa [honest1_length] at hj
  rw [getElem!_pos honest1 116 (by rw [honest1_length]; omega),
    honest1_get 116 (by rw [honest1_length]; omega), honest1_get j hj] at heq
  simp only at heq
  by_cases hj0 : j = 0
  · subst hj0
    rw [shape0_zero] at heq
    have := congrArg tagOf heq
    simp [qOf] at this
  · simp only [hj0, ↓reduceIte] at heq
    rcases qOf_eq_squeezeQ heq with h2 | h2
    · have := ansOf_inj (by omega) (by omega) h2
      omega
    · exact shape0_ne_seed j (by rw [shape0_length]; exact hj') (by omega) h2

/-- **Negative**: the squeeze of entry `115`'s answer is in the log. -/
theorem honest1_not_frontier : ¬ OnFrontier honest1 honest1[115]! := by
  rintro ⟨-, hn⟩
  apply hn
  rw [getElem!_pos honest1 115 (by rw [honest1_length]; omega),
    honest1_get 115 (by rw [honest1_length]; omega)]
  refine List.mem_map.mpr ⟨honest1[116]'(by rw [honest1_length]; omega),
    List.getElem_mem _, ?_⟩
  rw [honest1_get 116 (by rw [honest1_length]; omega)]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
  rw [shape0_last]
  rfl

end SoundnessLogControls

end SpartanChain
