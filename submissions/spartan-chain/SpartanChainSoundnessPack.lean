import SpartanChainSoundnessDefs

/-!
# The bit-plane packing lemma in the knowledge state's names (review S2b-M4)

`SoundnessPCS.qDec_bitplanes(_EF)` restated for `KS.qPack` (the decoded packed witness, §5.2's
layout) and the bit planes `wDec κ U (Fin.cast (pack_eq κ) (join i u))` (§4.1: position
`i + 64 u` is bit `i` of `q_dec(u)`), in the exact form `absorb_gR0` uses.
-/

namespace SpartanChain.KS

open PCS SoundnessPCS

/-- **`qPack_eq_sum`**: `q_dec(u) = Σ_{i<64} Q_i(u) · x^i` over `F`. -/
theorem qPack_eq_sum (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ))) :
    qPack κ U u =
      ∑ i : Fin 64, wDec κ U (Fin.cast (pack_eq κ) (join (i : Fin (2 ^ 6)) u)) * F.x ^ (i : ℕ) :=
  qDec_bitplanes κ U u (qRow_lt κ u) (fun i => Fin.cast (pack_eq κ) (join i u))
    (fun i => by simp [join])

/-- **`qPack_ofF_eq_sum`**: the same over `EF`, `EF.ofF (q_dec(u)) = Σ_i ι(x^i) · EF.ofF (Q_i(u))`. -/
theorem qPack_ofF_eq_sum (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ))) :
    EF.ofF (qPack κ U u) =
      ∑ i : Fin 64, algebraMap F EF (F.x ^ (i : ℕ)) *
        EF.ofF (wDec κ U (Fin.cast (pack_eq κ) (join (i : Fin (2 ^ 6)) u))) :=
  qDec_bitplanes_EF κ U u (qRow_lt κ u) (fun i => Fin.cast (pack_eq κ) (join i u))
    (fun i => by simp [join])

end SpartanChain.KS
