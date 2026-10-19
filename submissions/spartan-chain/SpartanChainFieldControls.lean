import SpartanChainFieldExtCorrect

/-!
# Controls for the field layer

Kernel-checked evaluations of the compiled operations on fixed inputs, positive and negative.
They pin the conventions a wrong constant would silently change: the bit order (bit `i` is `x^i`),
the base modulus (`x^64 = x^4 + x^3 + x + 1`), the extension modulus (`y^3 = y + 1`) and the
little-endian byte order.
-/

namespace SpartanChain.FieldControls

open SpartanChain

/-- `x * x = x^2`: bit `1` times bit `1` is bit `2`. -/
theorem mul_x_x : (⟨2⟩ : F) * ⟨2⟩ = ⟨4⟩ := by decide +kernel

/-- Negative: `x * x` is not `x + 1`, as a wrong bit order or integer product could give. -/
theorem mul_x_x_ne : (⟨2⟩ : F) * ⟨2⟩ ≠ ⟨3⟩ := by decide +kernel

/-- `x^63 * x = x^64 = x^4 + x^3 + x + 1`, the modulus. -/
theorem mul_wraps : (⟨0x8000000000000000⟩ : F) * ⟨2⟩ = ⟨0x1B⟩ := by decide +kernel

/-- Negative: the wrap is not the GHASH or AES constant. -/
theorem mul_wraps_ne : (⟨0x8000000000000000⟩ : F) * ⟨2⟩ ≠ ⟨0x87⟩ := by decide +kernel

/-- `x^63 * x^63 = x^126`, which needs both folds of `reduce`. -/
theorem sq_top : F.sq ⟨0x8000000000000000⟩ = (⟨0x8000000000000000⟩ : F) * ⟨0x8000000000000000⟩ := by decide +kernel

/-- The inverse of `x`: `x * x⁻¹ = 1`. -/
theorem mul_inv_x : (⟨2⟩ : F) * (⟨2⟩ : F)⁻¹ = 1 := by decide +kernel

/-- Negative: `x` is not its own inverse. -/
theorem inv_x_ne : (⟨2⟩ : F)⁻¹ ≠ ⟨2⟩ := by decide +kernel

/-- `y^3 = y + 1` in `EF`. -/
theorem y_cube : (⟨0, 1, 0⟩ : EF) * ⟨0, 1, 0⟩ * ⟨0, 1, 0⟩ = ⟨1, 1, 0⟩ := by decide +kernel

/-- Negative: `y^3` is not `y^2 + 1` (the modulus `y^3 + y^2 + 1`). -/
theorem y_cube_ne : (⟨0, 1, 0⟩ : EF) * ⟨0, 1, 0⟩ * ⟨0, 1, 0⟩ ≠ ⟨1, 0, 1⟩ := by decide +kernel

/-- The inverse of `y` in `EF`: `y * y⁻¹ = 1`. -/
theorem mul_inv_y : (⟨0, 1, 0⟩ : EF) * (⟨0, 1, 0⟩ : EF)⁻¹ = 1 := by decide +kernel

/-- Bytes are little-endian: the low byte comes first. -/
theorem toBytes_le : (F.toBytes ⟨0x0807060504030201⟩).toList = [1, 2, 3, 4, 5, 6, 7, 8] := by
  decide +kernel

/-- Negative: not big-endian. -/
theorem toBytes_not_be :
    (F.toBytes ⟨0x0807060504030201⟩).toList ≠ [8, 7, 6, 5, 4, 3, 2, 1] := by decide +kernel

/-- The encoding agrees with CompPoly's on a value (an instance of `F.toBytes_eq`). -/
theorem toBytes_bf64 : (F.toBytes ⟨0x0807060504030201⟩).toList =
    (CompPoly.ByteCodec.toBytes (F.toBF64 ⟨0x0807060504030201⟩)).toList :=
  F.toBytes_eq _

end SpartanChain.FieldControls
