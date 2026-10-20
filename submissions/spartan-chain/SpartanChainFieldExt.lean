import SpartanChainFieldBaseCorrect

/-!
# `GF(2^192)` as a cubic extension of `F`

`EF` is `F[y] / (y^3 + y + 1)` with coefficients `c₀ + c₁ y + c₂ y^2`: the modulus, the
coefficient order and the byte layout of CompPoly's `BF64.Ext3` (`ext3Params`, lower
coefficients `#v[1, 1, 0]`, CompPoly `572f997`). The operations are written out for degree three:

* addition is coefficientwise;
* multiplication is three-term Karatsuba (six `F` products) followed by the reduction
  `y^3 = y + 1`, `y^4 = y^2 + y`;
* squaring is three `F` squarings, since squaring is additive in characteristic two;
* inversion is the adjugate of the multiplication matrix: `x * w = det` for an explicit `w`
  quadratic in the coefficients, so `x⁻¹ = w * det⁻¹`, one inversion in `F`;
* bytes are the three coefficient encodings concatenated (CompPoly's `ByteCodec (Ext P)`).

The agreement with `Ext3` is in `SpartanChainFieldExtCorrect`.
-/

namespace SpartanChain

/-- An element `c₀ + c₁ y + c₂ y^2` of `F[y] / (y^3 + y + 1)`. -/
structure EF where
  /-- The constant coefficient. -/
  c₀ : F
  /-- The coefficient of `y`. -/
  c₁ : F
  /-- The coefficient of `y^2`. -/
  c₂ : F
  deriving DecidableEq, Inhabited, Hashable

namespace EF

instance : BEq EF := ⟨fun x y => x.c₀ == y.c₀ && x.c₁ == y.c₁ && x.c₂ == y.c₂⟩

instance : Repr EF := ⟨fun x _ => repr (x.c₀, x.c₁, x.c₂)⟩

instance : Zero EF := ⟨⟨0, 0, 0⟩⟩
instance : One EF := ⟨⟨1, 0, 0⟩⟩

/-- The base field element `c` as `c + 0 y + 0 y^2`. -/
@[inline] def ofF (c : F) : EF := ⟨c, 0, 0⟩

/-- Coefficientwise addition; it is also subtraction and negation is the identity. -/
@[inline] def add (x y : EF) : EF := ⟨x.c₀ + y.c₀, x.c₁ + y.c₁, x.c₂ + y.c₂⟩

instance : Add EF := ⟨add⟩
instance : Sub EF := ⟨add⟩
instance : Neg EF := ⟨fun x => x⟩

/-- Multiplication: Karatsuba over the three coefficients, then `y^3 = y + 1`. With
`d_k = ∑_{i + j = k} x_i y_j` the unreduced product, the result is
`(d0 + d3) + (d1 + d3 + d4) y + (d2 + d4) y^2`. -/
def mul (x y : EF) : EF :=
  let m0 := x.c₀ * y.c₀
  let m1 := x.c₁ * y.c₁
  let m2 := x.c₂ * y.c₂
  let m01 := (x.c₀ + x.c₁) * (y.c₀ + y.c₁)
  let m02 := (x.c₀ + x.c₂) * (y.c₀ + y.c₂)
  let m12 := (x.c₁ + x.c₂) * (y.c₁ + y.c₂)
  ⟨m0 + m12 + m1 + m2, m01 + m0 + m12, m02 + m0 + m1⟩

instance : Mul EF := ⟨mul⟩

/-- Multiplication by a base field element: three `F` products. -/
@[inline] def smulBase (c : F) (x : EF) : EF := ⟨c * x.c₀, c * x.c₁, c * x.c₂⟩

/-- Squaring: `(c₀ + c₁ y + c₂ y^2)^2 = c₀^2 + c₁^2 y^2 + c₂^2 (y^2 + y)`. -/
def sq (x : EF) : EF :=
  let s2 := F.sq x.c₂
  ⟨F.sq x.c₀, s2, F.sq x.c₁ + s2⟩

/-- The adjugate column `w` of `x`: `x * w` is the base field element `normOf x`. -/
@[inline] def adj (x : EF) : EF :=
  let s1 := F.sq x.c₁
  let s2 := F.sq x.c₂
  ⟨F.sq x.c₀ + s1 + s2 + x.c₁ * x.c₂, x.c₀ * x.c₁ + s2, s1 + x.c₀ * x.c₂ + s2⟩

/-- The determinant of multiplication by `x`, its norm to `F`. -/
@[inline] def normOf (x : EF) (w : EF) : F := x.c₀ * w.c₀ + x.c₂ * w.c₁ + x.c₁ * w.c₂

/-- The inverse, `adj x * (normOf x)⁻¹`, with `0⁻¹ = 0`. -/
def inv (x : EF) : EF :=
  let w := adj x
  smulBase (normOf x w)⁻¹ w

instance : Inv EF := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k`. The fuel `k` makes the
recursion structural on a natural number, so the kernel evaluates powers by peeling literals
(Mathlib's `npowBinRec` recurses through `Nat.binaryRec`, which the kernel unfolds slowly). -/
def powGo : Nat → EF → Nat → EF → EF
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow EF ℕ := ⟨fun a n => powGo n a n 1⟩

/-- The generator `y` of `EF` over `F`, a root of `y^3 + y + 1`. -/
def y : EF := ⟨0, 1, 0⟩

/-- The Frobenius power `x ^ (2 ^ k)`, by `k` squarings. -/
def frob : Nat → EF → EF
  | 0, x => x
  | k + 1, x => frob k (sq x)

/-- The three coefficient encodings concatenated, CompPoly's `ByteCodec Ext3` layout. -/
def toBytes (x : EF) : Vector UInt8 24 :=
  (x.c₀.toBytes ++ x.c₁.toBytes) ++ x.c₂.toBytes

/-- Decode three coefficients of eight bytes each; every byte string decodes. -/
def ofBytes (v : Vector UInt8 24) : EF :=
  ⟨F.ofBytes (Vector.ofFn fun i : Fin 8 => v[i.1]),
    F.ofBytes (Vector.ofFn fun i : Fin 8 => v[8 + i.1]),
    F.ofBytes (Vector.ofFn fun i : Fin 8 => v[16 + i.1])⟩

end EF

end SpartanChain
