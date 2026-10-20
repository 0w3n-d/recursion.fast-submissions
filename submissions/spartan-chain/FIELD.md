# The field layer of `spartan-chain`

`F = GF(2^64)` in one `UInt64` and `EF = GF(2^192) = F[y]/(y^3+y+1)` in three, with compiled
word arithmetic, proved equal to CompPoly's `BF64` and `BF64.Ext3` (CompPoly `572f997`, the
organiser's field library, design §7.4).

| module | what |
|---|---|
| `SpartanChainFieldBase` | `F`: the word operations (definitions only) |
| `SpartanChainFieldBaseCorrect` | `toBF64`, the agreement proofs, `Field F`, cardinality, bytes, `conj_distinct` |
| `SpartanChainFieldExt` | `EF`: the operations (definitions only) |
| `SpartanChainFieldExtCorrect` | `toExt3`, the agreement proofs, `Field EF`, `Algebra F EF`, cardinality, bytes, `ybasis` |
| `SpartanChainFieldControls` | kernel-decided positive and negative controls on fixed values |
| `SpartanChainField` | the umbrella |

Imports: Mathlib and CompPoly's `BF64` closure only (`BF64.Bytes`, `BF64.Ext3`). No `sorry`,
`native_decide`, `partial`, `unsafe`, code-changing attribute or elaboration-time code; the
source rule (`.contract/scripts/source-rule.py`) reports 0 findings.

## Conventions (checked against CompPoly, and pinned by the controls)

* **Bit order.** Bit `i` of the word is the coefficient of `x^i` (`BF64`'s `BitVec 64`
  coordinates; `F.toBF64 a = BF64.ofBitVec a.val.toBitVec`). Modulus `x^64 + x^4 + x^3 + x + 1`
  (`x^64 = 0x1B`, control `mul_wraps`).
* **Extension.** `EF.mk c₀ c₁ c₂ = c₀ + c₁ y + c₂ y^2`, `y^3 = y + 1` (CompPoly `ext3Params`,
  lower coefficients `#v[1, 1, 0]`, coefficient vector in ascending order; control `y_cube`).
* **Bytes.** `F.toBytes`: the 8 little-endian bytes of the word (CompPoly's
  `ByteCodec BF64`, `u64::to_le_bytes`). `EF.toBytes`: the three coefficient encodings
  concatenated, `c₀` first (CompPoly's `ByteCodec (Ext P)`). Both decoders are total and
  bijective (`ofBytes_toBytes`, `toBytes_ofBytes`).

## API

`namespace SpartanChain`:

* `F` (`structure F where val : UInt64`), `F.ofUInt64`, `F.toUInt64`, `F.x` (the generator
  `x`), `+ - * ⁻¹ /` and `^` (binary powers), `F.sq`, `F.frob k` (`k` squarings),
  `F.toBytes : F → Vector UInt8 8`, `F.ofBytes`.
* `EF` (`structure EF where c₀ c₁ c₂ : F`), `EF.mk c₀ c₁ c₂`, `EF.ofF`, `EF.y`, `+ - * ⁻¹ /`,
  `^`, `EF.sq`, `EF.frob k`, `EF.smulBase` (three `F` products), `EF.toBytes : EF → Vector UInt8 24`,
  `EF.ofBytes`.
* Instances: `Field`, `CharP · 2`, `DecidableEq`, `BEq`, `Hashable`, `Finite`, and a
  noncomputable `Fintype` for both (a computable enumeration of `2^64` elements would be a closed
  term evaluated at program start); `Algebra F EF` by `ofF`.
* Maps: `F.toBF64`, `F.ofBF64`, `F.equivBF64`, `F.ringEquivBF64 : F ≃+* BF64`; `EF.toExt3`,
  `EF.ofExt3`, `EF.equivExt3`, `EF.ringEquivExt3 : EF ≃+* BF64.Ext3`.

**Write hot loops monomorphic in `F`/`EF`.** A generic `[CommRing R]` loop instantiated at `F`
goes through the instance dictionary and boxes each `UInt64` (measured: 2.2x slower per product,
below).

## Algorithms

* `F` product: a branch-free shift-and-add carry-less product, 64 steps (`mulStep`, four per
  round of `mulLoop`), state in five words so the compiled loop allocates nothing; then `reduce`
  folds the high word with one multiplication by `x^4 + x^3 + x + 1` of
  `d = hi ⊕ hi≫63 ⊕ hi≫61 ⊕ hi≫60`.
* `F` square: bit spreading (5 mask-and-shift steps per half) and `reduce`.
* `F` inverse: CompPoly's Itoh–Tsujii chain (63 squarings, 10 products).
* `EF` product: three-term Karatsuba (6 `F` products), reduction by `y^3 = y + 1`.
* `EF` square: 3 `F` squares. `EF` inverse: adjugate column `w` of the multiplication matrix,
  `x * w = det ∈ F`, `x⁻¹ = det⁻¹ · w` (one `F` inverse, ~9 products and 3 squares).

## What is proved (theorem names; axioms `propext`, `Classical.choice`, `Quot.sound` only)

* `F.toBF64_add`, `toBF64_mul`, `toBF64_sq`, `toBF64_inv`, `toBF64_div`, `toBF64_npow`,
  `toBF64_frob`, `toBF64_natCast`; `F.ringEquivBF64`; `F.instField`; `F.nat_card_F`, `F.card_F`;
  `F.frob_eq_pow : frob k a = a ^ 2 ^ k`.
* The product proof is against CompPoly's specification, not its code: each word denotes a
  polynomial over `ZMod 2` (CompPoly's `toPoly`), `mulStep_inv` keeps
  `lo + x^64 hi + a(bl + x^64 bh)` invariant, `mk_reduce` maps `lo + x^64 hi` to its class in
  `AdjoinRoot basePoly`, and CompPoly's injective multiplicative `BF64.toQuot` closes
  `toBF64_mul`. No case split over `2^64` values; `bv_decide` is not used.
* `EF.toExt3_add`, `toExt3_mul`, `toExt3_sq`, `toExt3_inv`, `toExt3_div`, `toExt3_npow`,
  `toExt3_ofF`, `toExt3_y`; `EF.mul_adj` (the adjugate identity); `EF.ringEquivExt3`;
  `EF.instField`; `EF.nat_card_EF : Nat.card EF = 2 ^ 192`, `EF.card_EF`; `EF.frob_eq_pow`.
* Bytes: `F.toBytes_eq` (the list of bytes is `ByteCodec.toBytes (toBF64 a)`'s),
  `F.ofBytes_eq` (`toBF64 (ofBytes v) = CanonicalNat.ofBytesModOrder v`), `EF.toBytes_eq`,
  `EF.toExt3_ofBytes`, and the round trips. CompPoly's `Extension.Bytes` and `Data.Bytes.Vector`
  are outside the import allowlist, so the `EF` codec is stated through `BF64`'s codec.
* Kernel-decided facts (`decide +kernel` on the word arithmetic, no extra axiom):
  `F.conj_distinct : ((List.range 64).map (fun k => x ^ 2 ^ k)).Nodup` and
  `EF.ybasis : ∀ k < 64, det[1, y^(2^k), y^(2^(k+1))] ≠ 0` (coordinates as columns, as
  `Matrix.det` of the `!![…]`; `det_coords` expands it).
* Controls (`SpartanChainFieldControls`): `x·x = x^2`, `≠ x + 1`; `x^63·x = 0x1B`, `≠ 0x87`;
  `sq` on the top bit; `x·x⁻¹ = 1`, `x⁻¹ ≠ x`; `y^3 = y + 1`, `≠ y^2 + 1`; `y·y⁻¹ = 1`;
  little-endian bytes and not big-endian.

## Kernel cost (nanoda)

`logs/field/nanoda.log`. Every field module's closure checks under the second kernel (nanoda)
in about 71 s and 2.4 GB. That is CompPoly's own floor: `BF64.Impl` alone takes 75 s and
2.3 GB. The field-specific decided facts take seconds or less: the decided part of
`conj_distinct` 1.6 s, the three values of `ybasis` 0.5 s, the controls 3.4 s. `spread_getLsbD`
is proved by five mask-and-shift stage lemmas (linear index arithmetic, `omega`), not a 64-way
case split. `^` on `F` and `EF` is `powGo` (square-and-multiply with structural fuel), not
Mathlib's `npowBinRec`. `F.x_pow_word` proves `x ^ i = 1 <<< i` (`i < 64`) through the polynomial
instead of by evaluation.

## Measurements

Log: `logs/field/bench-20261019-185727.log` (machine, toolchain, source hashes, three runs); axioms:
`logs/field/axioms.log`. Compiled Lean, `QEMU Virtual CPU` (KVM, 32 vCPU), Lean 4.34.1.
Every loop is a dependency chain or an accumulator whose value is printed (no dead code); the
same run cross-checks 200 random inputs against CompPoly (a test; the proofs are above).

| operation | n | ns/op (3 runs) | median | CompPoly | speed-up |
|---|---|---|---|---|---|
| `F` add | 10^7 | 2.2 / 2.6 / 2.1 | 2.2 | | |
| `F` mul (latency chain) | 10^6 | 89 / 83 / 87 | **87** | 30,300 (`BF64.mul`, n = 10^5) | ~350x |
| `F` mul (independent) | 10^6 | 89 / 95 / 93 | 93 | | |
| `F` sq | 10^6 | 10 / 9.8 / 9.8 | 9.8 | | |
| `F` inv | 10^6 | 1518 / 1438 / 1506 | **1,506** | 1,780,000 (Itoh–Tsujii, n = 10^3) | ~1,200x |
| `EF` mul | 10^6 | 551 / 524 / 535 | **535** | 466,000 (`Ext3.mul`, n = 500) | ~870x |
| `EF` sq | 10^6 | 30 / 29 / 42 | 30 | | |
| `EF` inv | 10^6 | 2295 / 2217 / 2194 | **2,217** | 1.67·10^8 (`x^(q^3-2)`, n = 3) | ~75,000x |
| `F` mul through a generic `CommRing` dictionary | 10^6 | 186 / 169 / 178 | 178 | | |

Targets: `F` mul ≤ 0.2 µs (reached, 0.087 µs); `EF` mul ≤ 2 µs (reached, 0.54 µs).

**What limits it.** The `F` product is instruction-bound: 64 steps of about ten word operations
(the loop is unrolled four steps per round and allocates nothing; the emitted C keeps every
word unboxed). Compiled Lean has no carry-less-multiply instruction (`pclmulqdq` would be one
instruction) and no small fixed arrays without allocation, so a windowed table method does not
pay. `EF` mul is six `F` products. A generic `[CommRing R]` loop boxes every `UInt64` through
the instance dictionary: 2x slower.

## Names against the blueprint (`docs/snark-baseline/BLUEPRINT-R1.md` §10, row `Field.lean`)

The blueprint's `toBF64 : F ≃+* BF64` and `toExt3 : EF ≃+* Ext3` are `F.ringEquivBF64` and
`EF.ringEquivExt3`; `F.toBF64` and `EF.toExt3` are the underlying functions (the simp normal
form). `sq` and `frob k` exist for both fields (`F.sq`, `F.frob`, `EF.sq`, `EF.frob`), with
`frob_eq_pow`. `conj_distinct` is `F.conj_distinct`, `ybasis` is `EF.ybasis`; `ybasis` is decided
for `k < 3` and transported by `y^(2^3) = y` (`EF.frob_three_y`, `EF.frob_y_mod`), because the
direct 64-case `decide +kernel` hits the kernel's recursion limit.

