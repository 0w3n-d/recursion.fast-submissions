import SpartanChainLigero
import SpartanChainRingSwitch
import SpartanChainBlake2sWitness
import RecursionFast.Contract.Certificate

/-!
# Known-answer dumps (BLUEPRINT-R1 §11.3)

Pure functions producing, line for line, the text the Rust prover's `dump-*` commands write
(`kat.rs`; formats in `docs/snark-baseline/reports/rust-prover.md` §5). A driver outside the entry
root writes them to files, and `kat.py` diffs the two sides. Nothing here is on the badge path, and
nothing here is a closed term: every dump takes an argument.

Inputs come from `katRand tag i = blake2s256("spartan-chain-kat/" ‖ tag ‖ 0x00 ‖ enc64 i)`: a
`K` element is its bytes `0..8`, an `E` element is `chE` of it.

Hex: a `K` value as 16 lowercase hex digits of its word (most significant first), an `E` value as
`c₀.c₁.c₂`, byte strings as two digits per byte in order.
-/

namespace SpartanChain.Kat

open RecursionFast ProductCircuit Blake2sCircuit

/-! ## Text helpers -/

/-- Lowercase hex digit. -/
def hexDigit (d : ℕ) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- `n` as exactly `w` hex digits (most significant first). -/
def hexNat (w n : ℕ) : String :=
  String.ofList ((List.range w).reverse.map fun i => hexDigit (n / 16 ^ i % 16))

/-- A byte string. -/
def hexBytes (b : List UInt8) : String := String.join (b.map fun x => hexNat 2 x.toNat)

def hexF (a : F) : String := hexNat 16 a.val.toNat

def hexE (x : EF) : String := hexF x.c₀ ++ "." ++ hexF x.c₁ ++ "." ++ hexF x.c₂

def hexEs (xs : List EF) : String := " ".intercalate (xs.map hexE)

def lines (ls : List String) : String := String.join (ls.map (· ++ "\n"))

/-! ## Inputs -/

/-- `blake2s256("spartan-chain-kat/" ‖ tag ‖ 0x00 ‖ enc64 i)`. -/
def katRand (tag : String) (i : ℕ) : Digest :=
  blake2sDigest ("spartan-chain-kat/".toUTF8.toList ++ tag.toUTF8.toList ++ [0] ++ enc64 i)

def randF (tag : String) (i : ℕ) : F := F.ofBytes (Vector.ofFn fun j : Fin 8 => (katRand tag i)[j.1])

def randE (tag : String) (i : ℕ) : EF := Transcript.chE (katRand tag i)

def randEs (tag : String) (n : ℕ) : List EF := (List.range n).map (randE tag)

/-! ## `field`: products, squares, byte codecs -/

def dumpField (count : ℕ) : String :=
  lines <|
    ((List.range count).map fun i =>
      let a := randF "field-k-a" i
      let b := randF "field-k-b" i
      s!"kmul {i} {hexF a} {hexF b} {hexF (a * b)} {hexF (F.sq a)} {hexBytes a.toBytes.toList}") ++
    ((List.range count).map fun i =>
      let a := randE "field-e-a" i
      let b := randE "field-e-b" i
      s!"emul {i} {hexE a} {hexE b} {hexE (a * b)} {hexE (EF.sq a)} {hexBytes a.toBytes.toList}")

/-! ## `mle`: `eq` tables, an evaluation, `eq` of two points -/

def dumpMle (len : ℕ) : String :=
  let r := randEs "mle-r" len
  let r2 := randEs "mle-r2" len
  let t := (Array.range (2 ^ len)).map (randE "mle-t")
  let eqs := (eqTable r).toList
  lines <|
    (eqs.zipIdx.map fun (e, u) => s!"eq {u} {hexE e}") ++
    [s!"mle {hexE (mleEval t r)}", s!"eqpts {hexE (eqPts r r2)}"]

/-! ## `transcript-ops`: the primitives under `blake2sOracle` -/

/-- The absorbed message lengths, one per kind `1 … 8`. -/
def trLens : List ℕ := [0, 1, 31, 32, 33, 63, 64, 200]

def trMsg (i len : ℕ) : ByteArray :=
  ⟨((List.range len).map fun j => (katRand s!"tr-msg-{i}" (j / 32))[j % 32]!).toArray⟩

def dumpTranscriptOps (n : ℕ) : String := Id.run do
  let H := blake2sOracle
  let mut st := (Transcript.seed (katRand "tr-s" 0) n (katRand "tr-h" 0)).run H
  let mut out : List String := [s!"seed {hexBytes st.toList}"]
  for (len, i) in trLens.zipIdx do
    st := (Transcript.absorb st (UInt8.ofNat (i + 1)) (trMsg i len)).run H
    out := out ++ [s!"absorb {i + 1} {len} {hexBytes st.toList}"]
    for _ in [0, 1] do
      st := (Transcript.squeeze st).run H
      out := out ++ [s!"squeeze {hexBytes st.toList} {hexE (Transcript.chE st)}"]
  for ln in [12, 10] do
    let r := (Transcript.squeezeIdx st ln 260).run H
    st := r.1
    let idx := ",".intercalate (r.2.map toString)
    out := out ++ [s!"idx {ln} {hexBytes st.toList} {idx}"]
  return lines out

/-! ## `encode`: `Enc` at every point, `k = 512`, `N = 4096` -/

def dumpEncode (nmsg : ℕ) : String :=
  let ks := Ligero.kapArr 9
  lines <| (List.range nmsg).flatMap fun i =>
    let msg := (Array.range 512).map (randE s!"encode-{i}")
    (List.range 4096).map fun c => s!"enc {i} {c} {hexE (Ligero.encAtE ks 9 msg (Ligero.ptOf c))}"

/-! ## `phi`: ring switching -/

def dumpPhi (nr : ℕ) : String :=
  let fs := randEs "phi-f" 6
  let s := (Array.range 64).map (randE "phi-s")
  lines <|
    ((phiTable fs).toList.zipIdx.map fun (c, k) => s!"ck {k} {hexE c}") ++
    ((List.range 16).map fun i =>
      let a := randE "phi-a" i
      s!"phi {i} {hexE a} {hexE (phiApply fs a)}") ++
    [s!"target {hexE (target (EF.ofF F.x) fs s)}",
     "weight " ++ hexE (weightEval fs (randEs "phi-r" nr) (randEs "phi-r2" nr))]

/-! ## `sumcheck`: honest product rounds at fixed challenges -/

def prodExpr : Expr := .mul (.var 0) (.var 1)

def dumpSumcheck (len : ℕ) : String :=
  let f := (Array.range (2 ^ len)).map (randE "sc-f")
  let g := (Array.range (2 ^ len)).map (randE "sc-g")
  let rs := randEs "sc-r" len
  let polys := honest prodExpr #[f, g] rs
  let fin := bindAll #[f, g] rs
  lines <|
    (polys.zipIdx.map fun (p, l) => s!"round {l} {hexEs p.toList}") ++
    [s!"final {hexE ((fin.getD 0 #[]).getD 0 0)} {hexE ((fin.getD 1 #[]).getD 0 0)}"]

/-! ## `walk`: `A0̃`, `B0̃` of the chain block (row 512 skipped) -/

def dumpWalk (count : ℕ) : String :=
  lines <| (List.range count).map fun i =>
    let e := eqTable ((List.range 14).map fun l => randE "walk-rk" (14 * i + l))
    let wt := eqTable ((List.range 14).map fun l => randE "walk-rj" (14 * i + l))
    let ab := walkAB (fun k : Pos Blake2sCircuit.m => e[k.val]!) (fun k => wt[k.val]!)
    s!"walk {i} {hexE ab.1} {hexE ab.2}"

/-! ## `circuit`: the rows of `chainBlock` -/

/-- The 256 little-endian words of a form. -/
def formWords (L : Form Blake2sCircuit.m) : List UInt64 :=
  (List.range 256).foldl (fun (p : List UInt64 × ℕ) _ => (p.2.toUInt64 :: p.1, p.2 >>> 64))
    ([], L.toNat) |>.1.reverse

/-- Population count of a word. -/
def popcount (w : UInt64) : ℕ :=
  (List.range 64).foldl (fun c j => c + ((w >>> j.toUInt64) &&& 1).toNat) 0

def wordsBytes (ws : List UInt64) : List UInt8 :=
  ws.flatMap fun w => (List.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8

/-- One line per position of `chainBlock`'s `rowOf` (`circuitRows_eq`, row 512 included):
`k`, the popcounts of the two forms, `blake2s256` of each form as 2048 little-endian bytes. -/
def dumpCircuit (_ : Unit) : String :=
  lines <| (circuitRows gateBase).zipIdx.map fun (g, k) =>
    let a := formWords g.a
    let b := formWords g.b
    s!"{k} {(a.map popcount).sum} {(b.map popcount).sum} \
      {hexBytes (blake2sDigest (wordsBytes a)).toList} {hexBytes (blake2sDigest (wordsBytes b)).toList}"

/-! ## `leaf`: the `n = 1` leaf recomputed from the Rust prover's challenges and tables -/

/-- What `leaf-input.txt` carries: the statement, the challenges, the bit tables `Az`, `Bz`,
`Cz`, `z = (w ‖ pub)` as `0/1` values, the packed witness `q`, and the dense `M̃ρ(r_x, ·)`. -/
structure LeafInput where
  s : Digest
  n : ℕ
  h : Digest
  tau : List EF
  rx : List EF
  rho : EF
  ry : List EF
  f : List EF
  r2 : List EF
  A : Array EF
  B : Array EF
  C : Array EF
  z : Array EF
  q : Array F
  M : Array EF

/-- The outer summand `eq · (A·B + C)`, tables `0 … 3`. -/
def outerExpr : Expr := .mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))

/-- Bit `i` of every word of `q`, as `0/1` in `EF` (the bit-plane `Q_i`). -/
def plane (q : Array F) (i : ℕ) : Array EF :=
  q.map fun w => if (w.val >>> i.toUInt64) &&& 1 = 1 then 1 else 0

def dumpLeaf (inp : LeafInput) : String :=
  let H := blake2sOracle
  let κ := 0
  let cm := (Ligero.commit κ inp.q).run H
  let st := (Transcript.seed inp.s inp.n inp.h).run H
  let p1 := (Ligero.prove1 κ st cm).run H
  let ubar := Ligero.readEFs p1.2.2.2 0 (PCS.msgLen κ)
  let outer := honest outerExpr #[eqTable inp.tau, inp.A, inp.B, inp.C] inp.rx
  let vabc := [mleEval inp.A inp.rx, mleEval inp.B inp.rx, mleEval inp.C inp.rx]
  let inner := honest prodExpr #[inp.M, inp.z] inp.ry
  let rhi := (inp.ry.drop 6).take (8 + κ)
  let sl := (Array.range 64).map fun i => mleEval (plane inp.q i) rhi
  let rs := honest prodExpr #[weightTable inp.f rhi, inp.q.map EF.ofF] inp.r2
  lines <|
    [s!"root {hexBytes (cm.root κ).toList}"] ++
    (ubar.toList.zipIdx.map fun (e, j) => s!"ubar {j} {hexE e}") ++
    (outer.zipIdx.map fun (g, l) => s!"outer {l} {hexEs g.toList}") ++
    [s!"vabc {hexEs vabc}"] ++
    (inner.zipIdx.map fun (g, l) => s!"inner {l} {hexEs g.toList}") ++
    (sl.toList.zipIdx.map fun (e, i) => s!"slice {i} {hexE e}") ++
    [s!"target {hexE (target (EF.ofF F.x) inp.f sl)}"] ++
    (rs.zipIdx.map fun (g, l) => s!"rs {l} {hexEs g.toList}")

end SpartanChain.Kat
