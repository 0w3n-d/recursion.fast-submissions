/-
# Local runner of the baseline's compiled code (not the badge path)

The executable (`entry-run`, built by the interim core branch's `scripts/setup-scratch.sh`; called
`baseline-run` below) runs the compiled code of the certified
constant `RecursionFast.Challenge.submission` (the solution module), for `smoke.py`, the
calibration and the liveness inputs, until S3's badge executables replace it:

* `baseline-run verify STMT.hex PROOF.bin`: the instantiated verifier `Submission.Vb` on the
  statement (64 hex digits) and the proof; exit 0 on accept, 1 on reject, 2 on a usage or IO
  error. It
  prints the verifier's own wall time (the call, without process start-up) on standard error.
* `baseline-run prove-leaf START.hex N OUT.bin` and
  `baseline-run prove-node C1.hex C2.hex PROOF1.bin PROOF2.bin OUT.bin`: the honest prover `P` (run
  with the BLAKE2s oracle; it asks no query) on a leaf or a node witness.
-/
import BaselineV3Solution

namespace BaselineV3Run
open RecursionFast

/-- The value of one hex digit. -/
def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Bytes from hex digits, two per byte. -/
def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: r => do
    let x ← hexDigit a
    let y ← hexDigit b
    let t ← parseHex r
    pure ((x * 16 + y) :: t)
  | [_] => none

/-- A digest from 64 hex digits. -/
def digestOfHex (s : String) : Option Digest := do
  let l ← parseHex s.trimAscii.toString.toList
  if h : l.toArray.size = 32 then some ⟨l.toArray, h⟩ else none

/-- Read a digest file (64 hex digits). -/
def readDigest (path : String) : IO Digest := do
  match digestOfHex (← IO.FS.readFile path) with
  | some d => pure d
  | none => throw (IO.userError s!"{path}: not a digest (64 hex digits)")

/-- `verify`: the compiled `Submission.Vb` of the certified submission. -/
def verify (stmt proof : String) : IO UInt32 := do
  let c ← readDigest stmt
  let π ← IO.FS.readBinFile proof
  let t₀ ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => Challenge.submission.Vb c π
  let t₁ ← IO.monoNanosNow
  let verdict := if b then "accept" else "reject"
  IO.eprintln s!"Vb: {verdict} in {(t₁ - t₀) / 1000} us ({π.size} bytes)"
  pure (if b then 0 else 1)

/-- Run the honest prover on a witness and write the proof. -/
def prove (w : Wit) (out : String) : IO UInt32 := do
  IO.FS.writeBinFile out ((Challenge.submission.P (Vector.replicate 32 0) w).run blake2sOracle)
  pure 0

/-- Dispatch on the subcommand. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | ["verify", stmt, proof] => verify stmt proof
  | ["prove-leaf", s, n, out] =>
    match n.toNat? with
    | some n => prove (.leaf (← readDigest s) n) out
    | none => throw (IO.userError s!"{n}: not a number")
  | ["prove-node", c₁, c₂, p₁, p₂, out] =>
    prove (.node (← readDigest c₁) (← readDigest c₂) (← IO.FS.readBinFile p₁)
      (← IO.FS.readBinFile p₂)) out
  | _ =>
    IO.eprintln "usage: baseline-run verify STMT.hex PROOF.bin | prove-leaf START.hex N OUT.bin | \
      prove-node C1.hex C2.hex PROOF1.bin PROOF2.bin OUT.bin"
    pure 2

/-- The subcommands; any IO error (an unreadable file, a malformed statement) exits with 2, never
with the verifier's reject code 1. -/
def main (args : List String) : IO UInt32 :=
  try run args catch e => do IO.eprintln s!"baseline-run: {e}"; pure 2

end BaselineV3Run

/-- The executable's entry point. -/
def main (args : List String) : IO UInt32 := BaselineV3Run.main args
