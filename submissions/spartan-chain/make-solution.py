#!/usr/bin/env python3
"""Make the solution module from the rendered challenge (the organiser's stub rendered with
claim.json; interim, the core branch `v3/ks-interim-harness`'s `scripts/render-challenge.py`): the
organiser's definitions verbatim, the challenge's two placeholders filled, and the entry imported.

  python3 -I make-solution.py CHALLENGE.lean OUT.lean

The entry's final module `SpartanChainFinal` supplies `SpartanChain.leafVerifier`,
`SpartanChain.proveLeafR1` and `SpartanChain.facts : Facts leafVerifier proveLeafR1` (the parts of
`Verifier.lean`, `Prover.lean`, `Completeness.lean`, `Soundness/KS.lean`). Then
`submission := SpartanChain.submission leafVerifier proveLeafR1` (noncomputable: `ε = 2^-129` is a
real; the comparator ignores the keyword) and `certified := certificateR_of …`: the image binding
by `rfl`, the declared error `1/2^128` by `εR1_le_declared`, the query bound `2^14 ≤ 16384` and the
affine fuel by arithmetic. Asserts that each placeholder occurs once and no `sorry` remains.
"""
import sys
src, out = sys.argv[1:3]
s = open(src).read()
old = "import RecursionFast.Contract\n"
assert s.count(old) == 1, "no contract import"
s = s.replace(old, old + "import SpartanChainFinal\n", 1)
old = "def submission : Submission := sorry"
assert s.count(old) == 1, "no submission placeholder"
s = s.replace(old, "noncomputable def submission : Submission :=\n"
              "  SpartanChain.submission SpartanChain.leafVerifier SpartanChain.proveLeafR1", 1)
old = "theorem certified : CertificateR declared submission := sorry"
assert s.count(old) == 1, "no certified placeholder"
s = s.replace(old, """theorem certified : CertificateR declared submission :=
  SpartanChain.certificateR_of _ _ SpartanChain.facts declared rfl SpartanChain.εR1_le_declared
    (show SpartanChain.qVR1 ≤ 16384 by decide)
    fun t => ⟨show 8 ≤ 8 + 0 * t by omega, show 8 + 0 * t ≤ 2 ^ 40 + 2 ^ 8 * t by omega⟩""", 1)
assert "sorry" not in s.split("-/", 1)[1], "unreplaced sorry"
open(out, "w").write(s)
