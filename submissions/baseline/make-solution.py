#!/usr/bin/env python3
"""Make the solution module from the rendered challenge (the organiser's stub rendered with
claim.json by the interim core branch's `scripts/render-challenge.py`): the organiser's
definitions verbatim, the challenge's two placeholders filled, and the entry's library imported.

  python3 -I make-solution.py CHALLENGE.lean OUT.lean

`submission := BaselineV3.submission`; `certified` is the entry's certificate, the image binding by
`rfl` (the rendered image is definitionally the library's literal) and the declared numbers by
arithmetic. Asserts that each placeholder occurs exactly once and that no `sorry` remains.
"""
import sys
src, out = sys.argv[1:3]
s = open(src).read()
old = "import RecursionFast.Contract\n"
assert s.count(old) == 1, "no contract import"
s = s.replace(old, old + "import BaselineV3\n", 1)
old = "def submission : Submission := sorry"
assert s.count(old) == 1, "no submission placeholder"
s = s.replace(old, "def submission : Submission := BaselineV3.submission", 1)
old = "theorem certified : CertificateR declared submission := sorry"
assert s.count(old) == 1, "no certified placeholder"
s = s.replace(old, """theorem certified : CertificateR declared submission :=
  ⟨BaselineV3.certificate, rfl, zero_le, le_rfl,
    fun t => ⟨show 8 ≤ 8 + 0 * t by omega, show 8 + 0 * t ≤ 2 ^ 40 + 2 ^ 8 * t by omega⟩⟩""", 1)
assert "sorry" not in s.split("-/", 1)[1], "unreplaced sorry"
open(out, "w").write(s)
