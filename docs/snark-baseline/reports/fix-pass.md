# Fix pass: final review `V3-S2b-review.md` (findings assigned to this agent)

The only code edits are controls, one docstring and a de-duplication in the KAT module. No
statement on the certificate path changed, and `SpartanChainFinal`, `SpartanChainSubmission` and
`SpartanChainSolution` are untouched.

- **Build.** `lake build SpartanChain` is green: 2288 jobs, 1 min 58 s wall, warm.
- **Source rule.** It reports `61 files, 0 finding(s)`.
- **Axioms.** The new controls use only `propext`, `Classical.choice` and `Quot.sound`
  (`logs/spartan-chain/rs-proximity/axioms-fixpass.log`).

| finding | status | what changed |
|---|---|---|
| **V3-S2b-m1** ("memcpy cost" claim) | **fixed (documentation)** | See below. |
| **V3-S2b-m5 / S2b-m7** (booleanity load-bearing) | **fixed** | See below. |
| **V3-S2b-m5 / S2b-m10** (279 linter warnings) | **argued** | See below. |
| **V3-S2b-m5 / S2b-m11** (stale documentation) | **fixed** | See below. |
| **V3-S2b-m5 / S2b-m12** (the KAT's own `outerExpr`) | **fixed** | See below. |
| **V3-S2b-m6** (no kernel negative for `ε`) | **fixed (Lean side)** | See below. |

## V3-S2b-m1: the "memcpy cost" claim

`reports/submission-infra.md` claimed that caterpillar proofs now cost only memcpy speed. That
line is corrected. It now quotes the review's measurement:

- 6.8 s at depth 1 000;
- 64.0 s at depth 3 000;
- **275.0 s at depth 6 000** (1 008 080 B), about 80 ns per byte and 4.6 × `verify_s`
  (`logs/s2b-final-review-probes/caterpillar/`).

This is stated as a DoS-column property of this unranked entry: it affects `verify` on a
statement the prover chose, not the runner-fixed root and sample checks. The other mentions,
`decode.md` and `verifier-top.md`, state `O(|π|·depth)` with S2a's measurement and were already
correct. No other "memcpy" claim exists in `docs/` or the root. As the review decided, the code
stays under the freeze.

## V3-S2b-m5 / S2b-m7: booleanity is load-bearing

The chain R1CS has no booleanity rows by design: booleanity comes from the packing,
`wDec_bool`. New controls in `SpartanChainControls`, on the reduced AND row `x · y = out` over
`EF`:

- `and_gadget_bool`: with Boolean `x, y` and public `out = 1`, the row forces `x = y = 1`.
- `and_gadget_nonbool`: the non-Boolean `(y, y⁻¹)`, with `y ≠ 0, 1` (both by `decide +kernel`),
  satisfies the same row.

So a Boolean-only conclusion fails without the `0/1` hypothesis. This is the reduced-object form
of "a non-Boolean `w` satisfies `ChainSat` for a wrong end". That statement itself, a non-Boolean
solution of the full BLAKE2s chain R1CS, would mean solving the circuit over `EF` by hand, which
is out of scope. `C:chainSat_wrong_end` remains the Boolean negative.

## V3-S2b-m5 / S2b-m10: 279 linter warnings

Argued, not fixed. The warnings are linters only (unused simp arguments, unused tactics). Most
are in `SoundnessKSBase`, which is the KS agent's and the golf pass's, as the review itself
assigns. They change no statement and no proof, and the source rule and the axiom audit are
unaffected. The full build currently prints 284 warning lines.

## V3-S2b-m5 / S2b-m11: stale documentation

- `SpartanChainChain.lean`'s docstring no longer lists `chain_sound`/`chain_complete` as its own
  content. It points to `SpartanChainChainSound`. This is a docstring edit only.
- `reports/blake2s-r1cs.md`'s Open section marks the walk merge and the circuit KAT as done.
- The `controls.md` line the midreview flagged (M3) quoted escape bounds that did not exist then.
  `esc_single_le` now exists (`SoundnessKS.lean:823`), and the inventory gains rows for the new
  controls.

## V3-S2b-m5 / S2b-m12: the KAT's own `outerExpr`

`SpartanChainKat.lean` no longer defines `Kat.outerExpr`. It imports `SpartanChainSoundnessSpartan`,
so `honest outerExpr …` now uses `SpartanChain.outerExpr`, the definition the prover and the
proofs use. The two were textually equal, so the KAT output is unchanged.

## V3-S2b-m6: a kernel negative for `ε`

`C:claim_eps_negative`, for every leaf verifier and prover:

```lean
¬ CertificateR { claimR1 with ε := 2⁻¹ ^ 130 } (submission LV pl)
```

It follows the review's probe and goes through `CertificateR.bounds` against `εR1 = 2⁻¹^129`.
It sits in `SpartanChainControls.lean`, beside `Submission:claim_negatives` (image, fuel, `qV`),
and so does not touch `Submission.lean`.

Not done: `check.sh` step 8's `error` variant. That is script-level, belongs to the S2a
implementer, and is left to them.
