# V3-S2b golf: `submissions/spartan-chain`

Golf pass on the honest SNARK entry at commit `0358ec5`. It edits in place. No definition's
meaning, theorem statement, byte format, compiled code path, `SpartanChainSubmission.lean`,
`SpartanChainFinal.lean`, `SpartanChainSolution.lean` or the challenge was touched. Nothing is
committed.

Logs are in `logs/spartan-chain/golf/`:

- `before/` and `after/`: per-module `lake env lean` logs. `times.txt` holds wall seconds and peak
  RSS in KiB. Both runs used 8 modules in parallel under `systemd-run … MemoryMax=8G timeout 900`
  on the shared machine (load 2 to 5), so every time is an upper bound.
- `build-after.txt`: the remaining warnings of `lake build SpartanChain`.
- `axioms.txt`: `#print axioms` output.

## Result

| quantity | before | after |
|---|---|---|
| code lines (`loc.py`, all `*.lean`) | 16770 | 16766 |
| total lines | 23179 | 23175 |
| sum of per-module check times (61 modules, s) | 682.5 | 621.5 |
| `lake build` warnings (lines with `warning`) | 284 | 28 |
| `lake build SpartanChain` | green | green |
| `source-rule.py` | 0 findings | 0 findings |
| `#print axioms SpartanChain.KS.ks` | propext, Classical.choice, Quot.sound | unchanged |
| `#print axioms RecursionFast.Challenge.certified` | propext, Classical.choice, Quot.sound | unchanged |

### Modules whose check time changed

| module | before (s) | after (s) | cause |
|---|---|---|---|
| `SpartanChainSoundnessLog` | 44.0 | 10.2 | `shape` |
| `SpartanChainSoundnessDefs` | 38.8 | 8.3 | `pre8` |
| `SpartanChainBlake2sCompress` | 38.9 | 14.1 | `blake2s_complete` |

All three modules are on the critical path of the soundness chain (`Log → Defs → KSBase → …`), so
a cold build gains about as much wall time as they lose. A cold `lake build` was **not** re-measured:
measuring it would mean deleting build products in the shared clone. All other modules stayed within
±2 s of their earlier time, which is noise on this machine.

## What changed

1. **`SoundnessLog.shape` and `KS.pre8`: elaboration from 37 s to 0.4 s each.**
   - **Cause:** the definitions are long `++` chains in which bare dot-constructors (`.squeeze`,
     `.absorb …`) appear as arguments of `List.replicate` and in list literals. The `binop%`
     elaborator postponed them and re-elaborated the tree. The profiler (`trace.profiler`) showed
     `Elab.definition.value` at 37.3 s for `shape` and 31.5 s for `pre8`.
   - **Fix:** write `Step.squeeze` and `Step.absorb` in those positions.
   - **Check:** for both definitions, the elaborated value with `pp.all` is **byte-identical** to the
     old one (compared in a scratch file outside the root). `shape_eq_pre8 … := rfl` still checks.
2. **`Blake2sCircuit.blake2s_complete`: 31 s down to under 0.5 s.**
   - **Cause:** the two `congr 1` calls first tried `isDefEq` on two applications of `compress`. That
     unfolded `compress` and `Vector.ofFn` (6.5 s and 23.7 s in the profiler).
   - **Fix:** replace them with the explicit congruences that `congr 1` produced:
     `refine congrArg (fun v : Vector UInt32 8 ↦ v[k]) ?_` and
     `refine congrArg₂ (fun a b ↦ compress a b _ _ _) ?_ ?_`.
   - **Note:** this proof was also fragile. With `trace.profiler` on, it hit the default heartbeat
     limit.
3. **215 + 3 unused simp arguments removed.**
   - **How:** a script read the linter's positions from the logs. The 3 arguments that sat on a
     continuation line were removed by hand.
   - **Where:** mostly in `SoundnessKSBase` (197). The others are in `SoundnessChain`, `SoundnessKS`,
     `ChainTables`, `ChainMle`, `ChainInner`, `ChainEval`, `Blake2sWitness` and
     `SoundnessLogControls`.
4. **Dead tactics removed.** Each of these was flagged both "never executed" and "does nothing":
   - the 13 trailing `| simp` alternatives of `first | rfl | (split_ifs <;> …) | simp` in
     `SoundnessKSBase`;
   - 2 `all_goals (congr 1 <;> omega)` in `Chain`;
   - 1 `all_goals (congr 2 <;> omega)` in `ChainCols`;
   - 1 `(try simp only [pU, …])` in `KSBase.posClass_r0`;
   - the dead `funext` branch in `SoundnessKS` (`convert hd using 2 <;> rfl`).
5. **Deprecations:**
   - `List.getLast?_eq_getLast` became `List.getLast?_eq_some_getLast` (`KSBase`).
   - In `SoundnessKS`, `dif_pos hu` / `dif_neg …` became `hu`, `(show ¬ … by omega)` and
     `↓reduceDIte` in the same `simp only`.

## Declined, and why

- **`SpartanChainTranscriptControls` (69 s, 4.0 GB).** It is the slowest module. Its time is
  `decide +kernel` running BLAKE2s on concrete data: these are the known-answer controls, and
  evaluating BLAKE2s is what they test. Making them cheaper would change what they check. They are a
  candidate for nanoda's memory budget and should be watched.
- **`SpartanChainSoundnessKSBase` (36–38 s).**
  - **What is slow:** the twelve `shape_*` position lemmas take 3 to 17 s each, run in parallel. The
    cost is in the discharger `first | (simp [length_flatten_rep2]; done) | (simp …; omega)`.
  - **What I tried:** replacing it with the equivalent single pass `simp [length_flatten_rep2] <;>
    omega` gave no wall-time gain (37.8 s), so I did not apply it.
  - **What would work:** a real fix proves the lemmas through `shape_eq_pre8` / `pre8_length` and
    `List.getElem?_append_*` at known lengths. That is a proof-strategy rewrite of 12 lemmas, too
    large for this time box.
- **`FieldBaseCorrect` `mask*` lemmas (`decide +kernel` over `j < 64`, about 4–5 s each, in
  parallel).** The alternatives are `interval_cases` splits, which are forbidden (large terms for
  nanoda), or a bit-pattern proof per mask. The module takes 15 s in total.
- **Remaining 28 warning lines:**
  - **12 `tac1 <;> tac2` linter hints.** The fix would introduce a naked `;`, which the golf policy
    forbids. The `<;>` is harmless.
  - **5 "automatically included section variable(s) unused".** `omit … in` would drop arguments
    from those theorems' signatures, which is a statement change.
  - **5 unused hypothesis names (`hiL`, `h2`, `hlen` ×2, `hv`).** They are all binders of theorem
    statements, so renaming them to `_h…` changes the displayed statement and any named-argument
    call.
  - **1 `exponent 16384` warning in `ChainInner`.** It is informational: the term is not evaluated,
    as intended.
  - The rest are the multi-line `Hint:` continuations of the warnings above.
- **`KSBase.shape_zero` and `shape_seed` are duplicates** (same statement). I removed neither:
  removing a theorem is outside a golf pass. The orchestrator may drop `shape_zero`, which is unused.
- **Line-count golf.** Not pursued beyond the dead code: priorities 1 and 2 used the time box.
  Net −4 code lines.

## Note

`docs/snark-baseline/PLAN.md` shows as modified in the working tree. This pass did not touch it.
