# V3-S2a golf: the witness-sending baseline entry

Scope: `submissions/baseline/*.lean`. No statement, definition, challenge, claim, byte format or
image changed; only two proof bodies in `BaselineV3.lean`. Compiled code is untouched.

## Line counts (the core's `scripts/loc.py`, code lines)

| file | before | after |
|---|---:|---:|
| `BaselineV3.lean` | 162 | 150 |
| `BaselineV3Controls.lean` | 55 | 55 |
| `BaselineV3Run.lean` | 51 | 51 |
| `BaselineV3Solution.lean` | 21 | 21 |
| **total** | **289** | **277** |

Totals with comments and blanks: 503 to 491 lines. Comment lines are unchanged (132).

## What changed

1. **`packFast_eq`** (15 to 7 code lines). Before: strong induction on the length, then a case
   split on `8 ≤ length`, through `packBytes_append8` and a separate tail case. After: functional
   induction over `packFast` (`fun_induction packFast b`). The cons case unfolds both `packBytes`,
   splits the word count `(len + 7) / 8` as `(len - 8 + 7) / 8 + 1` (one `omega` fact, true for every
   non-empty list, so it covers both earlier branches) and peels off the first word with
   `List.range_succ_eq_map`. This is the same argument `packBytes_append8` uses in the library.
2. **`bytesAtF_eq`** (5 to 1 code line). `simp only` + `congr 2` + `List.map_congr_left` + `rw` +
   `simp` became a single `simp [bytesAtF, bytesAt, wordByte_eq, List.getD_eq_getElem?_getD]`.
   The private helper `wordByte_eq` stays, because `simp` cannot use `← wordByte_packBytes` with
   `packBytes_wordsBytes` (it loops or does not fire; tried).

## Verification

- `timeout 1800 lake build BaselineEntry baseline-run` in the scratch clone `rf-core-s2a`: green.
  `lake env lean entry/BaselineV3.lean` prints no message (no warnings, no unused simp arguments).
- `submissions/baseline/check.sh`: `CHECK OK` (log `logs/V3-S2/golf-check.log`). Clean entry rebuild
  13.41 s and 15.13 s wall (the two timed steps of stage 4), axiom audit OK for 55 declarations,
  leanchecker 24.77 s, the three negative claims rejected, `SMOKE: OK`.
- `python3 -I .contract/scripts/source-rule.py submissions/baseline`: 4 files, 0 findings.

## Declined, and why

- **`decodeWitF_eq`** (`cases o` then `rfl` / `simp only`). `unfold decodeWitF decodeWit` +
  `simp only [bytesAtF_eq]` rewrites inside the match, but the two sides use different matchers,
  so the goal does not close without an extra `rfl`. That saves no line. `cases o <;> simp only`
  would apply `<;>` to two different goals, which the golf policy forbids.
- **`check_canonical`**. A one-line leaf branch
  (`of_decide_eq_true (Bool.and_eq_true _ _ ▸ Bool.and_eq_true _ _ ▸ h).1.1`) compiles, but the line
  is over 100 characters and harder to read than the `simp only … at h` + `exact` pair. A
  `split at h <;> simp_all` node branch moves up the tactic ladder to save one line.
- **`check_sound`, `fits_of_rel`, `check_encode`, `Vb_eq`, `size_le_of_Vb`, `check`'s
  `decreasing_by`**. These mirror the library's `WitnessSending` proofs line for line (for this
  entry's `submission.Vb`), and they are already short. Keeping the parallel helps a reviewer
  compare the two.
- **Controls** (`BaselineV3Controls.lean`). Each `rw [check_eq]; decide +kernel` is needed: `check`
  is well-founded recursion, so it must be rewritten to its `match` form before the kernel can
  decide it. `decode_leaf_kat`'s `show 16 < 2 ^ 64 by decide` cannot become `by decide`, because
  there is no `Decidable w₀.Fits` instance (tried). `lib_check_*` are single `rw` lines.
- **`BaselineV3Run.lean`**. This is compiled IO code for the local runner (hex parsing, the CLI).
  Golfing it would only change its shape, and the policy is to leave compiled hot code alone.
- **`BaselineV3Solution.lean`**. `make-solution.py` generates it from the rendered challenge, and
  `check.sh` step 5 compares it byte for byte. It cannot be edited by hand.

## Saturation

Five candidates were tried. Two were accepted and three rejected (`decodeWitF_eq`,
`check_canonical`, `decode_leaf_kat`). The last three attempts failed, so the pass stops here.
