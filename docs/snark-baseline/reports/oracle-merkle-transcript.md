# Report: Oracle, Merkle and Transcript modules (`spartan-chain`, R1)

Scope: BLUEPRINT-R1 §1.3, §5.3, §6, §9.1 (as revised after review BP-M1 and BP-M2), §9.4 L-M1–L-M4
and L-K7, and the §10 rows Oracle, Merkle and Transcript. Root `submissions/spartan-chain/`.
Every module builds with no `sorry`. Axioms are `propext`, `Classical.choice` and `Quot.sound`
only (`logs/spartan-chain/oracle-merkle-transcript/axioms.txt`). The source rule reports 0
findings on the root (`source-rule.txt`).

## What was built

| module | content |
|---|---|
| `SpartanChainOracle.lean` | `OProg.bind`, a lawful `Monad OProg`, `ask`; `run`, `queries` and `runLog` lemmas for `bind`, `map`, `pure`, `List.mapM` and `Array.mapM`. The log view: `logOracle L` and **`runLog_eq_some_iff`**: `p.runLog L = some b ↔` (every query of `p` under `logOracle L` is in `L`) ∧ `p.run (logOracle L) = b`. Also `find?_logOracle`, `mem_logOracle`, `logOracle_eq` and `runLog_append`. Every query format in one place: `leafQ`, `nodeQ`, `seedQ`, `absorbQ`, `squeezeQ`, the 31-byte `Label` and `trunc`, `bytesOf`, and the `*_data` byte-list lemmas. |
| `SpartanChainMerkle.lean` | Prover side: `build` (all levels, an `OProg` over `Array`), `root` and `path`. Verifier side: `climb` and `verify`, an `OProg Bool`. Specification: `lab`, with `run_build`. Log side: the parsers `parseLeaf`, `parseNode` and `parseAbsorbRoot`, with `labelsIn`, `pre`, the per-column `colL` (`col_L`), the filled column `colOr`, `Collision` and `Hit`. |
| `SpartanChainTranscript.lean` | `seed`, `absorb`, `squeeze`, `squeezeN`, `chE`, `squeezeE`, `natLE`, `idxOf`, `cnt`, `nAns`, `indices` and `squeezeIdx`, with the run and query lemmas of `squeezeN`. The fiber-count lemmas. On the log side: `stateIn`, `seedOf` (with `seedOf_seedQ`), `StateHit`, `Repeated`, **`Bad`**, `bad_append` and **L-K7 `pred_unique_lt`**. Also `query_eq_of_answer` and `entry_unique`. |
| `SpartanChainTranscriptControls.lean` | Known-answer and non-vacuity controls under `blake2sOracle`, all `decide +kernel` (see below). |

All three modules are also imported by the umbrella file `SpartanChain.lean`. Downstream API in
use: `SpartanChainLigero.lean` uses `build`, `root`, `path`, `verify`, `path_complete`,
`squeezeE`, `indices` and `idxOf`. None of these changed.

## What is proved

### Blueprint lemmas

- **L-M1 `Merkle.path_complete`.** For every `H`, every `cols` with `size = 2^ℓ` and every
  `c < 2^ℓ`, `verify (root lv ℓ) c cols[c] (path lv ℓ c)` runs to `true`, where
  `lv = (build cols ℓ).run H`.
- **L-M2 `Merkle.tree_of_log`.** Assume the log is consistent with `H`, contains every query of
  the build and has `¬ Collision`. Then `colL L w (root …) ℓ c = some cols[c]` for every
  `c < 2^ℓ`.
- **L-M3, in two parts.**
  - `Merkle.open_binding`: same log, needs only `¬ Collision`. If
    `(verify root c col ss).runLog L = some true`, `|col| = w` and `|ss| = ℓ`, then
    `colL L w root ℓ c = some col`.
  - `Merkle.open_binding_prefix`: the restated form, with `¬ Collision` and `¬ Hit`. Write the log
    as `L₀ ++ e :: L₁`, where `e` is the `absorb(root)` entry. Then the verified column is
    `colL L₀ …`.
- **L-M4 `Merkle.tree_prefix`.** Under `¬ Hit (L₀ ++ e :: L₁)`, where `e` absorbs `root`,
  `colL (L₀ ++ e :: L₁) … = colL L₀ …`. Helper lemmas: `colL_prefix`, `colL_append` and
  `colL_of_append_one`.
- **L-K7 `Transcript.pred_unique_lt`.** Assume `¬ Bad`. For an entry with
  `stateIn q = some st`, at most one entry of the log answers `st`, and that entry comes earlier.

### Fiber-count lemmas (exact uniformity)

- `card_chE_fiber`: `#{a : Digest | chE a = x} = 2^64`. The decoder is abstracted in
  `card_fiber_dec24` (any bijective `Vector UInt8 24 → β`). `ofBytes_bijective` holds for
  `EF.ofBytes`.
- `card_idx_fiber`: if `ℓ·c ≤ 256`, each tuple of `c` indices below `2^ℓ` is hit by exactly
  `2^(256−ℓc)` answers.
- `card_chE_mem` and `card_idx_mem`: the same counts for a set `S`, giving `|S|·fiber`.
- `idxOf_testBit`: bit `j` of index `i` is bit `(iℓ+j) mod 8` of byte `⌊(iℓ+j)/8⌋`. This is the
  bit layout §6.1 specifies.

### Controls (all kernel-checked)

The expected bytes come from Python `hashlib`, through
`logs/spartan-chain/oracle-merkle-transcript/kat/transcript_kat.py`; its output is beside it.

| control | kind | what it checks |
|---|---|---|
| `kat_transcript` | positive | seed, absorb(root), then 2 squeezes equal `hashlib` |
| `kat_transcript_root_ne` | negative | one changed root byte changes the state |
| `kat_chE` | positive | `chE` reads three little-endian words |
| `chE_not_be` | negative | big-endian words do not match |
| `kat_indices` | positive | 10-bit indices of an answer |
| `kat_merkle_root` | positive | 2-leaf root |
| `kat_verify` | positive | honest opening verifies |
| `kat_verify_flip` | negative | a flipped column byte is rejected |
| `kat_verify_index` | negative | an opening at the wrong index is rejected |
| `colL_log4` | positive | `tree_L` on an honest 4-leaf log returns every column |
| `colL_log4_missing` | negative | with a leaf entry removed, that column is `none` and the others are still read |
| `bad_stateHit` | positive | `Bad` holds on a 2-entry log with a state hit |
| `not_bad_one` | negative | `¬ Bad` on a 1-entry log |
| `runLog_empty` | negative | a run on the empty log answers nothing |

## Measurements

- **Module compile times** (`lean -o`, private olean directory; `build-modules.log`,
  `build-final.log`):

  | module | time |
  |---|---|
  | Oracle | 6.4 s |
  | Merkle | 7.9 s |
  | Transcript | 10.3 s |
  | Controls | 71 s (the kernel's BLAKE2s evaluations) |

- **Code lines** (`loc.py`, `loc.txt`):

  | module | code lines |
  |---|---|
  | Oracle | 168 |
  | Merkle | 546 |
  | Transcript | 279 |
  | Controls | 75 |
  | **total** | **1 068** (112 theorems) |

## Deviations from the blueprint, with reasons

1. **L-M2 has the extra hypothesis `¬ Collision L`.** Without it the statement is false. An
   earlier entry whose answer has the root's label but a different query is `pre_L(root)`, and
   the tree read then fails.
2. **`StateHit` uses `i ≤ j`; §9.1 (iii) uses `i < j`.**
   - With `i < j`, an entry whose answer equals its own state field is not bad, and then
     `pred_L(e) = e`. §9.1's claim that the predecessor "precedes" (L-K7) is then false.
   - The extra case costs one more answer per step in L-K1's count.
3. **L-M4 is stated with the cut at the `absorb(root)` entry.** The log is written
   `L₀ ++ e :: L₁` with `parseAbsorbRoot e.1 = some root`.
   - §9.4's wording "some entry … at or after the cut" is false. Counterexample: `L₀ = []` and
     `L = [node entry, absorb(root)]`. Then `tree_L(root)` reads the node entry, `tree_{L₀}` is
     `none`, and `¬Bad` holds.
   - `e` must also be an absorb rather than an arbitrary carrier. A node query whose own answer is
     its child's label is not a hit under the strict `i < j`, and it would break the lemma.
4. **L-M3 comes in two forms.** `open_binding` works on one log and needs only `¬ Collision`.
   `open_binding_prefix` is the restated L-M3, using `¬ Collision ∧ ¬ Hit`.
5. **Locations and helpers.**
   - `Bad`, `stateIn`, `seedOf` and L-K7 are in Transcript; `labelsIn`, `col_L`, `Collision` and
     `Hit` are in Merkle. The blueprint places them in `Soundness/Log.lean`. They depend on
     nothing later.
   - `U_L` is provided as byte columns through `colOr` (missing columns become `fill`). Decoding
     to `K^m` is left to the PCS module.
   - Repeated queries are expressed as `¬ (L.map fst).Nodup`.

## Open

- L-K1, L-K4 and L-K8 (the transcript forest and chains) belong to `Soundness/Log.lean`. They are
  not done here; `runLog_eq_some_iff`, `pred_unique_lt`, `entry_unique` and `stateIn_*` are their
  inputs.
- The compiled speed of `build`/`verify` at `N = 4096` has not been measured. It needs a lake
  executable target, and flat modules are not lake targets in the dev clone. Oleans were built
  with `lean -o` into `rf-core-sc/scratch/omt-build`.
