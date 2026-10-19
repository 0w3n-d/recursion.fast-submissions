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

## Round 2: `SpartanChainSoundnessLog.lean` and measurements

**Build.** The dev clone now builds flat modules (`./refresh-roots.sh`, then
`lake build +SpartanChainMerkle +SpartanChainSoundnessLog +SpartanChainTranscriptControls`):
2093 jobs, green. The source rule finds nothing on 32 files. Axioms are standard
(`logs/…/axioms-log.txt`).

### What `SpartanChainSoundnessLog.lean` proves

All statements are against the amended contract (`logCap = 2^96`) and the review's fixes S9-M2
and S9-M3.

- **L-K1 `bad_step_le`.** On a log with `¬ Bad L` and a fresh query `q`, at most
  `|L|·(3·2^8 + 1) + 1` answers make `L ++ [(q,a)]` bad. The `+1` is the new query's own state,
  as the `i ≤ j` state hit requires. `bad_step_frac` restates it with `|L| < 2^96`. Helpers:
  - `card_trunc_fiber`: each label has exactly `2^8` preimages.
  - `length_labelsIn`: a query carries at most 2 labels.
- **Transcript forest (§9.1).** `ansIdx`, `predIdx` and `pathOf`, the path of predecessors that
  ends at an entry. `predIdx_lt` says the predecessor is earlier under `¬ Bad`.
- **L-K8 `fresh_leaf`.** Assume `¬ Bad (L ++ [(q,a)])`.
  - Every old entry keeps its predecessor and its path (`predIdx_append_old`,
    `pathOf_append_old`).
  - The new entry's path is its predecessor's path in `L` followed by the new entry, or the new
    entry alone (`back_new`, with `predIdx_new`).
- **Frontier (S9-M2).** `OnFrontier` and `frontier_append`: a fresh query removes from the
  frontier only the entries whose squeeze it is.
- **L-K2, generic (`extCount_split`).** For any event `P`, the sum over `a` of
  `#completions(pre ++ [a], k)` equals `#completions(pre, k+1)`. This is the review's
  `roundPot_split`, the martingale step of R0 and R7.
- **Controls** (in `SpartanChainTranscriptControls.lean`):
  - `pathOf_linked`: a seed, absorb, squeeze log forms the path `[0,1,2]`.
  - `pathOf_orphan`: a squeeze whose state nothing answers is a path of its own.

### Left open

- **The §6.2 match of a chain.** The kinds and lengths of the absorbs and squeezes depend on
  `n`'s shape, which lives in the verifier modules. It belongs with L-K4.
- **L-K4 `runLog_chain`, intended statement.** Assume `¬ Bad L` and
  `(leafProg c π).runLog L = some b`. Then:
  - The run's Fiat–Shamir queries, in the order asked, are answered by entries
    `i_1 < i_2 < … < i_r` of `L`. These are unique by `entry_unique` and ordered by
    `pred_unique_lt`.
  - The path of the last entry is `pathOf L i_r = [i_1, …, i_r]`.
  - `seedOf q_{i_1} = some (s, n, h)` of the proof, and the absorb messages are the proof's
    fields.
  - With `L = L₀ ++ L[i_2] :: L₁`, where `i_2` is the `absorb(root)` entry, every Merkle
    sub-run is `verify root c col ss`, so `open_binding_prefix` applies.
  - If `b = true`, the chain is complete: `r = 1 + 1 + m + … + J`.

  The proof route is `runLog_eq_some_iff` (the run is the run under `logOracle L`),
  `runLog_bind` to split off the sub-runs, `stateIn_absorbQ` and `stateIn_squeezeQ`.

### Measurements

The run used a compiled exe outside the root (`logs/…/OmtBench.lean`, `bench.log`), 3 runs, at
`n = 16`:

| operation | time |
|---|---|
| one oracle call on 33 bytes | 5.9–7.3 µs |
| Merkle `build`, N = 4096 columns of 64 bytes (8191 queries) | 65–77 ms |
| 260 openings (`path` + `verify`, 260 × 13 queries) | 25–28 ms |
| one leaf's transcript (60 absorbs ≈ 28 KB, 97 squeezes, 260 indices) | 9.7–11.3 ms |

Whole process: 0.21 s wall, 84 MB.

### Contract finding: the amended contract cannot start in compiled code

- **The defect.** Core branch `v3/ks-potential` (c3f6380) has, in `Contract/Security.lean:74`,
  `instance : Fintype Digest := Fintype.ofSurjective …`. It is a nullary computable instance, so
  every executable that imports `Contract.Security` (hence `Certificate`, and this entry's
  `verify`) evaluates it at module initialisation, which enumerates `256^32` functions.
- **The evidence** (`logs/…/init-blowup.log`):
  - An exe whose only import is `Contract.Security` and whose `main` prints "hello" reaches 22.9 GB
    in 20 s without printing.
  - A copy of the instance in a probe reproduces it.
  - The pinned `15e4ae5` has no such instance; it uses `Nat.card`.
- **The fix** is a one-word change in the core: `noncomputable instance`. The bench above ran in
  a private clone with that change (`/home/devops/Verified-zkEVM/omt-bench-core`). Nothing in
  the shared clone or the core was edited.
- `rf-core-sc/lakefile.toml` gained a scratch `omt-bench` exe entry, marked "SCRATCH ONLY". It
  starts only after this fix.

**Code lines** (`loc.py`): SoundnessLog 276; Controls now 83; all five files 1 352 lines,
132 theorems.

## Round 3: §9.1 chains and L-K4 `runLog_chain`

### §9.1 chains (`SpartanChainSoundnessLog.lean`)

These are the second-review items, named exactly as §9.1 has them.

- **Definitions.**
  - `Step` with `Step.matches`, which checks the tag, the length (seed 73, absorb `34 + len`,
    squeeze 33) and the absorb's kind byte, through `Step.check`.
  - `shape`, `len` and `entriesOf`.
  - `Matches`, decidable through `matchesB` (`matches_iff`).
  - `IsChain`, `chains`, `cut` and `L₀`.
- **Lemmas.**
  - `L₀_append`.
  - `split_at_cut`: `L = L₀ ++ L[cut] :: drop`, with `parseAbsorbRoot L[cut].1 = some root`.
  - **L-K8 `chains_append`**: `chains (L ++ [e]) = chains L ++ [L.length]?`.
  - `isChain_new`: a new chain is a seed with no predecessor, or extends its predecessor's chain.
  - `isChain_new_of_seed` and `isChain_new_of_extend`: the converse directions.
  - Helpers: `matches_of_append`, `matches_append`, `pathOf_getLast?`, `mem_pathOf_le` and
    `cut_le`.

### L-K4 (`SpartanChainSoundnessChain.lean`, new module)

**The main theorem.** `runLog_chain ev (hb : ¬Bad L) (hn : 1 ≤ n) (hcap : n ≤ chainCap)
(hsz : off₃ (kap n) ≤ π.size) (hacc : (snarkProg ev s n h π).runLog L = some true) :
SoundnessFinal.RunChain ev L s n h`.

**Two extra hypotheses.** These are needed; without them the statement is false:

- `hcap`: `Matches` requires `n ≤ chainCap`, and `snarkProg` does not check it.
- `hsz`: `snarkProg` reads bytes past the end of a short proof as zeros. The `absorb(root)`,
  `absorb(ū)` and `absorb(v)` messages are extracts of `π`, so on a short proof they have the
  wrong lengths and the run is no chain.

`leafProg` checks both before the SNARK runs. **`hchain_of_leafProg`** derives them, giving
`mu_final_leaf`'s `hchain` exactly, and **`mu_final_leaf_closed`** is `mu_final_leaf` with
`hchain` discharged.

**How it is proved.**

1. `chain_of_linked`: under `¬Bad`, linked entries of `L` are the path of their last entry.
2. The verifier's Fiat–Shamir entries are built as explicit blocks: `sqBlock`, `rdBlock`,
   `v1Block`, `spBlock`, `v2Block` and `fsEntries`. Lemmas give each sub-program's run and query
   list in terms of the blocks (`run_spartan`, `run_verify1`, `queries_*`).
3. `snark_accept` analyses an accepting run.
4. Block-position lemmas identify every §9.1 field with the verifier's value: `rootOf_fs`,
   `rVec_fs`, `ubarOf_fs`, `tauOf_fs`, `gOut_fs`, `rxOf_fs`, `triOf_fs`, `rhoOf_fs`, `gIn_fs`,
   `ryOf_fs`, `slicesOf_fs`, `fsOf_fs`, `gRs_fs`, `rrOf_fs`, `vOf_fs` and `bOf_fs`.
5. `verifyRounds_some` and `check_some` give `¬Rej` (`not_rej`).
6. `linked_fs` and `steps_fs` (the §6.2 shape) give `Matches`.

**Controls** (`SpartanChainSoundnessLogControls.lean`, proved symbolically):

- `honest1_chain`: the full 117-entry transcript of a 1-leaf is a chain.
- `broken_not_chain`: with one state byte changed it is not.
- `short_not_chain`: a seed with `n = 0` starts no chain.
- `honest1_frontier` and `honest1_not_frontier`.

The first version decided these with `decide +kernel`. That took 7 m 45 s, a single `predIdx`
needed 5.3 GB, and parallel runs were killed for memory (`controls-decide-profile.log`). The
symbolic version checks in 7.5 s.

**Status.**

- No `sorry`, standard axioms (`axioms-chain.txt`), and the source rule finds nothing.
- Code lines: SoundnessLog 598, SoundnessChain about 1 100, controls 39 → about 120.

## Round 4: the `final` law (`SpartanChainSoundnessKSFinal.lean`)

**`mu_final`** has the contract's `KState.final` shape and is proved. It takes:

- the verifier `V LV`, with `LV := Leaf.leafVerifier chainEvals`;
- the library's extractor `WitnessSending.E`;
- the relation `Rel (vb LV)`;
- the potential `KS.μ chainEvals`.

`final_law` is the same law with its binders in `KState.final`'s order.

How the two branches are proved:

- **Off the leaf branch** (nodes and every other tag) it uses `final_of_not_leaf` and
  `checkNode_rel`. These proofs make no queries.
- **On the leaf branch**, `final_of_leaf` gives the decoding `.leaf s n`. `mu_final_leaf_closed`
  gives `n ≤ chainCap`, `c = leafStmt h n` and `chainEnd s n = h`, through L-K4, L-K3 and
  `doom_of_not_esc`.

**Status.**

- Axioms are standard (`axioms-ksfinal.txt`), and the source rule finds nothing.
- 22 code lines.
- The R0 and R7 `hround` instances were not redone. They are the KS agent's `round_r0_le`,
  `round_r7_le` and `round_le` in `SpartanChainSoundnessKSBase.lean`.
