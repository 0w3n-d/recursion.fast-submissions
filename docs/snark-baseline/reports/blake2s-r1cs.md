# Report: the BLAKE2s chain block (`Blake2sR1CS`, L-C1, L-C4 walk)

Module group "Blake2sR1CS" of BLUEPRINT-R1 §2.1–§2.2, §2.4.2, §9.4 (L-C1, L-C4 `walk_eq_sum`),
§10, §10.1, §11.3 (2). Root `submissions/spartan-chain/`, seven flat modules. Every module builds,
and none contains `sorry`. Every listed theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (`logs/spartan-chain/blake2s-r1cs/axioms.log`). The source rule reports 0 findings on
the root.

## Provenance

The code is copied from leanerVM (Apache-2.0), `main` at `95957214d42b6d5e21d7066f760e5ec256514cf8`.
The circuit file last changed in `e715c49`. The same files are byte-identical on the branch
`docs/protocol-headline-theorems` at `532ebb4`, so no unmerged branch carries a newer version.
Each file has its own provenance block.

## What was built

| module | content | code lines |
|---|---|---|
| `SpartanChainBlake2sCircuit` | copy of `Flock/Circuit.lean` and a cut-down `Flock/BlockR1CS.lean`: `Form`, `ProductCircuit`, `rowOf`, `toBlockR1CS`, `BlockR1CS.Holds`, `traceF`/`trace`, `Bounded`, `trace_satisfies`, `holds_eq_trace`, `gates_of_holds`, `eq_trace_of_holds_isBool`, plus the new `traceF_of_not_mem` | 450 |
| `SpartanChainBlake2sWords` | copy of `Flock/Builder.lean` and `Flock/Words.lean`: `Builder`, `Sound`, `Ok`, `addW`/`add3W` with `sound_*`/`ok_*` | 630 |
| `SpartanChainBlake2sCompress` | copy of `Protocol/Blake2sCircuit.lean`, re-targeted to the contract's `compress` (bridge `den_rotr` via `Blake2s.rotr_eq_rotateRight`): `blake2sCircuit`, `bounded_blake2s`, `blake2s_sound_of_gates`, `blake2s_sound(_words)`, `blake2s_complete` | 463 |
| `SpartanChainBlake2sR1CS` | the chain block and **L-C1**: `h0`, `stepWords`, `leDigest`, `chainStep_eq`, `constPositions`/`constBit`/`constGates`, `chainInputs`, `chainBlock`, `bounded_chainBlock`, `readByte`/`readDigest`, `block_sound`, `block_complete`, `chainTrace`, controls | 324 |
| `SpartanChainBlake2sGeneric` | the gadgets once more, over an abstract interpretation `GOps m α S` (zero, xor, var, product gate = `res` and `upd`), and the simulation framework `Generic.Sim` with `sim_compressW` | 337 |
| `SpartanChainBlake2sWalk` | the verifier's walk: `formVal`, `walkOps`, `walkAB`, `sum_rows`, **`walk_eq_sum` (L-C4 part)** | 180 |
| `SpartanChainBlake2sWitness` | the prover's witness, `fastTrace` (Boolean interpretation) with `fastTrace_eq`; the KAT dump (`chainBlockAt`, `circuitRows`, `circuitRows_eq`, `rowLine`, `dumpCircuit`, `dumpTrace`) | 215 |

Total: 2 599 code lines (`.contract/scripts/loc.py`, 229 theorems). About 1 540 of them are the
leanerVM copy and about 1 060 are new. The umbrella `SpartanChain.lean` imports
`SpartanChainBlake2sR1CS` and `SpartanChainBlake2sWitness`, which reach all seven modules.

## What is proved (statements)

Everything is over any `CommRing R` with `CharP R 2`, plus `Nontrivial R` for the soundness
direction. The walk needs `R : Type`. This covers the entry's `F` and `EF` (`SpartanChainField`
has `Field`/`CharP 2` instances), and the walk was run on `EF`. No `Field` import is needed.

* **L-C1 `block_sound`.** Let `z : Pos 14 → Bool` with
  `chainBlock.toBlockR1CS.Holds (liftBlock R z)` and `z constPos = true`. Then
  `readDigest z 256 = chainStep (readDigest z 648)`. Here `readDigest z b` has byte `e`, bit `b'` at
  `b + 8e + b'`, and `chainStep` is the contract's own (`Relation.lean`).
* **L-C1 `block_complete`.** Holds `(liftBlock R (chainTrace d))`, `chainTrace d constPos = true`,
  `readDigest (chainTrace d) 648 = d`, and `readDigest (chainTrace d) 256 = chainStep d`.
* `chainStep_eq`: `chainStep d = leDigest (compress h0 (block (0x43 :: d)) 33 0xFFFFFFFF 0)`. This is
  one compression of the contract's BLAKE2s, proved by unfolding `blake2s`.
* **L-C4 `walk_eq_sum`.** `walkAB e wt` equals
  `(Σ_k if k = 512 then 0 else e k * mulVec A wt k, the same for B)`, where `A`, `B` are
  `chainBlock.toBlockR1CS`. **Row 512 is skipped**, as required by review BP-m5.
* `fastTrace_eq`: `(fastTrace d)[k]? = some (chainTrace d k)` for every position. This is the
  prover's witness generation, `O(|circuit|)` Boolean operations.
* `circuitRows_eq`: the dumped rows are `(List.finRange 2^14).map chainBlock.rowOf`.

## Controls (§10.1)

* Positive: `chainTrace_zero_kat`. The honest trace of the zero digest satisfies the R1CS and carries
  `954ac2a4…418d8d` = `hashlib.blake2s(0x43‖0^32)`. This rests on `chainStep_zero_kat`, checked by
  `decide +kernel` on the contract's BLAKE2s. The compression is never unrolled in the kernel.
* Negative: `not_holds_flip`. For **every** satisfying block with `1` at 512, in particular every honest
  trace, flipping any output bit in `256 … 511` breaks `Holds`. It is a theorem, not a kernel run.
* Runtime cross-check (scratch, `logs/…/interp-run.log`): `fastTrace` of the zero digest has output
  bytes `[149, 74, 194, 164, …]` = `0x95 0x4a 0xc2 0xa4 …`, which is the KAT.
* `walkAB` has no separate negative control. `walk_eq_sum` fixes its value exactly.

## Build and run times (measured)

* `lake build +SpartanChainBlake2sWitness`, all seven modules rebuilt on a loaded machine (other agents
  were building): Circuit 40 s, Words 53 s, Compress 56 s, Generic 21 s, R1CS 21 s, Walk 4.8 s,
  Witness 9.0 s, 3 m 23 s wall (`logs/spartan-chain/blake2s-r1cs/lake-build-full.log`).
* An earlier rebuild of the same modules was much faster (Circuit 4.1 s … Compress 34 s, about 77 s in all).
  That log was overwritten; the per-file `lean -o` times are in `times.log`.
* Nothing unrolls `2^14` rows during elaboration. `blake2sCircuit` and `chainBlock` are
  `@[irreducible] noncomputable`.
* Interpreter only (`lake env lean`, `#eval` in `scratch/`; a compiled measurement is still open):
  * `fastTrace`: 117 ms.
  * `walkAB` on `EF`: 15.9 s, presumably dominated by interpreted field multiplications (about
    3·10⁴ `EF` products); not profiled.
  * building the circuit rows: 28 s.

## Deviations from the blueprint, with reasons

1. **Constant rows are recorded as gates in the `ProductCircuit`** (BP-M3, fix (a)). Both
   `(var 512, var 512)` (bit 1) and `(0, 0)` (bit 0) are gates placed before the compression's.
   This keeps `chainBlock` `Bounded` (`bounded_chainBlock`). The matrices are exactly the §2.2
   table: a `(0,0)` gate row equals a padding row.
   * Constant positions: `0…255`, `640…647` and `904…1279`.
   * There is no `holds_chainBlock_imp`. Soundness goes through `gates_of_holds` on `chainBlock` and
     the gate-level `blake2s_sound_of_gates`, so the review's added `z 512 = true` hypothesis is
     moot.
2. **`BlockR1CS m` keeps only the two Boolean matrices.** It has no ring parameter and no walks.
   `Holds` takes `z : Fin 2^m → R`, so the statement is `chainBlock.toBlockR1CS.Holds (liftBlock R z)`,
   not `(… .toBlockR1CS E)`. The batch/linearity/adjoint parts of `BlockR1CS.lean` are not copied.
3. **The generic form type is a second program, not a rewrite of leanerVM's.**
   * The bitset gadgets stay verbatim, so their proofs are untouched.
   * `Generic.sim_compressW` proves that the generic program, under any interpretation linear in
     `φ`, returns `φ` of the bitset forms and accumulates `upd` over exactly the recorded gates.
   * This is the §2.4.2 simulation invariant, applied twice: walk (`φ = Σ_j L_j wt_j`) and
     evaluation (`φ = eval z`).
4. **Closed terms.** `blake2sCircuit`, `chainBlock` and `chainTrace` are `noncomputable`, because a
   compiled closed term runs when the executable starts. The dump uses the computable
   `@[never_extract] chainBlockAt base` (`chainBlockAt_eq`).
   * Still closed and computable: `initW` (512 forms of 2 KiB), `constGates` (640 forms), `inputs`,
     `chainInputs`, `start`.
   * They are initialised at start-up, a few MiB. This has not been measured.
5. leanerVM's `private` lemmas are public. `rowOf c k` is now `c.rowOfList c.gates.toList k`; this
   is definitional. `traceF_of_not_mem` is new.
6. `import Batteries.Data.BitVec.Lemmas` (leanerVM's import). It is in `Mathlib`'s import closure
   (`Mathlib.lean` imports `Batteries`), so gate rule 6 allows it.

## Open

* The compiled timing of `walkAB` and `fastTrace`. `Run.lean` should measure them.
* The Rust `circuit` KAT. The format is fixed in the `SpartanChainBlake2sWitness` docstring: `k`,
  then two forms, each as 256 × 16 hex digits, lowest 64-bit chunk first.
* Merging `walkAB` into Chain's `Ã, B̃` formula (§2.4: `A0̃(r_k, r_j) = walkAB(eq(r_k,·), eq(r_j,·)).1`).
  Chain also needs `fastTrace` → `chainWitness`.
* One linter warning (an unused `simp` argument) remains in `SpartanChainBlake2sWitness`.
