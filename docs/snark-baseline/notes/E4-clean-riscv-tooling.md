# E4: Clean, RISC-V proof tooling and the harness at the pin

Exploration note for the honest recursive SNARK baseline: R1CS over BF64 or a prime field,
Spartan-style, with Merkle commitments and Fiat–Shamir over BLAKE2s. It budgets two Lean
obligations:

- **(a) circuit correctness.** The R1CS for one BLAKE2s compression, and for the whole verifier,
  is satisfiable iff the computation holds.
- **(b) `ImageComputes`.** A RISC-V image computes the extractor `E` within
  `2^40 + 2^8·t` steps.

Written 2026-10-19. I only read files and ran `scripts/source-rule.py` (`python3 -I`) on two
foreign trees. Nothing was built and no repository was edited.

Labels: **[V]** means I read the code or ran the command. **[I]** means inference.

## 0. Revisions inspected

| What | Where | Revision |
|---|---|---|
| Core (contract) | `.contract` | `15e4ae5` (the pin) |
| Core v2 tree | `git -C .contract show v2-archive:…` | tag `v2-archive` |
| Clean | `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages/Clean`; `/home/devops/Verified-zkEVM/recursion.fast/ext/Clean` is the same commit and `diff -rq` finds no difference | `42fe4b26` |
| riscv-zkvm | `/home/devops/Verified-zkEVM/riscv-zkvm` | `6810fc1`, the commit the contract vendors |
| sig.golf | `/home/devops/Layr-Labs/sig.golf-dev` | `eaa0c7f` |
| ots.golf submissions | `/home/devops/leanEthereum/ots.golf-submissions` | `30cff14` |
| leanerVM | `/home/devops/Verified-zkEVM/leanerVM` | `532ebb4` |
| v0.2 / v0.3 baselines (design workspace, read-only) | `/home/devops/CambridgePQ/recursion.fast/submissions/{baseline,baseline-v03}` | n/a |
| CompPoly BF64 | `…/contract/.lake/packages/CompPoly/CompPoly/Fields/Binary/BF64/` | `572f997` |

---

## 1. Clean (`42fe4b26`)

### 1.1 Status for a v3 entry [V]

- **The v3 pin does not have Clean.**
  - `.contract/lakefile.toml` requires Mathlib, CompPoly, Arklib, VCVio and PolyFun, and nothing
    else.
  - `.contract/scripts/` has no `import-frontend.txt`.
  - `docs/baseline/BASELINE-TASK.md:329` says "the pin dropped Clean, which no v3 target
    requires".
- `AGENTS.md:321-324` and `DESIGN-v3.md` §9.3 still describe Clean as an optional frontend that
  may be imported for circuit proofs, never on the badge path (gate rules 8 and 9). At `15e4ae5`
  this is not possible: the frontend list and the require are absent.
- **So under the current pin, Clean assets have to be copied and re-proved inside the entry's own
  root.** Clean imports `Lean`, which the source rule bans. Any copy must therefore be stripped
  of Clean's tactics, `circuit_norm` simp sets, `elaborate_circuit` and so on.
- Size: 192 `.lean` files and 48,750 lines in `Clean/` (`wc -l`).

### 1.2 The DSL and its soundness and completeness notions [V]

- **Circuits.** `Circuit F α` is a monad that emits `Operations`.
  - Flat operations (`Clean/Circuit/Operations.lean:22-25`): `witness m (WitgenIR)`,
    `assert (e : Expression F)` (meaning `e = 0`, any polynomial degree), `lookup`, `interact`
    (channels).
  - `ConstraintsHoldFlat` (`:54-55`) is the semantics.
  - Core: `Clean/Circuit/*.lean`, 11,640 lines.
- **The field interface** is `class FiniteField (F) extends Field F` (`Clean/Utils/FiniteField.lean:27`).
  - Its fields are `val : F → ℕ`, `fromNat`, `size`, injectivity and `val_fromNat`.
  - The doc comment was written for binary fields (issue #154): "for binary fields it interprets
    the binary digits … `Nat.cast` would be wrong there".
  - The only instance in Clean is `ZMod p` (`F p`).
- **Specifications** (`Clean/Circuit/Formal.lean`):
  - `Soundness F main Assumptions Spec` (`:158`): ∀ offset, env, input, if `Assumptions input` and
    the constraints hold, then `Spec input output`. This is the "constraints ⇒ computation"
    direction.
  - `Completeness F main Assumptions` (`:174`): with the default witness generators
    (`UsesLocalWitnessesCompleteness`), the constraints hold. This is "computation ⇒
    satisfiable", for the honest witness.
  - `FormalCircuit` (`:199`) bundles both. `DeterministicFormalCircuit` (`:212`) adds output
    uniqueness. `FormalAssertion` and `GeneralFormalCircuit[.WithHint]` (`:218-370`) are
    variants.
  - `Clean/Circuit/Foundations.lean` (`original_soundness`, `original_completeness`) proves that
    the "modified" forms imply the plain `ConstraintsHold` forms.
- **Mapping to obligation (a).** "R1CS satisfiable iff computation" is `Soundness` plus
  `Completeness`. With a deterministic spec, `Soundness` already gives "satisfiable ⇒ spec" for
  every witness. That is the shape our BLAKE2s gadget needs.
- **R1CS export.** `Clean/Backends/Circom/R1CS.lean` (226 lines), `processOps`:
  - it flattens `assert` expressions of the form `a·b ± z` into `(A, B, C)` triples;
  - it fails on lookups: `"lookup constraints cannot be represented in R1CS"`;
  - it is generic in `[FiniteField F]`;
  - nothing in it proves that the export preserves semantics.
- **Air layer.** `Clean/Air` (FlatEnsemble, Balance, OrderedChannel, Vm) is AIR with channels.
  - In characteristic 2 it is unusable as is.
  - v2's note `git show v2-archive:docs/upstream/clean-char2-balance.md` proves this over
    GF(2^64): `clean_balance_vacuous`, `clean_balance_K` and `clean_push_requirement_vacuous`.
  - `Air/Vm.lean` even assumes `[Fact (ringChar F ≠ 2)]`.

### 1.3 Hash gadgets and their fields [V]

There is **no BLAKE2s** anywhere in Clean: `grep -ril blake2` finds only a mention in
`Specs/BLAKE3.lean`. Every hash gadget is prime-field only.

| Family | Files / lines | Field assumption | Technique |
|---|---|---|---|
| BLAKE3 (`Gadgets/BLAKE3/*`, `Specs/BLAKE3.lean`, plus `Xor`, `Addition32`, `Addition8`, `Rotation32`, `ByteDecomposition`, `Types/U32`) | 3,850 lines in all; `Gadgets/BLAKE3` alone is 1,416 (`ApplyRounds` 637, `FinalizeChunk` 284, `BLAKE3G` 142, `Round` 103, …); spec 368 | `[Fact p.Prime] [Fact (p > 2^16 + 2^8)]` | `U32` = 4 byte limbs; XOR by byte **lookup** (`ByteXorTable`); add by byte carry chains; rotation by byte decomposition |
| SHA-256 (`Gadgets/SHA256/*`, `Specs/SHA256.lean`) | 3,918 | `[Fact (p > 2^33)]` for `Add32`, `SHA256Compress`; `[Fact (p > 2)]` or none for bitwise | **bit-level R1CS, no lookups** (`BitwiseOps.lean:20`): words as `fields 32` bits; `Xor32`: `z = a + b − 2ab`; `Add32`: `Σa_i2^i + Σb_i2^i = Σz_i2^i + 2^32·cout` (needs `p > 2^33`) |
| Keccak (`Gadgets/Keccak/*`, `Specs/Keccak256.lean`, `Rotation64`, `U64`, `Xor64`) | 1,873 | `p > 2^16 + 2^8` | byte limbs and lookups |
| Poseidon (`Circomlib/Poseidon.lean`, `Specs/Poseidon*.lean`) | 502 + 2,254 | BN254 prime | prime-field S-box |
| Circomlib port (`BinSum`, `Bitify`, `Comparators`, `Gates`, `Mux*`, …) | 8,034 with backends | prime | circomlib templates |

Gadgets that are already generic in `[FiniteField F]`:

- `Gadgets/Boolean.lean:35` `iff_mul_sub_one`: `x(x−1) = 0 ↔ x ∈ {0,1}`, valid in any field;
- `Gadgets/IsZero.lean`, `Equality.lean`, `Conditional.lean`.

The bit gadgets (`Gadgets/Bits.lean`, `Utils/Bits.lean`) are prime-only.

### 1.4 Characteristic 2 [V]

- **Inside Clean:** no instance. The `FiniteField` class allows one.
- **v2's bridge** (`git show v2-archive:legacy/v2/RecursionFast/Clean/*`, about 2,670 lines):
  - `FiniteField.lean` (47 lines): `K.instFiniteField`, with `val a = a.bits.toNat` and
    `fromNat n = ⟨BitVec.ofNat 64 n⟩`.
  - `Gadget.lean` (410): Clean `Expression` to a sum-of-products row gadget.
  - `ToLayout.lean` (467) and `Semantics.lean` (1,094): an ℕ-counted channel balance replacing
    Clean's field sum, and `toLayout_rel_iff`.
  - `Examples.lean` (653): a Fibonacci over `K`, with positive and negative controls and the
    char-2 counterexamples.
  - All of it was written against v2's `K`, which v3 deleted. It is a template, not something to
    import.
- **leanerVM:**
  - `LeanerVM/Parameters/CleanField.lean:36` (49 lines): `instFiniteFieldK : FiniteField K` with
    **`K = CompPoly BF64`**, at the same Clean pin.
  - `LeanerVM/Arithmetization/Tables/Blake2s.lean` (359) is a Clean component for a BLAKE2s
    *table row*. It does **not** prove the compression: `Blake2sRelation` is an `Assumptions`
    field, discharged by Flock.
  - `LeanerVM/Semantics/Blake2s.lean` (187) is a `UInt32` BLAKE2s compress spec with BF64 packing
    (`lowWord`, `highWord`, `ofWords`, `CompressCells`).
  - No arithmetised BLAKE2s compression exists anywhere locally.

### 1.5 What could be transcribed into an R1CS-over-BF64 BLAKE2s proof [I, grounded in §1.3]

- **The spec layer: little.**
  - The relation and the oracle are the contract's `RecursionFast.Contract.Hash.Blake2s`: `mix`,
    `round`, `initialState`, `compress`, `compressInput`, `blake2s256`.
  - The R1CS must be proved against those definitions. Clean's `Specs/BLAKE3.lean` `g` has the
    same G as BLAKE2s (rotations 16, 12, 8, 7), but BLAKE3 has a different schedule (fixed
    permutation, 7 rounds), IV handling and finalisation.
  - What does carry over is the proof pattern of `BLAKE3G.soundness`: the state-vector `set`
    chains, `repeat' split` on index coincidences, `simp_all` to chain sub-specs.
- **The gadget layer: almost nothing** for addition.
  - Over GF(2^64), XOR of bit vectors is field addition: linear, **0 constraints**. On packed
    polynomial-basis words it is also plain addition (`BF64.add_def` is `xor`).
  - Rotation of a bit vector is rewiring, also 0 constraints.
  - Clean's prime-field XOR (`a+b−2ab`, or byte lookups) is irrelevant here.
  - **Addition mod 2^32 is the only real gadget.** Clean's `Add32` relies on integer packing with
    `p > 2^33`, which is impossible in char 2.
  - Over BF64 it must be a ripple-carry chain: `s_i = a_i + b_i + c_i` (linear), and
    `c_{i+1} = a_ib_i + c_i(a_i + b_i)`. That is 2 product constraints per bit, plus booleanity
    `z² + z = 0`.
  - Per BLAKE2s compression: 10 rounds × 8 G × 6 32-bit additions = 480 additions, so about
    480·32·2 ≈ 31k product constraints plus about 15k booleanity constraints.
  - This proof is new: an induction over the 32 bits against `UInt32.add`/`BitVec` addition.
  - Clean's `SHA256/Add32.lean` (411 lines) and `Xor32.lean` (173) show the *proof organisation*
    (`valueBits`, `Normalized`, `sum_bool_lt_two_pow`, `bitsVal_eval`), not the content.
- **The framework layer: reusable by copying the definitions.**
  - The `Soundness`/`Completeness` shapes (§1.2) are the right obligations.
  - Re-implementing a minimal R1CS DSL (linear forms, `A z ∘ B z = C z`, witness generator,
    sound/complete lemmas) inside the entry is a few hundred lines. v2's `Gadget.lean` with its
    `Lin`, `SOP`, `holds_gadgetOf` is the closest local template. [I]
  - Copying Clean's 11.6k-line core is not worth it: it is tactic-heavy, with `circuit_norm`,
    `elaborate_circuit` and simprocs, and needs `import Lean`, which the source rule bans.
- **FemtoCairo** (`Clean/Examples/FemtoCairo/*`, 1,870 lines):
  - a small VM in circuit: decode, memory read by lookup table, `nextState`, with
    `femtoCairoStepSoundness` and `femtoCairoTableStatement` over an `InductiveTable`;
  - prime field with `p > 512`, and memory and program by lookups;
  - not reusable for R1CS over BF64. It is useful only as a model of "VM step soundness by
    induction over a trace table".

---

## 2. RISC-V proof tooling for `ImageComputes`

### 2.1 The obligation [V]

`Contract/Extractor.lean:105`:

```lean
def ImageComputes (img : Image) (E : Digest → Proof → Log → Option Wit) (fuel : ℕ → ℕ) : Prop :=
  ∀ c (π : Proof) (L : Log), π.size ≤ proofCap → (extractorInput c π L).length ≤ 2 ^ 60 →
    ∃ o, run img (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap ∧ decodeWit o = E c π L
```

- The machine (`Contract/Machine.lean`, 209 lines):
  - RV64IM plus the W-ops (`wordResult`) plus Zbc (`clResult`, `clmul`);
  - Harvard code at `CODE_BASE = 0x1000`, decoded from raw words (`decodeInstruction`);
  - data at 0, the read-only tape at `TAPE_BASE = 2^63`;
  - `ordinaryStep` checks only alignment and "store below the tape";
  - `execute` is fuel-indexed, and `HALT` is `t0 = 0` with output `readWords a0 a1`.
- It is sig.golf's machine with the oracle, the counters and the harts removed. The names are
  the same: `Image`, `WordOp`, `Instruction`, `decodeInstruction`, `ordinaryStep`, `fetch`.
- **For every log.** `final` in `Contract/Security.lean` asks `E` to work on every good log, of
  any length.
  - So the image must index logs of up to 2^60 words within `2^40 + 2^8·t`.
  - A linear scan per lookup is not enough: 2^15 digest lookups × t words exceeds `2^8·t` once
    t is above about 2^22.
  - The image needs a sort or radix pass (for example LSD radix on the 4-word answers, about 32
    byte passes, well inside the ≥ 6 words × 2^8 steps an entry brings) or a hash table with
    proved worst-case behaviour. [I] This is a proof cost to budget.
- **Output leniency.** `decodeWit` lets the image output a node's child proofs in place. The
  child proofs must be rebuilt from Merkle leaves found in the log, then written out.

### 2.2 What the core ships today [V]

| Module | Lines | Content |
|---|---|---|
| `RecursionFast/Library/Machine.lean` | 120 | simp lemmas `getReg_setReg`, `getReg_initState`, `pc_initState`, `getMem_initState(_tape)`; `execute_step`, `execute_halt`, `execute_mono`, `run_mono`, `run_none_of_le`, `fetch_eq`, `ordinaryStep_ld`, `ordinaryStep_sd`, `readWords_eq`, `length_readWords`. One instruction at a time, no loop rule, no block abstraction. |
| `RecursionFast/Library/Words.lean` | 212 | the tape and output codecs: `wordByte_packBytes`, `packBytes_wordsBytes`, `digestAt_packBytes`, `bytesAt_packBytes`, `getD_append_mid`, `decodeWit_cons`, `decodeWit_witWords`, … |
| `RecursionFast/Library/WitnessSending.lean` | 267 | the 8-instruction image (`tests/asm/proofwords.S`); `run_img` proves it by 8 explicit `execute_step` rewrites (lines 189-229), then `computes` and `certificate` |

This is enough for straight-line code of a few dozen instructions. It does not scale to loops.

### 2.3 riscv-zkvm `Rv64.Logic` (local, not vendored) [V]

- **Content.** `RiscvZkvm/Rv64/Logic/**`, 20,153 lines:
  - separation logic (`SepLogic.lean`, 3,201 lines);
  - `cpsTripleWithin n entry exit cr P Q` and `cpsBranchWithin` (`CPSSpec.lean:49`, 1,336
    lines);
  - a WP framework (`WP/{Core,CFG,Loop,Call,GeneratedCFG}.lean`), including a bounded loop rule:
    `WP/Loop.lean` `loopNatCert`, `loopNatCert_sound`, `loopBound`;
  - tactics `runBlock` (1,534 lines), `seqFrame` (1,109), `xperm`, `xcancel` and the `wp_rv64_*`
    family (1,982).
- **It is stated over the wrong machine.** Everything is about riscv-zkvm's own `step`/`stepN`.
  - That machine fetches from `MachineState.code : Word → Option Instr` (an AST, not raw words).
  - Its memory zones: `isValidDwordAccess` requires `isValidMemAddr`, with valid zones
    `[0x20, 0x78000000]`, input and RAM (`Word.lean`).
  - **Tape addresses ≥ 2^63 trap there.** There are no W-ops (only `ADDIW`) and no Zbc.
  - So no simulation `contract execute ↔ stepN` exists for tape-reading code. Using the Logic
    layer would mean re-instantiating it on the contract machine. [I]
- **It is not on the allowlist.** It is not vendored (`.contract/RecursionFast/Vendor/RiscvZkvm`
  holds only `Rv64/{Basic,Execution,Word,Instructions,ZiskAccel}` and
  `Interpreter/Decode`).
  - Copying it into an entry means copying tactic files that use `syntax`/`macro`/`elab`, which
    the source rule bans.
- **It scales badly.** R6 measured `runBlock` at 161 s for a 128-instruction block, against 4.3 s
  for 32 (`docs/research/notes/R6-riscv.md` §2.1).
- **Verdict [I]:** usable only as a pattern. `loopNatCert`'s shape is a reasonable loop rule to
  restate over the contract machine.

### 2.4 sig.golf: "custom verified symbolic executor certified by `Eq.refl`" [V]

- **Location.** `/home/devops/Layr-Labs/sig.golf-dev/submission/SigGolfCandidate/Rv/`, 2,289
  lines. Also copied for the build probe at
  `/home/devops/CambridgePQ/recursion.fast/probes/sig-golf-build/repo/SigGolfCandidate/`.

| File | Lines | Content |
|---|---|---|
| `Steps.lean` | 190 | `Steps image s n cycles s'`, `Steps.execute`, HASH/HALT laws (imports `SigGolfCandidate.Legacy`, its copy of the old contract) |
| `Expr.lean` | 404 | the symbolic word language `E` (`E.reg r`, `E.ld a`), constant folding, `base + const` address normalisation |
| `Micro.lean` | 183 | `Micro` (alu, load, store, branch, jal, jalr); `classify_sound`: `ordinaryStep` agrees with `Micro.exec` |
| `Exec.lean` | 332 | `symRun cfg code pc fuel : Option Result` over **raw words**, straight-line to ECALL or branch; records `Oblig` (aliasing, alignment) |
| `Sound.lean` | 599 | `symRun_sound` (`:558`): `symRun … = some r → CodeAt image pc code → s.pc = pc → r.obligs s → Steps image s r.steps r.cycles (r.toState s)`; `symRun_ecall` |
| `Hash.lean` | 143 | HASH syscall laws (no counterpart in v3) |
| `Tactic.lean` | 170 | `sym_eval`, `sym_block`, `kernel_theorem`: evaluate `symRun` with compiled code (`@[implemented_by evalOptResultUnsafe]`), turn the result into a literal with DAG sharing, close by kernel `Eq.refl` |
| `Api.lean` | 263 | `BlockSpec`, `BlockSpec.of_symRun`, `Steps.iterate` (`:64`, the loop-invariant rule for loops whose body is one block) |
| `SimpAttr.lean` | 5 | `register_simp_attr` |

- **Can it be reused? Partly.** I ran `python3 -I .contract/scripts/source-rule.py` on that
  directory: **27 findings in 4 files**.
  - `Tactic.lean`: `open Lean`, `unsafe`, `implemented_by`, `elab`, `…Unsafe` names.
  - `Api.lean:230-256`: `open Lean`, `simproc`, `macro`.
  - `SimpAttr.lean`: `import Lean`, `register_simp_attr`.
  - `Expr.lean:17`: `deriving instance Lean.ToExpr`, raw scan.
- Gate rules 2 and 3 also reject `opaque` and `implemented_by`. So **the reflection tactic cannot
  ship in an entry.**
- **The pure core is portable:** `Steps`, `Expr`, `Micro`, `Exec`, `Sound` and most of `Api`,
  about 1,700 lines. The machine is the ancestor of ours. Changes needed [I]:
  - drop cycles and HASH;
  - replace sig.golf's `accessValid` by the contract's alignment and "store below `TAPE_BASE`"
    check;
  - add a `Micro` case for `.cl` (Zbc);
  - keep the W-ops (already there);
  - drop `ToExpr`.
- **Replacing `sym_eval` within the rules [I]:**
  - generate the literal `Result` offline, with a Python mirror of `symRun`, or a Lean script kept
    **outside** the entry root (the source rule scans every `.lean` file under the root, and
    `#eval` is banned);
  - paste it into a generated file;
  - close `symRun cfg code pc fuel = some <literal>` by `decide +kernel` (needs `DecidableEq
    Result`) or `rfl`. `decide +kernel` is allowed: no rule bans it, and the core's controls use
    it.
  - sig.golf's own figure: blocks of up to 441 steps (`sym_block blk718 … 441`).
- **Scale reference** (`docs/research/notes/R2-sig-golf.md` §3.4):
  - RISC-V refinement proofs total about 33k lines for four programs;
  - verify (145,952 words, half NOP padding) took 9.5k lines, mostly `decide +kernel` checkers
    over unrolled code;
  - the loop composition is `Verify/Judg.lean` `Good` plus induction.

### 2.5 ots.golf [V]

- **Location and approach.** `/home/devops/leanEthereum/ots.golf-submissions/formal/Submissions/UpperRiscv/`
  uses hand-written block lemmas over riscv-zkvm `step` on a `List Instr` AST:
  - `Refines.lean` (115 lines): `Refines fuel s q c`, composition rules
    `.steps/.linear/.hash/.halt/.branch`;
  - `BlockExecution.lean` (180): `LinearReady`, `linear_steps` over `foldl execInstrBr`;
  - `MachineFacts.lean` (147).
- **Not portable as code.** It targets a different machine: an AST image, riscv-zkvm `step` and
  its zones.
- **Not admissible as is.** The source rule finds 7 findings in 100 files, for example
  `Count.lean:8 partial` and `Deterministic.lean:48 attribute init`.

### 2.6 The closest precedent: the v0.2/v0.3 RISC-V baselines (design workspace) [V]

- **What they are.** `/home/devops/CambridgePQ/recursion.fast/submissions/baseline` (v0.2) and
  `baseline-v03` (v0.3) proved an **84-instruction RISC-V R1CS checker over GF(2^64)**.
  - It loops over rows and sparse entries, with `ld`, `addi`, `slli`, `xor`, `clmul`, `clmulh`,
    `beq`, `bne`, `ecall`.
  - The machine was the same one (contract `execute`), plus counters and QUERY.
  - Exact step and counter bounds were proved, and the harness printed **HARNESS: ACCEPT** with
    Lean kernel plus nanoda (v0.3 RESULT §0, §5).
- **Sizes.**
  - v0.2: 1,481 code lines in all.
  - v0.3: 1,920 code lines; 2,663 total lines in `RecursionFastCandidate/*.lean`.
- **The source rule is clean on it:** I ran it on `baseline-v03/RecursionFastCandidate`, with
  0 findings in 12 files.
- **Tooling** (`Rv/L0.lean`, 253 lines in v0.2, 475 in v0.3):
  - `Reach img os s n d s'`: n steps from `s` reach `s'` for every fuel ≥ n;
  - `Reach.trans`, `Reach.cast`, `Reach.trans_ex`;
  - `CodeAt img j i`, proved by `rfl` in the generated `Code.lean`;
  - `pcOf`, `pcOf_add/sub`;
  - one lemma per instruction form with **symbolic** immediates: `Reach.addi/slli/xor/ld/cl/beq/bne`.
- **Loops.** `Seg.lean`, `Row.lean`, `Run.lean` (`body_step`, `loop_run`, `head_step`,
  `red_step`, `seg_run`, `row_run`, `rows_run`, `prologue`, `run_rows`), by induction.
- **Field arithmetic.** `Arith.lean` has `clmul_xor_left`, `reduce_xor`, and
  `red_halves : red lo hi = K.reduce T` (clmul/clmulh by `0x1B` reduction), `red_acc` and
  `red_mul`.
  - v3 uses CompPoly `BF64` (`BF64.mul = ofBitVec (reduce (carryLessMul a b))`,
    `Reduce.lean:116` `reductionConstant = 0x1B`, `:167` `reduce`).
  - So porting needs one bridge lemma: contract `clmul` = CompPoly `carryLessMul`.
- **The structural-refinement trick.** v0.2's spec verifier `walkRows` "follows the end words
  exactly like the machine (so the refinement is structural)" (v0.2 RESULT §2).
  - For v3: **define `E` as a Lean function that mirrors the image's loops one to one**, so that
    `ImageComputes` is a mechanical refinement.
  - Then prove the semantic facts (Merkle path recovery, decoding) about that Lean `E` inside the
    KS proof, not at machine level. [I]
- **Porting to v3 [I].**
  - Remove `CostVec`/`Kind`/QUERY from `Reach`, which becomes plain `execute (n+f) s = execute f s'`.
  - Add `sd`/`sb` stores (v0.2 had none), `jal`/`jalr`, and the W-ops if used.
  - Rebase `Arith` on BF64.
  - What remains is per-program loop proofs.

### 2.7 Cost drivers for the SNARK extractor image [I]

Rough order of proof difficulty:

1. **Parse.**
   - Straight-line loops over packed bytes.
   - `Library/Words.lean` already has the codec lemmas.
   - Note that `E` is a free specification, and `decodeWit` is lenient.
2. **Log indexing by answer, for every log** (§2.1).
   - Needs a sort (radix or merge) with a permutation and stability proof, plus binary search.
   - It is the largest new loop proof. sig.golf and the v0.2 baseline have no precedent for it.
3. **Merkle-path rebuild.** Lookups plus copying query bytes. These are loops over digests,
   using the comparison and copy blocks.
4. **Reed–Solomon decoding.**
   - Only needed if the witness is committed in encoded form and the extractor must decode
     within unique-decoding radius. Berlekamp–Welch or Gao over BF64 means linear algebra or
     polynomial division with `clmul` arithmetic.
   - This is the most expensive at machine level.
   - **Design lever:** commit to the witness systematically (or the witness itself under a
     Merkle tree), so that `E` only reads leaves and decoding happens in the Lean KS argument,
     if the protocol permits. Otherwise state `E` as a Lean decoder that the image mirrors
     structurally (§2.6).
5. **Budget arithmetic** (`2^40 + 2^8·t`). The proof composes step counts with `Reach.trans`. The
   counts are symbolic in `t`, so the proof must be generic in the input size (the R2 lesson:
   sig.golf's per-concrete-block `decide +kernel` does not carry over).

---

## 3. The core's harness at the pin (`15e4ae5`) [V]

| Tool | Lines | What it checks | Usable on an entry now? |
|---|---|---|---|
| `scripts/source-rule.py` | 334 | Two nets, a Lean-faithful lexer and a raw word scan (comments and strings included), over every `.lean` under DIR. Rejects elaboration-time code (`#eval` and every `#`-command except `#check/#print/#reduce/#guard_msgs`; `run_*`, `elab`, `macro`, `syntax`, simprocs, `declare_…`), load-time code (`initialize`, `register_…`, `builtin_…`), `unsafe…`/`partial`, the attributes `implemented_by/extern/cpass/computed_field/csimp` (and `tactic/init/export` after `[`), compiler/debug `set_option`s, and `import`/`open Lean…/Lake…/Qq…`. | **Yes**: `python3 -I .contract/scripts/source-rule.py submissions/<root>` |
| `scripts/Gate.lean` (`lake exe gate`) | 614 | Environment-level, on `.olean`s; trust by content hash against a manifest. Rules: (1) axioms ⊆ {propext, Choice, Quot.sound}, no `sorryAx`/`ofReduceBool`/`ofReduceNat`/`trustCompiler`; (2) no `unsafe/partial/opaque` in untrusted code; (3) no code-substituting attributes; (4) `--computable`: badge-path fields have compiled code; (5) organiser oleans match the manifest; (6) imports only from `--allowed-imports` (+ frontend); (7) untrusted definitions do not reference compiler or environment internals; (8, 9) the badge root module does not reach Clean or the compiler. **The header still names v2's `badgeFields`** (`Protocol`, `ExtractorImage`, …); its v3 reinterpretation is S3's. | Partly: needs a manifest generated by `olean-manifest.py gen` on a clean organiser build, and an allowlist (`scripts/import-allowlist.txt` is **absent at the pin**; v2's copy is `docs/core/import-allowlist.txt`) |
| `scripts/AxiomAudit.lean` (`lake exe axiomaudit`) | 64 | Imports `RecursionFast.{Contract,Library,Controls}` (hard-coded) and checks every `RecursionFast.*` constant's axiom closure. | Organiser only. For an entry, use `#print axioms` in a `#guard_msgs` block (allowed) or the gate's rule 1. |
| `scripts/check-hygiene.sh` | 21 | Text lint of the core's own `RecursionFast/` (not vendored): `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `csimp`, `axiom`, local `maxRecDepth`/`maxHeartbeats` ("comparator replay ignores them", A3-M3). | Core only; v2's entry copy is `docs/baseline/v2-example/scripts/check-hygiene.sh` |
| `scripts/ci.sh` | 40 | The core's CI: vendor, hygiene, source-rule fixtures, build, axiom audit, trusted line budget ≤ 500. | Core only |
| `scripts/loc.py` | 34 | Line counter (total, blank, comment, code, theorem lines). Used for RESULT line counts. | Yes |
| `scripts/olean-manifest.py` | 160 | `gen`/`check` sha256 manifest of trusted and pinned `.olean`s (core, packages in the allowlist closure, project `RecursionFast.Contract*` and `RiscvZkvm*`). Its `PINNED_PKGS` still lists `Clean`. | Yes, after a clean organiser build |
| `scripts/bwrap-landrun.sh` | 46 | A landrun-compatible bubblewrap sandbox. `/usr/bin/bwrap` is present. | Yes, as the comparator's `landrun` |
| `scripts/check-vendor.sh` | 31 | The vendored Rv64 is byte-identical to riscv-zkvm `6810fc1`. | Core only |

**Absent at the pin.** The harness driver, the renderer, the challenge stubs, the organiser
build, `tools.env`, the manifest and the allowlist are absent. They are at `v2-archive` only:
`scripts/harness.sh` (294 lines), `scripts/org-build.sh`, `scripts/render-challenge.py`,
`RecursionFast/Challenge/*.lean.in`, `scripts/tools.env`, `scripts/olean-manifest.sha256` and
`scripts/import-allowlist.txt`. v2's `harness.sh` runs these stages:

- (0) manifest check;
- (1) **comparator first** in a fresh tree, with the organiser package required by path and
  read-only, Lean kernel plus nanoda, and an artifact hash record;
- (2) the gate in a second fresh tree at the same path, with a byte-identical build binding;
- (3) the badge build and benchmark.

The source rule runs in each fresh tree before the build.

**Running an entry today** (BASELINE-TASK §1 note):

- source rule;
- build the `.contract` organiser package (it is not built yet: `.contract/.lake` holds only
  `config/` and the `packages` symlink);
- `olean-manifest.py gen` on that clean build;
- a hand-written challenge file from the claim, then the comparator;
- `lake exe gate <Solution module> <certified thm> --manifest … --allowed-imports …`.

**Tools installed** [V]:

- **Comparator:** `/home/devops/CambridgePQ/recursion.fast/contract/tools/comparator`, at
  `d03acab` (the `tools.env` pin), built.
  - `.lake/build/bin/comparator`; lean4export at
    `.lake/packages/lean4export/.lake/build/bin/lean4export`; toolchain `v4.34.1`.
  - `COMPARATOR_HOME` is **not set** in the environment. v2's `tools.env` defaults to that path.
- **nanoda:** `/home/devops/CambridgePQ/recursion.fast/contract-v03/tools/ext/nanoda_lib/target/release/nanoda_bin`,
  at `3a24072` (the pin), built.
  - Set `COMPARATOR_NANODA` to it.
  - Warning from v0.3 RESULT §5: nanoda was OOM-killed at 60 GB on a declaration that diverged
    (`row_run`). Give it a `ulimit -v` and a `timeout`.
- **RISC-V assembler:** `/usr/bin/riscv64-unknown-elf-as`, GNU as 2.45.50, with gcc 14.2.0.
  `-march=rv64im_zbc` assembles.
- **Sandbox:** `/usr/bin/bwrap` is present. landrun is absent; the shim covers it.

**Caps** (`AGENTS.md` §, caps table): `lake build` of the submission ≤ 1 h and ≤ 48 GB; harness
(comparator + nanoda + gate + audit) ≤ 2 h.

**Rules that matter for the tooling choice:**

- `decide +kernel` and `rfl` are allowed.
- `native_decide`, `bv_decide` (it uses `ofReduceBool`), reflection via `implemented_by`, custom
  simprocs and macros are not.
- Declaration-local `maxHeartbeats` and `maxRecDepth` do not affect comparator replay.

---

## 4. A Lean → RISC-V path [V: none exists locally]

- **What is absent.** No verified compiler, codegen or Lean-to-RV64 translator exists in any local
  tree (`grep` over riscv-zkvm, leanerVM, sig.golf, ots.golf, the design workspace and these
  docs).
  - riscv-zkvm has a decoder (`Interpreter/Decode.lean`) but no encoder: no `encode`, no
    `decode_encode`.
  - Its `Rv64/Program.lean` (138 lines) is `abbrev Program := List Instr` with append lemmas, an
    evm-asm style macro assembler at the AST level only.
- **Where the idea appears.** Only in planning:
  - `docs/research/reviews/A3-feasibility.md:521`, S7: "A verifier IR/DSL with a verified
    compiler to RV64IM … compiler 5–15k lines … later, optional";
  - `DESIGN-v3.md` §6.5: O-18 and O-12 need "a Lean-to-RISC-V build of the badge executables" for
    a different purpose, which is timing `Vb`.
- **Cheaper alternatives [I]:**
  1. **Structural refinement, no compiler** (§2.6). Write `E` in Lean as the image's loops,
     using the same words, the same index arithmetic and the same early exits. Each loop then
     needs one invariant lemma that is mostly bookkeeping. This is the only route with a
     certified local precedent: 1.5–1.9k lines for an 84-instruction looping program.
  2. **Interpreter in the image.**
     - Prove once that a small RISC-V interpreter for a bytecode (registers, BF64 ops via
       `clmul`, digest compare, memory copy, bounded loops) computes `Interp.run bc tape`.
     - Ship the extractor logic as **data** (the bytecode in `img.data`).
     - `ImageComputes` then reduces to Lean-level facts about `Interp.run bc`, plus a step bound
       of (interpreter overhead per bytecode step) × (bytecode steps).
     - Cost: the interpreter proof (its dispatch loop and one case per opcode), and a constant
       factor of overhead against `2^8` steps per word. A 10–30× interpretive overhead may
       still fit `2^40 + 2^8·t` if the bytecode does O(1) work per input word.
     - It helps most if the extractor is large or changes often.
  3. **Python-generated literals plus `decide +kernel`.** Port sig.golf's `symRun`/`symRun_sound`
     (§2.4) for straight-line blocks. Loops still need a hand rule, `Steps.iterate`-style.

---

## 5. Summary for budgeting

| Obligation | Reusable assets | New work [I] |
|---|---|---|
| (a) BLAKE2s compression R1CS, both directions | contract spec `Contract/Hash/Blake2s.lean` (`mix`, `round`, `compress`); proof patterns from Clean `BLAKE3G` and `SHA256/{Xor32,Add32}`; minimal R1CS-DSL template from v2's `Clean/Gadget.lean` (`Lin`, `SOP`, `holds_gadgetOf`); Clean's `Soundness`/`Completeness` shapes; `iff_mul_sub_one` (booleanity, any field) | char-2 ripple-carry adder gadget (≈ 2 products/bit) with bit-level proof against `UInt32` addition; bit decomposition and packing of BF64 words; composition over 80 G calls; the whole recursive verifier circuit (Merkle path checks = repeated compressions, FS transcript, sumcheck and PCS arithmetic in BF64, natively free) |
| (b) `ImageComputes` | `Library/{Machine,Words}.lean` (single-step, codecs); v0.2/v0.3 `Rv/L0.lean` `Reach` and per-instruction lemmas, loop lemmas in `Seg/Row/Run`, `Arith.red_halves` (clmul reduction); sig.golf `Rv/{Expr,Micro,Exec,Sound,Steps}` (≈ 1.7k lines, pure; tactic not admissible); `WP/Loop.lean` `loopNatCert` as a pattern | port L0 to v3 (drop counters, add stores/jumps); BF64 bridge `clmul = carryLessMul`; log index (sort + search) for every log within `2^8` steps per word; Merkle rebuild loops; RS decoding unless the design avoids it; budget arithmetic generic in `t` |
