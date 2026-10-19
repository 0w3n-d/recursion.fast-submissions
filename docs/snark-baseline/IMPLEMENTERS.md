# Brief for every agent implementing the honest entry (R1, `submissions/spartan-chain/`)

Read this file first, then `BLUEPRINT-R1.md`, which is normative. Background is in `PLAN.md` (the
decisions) and in `notes/` (F1, E1–E4, ADV1).

## Where things are

- **Entry root:** `/home/devops/Verified-zkEVM/recursion.fast-submissions/submissions/spartan-chain/`.
  - It is flat: no subdirectories.
  - Each Lean module is one file named `SpartanChain<Name>.lean` (the blueprint's
    `Soundness/KS.lean` becomes `SpartanChainSoundnessKS.lean`). Use `namespace SpartanChain`
    inside.
  - The umbrella file `SpartanChain.lean` imports every module. When you add a module, add one
    import line to it.
  - The Rust prover goes in the same root, flat: `Cargo.toml` with `[[bin]] path = "main.rs"`
    and its modules beside it.
- **Shared Lean development clone:** `/home/devops/Verified-zkEVM/rf-core-sc`.
  - It is the core on the amended-contract branch `v3/ks-potential`.
  - Its `.lake/packages` is a symbolic link to the shared, prebuilt, **read-only** package tree.
    Never run `lake update` or `lake exe cache get`.
  - The entry is reached through the symbolic link `SpartanChainRoot`.
  - Build one module and its dependencies with `cd /home/devops/Verified-zkEVM/rf-core-sc &&
    timeout 3600 lake build +SpartanChainMLE` (substitute your module name).
  - After you **add a new module file**, run `./refresh-roots.sh` in that clone. It lists every
    `SpartanChain*.lean` as a lake root; without it lake reports "unknown module".
  - Other agents build other modules in the same clone at the same time. If you see a lake lock
    or "file busy" error, wait and retry rather than deleting anything.
  - For quick checks, run `timeout 900 lake env lean SpartanChainRoot/<File>.lean`.
  - For `#eval` or `#print axioms` experiments, use scratch files **outside** the entry root,
    e.g. `/home/devops/Verified-zkEVM/rf-core-sc/scratch/`.
- **Logs and measurements:** under
  `/home/devops/Verified-zkEVM/recursion.fast-submissions/logs/spartan-chain/<your-topic>/`.

## Hard rules

These are checked by `python3 -I /home/devops/Verified-zkEVM/recursion.fast-submissions/.contract/scripts/source-rule.py <root>`.
Run it on the root before you finish.

- Axioms: only `propext`, `Classical.choice` and `Quot.sound`. No `sorry` in finished work,
  and no `native_decide`.
- None of these attributes: `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`. No `unsafe`, `partial` or `opaque`.
- Inside the root, no elaboration-time code at all, **including in comments and docstrings**:
  no `#eval`, `#guard`, `run_cmd`, `elab`, `macro`, `syntax`, `initialize`, or `import Lean`.
  `#check`, `#print`, `#reduce` and `#guard_msgs` are allowed.
- Imports: Mathlib, `RecursionFast.Contract.*`, `RecursionFast.Library.*`, CompPoly's
  `BF64`/`Ext3` closure, and the entry's own modules. Nothing from ArkLib, VCVio, Clean or
  leanerVM: **copy** what you need, with a provenance comment line naming the source repository,
  path and commit.
- `V`, `P`, `E` and everything they call must be computable, compiled code. Never write a large
  closed term (a table or a literal) at module level: compiled executables evaluate them at
  start-up.
- Computable definitions should be efficient in compiled code. Use `Array` or `ByteArray` with
  indices; don't build `List`s of millions of elements, and don't use `Fin n → α` closures as data
  (the contract switched `Digest` to `Vector` for exactly this reason).
- Statements are non-vacuous: give every definition the certificate relies on a positive and a
  negative control (blueprint §10.1). A proof never changes the statement it proves. If a
  blueprint statement is false or unprovable as written, **stop and report** with a
  counterexample; don't weaken it silently.
- Don't commit. The orchestrator commits.
- **Build budget.** The machine is shared by about ten agents and has 62 GB. Each module should
  check in under about 2 minutes and under about 4 GB. Run probes under
  `systemd-run --user --scope -p MemoryMax=8G timeout 900 …`. A module that needs more is a
  build-time defect, and build time is a stated priority of this work. Never let the kernel or
  `decide` evaluate the `2^14`-row block or BLAKE2s on concrete data; reason about the generic
  definitions instead.
- Give every Lean or cargo command a `timeout`. If a build runs much longer than expected,
  inspect it with `ps` (locks, a package being rebuilt from scratch) rather than waiting.

## Skills

Use `lean4:lean4` for all Lean work. Use `lean-spec-authoring` when writing definitions or
statements.

## Finishing

Leave the module building with no `sorry`. If a lemma is genuinely unfinished, leave it as a
clearly listed `sorry` and say so. Then write a short report,
`docs/snark-baseline/reports/<topic>.md`, containing:

- what was built, with module names and the theorem names of the blueprint lemmas (L-…);
- what is proved;
- what remains open;
- the code line counts from `python3 /home/devops/Verified-zkEVM/recursion.fast-submissions/.contract/scripts/loc.py`;
- every deviation from the blueprint, with its reason.
