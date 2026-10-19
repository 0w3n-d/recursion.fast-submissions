# Report: the submission assembly and the entry's check infrastructure

There are two parts:

1. `SpartanChainSubmission.lean`, the submission and its certificate, parametrised so that the
   final instantiation is one line;
2. the entry's checks: claim, challenge stub, solution generator, `check.sh`, `smoke.py` and a
   compiled Lean runner.

Nothing is committed in the submissions repository. Logs are under `logs/spartan-chain/infra/`.

## 1. `SpartanChainSubmission.lean` (§1.4; §10 `Submission.lean`)

The module imports `SpartanChainVerifierTop` and `SpartanChainOracle`, and is in the umbrella
`SpartanChain.lean`.

**Parameters.**

- `LV : LeafVerifier` (`SpartanChainVerifierTop`): `size` is `leafSize`, `prog s n h π_S` is the
  SNARK verifier.
- `proveLeaf : Digest → ℕ → Digest → OProg ByteArray`: the SNARK prover. It is called as
  `proveLeaf s n h` with `h = chainEnd s n`, for `n ≥ 1` (§1.4).
- `Facts LV proveLeaf : Prop`, the facts the other agents prove:
  - `size_zero : LV.size 0 = 80`;
  - `leaf_complete`: for every `H` and every `1 ≤ n ≤ chainCap`, the honest SNARK has
    `leafSize n − 80` bytes and `LV.prog … .run H = true`;
  - `ks : Nonempty (KState (Rel (vb LV)) (V LV) WitnessSending.E εR1)`, the **amended** `KState`,
    with `ε` a structure parameter;
  - `queries`: L-Q1 for `LV.prog`, at most `2^14` queries.

**Definitions.**

- `leafBytes s n h π_S := encodeF (.leaf s n) ++ h ++ π_S`.
- `P`:
  - for a leaf with `n = 0`: `ret (leafBytes s 0 s ∅)`;
  - for a leaf with `n ≥ 1`: `proveLeaf s n h >>= ret ∘ leafBytes s n h`, with
    `h = chainEnd s n`;
  - for a node: `ret (encodeF node)`.
- `εR1 := 2^-129` and `qVR1 := 2^14`.
- `submission LV proveLeaf` takes `V := V LV`, `P`, `E`, `img`, `fuel` (the library's, as in the
  S2a baseline), `ε := εR1` and `qV := qVR1`. It is `noncomputable` because `ε` is a real number.
  `V`, `P`, `E` and `img` themselves compile.

**Proved** (no `sorry`):

- `leafBytes_parse`: the honest leaf proof parses back to `(0, n, s, h, π_S)`.
  `leafBytes_size` gives its size, `80 + |π_S|`.
- `Vb_eq : (submission …).Vb = vb LV`.
- `fits_of_rel`.
- `complete (F)`: perfect completeness for every oracle.
  - Node: node completeness (`check_encode_node`).
  - Zero-step leaf: the header.
  - `n ≥ 1`: `leafBytes_parse` and `F.leaf_complete`.
- `V_queries (F)`: at most `2^14` queries on every input. Off the leaf branch there are none; on
  it, only the SNARK's.
- `certificate (F) : Certificate (submission …)`:
  - `secure`: `⟨F.ks, V_queries⟩` after `Vb_eq`;
  - `computes`: `WitnessSending.computes`;
  - `cap`: `εR1 ≤ errorCap`, `2^14 ≤ 2^16`, fuel 8, image 32 bytes.
- `certificateR_of (F) D …`: `CertificateR` against any claim whose numbers are at least the
  submission's.
- `εR1_le_declared`: `2^-129 ≤ 1/2^128`, exactly as the renderer writes it.
- **Controls.**
  - `certificateR_claim (F)` (positive): `claimR1` is a literal of `claim.json`.
  - `claim_negatives` (negative, needing no fact): no certificate with one image bit flipped,
    with fuel 7, or with `qV = 2^14 − 1`.

**The final instantiation** (`SpartanChainFinal.lean`, when the parts land). It must provide:

```lean
def leafVerifier : LeafVerifier := …        -- Verifier.lean
def proveLeafR1 : Digest → ℕ → Digest → OProg ByteArray := …   -- Prover.lean
theorem facts : Facts leafVerifier proveLeafR1 := ⟨…, …, …, …⟩
```

Then `make-solution.py` writes:

- `submission := SpartanChain.submission leafVerifier proveLeafR1`;
- `certified := certificateR_of _ _ facts declared rfl εR1_le_declared (2^14 ≤ 16384) (affine fuel)`.

## 2. Check infrastructure

- **Organiser side.**
  - It is on the scratch branch **`v3/ks-interim-harness`** of `/home/devops/Verified-zkEVM/rf-core-s2a`,
    based on rf-core-ks `v3/ks-potential` `05fde28`. The branch has three local commits:
    - `2464e97` is S2a's interim tools, cherry-picked: the stub `RecursionFast/Challenge/V3.lean.in`,
      `scripts/render-challenge.py`, `scripts/harness-local.sh` and `scripts/setup-scratch.sh`;
    - `26c3b23` notes the amended contract in the stub's header;
    - `9d5b26a` makes `setup-scratch.sh` take `ENTRY_TARGETS`, so that only the needed modules
      are built.
  - The stub is unchanged: `Certificate`, `CertificateR` and `Declared` are the same in the
    amended contract. Only `Security.lean` differs from the pin.
- **The entry root.**
  - `claim.json`: the image `extractor.bin`/`extractor.data`, error `"1/2^128"` written out in
    digits, `qV` 16384, fuel `8 + 0·t`.
  - `extractor.S`, `build-extractor.sh`, `extractor.bin` and `extractor.data`, copied from
    `submissions/baseline` at `91b3a56`, with provenance lines.
  - `make-solution.py` (above).
  - `comparator.json` and `comparator-nanoda.json` (`SpartanChainChallenge`, `SpartanChainSolution`).
  - `SpartanChainRun.lean`, the runner built as `entry-run`, with the command
    `verify STMT PROOF` → `vb runLV`. **`runLV` is a STUB**, marked as such: `leafSize = 80`, and
    the SNARK branch rejects. It prints `leaf verifier: STUB`. Replace `runLV` when
    `Verifier.lean` lands.
  - `smoke.py` and `check.sh` (below).
- **`check.sh`.**
  - Set-up and source checks:
    - clones the branch into `CORE`; `BASE` must be an ancestor;
    - the image is reassembled and compared;
    - hygiene, reported only until the final module exists;
    - the source rule.
  - Build: the scratch clone, `ENTRY_TARGETS` = the contract, `SpartanChainSubmission`,
    `entry-run`, and later `SpartanChainFinal`.
  - Challenge: renders the stub with the claim; the challenge must have exactly its two `sorry`.
  - Solution:
    - with `SpartanChainFinal.lean`: generated, compared with the committed solution, built;
    - until then, **PREVIEW**: elaborated against a stand-in `SpartanChainFinal` whose only gap is
      `facts := sorry`.
  - Axiom audit of the infrastructure modules (Decode, VerifierTop, Submission, Run).
  - Negative claims (image bit, fuel 7, `qV − 1`), once final.
  - `smoke.py` and `loc.py`.
  - `HARNESS=1`: the comparator with both kernels and the gate through `harness-local.sh`, once
    final.
  - `LOGDIR` is never overwritten.
- **`smoke.py`.**
  - Builds the Rust prover: `cargo build --release --offline`, with `CARGO_TARGET_DIR` at
    `logs/spartan-chain/infra/target`, outside the root.
  - Runs the tree at `r = 2`, `n = 16`, and computes the digests independently (hashlib, tags from
    `Relation.lean`).
  - The **native** `verify` accepts every proof and rejects all four canaries on every proof;
    node sizes match the format; `node` reproduces `root.bin`.
  - The **Lean** `verify`:
    - with the stub, it rejects the `n = 16` leaves (expected). An `n = 0` tree is then run
      through both verifiers: every proof accepted, every canary rejected;
    - with the real leaf verifier, the `n = 16` tree is verified by it.
  - DoS sample on both verifiers.

## Measured (`logs/spartan-chain/infra/check-5/`, `check-5.log`, `check-4.log`)

All runs are `CHECK OK` in PREVIEW mode.

| What | Result |
|---|---|
| Source rule | 44 files, 0 findings |
| Hygiene | 0 findings |
| Axiom audit | 102 declarations, within the three axioms |
| Challenge | exactly 2 `sorry` |
| PREVIEW | OK |
| `SMOKE` | OK, with 147 `ok` lines |
| Native tree, `r = 2`, `n = 16` | 0.72 s, root 575 112 B |
| Lean, `n = 0` tree | root and every proof accepted, 28 canaries rejected |
| DoS sample | max 0.10 s (Lean), 0.011 s (native) |
| `cargo build --release` | 27.8 s |
| Scratch core clone, cold | 186.7 s (`check-1.log`) |
| `check.sh`, warm | 50.3 s |
| Code lines (`loc.py`) | Submission 167 (14 theorems), Run 48, VerifierTop 379 |

## Open, and deviations

- **Facts.** `Facts` is a hypothesis structure. Its satisfiability is not shown here: it needs the
  real parts. The PREVIEW checks only that the solution elaborates.
- **`submission` is noncomputable**, because of `ε`. Gate rule 4's per-field list is still v2's
  (S2a open question 3). The badge fields `V`, `P`, `E` and `img` compile, but rule 4 needs the v3
  field names to check them one by one.
- **`P`'s leaf with `n = 0`** emits the 80-byte header without calling `proveLeaf`. This matches
  `leafSize 0 = 80` (§7).
- **The runner's leaf verifier is a stub** until `Verifier.lean` exists.
- **Harness and negative claims are PENDING** until `SpartanChainFinal.lean` exists.

## Mid-review fixes (`docs/reviews/V3-S2b-midreview.md`)

- **S2b-M1, fixed.**
  - `Facts.queries` now reads
    `∀ H s n h sn, n ≤ chainCap → ((LV.prog s n h sn).queries H).length ≤ qVR1`.
  - `V_queries` takes `n ≤ chainCap` from `leafHeaderOK`, through `leafHeaderOK_iff`.
  - For the real verifier the field is now `Leaf.queries_le`. This was kernel-checked in the
    scratch file `logs/spartan-chain/infra/core/scratchm2/M1.lean`:
    `fun H s n h sn hn => Leaf.queries_le (H := H) ev s hn h sn`. The final module can use it as
    is.
- **S2b-M2, fixed.** A node codec over byte offsets is now in `SpartanChainDecode.lean`:
  - `encodeNodeB` builds the node encoding by `ByteArray` appends; `encodeNodeB_eq` proves it
    equal to `encode`, through `wordsBytes_packBytes`.
  - `nodeParse` reads the two length words, the two digests and the two children with `extract`,
    and tests canonicity against `encodeNodeB`.
  - `nodeParse_eq : nodeParse π = nodeSpec π` proves it equal to the library's canonical node
    decoding. It rests on `nodeParse_sound`, `nodeParse_encode` and `decode_node_fits`.
  - `check` and `checkNode` (`SpartanChainVerifierTop`) now run `nodeParse`. Every public
    statement is unchanged: `check_eq`, `checkNode_eq`, `checkNode_sound`, `check_encode_node`,
    `final_*`.
  - `P` builds nodes with `encodeNodeB`.

  Measurements: the compiled `vb (Leaf.leafVerifier chainEvals)`, on the same `r = 2`, `n = 16`
  Rust tree, `Vb` call time on the development VM.

  | Proof | Before | After |
  |---|---|---|
  | Root (575 112 B) | 2.33 / 2.40 / 2.51 s | 0.99–1.21 s over 8 runs (one outlier 1.71 s at load 6) |
  | Level-1 node | 0.83 s | 0.47 s |
  | Leaf | 0.24 s | 0.24 s |

  Logs: `logs/spartan-chain/fix-m2/before-root.log` and `after-root.log`. The root now costs
  about its four leaves (≈ 0.95 s) plus under 0.1 s of codec. A 1 MiB random proof is rejected in
  4 ms. The smoke run of `check.sh` measured the root check at 1.19 s of process wall
  (`logs/spartan-chain/infra/check-m2b/smoke.log`). Each level still copies its children
  (`extract`), so caterpillar proofs remain `O(|π|·depth)` (m4), now at memcpy cost.
- **S2b-m3, fixed.**
  - `check.sh` no longer uses `Run`. It builds the local runner `entry-verify` outside the root
    (`vb (Leaf.leafVerifier chainEvals)`, in the scratch core clone's `entrymain/`).
  - The PREVIEW stand-in uses the real leaf verifier.
  - `smoke.py` defaults to `entry-verify` and checks the real `n = 16` tree with the Lean
    verifier.
  - The source rule and hygiene are reported, and become fatal once `SpartanChainFinal.lean`
    exists. They currently flag `partial` in a comment of `SpartanChainSoundnessPCS.lean:511`,
    which is not one of these modules.
  - Run `logs/spartan-chain/infra/check-m2b.log`: `CHECK OK` (PREVIEW), axiom audit 111
    declarations, `SMOKE: OK` (109 checks, with the Lean root check and its 28 canaries).
- **S2b-m5, fixed.**
  - `LICENSE-leanerVM` is leanerVM's `LICENSE` (Apache-2.0) at `532ebb4`.
  - `README.md` (new) has a "Licences and provenance" section that names the copied files.
- **Not done here.**
  - m2, the equality of `Submission.P` with `Leaf.proveLeaf`: it needs the prover module's
    `leafHeader`, and is for the final instantiation.
  - m6 to m12 concern other modules.
