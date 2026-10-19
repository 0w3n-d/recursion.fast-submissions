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
