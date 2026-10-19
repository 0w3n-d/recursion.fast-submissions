# Baseline entry: the witness-sending argument (v3, stage S2)

The first entry of the submissions repository (DESIGN-v3 §7.3, §11 S2, V3-9). It is the trivial
argument: **the proof is the witness**. It is certified against the v3 contract at the pin
`15e4ae5`, proves the smoke tree, and is **listed, unranked**: its root check recomputes every
chain of the tree, which takes about 21 s at the ranked size (20.93 s median) against the succinctness cap
`T_V = 2 s` (§6.5). That measurement is what calibrates `T_V`.

This README is also the worked example of an entry: every certificate field, what the baseline
puts there, and who checks what. Section numbers (§n) refer to `docs/design/DESIGN-v3.md`.

## 1. Files

| File | What |
|---|---|
| `BaselineV3.lean` | the argument: the strict verifier `check`, `V`, the linear-time format functions (`decodeF`, `encodeF`, proved equal to the library's), `submission` and `certificate` |
| `BaselineV3Controls.lean` | kernel-checked controls: known answers of the format, the canaries that need no hash, statement binding, and why the library's own verifier is not used (§5) |
| `BaselineV3Solution.lean` | the solution: the rendered challenge with its two placeholders filled (`make-solution.py`) |
| `BaselineV3Run.lean` | the local runner of the compiled code (`verify`, `prove-leaf`, `prove-node`; built as `entry-run`), until S3's badge executables exist |
| `claim.json` | the claim: the image files, the error, the verifier query bound, the fuel |
| `extractor.S`, `build-extractor.sh`, `extractor.bin`, `extractor.data` | the extractor image (the core's `tests/asm/proofwords.S`, 8 instructions; no data) |
| `prover.py` | the native prover (python3, standard library only) |
| `smoke.py` | the smoke tree, the canaries, the node mode, a DoS sample and the calibration |
| `check.sh` | the end-to-end check (§4 below) |
| `comparator.json`, `comparator-nanoda.json` | the comparator configurations (Lean kernel; Lean kernel and nanoda) |
| `NOTES.md` | the journal |

**Not in this root: the organiser's side.** The v3 challenge stub, its renderer, the local proof
half of the harness and the scratch build setup are organiser material, and stage S3 owns them.
Until S3 exists they are **interim** files on the branch `v3/s2-interim-harness` of a scratch clone
of the core (`RecursionFast/Challenge/V3.lean.in`, `scripts/render-challenge.py`,
`scripts/harness-local.sh`, `scripts/setup-scratch.sh`; the paths the v2 harness used). `check.sh`
takes them from a clone of that branch (`CORE`, `ORG`), and the harness renders the challenge
itself from its own stub and this root's `claim.json`: the entry supplies no statement.

## 2. The argument

- **Proof format.** The core library's `encode` (`RecursionFast.Library.WitnessSending`): the
  bytes of the extractor output words of the witness (`witWords`, `Contract/Extractor.lean`'s
  output format), 8 little-endian bytes per word.

  ```
  leaf (s, n)            u64(0) ‖ s ‖ u64(n)                                         48 bytes
  node (c₁, c₂, π₁, π₂)  u64(1) ‖ c₁ ‖ c₂ ‖ u64(|π₁|) ‖ π₁ ‖ 0-pad ‖ u64(|π₂|) ‖ π₂ ‖ 0-pad  (pad to 8)
  ```

  So a proof is 48 bytes at a leaf and `88 + 2 · |child|` bytes at a node with two equal
  children: 184 and 456 bytes at levels 1 and 2, and 34,728 bytes at the root of the ranked tree
  (`r = 8`).
- **`V c π := .ret (check c π)`**: no oracle query. `check` decodes `π`. A leaf passes when `π` is
  the canonical encoding of the leaf, `n ≤ chainCap` (checked before any hash) and
  `c = leafStmt (chainEnd s n) n`. A node passes when `π` is the canonical encoding of the node,
  `c = nodeStmt c₁ c₂`, each child is at most `proofCap` bytes and is accepted by `check`,
  recursively.
- **`P c w := .ret (encode w)`**, **`E c π L := decode π`**: the library's.
- **`img`**: the library's 8-instruction image. On the input tape `⟦c, |π|, π, |L|, L⟧` the proof's
  packed words already are an output in `decodeWit`'s format, so the image returns them in place:
  `a0 :=` the address of tape word 5, `a1 := ⌈|π| / 8⌉`, HALT. 8 steps on every input.

## 3. The objects, field by field

The contract is `.contract/RecursionFast/Contract/Certificate.lean` at the pin.

### 3.1 `Submission`

| Field | Meaning | The baseline | Checked by |
|---|---|---|---|
| `V` | the verifier, a query program | `.ret (check c π)` | kernel (types); gate rule 4 (`submission` compiled as a whole, which covers every field) |
| `P` | the honest prover, a query program | `.ret (encode w)` (library) | kernel; gate rule 4 (as for `V`) |
| `E` | the extractor's specification | `decode π` (library) | kernel; gate rule 4 (as for `V`) |
| `img` | the extractor as a RISC-V image | `proofwords.S`, 8 words (library) | kernel; bound to the claim's files (§3.3) |
| `ε` | knowledge error per fresh query | `0` | kernel |
| `qV` | verifier query bound | `0` | kernel |
| `fuel` | the image's step budget, by tape length `t` in words | `fun _ => 8` (library) | kernel |

`Submission.Vb S c π := if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false` is what
the relation and the harness use. For the baseline, `Vb c π = (π.size ≤ proofCap && check c π)`
(`Vb_eq`), and what it decides is one theorem, `Vb_iff`: `Vb c π = true` exactly when
`π.size ≤ proofCap` and `π` is the canonical encoding (`encode w = π`) of the witness `w` it decodes
to, with `Rel S.Vb c w`.

### 3.2 `Certificate`

| Field | Statement | Discharge | Where |
|---|---|---|---|
| `secure` | `KS (Rel S.Vb) S.V S.E S.ε S.qV`: a bounded knowledge state and `≤ qV` queries | `good := True`, `bad := False`. `final`: an accepted proof decodes to a witness of `Rel S.Vb` (`check_sound`), and `E = decode` returns it. `Bounded 0`: no answer is bad (`bounded_of_not_bad`). `V` asks no query | `BaselineV3.ks` |
| `complete` | `Complete (Rel S.Vb) S.P S.V`, every oracle | `check c (encode w) = true` whenever `Rel S.Vb c w` (`check_encode`): every witness of the relation fits the format (`fits_of_rel`), so `decode (encode w) = w` | `BaselineV3.complete` |
| `computes` | `ImageComputes S.img S.E S.fuel` | the library's theorem: the image outputs the proof's words in 8 steps, and they denote `decode π` | `WitnessSending.computes` |
| `cap` | `ε ≤ 2^-128`, `qV ≤ 2^16`, `fuel t ≤ 2^40 + 2^8 t`, image `≤ 2^20` bytes | `0`, `0`, `8`, 32 bytes | `BaselineV3.certificate` |

### 3.3 The claim, the challenge and the solution

`CertificateR D S` extends the certificate with the binding to the rendered claim `D : Declared`:
`S.img = D.img`, `S.ε ≤ D.ε`, `S.qV ≤ D.qV`, and `S.fuel t ≤ D.fuel t ≤ B t` for every `t`.

- **The claim** (`claim.json`): `image` (`extractor.bin`, `extractor.data`), `error` `"0"`, `qV`
  `0`, `fuel_base` `8`, `fuel_per_word` `0`. The declared fuel is `fuel_base + fuel_per_word · t`.
- **The challenge** (organiser-side): the organiser renders its stub with the claim
  (`scripts/render-challenge.py RecursionFast/Challenge/V3.lean.in claim.json`, interim, see §1) to
  `BaselineV3Challenge.lean`: the image as packed literals read back by the contract's `unpack`,
  `declared`, and the two placeholders `submission : Submission := sorry` and
  `certified : CertificateR declared submission := sorry`. The renderer's rules are v2's: the key
  set equals the placeholders, no float, no duplicate key, plain relative paths.
- **The solution** (`make-solution.py`): `submission := BaselineV3.submission` and
  `certified := ⟨BaselineV3.certificate, rfl, zero_le, le_rfl, fun t => ⟨8 ≤ 8 + 0·t, 8 + 0·t ≤ B t⟩⟩`.
  The image binding is `rfl`: the rendered image is definitionally the library's literal.

## 4. Who checks what

| Checker | What it checks | For this entry |
|---|---|---|
| **Kernel** (build) | every field of §3 has its type; `check.sh` also runs `leanchecker` on the solution's closure | all pass |
| **Axiom audit** (`check.sh` step 7) | `#print axioms` of every declaration of the entry | only `propext`, `Classical.choice`, `Quot.sound` |
| **Source rule** (the core's `scripts/source-rule.py`) | no elaboration-time or load-time code, no code-changing attribute, no `unsafe`/`partial` | 0 findings |
| **Comparator** (interim `scripts/harness-local.sh` stage 1, a fresh sandboxed tree; the challenge rendered by the harness from the organiser's stub) | the challenge is built and exported first; `certified` has the challenge's statement, the axioms are permitted, only `submission`'s value differs; replayed by the Lean kernel and nanoda | "Your solution is okay!" |
| **Gate** (stage 2, a second fresh tree, byte-identical build) | trust by `.olean` hash against a manifest of a clean organiser build; no `sorryAx` or other axioms; no `unsafe`/`partial`/`opaque` and no code-substituting attribute in untrusted modules; imports within the allowlist; the badge path compiled | PASS: `submission` has compiled code as a whole (rule 4 checks the whole constant; its per-field list is still v2's). Interim limits: the manifest and the allowlist are generated from the same organiser clone, and the allowlist (v2's closure) admits `RecursionFast.Controls` |
| **Smoke** (`smoke.py`, until S3's runner) | the native prover's tree at `r = 2`, `n = 16` against independently computed digests; the four canaries; node mode; Lean `P` = native prover; a DoS sample | all pass |
| **Calibration** (`smoke.py --calibrate`) | the compiled root check at `r = 8`, `n = 2^14` | about 21 s, above `T_V = 2 s`: listed, unranked |

The badge executables, the benchmark run, the extractor liveness on the emulator and the
`treeRoot` known-answer test are S3's; nothing of them runs here.

## 5. Why the entry has its own verifier

The core library's `check` checks canonicity only for nodes. For a leaf, the decoder reads six
words and ignores the rest, so the library accepts a leaf proof with a byte appended and with its
last byte removed: two of the four canaries of §6.3 step 7 (`BaselineV3Controls.lib_check_appended`,
`lib_check_truncated`). The entry's `check` requires the canonical encoding of every proof. The
relation is about the submission's own instantiated verifier, so the children must be checked by
the strict `check` too; hence `check` and its two proofs (`check_sound`, `check_encode`) are the
entry's, and everything else is imported from the library.

The contract's `packBytes` and `bytesAt` compile to quadratic code. The verifier therefore runs
`decodeF` and `encodeF`, linear in the length of the proof they read and proved equal to `decode`
and `encode` (`decodeF_eq`, `encodeF_eq`); the proofs reason about the library's functions only
(`check_eq`). The whole verifier is not linear: each node decodes and re-encodes its whole subproof
before recursing, so its time is `O(Σ over the nodes of the subproof size)`, i.e.
`O(|π| · depth)` (§7).

## 6. Measurements

On the development VM (QEMU virtual CPU, 32 logical CPUs, AVX2, no `pclmulqdq`; not the reference
machine, O-6). Logs under `logs/V3-S2/` (gitignored), quoted in `docs/stages/V3-S2a-RESULT.md`.

| What | Measured | Log |
|---|---|---|
| root check, compiled `Vb`, `r = 8`, `n = 2^14` (34,728-byte root proof) | 20.69 / 21.11 / 20.93 s process wall (median 20.93 s; the `Vb` call alone 20.85 s), about 5.0 µs per compression | `logs/V3-S2/fix/calibration-r8-n16384.log` |
| native prover, whole tree, `r = 8`, `n = 2^14` (32 processes) | 0.52 s wall | same |
| root check, `r = 2`, `n = 16` (456-byte root proof) | 2.0 ms (`Vb` call) | `logs/V3-S2/fix/check/smoke.log` |
| DoS sample: 16 random proofs, uniform length up to `2^20` | max 0.28 s process wall, all rejected | same |
| adversarially shaped `2^20`-byte proofs under the root digest (tag 0; tag 1; node with consistent lengths) | max 1.25 s process wall, all rejected | same |
| valid lopsided proofs, no chain work (review) | depth 2,000, 272 KB: 212.6 s | `logs/V3-S2/review/caterpillar.log` |
| clean build of the entry (4 modules, the executable) | 15.8 s wall, 2.2 GB max | `logs/V3-S2/fix/check/build-entry.log` |
| `leanchecker BaselineV3Solution` | 24.5 s wall, 1.7 GB max | `logs/V3-S2/fix/check/leanchecker.log` |
| comparator (Lean kernel and nanoda) | 72.7 s wall, 1.0 GB max | `logs/V3-S2/fix/check/harness-work/comparator.log` |
| `harness-local.sh` (render, comparator, rebuild, gate) | 122.9 s wall | `logs/V3-S2/fix/check/harness.log` |
| `HARNESS=1 check.sh` from fresh scratch clones (two core builds included) | 530.8 s wall | `logs/V3-S2/fix/check-run.log` |

So `T_triv ≈ 21 s ≥ 5 · T_V = 10 s` (§6.5), and the root check stays within `verify_s = 60 s`.

## 7. Known properties

- **Verifier time.** Two terms: the chain work (as many compressions as the proof's chains
  declare, up to `chainCap = 2^20` per leaf) and the decoding, which is `O(|π| · depth)`: every
  node decodes, re-encodes and compares its whole subproof. On honest balanced trees the depth is
  `r` and the decoding is negligible (the ranked root check is all chain work). On valid lopsided
  proofs it dominates. Measured by the review on "caterpillar" proofs (every node a deeper left
  child and a zero-step leaf, so no chain work): depth 250, 34 KB: 2.7 s; depth 500: 11.6 s; depth
  1,000: 49.6 s; depth 2,000, 272 KB: **212.6 s**, past `verify_s = 60 s`
  (`logs/V3-S2/review/caterpillar.log`). This is a DoS-column property of this unranked entry:
  under the runner's root digest such a proof needs a hash preimage, and the DoS column draws random
  proofs, which are rejected within 0.25 s; adversarially shaped 1 MiB proofs under the root digest
  are rejected within 1.3 s (`smoke.log`). It matters to anyone who runs `verify` on a statement
  the prover chose.
- **Interim tooling.** The challenge stub, the renderer and the local harness are organiser-side
  stand-ins for S3, outside this root (§1). The claim schema (`error`, `qV`, `fuel_base`, `fuel_per_word`) is this
  entry's proposal; S3 fixes the v3 one.
- **Prover file formats** (`leaves.json` as `{"n", "starts"}`, levels `N1_j` … `Nr_0`) are this
  entry's; S3 fixes them.
