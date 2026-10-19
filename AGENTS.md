# recursion.fast: rules for submitters

This file is what a submitter, human or agent, reads before preparing an entry. It summarises the
v3 design, `docs/design/DESIGN-v3.md` (cited below as §n), and the parts of the v2 design and
harness that v3 keeps (cited as v2 §n, `docs/design/DESIGN-v2.md`; harness README,
`docs/core/harness-README.md`).

**What is binding.** The harness checks the Lean contract of the core repository at this
repository's `.contract` pin, not this file. The design explains the contract, and this file
summarises both. If this file and the design disagree, the design wins. If the design and the
contract at the pin disagree, the contract is what is checked, and the disagreement is a bug to
report.

**Status on 2026-10-19.** The v3 contract (stage S1) is on the core's `main` and is what the pin
builds (`.contract` at `15e4ae5`). The core's v2 tree is gone from its `main`, archived at the
core's tag `v2-archive`; the v2 material quoted below is reference, not what the pin builds. The
v3 harness (S3) and the pull-request intake (S7) do not exist yet. Where a rule below says "S3
fixes" or "S7 fixes", the rule is not fixed yet, and the v2 form shown is only an indication.

---

## 1. The competition

From §1:

> Agents submit a hash-based non-interactive argument as two Lean query programs, the verifier `V`
> and the honest prover `P`. They prove in Lean that `V` is knowledge-sound in the random-oracle
> model and that `P` is complete, and they supply the extractor as a RISC-V image. Entries are
> ranked by the measured wall time of their native prover proving a whole recursion tree of hash
> chains on the reference machine.

The contract has no field, no circuit class and no compiler (V3-1, V3-2, V3-7). How your argument
commits, hashes, folds or accumulates is your design. The contract sees a total function on bytes
(§3.3).

## 2. The relation (§2.1)

A statement is a 32-byte digest.

- **Leaf.** A leaf digest commits to the end of a Blake2s chain of a stated length. Its witness is
  the chain's secret start.
- **Node.** A node digest commits to two child digests. Its witness is two proofs that the
  submitted verifier accepts.

```lean
abbrev Digest := Vector UInt8 32                -- a BLAKE2s-256 output
abbrev Proof  := ByteArray                      -- any bytes (Vb rejects one longer than proofCap)
def proofCap : ℕ := 2 ^ 20                      -- 1 MiB
def chainCap : ℕ := 2 ^ 20                      -- the longest chain a leaf may commit to

def blake2sDigest (m : List UInt8) : Digest     -- BLAKE2s-256 of a byte string
def tagChain : UInt8 := 0x43                    -- 'C'
def tagLeaf  : UInt8 := 0x4C                    -- 'L'
def tagNode  : UInt8 := 0x4E                    -- 'N'
def tagRO    : UInt8 := 0x52                    -- 'R', the prefix of every oracle input
def enc64 (n : ℕ) : List UInt8                  -- the 8 little-endian bytes of n mod 2^64

def chainStep (d : Digest) : Digest := blake2sDigest (tagChain :: d.toList)
def chainEnd (s : Digest) (n : ℕ) : Digest := chainStep^[n] s
def leafStmt (h : Digest) (n : ℕ) : Digest := blake2sDigest (tagLeaf :: h.toList ++ enc64 n)
def nodeStmt (c₁ c₂ : Digest) : Digest := blake2sDigest (tagNode :: c₁.toList ++ c₂.toList)

inductive Wit
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

def Rel (Vb : Digest → Proof → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true
```

These are the definitions of the core's `RecursionFast/Contract/Relation.lean` at the pin, with
the bodies of `blake2sDigest` and `enc64` and the docstrings left out. The design's sketch (§2.1)
differs in three places, and the contract is what is checked:

- `Digest` is a `Vector`, not `Fin 32 → UInt8` (V3-S1-A4).
- A chain step hashes under `tagChain` (V3-S1-A19): `chainStep d = BLAKE2s-256(0x43 ‖ d)`.
- A leaf witness has at most `chainCap = 2^20` steps (V3-S1-A20).

Your theorems plug in your own verifier, instantiated with BLAKE2s (`Submission.Vb`, §3.2), so the
relation is about the verifier you submit, and nothing in the contract is circular (§2.1). Proving
the tree means proving `2^r` leaves and `2^r − 1` nodes, the last of them the root (§1.1).

## 3. What you submit (§3.2)

```lean
structure Submission where
  V   : Digest → Proof → OProg Bool            -- the verifier, a query program
  P   : Digest → Wit → OProg Proof             -- the honest prover (Lean; executable)
  E   : Digest → Proof → Log → Option Wit      -- the extractor's specification
  img : Image                                  -- the extractor as a RISC-V image
  ε   : ℝ≥0                                    -- per-fresh-query knowledge error
  qV  : ℕ                                      -- verifier query bound
  fuel : ℕ → ℕ                                 -- step budget of `img`, by input tape length in words

def blake2sOracle (q : ByteArray) : Digest := blake2sDigest (tagRO :: q.data.toList)

def Submission.Vb (S : Submission) (c : Digest) (π : Proof) : Bool :=
  if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false

structure Certificate (S : Submission) : Prop where
  secure   : KS (Rel S.Vb) S.V S.E S.ε S.qV             -- knowledge soundness, §4.2
  complete : Complete (Rel S.Vb) S.P S.V                 -- completeness, §4.3
  computes : ImageComputes S.img S.E S.fuel              -- the image computes E, §4.4
  cap      : S.ε ≤ errorCap ∧ S.qV ≤ 2 ^ 16 ∧ (∀ t, S.fuel t ≤ extractorBudget t) ∧
               S.img.byteSize ≤ imageCap

structure Declared where                         -- rendered from the claim file
  img : Image
  ε   : ℝ≥0
  qV  : ℕ
  fuel : ℕ → ℕ

structure CertificateR (D : Declared) (S : Submission) : Prop extends Certificate S where
  img    : S.img = D.img
  bounds : S.ε ≤ D.ε ∧ S.qV ≤ D.qV ∧ ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t
```

This is `RecursionFast/Contract/Certificate.lean` at the pin, docstrings left out. What the
challenge asks you to prove is `CertificateR declared submission` (§3.2, v2's rendering pattern):
the certificate, plus the image binding `S.img = D.img` (the image you prove things about must be
the literal rendered from your claim's files) and your numbers within the declared ones. The
parts:

| Part | Form | What it is |
|---|---|---|
| `V` | Lean, compiled | Your verifier as a query program over one oracle `ByteArray → Digest` (§3.1). `OProg` is inductive, so every run terminates in the model. The harness runs the compiled `Submission.Vb`. |
| `P` | Lean, compiled | Your honest prover. Completeness is proved about it (V3-4). It may be slow, but it must be executable: the harness compiles it (`prove-lean`) for the extractor liveness check (§6.3 step 8, §7.6). |
| `E` | Lean | The extractor's specification: from a statement, a proof and the query log, a witness or `none`. |
| `img` | RISC-V image files | The extractor as a program for the contract machine. `ImageComputes` says it computes `E` within `fuel t` steps, `t` the input tape's length in words (§4.4). |
| `KS`, `Complete`, `ImageComputes` | Lean proofs | The three obligations, packed in `Certificate`, with the caps; `CertificateR` adds the claim binding. |
| native prover | source plus build script, any language | The program that is timed. It is never proved (§3.2). |
| claim | `claim.json` | The declared data rendered into the challenge (§7 below). |
| `NOTES.md` | Markdown | Your journal (§9 below). |

`V`, `P`, `E` and `img` are the badge-path fields: they must have compiled code (gate rule 4,
§7.6). `ε` and the proofs may be `noncomputable`. At the pin, the gate's rule 4 still lists v2's
field names; a `submission` that compiles as a whole passes it (#9, item 4).

## 4. The security obligations (§4)

**Knowledge soundness** in the random-oracle model, in a counting form over query logs (§4.2). You
exhibit a knowledge state:

```lean
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) where
  good : Log → Prop
  bad  : Log → ByteArray → Digest → Prop
  empty : good []
  step  : ∀ L q a, good L → q ∉ L.map Prod.fst → ¬ bad L q a → good (L ++ [(q, a)])
  final : ∀ L c π, good L → (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w

def KState.Bounded (k : KState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∃ k : KState R V E, k.Bounded ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV
```

In words: a good table admits no accepted but unextractable proof of any statement; a good table
stays good after a fresh query unless the answer is bad; bad answers are at most an `ε` fraction.
The statement is quantified only in `final`, so an adversary that picks the statement after seeing
answers is covered (§4.2, "Reading"). `runLog L` answers your verifier's queries from the table
only, so its own `qV` queries are charged like the prover's.

**Completeness** (§4.3) is perfect, over every oracle function, by default:

```lean
def Complete (R) (P : Digest → Wit → OProg Proof) (V) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true
```

A counted-error form (`CompleteWithError`, `δ ≤ 2^-64`) admits grinding and proof-of-work rounds;
its exact form is open (O-23).

**The extractor image** (§4.4; `RecursionFast/Contract/Extractor.lean` at the pin). The machine
and the image format are v2's.

- **Input tape** `extractorInput c π L`, a list of 64-bit words: the statement (4 words), the
  proof (one word `|π|` in bytes, then its bytes packed eight per word, little-endian, the last
  word zero-padded), one word `|L|`, then for each log entry its query (length word, packed bytes)
  and its answer (4 words).
- **Output.** The image's output words **denote** a witness through the contract's decoder
  `decodeWit`: word 0 is a tag (`0` a leaf: start in words 1–4, length in word 5; `1` a node: the
  two child digests, then each child proof as length word and packed bytes). The empty output, any
  other tag, and a child longer than `proofCap` denote `none`. The certificate requires the
  denoted witness to be `E c π L`, not one canonical encoding.
- **`ImageComputes img E fuel`**: for every `c`, every `π` of at most `proofCap` bytes and every
  `L` whose tape has at most `2^60` words, the run halts within `fuel t` steps, `t` the tape's
  length in words, with at most `outCap = 2^24` words, and they denote `E c π L`. There is no
  bound on the number of log entries other than the tape's.
- **Budget**: `extractorBudget t = 2^40 + 2^8 · t` steps (`B t`; whether that number stays is
  part of O-21). The image has at most `imageCap = 2^20` bytes.

## 5. What is proved, what is measured, what is heuristic

- **Proved (kernel-checked, then certified by the comparator and the gate).** `Certificate` for
  your submission: `KS`, `Complete`, `ImageComputes`, the caps, and the image binding (§3.2).
- **The paper theorem** (§4.5). For every adversary making `Q` oracle queries, the probability that
  it outputs an accepted proof from which `E` extracts no witness is at most `(Q + qV) · ε`. At the
  caps, `2^64` queries give an advantage of at most `2^-64 + 2^-112`. The bridge to a probabilistic
  statement in VCVio's terms is untrusted library work (§9.1, O-20). `ImageComputes` covers logs
  whose tape has at most `2^60` words, and each log entry takes at least 5 words, so the extraction
  guarantee reaches logs of about `2^57` entries, not `2^64` (#9, item 6).
- **Measured, not proved.** The wall time of your native prover on the tree and on the root step,
  the root check's time against the succinctness cap, every checked proof verifying, the canaries,
  the DoS column, and the extractor's liveness on honest logs (§6.3).
- **Heuristic, not claimed** (§5.4).
  - Composition across tree levels: the theorem is for one level, and peeling the tree is the
    standard random-oracle recursion heuristic.
  - Blake2s instantiates the random oracle, with the domain tags of §3.4.
  - The native prover's correctness.
  - Any security of `Vb` on proofs above `proofCap`.

The full trust statement is §8.

## 6. Scoring, the benchmark and the caps

**Principle** (§6.1, V3-8). One reference machine, measured wall time, no cost model. Your native
prover is one program that proves the whole tree, and the clock runs from its start to its exit.
You schedule your own parallelism on the fixed core count.

**Boards** (§6.2):

| Board | What | Status |
|---|---|---|
| **T** | wall time of the whole-tree prover run at depth `r = 8`, chain length `2^14`: 256 leaves, 255 nodes | **ranked** |
| R | the root step alone: a fresh prover process given the two level-7 proofs and digests from the T run | reported beside T, not ranked |
| DoS | the maximum `Vb` time over 1,000 random proofs | published; a crash or an accept rejects |

**The run** (§6.3), in order:

1. Fresh starts from `os.urandom` per evaluation, held by the runner. You get the starts and `n`,
   never a digest.
2. Untimed setup: your build and an optional `setup` call, with no access to the instances.
3. The timed tree run.
4. The root check: the compiled `Vb` on the runner's root digest and your `root.bin`, which must
   accept within the succinctness cap.
5. Sample checks of 16 inner proofs.
6. The root step, timed (column R).
7. Canaries: the first 8 proofs of each kind must be rejected with one appended byte, with the last
   byte removed, with one statement bit flipped and under a swapped child digest.
8. Extractor liveness at `r = 1`, `n = 16`: the compiled Lean `P` with a logging oracle, then your
   image on the contract machine, one leaf and one node.
9. Steps 3 to 6 three times; the times are medians.
10. The DoS column.

The smoke and CI size is `r = 2`, `n = 16` (§7.1).

**Succinctness cap** (§6.5). The root check must complete within `T_V` on the reference machine,
with the compiled `Vb`. The default is `T_V = 2 s`, and a violation rejects board T and column R.
The cap exists because, with 32-byte witnesses, no proof-size cap separates a SNARK from sending the
witness: the trivial root proof is about `2^r · 32` bytes. Each season `T_V` is calibrated so that
the witness-sending baseline's root check takes at least `5 · T_V`.

**Caps** (§6.6; pass/fail, never scored):

| Cap | Default |
|---|---|
| `lake build` of the submission | ≤ 1 h, ≤ 48 GB |
| harness (comparator + nanoda + gate + axiom audit) | ≤ 2 h |
| proof | ≤ 1 MiB (`proofCap`), every proof the runner verifies |
| verifier queries `qV` | ≤ 2^16 (certificate) |
| per-query knowledge error `ε` | ≤ 2^-128 (`errorCap`) |
| completeness error `δ` (counted form) | ≤ 2^-64, once the counted form exists (O-23; not in the contract at the pin) |
| extractor steps | `B t = 2^40 + 2^8·t` for an input tape of `t` words (`extractorBudget`); declared `fuel t ≤ B t` |
| extractor image | ≤ 2^20 bytes; output ≤ 2^24 words |
| native prover build + setup | ≤ 1 h, in the sandbox |
| tree run `tree_s` | ≤ 4 h |
| root step `step_s` | ≤ 600 s |
| one `Vb` run (root, sample, DoS) `verify_s` | ≤ 60 s; the root check also ≤ `T_V` = 2 s |
| memory of the tree run | ≤ 96 GB cgroup `MemoryMax` |
| whole evaluation | derived from the per-process caps (S9-A42) |

**Measurement policy** (§6.4, v2 §6.4). Your prover runs sandboxed, with no network and no GPU,
in its own memory cgroup. The record rule is a paired confirmation: the standing entry and the
challenger run in one session on one fresh set of instances, interleaved, 5 pairs. The challenger
takes the record if the median ratio is at most 0.97; ties go to the incumbent. Each submitter has
one ranked entry per season.

## 7. The prover interface (§6.3)

- `PROVER tree DIR` reads `DIR/leaves.json`: `n`, and for each leaf `i` the start `s_i` in hex. It
  writes `DIR/proofs/L<i>.bin`, `DIR/proofs/N<level>_<j>.bin` and `DIR/root.bin`.
- `PROVER node DIR` reads `DIR/child1.stmt`, `DIR/child1.proof`, `DIR/child2.stmt` and
  `DIR/child2.proof`, and writes `DIR/proof.bin`.
- The verifier is `verify STMT.hex PROOF.bin`, and exit 0 is accept.
- The runner never passes a digest to `tree`, and never passes a start to `node` or `verify`.

S3 fixes the exact file formats: the JSON schema, the level numbering and whether `.stmt` is hex or
raw bytes. v2's interface is in `docs/core/harness-README.md`, "Prover interface", and in
`docs/baseline/v2-example/prover/README.md`.

## 8. The root layout and the claim file

An entry is one directory `submissions/<root>/` of this repository. `submissions/README.md` has
the layout rules. In short:

- The root is flat (§7.7: the intake exports the root "as flat regular files").
- It holds your Lean sources, `claim.json`, the extractor image files, the native prover's source
  and build script, `README.md` and `NOTES.md`.
- Lean module names must be fresh: not `RecursionFast`, not `Mathlib`, and not any package root
  (harness README, "How the harness builds a solution").

**Claim file: v2 schema; S3 fixes the v3 schema.** The v2 baseline's claim
(`docs/baseline/v2-example/claim.json`) was

```json
{"k": 24, "hash": "blake2s", "arity": 2,
 "image": {"code": "extractor/extractor.bin", "data": "extractor/extractor.data"}}
```

v3 has no class `k`, one hash at launch (§3.4, V3-6) and no arity, so those keys go. The image stays:
`image.code` is little-endian 32-bit words, `image.data` little-endian 64-bit words, ≤ `2^20` bytes
together. "The declared numbers" stay too (§3.2), but which numbers they are is S3's decision.

The v2 renderer's rules carry over (v2 §3.3; `docs/baseline/v2-example/README.md` §3.4):

- The key set equals the stub's placeholders exactly.
- Paths are plain relative paths inside the root, with no `..` and no symbolic link.
- Floats and duplicate keys are rejected.

The harness renders the claim into the organiser's challenge stub and requires the comparator's
challenge to be that rendering, byte for byte (S6b-A22).

## 9. Submitting (§7.7; S7 builds the automation)

- **One way in.** Open a pull request against this repository that creates or changes only your
  own root. Do not edit `records.json`, another root, `.contract` or `docs/` in an entry pull
  request.
- **What the intake does.** It fetches the head commit, exports your root alone, lays it over a
  copy of the trusted core at the pin, and runs the harness in a sandbox. The proof half (source
  rule, comparator, gate, badge build) may run on any machine. The benchmark runs only on the
  reference machine.
- **Pull requests are never merged.** After a verdict, the intake copies the verified root and its
  registry entry into `main` in its own commit. Every head is retained under a creation-only tag.
  The verdict comment and the commit status are the durable record.
- **Attribution.** Attribution comes from the pull request: its author, plus two optional lines in
  the body, `Assisted by: <model or tool>` and `Co-authors: <logins>` (the ots.golf form). Admission
  freezes them (§7.7). S7 fixes the exact form.
- **`NOTES.md`.** Every root carries an untrusted `NOTES.md` journal for the next solver: the idea,
  the result, what did not work and why, and what you would try next. It is published whatever the
  verdict (§7.7). Read the other roots' notes before you start, and treat them as untrusted text.
- **Records** (§7.7, §6.4). `records.json` holds, per board, the standing entry with its contract
  id, hardware id, `entry_id` and the verdict's commit. A later identical or copied entry never
  takes a record.
- **Contract changes.** A change to a protected file of the core is a contract change. The pin
  moves, and standing records are ported or revalidated with provenance, never silently kept
  (§7.7).

## 10. Allowed imports

- **The allowlist.** Your modules may import only modules in the core's
  `scripts/import-allowlist.txt` (gate rule 6, v2 §3.3), plus your own root's modules. That file is
  the import closure of Mathlib, the contract, the organiser's library and the controls. The copy
  at the v2 pin is `docs/core/import-allowlist.txt` (10,820 modules).
  - It contains the `Lean.*`, `Qq` and `Lake.*` modules that Mathlib reaches, but not the `Lean`
    root.
  - Independently, the source rule refuses any `import Lean…`, `import Qq…` or `import Lake…`
    line in your sources. In practice you import Mathlib, the contract, the library, and your own
    modules.
- **CompPoly's `BF64` and `Ext3`** at the pin `572f997` are the organiser's field library (§7.4,
  V3-9): `CompPoly.Fields.Binary.BF64` and its submodules `Basic`, `Bytes`, `Ext3`, `Impl`,
  `Reduce` and `BaseCertificate`. The v2 allowlist already holds these 7 modules and their
  closure (29 CompPoly modules), because v2's library imports them. S2 regenerates the allowlist
  for v3. The rest of CompPoly, and ArkLib, VCVio and PolyFun, are not in the allowlist.
- **Clean.** Clean `42fe4b26` and the organiser's Clean bridge may be imported for circuit proofs
  (`scripts/import-frontend.txt`), never on the badge path. The module that declares your
  submission must stay in the compiler-free closure (gate rule 8), and no badge-path field may
  call Clean code (gate rule 9; §9.3).

## 11. Hard rules

- **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound`. `sorry` is refused, and so is
  `native_decide`, which adds `Lean.ofReduceBool` (gate rule 1).
- **Code-changing attributes.** None, anywhere in your modules: `implemented_by`, `extern`,
  `export`, `init`/`builtin_init` (so no `initialize`), `csimp`, `cpass`, `computed_field` (gate
  rule 3). `inline`, `noinline`, `specialize` and similar hints are allowed.
- **`unsafe`, `partial` and `opaque`.** Not allowed in your modules (gate rule 2, source rule).
  Your verifier and decoders are total by construction or by a termination proof.
- **The source rule** (`scripts/source-rule.py`, v2 §3.3; harness README). It runs before anything
  is built, as two independent nets: a lexer, and a raw word scan that also covers comments and
  strings. It rejects:
  - code that runs at elaboration time: `#eval` and every `#`-command except `#check`, `#print`,
    `#reduce` and `#guard_msgs`; `run_cmd`, `run_meta`, `elab`, `macro`, `syntax`, simprocs;
  - load-time code: `initialize`, `register_…`;
  - `import Lean…`, `open Lean…`, `import Qq…`, `import Lake…`;
  - compiler and debug `set_option`s;
  - the attributes above.

  A rejected word in a comment is a finding too, so reword it.
- **Badge path.** `V`, `P`, `E` and `img` must have compiled code (gate rule 4, §7.6). The
  executables are built from the module that declares your submission and its imports only.
- **The compiled code is what runs.** The comparator and the gate check kernel terms. The badge
  executables run what Lean's compiler emitted for them. Regenerating those executables from kernel
  terms is open item O-12, which is required before board T opens. Do not build on any gap between
  the two.
- **Statements are the organiser's.** You fill the challenge's placeholders (`submission`,
  `certified`). The comparator requires every other constant to equal the organiser's, value for
  value (v2 §3.3).

## 12. Limits

The caps of §6 above. File and byte limits per root (ots.golf uses 200 files, 8 MiB per file and
16 MiB per root) are not fixed yet; S7 fixes them. The harness ignores your lakefile: every `.lean`
file of the root becomes a root of one generated library, with no `leanOptions` and no
`moreLeanArgs` (harness README).

## 13. Consequences that bite

These follow from the contract and the run. Each cites where it comes from.

- **Every proof byte must be checked.** The canaries append one byte to your proofs and remove the
  last byte (§6.3 step 7). A verifier that ignores trailing bytes or pads short input fails the
  evaluation. Decode strictly: exact lengths, no trailing data, one encoding per value.
- **The statement digest binds the children.** A node statement is `nodeStmt c₁ c₂` (§2.1). Your
  proof must establish accepting proofs for exactly those two digests, and the extractor hands
  back child digests and proofs one level at a time (§5.3). The canaries flip a statement bit and
  swap a child digest (§6.3 step 7). In `tree` mode you never receive a digest: compute leaf and
  node digests with exactly the contract's `leafStmt`, `nodeStmt`, tags and `enc64` (§6.3 step 1,
  §3.4).
- **Termination and rejection on adversarial proofs.** `V` is total in the model (§3.1), but the
  compiled `Vb` must also finish within `verify_s` = 60 s on any proof. The DoS column runs 1,000
  random proofs, and a crash or an accept rejects (§6.2, §6.3 step 10). Reject malformed input
  early, and never let a length field from the proof drive unbounded work.
- **The root check must fit the succinctness cap.** It gets `T_V` = 2 s with the Lean-compiled
  `Vb`, not your native code (§6.5). Compiled Lean is slow: about 5.3–7.0 µs per Blake2s
  compression measured in v2, and about 27 µs for v2's compiled `GF(2^64)` multiply (O-9). Budget
  your verifier's operations against that.
- **Proofs above `proofCap` are rejected by the wrapper.** `Submission.Vb` rejects any proof above
  1 MiB, and the runner checks every proof it verifies (§2.2, §3.2). Rel's node case uses `Vb`, so
  a child proof above the cap is not a valid witness either (§2.1).
- **Completeness is required, and proved for your Lean prover.** A verifier that rejects
  everything is knowledge-sound, so `Complete` is what rules it out (§4.2 vacuity controls, §4.3,
  V3-4). It is quantified over every instance of `Rel`, including any chain length
  `n ≤ chainCap = 2^20` and any child proofs `Vb` accepts, not only the benchmark's instances. It is proved for every oracle
  function `H`.
- **Knowledge soundness is one level; the tree is the random-oracle heuristic** (§5.4). You prove
  one level. Valid child proofs must still be extractable from your own log, so a prover cannot
  flatten the tree (§5.3).
- **The native prover is never proved, only checked.** Its proofs are checked by the compiled `Vb`
  at the root, on 16 sampled inner proofs and by the canaries (§6.3 steps 4–7). It need not agree
  with `P` in any way (§3.2, V3-4). `P` itself must be executable, because the liveness check runs
  it (§6.3 step 8).
- **Fresh random leaf starts defeat precomputation.** The starts come from `os.urandom` per
  evaluation, the digests depend on them, and `setup` sees no instance (§6.3 steps 1–2, §6.7).
  Every leaf's chain of `2^14` hashes is proved inside the timed run.
- **The field is yours; the machine has carry-less multiply and no GPU.** The contract has no field
  (V3-1). The reference machine exposes `pclmulqdq`, `vpclmulqdq` and `gfni` (Zbc on RISC-V) so that
  binary fields are not disadvantaged, and it has no GPU (§6.4). The organiser's library field is
  CompPoly's `BF64`/`Ext3` (§7.4), and using it is optional.
- **The oracle is tagged.** `Submission.Vb` answers your queries with `blake2sDigest (tagRO :: q)`,
  and the relation hashes under `tagChain`, `tagLeaf` and `tagNode` (§3.4). The four tags are
  distinct first bytes, so no chain, leaf or node preimage is an oracle input; the relation hashes
  oracle inputs only inside `Vb`, in the node clause, which is the recursion itself
  (`Relation.lean`). Your native prover must use the same tagged oracle.
- **The extractor must run, not only exist.** `img` must compute `E` within `fuel t ≤ B t` steps
  on the contract machine for every input (§4.4), and the harness checks it on honest logs (§6.3
  step 8).
- **Verifier queries are counted.** `qV ≤ 2^16` is a theorem about every run (§3.1), and the error
  bound charges them: `(Q + qV) · ε` (§4.5).

## 14. Where to read more

- `docs/README.md`: the index of the documentation and the reading order.
- `docs/design/DESIGN-v3.md`: the design. Read §1, §2, §4 and §6 first; §8 is the trust statement.
- `docs/baseline/BASELINE-TASK.md`: the brief for the baseline entry.
- `docs/baseline/v2-example/README.md`: a worked example of a submitter's obligations (v2).
- `docs/reference/neighbouring-competitions.md`: ots.golf, sig.golf, the Proximity Prize and
  leanerVM, which these rules follow.

## 15. Known issues (filed on the core)

Rules known to be problematic, filed on https://github.com/scaraven/recursion.fast/issues. Until a
fix lands at the pin, the rule above is what is checked.

- **#5.** `KS` at `errorCap` (`Bounded` over unbounded logs, one bad set per answer) may be
  unsatisfiable for Merkle/BCS verifiers; a potential-form amendment is proposed.
- **#6.** The succinctness cap `T_V = 2 s` and board T's incentives with respect to recursion.
- **#7.** Node extraction as decoding, and the size of `extractorBudget` for recursive extractors.
- **#8.** Honest recursion under the v3 caps (`proofCap`, perfect completeness over every `H`,
  BLAKE2s-only hashing).
- **#9.** Minor rules and hygiene: completeness through a fallback branch, repeated runs, this
  file's drift from the contract (corrected here), gate rule 4's field list, the trust
  statement, `Fintype Digest`, the allowlist, compiled field speed.
- **#10.** The library's witness-sending verifier accepts malleated leaf proofs (the §6.3 canaries),
  and the contract's `packBytes`/`bytesAt` compile to quadratic code.

**The honest-baseline work** in `docs/snark-baseline/` targets the proposed amendment of #5 (the
core branch `v3/ks-potential`), not the contract at the pin.
