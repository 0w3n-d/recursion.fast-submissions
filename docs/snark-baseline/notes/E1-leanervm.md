# E1: leanerVM survey for the SNARK baseline

Surveyed 2026-10-19, read-only. Checkout `/home/devops/Verified-zkEVM/leanerVM` on branch
`docs/protocol-headline-theorems` at `532ebb4` (that is `main` `9595721` plus documentation). The WHIR
and Merkle work sits on unmerged branches: `review/whir-67` (`f8a94a3`) and `review/whir-103` (`8df6e09`).
Line counts are `wc -l`.

## 0. The target, and why most of leanerVM cannot be imported

- **Contract** (`.contract/RecursionFast/Contract/`). `Security.lean:51-78` defines `KState`
  (`good`/`bad` on query logs, with laws `empty`, `step` and `final`). It also defines `Bounded ε`,
  which is `∀ L q, #{a | bad L q a} ≤ ε·|Digest|`, and `KS`, which is a bounded knowledge state plus
  `qV`. `Certificate.lean:47-70` caps `ε ≤ 2^-128` and `qV ≤ 2^16`. The oracle is `ByteArray →
  Digest` (32 bytes, `Oracle.lean`). Completeness is perfect for every oracle function. `E` must be
  computed by a RISC-V image within its budget (`Extractor.lean`).
- **Allowlist** (`AGENTS.md:305-320`). An entry may import Mathlib, the contract and library, and
  only CompPoly's `BF64`/`Ext3` closure (29 CompPoly modules; `docs/core/import-allowlist.txt`).
  **ArkLib, VCVio, PolyFun and the rest of CompPoly** (`Multilinear`, `Univariate`, `Multivariate`)
  **are not allowed.** Every leanerVM protocol module imports one of these, so reuse means copying
  and rewriting.
- leanerVM uses Lean's module system (`module`, `public import`, `@[expose] public section`) and
  tests by `#guard`. Copies should drop the module keywords; tests do not port (the source rule
  refuses elaboration-time code).

## 1. Architecture

- **Layers** (`README.md`, `docs/architecture.md` 578 lines): Parameters (637 lines) → Semantics
  (1523) → Arithmetization (3175) → Protocol (24026). Total 29361 lines in `LeanerVM/`, plus about
  12.8k lines in `tests/`. `scripts/check-layers.sh` enforces the layering, with a "wall" that
  stops protocol modules importing the arithmetization except in the adaptor.
- **Fields** (`Parameters/Field.lean`, 228 lines):
  - `K = GF(2^64)` is CompPoly `BF64` (`x^64+x^4+x^3+x+1`).
  - `E = GF(2^192)` is `BF64.Ext3` (`y^3+y+1`). The ring is characteristic 2.
  - Challenges are in `E`; `card_E : Fintype.card E = 2^192` (`Protocol/Field.lean:96`).
  - This is the **same field library our allowlist admits**. The historical KoalaBear work is on
    the `koalabear` branch of leanVM, and in the private leanth tree (`docs/roadmap/leanth-reuse.md`).
- **Protocol** (`docs/roadmap/protocol-blueprint.md`, 1955 lines; status in `protocol-status.md`,
  681 lines). It is a chain of ArkLib `OracleReduction`s: `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫
  opening`. The pieces:
  - The **commit** sends the stack as an oracle; its query interface is inner products `⟨W,q⟩`
    (`Protocol/Field.lean:101-111`, `ToArkLib/InnerProduct.lean`).
  - The **bus** is a grand-product GKR over fingerprints, not logup: `ToArkLib/GrandProduct.lean`
    (656 lines), `GrandProductSecurity.lean` (550), `GrandProductPoly.lean` (172) and `Bus.lean`
    (1114).
  - The **table sumcheck** is a batched constraint sumcheck (`TableSumcheck.lean`, 567 lines).
  - The **public-input check** is `PublicInput.lean` (985 lines).
  - The **Flock** phase, for Boolean R1CS with `C = I` (the BLAKE2s rows), runs zerocheck,
    lincheck and Frobenius ring switching (`ToArkLib/Flock/`, 4346 lines over 12 files).
  - The **opening** is batching by powers followed by one inner-product query (`Opening.lean`, 216
    lines).
- **PCS.** The deployed scheme is WHIR over binary Reed–Solomon (additive NTT, novel basis) with
  Merkle trees. It is **not built on main.** `review/whir-103` has the encoder
  (`Protocol/NovelBasis.lean`, 543 lines). `review/whir-67` has the Merkle trees, the BLAKE2s byte
  hasher and the WHIR parameters (`ToArkLib/Merkle.lean` 201, `Merkle.lean` 92, `Blake2sHash.lean`
  192, `Parameters/Whir.lean` 219). WHIR itself (`whirOpen`), `McaJohnson` and Layer 11's soundness
  are unwritten.
- **Merkle, BCS and Fiat–Shamir.** None is built, and there is no transcript code. Layer 12
  (`protocol-blueprint.md:1250-1390`) is a specification only: a BLAKE2s Merkle–Damgård chain with
  tags, grinding of 17 bits per WHIR level, `bcsCompile`, `verifyWith` and the random-oracle
  theorems.

## 2. What is executable, proved and assumed

- **Executable.** Every verifier, prover and extractor is kept computable (the convention in
  `tests/README.md`; errors live in types). There is no executable and no runtime benchmark:
  `bench/README.md` measures build time only. The 803 `#guard`s under `tests/` run compiled code at
  build time. Examples are a hand-run plain sumcheck (`tests/LeanerVMTests/Protocol/Sumcheck.lean:88-121`)
  and a tiny Flock honest run. One `E` multiplication costs about 2 ms in the interpreter and an
  inversion about 1 s (`protocol-status.md:507-510`). No protocol-level honest run is evaluated.
- **Proved** (`#print axioms` gives only the three standard axioms):
  - `piop_perfectCompleteness` and `piop_rbrKnowledgeSoundness` (`Protocol/Spine/Compose.lean:211,222`)
    are the composition over an abstract `M3Instance` and a `Phases` bundle, with the named extractor
    `piopExtractor`. `piopExtractedStack_eq` (`:197`) says the extractor returns the committed stack.
  - Instantiated as `leanVm_perfectCompleteness` and `leanVm_rbrKnowledgeSoundness`
    (`Protocol/Piop.lean:80,89`) under `Bus.Conditions I` and `I.d ≤ 2`.
  - The notion is `rbrKnowledgeSoundnessWorstCaseWith`, in the **ideal oracle model**: uniform
    challenges, and the stack an inner-product oracle.
  - `piopError_le` (`Spine/Errors.lean:392`): the total is at most `(2^32+2^31+2^20)/|E|` under
    size hypotheses.
  - The knowledge-soundness append is ported from ArkLib #615 (`ToArkLib/KnowledgeAppend.lean`,
    582 lines).
- **Assumed or open.** The plain reading of round-by-round soundness is ArkLib's
  `rbrKnowledgeSoundness_implies_knowledgeSoundness`, admitted at the pin (`Compose.lean:34-37`).
  The blueprint's interface structures do not exist in code: `McaJohnson`,
  `stateRestoration_of_rbr`, `bcsCompile_stateRestoration`, `chain_*`, `niError`. `BcsSecurity` was
  deleted from the plan (`docs/reviews/protocol-headline-theorems.md:26`). The policy is that a
  missing theorem leaves the headline unstated, never assumed (`blueprint:1361`).
- **sorry and axioms.** `grep -rnw 'sorry|admit|native_decide|axiom'` over `LeanerVM/` and `tests/`
  finds **0**. `scripts/audit-lean.sh` bans them lexically, and `scripts/audit-axioms.lean` admits
  only `propext`, `Classical.choice` and `Quot.sound`. The upstream ArkLib dependencies do carry
  `sorry` (the build warns about `Append/Security.lean:94` and `Sequential/General.lean:411,443`).
  leanerVM consumes none of them; this is checked by the axiom audit.

## 3. Reuse for a minimal Spartan-style argument

The assets are ranked by value against the cost of extracting them.

| Asset | Where | Lines | Dependencies | Reuse cost |
| --- | --- | --- | --- | --- |
| Generic binary Merkle tree: `root`, `path`, `verify`, `verify_path` (completeness), `findCollision` and `collision_of_verify` (binding gives a *computed* collision) | `review/whir-67:LeanerVM/Protocol/ToArkLib/Merkle.lean` | 201 | `Mathlib.Data.Nat.Notation` only; hash abstract | **Trivial**: copy and drop `module`. It fits the contract's straight-line extractor, which can compute the collision from the log. |
| leanVM Merkle instance (leaf image, width checks) | `review/whir-67:…/Protocol/Merkle.lean` | 92 | `Blake2sHash`, which uses leanerVM's `compress` | Low. Re-instantiate over the contract's `blake2sOracle`/`OProg` instead. |
| Fields `K`, `E`, limb view, `card_E` | `Parameters/Field.lean`; `Protocol/Field.lean:96` | 228 | CompPoly `BF64`/`Ext3` (allowlisted) | **Trivial.** |
| Two degree-`d` polynomials agree at ≤ `d` points (`card_filter_evaluate_eq_le`); `Message = Vector F (d+1)`, `evaluate`, `weightedSum` | `ToArkLib/SumcheckRound.lean:82-220` | about 140 | Mathlib `Polynomial.roots` only | **Low.** This is the counting core of every sumcheck "bad challenge" set. |
| Sumcheck bad-set count per round: `card_badChallenge_le`, the `Family` (claim, honest poly, weighted domain, invariant), `Consistent`, `Sound` | `ToArkLib/SumcheckRound.lean:126-343` | about 220 | ArkLib `Component.badChallenge` and `OracleInterface` | Medium. The math (`Family` and its counts) ports; the ArkLib reduction, state-function and append scaffolding (`Component.lean` 318, `KnowledgeAppend.lean` 582, `Schedule.lean` 390) does not. Restate it as the contract's `KState.bad` on the squeeze query. |
| Virtual-polynomial sumcheck: weights per coordinate (plain or `eq`), honest round polynomial by interpolation at `d+1` nodes (char 2 has no `0..d`), final check, wire codec dropping one coefficient (`decodeWire`, `encodeWire`) | `ToArkLib/Sumcheck.lean` | 741 | `SumcheckRound`, CompPoly `Univariate.Lagrange`, `ToCompPoly/{IndividualDegree,WeightedCube}` | Medium–high. Lagrange and the computable polynomial are not allowlisted, so use Mathlib `Lagrange`. Wire codec: low. |
| Multilinear and `eq` utilities: `evalMle_eq_sum`, `sumCube`, `lagrangeBasis_*`, `boolVec`/`boolIndex`, `slice`, `evalMle_split`, `cubeIndex` | `ToCompPoly/Multilinear.lean` | 587 | CompPoly `Multilinear.Basic` (`CMlPolynomialEval`, `lagrangeBasis`, `evalMle`; 1187 lines; not allowlisted) | Medium. Either copy CompPoly `Multilinear/Basic.lean`, which needs `Data.List.Lemmas` and `Data.Vector.Basic` (also not allowlisted), or redo it over `Fin (2^n) → F`. |
| Weighted cube sums, `prodWeight` (`eq` as a product) | `ToCompPoly/WeightedCube.lean` | 176 | `Multilinear` | Low once `Multilinear` is in. |
| Power batching: `card_false_batch_le`, `(k−1)/|F|` | `ToCompPoly/PowerBatching.lean`; `ToArkLib/Batch.lean` | 147 + 90 | Mathlib roots plus `Multilinear` | Low. |
| R1CS: `BlockR1CS` (Boolean `A`, `B`, with `C = I`, walks for `A·z`, `Aᵀ·e`, adjoint identity) | `ToArkLib/Flock/BlockR1CS.lean` | 208 | `Multilinear`, Mathlib | Medium: it is specialised to `C = I` over Boolean matrices, which is not general R1CS. |
| Spartan-like zerocheck (eq-weighted) and **lincheck** (matrix–vector sumcheck with a native terminal walk) | `ToArkLib/Flock/{Zerocheck,Lincheck,Rounds,Tables}.lean`; security in `Flock/Security.lean` (744) | 313 + 184 + 157 + 539 + 744 | ArkLib throughout | High. Use it as a **design template**, since it is structurally Spartan's two sumchecks; the proofs need rewriting. |
| Product-gate circuits over GF(2), builder, 32-bit adders, BLAKE2s compression as R1CS with `blake2s_sound` and `blake2s_complete` (14720 gates) | `ToArkLib/Flock/{Circuit,Builder,Words}.lean`, `Protocol/Blake2sCircuit.lean` | 680 + 287 + 619 + 632 | `BlockR1CS` and `Multilinear` | Medium. **Valuable for recursion**: an R1CS for BLAKE2s compression with soundness proved against `compress`. leanerVM's `compress` is not the contract's `Hash/Blake2s`, so a bridge lemma is needed. |
| Binary RS encoder: novel basis, `encode`, `encode_columnWeight`, `encode_injective`, distance `2^(κ+R)−2^κ+1` | `review/whir-103:LeanerVM/Protocol/NovelBasis.lean` | 543 | `Generator`, `InnerProduct` (ArkLib `OracleInterface`), `BitProductTable` (`Multilinear`) | Medium. It is the only RS code in char 2 here. There is **no decoder** (no Berlekamp–Welch or Guruswami–Sudan); the blueprint plans brute-force subset interpolation for `extract` (`blueprint:1366-1372`). |
| Proximity (MCA up to Johnson) | ArkLib `ReedSolomon.mcaError_affineLine_johnson_le` (consumed only in plan) | about 51k lines in ArkLib `MutualCorrelatedAgreement/` plus `HiddenDerivative/` | ArkLib | **Not extractable.** A baseline should use a unique-decoding argument proved locally. |
| Transcript, Fiat–Shamir, BCS | none (blueprint Layer 12) | 0 | — | Nothing to reuse except the specification text. |
| AIR and CCS | M3 tables in leanISA terms (`Spine/Instance.lean`, `Arithmetization/`) | — | Clean, plus the wall | Not reusable for a generic relation. |

The extraction rule of thumb: anything under `ToCompPoly/` or `ToArkLib/` that is not named
`Security`, `Component`, `KnowledgeAppend`, `Schedule` or `Refutation` is mathematics plus
CompPoly `Multilinear`, and ports once `Multilinear` is replaced. Anything that touches
`OracleReduction`, `Verifier.rbr…`, `ProbComp` or `SampleableType` is ArkLib/VCVio framework and
does not port.

## 4. How leanerVM states the non-interactive bound

This is **only a plan.** It is in `docs/roadmap/protocol-blueprint.md:1250-1390` and
`docs/reviews/protocol-headline-theorems.md`, and nothing is in Lean. The statements:

```text
def roSpec := unifSpec + (List UInt8 →ₒ Vector UInt32 8)
abbrev HashQueryBound (oa) (Q) := oa.IsQueryBoundP (·.isRight) Q          -- coins not charged
theorem stateRestoration_of_rbr …   -- worst-case rbr KS ⇒ state-restoration KS at (Q + rounds)·max_i ε_i
theorem bcsCompile_stateRestoration … -- the Merkle compilation keeps it up to 3(Q² + 1)/2^256;
                                     -- its extractor reads the leaves off the query log
theorem chain_knowledgeSound …      -- leanVM's chain, PoW rounds of `grind i` bits: KS + c·Q²/2^256
theorem chain_randomOracle …        -- a chain of a random 64-byte map is a RO on transcript prefixes
def hashTerm (Q : ℕ) : ℝ≥0 := c * (Q + verifierQueries) ^ 2 / 2^256
theorem niError_le (Q) : niError Q ≤ (Q + rounds) / 2^128 + hashTerm Q
theorem verify_knowledgeSound (prog input) (A : Adversary) (hQ : HashQueryBound A Q) :
    Pr[ok = true ∧ ¬ ∃ s q, s? = some s ∧ q? = some q ∧ M3Holds (leanIsaInstance F prog s) input q
      | runRandom do let (proof, log) ← A.withQueryLog; … extract prog input proof log] ≤ niError Q
```

(`blueprint:1283-1305`.) The headline adds `hRO : Blake2sActsAsRandomOracle … δ` as a hypothesis,
never an axiom (`blueprint:1393-1421`).

**(a) The birthday or collision term.** leanerVM makes it **additive and quadratic**:
`hashTerm Q = c·(Q + verifierQueries)²/2^256`. It counts the verifier's own queries (a recomputed
node is a fresh value) and sits beside the linear `(Q + rounds)·max ε_i` (`blueprint:1331-1338`).
Merkle nodes share one untagged 64-byte domain with the chain, so binding is proved on the one
shared function (`blueprint:1350-1356`). The program-hash collision is dropped because the
statement is fixed (`headline-theorems.md:16`).

**Consequence for us.** The contract has **no additive term**. `KState.Bounded` needs
`#bad(L,q) ≤ ε·2^256` for **every** log `L`. A "fresh answer collides with an earlier answer in
`L`" bad set has `|L|` elements, so it is bounded only for `|L| ≤ 2^128`. The contract's paper
bound `(Q+qV)·ε` (`Security.lean:15-19`) therefore cannot absorb a birthday term naively. Collisions
must either be made irrelevant to `good` (bad only on answers that hit the specific nodes the
extractor relies on) or the contract needs a change, which is a report item for O-xx.

**(b) Query-phase randomness.** In leanerVM one squeeze gives one `E` element (three low words of a
BLAKE2s output; `blueprint:342`). A query round's `t_i` positions are many squeezes after one
absorbed prefix, and the round counts as **one challenge**. Its error is
`2^{-17}·(1−γ_i)^{t_i}`, where the factor `2^{-17}` is the grinding nonce
(`blueprint:1331-1347`). `chain_randomOracle` justifies treating all squeezes after a prefix as one
random-oracle output on that prefix. State restoration then pays `(Q + rounds)` times the
per-challenge maximum. Without grinding the statement certifies about 111 bits (`blueprint:1343-1345`).

**Consequence for us.** The contract charges error per **oracle query**. Errors that multiply
across `k` squeeze queries, `(1−γ)^{t}` split into `k` chunks, cannot be expressed as a per-query
bound of `2^-128`: given earlier chunks in `L`, the last chunk's conditional bad fraction is only
`(1−γ)^{t/k}`. To get `2^-128` from one 32-byte answer, `t·log2 n ≤ 256` and
`(1−δ)^t ≤ 2^-128` must both hold. Under unique decoding (`δ < 1/2`) that is impossible for
`n > 4`. leanerVM's design offers no answer to this; it sidesteps it with per-challenge
round-by-round soundness plus state restoration.

## 5. Build

- Toolchain `leanprover/lean4:v4.34.1`. Mathlib `v4.34.1`, CompPoly `572f997`, ArkLib `7653a90`,
  VCVio `a4232d0`, PolyFun `41d3b21` (`lakefile.toml`, `upstreams.json`). These are **identical to
  our pins**. leanerVM also requires Clean `42fe4b26`.
- `.lake` is built with its own packages (not the shared tree). `timeout 600 lake build --no-build`
  reported "All targets up-to-date (3516 jobs)" in 5.6 s, with ArkLib's `sorry` warnings replayed.
- No full build was run. CI caps the build job at 30 min (`.github/workflows/ci.yml:22`), and
  timing goes to the CI-only `build-timing.yml`.
- Measured single-module elaboration (`lake env lean`, warm):

  | Module | Time | Peak RSS |
  | --- | --- | --- |
  | `ToCompPoly/Multilinear.lean` | 10.6 s | 1.3 GB |
  | `ToArkLib/SumcheckRound.lean` | 7.8 s | 1.8 GB |
  | `ToArkLib/Sumcheck.lean` | 12.0 s | 1.9 GB |

- Recorded in the docs: the test module `LeanerVMTests.Protocol.Sumcheck` takes 157–181 s
  (`docs/reviews/protocol-sumcheck*.md:34-40`), and `Statement` tests 2 min 15 s.
- Another agent was building `.claude/worktrees/lazy-weight` (`timeout 1800 lake build
  LeanerVMTests`) during this survey. It was not touched.
