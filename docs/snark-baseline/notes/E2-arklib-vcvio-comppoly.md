# E2: ArkLib, VCVio and CompPoly at the pin, for an honest Spartan-style baseline

Survey for a Spartan-style entry (R1CS, sumcheck, a multilinear PCS from Merkle trees, Fiat–Shamir in
the ROM) over CompPoly's `BF64` / `Ext3`. Read-only exploration. Every axiom claim below is a
`#print axioms` result in `logs/probes/e2/build.log` (scratch workspace `logs/probes/e2ws/`) or
in the `.contract` probe `logs/probes/e2/ProbeCompPoly.lean`. Every timing is from
`logs/probes/e2/bfbench.log`.

Package roots below: `$P = /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages`.

## 0. Pins (checked)

| package | `$P/<dir>` HEAD | manifest pin | match |
|---|---|---|---|
| CompPoly | `572f997` (2026-09-29, "Mersenne31 circle group", #310) | `572f9973…` | yes |
| Arklib | `7653a90` (2026-09-26, "sumcheck: honest messages from CompPoly polynomials", #1243) | `7653a901…` | yes |
| VCVio | `a4232d0` (2026-09-29, "normalize query counts across PolyFun trace representations") | `a4232d08…` | yes |
| PolyFun | `41d3b21` | `41d3b21d…` | yes |
| mathlib | `d13f23b` (v4.34.1) | `d13f23b7…` | yes |

**The shared tree is only partly built.** The shared tree has oleans for 46 ArkLib modules, 119
VCVio/ToMathlib modules, 65 CompPoly modules (the BF64 closure, `Multilinear.Basic`, the
`Univariate` core and `Multivariate`) and 26 PolyFun modules. Nothing under ArkLib's sumcheck
`Interaction`, `CodingTheory`, `Spartan`, or VCVio's `MerkleTree` is built there. To probe those
modules without writing to the read-only tree, I built them in `logs/probes/e2ws/`. That workspace
symlinks mathlib and the other prebuilt packages, and copies Arklib, VCVio, CompPoly, PolyFun and
cslib. `lake build Mathlib --no-build` reported "All targets up-to-date (8923 jobs)" there first.
The build of the probe's closure took 2 min 41 s wall on 32 cores (file mtimes of `Probe.lean` and
`build.log`).

## 1. Import policy for entries at the pin

Sources:

- `.contract/scripts/Gate.lean:61-77`, rule 6 and its transitive form `rule6t` (`:476-496`);
- `.contract/scripts/source-rule.py:51,95,284`;
- `AGENTS.md:305-325` (§10) and `:326-355` (§11);
- `docs/core/import-allowlist.txt` (v2: 10,820 modules);
- `docs/design/DESIGN-v3.md:576-589` (§7.4) and `:697-707` (§9.1).

- **Rule.** An entry module may import (directly, and transitively via `rule6t`) only:
  - its own root's modules;
  - modules in `--allowed-imports` FILE, which is **the exact module list** of the import closure
    of the organiser's roots (`Mathlib`, `RecursionFast.Contract`, `RecursionFast.Library`,
    `RecursionFast.Controls`), produced by `gate --closure`;
  - frontend modules (Clean, never on the badge path).

  It is an exact module set, not a prefix list. Separately, the source rule refuses any
  `import Lean…`, `import Qq…` or `import Lake…` line.
- **Contents of the v2 allowlist.** All of Mathlib's closure (8,530 `Mathlib.*`, plus `Init`,
  `Std`, `Lean.*` reached by Mathlib, `Batteries`, `Aesop`, `Qq`, …) and **29 CompPoly modules**:
  the closure of `CompPoly.Fields.Binary.BF64` (`BF64`, `.Basic`, `.Bytes`, `.Ext3`, `.Impl`,
  `.Reduce`, `.BaseCertificate`, `Fields.Binary.Common{,.Arithmetic}`, `Fields.Extension.*`,
  `Data.Bytes.*`, `Data.Classes.*`, `Data.Nat.Bitwise`, `Data.Polynomial.{Frobenius,Rabin,
  RabinCertificate}`, …). It has **no ArkLib, VCVio, PolyFun or cslib module.**
- **v3 status.** No v3 module imports CompPoly yet (`.contract/lakefile.toml` comment; the v3
  Library and Contract import only Mathlib and the vendored Rv64). The v3 allowlist is
  regenerated in S2 (DESIGN-v3 §11 S2, `:765-768`). Per §7.4 it "gains the `BF64` modules and
  their closure". `AGENTS.md:316-320`: "The rest of CompPoly, and ArkLib, VCVio and PolyFun, are
  not in the allowlist." ArkLib/VCVio enter only if an organiser library module imports them
  (the S4 ArkLib bridge, §9.1; O-20). Even then only that module's closure enters.
- **Consequence.**
  - Importable: Mathlib and the BF64/Ext3 closure (after S2's regeneration).
  - Not importable, but copyable into the entry's own root (Apache-2.0, with attribution, and
    subject to the entry's own hard rules): CompPoly multilinear and univariate, and all of
    ArkLib/VCVio/PolyFun.

  Closure sizes outside the v2 allowlist (non-Mathlib), computed by
  `logs/probes/e2/scripts/closure.py`:

  | root module | modules | lines | packages |
  |---|---|---|---|
  | `CompPoly.Multilinear.Basic` | 3 | 1,723 | CompPoly |
  | `CompPoly.Univariate.Lagrange` | 12 | 5,857 | CompPoly |
  | `CompPoly.Univariate.ReedSolomon.GaoCorrectness` | 20 | 8,147 | CompPoly |
  | `CompPoly.Fields.Binary.AdditiveNTT.Executable` | 9 | 5,129 | CompPoly |
  | `ArkLib.ProofSystem.ConstraintSystem.R1CS` | 14 | 5,242 | ArkLib, CompPoly |
  | `ArkLib.Data.MvPolynomial.SchwartzZippelCounting` | 80 | 15,856 | ArkLib, VCVio, ToMathlib, PolyFun, cslib (pulled in via `ArkLib.Data.Probability.Uniform`) |
  | `ArkLib.Data.CodingTheory.ProximityGap.AHIV22` | 102 | 24,702 | ArkLib, VCVio, ToMathlib, PolyFun, cslib |
  | `VCVio.CryptoFoundations.MerkleTree.Extractor` | 107 | 27,470 | VCVio, ToMathlib, PolyFun, cslib |
  | `VCVio.CryptoFoundations.MerkleTree.Extractability` | 158 | 40,660 | VCVio, ToMathlib, PolyFun, cslib |
  | `VCVio.OracleComp.QueryTracking.Birthday` | 127 | 32,388 | VCVio, ToMathlib, PolyFun, cslib |
  | `ArkLib.ProofSystem.Sumcheck.Interaction.ComputableSoundness` | 280 | 83,181 | ArkLib, VCVio, ToMathlib, PolyFun, cslib, CompPoly; 6 files carry `sorry` (unused by the theorem) |

## 2. What the contract asks for (it shapes what is reusable)

`.contract/RecursionFast/Contract/Security.lean`, `Oracle.lean` and `Certificate.lean`:

- `V : Digest → Proof → OProg Bool` and `P` are inductive query programs over one oracle
  `ByteArray → Digest` (256-bit). They are deterministic and compiled; there is no probability
  monad.
- `KS` is **straight-line knowledge soundness in counting form**. The entry supplies:
  - a `KState` with `good`/`bad` on query logs;
  - `final`: every proof accepted on a good log is extracted by `E c π L` from the **log**;
  - `Bounded ε`: at most `ε·2^256` bad answers per (log, fresh query), with `ε ≤ 2^-128`;
  - a verifier query bound `qV ≤ 2^16`;
  - the extractor `E` with a RISC-V image within budget.

  `Complete` is perfect, for every oracle function.
- So the reusable content is mostly **deterministic / counting** facts: the number of roots of a
  low-degree polynomial, Schwartz–Zippel counts, a log-reading Merkle extractor, and code
  distance and decoding. VCVio/ArkLib's probabilistic `Pr[...] ≤ …` statements over `OracleComp`
  do not discharge `KS` directly; DESIGN §9.1 says the bridge runs contract → ArkLib, not back.

## 3. CompPoly (`$P/CompPoly`, 392 `.lean` files)

`sorry`: the only textual hit is `CompPoly/Fields/PrattCertificate.lean`, in comments. There is
no `implemented_by`, `extern`, `unsafe def` or `partial def` in `CompPoly/` (grep). Fiat–Shamir,
Flock, hashes and Merkle trees are **absent at `572f997`**: grep for
`fiat|shamir|flock|transcript|sponge|merkle|blake|poseidon` finds only byte-codec and GHASH hits.

### 3.1 BF64 / Ext3 (allowed; in the v2 allowlist closure)

- **Carrier.** `CompPoly/Fields/Binary/BF64/Impl.lean`:
  - `structure BF64 where toBitVec : BitVec 64` (`:58`); `ofBitVec` (`:66`);
  - `Add` = xor (`:112`); `mul` = `reduce (carryLessMul (w := 128) …)` (`:120`);
  - `powTwoPow` (`:334`); `invItohTsujii` (`:348`); `Inv`/`Div` (`:490-498`);
  - computable `CommRing` (`:305`), `Field` (`:513`), `CharP BF64 2` (`:524`);
  - `Finite` only, no `Fintype`, so nothing enumerates the field (`:459`);
  - `equivFin : BF64 ≃ Fin (2^64)` (`:453`).
- **Spec bridge.** `toQuot : BF64 → AdjoinRoot basePoly` (`:130`) with `toQuot_add/mul/…`
  (`:159-`) and `toQuot_injective`/`toQuot_surjective`. The irreducibility certificate is
  `Basic.lean:130` `basePoly_irreducible`.
- **Arithmetic.** `carryLessMul` is a `Fin.foldl` of 64 shift-xors on `BitVec 128`
  (`Common/Arithmetic.lean:78`). `reduce` is two folds by `0x1B` (`Reduce.lean:57,78`).
- **Ext3.** `BF64/Ext3.lean`:
  - `ext3Poly = X^3+X+1` (`:58`), `ext3Poly_irreducible` (`:127`);
  - `abbrev BF64.Ext3 := Ext ext3Params` (`:172`), `ext3Gen` (`:179`);
  - `nat_card_ext3 : Nat.card Ext3 = 2^192` (`:203`).

  Carrier: `Extension/Arithmetic.lean:88` `structure Ext (P) := Vector F P.d`, `mul` (`:201`),
  `mulTbl` (`:318`). The field instance is computable (`Extension/Field.lean:137`).
- **Bytes.** `BF64/Bytes.lean`: `ByteCodec BF64` (little-endian, 8 bytes).
- **Axioms** (`.contract` probe, 28 s wall, 2.6 GB RSS): `BF64.instField`,
  `BF64.mul_invItohTsujii`, `BF64.toQuot_mul`, `BF64.card_bf64`, `BF64.ext3Poly_irreducible` and
  `BF64.nat_card_ext3` each use only `[propext, Classical.choice, Quot.sound]`.
- **Compiled speed** (`logs/probes/e2/bfbench.log`, `lake build bfbench` executable, n = 200,000):

  | operation | per op |
  |---|---|
  | `BF64` mul+add | **29.7 µs** |
  | `Ext3` mul+add | **415 µs** |
  | `BF64` inverse (Itoh–Tsujii) | **1.72 ms** |
  | unverified UInt64 loop clmul + reduce (bit-at-a-time, 64 iterations) | 1.47 µs |

  The unverified loop agreed with `BF64.mul` on 1,000 random pairs. That is a test, not a proof.
  `BitVec 64/128` compiles to `Nat` (bignum) arithmetic, which explains the gap. This agrees with
  O-9 (v2 `K.mul` ≈ 27 µs).

  **Consequence:** a Spartan prover doing about 10^6–10^7 field multiplications over `BF64` at the
  pin needs 30–300 s. In `Ext3` it needs about 14× more per multiplication. An entry that wants
  speed needs its own `UInt64`-word carrier (no `extern` is allowed). It would prove
  `toBitVec (fastMul a b) = (BF64.mul ⟨a⟩ ⟨b⟩).toBitVec` once (bit-level), or prove field laws for
  the fast carrier directly. CompPoly's benchmark doc
  (`docs/wiki/benchmark-best-times.md:240-255`) shows CompPoly's `Tower` fields reach a 298 ns
  `GF(2^128)` multiply and 16 ns table `GF(2^64)` multiplies (`Fields/Binary/Tower/Fast*.lean`).
  Those use a different (tower) basis and are not in the allowlist.

### 3.2 Multilinear polynomials (not allowed; copy: 3 modules, 1,723 lines)

- `CompPoly/Multilinear/Basic.lean`. Imports: Mathlib MvPolynomial, `Data.List.Lemmas`,
  `Data.Vector.Basic` and `Data.Nat.Bitwise`; only the last is in the allowlist.
  - Types: `CMlPolynomial R n := Vector R (2^n)` (monomial basis, `:39`) and
    `CMlPolynomialEval R n` (hypercube evaluations, `:47`), both little-endian.
  - Evaluation: `evalMle` (`:561`), `evalMleLayer` (fold one variable, `:537`), `eval` (Lagrange
    dot product, `:586`).
  - The eq polynomial: `eqTilde w x` (`:605`) with `eqTilde_eq_prod` (`:662`) and
    `eqTilde_append` (`:694`); `lagrangeBasis` (`:472`).
  - Theorems: `eval_mle_eq_eval` (`:648`), `evalMle_succ` (`:574`).
  - Basis change: `monoToLagrange`/`lagrangeToMono` (`:771,808`) and
    `equivMonomialLagrangeRepr` (`:1130`).
  - `Multilinear/Equiv.lean` bridges to `MvPolynomial` (`toMvPolynomial_is_multilinear`, `:92`).
  - Axioms of `eval_mle_eq_eval`, `eqTilde_eq_prod` and `evalMle`: standard 3 (`.contract` probe).
- `Multilinear/ManyEval/Basic.lean:38,92`: `evalManyMle` and `evalManyMleByLayers` (batch
  evaluation at one point).
- ArkLib adds `ArkLib/ToCompPoly/Multilinear/Basic.lean:56`
  `eval_eq_MvPolynomial_MLE` (CompPoly table eval = `MvPolynomial.MLE` eval). Its axioms were not
  probed.

### 3.3 Univariate, Reed–Solomon, NTT (not allowed; copyable)

- `CPolynomial R` (canonical array, `Univariate/Basic.lean:59`), `eval`/`evalHorner` (`:261,278`).
  Lagrange `interpolate` (`Lagrange.lean:195`), `Barycentric.lean`, `BatchEval/`,
  `EuclideanAlgorithm.lean` (`xgcd` with early stop).
- **Reed–Solomon** (`Univariate/ReedSolomon.lean:38,54,78`): `Domain F` (a nodup array),
  `messagePoly` and `encode`.
- **Decoding: Gao decoder (unique decoding up to (n−k)/2)**, computable, generic over
  `[Field F] [BEq F] [LawfulBEq F]`, so it works over `BF64`/`Ext3`:
  - `ReedSolomon/GaoDecoder.lean:66` `decode`;
  - `GaoCorrectness.lean:218` `decode_sound`, `:257` `decode_eq_some`, `:322` `decode_eq_none_iff`,
    `:331` `decode_unique`.

  The three theorems probed (`decode_sound`, `decode_unique`, `decode_eq_none_iff`) use the
  standard 3 axioms. The closure is 20 CompPoly modules, 8,147 lines. This is the natural
  straight-line extractor's decoder for a Ligero/RS-based PCS: decode the rows the extractor
  reads from the log.
- **Multiplicative NTT** (`Univariate/NTT`, `NTTFast`) needs roots of unity, so it does not apply
  to `BF64`.
- **Additive NTT** (`Fields/Binary/AdditiveNTT/`):
  - It is generic over `[Field L] [Fintype L] [Algebra 𝔽q L]` with `card 𝔽q = 2` and a linearly
    independent basis `β`. `BF64` has no `Fintype` instance (deliberately); a local one could be
    supplied.
  - `computableAdditiveNTT` (`Executable.lean`) is benchmarked only over tower fields:
    128 → 512 evaluations in 372 ms with the fast variant (`benchmark-best-times.md:271-275`).
  - Not a good fit for the baseline.
- **Guruswami–Sudan / list decoding** (`Bivariate/GuruswamiSudan/…`) exists. It is not needed
  for a unique-decoding baseline.

## 4. ArkLib (`$P/Arklib`, 920 `.lean` files)

Seventy-six files contain the token `sorry` (with comments). The probe results that matter:

| declaration | file:line | axioms |
|---|---|---|
| `Sumcheck.Interaction.Computable.execute_soundness` | `ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean:31` | standard 3 |
| `Sumcheck.Interaction.Computable.execute_perfectCompleteness` | `…/ComputableCompleteness.lean:116` | standard 3 |
| `Sumcheck.Interaction.Native.execute_soundness` | `…/ProtocolSoundness.lean:201` | standard 3 |
| `Sumcheck.Interaction.Native.execute_perfectCompleteness` | `…/ProtocolCompleteness.lean:110` | standard 3 |
| `R1CS.pad_preserves_relation` | `ProofSystem/ConstraintSystem/R1CS.lean:89` | standard 3 |
| `Spartan.Spec.oracleReduction.firstChallenge` | `ProofSystem/Spartan/Basic.lean:240` | **sorryAx** |
| `ProximityToRS.e_le_dist_over_3` (AHIV22 Lemma 4.3/4.4, a counting form) | `Data/CodingTheory/ProximityGap/AHIV22.lean:315` | standard 3 |
| `ProximityToRS.prob_of_bad_pts` (AHIV22 Lemma 4.5) | `AHIV22.lean:343` | standard 3 |
| `ProximityGap.RS_correlatedAgreement_affineLines_uniqueDecodingRegime` | `ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean:33` | standard 3 |
| `ProximityGap.RS_correlatedAgreement_affineLines` (BCIKS20 Thm 1.4, full range) | `…/AffineLines/Main.lean:38` | **sorryAx** (list-decoding branch, `:49`) |
| `BerlekampWelch.decoder_eq_some` | `Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:99` | standard 3 (but `decoder` is **noncomputable**, `:56`) |
| `MvPolynomial.card_zeros_le_of_totalDegree_le` (counting Schwartz–Zippel) | `Data/MvPolynomial/SchwartzZippelCounting.lean:177` | standard 3 |

- **Sumcheck.** The new `Interaction` framework (20 files, `ProofSystem/Sumcheck/Interaction/`) is
  sorry-free for completeness and soundness.
  - Soundness bound: `count·deg/|F|` for a false initial claim, against any native prover
    strategy.
  - It is **interactive, probabilistic** soundness over `OracleComp`/`unifSpec`. It is not RBR
    knowledge soundness, not Fiat–Shamir, and not counting form.
  - `Computable.*` runs the verifier on CompPoly coefficient arrays with Horner evaluation
    (`Impl/Representation.lean:28`). The honest prover (`Impl/Projection.lean:65`
    `projectedRoundPolynomial`) **enumerates the summation domain**, with no running-time claim.
  - Its closure carries `Sumcheck/Spec/SingleRound.lean` (13 non-comment `sorry`), unused by these
    theorems.
  - Reuse value for the contract: low. The per-round fact the entry needs (a nonzero degree-≤d
    univariate has ≤ d roots) is Mathlib's `Polynomial.card_roots'`. The multivariate counting
    form is Mathlib's `MvPolynomial.schwartz_zippel_sup_sum` (which ArkLib's counting lemma wraps).
- **Spartan.** `ProofSystem/Spartan/Basic.lean`:
  - It is a PIOP skeleton with `sorry` at `:245,333,364,376`; the two sumchecks and the final
    check are commented out (`:279,395,411`). **Not usable.**
  - `R1CS.lean` is a clean relation spec: `Size`, `relation` (`:64`), `pad`, `pad_preserves_relation`.
    It uses Mathlib `Matrix`, so it is noncomputable-friendly but fine as a spec.
- **BCS / Fiat–Shamir.**
  - `OracleReduction/BCS/Basic.lean` is commented out (`:63,82`).
  - `OracleReduction/FiatShamir/Basic.lean:173` (completeness) is `sorry`.
  - The DuplexSponge security files have 17 `sorry`s.
  - `OracleReduction/Security/StateRestoration.lean` holds definitions only (`:35-156`).
  - The FS/BCS theorems DESIGN §9.2 cites are in the unmerged chain #1267–#1283 and on ArkLib HEAD
    `db7005f`, **not at the pin**.
- **Proximity gaps / IOPs.**
  - AHIV22 (Ligero) Lemmas 4.3–4.5 are sorry-free (above).
  - BCIKS20 is sorry-free only in the unique-decoding regime.
  - Not sorry-free, by non-comment `sorry` count:
    - FRI `Spec/SingleRound` (4);
    - BatchedFri (6);
    - Binius BinaryBasefold (23);
    - FRIBinius (9);
    - RingSwitching (18);
    - STIR (4).

    The Binius #383 port is in progress (§9.4).
  - There is no Ligero/Brakedown/Basefold/WHIR **protocol** at the pin; only the coding lemmas.
  - Reed–Solomon (`Data/CodingTheory/ReedSolomon.lean:65` `code`) is a `Submodule` spec
    (noncomputable).
- **Merkle trees in ArkLib:** none of its own (it uses VCVio's).

## 5. VCVio (`$P/VCVio`)

- **`prEvent_randomOracle_le_of_bad_queries` is NOT at the pin.** It is introduced by `d606eab`
  (2026-10-03, #823, `VCVio/OracleComp/QueryTracking/RandomOracle/FreshQuery.lean:517`).
  `git merge-base --is-ancestor d606eab a4232d0` fails, and the pin has no `FreshQuery.lean`
  (`RandomOracle/` has Basic, DeferredSampling, Eager, EagerTable, ProbeEps, Programming,
  Routing, Simulation, Wiring). This is O-20.
- **Merkle trees** (`VCVio/CryptoFoundations/MerkleTree/`, 52 files, 14,108 lines). The textual
  grep finds **no `sorry`**. Probed:

  | declaration | file:line | axioms |
  |---|---|---|
  | `MerkleTreeExtractability.extractability_rom_bound` | `Extractability.lean:591` | standard 3 |
  | `…extractability_rom_bound_birthday_dominates` | `:694` | standard 3 |
  | `InductiveMerkleTree.extractability_rom_bound` | `Inductive/Extractability.lean:150` | standard 3 |
  | `InductiveMerkleTree.getPutativeRootWithHash_binding` | `Inductive/Binding.lean:148` | `[propext]` only |
  | `MerkleTreeExtractability.fresh_extractedTarget_of_extractor_disagreement` | `ExtractionKernel.lean:249` | standard 3 |

  - **The deterministic pieces are the useful ones.**
    - `MerkleTreeExtractor.tree view s log root` (`Extractor.lean:94`) reconstructs the tree
      from a query log, with `targets` (`:100`) and `ResponseInjectiveOn` (`:111`). This is the
      shape of the contract's `E c π L`.
    - `ExtractionKernel.lean:249`: with a collision-free cache, an accepted authentication chain
      that disagrees with the reconstructed tree contains a later query whose answer is one of
      the reconstructed labels. Each such fresh answer is a "bad" event over at most
      #targets/2^256 of the answers, i.e. the contract's `bad` predicate.
    - `Inductive/Binding.lean:148,192` (`getPutativeRootWithHash_binding{,_collision}`,
      `findCollision`, `:77`) is pure collision extraction.
    - `Inductive/Defs.lean:99,130,165` (`buildMerkleTreeWithHash`, `generateProof`,
      `getPutativeRootWithHash`) are pure computable functions over an explicit hash.
  - The probabilistic bounds (`extractability_rom_bound…`) are over `OracleComp` with lazily
    sampled caches. They do not plug into `KS`.
  - The trees are typed (`Skeleton`, `FullData`), not `ByteArray`. The entry must re-encode
    them against `OProg`/`Log` and BLAKE2s-style `ByteArray` queries.
- **Birthday / collision.** `OracleComp/QueryTracking/Birthday.lean:224,268,470-524`
  (`probEvent_logCollision_le_birthday_total`: standard 3). `Collision.lean`. All probabilistic.
- **Fiat–Shamir in VCVio.** VCVio has `CryptoFoundations/FiatShamir/` (`Sigma`, `WithAbort`, `QueryBounds`: Σ-protocol FS) and
  `ReplayFork.lean`. These are not relevant to a BCS-style NARG.

## 6. Other in-house assets (not packages)

- **The core's v2 tree at tag `v2-archive`** (`git -C .contract show v2-archive:<path>`):
  - `legacy/v2/RecursionFast/Library/Compile.lean` (926 lines, no `sorry`). It is a full
    **Merkle (arity 2–16) + Fiat–Shamir compiler** over the v2 field `K` (= `BF64`), byte tapes
    and a 32-byte hash, with:
    - completeness: `narg_complete`, `narg_complete_of_perfect`, `prove_isSome`;
    - `NARG_eq_true_iff`;
    - `narg_local`, the deterministic core of BCS soundness;
    - Merkle path correctness: `climb_pathOf`, `verifyPath_pathOf`.

    It has **no soundness theorem** ("binding … is not a Lean statement").
  - `Controls/CompileFS.lean`.
  - `probes/s9/feasibility/compiled-bench/` (measured `K.mul` ≈ 27 µs, O-9).

  These are the closest existing code to the transcript and Merkle layer the entry needs, and
  they are Mathlib-only.
- `.contract/RecursionFast/Library/WitnessSending.lean` (the S2 baseline) is the template for the
  `Submission`, `KState` and certificate plumbing.

## 7. Cost and fit per candidate

| asset | sorry-free | computable | allowed to import | closure beyond allowlist | verdict |
|---|---|---|---|---|---|
| CompPoly `BF64`, `Ext3` | yes (probed) | yes, but slow (29.7 µs / 415 µs per mul) | **yes** (after S2 regen) | 0 | use as the spec field; consider a verified `UInt64` fast path |
| CompPoly `Multilinear.Basic` (`evalMle`, `eqTilde`, `lagrangeBasis`) | yes (probed) | yes | no | 3 modules / 1.7k lines | copy into the entry root |
| CompPoly Gao RS decoder + correctness | yes (probed) | yes, generic field | no | 20 / 8.1k | copy if the PCS is RS/Ligero-based (straight-line extraction by decoding) |
| CompPoly Lagrange/`CPolynomial`/`xgcd` | yes (grep) | yes | no | 12 / 5.9k | comes with Gao |
| Mathlib `Polynomial.card_roots'`, `MvPolynomial.schwartz_zippel_sup_sum` / `schwartz_zippel_totalDegree` (`Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean:72,192`) | yes | n/a (proofs) | **yes** | 0 | the sumcheck and eq-check counting facts |
| ArkLib AHIV22 Lemmas 4.3–4.5 | yes (probed) | proofs only | no | 102 / 24.7k (VCVio/PolyFun probability layer) | copy the counting core (`e_le_dist_over_3_strong`, the affine-line count) for a Ligero-style proximity test |
| ArkLib BCIKS20 unique-decoding correlated agreement | yes (probed) | proofs only | no | large | optional, for an FRI-style test |
| ArkLib sumcheck `Interaction` | yes (probed) | verifier yes; prover enumerates | no | 280 / 83k | reference only; restate in counting form |
| ArkLib Spartan | **no** (`sorryAx`) | — | no | — | do not use |
| ArkLib BCS / FS / state restoration | **no** / commented out / definitions only | — | no | — | not at the pin |
| ArkLib FRI / Binius / RingSwitching / STIR | **no** | — | no | — | not at the pin |
| VCVio Merkle extractor + extraction kernel + binding | yes (probed) | pure functions | no | 107–158 modules / 27–41k | copy or adapt the deterministic kernel; re-encode to `OProg`/`Log` |
| VCVio `prEvent_randomOracle_le_of_bad_queries` | — | — | — | — | **absent at the pin** (`d606eab`, O-20) |
| v2 `Library/Compile.lean` (Merkle+FS NARG, completeness) | yes (0 `sorry`) | yes | entry may copy (Mathlib-only) | 0 | the best starting point for the transcript, Merkle and tape layer |
