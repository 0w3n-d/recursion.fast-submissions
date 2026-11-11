# leanvm-inspired

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #7

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, a logup bus,
ring switching and stacked WHIR. It is reshaped for the contract in three ways: unique decoding, a
hash-chain transcript over the signed oracle, and an in-circuit verifier written as loop tables
instead of a VM guest. From #7 it takes the core library's `WitnessSending` relation, unchanged: that
relation is the right leaf of every node and the completeness route.

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`) and `E = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`);
  `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding.
- P20 is the production parameter set and P8 the test set.
- [e] marks an estimate.

## Changes since pr11-983bdcfa21d6

pr11-983bdcfa21d6 was accepted on the evaluation machine: S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s,
g 1.19), mean |π| 1,180,192 B. This version changes the chain link, the prover and the native verifier. The kinds, the
fields, the commitments, Fiat–Shamir, the extractor, the claim and the theorem's statement are unchanged.

- **The chain link is gated by `n`, so the prover's work grows with `n`.** In pr11 the chain table proved 2^20
  Keccak-f rows for every `n`, and steps took 12–14 s at every `n` (dev VM).
  - The dead rows `i ≥ n` hold the zero input, and the link `in_{i+1} = Pad43(Y_i)` is only asserted on the live
    rows (`i + 1 < n`). With `m = n − 1`, the shift sumcheck's kernels carry the masks `[1 ≤ k ≤ m]` and `[k < m]`,
    its target is `C·lt̃_m(ρ)`, and the 17 constant-lane claims are `c_l·lt̃_n(ρ')`. `V` evaluates every mask
    extension in closed form from `m`'s bits (`LvmMask`, `LvmMaskF`).
  - The prover runs the GKR on the written prefix with leanVM's padding block, and sums the dead rows in closed form.
  - The child's verifier circuit checks the gated link with a closed-form gadget (`n ≤ 2^20` from the child's
    header) and a borrow chain over `n`'s 20 bits. `chain_of_CH` needs the link only on the live rows.
  - Re-frozen record: P20 (22, 1, 17, **4,253**), 88 groups (pr11: 4,199, 84). `|π|` grows by 1,296 B to
    **1,181,488 B**; `qS` 11,832 is unchanged.
- **Prover levers** (proof bytes unchanged by each): the node program is built before `ready`; the chain and sponge
  walks use the vendored AVX-512 Keccak-f; the chain walk, the sponge walk and the recursion tables overlap; the
  group tables are built on 4 threads; the LoopIR table writer resolves each column once per piece.
- **Faster `V`:** fast twins in `LvmVFast`, each proved equal to the code it replaces, ending in `VS20F_eq` as before:
  group leaves computed once per (piece, column) with an array MLE; cached BITS address columns; a closed form for
  the sponge link's shift term; bus values computed directly from the static key polynomials, without building a
  `Form` (`decideProgB_eq`, `busFinalV_agree`). On pr11's proofs this alone took `V` from 505 to 264 ms per check.
- **Measured, local season shape** (dev VM, 8 pinned CPUs, caps unchanged, one run): **ACCEPT**, S = **8.76**
  (P̄ 6.05, V̄ 2.71), S× = **6.46** at the local `v_ref` (1,068 ms); mean `V` **275.5 ms** (median 272 ms); steps
  4.9–11.7 s, step 1 9.7 s; fit `P(n) = 4.34 + 7.60·n/2^20` s; prover peak 7.67 GiB. pr11 on the same harness:
  S = 16.21 (P̄ 12.76, V̄ 3.45), S× = 15.74, mean `V` 506 ms.
- **Expected on the evaluation machine [e]:** pr11's evaluation-to-local ratios (P̄ 0.54, `V` 0.57) give P̄ ≈ 3.3 s
  and mean `V` ≈ 0.16 s, so S ≈ 5.9 and S× ≈ 3.5. The ratio for P̄ may be worse now: pr11's step was mostly the GKR,
  which Zen 4's GFNI/VPCLMULQDQ tiers speed up most, and the fixed, oracle-bound commit is now a larger share. At a
  ratio of 0.7, P̄ ≈ 4.2 s, S ≈ 6.8 and S× ≈ 4.4.
- **Also in the root:** `LvmTapeRel` and `LvmWire*`, not imported by `Solution`, and generic-shape statements added
  to `LvmKeccak{Start,Gkr,Candidate}` (imported; their earlier statements are unchanged). They are sorry-free work
  towards a later version.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission` with `submission = subG staticOkB VS20F`
  (`LvmFinCert.certificateFin`). It uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no `native_decide` and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`,
  `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP: leanVM's doom certificates, plus luck, plus the self-fold accumulator (A23).
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`.
  - The node relation from the tables: chain, sponge, WOTS, and the child's `acc` through `loopir_sound`,
    `qlink_sound`, `qsig_sound` and `harith_core`/`harith20`.
  - The native `V` refines the compiled IOP verifier (`refines_VSL`, `VS20F_eq`).
  - The extractor's output and cost (`computesX` at the declared fuel).
- **Discharged by kernel `decide` at the frozen record.** These are facts about the concrete program `Q`
  and its tables:
  - `fitsR`, the table shapes and the `chkB` checks (`chkFit_P20`, 23.7 s of kernel);
  - the 23 layout and input-map fields (`LvmQAsmFacts*`);
  - the cell bounds of the position fields (`posCellsB_P20`, 15.6 s);
  - the positions and lanes of every phase (`harNum20`, `okAG/BG/CG_P20`, `okN_P20`, `okE_P20`, `posLanesR20/M20`, `hbs20`).
- **Checked when V runs: the A24 guard.** Five static facts are not kernel-decidable within the caps:
  - no computed-address read in `Q_arith`;
  - `Q.wf`;
  - grouping and injectivity of the table pieces;
  - well-formedness of the claim lists.

  The table builder's `List.mergeSort` is well-founded recursion and gets stuck in the kernel. A
  structural sort is OOM-killed at 12 GB. So these facts are one closed `Bool`, `staticOkB`.
  - The submitted verifier is `if staticOkB then VS20F else reject every 'S' proof`.
  - The certificate case-splits on `staticOkB` without evaluating it. In the `true` branch,
    `staticFacts` gives the facts, and the full proof applies. In the `false` branch, the `S` branch
    accepts nothing, and KS holds trivially (`certificateR_reject`, εFS ≤ 2^-139).
  - **Soundness therefore holds for either value.** Only completeness of the native prover depends on
    `staticOkB = true`. The compiled V evaluates it once per process (1.5 s), and it is `true` at P20:
    every e2e run and badge check accepts.
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness,
  not proved complete.
- **Soundness error.**
  - Model (`params.py`): 2^-129.08. The dominant term is WHIR level 0's 311 positions; the table below
    has every group.
  - Lean: `εFS = ε + εB + hash ≤ 2^-129 + 2^-130 + 2^-139 ≤ 2^-128` (`kcertS`, `εFS_le_of`). Inside ε:
    WHIR folds ≤ 2^-147 and positions ≤ 2^-129 per group.
  - The hash term covers collisions, state repeats and 32-byte window hits at any offset of any query.

### Construction

**Tree shape: one SNARK per step.** Every output is `nodeStmt c_L (leafStmt h n)`.
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`. `(s, n, h, σ_leaf)` are in
  the clear; `V` checks `σ_leaf` natively, and the SNARK proves `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`. It is committed, and it is verified in the
  circuit.

A flag `b` selects leaf mode (`b = 0`, step 1's first proof) or node mode. There is one shape and one
schedule, so every proof has the same size and makes the same queries. The chain table always has
2^20 rows; the rows `i ≥ n` hold the zero input, so the prover's work grows with `n`. `traceDigest []` is constant, so one `σ_leaf` (one SIGN) serves the whole stream, and one
WOTS walk per proof remains. A `W` proof never starts with `'S'` (`encode_first_byte`), so `V`
dispatches on `π[0]`.

**Chain table `CH` (2^20 rows: `in[25]`, `mid[25]`, `Y[4]`).**
- `Y = Keccak-f(in)` is proved by leanVM's GKR (RMFE χ, two 12-round segments, all 25 output lanes bound
  first).
- The link `in_{i+1} = Pad43(Y_i)` is the block `0x43 ‖ Y_i`, so lane `j` is
  `(D_j << 8) | (D_{j−1} >> 56)`. That is not `K`-linear: multiplying by `x^8` reduces modulo the field
  polynomial and carries nothing into the next word.
- So the link is proved bitwise: a 20-round shift sumcheck (non-cyclic kernel, closed form), two
  ring-switched bit-slice claims, and 17 constant-lane word claims.
- The link is gated: with `m = n − 1`, the shift sumcheck's kernels are masked to the live rows (`[1 ≤ k ≤ m]`,
  `[k < m]`, target `C·lt̃_m(ρ)`), and the constant-lane claims are `c_l·lt̃_n(ρ')`. `V` evaluates the masks in
  closed form from `m`'s bits; the prover sums the dead rows in closed form.
- The boundaries are `in_0 = Pad43(s)` and `Y(n−1) = h`, and `chain_of_CH` gives `chainEnd s n = h`.

**Sponge table `KS` (2^15 rows).** The same GKR, with a word-linear sponge link. It holds the child's
trace sponge (its message lanes are `C_rec`'s stream columns), one WOTS walk (399 + 32 + 16 rows) and the
child's statement hashes. Six `BITS` tables decompose words for the unaligned prefixes, the WOTS
digits, the positions and the range checks.

**Two commitments.**
- `C_main`: 2^26 `K` words, never decoded.
- `C_rec`: 2^19 words, holding the child's trace as 17 lane columns plus `σ'`. It is the only thing `Ex`
  decodes.

Decoding `C_main` would cost 2^52.6 `K` products, against a fuel cap of `2^48 + 2^16·t`.

**Stacked WHIR, UD regime.** The radius is `(1 − ρ)/2`, the list size is 1, and there is no OOD sample and
no grinding.
- `C_main`: folds 6/4/4/4, rates 1/2 to 1/16, 311/191/156/142 queries, caps 2^8/2^7, final 2^8.
- `C_rec`: one level (fold 6, rate 1/4, 191 queries), final 2^13 `E` scalars in the clear.

UD is what makes the extractor cheap. `Ex` folds `C_rec`'s word, finds the agreement set against
`Enc(final)`, interpolates the 64 rows on 2^13 agreeing positions (barycentric, with shared weights) and
back-substitutes into the novel basis. That costs 2^37.95 steps; the proved total is
`2^39 + ≈ 2.55 k·t`. The proximity side is a new UD mutual-correlated-agreement lemma (Berlekamp–Welch
by counting), plugged into leanVM's one-variable-per-round WHIR soundness.

**Fiat–Shamir is a hash chain over the contract oracle.**
- `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`.
- Each FS query is `st ‖ pending messages` and yields `st'`. The challenge is lanes 0–2 of `st'`; a
  positions query yields 8 positions.
- Merkle leaves (512 B or 384 B) and nodes (64 B) are queries, and paths stop at the cap.
- There are no tags: query classes are told apart by length, and the trace is lane-aligned, so the
  circuit reads it as `K` words.

**Verifier circuit: LoopIR, not a VM guest.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier
on the child's trace:
- `Q_link`: the trace follows the schedule. FS states chain, nodes hold the previous answer, paths end at
  the absorbed cap, and positions are the answer's bits. Answers are read, never hashed.
- `Q_sig`: the WOTS walk to `vk`, and the child's header and statement.
- `Q_arith`: `V_S`'s accept bit. It covers the bus GKR, table sumcheck, accumulator fold, both Keccak GKRs
  and links, four ring switches, every claim, and both WHIR openings.

Blocks are row templates over loop dimensions with affine addresses `A·g^{Σ s_d j_d}`, so `V` evaluates a
block's fixed columns in closed form. Rows of one shape are grouped into power-of-two tables. Every
operand is a read on leanVM's `g`-power memory bus (logup with counts, a grand-product GKR, one table
sumcheck). `loopir_sound` is generic: table constraints, a balanced bus and nonzero counts imply that
the committed cells are `interp Q`'s cells and its assertions hold. Assertions are gated by `b`.

**The recursion fixed point: a self-fold accumulator (A23).** A recursive verifier must check the
fixed-column claims of its own program. Two alternatives fail:
- Evaluating them in the circuit (self-evaluation) needs ≥ 1.5–2.5 M extra words.
- Plain deferral, where the parent folds the child's claims, has no sound fold challenge. The child's
  trace is adversarial (KS is for every `vk`), and the parent's transcript comes after the commitment.

So every `S` proof folds its incoming accumulator `acc_in = (pt ∈ E^28, y)` with its own fixed claims in
its own transcript:
1. draw `κ ∈ E^11` and set `y_own = Σ_k eq(κ, k)·v_fix[k]`;
2. read a degree-28 line polynomial `h` with `h(0) = acc_in.y` and `h(1) = y_own`;
3. draw `t` and set `acc_out = (line(t), h(t))`.

`V` checks only `Φ̃(acc_out.pt) = acc_out.y` natively, in one sweep over the fixed columns. The parent's
circuit (`Q_acc`, 53 k words) recomputes the child's `acc_out` deterministically from the child's trace
and asserts that it equals the parent's `acc_in`, which is in the header and the seed. The new escapes
are ≤ 2^-192 per `κ_j` and ≤ 28/|E| for `t`, so ε is unchanged. One `Φ` serves every proof, and the
program need not be a fixed point of itself.

**Native `V`.** Direct functional Lean on `UInt64` field kernels proved equal to CompPoly. It does not
interpret `Q`: `harith_core` proves that `Q_arith`'s rows imply `decideCore` and the accumulator equation.
The compiled `VS20F` shares the header-independent table parts across checks and is proved equal to the
specified `VS20` (`VS20F_eq`).

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E`; Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck; ring switching; stacked WHIR | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine; Johnson MCA; OOD; grinding | UD; hash-chain FS; Merkle through the oracle with caps; two commitments; LoopIR; bitwise chain link; accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR minus Johnson (≈ 120 modules / 31 k lines, ported to 4.34.1) | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with a UD threshold, `listMax = 1` |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers (`prover/src/lv/PATCHES.md`) |
| leanerVM | bus `lookup_sound`, generator facts | ArkLib-typed PIOP layers | — |
| earlier Flock-class entry | field kernels; extractor DSL, log index, sort, lookup, FS scan (≈ 9 k lines); barycentric decoder; `mca_ud_line`; Keccak sponge layer; W/S dispatch; oracle client, format, asm pipeline | PIOP, layout, Ligerito proofs; BLAKE2s circuits | decoding over `K` rows in the novel basis |
| organiser library | `WitnessSending`, `KState`/`KS`, fast Keccak and signature twins | — | — |

## Result

**Harness.**

| run | result |
|---|---|
| pr11-983bdcfa21d6, evaluation machine | ACCEPT; S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s, g 1.19) |
| pr11-983bdcfa21d6, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 16.21 (P̄ 12.76, V̄ 3.45), S× = 15.74, mean V 0.506 s; `build_s` 683 s, comparator 444 s |
| this version, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46, mean V 0.276 s; `build_s` 662 s, comparator 513 s (cap 600); axioms `propext`, `Classical.choice`, `Quot.sound` |
| this version, evaluation machine | from this PR's evaluation (projected S ≈ 5.9–6.8, S× ≈ 3.5–4.4) |
| `prover setup` variant on Zen 4 | v4 expected (cpuid); the dev VM runs v4p |

**Frozen P20 record** (busDepth, leafdec, rounds, evals) = (22, 1, 17, 4,253).

| quantity | value |
|---|---|
| `|π|` | **1,181,488 B** |
| `qS` | **11,832** (`qV` 16,384) |
| trace | 250,206 lanes (0.898 of `C_rec`'s capacity) |
| signed file | 3,187,927 B (cap 64 MiB) |
| tables | 88 groups, 4,253 evaluations, **6.83 M committed words** (`C_main`'s free region is 7.34 M) |
| `Q` words | 5.90 M |

**Prover, dev VM.** QEMU, 8 threads, shared host. Its cpuid hides PCLMULQDQ, but the instruction executes;
VPCLMULQDQ and GFNI do not, so the evaluation variant v4 cannot start there. The runs use the dev variant
v4p (AVX-512 + PCLMUL) and the shipped binary with the embedded program blob. The P8 and P20 streams
(b = 0; b = 1 over b' = 0 and over b' = 1, including children with n = 1, 2^17 + 1 and 2^20) are accepted by the
Lean `V_S`, and tampered links (n ± 1, the shift round, the slice claims) are rejected.
- Local season shape: step 1 **9.7 s**; later steps **4.9–11.7 s**; a fit over the stream gives
  `P(n) ≈ 4.3 + 7.6·n/2^20` s.
- Peak RSS: **7.67 GiB** (cap 11).
- In pr11 the steps took 12–14 s whatever `n`, of which the CH GKR was 8.6–9.1 s; it now scales with `n`. The fixed
  part (≈ 4.3 s) is mostly the 2^26 commitment, bound by the oracle.
- Zen 4 [e]: the GFNI/VPCLMULQDQ tiers make the GKR 2–3× faster.

**Verifier**, measured on the dev VM (one core):
- **275.5 ms per check** (harness mean, local season shape; median 272, p10 258, p90 299 ms). pr11: 506 ms.
- Start-up is not charged; it is 10.7–11.4 s per process on the loaded dev VM (`staticOkB`, shared table parts,
  caches).

**Score.** pr11-983bdcfa21d6 scored S = 10.17 and S× = 8.19 on the evaluation machine, against #7's S = 105.9 and
S× = 505.8.

**Error budget (model, P20, per fresh query, log₂).**

| group | bound |
|---|---|
| sumcheck rounds / Keccak GKR step 2 (degree 46) | −190.4 / −186.5 |
| bus fingerprint and grand product / ring switching per challenge | −171.0 / −192.0 |
| WHIR λ batching / stacked-claim batching | −183.7 / −182.4 |
| WHIR folds (main 0–3, rec) | −168.4, −172, −175, −178, −174.4 |
| WHIR positions (main 0–3, rec) | −129.08, −129.51, −129.49, −129.58, −129.51 |
| gated link round, slot round | −191 |
| accumulator `κ_j` / `t` | −192 / −187 |
| extractor luck / hash | −174.4 / −151.4 |
| **worst + luck + hash** | **−129.08** |

**Extractor.** `fuel = 2^46 + 8192·t`; the decode's fixed cost (≤ 2^38 steps) is 2^8 below `fuel_base`.

**Lean.** 481 flat modules, ≈ 142 k lines; `Solution`'s import closure holds 452 of them. The heaviest decide module is
`LvmQAsmFactsDec` (47 s, 5.4 GB). In v1, comparator time was cut from 705 s to 462 s on the dev VM by proof-only changes
(`rfl`-lemma `simp` replays, one-pass checkers).

## What failed, and why

- **leanVM's extractor.**
  - Guruswami–Sudan list decoding has a proved cost of ≤ 2^81 + …, and its cone is 443 modules /
    133 k lines.
  - Even at multiplicity 1 (Berlekamp–Welch), 64 lanes × 2^55 = 2^61 is about 2^12 over the
    `2^48 + 2^16·t` cap.
  - Hence UD, which doubles the proof bytes (about +0.9 on `S`).
  - ArkLib's Johnson MCA closure (300 modules / 80 k lines) is off the import allowlist anyway.
- **Witness-sending nodes over SNARK leaves.** Each leaf is ≥ 0.75 MB of `(π, tr)`, so the 64 MiB cap
  breaks near step 85 (step 30 in UD), and the mean `|π|` of ≈ 36 MB gives `S ≥ 60`. Recursion is
  necessary.
- **Step 1 as one SNARK over two chains.** That needs a 2^27 commitment (≈ 14.6 GiB), more than 11 GiB.
- **leanVM's VM guest as the circuit.** Guest correctness is 300 k+ lines of proofs, and a 2^20 chain is
  2^27–2^28 cycles, past `MAX_MU = 28`. A flat gate list fails too: `V` would evaluate fixed columns of
  ≥ 2^20 rows.
- **The `0x43` byte shift** is not `K`-linear (see Idea). It is proved bitwise, with ring switching, and
  the BITS tables handle the small unaligned prefixes.
- **The in-circuit self-evaluation** of fixed columns needs ≥ 1.5–2.5 M extra words: 1,160 columns,
  25 k loop terms and 56 k BITS monomials. **Plain deferral** to the parent has no sound fold challenge.
  Both were replaced by the self-fold accumulator (A23).
- **`C_rec`'s direct final check** cost ≥ 3.28 M words. It was dropped; ε and `Ex` are unchanged, since
  WHIR's final-level check has the same postcondition.
- **Ungrouped tables** would send 9,806 evaluations instead of 440. The final count is still 4,253
  (24 B each in `π`), mostly from BITS (2,975).
- **The assembler fixpoint** (record ↦ program ↦ record) oscillated between 76 and 81 groups once
  `Q_arith` was complete. Padding `Q` to the record made it converge (P20 +16 k words).
- **Kernel-deciding the whole program.** `mergeSort` is well-founded recursion, and a structural sort is
  OOM-killed at 12 GB. This is why A24 exists. Cheaper decide forms cut the rest from 42 to 13 s (`SLokF`
  16.1 → 1.2 s; per-block position lanes 20.1 → 6.5 s).
- **The extractor's FS replay by query prefix** was unsound: abandoned branches share prefixes. The replay
  now uses exact full queries.
- **Two statement bugs found while proving.** A WHIR phase's doom did not imply residual consistency; it
  was fixed with a joined residual doom. `ext_eq` as an equality is false outside `Ex`'s domain (an entry
  of ≥ 2^64 bytes); it became `(∃ w, Ex = some w ∧ Rel) ∨ Ex = S.Ex`.
- **Lean 4.35 → 4.34.1.** 70 leanVM modules compiled unchanged. Three failed on pin drift: ArkLib's
  Johnson API, the BF64 evaluation drift (CompPoly `572f9973` vs `e28da348`) and `.trans` resolving to
  `Function.trans`.
- **Build time.**
  - An RMFE `decide +kernel` went from 61 s / 8.5 GB to 3–4 s, by checking rows on `ℕ` rather than
    parities in `List Bool`.
  - A `Vector.replicate (2^19)` evaluated by the kernel had cost 78 s.
  - `congr 1` on field terms costs 5–31 s each.
  - Every module pays ≈ 3 CPU-s just to import.
  - Together these cut the clean build from 458 to 386 s and from 918 to 847 s at two stages, and the peak
    from 9.6 to 3.6 GiB.
- **The V target.** V was 0.34 s before `Q_arith` was complete and 0.5 s after: 84 groups, 1,226 fixed
  columns, 4,199 evaluations. The `Φ̃` sweep grew from 65 to 160 ms.
- **Testing v4 without the machine.** LLVM auto-vectorised std's start-up with GFNI, so v4 raises SIGILL
  on the dev VM even for `info`. Under Intel SDE, v4's P8 proof is byte-identical to v2's. `prover setup`
  self-tests each variant against v2's digest and caps the dispatch.

## What to try next

1. **`V` below 275 ms.** `|π|` is now the larger part of `V̄` on the evaluation machine (0.56 of ≈ 0.8 per check [e]).
   - WHIR final claims keyed by their point inside the bus step (10–15 ms [e]).
   - One shared `eq` table per (height, size) within a group (−20–25 ms [e]); leaves for the non-uniform rows.
   - The Keccak GKR checks on arrays; faster Lean Keccak and Merkle paths for the openings.
   - Fewer BITS evaluations: fixed count columns, no `w` column, one address column per class.
2. **Prover speed.**
   - The fixed part of a step (≈ 4.3 s) now dominates at `n` near 2^17, where most of `P̄`'s weight is.
   - The commit is bound by the oracle: 12 M service permutations for the 512 B level-0 leaves.
3. **Smaller proofs.** Openings are ≈ 64 % of `π`:
   - prune Merkle paths, use rate 1/4 at level 0, and add grinding (−16 % queries, plus a completeness
     argument);
   - the Johnson regime halves the proof bytes, but only with an extractor far cheaper than GS.
4. **Fewer guarded facts.** A structural, kernel-friendly table builder would let the kernel decide `wf`,
   grouping and claim well-formedness. That would remove `staticOkB` and 1.5 s of start-up.
5. **Left unapplied.**
   - GKR layers as 8 + 4 loops (−0.27 M words);
   - `Q_link`'s node-half selection as one degree-2 assertion (−0.35 M);
   - `C_rec`'s zero columns as free table space;
   - batching the 17 constant-lane claims and dropping the 5 unused samples;
   - a Rust test verifier;
   - the extractor's 354 s serial build chain.
