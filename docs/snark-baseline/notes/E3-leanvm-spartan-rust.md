# E3: leanVM, Spartan, the Rust ecosystem, and R1CS sizes

Exploration notes for the honest recursive SNARK baseline (native prover plus a compiled Lean
verifier `V`, `T_V = 2 s` at the root, proof ≤ 1 MiB, oracle `H(q) = blake2s256(0x52 ‖ q)`).
Sources read: leanVM at `/home/devops/leanEthereum/leanVM` (HEAD `a386121f`), its paper
`doc/leanvm/main.tex` and all of `body/*.tex`, `python-verifier/verifier.py`, `crates/`; the
Spartan primer (https://hackmd.io/@srinathsetty/spartan); `docs/snarks/spartan.pdf` (Setty,
"BinarySpartan: Spartan over binary fields", 13 pp.). Every timing below is a measurement on
this VM, with its log under `logs/probes/`. **The VM was shared during the runs (load average 21
on 32 cores), so treat absolute timings as upper bounds.**

## 0. Headline findings

1. **leanVM is already our design, in Rust, over our exact fields.** It is a binary-field,
   BLAKE2s-based, hash-only SNARK with recursion. `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
   `E = K[y]/(y^3+y+1)` (`doc/leanvm/body/02-vm-specification.tex`), which are CompPoly's `BF64`
   and `Ext3` (DESIGN-v3 §7.4). The PCS is WHIR/Ligerito with ring switching. BLAKE2s
   compressions are proven by **Flock**, which is Spartan over binary fields: a SIMD R1CS,
   a zerocheck (the outer sumcheck) and a lincheck (the inner sumcheck). The README's
   `hash_chain.rs` test proves exactly our leaf shape: an unrolled BLAKE2s hash chain.
   The `koalabear` branch (`origin/koalabear`, `15946578`) holds the old KoalaBear/Poseidon
   version. `main` has no KoalaBear or Poseidon2 left.
2. **This VM has no `pclmulqdq`, `vpclmulqdq` or `gfni`.** `/proc/cpuinfo` reports
   `QEMU Virtual CPU version 2.5+`, with flags `avx2 avx512f/dq/cd/bw/vl bmi2 aes`. leanVM's
   GF(2^64) multiplication therefore falls back to a naive 64-iteration carry-less loop
   (`crates/primitives/src/field/gf2_64x3.rs:415`). Measured here:
   - leanVM Flock, 2^14 BLAKE2s compressions (our leaf size): **prove 14.25 s, verify 477 ms,
     1,150 compressions/s** (`logs/probes/flock-2e14.log`). The README reports
     485,033 compressions/s at 2^18 and 1.9 ms verify on an M4 Max.
   - leanVM `fibonacci --n 200000`: 13,640 cycles/s, verify 0.528 s. The README reports
     5.3 M cycles/s and 2.9 ms on an M4 Max.
   - Micro-benchmark (`logs/probes/fieldbench.log`, source `logs/probes/fieldbench-main.rs`),
     time per multiplication:

     | Multiplication | ns per mul |
     |---|---|
     | GF(2^64), naive loop (leanVM's fallback) | 22–25 |
     | GF(2^64), integer-multiply "holes" carry-less product | 23–27 |
     | GF(2^64) by a fixed scalar, 8×256 tables | 4.2–6.7 |
     | Goldilocks, scalar | 3.6–5.5 |
     | KoalaBear, scalar (p3) | 5.8–9.7 |
     | KoalaBear, AVX2 packed, 8 lanes (p3) | **0.71** |

   Native BLAKE2s: 124 ns per 33-byte hash serially, 46 ns per hash with `hash_many` SIMD. One
   leaf chain `chainEnd(s, 2^14)` takes 2.1 ms.

   **Consequence.** A binary-field prover on this machine needs one of two things. Either it
   rewrites the multiplication hot paths to multiply by a fixed scalar through tables (folding
   by a challenge, NTT twiddles and eq tables are almost all scalar×vector), or it accepts
   roughly 25× slower field arithmetic than a prime field with SIMD. The verifier is affected
   too: leanVM's own Rust verifier takes about 0.5 s here, and a Lean `V` built on
   `BitVec 128` carry-less products (CompPoly `BF64/Reduce.lean`) will be slower still. That is
   a real `T_V` risk to measure early.
3. **The R1CS sizes are known.** One BLAKE2s compression costs about **15.9 k Boolean
   constraints over GF(2)** (Flock: 2^14 block) and **21,518 constraints over a prime field**
   (bellman). Recursion per node costs about **18.4 k compressions**, measured by leanVM for a
   2→1 step, which is about **2^28 Boolean constraints**. The leaf is 2^14 × 2^14 = 2^28.
   Both are the same order. Details are in §4.
4. **The oracle's one-byte tag breaks leanVM's one-compression framing.** leanVM hashes
   64-byte Merkle nodes and 64-byte transcript blocks in one compression each.
   `0x52 ‖ left ‖ right` is 65 bytes, which is **2 compressions** and doubles in-circuit Merkle
   cost. Keep every oracle input at 63 bytes or less. One way is 31-byte (248-bit) digests in
   Merkle nodes and the transcript state, giving `1 + 31 + 31 = 63` bytes per node. Another
   is a transcript block of `tag + 32-byte state + 24-byte E element + 1 ds byte = 58` bytes.

## 1. leanVM

### 1.1 Paper (`doc/leanvm/main.tex`, 1,789 lines including `body/`)

- **Primitives (§3, `03-proving-primitives.tex`).**
  - `eq(X,Y) = Π(1+X_i+Y_i)` in characteristic 2.
  - Sumcheck (degree d, κ rounds, error dκ/|E|) and zerocheck (`Σ P(x) eq(r,x) = 0`).
  - The partially fixed zerocheck lemma [DT24].
  - Gruen's savings: a round message of degree D costs D elements, and a zerocheck round on a
    degree-d cofactor costs d elements.
  - The inner-product PCS abstraction: claims `⟨W, g⟩ = c` with an MLE-friendly weight `W`.
- **Committing the witness (§4).**
  - Every column is *stacked* into one multilinear `q`, largest first. A claim on column `P_i`
    becomes a claim on `q` with a selector suffix.
  - All claims are batched by powers of one challenge λ into one opening.
  - The Flock bit-witness is packed 64 bits per K element by **ring switching** (Annex A).
- **End-to-end (§8).** The Fiat–Shamir initial state is seeded by the public input, the
  bytecode and Flock's R1CS matrices. The protocol then runs:
  1. Commit to the stack: one WHIR Merkle root, no out-of-domain sample, so the PCS is only
     list-binding.
  2. Bus: one batched **GKR** grand product over the push, pull and count trees (memory and
     bytecode multiset checks).
  3. One batched table sumcheck. Its summand has degree 3, so a round costs 3 E elements.
  4. A public-input line check.
  5. Flock for BLAKE2s.
  6. Ring switching.
  7. One stacked WHIR opening that discharges every pooled claim.

  §8.4 "Fiat Shamir instantiation" is `TODO` in the paper. The real transcript is in
  `crates/fiat_shamir` and `python-verifier`:
  - state `= compress(IV, public_input)`, where `compress` is BLAKE2s-256 of 64 bytes;
  - `observe(e) = compress(state, (e.c0, e.c1, e.c2, DS_OBSERVE))`;
  - `sample() = compress(state, (0, 0, 0, DS_SQUEEZE))`, taking the first 3 words as an E element;
  - proof-of-work grinding through `DS_POW_*`;
  - Merkle leaf hash `blake2s(leaf bytes)` and node hash `blake2s(left ‖ right)`.
- **Recursion (§9).** A node verifies `n_rec` child proofs of the *same bytecode* (the
  recursion is self-referential). Two large fixed multilinears are **deferred**, not evaluated
  in-circuit: the bytecode MLE and Flock's matrices `Ã0, B̃0` (28 variables, about 89 M nonzeros).
  - Each child carries its deferred claims. The node batches the 2·n_rec claims per polynomial
    with two sumchecks (28 cheap rounds for the matrices), so the statement stays constant-size.
  - Only the root verifier pays the native evaluations: a circuit walk of 30,594 field
    multiplications for the matrices.
  - The public input is a 32-byte BLAKE2s digest of: the environment digest, the signer digest,
    the deferred bytecode point and value, and the deferred matrix point and values.
- **Annex A, ring switching (175 lines).** It turns 64 claims `s_i = Q̃_i(r)` on bit
  multilinears into one weighted claim on the packed `q_flock`:
  - a random F2-linear map `Φ` (a Frobenius sum with restricted support);
  - the target `T = Σ x^i Φ(s_i)`;
  - the weight `W(u) = Φ(eq(r,u))`;
  - soundness error about 2^-160.
- **Annex B, PCS (414 lines).** WHIR = Ligerito over binary Reed–Solomon codes.
  - Encoding is the additive NTT in the novel polynomial basis [LCH14], at
    `½ κ n` multiplications.
  - Column weights `W_x` are MLE-friendly in `O(κ)`, so the verifier never encodes.
  - Each level does: batch with λ, ℓ_i sumcheck rounds of degree 2, commit the folded oracle,
    an OOD sample (not at level 0), and t_i queries that become consistency claims. The last
    level is sent in the clear.
  - Round-by-round soundness is proven in the Johnson list-decoding regime, using
    [BCHKS25]'s mutual correlated agreement (MCA).
  - Parameters (`python-verifier/verifier.py` 900–910): initial fold 6, then fold 4,
    domain-reduction factors 3 then 1, residual ≤ 2^5 values, 17 query-grinding bits, stack
    sizes 2^15 to 2^28.
  - Query table `WHIR_QUERIES`. At log-inv-rate 2 and a 2^22 stack:
    `(112, 45, 28, 21, 16)`. At rate 1/2: `(225, 56, 32, 23, 17)`.
  - Leaf trick: hash the zero padding first and reuse the BLAKE2s state.
- **Annex C, Flock (284 lines).** This is the BLAKE2s proof.
  - The R1CS block has 2^14 bits, with `A = I ⊗ A0`, `B = I ⊗ B0`, `C = I`, and a constant-one
    position at 512.
  - Committed wires: 896 free inputs, the constant, 256 output ⊕ wires, and 14,720 ∧ wires
    (the product bits of 320 modular additions). Linear wires are substituted away.
  - Zerocheck with a univariate skip over the first 6 variables: the prover sends 64 coset
    values, then runs n_flock quadratic rounds.
  - Lincheck with 8 rounds over a single block, using the block-diagonal fold. The prover sends
    64 `s_i`. The verifier's terminal check needs `Σ A0(k,j) e_row(k) w_col(j)`, computed by a
    forward walk of the circuit in O(circuit). In recursion this check is a hint, deferred.
  - Soundness error `(4 k_batch + 163)/|E| < 2^-183`.

**Reported performance** (README, M4 Max):

| Run | Proof | Prove | Verify |
|---|---|---|---|
| 2→1 recursion | 206 KiB (log-inv-rate 2) | 0.394 s | 14.6 ms |
| 900-XMSS aggregation | 296 KiB | 0.82 s | — |

In the 2→1 recursion, the verifier program executes 686 k VM cycles:
- `BLAKE2S` 2^14.17 ≈ **18.4 k compressions**;
- `MUL` 2^17.7 ≈ 215 k E multiplications;
- `XOR` 2^17.4 ≈ 172 k additions;
- `DEREF` 2^17.7;
- total committed 2^24.66.

Security target: 128 bits (Johnson LDR, no proximity-gaps conjecture).

### 1.2 Crates (Rust 2024 edition, Apache-2.0/MIT, line counts of `*.rs`)

The workspace is **self-contained**. Its only external dependencies are `serde`, `bincode`,
`libc`, `tracing*`, `rand` (test-only) and `clap`. It does not use rayon: it has its own
`parallel` crate.

| crate | lines | reusable content | ties |
|---|---|---|---|
| `primitives` | 4,999 | `field/gf2_64.rs` (340, `F64` = BF64), `field/gf2_64x3.rs` (1,210, `F192` = Ext3, Karatsuba), `gf2_8.rs`, `hash.rs` (1,343, BLAKE2s `compress`, `hash`, AVX-512 16-lane `hash_many`), `multilinear.rs` (334), `bits.rs` | Fast multiplication only on aarch64 PMULL or x86 `pclmulqdq`; the software fallback is the naive loop |
| `fiat_shamir` | 982 | `lib.rs` (BLAKE2s duplex, PoW), `transcript.rs` (prover and verifier state, proof stream), `merkle.rs` (pruned multi-paths) | Untagged BLAKE2s. Needs the `0x52` tag and a ≤63-byte framing |
| `pcs` | 9,547 | `whir.rs` (2,772), `whir_config.rs` (1,076, soundness and query computation), `ntt/additive_ntt_f64.rs` (1,131), `ring_switch.rs` (1,093), `stack_open.rs` (859), `merkle.rs`, `pack.rs`, `tensor_algebra.rs` | K/E only |
| `flock` | 7,647 | `zerocheck*.rs` (about 3.6 k, univariate skip, multilinear rounds), `lincheck.rs` (1,879), `hash.rs` (1,184, the BLAKE2s circuit plus forward and transpose walks), `witness.rs`, `gf2.rs` | BLAKE2s compression only. Free inputs are unconstrained, so a hash chain needs linking (the leanVM bus, or a `next`-shift constraint) |
| `lean_vm` | 7,540 | `gkr.rs` (559, grand-product GKR), `tables.rs`, `leaf.rs`, `hash_flock.rs` (474) | VM-specific |
| `rec_aggregation` | 4,811 | `aggregation.rs` (3,975, recursion and deferred claims), `hash_chain.rs` (132, **our leaf relation as a VM program**) | Uses the zkDSL compiler (`lean_compiler`, 11,318) |
| `parallel`, `zk_alloc` | 886, 1,247 | Thread pool and topology, arena allocator | Generic |

**What to reuse for a native Spartan-style prover:**
- `primitives::field` and `hash`;
- `pcs` (WHIR, ring switching, stacking, additive NTT);
- `flock` (it *is* Spartan's two sumchecks for SIMD BLAKE2s);
- `fiat_shamir`, retagged.

Before reuse: replace the naive `clmul64` and add table-based scalar×vector paths, given the
missing `pclmulqdq`.

### 1.3 `python-verifier/verifier.py` (1,439 lines)

This is a complete, readable verifier of a leanVM execution proof: field `K`/`E`, transcript,
Merkle multi-paths, sumcheck, GKR bus, table sumcheck, WHIR (`verify_whir`, lines 1006–1103),
Flock zerocheck and lincheck including the **BLAKE2s circuit walk** (`blake2s_row_values`, lines
1180–1297), ring switching (`ring_switch`, 1338) and the stacked opening. The proof is two byte
streams: 24-byte E scalars, and Merkle openings. **It is the best template for a Lean
transcription.** The WHIR, Flock, ring-switching and transcript parts are about 700 lines and
are what a Spartan+WHIR `V` needs. The VM-bus and table parts would be dropped.

### 1.4 `formal/`

`formal/xmss`: a Lean project, about 45 k lines, proving 127-bit classical security of leanVM's
XMSS in the ROM. It is not a SNARK verifier and has no reuse here beyond its style: a
`Statement.lean` file a reviewer reads, and an axiom footprint pinned by `#guard_msgs`.

## 2. Spartan: the minimal variant for us

R1CS `Az ∘ Bz = Cz`, `z = (w, 1, x)`, `m = 2^s` rows. The steps are:

1. Commit to `w̃`, the witness MLE.
2. **Outer sumcheck** (s rounds, degree 3; degree 2 per round with Gruen's eq factoring):
   `0 = Σ_x eq(τ,x)·(ã(x) b̃(x) − c̃(x))`. The prover then sends `v_A, v_B, v_C` at `r_x`, and the
   verifier checks `e = eq(τ,r_x)(v_A v_B − v_C)`.
3. **Inner sumcheck** (s rounds, degree 2):
   `v_A + ρ v_B + ρ² v_C = Σ_y (Ã + ρB̃ + ρ²C̃)(r_x, y)·z̃(y)`. It ends at `r_y`.
4. **Opening.** `w̃(r_y[1..])` comes from the PCS. The `(1, x)` part is computed by `V`.
5. **The verifier evaluates `Ã, B̃, C̃(r_x, r_y)`.**
   - *SPARK*: commit to sparse `row/col/val` encodings and prove the evaluation with an
     offline-memory-checking or lookup argument. This is heavy and avoidable.
   - *Uniform/SIMD R1CS* (Phalanx, SuperSpartan, BinarySpartan, Flock): with `A = I ⊗ A0`, the
     verifier evaluates only the per-block matrices, in O(block) time. A circuit walk avoids
     even materialising them (Flock: 30.6 k multiplications for BLAKE2s).

   **BinarySpartan never uses SPARK** (spartan.pdf §2).

Concrete figures from BinarySpartan (spartan.pdf §4):
- F_{2^128}, ring switching with 128 bits per element, Ligerito in the unique-decoding regime
  without grinding, 100-bit security, univariate skip over the first 4 rounds.
- Constraints: BLAKE3 14,000 per compression, SHA-256 30,376, Keccak-f 38,400.
- Throughput: 872 k BLAKE3/s on 12 M4 cores.
- **Proof 519 KiB at 2^14 BLAKE3 hashes** (Flock 357 KiB); paths are not deduplicated, and
  gzip brings it to 422 KiB.
- Verifier 2.7–4.1 ms natively.
- The SuperSpartan `next` MLE links instance t's output to instance t+1's input, which is
  exactly our hash chain. A tail matrix of linear rows pins chosen bits to public values.

**For us**:
- *Leaf* = one uniform SIMD R1CS. There are 2^14 chain compressions linked by `next`, with
  input 0 pinned to `0x43 ‖ s` and the last output fed to one extra compression for
  `0x4C ‖ end ‖ le64(n)` (41 bytes, one compression). The verifier work is the
  two sumchecks, the block-matrix walk and one PCS opening.
- *Node* = the verifier circuit, which is not uniform. Split it into:
  - a SIMD block of BLAKE2s compressions, linked to the glue by a permutation/lookup (bus)
    argument or by structured linear rows;
  - a small K-valued "glue" R1CS of about 1–2 M constraints (§4).

  The glue matrices must have an MLE that `V` evaluates cheaply, or be deferred to the root as
  leanVM does. A generic sparse evaluation of 2^21 nonzeros in compiled Lean is at the edge of
  `T_V`: DESIGN-v3 §6.5 assumes 2^20 field operations take 0.5–2 s.

**PCS choice with hash commitments:**
- **Ligero/tensor** is the simplest: one Merkle tree, one row combination, column queries, and
  `V` re-encodes one row. The proof is O(√N). For N = 2^22 K elements (a leaf, packed), with
  2^8 rows × 2^14 columns, the row combination is 2^14 E = 384 KiB plus about 100–200 queries ×
  2 KiB. That is about 0.6–0.8 MiB, borderline against the 1 MiB cap. In-circuit, each query
  hashes a whole column.
- **Brakedown** is worse on size.
- **Basefold/FRI** are polylog with more queries per level.
- **WHIR/Ligerito** is polylog and has the fewest queries. leanVM measured 206 KiB at rate 1/4.
  It already exists in Rust over exactly K/E (`crates/pcs`), and there is a Python verifier to
  transcribe.

**Recommendation: WHIR as in leanVM.** Ligero is a fallback only for a first non-recursive
step.

## 3. Rust ecosystem on this machine

- Toolchain: `rustc 1.99.0 (2026-09-28)`, `cargo 1.99.0`.
- **crates.io works.** `cargo search` answers, and `cargo fetch` downloaded `blake2s_simd 1`,
  `blake2 0.10`, `rayon 1.12`, `p3-koala-bear 0.3`, `p3-goldilocks 0.3` and `p3-field 0.3`. The
  probe crate is `logs/probes/fieldbench/`. The latest `p3-*` is `0.9.0-rc.2`.
- p3 0.3's AVX-512 packing needs its `nightly-features` flag. AVX2 packing works on stable.
- The local registry cache (`~/.cargo/registry/cache`) had **none** of blake2, rayon, p3, binius,
  arkworks-snark, spartan or ligero before the probe. It held only ark-ff/serialize/std, sha2/3,
  k256 and the like.
- On crates.io, binius exists only as placeholder or reserved crates (`binius-field 0.1.0`
  "Reserved"). Use git for binius64 if wanted.
- leanVM builds offline from the cache with an external target dir:
  `CARGO_TARGET_DIR=... cargo test --release --locked --offline -p flock` built in 34 s. The
  leanVM tree was not modified.

## 4. R1CS sizes

### 4.1 One BLAKE2s compression

10 rounds × 8 G. Each G has 4 rotation-XORs and 6 two-operand 32-bit additions (two of them
add the message word). That is 480 two-operand additions, or 320 when a three-operand addition
counts as one.

| Setting | Count | Source |
|---|---|---|
| GF(2) bits, XOR free, AND = 1 constraint | **15,873 committed wires** (14,720 ∧, 896 inputs, 256 outputs, 1 constant), padded to a **2^14** block; A0 and B0 have about 89 M nonzeros because XOR chains are substituted | leanVM `c-flock-protocol.tex` §C.1, §C.2.4 |
| First principles over GF(2^k) | Carry `c_{i+1} = a_i ⊕ (a_i⊕b_i)(a_i⊕c_i)`: 31 ANDs per two-operand addition, so 480 × 31 = 14,880, plus input booleanity (512 message + 256 cv bits, one `b² = b` each if committed as K elements) | — |
| BLAKE3 (7 rounds) for comparison | 14,000 | spartan.pdf §4 |
| SHA-256 for comparison | 30,376 | spartan.pdf §4 |
| Prime field (bellman `UInt32`; XOR costs 1 constraint per bit, `addmany` ≈ 34 constraints) | **21,518** (one 64-byte block, 512 allocated input bits) | `bellman/src/gadgets/blake2s.rs` test `test_blake2s_constraints` |

The ratio of prime to binary constraint counts is about 1.35×. The commitment cost differs far
more than that. Binary ring switching commits 64 bits per K element, so a leaf of 2^28 bits is
2^22 K elements (32 MiB). A prime field commits each bit as one element: about 2^28.4
KoalaBear elements (1.4 GiB), roughly 45× more data to encode and Merkle-hash.

### 4.2 Hashes in our relation

| Use | Bytes per input | Compressions |
|---|---|---|
| Chain step `0x43 ‖ d` | 33 | 1 |
| Leaf statement | 41 | 1 |
| Node statement `0x4E ‖ c1 ‖ c2` | 65 | **2** |
| Oracle `0x52 ‖ q`, q ≤ 63 bytes | — | 1 |

Leaf circuit: 2^14 + 1 compressions ≈ 2^14 × 2^14 = **2^28 Boolean constraints**, plus the
`next` linking (linear) and the pinning.

### 4.3 Verifier circuit per node (two children)

**Measured anchor.** leanVM's 2→1 recursion executes 18.4 k BLAKE2s compressions, 215 k E
multiplications and 172 k E additions, at log-inv-rate 2 with 17-bit grinding. The other
measured figures are in §1.1.

**First-principles count per child** (WHIR at rate 1/4, 2^22 K-element stack, queries
`(112, 45, 28, 21, 16)`):
- Level 0: 112 × (a 512-byte leaf ≈ 9 compressions with the tag, plus 18 nodes) ≈ 3 k
  compressions with 63-byte nodes, or 5 k with 65-byte nodes.
- Later levels (E leaves of 16 values = 384 bytes, depths 15 to 13): about 1.3 k compressions
  with 63-byte nodes, or 3.9 k with 65-byte nodes.
- The transcript adds a few hundred compressions.
- Per child: about **4.5–9.5 k** compressions. Per node: **9–19 k**. This is consistent with
  leanVM's 18.4 k.

**Boolean cost of the hashes:** 18.4 k × 15.9 k ≈ 2.9·10^8 ≈ **2^28.1** constraints.

**Field arithmetic.** It must be native K constraints (R1CS over K). One E multiplication is 6
K-constraints with Karatsuba, so 215 k E multiplications give ≈ 1.3 M ≈ 2^20.3 constraints.
At bit level the same work is a 64-bit carry-less product of about 729 ANDs (Karatsuba, 3^6), so an
E multiplication is about 4.4 k ANDs and the total is about 2^29.8. **The circuit therefore
mixes a packed bit-witness for the hashes with a K-valued witness for the field arithmetic.**
Packing bits into K is K-linear, `k = Σ x^i b_i`, so the link between them costs nothing in R1CS
over K.

**Totals.** Node ≈ 2^28 hash constraints plus about 2^20–2^21 K-constraints, matched to the
leaf's 2^28. The tree has 256 leaves and 255 nodes, so about **2^37 constraints in total**
(≈ 2^23 compression-equivalents).

**Proof size.** With WHIR at rate 1/4 on a 2^22–2^23 packed stack, expect 200–300 KiB (leanVM:
206 KiB). With rate 1/2: about 300 KiB. Either is well under 1 MiB.

**Root `V` cost** (natively, per proof):
- about 9 k compressions (1.1 ms at 124 ns each);
- about 10^5 E multiplications;
- the Flock-style block walk (30.6 k);
- WHIR column weights.

In Rust on this VM with leanVM's software multiplication, verification takes about 0.5 s
(measured). Compiled Lean with `BitVec 128`-based `BF64` multiplication is the dominant unknown
for `T_V = 2 s`. **Benchmark `BF64.mul` and `Ext3.mul` in compiled Lean first.**

## 5. Implications (inputs for the plan, not decisions)

- **Field.** Binary K/E wins on commitment size (64 bits per element via ring switching) and
  matches the Lean library (`BF64`/`Ext3`) and leanVM's code. On this VM, binary arithmetic is
  about 25× slower per multiplication than AVX2 KoalaBear. Prime fields need about 45× more
  committed data for bit-heavy BLAKE2s.
  - If we stay binary: tables for multiplication by a fixed scalar are about 4× faster than the
    generic multiplication here, and should be used in NTT, folding and eq tables.
  - The Lean side may need its own `BF64.mul` performance work, or a `UInt64`-based kernel
    proven equal to CompPoly's.
- **Leaf.** Take Flock's SIMD BLAKE2s prover and add the `next` linking.
- **Node.** Take WHIR + ring-switching verification as a K-valued glue circuit, plus a batch of
  Flock compressions with a linking argument. Defer the block-matrix and glue-matrix evaluations
  to the root, as leanVM does, or keep the glue tiny.
- **Tagging.** Design every oracle input at 63 bytes or less, so it costs one compression.

## Logs

- `logs/probes/flock-2e14.log`: leanVM Flock, 2^14 compressions on this VM.
- `logs/probes/fieldbench.log` and `logs/probes/fieldbench-main.rs`: field and BLAKE2s
  micro-benchmarks.
- The leanVM fibonacci figure (13,640 cycles/s, verify 0.528 s) was read from the terminal and
  not logged. Re-run with
  `leanvm --repeat 1 --cooldown 0 fibonacci --n 200000` if it is needed.
