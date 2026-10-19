# Report: the native Rust prover of `spartan-chain` (BLUEPRINT-R1 §11)

Status: built, tested, measured, 2026-10-19. Nothing is committed. Logs are in
`logs/spartan-chain/rust/` (gitignored); `measure.sh` there reproduces every measurement below.

The code follows the blueprint as revised after the review, with the §14 review response. That
revision changes no byte, as the blueprint itself says, and the KATs confirm it. The only code
change it caused is the zero gates of A4. The measurements were taken with the binary from just
before that change; `machine.txt` records its sha256. The same KAT outputs show that change is
byte-neutral, and its cost is under 640 trivial gates.

## 1. What was built

The crate sits flat in `submissions/spartan-chain/`. `Cargo.toml` has `[[bin]] path = "main.rs"`,
and the modules sit beside the Lean files.

- **No dependencies.** The crate needs no crates.io package: BLAKE2s and the thread pool are
  written here. It builds offline from the root alone, and `Cargo.lock` lists only the crate.
- **Build:**

  ```sh
  CARGO_TARGET_DIR=<outside the root> cargo build --release --offline
  ```

  A clean build took 22.7 s (`build.log`). Never build with the target directory inside the root:
  the root must stay flat.

| file | code lines (non-blank, non-comment; of which tests) | content |
|---|---|---|
| `field.rs` | 345 (55) | `K` and `E`: windowed carry-less product, Karatsuba, squaring, byte codecs, `chE`, and byte tables for products by a fixed scalar (`KTab`, `ETab`) |
| `blake2s.rs` | 165 (29) | BLAKE2s-256 (RFC 7693), streaming; `chainStep`, `leafStmt`, `nodeStmt` and the oracle `H(q) = blake2s256(0x52 ‖ q)` |
| `circuit.rs` | 441 (81) | the leanerVM gadget program run once into an XOR-DAG tape, `chainBlock` (§2.2), the bit trace, the forward walk `A0̃/B0̃` (§2.4.2), the transpose walk, and the `rowOf` bitsets |
| `chain.rs` | 363 (110) | `Shape`, `leafSize`, the witness and the `Az/Bz/Cz` bit tables (§2.3), `pub`, `pub̃`, `S̃`, and the verifier's closed form `M̃ρ(r_x, r_y)` (§2.4) |
| `mle.rs` | 66 | `eq` tables and evaluations, Horner |
| `sumcheck.rs` | 458 | the honest outer, inner and product sumchecks (§3, §4.4), and the slices |
| `ringswitch.rs` | 140 (62) | `Φ` by stages, the `c_k` table, `Φ` as 24 byte tables, `T`, `W̃` (§4.3) |
| `rs.rs` | 131 (31) | the code of §5.1: `κ_i`, the basis tensor at a point, `Enc` at a point, and the additive FFT (LCH14) in the unnormalised basis |
| `transcript.rs` | 100 | Fiat–Shamir (§6), index chunking, Merkle tree, paths, climb (§5.3) |
| `prover.rs` | 153 | `proveLeaf`, byte for byte as §7 |
| `verifier.rs` | 201 | the native `Vb`/`check`/`checkNode`/`leafProg` (§1.2–§1.3, §3–§6), and the canonical node codec |
| `kat.rs` | 102 | the §11.3 dumps |
| `par.rs` | 80 | `std::thread::scope` helpers |
| `main.rs` | 353 (137) | the command-line interface; the round-trip, tree and canary tests |
| total | 3 098 | |

Counts are by `grep -cvE '^\s*(//.*)?$'`. The core's `scripts/loc.py` counts Lean comments only,
so it would count every Rust line as code.

**Commands** (`spartan-chain-prover …`):

- `tree DIR`: DESIGN-v3 §6.3. Reads `DIR/leaves.json` (`{"n": N, "starts": [hex, …]}`, the S2a
  format) and writes `DIR/proofs/L<i>.bin`, `DIR/proofs/N<level>_<j>.bin` and `DIR/root.bin`.
- `node DIR`: reads `child{1,2}.{stmt,proof}` (a statement is 64 hex digits or 32 raw bytes) and
  writes `proof.bin`.
- `prove-leaf START.hex N OUT.bin`: writes one leaf proof and prints its statement.
- `verify STMT.hex PROOF.bin`: the native `Vb`. Exit 0 is accept, 1 reject, 2 usage or IO error.
- `dump-field | dump-circuit | dump-walk | dump-encode | dump-transcript` and `dump-proof DIR`:
  the KAT dumps (§5).
- Diagnostics:
  - `check-leaf`: the leaf branch without the `proofCap` guard, needed for `n > 4096`.
  - `bench-field`.
- Environment:
  - `SPARTAN_VERBOSE=1` prints the timing of each phase; `=2` adds the outer rounds.
  - `SPARTAN_THREADS` bounds the number of threads.

The node encoding is S2a's (`WitnessSending.encode`). The leaf format is §1.1 (80-byte header,
then `π_S`).

### Reuse and provenance

- **Field.** leanVM `crates/primitives/src/field/{gf2_64,gf2_64x3}.rs` (pin `a386121f`, MIT or
  Apache-2.0), used for the conventions: `R64 = 0x1B`, limb order `c0, c1, c2`, Karatsuba. The
  code is fresh, because leanVM's fast path is PMULL or `pclmulqdq`, which this machine lacks.
- **Circuit.** A line-by-line transcription of leanerVM `532ebb4`:
  - `LeanerVM/Protocol/Blake2sCircuit.lean` (`gW`, `roundW`, `initW`, `compressW`, `outRows`);
  - `Protocol/ToArkLib/Flock/Words.lean` (`addCarries`, `majorities`, `rippleCarries`, `sumW`,
    `shiftW`, `add3W`);
  - `Builder.mul`, `ProductCircuit.rowOf` and `trace`.

  leanerVM is itself a transcription of leanVM `crates/flock/src/hash.rs`. Provenance is in the
  module header.
- **Additive FFT.** Structure of leanVM `crates/pcs/src/ntt/additive_ntt_f64.rs`, adapted to the
  unnormalised `W_i`.
- **Ring switching.** Stage order of leanVM `crates/pcs/src/ring_switch.rs`.
- **Written fresh:** sumchecks, Ligero, Merkle, transcript and BLAKE2s.

## 2. Tests (`cargo test --offline`, 21 tests, all pass; `cargo-test.log`)

| test | what it shows |
|---|---|
| `rows_digest_matches_leanervm` | **The circuit is leanerVM's, row for row.** For leanerVM's own `blake2sCircuit`, built by `Circuit::build_variant(false)`, `rowsDigest = 4056851438423586957`. That is the value leanerVM's test `#guard`s (`tests/LeanerVMTests/Protocol/Blake2sCircuit.lean`), and its script computes it from leanVM's Python verifier. The test also checks 14 720 + 256 gates. |
| `trace_computes_chain_step_and_satisfies_rows` | The chain block's trace outputs `chainStep d` at 256…511, every row holds (`Az·Bz = z`), and a flipped output bit violates its row. |
| `transpose_is_adjoint_of_walk` | `Σ_j u(j)·wt(j) = A0̃ + ρB̃0` at random points: the prover's transpose agrees with the verifier's walk. |
| `honest_witness_satisfies_and_wrong_bit_fails` | `Sat` holds for `n = 1, 2, 3`, the tail gives `chainEnd s n`, and one wrong witness bit fails `Sat`. |
| `matrix_formula_matches_definition` | **The §2.4 closed form equals the MLE of the matrices built row by row from the §2.3 definitions** (`n = 1, 2`, dense `2^{16}` tables at random `r_x`, `r_y`, `ρ`). |
| `shift_is_the_boolean_shift` | `S̃(t, t') = [t' + 1 = t]` on the cube, for `κ ≤ 3`. |
| `fft_matches_naive_encoding` | The FFT equals the naive `Enc` (§5.1 tensor at each point) at `(ℓ_k, ℓ_N) = (2,5), (4,7), (7,10)`. |
| `basis_is_the_subspace_basis` | `X_1 = X`, `X_2 = X(X+1)`, `X_3 = X²(X+1)`; a nonzero message has a nonzero codeword. |
| `phi_forms_agree`, `ring_switch_identities` | `Φ` by stages = `Σ c_k a^{2^k}` = the byte-table form. `Φ` with every `f_p = 0` is the identity, and with one `f_p ≠ 0` it is not. L-R3 and L-R4 on a 4-variable instance. |
| `k_mul_matches_naive`, `e_field_laws`, `rfc_vectors`, `shapes_and_sizes` | `K` against a bit-by-bit product, `x^64 = 0x1B`; `y³ = y + 1`, field laws, `a^{2^{192}} = a`; BLAKE2s RFC vectors; the §7 `leafSize` table. |
| `roundtrip_n{1,2,3,16,64}` | `prove → Vb` accepts. One flipped byte (bits 0 and 7) is rejected in each of: the tag, `s`, `n`, `h`, the root, the first and last byte of every §7 field, the first column, the first path, the last byte, and 16 random positions. An appended byte, a removed last byte and a flipped statement bit are rejected. Proving twice gives identical bytes. |
| `n0_leaf` | `n = 0`: an 80-byte proof is accepted, and a flipped `h` is rejected. |
| `smoke_tree_r2_n16` | `tree` at `r = 2`, `n = 16`. Every leaf, both level-1 nodes and the root (575 112 B, as §7) verify. Rejected: appended byte, truncated proof, flipped statement bit, swapped children, a byte flipped deep inside an embedded leaf. `node` reproduces `root.bin`. |

Debug assertions are on in the test profile. The prover then checks `g(0) + g(1) = claim` in every
round of every sumcheck, `Sat` on the tables, the identity between the slices and `z̃(r_y)`, and
`q̃(r'') = Σ_j b_j v_j`.

**Independence of the self-check.** The native verifier shares the field, transcript, Merkle, code
and `Φ` modules with the prover, so a misreading in one of those would pass both. Three checks are
independent:

- the verifier's `M̃ρ` is the closed form, while the prover's tables come from the transpose walk,
  and both are tested against the row-by-row definition;
- `rowsDigest` ties the circuit to leanerVM and leanVM;
- the FFT is tested against the naive `Enc`.

For the rest, the oracle is the Lean known-answer test (§5).

## 3. Measurements

Machine (`machine.txt`):

- QEMU Virtual CPU, 32 vCPUs, 62 GiB RAM, Linux 7.0.0-38;
- no `pclmulqdq`, `vpclmulqdq` or `gfni`;
- shared with other agents: load average 3.8–16 during the runs, recorded in each log;
- rustc 1.99.0.

Field (`bench-field.log`):

| operation | time |
|---|---|
| `K` product | 17.5 ns |
| `E` product, dependent chain | 66 ns |
| `E` product by a fixed scalar (`ETab`) | 35 ns |

Leaf proving, 3 runs each, all threads (`leaf-n16.log`, `leaf-n1024.log`, `leaf-n16384.log`):

| `n` | proof size | prove wall (3 runs) | peak RSS | native verify | queries |
|---|---|---|---|---|---|
| 16 | 143 711 B (= §7) | 0.18, 0.19, 0.18 s | 8 MB | 0.084–0.103 s | 3 533 (= §6.3) |
| 1 024 | 457 843 B (= §7) | 0.71, 0.71, 0.70 s | 255 MB | 0.39–0.42 s | 4 414 |
| 16 384 | 1 464 107 B (= §7; above `proofCap`) | 7.61, 7.43, 7.98 s | 3.95 GB | 0.81–0.84 s (`check-leaf`; `Vb` rejects on size) | 5 156 (= §6.3) |

- **Where the time goes at `n = 2^14`:**

  | phase | time |
  |---|---|
  | outer sumcheck | 4.4 s |
  | inner sumcheck | 1.5 s |
  | encode | 0.5 s |
  | witness | 0.4 s |
  | ring switching | 0.4 s |
  | Merkle tree | 0.1 s |

  It uses about 2 200 % CPU.
- **Native verify is single-threaded.** At `n ≥ 1024` the `Enc(ū)_c`, `Enc(v)_c` checks at 260
  columns dominate (`7k` `K`-products per column).

The `r = 2`, `n = 16` smoke tree (`tree-r2-n16.log`):

- `tree` took 0.72–0.76 s wall (four leaves proved one after another);
- the root is 575 112 B;
- the native root `Vb` accepted in 0.17–0.20 s. The statement was computed independently with
  Python `hashlib`;
- `node` reproduces `root.bin`;
- the truncated and appended canaries are rejected.

## 4. Interpretations chosen (the Lean side must match these bytes)

Every point below is fixed by the code and by the KAT dumps. "No byte effect" means that the
choice cannot change a proof.

- **A1. Row 512 is removed from `A0`, `B0`** (§2.3, §2.4.2; the review's BP-m5). The walk and the
  transpose skip position 512. Region 0's row 512 is `(pub(0), pub(0), w(t,512))` exactly.
  **Byte effect:** this decides the inner sumcheck's table. The `dump-walk` file gives both
  variants: row 512 skipped first, then `rowOf` literal with row 512.
- **A2. Sumcheck check** `g(0) + g(1) = c_0 + Σ_{i≥0} c_i = c_1 + … + c_d` (BP-m4). No byte effect.
- **A3. Column openings "in index order"** (§7 field 9) means the order in which the 260 indices
  are squeezed (`c_0 … c_259`), repetitions included. They are not sorted. The Lean
  `SpartanChainLigero.prove2`/`verify2` already read it this way. **Byte effect.**
- **A4. `chainBlock`'s gates** follow the revised §2.2.1 (BP-M3, option (a)).
  - The order is: one gate per constant position in ascending position (`(var 512, var 512)` for
    a 1 bit, `(0, 0)` for a 0 bit), then the 14 720 compression gates at 1280…15999, then the
    256 output rows.
  - Neither `rowOf` nor the trace depends on that order or on the zero gates.
  - The KATs were identical before and after the zero gates were added. No byte effect.
- **A5. `n` that is not a power of two.** Padding blocks `t ∈ [n, 2^κ)` continue the chain (block
  `t` hashes `chainEnd s t`). The wiring rows cover every `t < 2^κ`, and the tail reads block
  `n − 1`. `n = 3` is tested.
- **A6. The packed witness `q`** is the bit vector `w` read as little-endian 64-bit words:
  - `q(u')` is word `u'`, and bit `i` of the word is `w(i + 64u')`;
  - `Q[i][j] = q(j + k·i)`;
  - a column is `U[0][c] ‖ … ‖ U[m−1][c]`, each 8 bytes little-endian.
- **A7. Variable order.**
  - `x` and `y`: index `= k + 2^{14}·t + 2^{14+κ}·top`; `r_x[0..14)` binds `k`.
  - `r_u = r_y[0..14+κ)`, with `r_lo = r_u[0..6)` and `r_hi = r_u[6..14+κ)`.
  - Ring-switch sumcheck: the `8+κ` variables of `u'` in bit order. `r''_lo = r''[0..ℓ_k)` is the
    column variables and `r''_hi = r''[ℓ_k..)` the row variables.
- **A8. Index chunking.** `cnt = ⌊256/ℓ_N⌋` indices per answer and `⌈260/cnt⌉` answers; index `i`
  is the little-endian integer of bits `[i·ℓ_N, (i+1)·ℓ_N)`. That is 13 answers at `ℓ_N = 12`
  (BP-m6: the §6.1 parenthesis is wrong; §6.3's totals are right).
- **A9. Query count reported by the native verifier** = seed + absorbs + squeezes + `260·(1 + ℓ_N)`
  Merkle queries. It matches §6.3: 3 533 at `n = 16` and 5 156 at `n = 2^14`.
- **A10. Node decoding** is a strict parse:
  - both child lengths at most `proofCap` (as `decodeWit`);
  - zero padding;
  - nothing after the second child.

  It is equivalent to `decode` followed by the canonical `encode … = π` check. It is linear, as
  BP-M4 asks of the Lean side.
- **A11. Leaf checks, in order:** `π.size ≥ 80`, then `n ≤ chainCap`, then `size = leafSize n`,
  then `c = leafStmt h n`, then `n = 0 ⇒ h = s`. Only accept or reject is observable; the order
  does not change the bytes.
- **A12. `Φ` stage order** is `p = 0` first (`M_0 = 32`). `T = Σ_i Φ(s_i)·x^i`, with `x^i` the `K`
  word `1 << i`.

None of the review's findings (BP-M1…M4, m1…m14) changes a protocol byte. M1–M3 are about the Lean
proofs, and M4 is the Lean decoder's cost. Where they touch the prover (m4, m5, m6), this code
already agrees with the corrected reading.

## 5. Known-answer formats (§11.3)

The Rust side writes these files and the Lean `spartan-run dump-*` must write the same text.
Reference outputs are in `logs/spartan-chain/rust/kat/`.

**Inputs.**

- `katRand tag i = blake2s256("spartan-chain-kat/" ‖ tag ‖ 0x00 ‖ enc64 i)`, with plain BLAKE2s.
- A `K` input is bytes 0..8 of it, as a little-endian word. An `E` input is `chE` of it (bytes
  0..24).

**Hex conventions.**

- A `K` value is 16 lowercase hex digits of the word, most significant digit first (`%016x`).
- An `E` value is `c0.c1.c2`, each in the `K` format.
- Byte strings are lowercase hex, two digits per byte, in byte order.

**The files.**

- **`dump-field`** (2 000 lines).
  - Lines `kmul i a b a·b a² bytes(a)`, for `i < 1000` with `a = K(katRand "field-k-a" i)` and
    `b = K(katRand "field-k-b" i)`.
  - Then lines `emul i a b a·b a² bytes(a)` with tags `field-e-a` and `field-e-b`.
- **`dump-circuit`** (16 384 lines). Line `k na nb ha hb` for each position `k` of `chainBlock`'s
  `rowOf`:
  - `na`, `nb` are the popcounts of the `a` and `b` forms;
  - `ha`, `hb` are `blake2s256` of the form as 2 048 bytes (byte `i` bit `b` is position `8i+b`).

  Row 512 is `rowOf`'s `(var 512, var 512)`. In total there are 53 619 173 nonzeros in `A` and
  35 685 307 in `B` (≈ 8.9·10^7, as the blueprint says).
- **`dump-walk`** (8 lines). Line `walk i A0 B0 A0' B0'`:
  - `r_k[l] = chE(katRand "walk-rk" (14i+l))` and `r_j[l]` likewise with tag `walk-rj`, `l < 14`;
  - `A0, B0` skip row 512 (A1); `A0', B0'` include `rowOf 512`.
- **`dump-encode`** (32 768 lines). Line `enc i c Enc(msg_i)_c`:
  - `k = 512`, `N = 4096`, `msg_i[j] = chE(katRand "encode-<i>" j)`;
  - `i < 8`, `c < 4096`.
- **`dump-transcript`** (126 lines). Line `idx op st`, where `op` is one of `seed`,
  `absorb <kind hex> <msg length>` or `squeeze`, and `st` is the state after it. It covers the
  leaf `s = 00 01 … 1f`, `n = 2`, from the seed to the last index squeeze (Merkle queries are not
  transcript states).
- **`dump-proof DIR`** (4 lines, plus `DIR/kat-n<n>.bin`). Line `proof n s stmt size blake2s(π)`
  for `n ∈ {1, 2, 16, 64}`, with `s = katRand "proof-start" n`.

  | `n` | proof size | `blake2s(π)` prefix |
  |---|---|---|
  | 16 | 143 711 B | `1c269726…` |
  | 64 | 193 467 B | `ceac6ba5…` |

  The full values are in `kat/proof.txt`.

`kat.py` is not written: no Lean dump exists yet to diff against, and the diff is `diff -u` file
by file.

## 6. Deviations from the blueprint

- **Location.** §11 places the crate in `native/`; IMPLEMENTERS.md requires the flat root, so it
  is in the root.
- **No `blake2` or `rayon`.** Both are written here, so the build needs no network and no
  vendoring.
- **Extra commands:** `check-leaf` (needed to verify `n > 4096` natively) and `bench-field`.
- **Prover algorithm (not the bytes).**
  - In the first four outer rounds and the first three inner rounds, the tables are read from bit
    tables through lookup tables over bit patterns, instead of folding over `E`.
  - The inner table is held as three tensors (`P_i(j)·γ_i(t')`) plus the public part, never as a
    dense `2^{15+κ}` table.

  The round polynomials are the unique ones of the definition, so the bytes are the same. They
  were checked identical before and after these optimisations at `n = 2^14`, and the
  `dump-proof`/`dump-transcript` KATs are stable.

## 7. Open points

1. **Lean-side byte equality is untested until `spartan-run dump-*` exists.** The highest-risk
   items:
   - A1 (row 512);
   - A3 (opening order);
   - A6 (packing);
   - the inner table's region-2 terms, which `matrix_formula_matches_definition` covers on the
     Rust side only.
2. The native verifier's column checks are single-threaded and take 0.4 s at `n = 1024`. That does
   not matter for R1 (`n = 16`). It is the same `7k`-per-column cost the Lean `V` will pay
   (blueprint §12).
3. `n = 2^14` needs 3.95 GB of peak memory. `n = 2^20` was not attempted: its proof is 10.2 MiB,
   far above `proofCap`.
