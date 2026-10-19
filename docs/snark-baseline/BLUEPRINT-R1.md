# BLUEPRINT-R1: the `spartan-chain` entry (normative)

Status: specification, 2026-10-19, revised the same day after the adversarial review
`docs/reviews/BLUEPRINT-R1-review.md` (§14 answers every finding), for implementation in parallel
(Lean verifier `V`, Lean honest prover `P`, Lean proofs, Rust native prover). Root
`submissions/spartan-chain/`, Lean module prefix `SpartanChain`. Read against the core at
`15e4ae5` and the **amended** contract on the core branch `v3/ks-potential` (checkout
`/home/devops/Verified-zkEVM/rf-core-ks`, head `c3f6380`): `KState` is a potential `μ : Log → ℝ≥0`
with `empty`, `step` (`Σ_a μ(L ++ [(q,a)]) ≤ (μ L + ε)·2^256` for fresh `q`, `L.length < logCap`,
`μ L < 1`) and `final` (`L.length ≤ logCap`, `μ L < 1`, `runLog L = some true` ⇒ the extractor
returns a witness in `R`); **`logCap = 2^96`**; the paper theorem is
`Library/PaperTheorem.lean` (`paper`: failure probability `≤ n·ε` for a game of `n ≤ logCap`
queries). Nothing here uses the counting form `KState.Bounded`. Decisions taken here are
**[D-7]** … **[D-11]** (continuing `PLAN.md`); §13 lists what the orchestrator still has to
decide. Everything numeric below is either a definition or was computed by the script quoted in
§12 (recomputed by the review's `logs/blueprint-review/check.py`); nothing is a measurement.

Notation. `K = BF64` (CompPoly), `E = Ext3 = K[y]/(y³+y+1)`, `|K| = 2^64`, `|E| = 2^192`,
characteristic 2 (so `−` is `+`). `x ∈ K` is the class of `X` (bit 0 of the word is `X⁰`).
`{0,1}^ℓ` is the Boolean cube; an integer `u < 2^ℓ` is also its little-endian bit vector
`(u_0, …, u_{ℓ−1})`, `u_0` least significant. For `r ∈ E^ℓ` and `u ∈ {0,1}^ℓ`,
`eq(r, u) = ∏_l (1 + r_l + u_l)`; for `f : {0,1}^ℓ → E`, `f̃(r) = Σ_u eq(r, u)·f(u)`. `H` is the
oracle (`ByteArray → Digest`); `H(a ‖ b)` means the query whose bytes are `a` followed by `b`;
`[v]_{31}` is the first 31 bytes of a digest. `enc64` is the contract's 8-byte little-endian
encoding. BLAKE2s names (`compress`, `block`, `iv`, `blake2s256`) are the contract's
(`Contract/Hash/Blake2s.lean`).

---

## 0. What R1 is, and three facts that shaped it

R1 is `[D-3]`: leaf proofs carry `(s, n)` in the clear and a SNARK of `chainEnd s n = h`; node
proofs are witness-sending. Three facts found while sizing it:

1. **A node proof embeds its children.** `witWords (.node c₁ c₂ π₁ π₂)` contains `π₁` and `π₂`
   verbatim, and `Vb` rejects any proof above `proofCap = 2^20` bytes. So the root of the `r = 2`
   smoke tree carries **four** leaf proofs and must still be under 1 MiB: a leaf at `n = 16` must
   be at most about 255 KiB. The ranked tree (`r = 8`, 256 leaves) can never fit: it would need
   leaves under 4 KiB. **R1's acceptance run is the smoke tree; the §6.3 root check at `r = 8`
   is impossible for any entry with witness-sending nodes and SNARK leaves** (§13, item 1).
2. **An unpacked bit witness is too large for that.** One compression is a block of `2^14`
   Boolean positions (§2); `n = 16` gives `2^18` committed field elements, and a Ligero proof
   over them at `2^-129` is about 450 KiB with the best matrix shape (computed in §12). No
   choice of rate, shape or path deduplication brings it under 255 KiB while keeping the
   provable `e < d/3` regime.
3. **Packing 64 bits per `K` element fixes it,** and the price is leanVM's ring switching
   (Annex A of the leanVM paper), whose soundness is elementary (§5, §9): six single-answer
   challenges, two kernel-decidable facts about `K ⊂ E`, and one root count. The committed
   object shrinks 64× (`2^12` elements at `n = 16`), the leaf is ≈ 140 KiB, the smoke root
   ≈ 562 KiB, and the verifier's PCS work shrinks 64× too. **[D-7] R1 packs the witness and uses
   Frobenius ring switching.** The PCS stays the Ligero tensor commitment of `[D-4]`.

The protocol, top to bottom (one leaf): parse → BLAKE2s-chain R1CS over `K` with uniform block
matrices (§2) → Spartan outer and inner sumchecks over `E` (§3) → 64 slice claims → ring
switching to one weighted claim on the packed witness → one more sumcheck → one Ligero
evaluation claim (§4) → proximity test, evaluation test, `t = 260` column openings, Merkle
tree over `H`, Fiat–Shamir over `H` (§5–§6).

---

## 1. Statement handling and `V`'s top level

### 1.1 Proof formats

A proof is a byte string whose first 8 bytes are the extractor-output tag word (`Library/Words.lean`,
`witWords`): `0` for a leaf, `1` for a node. Every other first word is rejected.

**Leaf proof** (`n` the chain length, `s` the start, `h` the claimed chain end):

| bytes | content |
|---|---|
| 0–7 | `enc64 0` (tag word) |
| 8–39 | `s` |
| 40–47 | `enc64 n` |
| 48–79 | `h` |
| 80– | the SNARK `π_S(n)` of §7, **absent when `n = 0`** |

Bytes 0–47 are exactly `wordsBytes (witWords (.leaf s n))`, so `packBytes` of the proof starts with
the six words `decodeWit` reads for a leaf (`decodeWit_cons`: a leaf reads words 1–5 and ignores
the rest). The library's `WitnessSending.decode π = some (.leaf s n)` for every leaf proof, with
any trailing bytes, which is what makes the 8-instruction image and its `computes` theorem
reusable unchanged (§1.4).

**Node proof**: exactly `WitnessSending.encode (.node c₁ c₂ π₁ π₂)`, i.e. `wordsBytes` of
`toWord 1 :: packBytes c₁ ++ packBytes c₂ ++ bytesWords π₁ ++ bytesWords π₂` (each child proof:
one length word, then its bytes packed and zero-padded to a word).

The total size of a leaf proof is a function `leafSize n` of `n` alone (§7); `V` rejects any
other size, so the canaries of DESIGN-v3 §6.3 step 7 (one byte appended, last byte removed) are
rejected by the parse, not by a hash.

### 1.2 `V`

```
V c π :=
  if π.size < 8 then ret false
  else match word 0 of π with
  | 0 => leafProg c π          -- a query program, §1.3
  | 1 => ret (checkNode c π)   -- no query
  | _ => ret false

checkNode c π :=
  match decodeF π with                         -- the linear decoder, §1.2.1
  | some (.node c₁ c₂ π₁ π₂) =>
      if encodeF (.node c₁ c₂ π₁ π₂) = π then  -- canonical, as the S2a entry's `check`; linear
        c = nodeStmt c₁ c₂
        ∧ π₁.size ≤ proofCap ∧ check c₁ π₁
        ∧ π₂.size ≤ proofCap ∧ check c₂ π₂
      else false
  | _ => false

check c π : Bool :=                            -- the instantiated decision, recursive on size
  if π.size < 8 then false                     -- the same guard as `V`
  else match word 0 of π with
  | 0 => (leafProg c π).run blake2sOracle
  | 1 => checkNode c π
  | _ => false
```

`check` terminates by `π.size` exactly as the S2a entry's `check` does (a canonical node encoding
is longer than each child: `encodeF_eq`, `size_encode`). The theorem `Vb_eq :
submission.Vb c π = (decide (π.size ≤ proofCap) && check c π)` is the bridge to
`Rel submission.Vb`; it holds for every `π` because `check` and `V` take the same branches (the
`π.size < 8` guard included). The node branch decides `Rel` locally, so `final` for node proofs is
`checkNode_sound`, with no oracle in it (`WitnessSending.check_sound`'s pattern); its proof goes
through `check_eq`, which restates `check` with the library's `decode` and `encode`
(`decodeF_eq`, `encodeF_eq`). `check` is what the compiled `verify` binary runs.

**1.2.1 The linear decoder (`Decode.lean`).** The library's `decode`, `encode`, `packBytes`,
`bytesWords` and `bytesAt` compile to code quadratic in the proof length (S2a RESULT §6: 563 s to
reject a random 1 MiB proof, `logs/V3-S2/dos-unfiltered/run.log`); the smoke root is 575 112 B,
so the node check must not run them. `Decode.lean` is a copy, with a provenance line, of the S2a
entry's linear twins (`submissions/baseline/BaselineV3.lean`, entries do not import each other):
`packFast` (8 bytes at a time) with `packFast_eq : packFast b = packBytes b`; `bytesAtF` (through
an array) with `bytesAtF_eq`; `decodeWitF` with `decodeWitF_eq : decodeWitF o = decodeWit o`;
`decodeF π := decodeWitF (packFast π.data.toList)` with `decodeF_eq : decodeF π = decode π`;
`witWordsF` and `encodeF` with `encodeF_eq : encodeF w = encode w`. `checkNode` runs `decodeF`
and `encodeF`; every proof about it rewrites with the `_eq` theorems to the library's functions.
The S2a measurements for the same code (`logs/V3-S2/fix/check/smoke.log`): random 1 MiB proofs
rejected in at most 0.28 s, adversarially shaped ones in at most 1.25 s. The work per node is
linear in the node's size; the smoke root (depth 2) decodes three nodes, 1.15 MB in all. The
`check.sh` of this entry measures it (§12).

### 1.3 `leafProg c π` (the only query program)

1. Parse `s := π[8..40)`, `n := ofLE π[40..48)`, `h := π[48..80)`. Reject unless `n ≤ chainCap`
   and `π.size = leafSize n` (both before any query). Reject unless `c = leafStmt h n`
   (computed locally with `blake2sDigest`, not through `H`).
2. If `n = 0`: accept iff `h = s`.
3. Else let `κ := ⌈log₂ n⌉` (`κ = 0` for `n = 1`), shape `(m, k, N, t)` from `κ` (§5.2), and run
   the SNARK verifier of §3–§6 on `π_S(n)` with public input `(s, n, h)`; it queries `H` only for
   the Fiat–Shamir chain and the Merkle paths.

The public input of the SNARK is `(s, h)`; `n` fixes the circuit. `c` is bound by step 1; the
transcript is seeded with `(s, n, h)` (§6). No part of the leaf branch computes BLAKE2s on an
oracle input and compares it with an oracle answer (the near-CGH pattern F1 §7.1 warns about):
`leafStmt` is applied to proof bytes and compared with `c`.

### 1.4 `P`, `E`, `img`, `fuel`

* `P c (.leaf s n) := do let π_S ← proveLeaf s n h; ret (leafBytes s n h π_S)` with
  `h := chainEnd s n` (recomputed by `P`, not taken from `c`); `P c (.node c₁ c₂ π₁ π₂) :=
  ret (encode (.node c₁ c₂ π₁ π₂))`. `proveLeaf` is a query program (Merkle and Fiat–Shamir
  through `H`); its messages are §7's, byte for byte, so the Rust prover's output must be
  **byte-identical** to the Lean `P`'s on the same `(s, n)` (the protocol is deterministic given
  `H`) — the strongest known-answer test (§11.3).
* `E := WitnessSending.E` (`fun _ π _ => decode π`, the library's `decode`: the specification,
  never run by `check`), `img := WitnessSending.img`, `fuel := WitnessSending.fuel` (8).
  `computes := WitnessSending.computes` is reused as is.
* `Submission.ε := 2^-129`, `qV := 2^14` (§9.4, §12).

---

## 2. The arithmetisation

### 2.1 What is reused, and the E1/E4 conflict

Both notes are right about different files. E4's "assumed" is
`LeanerVM/Arithmetization/Tables/Blake2s.lean`, the Clean table row, where `Blake2sRelation` is
an `Assumptions` field. E1's "proved" is `LeanerVM/Protocol/Blake2sCircuit.lean` (632 lines,
`main` at `e715c49`, branch `docs/protocol-headline-theorems` `532ebb4`), which R1 reuses:

| declaration (leanerVM) | statement | used for |
|---|---|---|
| `blake2sCircuit : ProductCircuit 14` | the compression as 14 720 product gates from position 1280, output rows `(out bit, 1)` at 256…511, constant at 512, inputs 0…255 and 640…1279 | the block matrices `A0, B0` |
| `bounded_blake2s` | every gate reads only inputs, the constant and earlier gates, at a fresh position | both directions below |
| `blake2s_sound_words` | for `z : Pos 14 → Bool` with `(toBlockR1CS R).Holds (liftBlock R z)` over any nontrivial `R` of characteristic 2 and `z 512 = true`: `readWord z (256+32k) = (compress (cv words of z) (msg words of z) (counter of z) (f0 of z) (f1 of z))[k]` | soundness |
| `blake2s_complete` | the trace of any input satisfies the R1CS, holds `1` at 512, keeps its inputs, and its output words are the compression | completeness |
| `Flock/{BlockR1CS,Circuit,Builder,Words}.lean` | the circuit framework: forms as bitsets, `rowOf`, `Holds`, `trace`, `holds_eq_trace`, `trace_satisfies`, adders `addW`/`add3W` with `sound_*`/`ok_*` | copied |

Its `compress` (`LeanerVM.Semantics.Blake2s.compress`) is textually the contract's
`RecursionFast.Blake2s.compress` except `rotr` (`BitVec.rotateRight` vs machine shifts); the
contract's `Library/Blake2s.lean` has `rotr_eq_rotateRight (hn : n < 32)`, and the circuit uses
only `16, 12, 8, 7`. **Bridge:** the copy restates `den_rotrW` and everything above it against
the contract's `compress` with that lemma; no other change of statement.

Copy, do not import (nothing under `LeanerVM` is allowlisted): the four framework files and
`Blake2sCircuit.lean` (≈ 2 300 lines, Apache-2.0, provenance line per file). Mechanical edits:
drop `module`/`public`/`@[expose]`; replace `CMlPolynomialEval R m` by `Fin (2^m) → R`; replace
the `local macro grows_gW_chain` (the source rule refuses `macro`) by its expansion
`repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ | exact grows_gW _ _ _ _ _ _ _)`.

### 2.2 The chain block (one circuit, `2^14` positions)

Position layout (leanVM `crates/flock/src/hash.rs:40-63`, as transcribed):

| positions | content | row kind in `chainBlock` |
|---|---|---|
| `0…255` | chaining value `h0`, word `w` bit `i` at `32w + i` | **constant** (§2.2.1) |
| `256…511` | output, word `w` bit `i` at `256 + 32w + i` | output rows `(outForm, var 512)` |
| `512` | the constant `1` | `(pub₀, pub₀)` (§2.3) |
| `513…639`, `904…1151`, `1184…1215`, `1248…1279`, `16000…16383` | padding / zero message bytes / `t_hi` / `f1` | `(0, 0)` |
| `640…647` | message byte 0 = tag `0x43` | constant |
| `648…903` | message bytes 1…32 = the digest `d` being hashed, byte `e` bit `b` at `648 + 8e + b` | **free input** `(var k, var 512)` |
| `1152…1183` | counter low word `= 33` | constant |
| `1216…1247` | `f0 = 0xFFFFFFFF` | constant |
| `1280…15999` | 80 `G` steps × 184 product gates | gates `(a_k, b_k)` from `blake2sCircuit` |

`C = I` on every row: row `k` has `C_k = e_k`. The message layout agrees with the contract's
`block`: message byte `e` is bits `8e … 8e+7` of word `⌊e/4⌋`; the chain step hashes the 33 bytes
`0x43 ‖ d`, so `m[0] = 0x43 + 2^8·d[0] + …`, `m[8] = d[31]`, `m[9..16) = 0`. The output digest
byte `e` is bits `256 + 8e …` (little-endian words, `blake2s`'s `le`).

**2.2.1 Constants.** For a constant position `k` whose required bit is `1` the row is
`(var 512, var 512)` (so `z_k = z_512² = 1` once `z_512 = 1`); whose bit is `0`, `(0, 0)` (so
`z_k = 0`). The constants: `h0 = iv` with `iv[0] ^= 0x01010020` (`kk = 0`, `nn = 32`), i.e.
`h0[0] = 0x6B08E647`; tag `0x43` (bits 0, 1, 6 of byte 640); counter `33` (bits 0 and 5 of word
1152); `f0` all ones; `t_hi = f1 = 0`.

`chainBlock : ProductCircuit 14` is `blake2sCircuit` with `inputs := {648 … 903}` and, prepended
to `gates`, one gate for **every** constant position `k ∈ ({0 … 255} ∪ {640 … 1279}) \ {648 … 903}`
(the inputs of `blake2sCircuit` that the chain fixes): `(k, ⟨var 512, var 512⟩)` where the
required bit is `1`, `(k, ⟨0, 0⟩)` where it is `0`. `rowOf` looks gates up first, so the gate and
output rows are literally `blake2sCircuit`'s, and the `(0, 0)` gates give the same row as a
non-input, non-gate position would (the row list, the matrices and the Rust `circuit` KAT are
unchanged by this choice; it exists so that `Bounded` holds, below). Lemmas:

* `holds_chainBlock_imp (hz : z 512 = true)`: a block satisfying `chainBlock` satisfies
  `blake2sCircuit`. The rows that differ are the constant positions, which in `blake2sCircuit` are
  input rows `z_k·z_512 = z_k`, trivial once `z_512 = 1`; the hypothesis is needed (without it the
  row reads `z_k·z_512 = z_k`, which a `(0,0)` or `(var 512, var 512)` row does not give).
* `bounded_chainBlock : Bounded chainBlock` (leanerVM `Flock/Circuit.lean`'s `Bounded c :=
  BoundedFrom (c.inputs ||| var cpos) c.gates`: every gate's forms mention only inputs, the
  constant and earlier gates). It holds because every input of `blake2sCircuit` is either an
  input of `chainBlock` or one of the prepended gates, the prepended gates read only `var 512`
  or nothing, and the BLAKE2s gates then read only `blake2sCircuit.inputs ∪ {512} ∪` earlier
  gates by `bounded_blake2s`. Proved from `bounded_blake2s` by set inclusion, or by `decide` on
  the gate list. `traceF`, `trace_satisfies` and `trace_holds` need it (§2.2.2, `block_complete`).

**2.2.2 Block correctness (both directions, against the contract).**

* `block_sound`: for `z : Fin 2^14 → Bool` with `Holds (chainBlock.toBlockR1CS E) (liftBlock E z)`
  and `z 512 = true`: `readDigest z 256 = chainStep (readDigest z 648)`, where
  `readDigest z b` is the 32 bytes whose byte `e` has bit `b'` equal to `z (b + 8e + b')`. Proof:
  `blake2s_sound_words` gives the 8 output words as `compress h0 (block (0x43 :: d)) 33 0xFFFFFFFF 0`
  (the constant rows fix `cv`, counter and flags; the tag row fixes byte 0); and
  `chainStep d = blake2sDigest (0x43 :: d.toList) = le-bytes of compressInput h0 0 (0x43 :: d) 0`
  with `(33 − 1)/64 = 0` blocks before the final one — one `unfold` of `blake2s`.
* `block_complete`: `chainTrace d := chainBlock.traceF (input with d at 648…903)` satisfies the
  R1CS, has `1` at 512, the message bits at 648…903, and `readDigest _ 256 = chainStep d`
  (`blake2s_complete` plus the constant rows' traces).

### 2.3 The chain R1CS (`n ≥ 1`, `κ = ⌈log₂ n⌉`, `2^κ` blocks)

**Columns** `z = (w ‖ pub)`, `|z| = 2^{15+κ}`; column index `y = u + 2^{14+κ}·top`:
* `top = 0`: `w(u)`, `u = k + 2^14·t` (position `k` of block `t`); **`w` is the committed
  witness and is Boolean by construction** (it is the bits of the packed `q`, §4): no
  booleanity rows.
* `top = 1`: `pub(u)`, public, computed by `V`: `pub(0) = 1`, `pub(1 + j) = s_j` (bit `j` of
  `s`, byte `⌊j/8⌋` bit `j mod 8`), `pub(257 + j) = h_j` for `j < 256`, else `0`.

**Rows** `x ∈ {0,1}^{15+κ}`, `x = i + 2^{14+κ}·xtop`:
* Region 0 (`xtop = 0`): `i = k + 2^14·t`: row `k` of `chainBlock` on block `t`'s columns, except
  row 512, which is `A = pub(0)`, `B = pub(0)`, `C = w(t, 512)`. Write **`A0, B0` for the row
  forms of `chainBlock` with row 512 cleared** (`chainBlock`'s own row 512 is `(var 512, var 512)`,
  which the chain R1CS replaces). So `A_0 = I_{2^κ} ⊗ A0` on the `w` columns plus `1 ⊗ A0ᵖ` on
  the `pub` columns with `A0ᵖ = {(512, 0)}`, likewise `B`, and `C_0 = I_{2^{14+κ}}`.
* Region 2 (`xtop = 1`), **wiring rows** `i = j + 256·t`, `j < 256`, `t < 2^κ`:
  `A = w(t−1, 256 + j)` if `t ≥ 1`, `A = pub(1 + j)` if `t = 0`; `B = pub(0)`; `C = w(t, 648 + j)`.
  (Block `t`'s message is block `t−1`'s output; block 0's is `s`.)
* Region 2, **tail rows** `i = 2^{8+κ} + j`, `j < 256`: `A = w(n−1, 256 + j)`, `B = pub(0)`,
  `C = pub(257 + j)`. (Block `n−1`'s output is `h`.)
* Every other row of region 2 is empty (`0 = 0`).

The matrices depend on `n` only; `s` and `h` enter through `pub`. Padding blocks `t ∈ [n, 2^κ)`
are constrained like the others (they continue the chain) and the tail reads block `n−1`.

**`Sat n s h z`**: `∀ x, (Az)(x)·(Bz)(x) = (Cz)(x)` with `z = (w ‖ pub(s,h))`.

* `chain_complete`: `w := chainWitness s n` with block `t := chainTrace (chainEnd s t)` satisfies
  `Sat n s (chainEnd s n)`.
* `chain_sound`: `w` Boolean and `Sat n s h (w ‖ pub(s,h))` ⇒ `chainEnd s n = h`. Proof: row 512
  gives `w(t,512) = 1`; `block_sound` per block gives `out_t = chainStep(msg_t)`; wiring rows give
  `msg_0 = s`, `msg_t = out_{t−1}`; induction gives `out_t = chainEnd s (t+1)`; the tail gives
  `out_{n−1} = h`.

### 2.4 Evaluating `Ã, B̃, C̃` at `(r_x, r_y)`

Write `r_x = (r_k ∈ E^14, r_t ∈ E^κ, r_xtop)` (variables `0…13`, `14…13+κ`, `14+κ`) and
`r_y = (r_j ∈ E^14, r_t' ∈ E^κ, r_ytop)`; within `r_k` also `r_kj := r_k[0..8)` (the low 8
variables) and `r_k8 := r_k[8..14)`. `V` builds two tables `e(k) = eq(r_k, k)` and
`wt(j) = eq(r_j, j)` over `k, j < 2^14` (the standard doubling construction, `2^15` multiplications)
and the 8-variable table `eq(r_kj, ·)`. In region 2 the batch index sits at row variables
`8 … 7+κ`, not `14 … 13+κ`; write `r_t² := r_x[8..8+κ)`. Abbreviations:

* `T0 := eq(r_t², 0)`, `T0' := eq(r_t', 0)`, `U0 := eq(r_j, 0)·T0'` (the `pub` column 0);
* `Σ_j^{b} := Σ_{j<256} eq(r_kj, j)·wt(b + j)` (256 products from the tables);
* row factors: region 0 `R0 := 1 + r_xtop`; wiring rows (bits `0…7 = j`, `8…7+κ = t`, the rest
  `0`) `RW := r_xtop·∏_{l=8+κ}^{13+κ}(1 + r_x[l])`; tail rows (bits `0…7 = j`, bit `8+κ = 1`, the
  rest `0`) `RT := r_xtop·∏_{l=8}^{7+κ}(1 + r_x[l])·r_x[8+κ]·∏_{l=9+κ}^{13+κ}(1 + r_x[l])`;
* `Σ_t eq(r, t) = 1` for every `r` (`eq_sum_one`), which is why the `1 ⊗ A0ᵖ` part and the
  `B = pub(0)` columns carry no batch factor; `eq(r_t', n−1)` is `eq` of the `κ`-bit constant
  `n − 1`; `S̃` is §2.4.1.

`M̃(r_x, r_y) = R0·(region 0 term) + RW·(wiring term) + RT·(tail term)` with:

| matrix | region 0 term | wiring term | tail term |
|---|---|---|---|
| `Ã` | `(1+r_ytop)·eq(r_t,r_t')·A0̃(r_k,r_j) + r_ytop·e(512)·U0` | `(1+r_ytop)·S̃(r_t², r_t')·Σ_j^{256} + r_ytop·T0·T0'·Σ_j^{1}` | `(1+r_ytop)·eq(r_t', n−1)·Σ_j^{256}` |
| `B̃` | `(1+r_ytop)·eq(r_t,r_t')·B0̃(r_k,r_j) + r_ytop·e(512)·U0` | `r_ytop·U0` | `r_ytop·U0` |
| `C̃` | `(1+r_ytop)·eq(r_t,r_t')·eq(r_k,r_j)` | `(1+r_ytop)·eq(r_t²,r_t')·Σ_j^{648}` | `r_ytop·T0'·Σ_j^{257}` |

The empty rows contribute nothing.

**2.4.1 The shift.** `S(t, t') = 1` iff `t' + 1 = t` (the column block precedes the row block):

```
S̃(a, b) = Σ_{i<κ} ( ∏_{l<i} b_l·(1 + a_l) ) · (1 + b_i)·a_i · ∏_{l>i} (1 + a_l + b_l)
```

(`b` has a run of ones below `i`, a zero at `i`; `a` the complement there; equal above.)
Multilinear in each variable, so it is the MLE; `O(κ)` with prefix and suffix products.

**2.4.2 The block walk.** `A0̃(r_k, r_j) = Σ_k e(k)·Σ_j A0(k,j)·wt(j)`, and `B0̃` alike, are
computed by **one forward walk of the gadget code** in `O(|circuit|)`, never from the matrices
(which have about `8.9·10^7` nonzeros). The copy of `Blake2sCircuit.lean` is written once over an
abstract form type: a `Word` is 32 forms, `xorW`/`rotrW`/`litW`/`inW` and the adders are
generic in operations `(zero, var, xor, mul)`. Two instances:

* bitsets (`Form 14 = BitVec 2^14`, `mul` records a gate): the R1CS, as in leanerVM;
* the walk (`Form := E`, `var k ↦ wt(k)`, `xor ↦ +`, `mul a b` at position `k` adds `e(k)·a` to
  `accA`, `e(k)·b` to `accB` and returns `wt(k)`); the output rows add `e(k)·val(outForm)` and
  `e(k)·wt(512)`; input rows `(var k, var 512)` add `e(k)·wt(k)` and `e(k)·wt(512)`; constant-one
  rows add `e(k)·wt(512)` twice; `(0,0)` rows nothing. **The walk skips position 512** (`cpos`,
  whose `chainBlock` row `(var 512, var 512)` is cleared in `A0, B0`, §2.3): that row's
  replacement is the `r_ytop·e(512)·U0` term of §2.4, and walking it too would double it (the
  honest check would then read `(w_512 + 1)² = w_512`, false).

`walk_eq_sum`: `walkA e wt = Σ_{k ≠ 512} e(k)·Σ_j (rowOf k).a[j]·wt(j)` (and `B`), by a simulation
invariant over the `Builder` monad: every form `L` produced by the bitset instance and the value
`v` produced by the walk instance at the same program point satisfy `v = Σ_j L[j]·wt(j)`
(`xor` ↦ `+` and `mul` ↦ the recorded gate). Cost: about `2·14 720 + 2·256 + 2·896` multiplications
plus `2^15` for the tables: `≈ 2^16` `E`-multiplications, independent of `n`.

---

## 3. Spartan

`ℓ_x = ℓ_y = 15 + κ`. All challenges in `E`, all sumchecks bind variable `0` first. A round
polynomial `g` of degree `≤ d` is sent as its `d + 1` coefficients `c_0 … c_d` (ascending); the
verifier checks **`c_1 + c_2 + … + c_d = claim`** — this is `g(0) + g(1)` with `g(0) = c_0` and
`g(1) = c_0 + c_1 + … + c_d`, the two `c_0` cancelling in characteristic 2; it is **not** `g(1) =
claim` — and sets the next claim to `g(r)` (Horner). No coefficient is dropped (it saves 24 bytes
a round and a lemma; not worth it).

**Outer (zerocheck).** `τ ∈ E^{ℓ_x}` (one squeeze per coordinate). Claim `0 =
Σ_x eq(τ, x)·( (Az)(x)·(Bz)(x) + (Cz)(x) )`, degree 3, `ℓ_x` rounds, challenges `r_x`. The prover
then sends `v_A, v_B, v_C ∈ E` claiming `v_M = (Mz)̃(r_x) = Σ_y M̃(r_x, y)·z(y)`. Check:
`claim_final = eq(τ, r_x)·(v_A·v_B + v_C)`.

**Inner.** `ρ ∈ E`. Claim `v_A + ρ·v_B + ρ²·v_C = Σ_y ( Ã + ρB̃ + ρ²C̃ )(r_x, y)·z(y)`, degree 2,
`ℓ_y` rounds, challenges `r_y`. Final check: `claim_final = M̃_ρ(r_x, r_y)·z̃(r_y)` where
`M̃_ρ = Ã + ρB̃ + ρ²C̃` is §2.4 and

```
z̃(r_y) = (1 + r_ytop)·w̃(r_u) + r_ytop·pub̃(r_u),        r_u = r_y[0..14+κ)
pub̃(r_u) = eq(r_u, 0) + Σ_{j<256} s_j·eq(r_u, 1+j) + Σ_{j<256} h_j·eq(r_u, 257+j)
```

(`pub̃`: the 10-variable table `eq(r_u[0..10), ·)` times `∏_{l≥10}(1 + r_u[l])`, 513 lookups.)
`w̃(r_u)` is **not** opened directly: §4.

**Padding and variable `n`.** Everything is sized by `κ`; `n` enters the matrices only through the
tail rows (`eq(r_t', n−1)`). `V` handles every `1 ≤ n ≤ 2^20` by the same code with `κ ≤ 20`.

**Honest prover.** Round polynomials are computed as exact products of linear polynomials in the
round variable (coefficient arithmetic, no interpolation, no inversion): for the outer sumcheck
each summand is `eq-factor × (A-factor × B-factor + C-factor)` with every factor linear.
Tables `Az, Bz, Cz` over `2^{15+κ}` rows come from the matrices' sparse structure (the gates' forms
on the block's values: one block walk per block over `K`-valued witnesses, plus the wiring and
tail rows).

---

## 4. Packing and ring switching

### 4.1 The packed witness

`w(u)`, `u = i + 64·u'`, `i < 64`, `u' < 2^{8+κ}`. Define `Q_i(u') := w(i + 64u')` (bit-plane `i`)
and the **packed witness** `q : {0,1}^{8+κ} → K`, `q(u') = Σ_{i<64} Q_i(u')·x^i` (bit `i` of the
word is `Q_i`). So one `K` element holds 64 consecutive positions of one block (leanVM's
`LOG_PACKING = 6`). `q` is what the PCS commits (§5). **The bits of `q` are the witness:** the
extractor's `w` is defined from the decoded `q`, hence Boolean.

### 4.2 Slices

After the inner sumcheck the verifier needs `w̃(r_u)` with `r_u = (r_lo ∈ E^6, r_hi ∈ E^{8+κ})`:

`w̃(r_u) = Σ_{i<64} eq(r_lo, i)·Q̃_i(r_hi)`.

The prover sends the 64 **slices** `s_i ∈ E` claiming `s_i = Q̃_i(r_hi)`; `V` sets
`w̃ := Σ_i eq(r_lo, i)·s_i` and uses it in the inner final check. The slices are then proved by
ring switching.

### 4.3 Ring switching (leanVM Annex A, with `κ_pack = 6`)

`V` squeezes `f_0, …, f_5 ∈ E` and defines the `F₂`-linear map `Φ : E → E` by the six stages

`a_0 = a`, `a_{p+1} = a_p + f_p·a_p^{2^{M_p}}`, `M_p = 2^{5−p}` (`32, 16, 8, 4, 2, 1`), `Φ(a) = a_6`.

Equivalently `Φ(a) = Σ_{k<64} c_k·a^{2^k}` with the table built by stages: `T_0 = {0 ↦ 1}`,
`T_{p+1} = T_p ∪ { k + M_p ↦ f_p · T_p[k]^{2^{M_p}} : k ∈ T_p }` (63 multiplications, 192 squarings).

* Target `T := Σ_{i<64} x^i·Φ(s_i)` (64 applications: 63 squarings and 6 multiplications each;
  `x^i ∈ K`).
* Weight `W(u') := Φ(eq(r_hi, u'))` for `u' ∈ {0,1}^{8+κ}`. Its MLE at any `r'' ∈ E^{8+κ}` is

  `W̃(r'') = Σ_{k<64} c_k · eq(r_hi^{2^k}, r'')`, `r_hi^{2^k}` coordinate-wise Frobenius,

  because `eq(r, u)^{2^k} = eq(r^{2^k}, u)` on the cube and `Σ_u eq(a,u)eq(u,b) = eq(a,b)`.
* The claim handed on: `Σ_{u'} W(u')·q(u') = T`. Completeness is the identity
  `Σ_{u'} Φ(eq(r_hi,u'))·Σ_i Q_i(u') x^i = Σ_i x^i Φ(Σ_{u'} eq(r_hi,u') Q_i(u'))` (`Φ` is additive,
  `x^i` is a constant, `Q_i(u') ∈ {0,1}`).

### 4.4 The weighted sumcheck

Claim `T = Σ_{u'} W̃(u')·q̃(u')` over `{0,1}^{8+κ}`, degree 2, `8 + κ` rounds, challenges
`r'' ∈ E^{8+κ}`. Final check: `claim_final = W̃(r'')·v'` where `v' ∈ E` is the **Ligero evaluation
claim** `q̃(r'') = v'`, proved in §5. `W̃(r'')` costs `64·(8+κ)` multiplications plus
`63·(8+κ)` squarings.

(Why a sumcheck: `W` is a sum of 64 tensors, not one, so the tensor PCS cannot take it directly;
the sumcheck turns it into an evaluation at a random point, which is one tensor.)

---

## 5. The PCS: Ligero over the packed witness

### 5.1 The code

* **Domain** `D = (ω_0, …, ω_{N−1})`, `ω_c :=` the element of `K` whose 64-bit word is `c`
  (bit pattern `c`), `N = 2^{ℓ_N}`; distinct by construction. (`D` is the `F₂`-span of
  `x^0 … x^{ℓ_N − 1}`; the native prover may use the additive NTT, `V` never needs the structure.)
* **Subspace polynomials** by recursion, **unnormalised** (no inversion anywhere):
  `W_0(X) = X`, `W_{i+1}(X) = W_i(X)·(W_i(X) + κ_i)` with `κ_i := W_i(ω_{2^i})` (so `deg W_i = 2^i`,
  monic). `V` evaluates `W_i(ω)` by the same recursion on values (`i` multiplications) and the
  `κ_i` by it too.
* **Basis** `X_j := ∏_{i<ℓ_k} W_i^{bit_i(j)}` for `j < k = 2^{ℓ_k}`: `deg X_j = j`, monic, so
  `{X_j}` is a basis of `K[X]_{<k}`.
* **Encoding** `Enc : E^k → E^N`, `Enc(msg)_c = Σ_{j<k} msg_j·X_j(ω_c)`; at one point this is
  the multilinear-monomial evaluation `Σ_j msg_j ∏_i W_i(ω_c)^{bit_i(j)}`: build the tensor
  `(∏_i W_i(ω)^{bit_i(j)})_j` in `k − 1` `K`-multiplications, then a `k`-term dot product
  (`E × K`: 3 `K`-multiplications each).
* **Code** `C = {Enc(msg)} = {(p(ω_c))_c : p ∈ E[X], deg p < k}`, `E`-linear, `K`-rational
  (`Enc(K^k) ⊂ K^N`), minimum distance `d = N − k + 1` (a nonzero polynomial of degree `< k` has
  fewer than `k` roots, Mathlib `Polynomial.card_roots'`).

### 5.2 Shape

`M' = 2^{8+κ}` packed elements as an `m × k` matrix, `q(u') = Q[i][j]` with `u' = j + k·i`
(column `j` = low `ℓ_k` bits, row `i` = high `μ_r` bits):

`μ_r(κ) = ⌊(κ+3)/2⌋`, `m = 2^{μ_r}`, `ℓ_k = 8 + κ − μ_r`, `k = 2^{ℓ_k}`, **rate `1/8`**:
`ℓ_N = ℓ_k + 3`, `N = 8k`, `d = 7k + 1`, `e := ⌊(d−1)/3⌋` (so `3e < d`, `2e < d`), **`t = 260`**
columns. (The split minimises `48k + 2080m` with `km = M'`; `t` is from §5.5.)

| `n` | `κ` | `m` | `k` | `N` |
|---|---|---|---|---|
| 1 | 0 | 2 | 128 | 1024 |
| 16 | 4 | 8 | 512 | 4096 |
| 1024 | 10 | 64 | 4096 | 32768 |
| 2^14 | 14 | 256 | 16384 | 2^17 |
| 2^20 | 20 | 2048 | 2^17 | 2^20 |

### 5.3 Commitment and Merkle tree

`U = (Enc(Q[i]))_{i<m} ∈ K^{m×N}` (rows encoded over `K`: the message rows are in `K`). Column `c`
is the `m` elements `U[0][c], …, U[m−1][c]`, as `8m` bytes (each `K` element its 8 little-endian
bytes). Leaves are the `N` columns.

* Leaf label `λ(c) := [H(0x00 ‖ column c bytes)]_{31}`.
* Node label `λ(v) := [H(0x01 ‖ λ(left) ‖ λ(right))]_{31}` (63 bytes; with `Vb`'s `0x52`, one
  64-byte block: one compression).
* `root := λ(top)`, 31 bytes, in the proof.
* A path for column `c` is the `ℓ_N` sibling labels (31 bytes each), bottom-up. `V` recomputes
  `λ(c)` from the opened column bytes, climbs with the bit `c_l` deciding the side at level `l`,
  and compares the result with `root`.

31-byte labels: `[D-8]`. They keep every node query at one compression (E3's observation; this
matters in R2's circuit, not here) at the cost of `2^-248` instead of `2^-256` in the collision
and hit terms (§9): `3·2^96·2^-248 = 3·2^-152` per step at `logCap = 2^96`, far below the
`2^-129.35` of the query phase (the contract's own note: at `logCap = 2^96`, events of at least
224 bits are chargeable).

### 5.4 The two tests

* **Proximity.** Right after the root is absorbed, `V` squeezes `r_0, …, r_{m−1} ∈ E`
  (independent, one per squeeze). The prover sends `ū := Σ_i r_i·Q[i] ∈ E^k`. At each opened
  column `c`: check `Enc(ū)_c = Σ_i r_i·U[i][c]`.
* **Evaluation.** With `r'' = (r''_lo ∈ E^{ℓ_k}, r''_hi ∈ E^{μ_r})` from §4.4, `a_i := eq(r''_hi, i)`,
  `b_j := eq(r''_lo, j)`. The prover sends `v := Σ_i a_i·Q[i] ∈ E^k`; `V` sets `v' := Σ_j b_j·v_j`
  (this is the `q̃(r'')` used in §4.4's final check) and checks at each opened column
  `Enc(v)_c = Σ_i a_i·U[i][c]`.
* **Columns.** `t = 260` indices `c_0 … c_{259} ∈ [0, N)`, with replacement, from squeezes (§6.3).
  For each, the proof carries the column bytes and the path; `V` checks the path and the two
  equations. Repeated indices are opened and checked repeatedly (no deduplication: `[D-9]`,
  simplicity; the smoke root has room).

Why uniform coefficients and not powers of one challenge: the lemma we prove is AHIV22 Lemma 4.5
(§9.2, L-RS2), which is for a uniformly random element of the row span; the powers variant needs
BCIKS20's curve theorem. Why two tests and not Brakedown's one: the tensor-coefficient proximity
lemma (Diamond–Posen) is an induction over the uniform-line lemma that is not needed once the
witness is packed.

### 5.5 Parameters and error terms (derivation)

Let `U` be the committed matrix read from the log (§9.1). `U` is **`e`-close** if there is a set
`S ⊆ [N]`, `|S| ≤ e`, and codewords `C_0, …, C_{m−1} ∈ C` with `U[i][c] = C_i[c]` for all `i` and
all `c ∉ S`. Since `2e < d`, the `C_i` are unique (two decompositions agree outside `S ∪ S'`,
`|S ∪ S'| ≤ 2e < d`), and they lie in `K^N` (the `K`-coordinate projection of `C_i` is a codeword
agreeing with the `K`-valued row outside `S`, hence equals `C_i`). The decoded messages define
`q_dec`, hence `w_dec`.

* Far case (`U` not `e`-close): `Pr_r[ Σ_i r_i U[i] is e-close to C ] ≤ d/|E|` (L-RS2); if it is
  not, every `ū` the prover sends has `Enc(ū)` differing from `Σ_i r_i U[i]` in more than `e`
  positions, so one random column catches it with probability `≥ (e+1)/N`, and `t` columns miss
  with probability `≤ (1 − (e+1)/N)^t`. With `e+1 = ⌊7k/3⌋ + 1 > 7k/3` and `N = 8k`:
  `(e+1)/N > 7/24`, so the miss probability is `< (17/24)^{260} = 2^{−129.35}` **for every `k`**.
* Close case: `Σ_i a_i U[i]` agrees with `Enc(Σ_i a_i q_dec[i])` outside `S`; if the prover's `v`
  differs from `Σ_i a_i q_dec[i]`, `Enc(v)` differs from it in `≥ d` positions and from
  `Σ_i a_i U[i]` in `≥ d − e` positions: miss probability `≤ (1 − (d−e)/N)^t < (5/12)^{260} = 2^{−328}`
  (and the same for a wrong `ū`, which only hurts the prover).

So the query phase's escape probability is `< 2^{-129.35}` in both cases; `t = 260` is the least
`t` with `(17/24)^t ≤ 2^-129` (`t = 259` gives `2^{-128.85}`). The bounds for every
`5 ≤ ℓ_k ≤ 20` were checked numerically (§12).

---

## 6. The Fiat–Shamir transcript

### 6.1 Primitives

* State `st`: 32 bytes (a full answer).
* `st ← H(0x10 ‖ s ‖ enc64 n ‖ h)` (73 bytes) at the start.
* `absorb(st, kind, msg) := H(0x20 ‖ st ‖ kind ‖ msg)`, `kind` one byte, `msg` the exact proof
  bytes of the message (§7), of any length.
* `squeeze(st) := H(0x30 ‖ st)` (33 bytes); the answer is the new state **and** the challenge
  source.
* **Field challenge from an answer** `a`: `chE(a) := E.ofBytes(a[0..24))` — `c_0 = K` of bytes
  `0..8`, `c_1` of `8..16`, `c_2` of `16..24`, each the little-endian word, the element
  `c_0 + c_1 y + c_2 y²`. Exactly uniform on `E` when `a` is uniform: every `E` element has
  exactly `2^64` preimages (bytes 24–31 free).
* **Column indices from answers**: with `ℓ_N ≤ 23`, `cnt := ⌊256/ℓ_N⌋` indices per answer; index
  `i` of answer `a` is the integer whose bits are bits `[i·ℓ_N, (i+1)·ℓ_N)` of `a` read
  little-endian (bit `b` of the string is bit `b mod 8` of byte `⌊b/8⌋`). Exactly uniform on
  `[0, N)`, independent across indices. The query phase uses `J := ⌈t/cnt⌉` answers (`11` at
  `ℓ_N = 10`, `cnt = 25`; `13` at `ℓ_N = 12`, `cnt = 21`; `22` at `ℓ_N = 20`, `cnt = 12`); the
  trailing bits of the last answer are unused.

### 6.2 The sequence (one leaf, `n ≥ 1`)

| step | operation | kind byte |
|---|---|---|
| 1 | `st ← H(0x10 ‖ s ‖ enc64 n ‖ h)` | |
| 2 | `absorb(root)` | `0x01` |
| 3 | `r_i ← chE(squeeze)`, `i = 0 … m−1` | |
| 4 | `absorb(ū)` | `0x02` |
| 5 | `τ_l ← chE(squeeze)`, `l = 0 … ℓ_x−1` | |
| 6 | for `l < ℓ_x`: `absorb(g_l)`; `r_{x,l} ← chE(squeeze)` | `0x03` |
| 7 | `absorb(v_A ‖ v_B ‖ v_C)`; `ρ ← chE(squeeze)` | `0x04` |
| 8 | for `l < ℓ_y`: `absorb(g'_l)`; `r_{y,l} ← chE(squeeze)` | `0x05` |
| 9 | `absorb(s_0 ‖ … ‖ s_63)`; `f_p ← chE(squeeze)`, `p = 0 … 5` | `0x06` |
| 10 | for `l < 8+κ`: `absorb(g''_l)`; `r''_l ← chE(squeeze)` | `0x07` |
| 11 | `absorb(v)` | `0x08` |
| 12 | `idx-answers ← squeeze` × `⌈t/cnt⌉`; indices as in §6.1 | |
| 13 | Merkle path queries for each opened column (leaf then `ℓ_N` nodes) | |

Statement binding: `s, n, h` seed the chain; `c = leafStmt h n` is checked by `V` outside the
transcript. Every prover message is absorbed before any challenge that may depend on it; `r` is
squeezed after the root; the indices after `ū` and `v`.

### 6.3 Counts

Squeezes `m + 2ℓ_x + 1 + ℓ_y + 6 + (8+κ) + ⌈t/cnt⌉`; absorbs `3 + ℓ_x + ℓ_y + (8+κ) + 2`; Merkle
`t·(1 + ℓ_N)`. At `n = 16`: `97 + 56 + 3380 = 3533`; `n = 2^14`: `5156`; `n = 2^20`: `7774`. All
below `qV = 2^14`.

---

## 7. Byte format of `π_S(n)` (`n ≥ 1`)

`E` elements: 24 bytes, `c_0 ‖ c_1 ‖ c_2`, each `K` element 8 little-endian bytes (CompPoly's
`ByteCodec` for `BF64`, `Fields/Binary/BF64/Bytes.lean`, and for `Ext` over the vector codec,
`Fields/Extension/Bytes.lean:37` with `Data/Bytes/Vector.lean:89`: coefficient 0 first —
the Lean side uses its own `Field.lean` codec proved equal to these). `K` elements: 8 bytes.
Labels: 31 bytes. Fields in order, no padding, no length prefixes (every length is a function of
`n`):

| # | field | bytes |
|---|---|---|
| 1 | `root` | 31 |
| 2 | `ū` (`k` elements of `E`) | `24k` |
| 3 | outer round polynomials `g_0 … g_{ℓ_x−1}`, 4 coefficients each | `96·ℓ_x` |
| 4 | `v_A, v_B, v_C` | 72 |
| 5 | inner round polynomials, 3 coefficients each | `72·ℓ_y` |
| 6 | slices `s_0 … s_63` | 1536 |
| 7 | ring-switch round polynomials, 3 coefficients each | `72·(8+κ)` |
| 8 | `v` (`k` elements of `E`) | `24k` |
| 9 | for each of the `t` columns, in index order: column bytes (`8m`), then the path (`31·ℓ_N`) | `260·(8m + 31ℓ_N)` |

`leafSize n = 80 + 31 + 48k + 96ℓ_x + 72 + 72ℓ_y + 1536 + 72(8+κ) + 260(8m + 31ℓ_N)` (`ℓ_x = ℓ_y = 15+κ`),
and `leafSize 0 = 80`. Values (computed, §12):

| `n` | `κ` | shape `(m, k, N)` | `leafSize n` | of which columns |
|---|---|---|---|---|
| 1 | 0 | `(2, 2^7, 2^10)` | 95 719 B = 93.5 KiB | 84 760 |
| 16 | 4 | `(8, 2^9, 2^12)` | **143 711 B = 140.3 KiB** | 113 360 |
| 64 | 6 | `(16, 2^10, 2^13)` | 193 467 B = 188.9 KiB | 138 060 |
| 1024 | 10 | `(64, 2^12, 2^15)` | 457 843 B = 447.1 KiB | 254 020 |
| 2048 | 11 | `(128, 2^12, 2^15)` | 591 203 B = 577.3 KiB | 387 140 |
| 2^14 | 14 | `(256, 2^14, 2^17)` | 1 464 107 B = 1.40 MiB (`> proofCap`) | 669 500 |
| 2^20 | 20 | `(2048, 2^17, 2^20)` | 10.2 MiB | |

Node sizes: `8·(11 + ⌈|π₁|/8⌉ + ⌈|π₂|/8⌉)`. Smoke tree (`r = 2`, `n = 16`): leaf 143 711, level-1
node 287 512, **root 575 112 B = 561.6 KiB < 2^20** (margin 45%). Leaves fit `proofCap` up to
`n = 4096` (`κ = 12`, ≈ 800 KiB); the entry is unranked by `proofCap` at `n = 2^14` and, as §0
says, its `r = 8` root can never fit.

---

## 8. Completeness and the circuit lemmas

`Complete (Rel Vb) P V`: for every `H`, `c`, `w` with `Rel Vb c w`, `(V c ((P c w).run H)).run H = true`.

* Nodes: `Rel` gives `c = nodeStmt c₁ c₂`, `Vb c₁ π₁`, `Vb c₂ π₂`; `Vb_eq` gives sizes and `check`;
  `decode_encode` and `fits_of_rel` give the canonical parse. No oracle.
* Leaves, `n = 0`: `h := chainEnd s 0 = s`.
* Leaves, `n ≥ 1`: `leafSize` by construction; `c = leafStmt (chainEnd s n) n = leafStmt h n`;
  L-C3 (the witness satisfies `Sat`), L-S4 for the three sumchecks (the outer claim `0` is true
  because `Sat` holds at every row; the inner claim because `v_M` are computed honestly; the
  ring-switch claim by L-R3), L-R4, L-RS5 for both tests at every column (`Enc` is linear),
  L-M1 for every path, and the transcript is replayed by `V` from the same bytes under the same
  `H`. **No challenge value is excluded anywhere**: no division, no distinct-point requirement,
  no out-of-domain sample (`[D-10]`: perfect completeness over every `H`, as the contract demands).

The circuit lemmas in both directions are L-C1 (block) and L-C2/L-C3 (chain), §2.2.2–§2.3.
Extraction of `(s, n)` is the parse (`decodeWit_cons`); the soundness direction used by `final`
is L-C2 applied to `w_dec` (§9). The lemma ids are listed in §9.4.

## 9. The security argument in the potential form

Revised after BP-M1 and BP-M2: Merkle trees are read **per column** (a missing column is a
column the prover can never open, not a reason to stop charging), `Bad` also charges hits on
Fiat–Shamir states and repeated queries, and the potential's step law is argued with the bad
answers split off before the martingale step (BP-m3). Everything below is stated for a fixed
`n` with `1 ≤ n ≤ chainCap = 2^20`, whose shape `(κ, m, k, N, ℓ_N, J)` is §5.2 and §6.1; `t = 260`.

### 9.1 Objects read off the log

A log `L` is a list of entries `e = (q, a)` (`q : ByteArray`, `a : Digest`), indexed `e_0, …,
e_{|L|−1}`. `runLog` answers a query `q` by the **first** entry of `L` whose query is `q`
(`List.find?`), and returns `none` when there is none.

**Fields of a query.** For a query `q`:

* `labelsIn(q) : Finset (31 bytes)`: `{λ_0, λ_1}` if `q = 0x01 ‖ λ_0 ‖ λ_1` (63 bytes);
  `{root}` if `q = 0x20 ‖ st ‖ 0x01 ‖ root` (65 bytes, an `absorb(root)`); else `∅`.
* `stateIn(q) : Option Digest`: `some st` if `q = 0x20 ‖ st ‖ kind ‖ msg` (`|q| ≥ 34`) or
  `q = 0x30 ‖ st` (33 bytes); else `none`.
* `seedOf(q) : Option (Digest × ℕ × Digest)`: `some (s, n, h)` if `q = 0x10 ‖ s ‖ enc64 n ‖ h`
  (73 bytes); else `none`.

**Bad events.** `Bad(L)` holds iff there are indices `i < j` with:

* (i) *collision*: `q_i ≠ q_j` and `[a_i]_{31} = [a_j]_{31}`;
* (ii) *label hit*: `[a_j]_{31} ∈ labelsIn(q_i)`;
* (iii) *state hit*: `stateIn(q_i) = some a_j` (the full 32 bytes);
* (iv) *repeat*: `q_i = q_j`.

`Bad` is monotone under appending. Under `¬Bad(L)`: all answers of `L` are pairwise distinct
(by (i) and (iv), already after truncation to 31 bytes); `find?` on a query of `L` returns the
only entry with that query; every 31-byte label and every 32-byte state that occurs as a field
of a query of `L` either has its preimage entry (the entry whose answer it is) **earlier** in
`L` or has none at all.

**Partial trees per column.** For a 31-byte `root`, a column index `c < N` and a log `L`,
`col_L(root, c) : Option (8m bytes)` descends from the root, level `l = ℓ_N − 1` down to `0`,
with a current label `λ` (initially `root`):

* at a node level `l`: let `e = (q, a)` be the first entry of `L` with `[a]_{31} = λ` (none ⇒
  `none`); require `q = 0x01 ‖ λ_0 ‖ λ_1` (63 bytes; otherwise `none`); continue with
  `λ := λ_{bit_l(c)}`;
* at the bottom: let `e = (q, a)` be the first entry with `[a]_{31} = λ` (none ⇒ `none`);
  require `q = 0x00 ‖ bytes` with `|bytes| = 8m` (otherwise `none`); return `some bytes`.

`tree_L(root) : Fin N → Option (8m bytes)` is `c ↦ col_L(root, c)`, and the **filled matrix**
`U_L(root) ∈ K^{m×N}` has column `c` equal to the `m` `K`-elements of `col_L(root, c)` when it is
`some`, and the zero column when it is `none`. `tree_L(root)` is total and defined for every
log, with no "dangling" case: a missing column is simply a column the prover cannot open (L-M3).

**Transcript structure.** For an entry `e` of `L` with `stateIn(q_e) = some st`, `pred_L(e)` is
the entry of `L` whose answer is `st`, if any. Under `¬Bad(L)` it is unique and precedes `e`
(L-K7). A **chain** of `L` is a list `e_1, …, e_r` of entries of `L` such that `seedOf(q_{e_1}) =
some (s, n, h)` with `1 ≤ n ≤ chainCap`, `pred_L(e_{i+1}) = e_i` for `i < r`, and the queries
`q_{e_2}, …, q_{e_r}` match, in order, the kinds and lengths of §6.2 for the shape of `n`: an
absorb of kind `0x01` with a 31-byte message, then `m` squeezes, then an absorb of kind `0x02`
with `24k` bytes, then `ℓ_x` squeezes, then `ℓ_x` pairs (absorb `0x03` of 96 bytes, squeeze), an
absorb `0x04` of 72 bytes and a squeeze, `ℓ_y` pairs (absorb `0x05` of 72 bytes, squeeze), an
absorb `0x06` of 1 536 bytes and 6 squeezes, `8+κ` pairs (absorb `0x07` of 72 bytes, squeeze),
an absorb `0x08` of `24k` bytes, and `J` squeezes; a list that stops anywhere in this pattern is a
chain (the pattern need not be complete). The **statement** of the chain is `(s, n, h)`, its
**messages** are the message fields of its absorb entries (`root`, `ū`, the `g_l`, `(v_A, v_B,
v_C)`, the `g'_l`, the slices, the `g''_l`, `v`), its **challenges** are `chE` of its squeeze
answers (and the column indices, §6.1, of its last `J` answers). Since `pred_L` is a function, a
chain is determined by its last entry: **sums over chains are sums over entries of `L`**, and an
entry lies on at most one chain. Two chains may share a prefix (the adversary forks at an absorb
with a different message); a squeeze entry lies on exactly the chains through its state, all of
which share the prefix up to it. The **prefix** of a chain `T` is `L₀(T)`, the entries of `L`
strictly before `T`'s `absorb(root)` entry; under `¬Bad(L)` all of `T`'s entries come after it
in the order `e_1, e_2, …` (L-K7), and the chain's committed matrix is

`U_T := U_{L₀(T)}(root_T)`,

a function of `L₀(T)` and `root_T` alone; by L-M4 it equals `U_L(root_T)` for the whole `L`
and every extension of `L` that keeps `¬Bad`.

A **run's chain** (L-K4): if `(leafProg c π).runLog L = some b` and `¬Bad(L)`, the entries that
answer the run's queries, taken in the order the run asks them, form a chain of `L` whose
statement is the proof's `(s, n, h)` and whose messages are the proof's fields; if `b = true`
the chain is complete (through the `J` index squeezes).

### 9.2 The state function (round by round)

Fix a chain `T` of `L` with statement `(s, n, h)` such that **`chainEnd s n ≠ h`** (for a true
statement nothing is charged: `final` is met by the parsed witness `.leaf s n`), with `U := U_T`.
Every quantity below is a function of `T`'s entries (hence of a prefix of `L`); none looks at
later entries. "Far" and "close" are §5.5's `eClose` with the bound `e = ⌊(d−1)/3⌋`; in the close
case `q_dec`, `w_dec` are the unique decoding (L-RS4) and `z_dec := (w_dec ‖ pub(s, h))`,
`F(x) := (Az_dec)(x)·(Bz_dec)(x) + (Cz_dec)(x)`, which is **not** identically zero on the cube
(L-C2, since `w_dec` is Boolean and `chainEnd s n ≠ h`). The sumcheck polynomials are

`G(X) := eq(τ, X)·((Az_dec)̃(X)·(Bz_dec)̃(X) + (Cz_dec)̃(X))` (outer; individual degree `≤ 3`),
`G'(Y) := M̃_ρ(r_x, Y)·z̃_dec(Y)` (inner; degree `≤ 2`), `G''(U') := W̃(U')·q̃_dec(U')` (ring
switch; degree `≤ 2`), with the true round polynomials `g*_l(X) := Σ_{x' ∈ {0,1}^{ℓ−l−1}}
G(r_{<l}, X, x')` (likewise `g'*_l`, `g''*_l`) and the claims `cl_0 := 0`, `cl_{l+1} := g_l(r_{x,l})`
(likewise `cl'`, with `cl'_0 := v_A + ρ v_B + ρ² v_C`, and `cl''`, with `cl''_0 := T`).

The **doom predicate** `Doom_T(ρ)` after each round `ρ` of the chain, and the **escape event**
`Esc_T(ρ) := Doom_T(ρ−1) ∧ ¬Doom_T(ρ)`:

| round `ρ` | answers | `Doom_T(ρ)` | `Esc_T(ρ)` bound (fraction of the fresh answers) | lemma |
|---|---|---|---|---|
| start | — | true | — | |
| R0: `r_0 … r_{m−1}` | `m` squeezes | `FarDoom := far(U) ∧ ¬eClose(Σ_i r_i U[i], e)`, or `¬far(U)` | `far(U) ∧ eClose(Σ_i r_i U[i], e)`: `≤ d/\|E\| ≤ 2^{-169.2}` | L-RS2 |
| R1, coordinate `l`: `τ_l` | 1 squeeze each | `FarDoom ∨ P_{l+1} ≢ 0`, where `P_l(X_l, …, X_{ℓ_x−1}) := Σ_x eq((τ_{<l}, X_l, …), x)·F(x)` (multilinear; `P_0 ≢ 0`) | `P_l ≢ 0 ∧ P_{l+1} ≡ 0`: at most one `τ_l`, `≤ 1/\|E\|` | L-S2 |
| R2, round `l`: `r_{x,l}` | 1 squeeze each | `FarDoom ∨ cl_{l+1} ≠ g*_{l+1}(0) + g*_{l+1}(1)` (for `l = ℓ_x−1`: `cl_{ℓ_x} ≠ G(r_x)`) | doomed entering (`cl_l ≠ g*_l(0)+g*_l(1)`; the check `g_l(0)+g_l(1) = cl_l` passed, so `g_l ≠ g*_l`) and `g_l(r_{x,l}) = g*_l(r_{x,l})`: `≤ 3/\|E\|` | L-S1 |
| after `(v_A, v_B, v_C)` | absorb | `FarDoom ∨ (v_A, v_B, v_C) ≠ ((Az_dec)̃(r_x), (Bz_dec)̃(r_x), (Cz_dec)̃(r_x))` — implied by the previous row when the check `cl_{ℓ_x} = eq(τ, r_x)·(v_A v_B + v_C)` passes (no division: equal triples would make the two sides of the previous row equal) | — | |
| R3: `ρ` | 1 squeeze | `FarDoom ∨ cl'_0 ≠ Σ_y M̃_ρ(r_x, y)·z_dec(y)` | the triple is wrong and `v_A + ρ v_B + ρ² v_C = v*_A + ρ v*_B + ρ² v*_C`: `≤ 2/\|E\|` | L-S3 |
| R4, round `l`: `r_{y,l}` | 1 squeeze each | `FarDoom ∨ cl'_{l+1} ≠ g'*_{l+1}(0) + g'*_{l+1}(1)` (for `l = ℓ_y−1`: `cl'_{ℓ_y} ≠ M̃_ρ(r_x, r_y)·z̃_dec(r_y)`) | as R2, degree 2: `≤ 2/\|E\|` | L-S1 |
| after the slices | absorb | `FarDoom ∨ δ ≠ 0`, `δ_i := s_i + Q̃_i^{dec}(r_hi)` — implied by the previous row when the check `cl'_{ℓ_y} = M̃_ρ(r_x, r_y)·((1 + r_ytop)·Σ_i eq(r_lo, i) s_i + r_ytop·pub̃(r_u))` passes (equal `δ = 0` would make `z̃_V = z̃_dec(r_y)`) | — | |
| R5, stage `p`: `f_p` | 1 squeeze each (6) | `FarDoom ∨ ∃ k < M_p, π^{(p+1)}_k ≠ 0`, with `π^{(p)}_k := Σ_i x^i·(Φ_p(δ_i))^{2^k}` (`Φ_p` the map after `p` stages, `Φ_0 = id`); entering: `∃ k < 2M_p = 2^{6−p}, π^{(p)}_k ≠ 0`, which at `p = 0` is L-R1 | `π^{(p+1)}_k = π^{(p)}_k + f_p^{2^k}·π^{(p)}_{k+M_p}` for `k < M_p`, so all vanish for at most one `f_p`: `≤ 1/\|E\|` | L-R2 |
| after R5 | — | `FarDoom ∨ T ≠ T*`, `T* := Σ_{u'} W(u')·q_dec(u')` — this is `π^{(6)}_0 = Σ_i x^i Φ(δ_i) = T + T*` (L-R3: `T* = Σ_i x^i Φ(Q̃_i^{dec}(r_hi))`) | — | L-R1, L-R3 |
| R6, round `l`: `r''_l` | 1 squeeze each | `FarDoom ∨ cl''_{l+1} ≠ g''*_{l+1}(0) + g''*_{l+1}(1)` (for `l = 7+κ`: `cl''_{8+κ} ≠ W̃(r'')·q̃_dec(r'')`) | as R2, degree 2: `≤ 2/\|E\|` | L-S1 |
| after `v` | absorb | `FarDoom ∨ v ≠ Σ_i a_i·q_dec[i]` (in `E^k`) — implied by the previous row when the check `cl''_{8+κ} = W̃(r'')·Σ_j b_j v_j` passes: `v = Σ_i a_i q_dec[i]` would give `Σ_j b_j v_j = q̃_dec(r'')` (L-E3) and so equal sides; **no division by `W̃(r'')`**, and the argument holds when `W̃(r'') = 0` | — | |
| R7: the `J` index answers | `J` squeezes | some decoded index lies in `D`, where `D := D_far := {c : Enc(ū)_c ≠ Σ_i r_i U[i][c]}` if `far(U)` (then `\|D\| > e` under `FarDoom`), and `D := D_close := {c : Enc(v)_c ≠ Σ_i a_i U[i][c]}` if `¬far(U)` (then `\|D\| ≥ d − e` under the previous row, by L-RS1 and the decoding agreeing outside `S`) | all `t` indices miss `D`: `≤ (1 − \|D\|/N)^t`, i.e. `< (17/24)^{260} = 2^{-129.35}` (far), `< (5/12)^{260} = 2^{-328}` (close) | L-RS3 |
| end | — | the final checks fail: the index `c* ∈ D` is opened; a verifying path makes the opened column `U`'s column `c*` (L-M3), at which the mode's equation (`Enc(ū)_{c*} = Σ_i r_i U[i][c*]` resp. `Enc(v)_{c*} = Σ_i a_i U[i][c*]`) is false; so `leafProg` rejects | — | L-K3 |

Notes. (1) In far mode (`FarDoom`), every later `Doom_T(ρ)` holds outright and no escape is
possible at R1–R6; the per-round bounds hold trivially (the escape set is empty). (2) In close
mode, `q_dec` is fixed by `U` alone, before any challenge. (3) The escapes of R0 and R7 are
events over a block of `m` resp. `J` answers; §9.3 charges them answer by answer through a
conditional count. (4) A chain whose statement is true (`chainEnd s n = h`) has no doom
predicate and is never charged. (5) A chain that stops before a round is complete, or whose
next entry does not match §6.2, is charged nothing beyond its partial-round term.

### 9.3 The potential

For a chain `T` whose last entry is the `j`-th squeeze of a multi-answer round (`1 ≤ j < m` in
R0, `1 ≤ j < J` in R7) and whose doom entering the round holds, the **conditional escape count**
is

* R0: `p_T(L) := #{(a_{j+1}, …, a_m) ∈ Digest^{m−j} : far(U) ∧ eClose(Σ_{i<m} chE(a_i)·U[i], e)} / 2^{256(m−j)}`
  (with `a_1 … a_j` the chain's answers so far; `0` when `¬far(U)`);
* R7: `p_T(L) := #{(a_{j+1}, …, a_J) ∈ Digest^{J−j} : all t indices decoded from (a_1, …, a_J) miss D_T} / 2^{256(J−j)}`;

and `p_T(L) := 0` for every other chain. `Esc(L)` holds iff some chain `T` of `L` has a complete
round `ρ` with `Esc_T(ρ)`. The potential:

```
μ(L) := 1                                    if Bad(L) ∨ Esc(L)
μ(L) := min(1, Σ_{T chain of L} p_T(L))      otherwise
```

(the sum is over the entries of `L` that end a partial multi-answer round, §9.1).

* `empty`: `μ [] = 0` (no entries, no chains).
* `step`. Let `q ∉ L.map Prod.fst`, `L.length < logCap = 2^96`, `μ L < 1`; so `¬Bad(L)`,
  `¬Esc(L)`, `X := Σ_T p_T(L) < 1` and `μ L = X`. Write `L_a := L ++ [(q, a)]`. Then

  `Σ_a μ(L_a) ≤ #{a : Bad(L_a)} + Σ_{a : ¬Bad(L_a)} ([Esc(L_a)] + Σ_T p_T(L_a))`

  (on `Bad(L_a)` the summand is `1`; otherwise `min(1, ·) ≤ ·`). The first term is at most
  `L.length·(3·2^8 + 1) < 2^96·(3·2^8 + 1)`, i.e. a fraction `3·2^{-152} + 2^{-160}` of `2^256`
  (L-K1). For the second, under `¬Bad(L_a)` the new entry is a **leaf** of the transcript
  forest: its answer is no earlier state (iii), no earlier label (ii) and no earlier answer (i),
  so every chain of `L` is a chain of `L_a` with the same entries, prefix, `U_T`, messages and
  challenges (its `p_T` and its escapes are unchanged), and the only new chain, if any, is one
  chain `T` of `L` extended by the new entry (L-K8; the new entry has a unique predecessor, or is
  a seed, which starts a chain in the doomed initial state with `p = 0`). By the kind of the new
  entry:
  - an absorb, a Merkle query, a seed, or an entry that matches no chain: no term changes;
  - a single-answer squeeze of `T` (R1–R6): `[Esc(L_a)]` is `1` for at most `3·2^{64}` answers
    (`chE` has exactly `2^{64}` preimages per element of `E`; at most `3` elements are bad):
    fraction `≤ 3/|E| = 3·2^{-192}`;
  - the first answer of a multi-answer round of `T`: `Σ_a p_T(L_a) = 2^256·Pr[Esc_T(round)]`,
    the round's escape probability (L-K2a), `≤ 2^{-169.2}` (R0, L-RS2 with the `2^{64m}`
    preimage count) or `< 2^{-129.35}` (R7, L-RS3);
  - a middle answer: `Σ_a p_T(L_a) = 2^256·p_T(L)` (L-K2b);
  - the last answer: `p_T` disappears and `Σ_a [Esc(L_a)] = 2^256·p_T(L)` (L-K2c).

  In every case `Σ_{a : ¬Bad(L_a)} (…) ≤ Σ_a (X + Δ_a) ≤ 2^256·(X + δ)` with `δ` the kind's
  bound (the sum over the `¬Bad` answers of the intended value is at most the sum over all
  answers, every term being non-negative). Hence
  `Σ_a μ(L_a) ≤ 2^256·(X + 3·2^{-152} + 2^{-160} + 2^{-129.35}) ≤ (μ L + ε)·2^256` with
  **`ε = 2^{-129}`** (`2^{-129.3499} + 3·2^{-152} + 2^{-160} = 2^{-129.3499…} < 2^{-129}`;
  `logs/blueprint-review/check.out`, "eps total").
* `final`: `(V c π).runLog L = some true`, `μ L < 1`, `L.length ≤ logCap`. Then `¬Bad(L)` and
  `¬Esc(L)`. Node proofs: `checkNode_sound` (no query). Leaf proofs with `n = 0` or with
  `chainEnd s n = h`: the parsed witness `.leaf s n` is in `Rel` (`n ≤ chainCap` and
  `c = leafStmt h n` are checked by `leafProg`). Leaf proofs with `chainEnd s n ≠ h`: the run's
  entries form a complete chain `T` of `L` (L-K4); `Doom_T` holds at the start and, since no
  round of `T` escaped (`¬Esc(L)`), after every round through R7; a chain doomed after R7 is
  rejected by `leafProg` (L-K3, through L-M3) — contradiction with `some true`.

The `KState` is built in `Soundness/KS.lean`; `KS` follows with `qV` from L-Q1. (`ε = 2^{-129}`
is declared as `2^{-128}` in `claim.json`; `CertificateR.bounds` compares.)

### 9.4 Lemma inventory (statement, module)

Circuit and chain (`Blake2sR1CS.lean`, `Chain.lean`):

* **L-C1** `block_sound`, `block_complete` (§2.2.2), with `holds_chainBlock_imp (hz : z 512 =
  true)` and `bounded_chainBlock` (§2.2.1).
* **L-C2** `chain_sound : (∀ u, w u ∈ {0,1}) → Sat n s h (w ‖ pub s h) → chainEnd s n = h`.
* **L-C3** `chain_complete : Sat n s (chainEnd s n) (chainWitness s n ‖ pub s (chainEnd s n))`
  and `chainWitness` Boolean with `pos 512 = 1` in every block.
* **L-C4** `walk_eq_sum` (§2.4.2, the sum over `k ≠ 512`); `shift_mle : ∀ t t' ∈ {0,1}^κ,
  S̃(t,t') = [t' + 1 = t]`; `matrix_mle_eq`: the formulas of §2.4 (with `A0, B0` the row forms
  of `chainBlock` with row 512 cleared) equal `Σ_{x,y} eq(r_x,x)eq(r_y,y)·M(x,y)` for
  `M ∈ {A,B,C}`.

Multilinear (`MLE.lean`): **L-E1** `eq_sum_one : Σ_u eq(r,u) = 1`; **L-E2** `eq_mle : Σ_u eq(a,u)eq(u,b)
= eq(a,b)`; **L-E3** `mle_split` (tensor split of variables); **L-E4** `eq_frob : eq(r,u)^{2^k} =
eq(r^{2^k},u)` for `u` Boolean.

Sumcheck (`Sumcheck.lean`): **L-S1** `round_bad_le : ` for `g ≠ g*` of degree `≤ d` with
`g(0)+g(1) = g*(0)+g*(1)`, `#{r : g(r) = g*(r)} ≤ d` (Mathlib `Polynomial.card_roots'`);
**L-S2** `zerocheck_bad_le : ` for a nonzero multilinear `P` in `ℓ` variables, drawing coordinates
one at a time, each coordinate makes the restriction vanish for at most one value;
**L-S3** `batch_bad_le : (v_A,v_B,v_C) ≠ (t_A,t_B,t_C) → #{ρ : Σ ρ^i v_i = Σ ρ^i t_i} ≤ 2`;
**L-S4** `sumcheck_complete`: the honest round polynomials pass every check for every challenge.

Ring switching (`RingSwitch.lean`): **L-R1** `ring_inj : δ ∈ E^{64}, δ ≠ 0 → ∃ k < 64,
Σ_i x^i δ_i^{2^k} ≠ 0` (Annex A §A.3: with the `F₂`-coordinates `Δ_w ∈ K`, the `K`-bases
`{1, y^{2^k}, y^{2^{k+1}}}` for each `k < 64`, and the 64 distinct conjugates `x^{2^k}`; the two
families of facts are kernel-decided in `Field.lean`, see §10 — `y ∈ F_8` makes `y^{2^k}`
3-periodic, so `ybasis` is three determinants with `F₂` entries, and `conj_distinct` may come
from the modulus's irreducibility certificate instead of 64 squaring chains; either proof is
acceptable, the statements are fixed); **L-R2** `stage_bad_le_one` (leanerVM
`card_stage_zero_le_one`, Mathlib-only, copied): a family with some `π_k ≠ 0`, `k < 2M`, keeps
some `π_k ≠ 0`, `k < M`, after the stage `(M, f)` for all `f` but at most one;
**L-R3** `ring_complete : Σ_{u'} Φ(eq(r,u'))·q(u') = Σ_i x^i Φ(Q̃_i(r))` for `q(u') = Σ_i Q_i(u')x^i`,
`Q_i` Boolean; **L-R4** `weight_mle : W̃(r'') = Σ_k c_k eq(r^{2^k}, r'')`; **L-R5** `phi_eq_sum`
(`frobMap_eq_sum`, copied).

Code and PCS (`RS.lean`, `Proximity.lean`, `Ligero.lean`): **L-RS1** `code_dist : c, c' ∈ C, c ≠ c'
→ #{i : c_i ≠ c'_i} ≥ N − k + 1` (from `basis_deg : deg X_j = j`, monic); **L-RS2** (AHIV22
4.3–4.5, counting form) `far_bad_le : 3e < d → d < |E| → ¬ eClose U e → #{r ∈ E^m : Δ(Σ r_i U[i], C)
≤ e} ≤ d·|E|^{m−1}`. Its proof is a **port with provenance** of ArkLib's sorry-free
`Data/CodingTheory/ProximityGap/AHIV22.lean` and `AHIV22Support.lean` (Apache-2.0; the
affine-line lemma `exists_codewords_agree_of_many_close_scalars`, `dist_interleaved_code_to_code_lb`,
`e_le_dist_over_3`, `prob_of_bad_pts`), with one change: ArkLib samples uniformly from the row
span, R0 samples `r ∈ E^m`, so the double count is redone directly over `E^m` along a fixed
`β` with `Σ β_i U[i] = v*` (the same proof, no pushforward lemma); **L-RS3** `miss_le : |D| ≥ δN →
#{index tuples missing D} ≤ (1−δ)^t·N^t` (exact: `(N − |D|)^t`), lifted to the `J` answers by the
exact uniformity of §6.1's chunking; **L-RS4** `close_unique` and `close_in_K` (§5.5); **L-RS5**
`encode_complete`: `Enc(Σ r_i Q[i]) = Σ r_i Enc(Q[i])` (linearity) and the tensor evaluation equals
`Enc(·)_c`.

Merkle and log (`Merkle.lean`, `Soundness/Log.lean`):

* **L-M1** `path_complete`: for every `H`, the prover's path for column `c` verifies against the
  root it computed.
* **L-M2** `tree_of_log` (a positive control for `tree_L`): if the prover's build queries for
  `U` are in `L`, answered as `H` answers them, then `tree_L(root) c = some (column c of U)` for
  every `c`.
* **L-M3** `open_binding` (restated; absorbs the former L-M4's "no completion" clause):
  `¬Bad(L) → L₀ <+: L → (∃ e ∈ L \ L₀ at the cut, root ∈ labelsIn(q_e)) →
  (verifyPath root c col path).runLog L = some true → tree_{L₀}(root) c = some col`.
  Here `verifyPath` is `V`'s path check (recompute `λ(c)` from `col`, climb with the sibling
  labels, compare with `root`). Proof: top-down along the path; at each level the path's query
  is answered in `L` by an entry whose truncated answer is the current label, and by (i) and
  (iv) that entry is the first one with that truncated answer, so `col_L` takes the same step;
  by L-M4 `col_{L₀} = col_L`. Consequence: a column with `tree_{L₀}(root) c = none` has no
  verifying path in `L`.
* **L-M4** `tree_prefix` (restated): `¬Bad(L) → L₀ <+: L → (some entry of L at or after the
  cut has root ∈ labelsIn(q)) → tree_{L₀}(root) = tree_L(root)`. Proof: every entry of the tree
  under `root` precedes the first entry whose query carries `root` (else a label hit (ii)), by
  induction on the depth, and `col` only reads first entries by truncated answer.

Knowledge state (`Soundness/Log.lean` for L-K1, L-K4, L-K7, L-K8; `Soundness/KS.lean` for the
rest):

* **L-K1** `bad_step_le` (restated): `¬Bad(L) → q ∉ L.map Prod.fst → #{a : Digest | Bad(L ++
  [(q,a)])} ≤ L.length·(3·2^8 + 1)`. Count: (i) at most `L.length` truncated answers, each with
  `2^8` full answers; (ii) at most `2·L.length` labels in the queries of `L`, each `2^8`; (iii) at
  most `L.length` states; (iv) impossible for a fresh `q`. With `L.length < 2^96` the fraction is
  `< 3·2^{-152} + 2^{-160}`.
* **L-K2a** `first_answer`: for a chain `T` of `L` entering a multi-answer round (doomed), the
  new entry being its first squeeze, `Σ_a p_T(L ++ [(q,a)]) = 2^256·Pr_T[escape]`, where the
  right side is the counting probability of §9.2's R0 or R7 escape event over all `m` resp. `J`
  answers; **L-K2b** `middle_answer`: for `1 ≤ j < m−1` resp. `j < J−1`,
  `Σ_a p_T(L ++ [(q,a)]) = 2^256·p_T(L)`; **L-K2c** `last_answer`: `Σ_a [Esc_T(round) in L ++
  [(q,a)]] = 2^256·p_T(L)`. All three are the splitting of a count over `Digest^{J−j}` by its
  first coordinate.
* **L-K3** `accept_not_doomed`: for a complete chain `T` of `L` with `¬Bad(L)` and `Doom_T`
  after R7, `(leafProg c π).runLog L ≠ some true` for the proof `π` carrying `T`'s messages (the
  index `c* ∈ D` is opened; L-M3 identifies the opened column with `U`'s; the mode's column
  equation fails there).
* **L-K4** `runLog_chain` (restated): `¬Bad(L) → (leafProg c π).runLog L = some b →` the
  entries `find?`-answering the run's queries, in the order asked, form a chain of `L` with the
  proof's statement and messages; `b = true →` the chain is complete. The ordering part
  (each entry after its predecessor) is L-K7; the matching part is the shape of `leafProg`'s
  queries (§6.2) and `find?`.
* **L-K5** `kstate : KState (Rel Vb) V E 2^{-129}` with `μ` of §9.3 (restated for the amended
  contract: `empty`, `step` with `(μ L + ε)·2^256`, `final` with `L.length ≤ 2^96`).
* **L-K6** `ks : KS (Rel Vb) V E 2^{-129} 2^{14}`.
* **L-K7** `pred_unique_lt`: `¬Bad(L) → stateIn(q_e) = some st → ` at most one entry of `L` has
  answer `st`, and if `e'` does then `e'` precedes `e` in `L`.
* **L-K8** `fresh_leaf`: `¬Bad(L ++ [(q,a)]) →` the chains of `L ++ [(q,a)]` are the chains of
  `L` (with the same `pred`, prefix `L₀`, `U_T`, messages and challenges) plus at most one chain
  ending in the new entry, which extends a chain of `L` or is a new seed.

Query bound (`Verifier.lean`): **L-Q1** `queries_le : ∀ H c π, ((V c π).queries H).length ≤ 2^{14}`
(the structured count of §6.3 for `n ≤ 2^{20}`; zero for rejects before the first query and for
nodes).

Decoder (`Decode.lean`): `packFast_eq`, `bytesAtF_eq`, `decodeWitF_eq`, `decodeF_eq`,
`encodeF_eq` (copied from S2a, §1.2.1).

Certificate (`Submission.lean`): `Vb_eq`, `check_eq`, `checkNode_sound`, `fits_of_rel`,
`certificate`, `certified` (the rendered challenge).

---

## 10. Lean module plan

Root `submissions/spartan-chain/`, flat like `submissions/baseline/`, modules `SpartanChain.*`.
Imports allowed: Mathlib, `RecursionFast.Contract`, `RecursionFast.Library`, CompPoly's
`BF64`/`Ext3` closure (the regenerated allowlist, DESIGN-v3 §7.4). Everything else is copied with a
provenance line (leanerVM: Apache-2.0; ArkLib: used as a guide, not copied verbatim).

| module | content | depends on | parallel group |
|---|---|---|---|
| `Field.lean` (other agent) | computable word-level `F`, `EF` with `Field`, `CharP 2`, `DecidableEq`, `Finite`; `toBF64 : F ≃+* BF64`, `toExt3 : EF ≃+* Ext3`; `F.ofUInt64/toUInt64`, `F.x` (the generator), `EF.mk c₀ c₁ c₂`, `EF.c₀/c₁/c₂`, `EF.ofF`, `EF.y`; byte codecs `F.toBytes : F → Vector UInt8 8`, `EF.toBytes : EF → Vector UInt8 24`, `EF.ofBytes` (total), proved equal to CompPoly's; `sq`, `frob k := (·)^(2^k)` by `k` squarings; `Nat.card EF = 2^192`; two decided facts: `conj_distinct : (List.range 64).map (fun k => F.x^(2^k)) nodup` and `ybasis : ∀ k < 64, det[1, y^(2^k), y^(2^(k+1))]_{K-coordinates} ≠ 0` (both by `decide +kernel` on the word-level arithmetic) | CompPoly | A |
| `Oracle.lean` | `OProg.bind`, `map`, `queries_bind`, `runLog_bind`; byte helpers | contract | A |
| `Decode.lean` | the S2a entry's linear decoder, copied with a provenance line (§1.2.1): `packFast`, `bytesAtF`, `decodeWitF`, `decodeF`, `witWordsF`, `encodeF` and `packFast_eq`, `bytesAtF_eq`, `decodeWitF_eq`, `decodeF_eq`, `encodeF_eq` | contract `Library` | A (mechanical) |
| `MLE.lean` | `eq`, `mle` over `Fin (2^ℓ) → R`, tables, L-E1…L-E4, tensor split | `Field` | A |
| `Blake2sR1CS.lean` | the copied framework and circuit, generic form type, both instances, L-C1, `walk_eq_sum` | `Field`, contract `Blake2s` | A (largest copy; can start on `BF64` directly) |
| `Chain.lean` | regions, `Sat`, `pub`, `chainWitness`, `S̃`, matrix MLE formulas, L-C2…L-C4 | `Blake2sR1CS`, `MLE` | B |
| `Sumcheck.lean` | verifier round logic over an abstract claim, honest rounds for products of linear factors, L-S1…L-S4 | `MLE` | A |
| `RS.lean` | domain, `W_i`, `X_j`, `Enc`, L-RS1, L-RS5 | `Field` | A |
| `Proximity.lean` | `eClose`, L-RS2 (AHIV counting: a port with provenance of ArkLib's `AHIV22.lean` and `AHIV22Support.lean`, the double count redone over `E^m`, §9.4), L-RS3, L-RS4 | `RS` | B (the one hard mathematics module; independent of the protocol) |
| `RingSwitch.lean` | `frobMap` and its lemmas (copied), stages, `c_k` table, `Φ`, `W̃`, `T`, L-R1…L-R5 | `Field`, `MLE` | A |
| `Merkle.lean` | build, path, `verify` as `OProg`, L-M1, L-M2 | `Oracle` | A |
| `Transcript.lean` | state, `absorb`, `squeeze`, `chE`, index chunking, fiber-count lemma | `Oracle`, `Field` | A |
| `Ligero.lean` | commit (prover), open, verify (`OProg`), shape function, sizes | `RS`, `Merkle`, `Transcript` | B |
| `Verifier.lean` | `leafProg`, `checkNode` (over `decodeF`/`encodeF`), `check` (with the `π.size < 8` guard), `V`, `leafSize`, L-Q1 | `Chain`, `Sumcheck`, `RingSwitch`, `Ligero`, `Decode` | C |
| `Prover.lean` | `proveLeaf`, `P` | same | C |
| `Submission.lean` | `submission`, `Vb_eq`, `check_eq`, `checkNode_sound`, `fits_of_rel` | `Verifier`, `Prover` | C |
| `Completeness.lean` | §8 | all of C | D |
| `Soundness/Log.lean` | §9.1 objects (`labelsIn`, `stateIn`, `seedOf`, `Bad`, `col_L`, `tree_L`, `U_L`, `pred_L`, chains, `L₀(T)`, `U_T`), L-M3, L-M4, L-K1, L-K4, L-K7, L-K8 | `Merkle`, `Transcript`, `Verifier` | D |
| `Soundness/Spartan.lean` | the state function's algebraic rounds (§9.2 R1–R6 and the absorb rows), their bounds | `Chain`, `Sumcheck`, `RingSwitch` | D |
| `Soundness/PCS.lean` | R0, R7, the modes (`FarDoom`, `D_far`, `D_close`), decoding, L-RS2 and L-RS3 applied to the filled `U_T` | `Proximity`, `Ligero` | D |
| `Soundness/KS.lean` | `p_T`, `Esc`, `μ`, L-K2a/b/c, L-K3, L-K5, L-K6 | all of D | E |
| `Controls.lean` | positive and negative controls (§10.1) | all | D |
| `Solution.lean` | the rendered challenge with `submission` and `certified` | `Submission`, `Completeness`, `Soundness/KS` | E |
| `Run.lean` | `spartan-run`: `verify`, `prove-leaf`, `prove-node`, and the KAT dumps of §11.3 | C | C |

Groups A are independent of each other (five to seven agents); B needs A; C needs B; D needs C;
E closes. `Proximity.lean` and `Blake2sR1CS.lean` are the long poles and need nothing from the
protocol modules.

### 10.1 Controls (non-vacuity)

For every definition the certificate relies on, one positive and one negative control, as
theorems or by `decide`/`rfl` on small instances. **The full-size objects are out of reach of
kernel `decide`** (leanerVM checks its circuit with `#guard`, which the source rule refuses; a
kernel decision over `2^16` rows of `2^14`-bit forms has not been measured), so the controls on
`chainBlock` and `Sat` are stated as theorems first, with kernel-decided known-answer tests only
on reduced objects, each measured in the RESULT before it is relied on:

* `chainBlock`: positive, `block_complete` instantiated at an RFC test vector, the output read
  by `readDigest` equal to `chainStep` by `native`-free evaluation of the contract's `blake2s`
  (`decide +kernel` on the 32 output bytes, not on the circuit); negative, a single row of
  `chainBlock` (one gate) evaluated against the honest trace with that gate's output bit flipped
  fails `Holds` at that row (one `2^14`-bit form dotted with one block; kernel `Nat` bit
  operations; measure first). Fallback: a `κ = 0` theorem from L-C1.
* `Sat`: positive, L-C3 at `n = 1, 2` (a theorem instance); negative, the contrapositive of
  L-C2: `¬ Sat 1 s h' (chainWitness s 1 ‖ pub s h')` for a concrete `h' ≠ chainStep s` (a
  one-line theorem), and, measured first, a flipped-bit witness failing one row as above.
* `S̃` at `κ = 3` equals the Boolean shift table and differs from the identity (`decide`);
  `Enc` on `k = 4` against naive polynomial evaluation, and a nonzero message has a nonzero
  codeword; `eClose` on a toy `2×8` matrix both ways; `Φ` with all `f_p = 0` is the identity,
  with one `f_p ≠ 0` is not; the transcript reproduces a fixed known answer under
  `blake2sOracle`; `tree_L` on a 4-leaf log gives every column (L-M2 instance) and `none` for a
  column whose leaf query is absent; `Bad` holds on a two-entry log with a state hit and fails
  on the honest 4-leaf log; `leafSize` canaries: `V` rejects the honest proof with a byte
  appended, truncated, with a flipped statement bit; `checkNode` rejects a swapped child digest;
  `decodeF` and `encodeF` on the smoke root's bytes agree with the library's functions
  (`decodeF_eq` instance, `rfl`). The AHIV lemma's hypotheses are non-vacuous: a control exhibits
  `U` far with the bound tight on a toy code.

---

## 11. Rust crate plan

Crate `submissions/spartan-chain/native/` (`spartan-chain-prover`), no network, stable Rust. The
runner interface of DESIGN-v3 §6.3 (`tree DIR`, `node DIR`) plus `prove-leaf`.

| module | source | notes |
|---|---|---|
| `field` | leanVM `crates/primitives/src/field/{gf2_64,gf2_64x3}.rs` | same modulus (`R64 = 0x1B`), same `F192 {c0,c1,c2}` limb order; this VM has no `pclmulqdq`, so add scalar×vector tables (E3) for the NTT and folds; a unit test checks 1 000 products against the Lean dumps |
| `hash` | `blake2` crate (or leanVM `hash.rs`) | the oracle is `blake2s256(0x52 ‖ q)`; the chain step and `leafStmt` as in `Relation.lean` |
| `circuit` | leanVM `crates/flock/src/{gf2,hash,witness}.rs` for the gate order and witness bits | the slot layout is leanerVM's transcription of this code; **verify against the Lean `rowOf` dump** (§11.3) before anything else; the chain block adds the constant rows (no gates) |
| `walk` | fresh (mirror the Lean walk) or leanVM `bilinear_walk_pair` | needed by the prover for `Az, Bz` tables and by the KAT |
| `r1cs` | fresh: regions, `pub`, `Sat` check (debug) | |
| `sumcheck` | fresh (leanVM's zerocheck/lincheck have the univariate skip; not ours) | |
| `ring_switch` | leanVM `crates/pcs/src/ring_switch.rs` for `Φ` and the weight | same stage order |
| `ntt` | leanVM `crates/pcs/src/ntt/additive_ntt_f64.rs` adapted to the **unnormalised** `W_i` (twiddles `W_i(ω)` and `κ_i`), or a fresh `O(N log N)` LCH butterfly; KAT against naive `Enc` | |
| `ligero`, `merkle`, `transcript`, `proof` | fresh | byte formats of §6–§7 |
| `bin` | `tree`, `node`, `prove-leaf`, `verify` (native, for self-check only), `dump-*` | |

Prover cost at `n = 16`: 16 compressions of witness generation, `2^18` rows of sumcheck tables,
`8 × 512 → 4096` encodings, a 4 096-leaf tree, ≈ 100 k `E`-multiplications: negligible. At
`n = 2^14`: `2^28` sumcheck rows (the outer sumcheck over `2^29` rows dominates: about
`3·2^29` `E`-multiplications per round halving, ≈ `2^31` in all) — minutes with the naive loop
multiplication; acceptable for an unranked size.

### 11.3 Known-answer harness (`kat/`)

`spartan-run dump-*` (Lean) and `spartan-chain-prover dump-*` (Rust) write the same text files;
`kat.py` diffs them: (1) `field`: 1 000 random products in `K` and `E`, squarings, byte codecs;
(2) `circuit`: the row list of `chainBlock` (`k, a-form bits, b-form bits`) — 16 384 rows;
(3) `walk`: `A0̃, B0̃` at 8 random points; (4) `encode`: `Enc` of 8 random messages at `k = 512`;
(5) `transcript`: the state sequence of a fixed leaf under `blake2sOracle`; (6) **`proof`: the
Lean `P` and the Rust prover produce byte-identical leaf proofs** for 4 fixed `(s, n)`,
`n ∈ {1, 2, 16, 64}`; (7) the Rust proof verifies under the compiled Lean `check`. The smoke tree
and the canaries are `check.sh`'s (as S2a's `smoke.py`).

---

## 12. Expected verifier cost and sizes

Per leaf verification (Lean `check`, compiled), counting `E`-multiplications as 6 `K`-multiplications
(Karatsuba) and `E×K` as 3:

| item | `n = 16` | `n = 2^14` |
|---|---|---|
| eq tables (`2·2^14`) and the block walk | ≈ `2^16` `E`-mul | same |
| `Ã,B̃,C̃` extra terms, `pub̃`, `S̃`, `eq(τ,r_x)` | ≈ 3 000 `E`-mul | ≈ 3 500 |
| three sumchecks (Horner, consistency) | ≈ 200 `E`-mul | ≈ 300 |
| slices, `Φ` table, `T` (64 applications), `W̃(r'')` | ≈ 1 300 `E`-mul + 4 900 squarings | ≈ 2 000 + 5 000 |
| Ligero: `Enc(ū)_c`, `Enc(v)_c` at 260 columns (`260·(k + 2·3k)` `K`-mul with the column tensor `(X_j(ω_c))_j` built once and shared by the two dot products; `2·260·4k` if not shared — either is allowed, the protocol is unchanged) | ≈ `0.9·10^6` `K`-mul | ≈ `3.0·10^7` `K`-mul |
| column combinations `Σ r_i U[i][c]`, `Σ a_i U[i][c]` (`2·260·3m`) | ≈ 12 000 `K`-mul | ≈ 400 000 |
| **field total (K-mul equivalents)** | **≈ 1.4·10^6** | **≈ 3.1·10^7** |
| oracle queries | 3 533 | 5 156 |
| compressions: FS absorbs (`≈ (leafSize − column bytes)/64 + #absorbs`; the column openings are not absorbed) + squeezes + Merkle (`260·(⌈(2+8m)/64⌉ + ℓ_N)`) | ≈ 530 + 100 + 3 640 ≈ **4 300** | ≈ 12 500 + 400 + 13 000 ≈ **26 000** |
| node check: linear decode and re-encode (`decodeF`, `encodeF`), per node of the tree | smoke root: three nodes, 1.15 MB in all; S2a's same code: ≤ 1.25 s per 1 MiB adversarial proof (`logs/V3-S2/fix/check/smoke.log`); measured by this entry's `check.sh` | — |

With a word-level `K`-multiplication at `0.1–0.5 µs` (unmeasured; E2's unverified loop ran at
1.47 µs, leanVM's Rust at 25 ns) and 5 µs per compression (S2a's measurement): **≈ 0.2–0.7 s per
leaf at `n = 16`**, so ≈ 1–3 s for the smoke root (4 leaves) plus the node decoding; `≈ 3–16 s`
at `n = 2^14`. The walk (`2^16` `E`-mul ≈ 0.4 M `K`-mul) is a fixed cost per leaf. The smoke-root
estimate straddles `T_V = 2 s` (DESIGN-v3 §6.5); this does not matter for R1, which **cannot be
ranked** (its `r = 8` root cannot fit `proofCap`, §0 and §13 item 1), so `T_V` removes nothing
that R1 could have had; `verify_s = 60 s` (§6.6) is the bound that binds, with a wide margin.

Sizes: §7's table and the smoke root 561.6 KiB. Script (reproducible):

```python
t=260
def shape(n):  # kappa, log m, log k, log N
    import math; k=0 if n<=1 else math.ceil(math.log2(n)); mu=(k+3)//2; lk=8+k-mu; return k,mu,lk,lk+3
def leaf(n):
    if n==0: return 80
    k,mu,lk,lN=shape(n); m,kk=2**mu,2**lk; lx=ly=15+k; lr=8+k
    return 80+31+24*kk+lx*96+72+ly*72+1536+lr*72+24*kk+t*(8*m+31*lN)
def node(a,b): return 8*(11+(a+7)//8+(b+7)//8)
L=leaf(16); print(L, node(node(L,L),node(L,L)))   # 143711 575112
```

---

## 13. Decisions the orchestrator still has to take

1. **The acceptance run for R1.** Witness-sending nodes embed their children, so the `r = 8` root
   check of DESIGN-v3 §6.3 cannot pass for *any* SNARK leaf (`256 × |leaf| ≤ 2^20` needs leaves
   under 4 KiB). R1 is certified and proves the `r = 2` smoke tree (root 562 KiB); it cannot be
   listed. If a listed R1 is wanted, the node encoding must stop embedding (a node that hashes
   its children's proofs is R2's extraction problem again). I designed for the smoke tree.
2. **[D-7] ring switching** (packing) — added to `[D-4]`; the alternative that fits the smoke
   root without packing needs the Diamond–Posen tensor lemma *and* BCIKS20's unique-decoding
   line lemma, for a 6% margin. Confirm or reject.
3. **[D-8] 31-byte labels** and **[D-9] no path deduplication** — cosmetic, reversible.
4. **[D-11] Copy leanerVM's circuit framework (≈ 2 300 lines) rather than re-derive it.** It is
   the only existing proved BLAKE2s R1CS; the alternative is a from-scratch adder-gadget proof.
5. `claim.json` numbers: `error = 2^-128` (declared; proved `2^-129`), `qV = 2^14`,
   `fuel = 8 + 0·t` (the library image). Confirm.
6. Whether the Lean `P`'s naive `O(kN)` encoding (`8 × 512 × 4096` at `n = 16`) is fast enough for
   the liveness run; an NTT with a correctness proof is the fallback (its only new lemma is
   `W_i(ω + ω_{2^i}) = W_i(ω) + κ_i` for `ω` in the span, i.e. additivity of `W_i`, which is a
   two-line induction in characteristic 2 from the recursion).

---

## 14. Review response (`docs/reviews/BLUEPRINT-R1-review.md`)

One line per finding: **fixed** (where) or **argued** (why). The protocol, the byte format
(§6–§7) and every parameter (`t = 260`, rate `1/8`, the shape function, `ε`, `qV`) are
unchanged; the figure `ε = 2^{-129}` survives the recount (`2^{-129.3499} + 3·2^{-152} +
2^{-160} < 2^{-129}`, `logs/blueprint-review/check.out`).

| finding | status | where |
|---|---|---|
| BP-M1 partial trees | fixed | §9.1 `col_L`, `tree_L : Fin N → Option`, the filled `U_L` (missing columns zero), `U_T` read on the prefix `L₀(T)`; §9.2 R0 row (no "dangling", no "doomed forever"); L-M3 restated with the former L-M4 folded in, L-M4 now the prefix lemma; §10.1 controls for `tree_L` |
| BP-M2 state hits, repeats | fixed | §9.1 `Bad` (iii) state hit on the full 32-byte `st`, (iv) repeated query; `pred_L`, chains as `pred`-paths from a seed in log order (L-K7); L-K4 restated under `¬Bad`; L-K8 (a fresh entry is a leaf of the transcript forest) carries the step argument |
| BP-M3 `bounded_chainBlock` | fixed, option (a) | §2.2.1: a gate for every constant position the circuit reads, `(var 512, var 512)` or `(0, 0)`; `holds_chainBlock_imp` takes `z 512 = true`; the row list, matrices and KAT are unchanged |
| BP-M4 quadratic decoder | fixed | §1.2 `checkNode` over `decodeF`/`encodeF`; §1.2.1 `Decode.lean`, the S2a linear decoder copied with its `_eq` theorems (not imported); `E` stays the library's `decode`; §10 table; §12 decode row (S2a's measurement quoted, this entry's `check.sh` measures) |
| BP-m1 stale `logCap` | fixed | header (`2^96`, literal `2^256`, `PaperTheorem.lean`), §5.3, §9.3 |
| BP-m2 L-K1 count | fixed | §9.4 L-K1: `≤ L.length·(3·2^8 + 1)`; §9.3 `step` |
| BP-m3 Jensen, L-K2 | fixed | §9.3 `step`: bad answers split off first, then the per-kind sums; L-K2 split into L-K2a (first answer), L-K2b (middle), L-K2c (last) |
| BP-m4 char-2 sumcheck check | fixed | §3: the check is `c_1 + … + c_d = claim`, stated explicitly |
| BP-m5 row 512 in the walk | fixed | §2.3 (`A0, B0` with row 512 cleared), §2.4.2 (the walk skips `cpos`; `walk_eq_sum` over `k ≠ 512`), L-C4 |
| BP-m6 §6.1 numbers | fixed | §6.1: `J = 11 / 13 / 22` at `ℓ_N = 10 / 12 / 20` |
| BP-m7 §12 compressions | fixed | §12: `(leafSize − columns)/64 + #absorbs`: 530 and 12 500 |
| BP-m8 `T_V` | fixed | §12: R1 cannot be ranked, `verify_s` binds; the shared column tensor (`7k` per column) noted as allowed, not required |
| BP-m9 `Vb_eq` guard | fixed | §1.2: `check` has the `π.size < 8` guard |
| BP-m10 L-R1 facts | argued (accepted as optional) | §9.4 L-R1: the 3-periodicity of `y^{2^k}` and the irreducibility-certificate route are recorded as acceptable proofs; the statements `conj_distinct`, `ybasis` are unchanged, so the `Field.lean` agent chooses |
| BP-m11 port AHIV22 | fixed | §9.4 L-RS2 and §10 `Proximity.lean`: port with provenance, the double count over `E^m` along a fixed `β` |
| BP-m12 controls feasibility | fixed | §10.1: theorems from L-C1/L-C2/L-C3 first; kernel KATs only on reduced objects, measured before relied on |
| BP-m13 R6 division wording | fixed | §9.2: the absorb rows after R2, R4 and R6 argue by equality of the two sides, no division, valid when `W̃(r'') = 0` (and `eq(τ, r_x)`, `M̃_ρ(r_x, r_y)`) |
| BP-m14 §2.2.1 justification | fixed | §2.2.1 rewritten with BP-M3 |

### Changes affecting implementers

Formats, parameters and the protocol are untouched; the Rust prover's output is unchanged. The
Lean-side changes, by module:

* **`Blake2sR1CS.lean`** (group A): `chainBlock` prepends a gate for *every* constant position
  the circuit reads (`(var 512, var 512)` or `(0, 0)`), not only the constant-one ones
  (§2.2.1); `holds_chainBlock_imp` gains the hypothesis `z 512 = true`; `bounded_chainBlock`
  is proved from `bounded_blake2s` by inclusion or by `decide`. The walk skips position 512
  and `walk_eq_sum` sums over `k ≠ 512` (§2.4.2). `rowOf`, the row list and the circuit KAT
  are unchanged.
* **`Chain.lean`** (B): `A0, B0` are `chainBlock`'s row forms with row 512 cleared (§2.3);
  `matrix_mle_eq` is stated with them.
* **`Sumcheck.lean`** (A): the verifier's consistency check is `c_1 + … + c_d = claim` (§3);
  no change if it was already computed as `g(0) + g(1)`.
* **`Decode.lean`** (A, new): copy of S2a's linear decoder and its five `_eq` theorems
  (§1.2.1), provenance line to `submissions/baseline/BaselineV3.lean`.
* **`Verifier.lean`** (C): `check` starts with `if π.size < 8 then false` (§1.2);
  `checkNode` matches on `decodeF π` and tests `encodeF (.node …) = π` (§1.2); imports
  `Decode`.
* **`Submission.lean`** (C): `Vb_eq` and `checkNode_sound` go through `check_eq`, which
  rewrites `decodeF`/`encodeF` to the library's `decode`/`encode` by `decodeF_eq`/`encodeF_eq`
  (S2a's pattern).
* **`Proximity.lean`** (B): L-RS2 is a port with provenance of ArkLib's `AHIV22.lean` and
  `AHIV22Support.lean`, the double count done over `E^m` (§9.4); the statement is unchanged.
* **`Field.lean`** (A): no change of statement; the proofs of `conj_distinct` and `ybasis` may
  take the shorter routes of BP-m10.
* **`Soundness/*.lean`, `Soundness/KS.lean`** (D, E): the whole of §9 is restated — `Bad` with
  (iii) and (iv), `tree_L` per column with the filled `U_T` on the prefix `L₀(T)`, chains as
  `pred`-paths, the modes `FarDoom`/close, `p_T` as conditional counts, `μ` with the `Bad ∨
  Esc` case first, and the lemmas L-M3, L-M4, L-K1, L-K2a/b/c, L-K3, L-K4, L-K5, L-K7, L-K8 as
  in §9.4.
* **`Controls.lean`** (D): the circuit and `Sat` controls are theorems first; kernel KATs on
  reduced objects only after a measurement (§10.1); new controls for `tree_L`, `Bad`, `decodeF`.
* **Rust** (`native/`): no change. The `circuit` KAT (row list) and the `proof` KAT
  (byte-identical leaf proofs) are as before.
