# BLUEPRINT-R1: the `spartan-chain` entry (normative)

Status: specification, 2026-10-19, for implementation in parallel (Lean verifier `V`, Lean honest
prover `P`, Lean proofs, Rust native prover). Root `submissions/spartan-chain/`, Lean module
prefix `SpartanChain`. Read against the core at `15e4ae5` and the **amended** contract of
`notes/F1-ks-feasibility.md` §4.2 (potential `μ`, `logCap = 2^64`), which is being implemented
on a core branch; nothing here uses the counting form `KState.Bounded`. Decisions taken here are
**[D-7]** … **[D-11]** (continuing `PLAN.md`); §13 lists what the orchestrator still has to
decide. Everything numeric below is either a definition or was computed by the script quoted in
§12; nothing is a measurement.

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
  match WitnessSending.decode π with
  | some (.node c₁ c₂ π₁ π₂) =>
      encode (.node c₁ c₂ π₁ π₂) = π          -- canonical, as the S2a entry's `check`
      ∧ c = nodeStmt c₁ c₂
      ∧ π₁.size ≤ proofCap ∧ check c₁ π₁
      ∧ π₂.size ≤ proofCap ∧ check c₂ π₂
  | _ => false

check c π : Bool :=                            -- the instantiated decision, recursive on size
  match word 0 of π with
  | 0 => (leafProg c π).run blake2sOracle
  | 1 => checkNode c π
  | _ => false
```

`check` terminates by `π.size` exactly as `WitnessSending.check` does (a canonical node encoding
is longer than each child). The theorem `Vb_eq : submission.Vb c π = (decide (π.size ≤ proofCap)
&& check c π)` is the bridge to `Rel submission.Vb`: the node branch decides `Rel` locally, so
`final` for node proofs is `checkNode_sound`, with no oracle in it (`WitnessSending.check_sound`'s
pattern). `check` is what the compiled `verify` binary runs.

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
* `E := WitnessSending.E` (`fun _ π _ => decode π`), `img := WitnessSending.img`,
  `fuel := WitnessSending.fuel` (8). `computes := WitnessSending.computes` is reused as is.
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

`chainBlock : ProductCircuit 14` is `blake2sCircuit` with `inputs := {648 … 903}` and the
constant-one rows prepended to `gates` as `(k, ⟨var 512, var 512⟩)`; `rowOf` looks gates up first,
so the gate and output rows are literally `blake2sCircuit`'s. Lemma `holds_chainBlock_imp`: a
block satisfying `chainBlock` satisfies `blake2sCircuit` (the rows that differ are trivial
`z_k·1 = z_k` rows in the latter). Lemma `bounded_chainBlock` from `bounded_blake2s` (the
prepended gates read only the constant, at positions that are neither inputs nor gates of
`blake2sCircuit`).

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
  row 512, which is `A = pub(0)`, `B = pub(0)`, `C = w(t, 512)`. So
  `A_0 = I_{2^κ} ⊗ A0` on the `w` columns plus `1 ⊗ A0ᵖ` on the `pub` columns with
  `A0ᵖ = {(512, 0)}`, likewise `B`, and `C_0 = I_{2^{14+κ}}`.
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
  rows add `e(k)·wt(512)` twice; `(0,0)` rows nothing.

`walk_eq_sum`: `walkA e wt = Σ_k e(k)·Σ_j (rowOf k).a[j]·wt(j)` (and `B`), by a simulation
invariant over the `Builder` monad: every form `L` produced by the bitset instance and the value
`v` produced by the walk instance at the same program point satisfy `v = Σ_j L[j]·wt(j)`
(`xor` ↦ `+` and `mul` ↦ the recorded gate). Cost: about `2·14 720 + 2·256 + 2·896` multiplications
plus `2^15` for the tables: `≈ 2^16` `E`-multiplications, independent of `n`.

---

## 3. Spartan

`ℓ_x = ℓ_y = 15 + κ`. All challenges in `E`, all sumchecks bind variable `0` first. A round
polynomial `g` of degree `≤ d` is sent as its `d + 1` coefficients `c_0 … c_d` (ascending); the
verifier checks `g(0) + g(1) = claim` (i.e. `c_0 + Σ_i c_i = claim`) and sets the next claim to
`g(r)` (Horner). No coefficient is dropped (it saves 24 bytes a round and a lemma; not worth it).

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
and hit terms (§9), which is irrelevant at `logCap = 2^64`.

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
  `[0, N)`, independent across indices. The query phase uses `⌈t/cnt⌉` answers (`16` at `ℓ_N = 12`
  … `22` at `ℓ_N = 20`); the trailing bits of the last answer are unused.

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

### 9.1 Objects read off the log

For a log `L` (entries `(q, a)` in order):

* **Labels in `L`.** `lab(L) := { [a]_{31} : (q, a) ∈ L }` and, for a 31-byte string `λ`,
  `pre_L(λ)` the first entry whose truncated answer is `λ` (if any).
* **Tree under a root.** `tree_L(root) : Option (Fin N → column bytes)`: from `pre_L(root)`
  (a node query `0x01 ‖ λ_l ‖ λ_r`, recursively) down to leaf queries `0x00 ‖ bytes`, requiring
  every query on the way to be present and of the right shape; `none` if any is missing
  ("dangling"). `U_L(root)` is the `K^{m×N}` matrix it denotes.
* **Bad events** `Bad(L)`:
  (i) *collision*: two entries with different queries and equal 31-byte truncated answers;
  (ii) *hit*: an entry `(q, a)` such that `[a]_{31}` equals a label occurring in the input of an
  **earlier** entry (as a child field of a node query, or as the `root` field of an `absorb(root)`
  query).
  Under `¬Bad(L)` every root used in a Fiat–Shamir chain of `L` either had its whole tree in `L`
  before the absorb, or stays dangling forever in `L`; and a verified path in `L` opens exactly
  `U_L(root)`'s column (L-M3).
* **Transcript prefixes.** A chain of `L` is a maximal sequence of entries matching §6.2 from a
  seed query `0x10 ‖ s ‖ enc64 n ‖ h` (the statement is read off the seed; the prover's messages
  off the absorb queries; the challenges off the squeeze answers). Under `¬Bad(L)` (no state
  collision) each squeeze entry belongs to at most one chain.

### 9.2 The state function (round by round)

Fix a chain with statement `(s, n, h)` such that `chainEnd s n ≠ h` (for a true statement nothing
is charged: `final` is satisfied by the parsed witness). Its state after each challenge round is
**doomed** or not; the initial state is doomed; a full accepting transcript is never doomed
(L-K3). Escapes (doomed → not doomed) are the events charged:

| round | state entering | escape event | bound (probability over the fresh answers) | lemma |
|---|---|---|---|---|
| R0: `r ∈ E^m` (multi-answer, `m` squeezes) | `U` dangling: doomed forever (no escape); `U` far: doomed | `Σ_i r_i U[i]` is `e`-close | `d/|E| ≤ 2^{-169}` | L-RS2 |
| R0, `U` close | doomed (the decoded `w_dec` cannot satisfy `Sat`, by L-C2) | — | 0 | |
| R1: `τ_l` (`ℓ_x` single answers) | `P_l(τ_{l+1..}) := Σ_x eq((τ_{<l}, ·), x)·F(x) ≢ 0` as a polynomial, where `F = (Az)(Bz)+(Cz)` for `z = (w_dec ‖ pub)` | `P_{l+1} ≡ 0` | `1/|E|` each | L-S2 |
| R2: outer round `l` | the claim is false for the true polynomial | `g_l(r) = true partial sum` with `g_l ≠` the true round polynomial | `3/|E|` | L-S1 |
| after R2 | `v_A, v_B, v_C` with `(v_A·v_B + v_C)·eq(τ,r_x) = claim` but some `v_M ≠ (Mz)̃(r_x)` | — (an unsound triple keeps doom) | 0 | |
| R3: `ρ` | some `v_M` wrong | `v_A + ρv_B + ρ²v_C = Σ_y M̃_ρ(r_x,y)z(y)` | `2/|E|` | L-S3 |
| R4: inner round `l` | false claim | as R2 | `2/|E|` | L-S1 |
| after R4 | slices with `Σ eq(r_lo,i)s_i = w̃` consistent but some `s_i ≠ Q̃_i(r_hi)` | — | 0 | |
| R5: `f_p` (6 single answers) | some `π_k^{(p)} ≠ 0` for `k < 2M_p` | all `π_k^{(p+1)} = 0` for `k < M_p` | `1/|E|` each | L-R2 |
| after R5 | `T ≠ Σ_{u'} W(u') q_dec(u')` | — | 0 | L-R1 |
| R6: ring-switch round `l` | false claim | as R2 | `2/|E|` | L-S1 |
| after R6 | `v' = claim/W̃(r'')` required but `q̃_dec(r'') ≠ v'`, i.e. `v ≠ Σ_i a_i q_dec[i]` | — | 0 | |
| R7: column indices (multi-answer) | far: `Enc(ū)` differs from `Σ r_i U[i]` in `> e` places; close: `Enc(v)` differs from `Σ a_i U[i]` in `≥ d − e` places | all `t` columns miss the difference set | `(17/24)^{260} < 2^{-129.35}`; `(5/12)^{260}` | L-RS3 |
| after R7 | — | — | accept impossible: the opened columns are `U`'s (L-M3) and one of them fails | |

Every state predicate is a function of the log prefix (the chain's messages, the decoded `U`,
and the challenges so far); none looks at future entries.

### 9.3 The potential

`μ(L) := min(1, [Bad(L) ∨ Esc(L)] + Σ_{chains T of L in a multi-answer round} p_T(L))`, where
`Esc(L)` says some chain of `L` escaped doom at a completed round, and for a chain in the middle
of R0 (after `j < m` coefficients) or R7 (after `j` index answers),
`p_T(L) := Pr[ the round ends in an escape | the answers so far ]` — a ratio of counts over the
remaining answers (`|E|^{m−j}` resp. `2^{256·(…)}`), zero once a column has already hit.

* `empty`: `μ [] = 0`.
* `step` (average over the `2^256` answers `a` of a fresh `q`, `L.length < logCap`, `μ L < 1`):
  the average of `[Bad(L ++ [(q,a)])]` rises by at most `(#labels in inputs or answers of L)/2^248
  ≤ 3·2^64/2^248 = 3·2^{-184}` (L-K1); a squeeze of a single-answer round raises `[Esc]` by at
  most `3/|E|`; the first answer of a multi-answer round creates a term `p_T` whose average is the
  round's escape probability (`≤ 2^{-169}` for R0, `< 2^{-129.35}` for R7); every later answer of
  the round leaves the average unchanged (the martingale property of a conditional probability,
  L-K2), and the last turns `p_T` into `[Esc]`; an absorb or a Merkle query changes nothing but
  `Bad`. Since `min(1, ·)` is concave, `E[min(1, X')] ≤ min(1, E[X']) ≤ min(1, X + ε) ≤ min(1, X) + ε`.
  Hence **`ε = 2^{-129}`** (`2^{-129.35} + 3·2^{-184} < 2^{-129}`).
* `final`: `(V c π).runLog L = some true` with `μ L < 1` and `L.length ≤ logCap`. Node proofs:
  `checkNode_sound`. Leaf proofs with `chainEnd s n = h`: the parsed witness is in `Rel`. Leaf
  proofs with `chainEnd s n ≠ h`: the run's queries are a chain of `L` (`runLog` reads them off
  `L`, L-K4); `¬Bad(L)` and `¬Esc(L)` make every state of the chain doomed through R7 (§9.2),
  and a doomed final state rejects — contradiction.

The `KState` is built in `Soundness/KS.lean`; `KS` follows with `qV` from L-Q1. (`ε = 2^{-129}`
is declared as `2^{-128}` in `claim.json`; `CertificateR.bounds` compares.)

### 9.4 Lemma inventory (statement, module)

Circuit and chain (`Blake2sR1CS.lean`, `Chain.lean`):

* **L-C1** `block_sound`, `block_complete` (§2.2.2).
* **L-C2** `chain_sound : (∀ u, w u ∈ {0,1}) → Sat n s h (w ‖ pub s h) → chainEnd s n = h`.
* **L-C3** `chain_complete : Sat n s (chainEnd s n) (chainWitness s n ‖ pub s (chainEnd s n))`
  and `chainWitness` Boolean with `pos 512 = 1` in every block.
* **L-C4** `walk_eq_sum` (§2.4.2); `shift_mle : ∀ t t' ∈ {0,1}^κ, S̃(t,t') = [t' + 1 = t]`;
  `matrix_mle_eq`: the formulas of §2.4 equal `Σ_{x,y} eq(r_x,x)eq(r_y,y)·M(x,y)` for `M ∈ {A,B,C}`.

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
families of facts are kernel-decided in `Field.lean`, see §10); **L-R2** `stage_bad_le_one`
(leanerVM `card_stage_zero_le_one`, Mathlib-only, copied): a family with some `π_k ≠ 0`, `k < 2M`,
keeps some `π_k ≠ 0`, `k < M`, after the stage `(M, f)` for all `f` but at most one;
**L-R3** `ring_complete : Σ_{u'} Φ(eq(r,u'))·q(u') = Σ_i x^i Φ(Q̃_i(r))` for `q(u') = Σ_i Q_i(u')x^i`,
`Q_i` Boolean; **L-R4** `weight_mle : W̃(r'') = Σ_k c_k eq(r^{2^k}, r'')`; **L-R5** `phi_eq_sum`
(`frobMap_eq_sum`, copied).

Code and PCS (`RS.lean`, `Ligero.lean`): **L-RS1** `code_dist : c, c' ∈ C, c ≠ c' → #{i : c_i ≠ c'_i} ≥ N − k + 1`
(from `basis_deg : deg X_j = j`, monic); **L-RS2** (AHIV22 4.3–4.5, counting form)
`far_bad_le : 3e < d → d < |E| → ¬ eClose U e → #{r ∈ E^m : Δ(Σ r_i U[i], C) ≤ e} ≤ d·|E|^{m−1}`,
proved by the affine-line lemma (`> d` close scalars on a line ⇒ base and direction agree with
codewords off a common set of `≤ e` columns; ArkLib `exists_codewords_agree_of_many_close_scalars`
as the guide), a far direction in the row span (`dist_interleaved_code_to_code_lb`), and the
double count (`prob_of_bad_pts`); **L-RS3** `miss_le : |D| ≥ δN → #{index tuples missing D} ≤ (1−δ)^t·N^t`
(exact: `(N − |D|)^t`); **L-RS4** `close_unique` and `close_in_K` (§5.5); **L-RS5**
`encode_complete`: `Enc(Σ r_i Q[i]) = Σ r_i Enc(Q[i])` (linearity) and the tensor evaluation equals
`Enc(·)_c`.

Merkle and log (`Merkle.lean`, `Soundness/Log.lean`): **L-M1** `path_complete`: for every `H`, the
prover's path for column `c` verifies against the root it computed; **L-M2** `tree_of_log`:
if the prover's build queries are in `L` consistently with `H`, `tree_L(root) = some (columns)`;
**L-M3** `open_binding : ¬Bad(L) → tree_L(root) = some cols → path for c verifies in L → opened
column = cols c`; **L-M4** `dangling_persists : ¬Bad(L) → tree_L(root) = none → ` no later entry
of `L` (without a hit) completes it — folded into the definition of `Bad`.

Knowledge state (`Soundness/KS.lean`): **L-K1** `bad_step_le : #{a : Bad(L ++ [(q,a)]) ∧ ¬Bad L} ≤ 3·L.length·2^{64}·…`,
precisely `≤ (2·L.length + 1)·2^{256−248}`; **L-K2** `martingale`: for `p_T` defined as a
conditional count, `Σ_a p_T(L ++ [(q,a)]) = 2^{256}·p_T(L)`; **L-K3** `accept_not_doomed`: a
chain whose last state is doomed is rejected by `leafProg` (the final checks); **L-K4**
`runLog_chain`: `(leafProg c π).runLog L = some b` ⇒ the queries of the run, in order, form a
chain of `L` with the proof's messages; **L-K5** `kstate : KState (Rel Vb) V E` with `μ` of §9.3;
**L-K6** `ks : KS (Rel Vb) V E 2^{-129} 2^{14}`.

Query bound (`Verifier.lean`): **L-Q1** `queries_le : ∀ H c π, ((V c π).queries H).length ≤ 2^{14}`
(the structured count of §6.3 for `n ≤ 2^{20}`; zero for rejects before the first query and for
nodes).

Certificate (`Submission.lean`): `Vb_eq`, `checkNode_sound`, `fits_of_rel`, `certificate`,
`certified` (the rendered challenge).

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
| `MLE.lean` | `eq`, `mle` over `Fin (2^ℓ) → R`, tables, L-E1…L-E4, tensor split | `Field` | A |
| `Blake2sR1CS.lean` | the copied framework and circuit, generic form type, both instances, L-C1, `walk_eq_sum` | `Field`, contract `Blake2s` | A (largest copy; can start on `BF64` directly) |
| `Chain.lean` | regions, `Sat`, `pub`, `chainWitness`, `S̃`, matrix MLE formulas, L-C2…L-C4 | `Blake2sR1CS`, `MLE` | B |
| `Sumcheck.lean` | verifier round logic over an abstract claim, honest rounds for products of linear factors, L-S1…L-S4 | `MLE` | A |
| `RS.lean` | domain, `W_i`, `X_j`, `Enc`, L-RS1, L-RS5 | `Field` | A |
| `Proximity.lean` | `eClose`, L-RS2 (AHIV counting), L-RS3, L-RS4 | `RS` | B (the one hard mathematics module; independent of the protocol) |
| `RingSwitch.lean` | `frobMap` and its lemmas (copied), stages, `c_k` table, `Φ`, `W̃`, `T`, L-R1…L-R5 | `Field`, `MLE` | A |
| `Merkle.lean` | build, path, `verify` as `OProg`, L-M1, L-M2 | `Oracle` | A |
| `Transcript.lean` | state, `absorb`, `squeeze`, `chE`, index chunking, fiber-count lemma | `Oracle`, `Field` | A |
| `Ligero.lean` | commit (prover), open, verify (`OProg`), shape function, sizes | `RS`, `Merkle`, `Transcript` | B |
| `Verifier.lean` | `leafProg`, `checkNode`, `check`, `V`, `leafSize`, L-Q1 | `Chain`, `Sumcheck`, `RingSwitch`, `Ligero` | C |
| `Prover.lean` | `proveLeaf`, `P` | same | C |
| `Submission.lean` | `submission`, `Vb_eq`, `checkNode_sound`, `fits_of_rel` | `Verifier`, `Prover` | C |
| `Completeness.lean` | §8 | all of C | D |
| `Soundness/Log.lean` | §9.1 objects, L-M3, L-K1, L-K4 | `Merkle`, `Transcript`, `Verifier` | D |
| `Soundness/Spartan.lean` | the state function's algebraic rounds, R1–R6 bounds | `Chain`, `Sumcheck`, `RingSwitch` | D |
| `Soundness/PCS.lean` | R0, R7, decoding, L-RS2 applied | `Proximity`, `Ligero` | D |
| `Soundness/KS.lean` | `μ`, L-K2, L-K3, L-K5, L-K6 | all of D | E |
| `Controls.lean` | positive and negative controls (§10.1) | all | D |
| `Solution.lean` | the rendered challenge with `submission` and `certified` | `Submission`, `Completeness`, `Soundness/KS` | E |
| `Run.lean` | `spartan-run`: `verify`, `prove-leaf`, `prove-node`, and the KAT dumps of §11.3 | C | C |

Groups A are independent of each other (five to seven agents); B needs A; C needs B; D needs C;
E closes. `Proximity.lean` and `Blake2sR1CS.lean` are the long poles and need nothing from the
protocol modules.

### 10.1 Controls (non-vacuity)

For every definition the certificate relies on, one positive and one negative control, by
`decide`/`rfl` on small instances or by a theorem: `chainBlock` on a known-answer chain step
(the trace's output equals `chainStep` of RFC vectors; a flipped output bit fails `Holds`);
`Sat` at `n = 1, 2` on the honest witness, and failing on a witness with one wrong bit;
`S̃` at `κ = 3` equals the Boolean shift table and differs from the identity; `Enc` on `k = 4`
against naive polynomial evaluation, and a nonzero message has a nonzero codeword; `eClose` on
a toy `2×8` matrix both ways; `Φ` with all `f_p = 0` is the identity, with one `f_p ≠ 0` is not;
the transcript reproduces a fixed known answer under `blake2sOracle`; `leafSize` canaries:
`V` rejects the honest proof with a byte appended, truncated, with a flipped statement bit;
`checkNode` rejects a swapped child digest. The AHIV lemma's hypotheses are non-vacuous: a
control exhibits `U` far with the bound tight on a toy code.

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
| Ligero: `Enc(ū)_c`, `Enc(v)_c` at 260 columns (`2·260·(k + 3k)` `K`-mul) | ≈ `1.1·10^6` `K`-mul | ≈ `3.4·10^7` `K`-mul |
| column combinations `Σ r_i U[i][c]`, `Σ a_i U[i][c]` (`2·260·3m`) | ≈ 12 000 `K`-mul | ≈ 400 000 |
| **field total (K-mul equivalents)** | **≈ 1.6·10^6** | **≈ 3.5·10^7** |
| oracle queries | 3 533 | 5 156 |
| compressions: FS absorbs (`≈ leafSize/64`) + squeezes + Merkle (`260·(⌈(2+8m)/64⌉ + ℓ_N)`) | ≈ 2 300 + 100 + 3 600 ≈ **6 000** | ≈ 23 000 + 400 + 13 000 ≈ **36 000** |

With a word-level `K`-multiplication at `0.1–0.5 µs` (unmeasured; E2's unverified loop ran at
1.47 µs, leanVM's Rust at 25 ns) and 5 µs per compression (S2a's measurement): **≈ 0.2–0.9 s per
leaf at `n = 16`**, so ≈ 1–4 s for the smoke root (4 leaves); `≈ 4–18 s` at `n = 2^14`. The walk
(`2^16` `E`-mul ≈ 0.4 M `K`-mul) is a fixed cost per leaf. R1 is unranked by `proofCap` before
`T_V` matters.

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
