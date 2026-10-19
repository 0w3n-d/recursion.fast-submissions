# Adversarial review of BLUEPRINT-R1 (the `spartan-chain` entry)

Reviewed: `docs/snark-baseline/BLUEPRINT-R1.md` (906 lines, 2026-10-19), against `PLAN.md`,
`notes/F1-ks-feasibility.md` §4, the amended contract `rf-core-ks/RecursionFast/Contract/Security.lean`
(branch `v3/ks-potential`, working tree: `logCap = 2^96`), the pinned contract
`.contract/RecursionFast/Contract/{Relation,Oracle,Extractor,Certificate}.lean`,
`.contract/RecursionFast/Library/{WitnessSending,Words}.lean`, leanVM
`doc/leanvm/body/{a-ring-switching,b-polynomial-commitment-scheme}.tex`, leanerVM `532ebb4`
(`Protocol/Blake2sCircuit.lean`, `Protocol/ToArkLib/Flock/{Circuit,FrobeniusMap}.lean`), ArkLib
`Data/CodingTheory/ProximityGap/AHIV22*.lean` (from the shared package tree), and
`docs/snark-baseline/issues/I7-…`.

Recomputations: `logs/blueprint-review/check.py`, output `logs/blueprint-review/check.out`.

**Verdict.** The protocol is sound in substance. Spartan, ring switching, Ligero with unique
decoding, and the chain R1CS all check out, and so do the sizes and query counts (list at the end).
The **security argument of §9 does not hold as written**. Two defects in `Bad`/`tree_L` make the
`final` or `step` law false (M1, M2). One lemma in group A is false as stated (M3). The compiled
node check reuses a decoder that is known to be quadratic, which breaks `verify_s` on the smoke
root (M4). All four fixes are local. None of them changes the protocol, the byte format or a
parameter.

---

## Major findings

### BP-M1. A partially built Merkle tree is not "doomed forever"; `final` fails

**Where.** §9.1 (`tree_L(root) : Option (Fin N → column bytes)`, `none` if anything is missing),
§9.2 row R0 ("`U` dangling: doomed forever (no escape)"), L-M2, L-M3, L-M4 (§9.4).

**Argument.** A cheating prover builds the left half of the tree honestly. It uses a random 31-byte
string `λ_r` with no preimage as the root's right child and absorbs
`root = [H(0x01 ‖ λ_l ‖ λ_r)]_31`. Then `tree_L(root) = none`, so the chain counts as dangling. The
blueprint gives a dangling chain no algebraic doom predicate and no escape event, so `Esc` can
never fire for it. Every path into the left half still verifies, and L-M4 only guarantees that the
right half is never completed. `final` quantifies over **every** log `L` with `μ L < 1`. Take a log
in which all 260 indices land in the left half (the answers of a log are arbitrary) and in which
the sumcheck and ring-switching challenges are lucky enough for a false statement. Then
`leafProg` accepts, `¬Bad`, `¬Esc`, and `μ L = 0`. No witness exists, so `final` is false. The
analysis also misses a real escape probability: about `2^-260` for the indices, times the
algebraic escapes.

**Fix.** Make the tree partial per column: `tree_L(root) : Fin N → Option column`, read on the log
prefix before `absorb(root)`. Define `U_L(root)` with every missing column (absent, wrong shape or
wrong length) filled with a fixed value, e.g. `0`. Restate L-M3 as follows: under `¬Bad`, a path
for `c` that verifies in `L` implies `tree_L(root) c = some col` and the opened column is `col`.
The analysis of §5.5 and R0–R7 then applies verbatim to the filled `U`. Missing columns can never
be opened, so they only shrink the accepting set, and the extractor never sees `U`. Delete
"doomed forever" from R0 and fold L-M4 into L-M3.

### BP-M2. `Bad` omits hits on Fiat–Shamir states, so chains can be assembled out of order

**Where.** §9.1 `Bad` (ii) covers only labels in node child fields and in `absorb(root)`. §9.1
"Transcript prefixes", the §9.3 step bullet ("an absorb … changes nothing but `Bad`"), L-K4.

**Argument.** Let `X` be a 32-byte string that is not yet any answer. The adversary first queries
`squeeze(X) = H(0x30 ‖ X)` and learns the challenge `chE(A)`. Later a fresh absorb
`H(0x20 ‖ st ‖ kind ‖ msg)` happens to answer `X`. Now the squeeze that follows `msg` was answered
before `msg` existed. There are two ways to read "chain" (§9.1 does not say):

- **Chains need not be in log order.** Then this absorb step creates a chain whose next challenge
  is already fixed. `[Esc]` can jump to 1 at an absorb, which the step accounting says cannot
  happen, so the `step` proof fails. A pre-queried run of R7 squeezes is the same problem for
  `p_T`.
- **Chains must be in log order.** `runLog` reads answers regardless of order
  (`Contract/Oracle.lean`, `find?`), so L-K4 ("the run's queries form a chain of `L`") is false,
  and `final` fails on such logs.

**Fix.** Add (iii), a **state hit**: the fresh answer equals the `st` field of an earlier absorb or
squeeze query (full 32 bytes). Its cost per step is at most `|L|·2^-256`. Under `¬Bad`, prove that
the predecessor of each chain entry (the unique entry whose answer is its `st`) comes earlier in
`L`; this is the lemma L-K4 needs. Also put **"`L` has a repeated query"** into `Bad`. `final`
ranges over arbitrary `L`, `runLog` uses the first entry for a query, and `step` never creates a
repeat because `q ∉ L.map Prod.fst`. Without this, the chain and tree definitions have to commit to
first-entry semantics everywhere.

### BP-M3. `bounded_chainBlock` is false as specified

**Where.** §2.2.1: "Lemma `bounded_chainBlock` from `bounded_blake2s` (the prepended gates read
only the constant, at positions that are neither inputs nor gates of `blake2sCircuit`)". The
module is `Blake2sR1CS.lean`, group A.

**Argument.** `Bounded c` is `BoundedFrom (c.inputs ||| var cpos) c.gates` (leanerVM
`Flock/Circuit.lean:174-190`, copied as `SpartanChainBlake2sCircuit.lean:186-195`). It requires
**every gate's forms to mention only inputs, the constant and earlier gates**. `chainBlock` shrinks
`inputs` to `648…903` and prepends gates only for the constant-**one** positions. The constant-zero
positions are neither inputs nor gates of `chainBlock`, yet the BLAKE2s gates read them. They are:

- the zero bits of `h0`, of the tag byte and of the counter;
- all of `904…1151` (message words 9–15, read in every round);
- `t_hi` and `f1`.

So `Sub g.a avail` fails and the lemma is false. Its justification is also wrong: `0…255` and
`640…1279` **are** inputs of `blake2sCircuit`. `trace_satisfies`/`trace_holds` need `Bounded`, so
`block_complete` as planned ("`chainBlock.traceF` … satisfies the R1CS") has no proof.

**Fix.** Either option works:

- (a) Prepend `(k, ⟨0, 0⟩)` gates for every constant-zero position the circuit reads. `rowOf` is
  unchanged (still `(0, 0)`), `traceF` still writes `0`, and `Bounded` then holds. Prove it by
  `decide` or from `bounded_blake2s`.
- (b) Drop `bounded_chainBlock`. Prove `block_complete` from `blake2sCircuit.traceF` on the full
  input `(h0, 0x43 ‖ d ‖ 0…, 33, 0xFFFFFFFF, 0)`, then check the constant rows of `chainBlock`
  directly.

Soundness is unaffected, because `block_sound` goes through `holds_chainBlock_imp` and
`bounded_blake2s`. Also add the hypothesis `z 512 = true` to `holds_chainBlock_imp`: the input rows
of `blake2sCircuit` read `z_k · z_512 = z_k`, which is not trivial without it.

### BP-M4. The compiled node check runs the quadratic library decoder; the smoke root exceeds `verify_s`

**Where.** §1.2 `checkNode` (`WitnessSending.decode π`, `encode (…) = π`), §1.4 ("reused as is"),
§12 (cost has no decode term).

**Argument.** `decode`, `encode`, `packBytes`, `bytesWords` and `bytesAt` compile to code that is
quadratic in the proof length. Issue I7 measured 563 s to reject a random 1 MiB proof. The smoke
root has 575 112 B and its two children 287 512 B each. Scaling quadratically, decoding the root
alone takes about `0.55² × 563 ≈ 170 s`, and the canonical re-encoding adds more. That is far above
`verify_s = 60 s` (DESIGN-v3 §6.6) and the root check must accept within it. A random proof of
about 1 MiB with word 0 equal to 1 takes 563 s, which fails the DoS column.

**Fix.** In `check`/`checkNode`, use the S2a entry's linear twins (`BaselineV3.lean`:
`decodeWitF`, `packFast`, `decodeF`, `decodeF_eq`), copied into the root with a provenance line,
plus a linear canonical-encoding test proved equal to `encode (…) = π`. Keep `E := decode` as the
specification. Add a measured decode time to §12.

---

## Minor findings

- **BP-m1 (stale `logCap`).** The header (line 6), §5.3 (last paragraph), §9.3 (step bullet) and
  F1-based text still say `logCap = 2^64`. The amended contract says `2^96`. The `Bad` term becomes
  `3·2^96/2^248 = 3·2^-152`, plus `2^96·2^-256` for state hits (M2). `ε` still holds: the total per
  step is `2^-129.3499 < 2^-129` (`check.out`). Update the figures.
- **BP-m2 (L-K1 count).** The statement is internally inconsistent: "`≤ 3·L.length·2^64·…`,
  precisely `(2·L.length + 1)·2^{256−248}`". The correct count of bad answers:
  - collisions: at most `|L|` truncated answers;
  - label hits: at most `2|L|` labels (a node query carries two, `absorb(root)` one), plus the new
    query's own child labels, at most 2, if the parse is not depth-bounded;
  - state hits (M2): at most `|L|` full answers.

  The total is `≤ (3|L| + 2)·2^8 + |L|` answers.
- **BP-m3 (step argument, L-K2).** §9.3 applies Jensen to `X'` itself. On answers that cause `Bad`,
  the set of chains, and hence the `p_T`, can change arbitrarily. The argument should be
  `E[min(1, X')] ≤ Pr[Bad'] + E[X'·1_{¬Bad'}]`. L-K2 as stated (`Σ_a p_T(L++[(q,a)]) =
  2^256·p_T(L)`) is false at a round's first answer, where `p_T(L) = 0`. Split it into three
  lemmas: first answer (the average is the round's escape probability), middle answers (equality),
  last answer (`p_T` becomes `[Esc]`).
- **BP-m4 (sumcheck check in char 2).** In §3, "`c_0 + Σ_i c_i = claim`" is ambiguous. In
  characteristic 2, `g(0) + g(1) = c_1 + … + c_d`: the `c_0` terms cancel. An implementer who
  reads `Σ` as `i ≥ 1` computes `g(1)`. Write the check explicitly.
- **BP-m5 (row 512 in the walk).** In §2.4, `A0̃, B0̃` must be `chainBlock`'s matrices **with row
  512 cleared**, because the chain R1CS replaces that row with `(pub₀, pub₀, w(t,512))`. `rowOf`
  gives `cpos` the row `(var 512, var 512)`, and §2.4.2's walk list does not mention `cpos`. A
  naive walk makes row 512 `(w₅₁₂ + 1)² = w₅₁₂`. Honestly that is `0 = 1` in characteristic 2, so
  completeness fails. State that the walk skips `cpos`.
- **BP-m6 (§6.1 numbers).** "16 at `ℓ_N = 12` … 22 at `ℓ_N = 20`" is wrong. At `ℓ_N = 12`,
  `cnt = 21` gives 13 answers, and at `ℓ_N = 10` it is 11. §6.3's totals already use 13 and are
  right: 3 533 / 5 156 / 7 774.
- **BP-m7 (§12 compressions).** The FS absorb cost is given as `≈ leafSize/64`, but the column
  openings are not absorbed. The correct estimate is `≈ (leafSize − columns)/64 + #absorbs`: about
  530 at `n = 16` (not 2 300) and about 12 500 at `2^14` (not 23 000). The error is conservative.
- **BP-m8 (`T_V`).** The smoke root estimate of 1–4 s straddles `T_V = 2 s` (DESIGN-v3 §6.5; a
  violation removes board T and column R, not certification). R1 cannot be ranked anyway, which
  §12 should say. A free saving: share the column tensor `X_j(ω_c)` between `Enc(ū)_c` and
  `Enc(v)_c`, which costs `7k` instead of `8k` per column.
- **BP-m9 (`Vb_eq`).** `V` has a `π.size < 8` guard that `check` (§1.2) lacks. `Vb_eq` needs
  `(V c π).run blake2sOracle = check c π` for every `π`. Add the same guard to `check`, or define
  `check` through `V`.
- **BP-m10 (L-R1 facts).** `y ∈ F_8` (`y³ = y + 1`), so `y^{2^k}` cycles through `y, y², y² + y`
  with period 3. `ybasis` is then three determinants with `F₂` entries. `conj_distinct` can come
  from the irreducibility certificate of the modulus (CompPoly `BF64/BaseCertificate.lean`)
  instead of 64 chains of kernel squarings. Optional.
- **BP-m11 (L-RS2 effort).** ArkLib's `AHIV22.lean` and `AHIV22Support.lean`
  (`dist_interleaved_code_to_code_lb`, `e_le_dist_over_3`, `prob_of_bad_pts`) are sorry-free,
  about 800 lines, Apache-2.0. Port them with provenance rather than using them only "as a guide".
  ArkLib samples uniformly from the **row span**, while R0 samples `r ∈ E^m`. Redo the double count
  directly over `E^m`, along any `β` with `Σ β_i U[i] = v*` (same proof), which avoids a pushforward
  lemma.
- **BP-m12 (controls feasibility).** leanerVM checks its circuit with `#guard`, which the source
  rule refuses. The §10.1 controls ("`Sat` at `n = 1, 2` … by `decide`") need a kernel
  `decide` over 2^16–2^17 rows of 2^14-bit forms, and its cost has not been measured. State them
  as theorems from L-C1/L-C3, plus a kernel-decided known-answer test on a reduced object, or
  measure first.
- **BP-m13 (R6 wording).** §9.2 "`v' = claim/W̃(r'')` required" reads as a division. Restate it:
  `claim ≠ W̃(r'')·q̃_dec(r'')` and `claim = W̃(r'')·v'` give `v' ≠ q̃_dec(r'')`. This also holds
  when `W̃(r'') = 0`. The same no-division argument applies to the outer check (`eq(τ, r_x)`) and
  the inner check (`M̃_ρ(r_x, r_y)`).
- **BP-m14 (§2.2.1 justification).** The wording "positions that are neither inputs nor gates of
  `blake2sCircuit`" is wrong independently of M3. Fix it together with M3.

---

## Checked and found correct

- **Arithmetisation (§2).** Positions and the contract's `block` agree: tag `0x43` at 640, `d[e]`
  at `648 + 8e`, `m[8] = d[31]`, zeros from 904, counter 33 at 1152, `f0` at 1216, and the digest
  byte `e` at `256 + 8e` (little-endian words). `h0[0] = 0x6B08E647`. The wiring rows, the tail
  rows, `pub` and row 512 bind `s` and `h`. The matrices depend only on `n`, and padding blocks are
  harmless. Every term of the §2.4 MLE table re-derived: `RW`, `RT`, `S̃` (the binary increment
  `t' + 1 = t`, with no wrap at `t' = 2^κ − 1`), `U0`, `T0`, `T0'`, `Σ_j^b`, and `eq_sum_one` for
  the `pub₀` columns. Cost: `O(2^16 + κ)`, independent of `n`. `n = 0`, `n = 1` (`κ = 0`, all
  empty products) and `n` not a power of two are handled.
- **Spartan.** Degrees (3, 2, 2), the zerocheck (`ℓ_x/|E|`), batching (`2/|E|`), and both final
  checks need no division.
- **Ring switching.** L-R1 is true. It matches leanVM Annex A §A.3 (`π_k = pair_k`, the `K`-basis
  `{1, y^{2^k}, y^{2^{k+1}}}`, and the Vandermonde in the 64 conjugates of `x`). The six-stage
  argument is correct: one stage maps `π_k ↦ π_k + f^{2^k}·π_{k+M}` (leanerVM
  `card_stage_zero_le_one` has exactly this form), so the bound is `6/|E|`, tighter than leanVM's
  Schwartz–Zippel bound of `2^-160`. `W̃` is the MLE of `W` (`eq_frob` and `eq_mle`), and the table
  for `c_k` matches leanVM's `c_k`.
- **Ligero.** `e = ⌊7k/3⌋`, so `3e < d` and `2e < d`, and `(e+1)/N > 7/24` for every `k = 2^ℓ`.
  The far case is at most `2^-129.35` (`t = 259` gives `2^-128.85`). The close case is
  `(5/12)^260 = 2^-328.39`, and `d/|E| ≤ 2^-169.2` for `ℓ_k ≤ 20`. The check is exact per `ℓ_k`
  from 5 to 20 in `check.out`. The `close_in_K` projection argument is valid because `ω_c ∈ K`.
  The ArkLib Lemma 4.5 hypotheses (`3e < d`, `e < |F|`) match L-RS2. The unnormalised `W_i` give a
  monic triangular basis, so no inversion is needed.
- **Fiat–Shamir binding.** `s`, `n` and `h` seed the transcript, and `c` is bound by
  `leafStmt h n`. Every message is absorbed before the challenges that depend on it: `r` comes
  after the root, `f_p` after the slices, `r''` after each round, and the indices after `ū` and
  `v`. First bytes `0x00`, `0x01`, `0x10`, `0x20` and `0x30` separate the query kinds, and every
  message length is a function of `n`. `chE` takes `2^64` preimages per element, and the index
  chunking is exactly uniform. Every byte string decodes to a field element, so there are no
  non-canonical encodings.
- **Completeness.** It holds for every `H`, including a constant `H`. No division, no distinctness
  requirement and no rejection sampling. `n = 0` uses `chainEnd s 0 = s`.
- **Parsing.** Leaf bytes 0–47 equal `wordsBytes (witWords (.leaf s n))`, and `decodeWit_cons`
  reads `s` from words 1–4 and `n` from word 5, as `leafProg` does. The `leafSize` check rejects an
  appended or truncated leaf proof, `c = leafStmt h n` rejects a flipped statement, the canonical
  encoding rejects an appended byte on a node, and `nodeStmt` rejects swapped children.
- **Sizes and query bound (script).** A leaf at `n = 16` is 143 711 B, a level-1 node 287 512 B,
  and the root 575 112 B (0.548 MiB). Leaves fit under `proofCap` up to `n = 4096` (796 111 B).
  The verifier makes at most 7 774 queries at `n = 2^20`, which is within `qV = 2^14`. `V`
  terminates for every `n ≤ 2^20`. At `n = 2^20` it is never reached through `Vb`, because the
  proof is 10.2 MiB, above `proofCap`.
- **CGH hygiene.** `V` never computes BLAKE2s on an oracle input and compares it with an oracle
  answer. `leafStmt` is the relation and is compared with `c`, Merkle and FS hashing go through
  `H`, and the node branch's concrete `Vb` is the relation itself.
