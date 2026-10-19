# Report: the leaf SNARK (`SpartanChainVerifier`, `SpartanChainProver`, `SpartanChainRun`)

Blueprint: §1.3–§1.4, §6.2, §7, §8, §9.2 checks (a)–(f), L-Q1, and the §14 "SpartanChainVerifier"
requirements.

**Status**

- **No `sorry`.**
- `lake build +SpartanChainRun +SpartanChainVerifier +SpartanChainProver` is green
  (`logs/spartan-chain/mle-sumcheck-ringswitch/lake-build-4.log`).
- Axioms are `propext`, `Classical.choice` and `Quot.sound` only (`axioms-4.log`).
- The source rule reports `47 files, 0 finding(s)`.
- Code lines: Verifier 100, Prover 200, Run 18.
- The Lean verifier has been run on Rust proofs. The prover's byte-identity test is still pending;
  see "Compiled run".

## Byte helpers merged with Ligero's

`SpartanChainSpartanProtocol` now imports `SpartanChainLigero` and uses its byte helpers:

- `Ligero.efBytes` for every absorbed message and for `encodeMsgs`;
- `Ligero.readEFs` for `parseMsgs`.

My `encE` and `decE` are deleted. The round-trip lemma is now `readEFs_append`, which reads back
inside `pre ++ efBytes xs ++ post`. The size lemma is `efBytes_size`.

Check (d) is now literally `(1 + r_top)·Σ_i eq(r_lo, i) s_i + r_top·p̃ub(r_u)`.

## `SpartanChainVerifier.lean` (namespace `SpartanChain.Leaf`)

**Definitions.**

- **`kap n := Nat.clog 2 n`**, the same as `SpartanChainSoundnessLog`.
- **`snarkSize κ = size1 + msgsBytes + size2`** (§7).
- **`leafSize n`**: `80` for `n = 0`, otherwise `80 + snarkSize`. `leafSize_ge` proves it is at
  least 80.

**`snarkProg ev s n h π_S`** runs §6.2 steps 1–13. Every query goes through
`Transcript.seed/absorb/squeeze/squeezeN` and `Merkle.verify`.

1. `seed s n h` (step 1).
2. `Ligero.verify1` (steps 2–4).
3. `Spartan.verify` (steps 5–10, checks (a)–(e)).
4. `finalCheck` (check (f)): `c = W̃(r'')·Σ_j eq(r''_lo, j) v_j`.
5. `Ligero.verify2` (steps 11–13), with `a = eqTable(r''_hi)`.

The fields are read at the §7 offsets `off₁`, `off₂` and `off₃`.

**`leafVerifier ev : LeafVerifier`** is the instance for `SpartanChainVerifierTop`.

**L-Q1, `queries_le`.** For `n ≤ 2^20`, every oracle and every `π_S`, the SNARK makes at most
`2^14` queries.

- The per-phase counts are lemmas:
  - `len_verify1`: `2 + m`;
  - `len_spartan`: `5ℓ_y + 9 + 2ℓ_q`;
  - `len_verify2`: `1 + J + 260(1 + ℓ_N)`;
  - also `len_absorbRounds`, `len_mverify` and `len_squeezeE`.
- `qBound_le : ∀ κ ≤ 20, qBound κ ≤ 2^14` is checked by `decide`. At `κ = 20` the bound is
  7 774, as in §6.3.

## `SpartanChainProver.lean`

- **`proveSnark wf s n`** runs:
  1. `seed`;
  2. `Ligero.commit`;
  3. `Ligero.prove1`;
  4. `Spartan.prove`, which now also returns `r''`;
  5. `Ligero.prove2` with `eqTable(r''_hi)`.

  It writes the bytes `root ‖ ū ‖ encodeMsgs ‖ v ‖ openings`.
- **`proveLeaf`** prepends the 80-byte `leafHeader` (`enc64 0 ‖ s ‖ enc64 n ‖ h`).
- **`snark_complete`.** Assume `HonestOps ev wf`: for every true statement the tables and the
  evaluators satisfy `Spartan.Honest` for some R1CS. Then for every oracle `H` and
  `1 ≤ n ≤ chainCap`, `snarkProg ev s n (chainEnd s n)` accepts `(proveSnark wf s n).run H`.
  - It composes `Ligero.prove1_verify1`, `Spartan.complete`, `parseMsgs_encodeMsgs`,
    **`evalClaim_eq`** and `Ligero.verify2_complete`.
  - **`evalClaim_eq`** is check (f) for the honest `v`: `Σ_j b_j (Σ_i a_i Q[i][j]) = q̃(r'')`.
    It uses `mleEval_split`, `matrixRows_getD` and `combRows_getD`.
  - It also uses the byte lemmas `extract_pre`, `extract_mid`, `extract_suf` and
    `readLabel_bytesOf`.

## `SpartanChainRun.lean`

- `Run.Ops` holds `ev` and `wf`.
- `verifyProof` is `vb (leafVerifier ev)`.
- `verifySnark`, `proveLeafBytes` and `verifyFile` run under `blake2sOracle`.
- There is no `main`.

## Size (§7)

- `openings_size`: the honest openings take `tQ · openW κ` bytes.
- `snark_size`: the honest SNARK takes `snarkSize (kap n)` bytes, for every oracle. No honesty
  hypothesis is needed.
- `proveLeaf_size`: the honest leaf proof takes `leafSize n` bytes.
- `leafSize_table`, by `decide`: `leafSize 16 = 143 711`, `leafSize 2 = 100 119`,
  `leafSize 1 = 95 719`, `leafSize 0 = 80`. These equal the sizes of the Rust leaf files.

## Compiled run (task 3), `logs/spartan-chain/leaf-snark/`

**Setup.**

- The Lean verifier is `vb (leafVerifier chainEvals)`, with `chainEvals` from the BLAKE2s
  agent's `SpartanChainChainEval`.
- It is compiled as the scratch executable `leaf-run`:
  - source: `rf-core-sc/scratch/leaf/LeafMain.lean`;
  - a `[[lean_exe]]` block added to the scratch lakefile;
  - build log: `exe-build.log`.
- Rust proofs come from `cargo build --release --offline`, with `CARGO_TARGET_DIR` in
  `scratch/leaf/target` (`cargo-build.log`).
- Inputs: start `ab…ab` for the single leaves; a smoke tree with `r = 2`, `n = 16` and starts
  `01…`, `02…`, `03…`, `04…`.
- Statements are computed by Python `hashlib`.

**Lean `V` on the Rust proofs** (`verify-leaves.log`, `verify-tree.log`; load average ≈ 4.5):

| proof | bytes | Lean `vb` | Lean time | Rust time |
|---|---|---|---|---|
| leaf `n = 1` | 95 719 | accept | 138–153 ms | 62.5 ms |
| leaf `n = 2` | 100 119 | accept | 140–158 ms | |
| leaf `n = 16` | 143 711 | accept | 211–227 ms | 92.1 ms |
| smoke leaves L0–L3 (`n = 16`) | 143 711 | accept | 227–289 ms | |
| nodes N1_0, N1_1 | 287 512 | accept | 1.01–1.06 s | |
| **smoke root** | 575 112 | **accept** | **2.25–2.50 s** (process wall 3.45 s, 123 MB) | 0.188 s |

- **Negative control.** One flipped byte (byte 1000) is rejected for every proof.
- **Canaries** (`canaries.log`) on the `n = 1` leaf, the `n = 16` leaf, node N1_0 and the root:
  - the honest proof is accepted;
  - five changes are each rejected: one byte appended, the last byte removed, the last byte
    flipped, a middle byte flipped, and one statement bit flipped.
  - **Node rejection is slow.** Even an immediate rejection of a node, root or level 1, costs
    0.3–0.67 s. The time goes to the node codec's decode, so `checkNode` should test the size
    and statement before decoding.
- **Where the time goes.**
  - `chainMats` alone takes about 80 ms per leaf at `κ = 4` (`bench-mats.log`), and `chainPub`
    under 1 ms.
  - At the root, about 1.2 s is the node branch of `SpartanChainVerifierTop`: decoding and
    re-encoding the subproofs. That is not the SNARK.
- **Over budget.** The root is just above the `T_V = 2 s` mark of review BP-m8. The node codec is
  the first thing to speed up.
- **Query count.** Rust reports 3 533 queries at `n = 16` and 2 977 at `n = 1`. This matches
  §6.3 and is below `qBound`.

**Prover byte-identity (Lean `proveLeaf` against the Rust bytes for `n ∈ {1, 2, 16}`): not run
yet.** The Chain modules still do not expose the prover's tables.

What is missing, precisely: a `Leaf.WitFor` (`κ → n → s → Spartan.Witness`) with these fields:

- `az`, `bz`, `cz : Array EF`, of size `2^(15+κ)`: the bit tables of Rust `chain::witness`;
- `z : Array F`, Boolean, `(w ‖ pub)`;
- `q : Array F`, of size `2^(8+κ)`: the packed `w`, word `u'` holding bits `64u' … 64u'+63`;
- `innerTab : List EF → EF → Array EF`, the table `M̃_ρ(r_x, ·)`. It needs a Lean port of Rust
  `Circuit::transpose` and the wiring and tail columns.

The proof side additionally needs `HonestOps chainEvals wf`. A watcher runs until these appear;
the KAT is then `leaf-run` with a `prove` command against `scratch/leaf/data/l{1,2,16}.bin`.

## Open

- **Merging further.** Ligero's `chunk_getD` and my `flatMap_getD` overlap. This is harmless.
