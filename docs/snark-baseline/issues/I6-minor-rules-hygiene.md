Minor rules and hygiene findings against the v3 pin: fallback completeness, repeated runs, AGENTS.md drift, gate rule 4, trust statement, Fintype Digest, allowlist, compiled field speed

## Summary

Ten minor items from an independent review of the rules (ADV1, ADV-m1 … m7) and from the honest
baseline's feasibility work (F1 §7.3). None blocks certification on its own. Each is a place
where the rulebook, the harness or the trust statement does not match the contract at `15e4ae5`,
or where a measured cost will steer entrants. Each item can be fixed separately.

## Items

**1. Completeness through a fallback branch is vacuous, and liveness tests only the fallback
(ADV-m1).** Take `V = SNARK ∨ witness-sending` with `P` the witness-sending prover. Then `Complete`
(`Security.lean:74-76`) is the baseline's proof, and nothing about the scored SNARK path is ever
proved complete. The liveness check of §6.3 step 8 then runs that `P` (no queries, an empty log)
and the 8-instruction copy image. *Fix:* run liveness on the **native prover's** proofs, with a
query log that the native prover must emit. The harness checks that every entry hashes correctly
and that the log contains `V`'s queries, then runs `img`. The output is decidable: `Rel` for a
leaf, and `Vb` on the extracted children for a node.

**2. Repeated runs on the same instances (ADV-m3).** §6.3 step 9 says "Repeat steps 3 to 6 three
times on the same instances; `T_tree` and `T_root` are medians". It does not require a fresh `DIR`
per repetition. A prover that finds its previous `root.bin`, or a cache outside `DIR`, makes two of
the three runs instant, and the median is the cached time. *Fix:* carry over v2's rule to every
repetition: a fresh step directory, which is the only writable path (v2's harness README at the
tag `v2-archive`; in the submissions repository's copy, `docs/core/harness-README.md:295-300`).

**3. `AGENTS.md` misstates the contract (ADV-m4).** The contract is what the harness checks, so a
submitter who follows the rulebook is misled.

| `AGENTS.md` | Says | The contract at the pin says |
|---|---|---|
| `:46` (and DESIGN §2.1) | `abbrev Digest := Fin 32 → UInt8` | `Vector UInt8 32` (`Relation.lean:35`) |
| `:49` | `chainEnd … := (blake2s256 ∘ bytes)^[n] s`, untagged | `chainStep d = blake2sDigest (tagChain :: d.toList)` (`:66`) |
| `:58` | leaf clause `c = leafStmt (chainEnd s n) n` | also `n ≤ chainCap` (`:88`) |
| `:78`, `:87`, `:148`, `:220` | `fuel : ℕ → ℕ → ℕ`, `B p l = 2^40 + 2^8·(p + l)` | `fuel : ℕ → ℕ` over tape words, `B t` (`Extractor.lean:92`), plus an image-size conjunct (`Certificate.lean:69-70`) |
| `:146-147` | `ImageComputes` for "`L` of at most `2^24` entries" | removed by the S1 fix of M3; the only bound is a tape of `≤ 2^60` words (`Extractor.lean:105`) |
| `:90` | `S.img = D.img` is in `Certificate` | it is in `CertificateR` (`Certificate.lean:86-88`) |
| `:406-408` | "Your proof system never queries a string the relation hashes" | S1 m7 reworded this in `Relation.lean:19-20`; `AGENTS.md` still has the old claim |

DESIGN §6.5's "22–29 s … margin 10×" and §6.7's "pays in `T_tree`" are refuted separately (see
the `T_V` issue).

**4. Gate rule 4 still lists v2 fields (ADV-m5).** `scripts/Gate.lean:250-255`, `badgeFields`,
contains `(`RecursionFast.Submission, [`P, `cfg])`. On a v3 `Submission` that does not compile as
a whole (for example one with a noncomputable `ε`), it fails closed ("no field cfg") and never
checks `V`, `E` or `img`. The S2a baseline passed only because its `submission` compiles as a
whole. *Fix (S3, already planned in DESIGN §10):* list `V`, `P`, `E`, `img`.

**5. The trust statement should name core `extern`s (ADV-m6).** DESIGN §8 item 6 trusts "what
Lean's compiler emitted for `Vb` and `P`". Entries may call core functions whose compiled code is
an `extern` with a Lean reference body: `Task.spawn`/`Task.get` (whose kernel body is transparent,
`(Task.spawn f).get = f ()` by `rfl`), and the `Array`/`ByteArray` primitives. Their agreement with
those bodies is an extra trusted assumption. The badge `verify` may also be multi-threaded. *Fix:*
name them in §8, or restrict them on the badge path (see the `T_V` issue).

**6. Restate the paper theorem's domain (ADV-m7).** After the `logCap` amendment, `(Q + qV)·ε`
holds for `Q + qV ≤ min(logCap, ≈2^57)`. The second bound is the extractor's addressable tape:
`ImageComputes` covers tapes of `≤ 2^60` words, and each log entry takes at least 5 words. DESIGN
§4.5 and `AGENTS.md` §5 quote `2^64` queries without that domain.

**7. No `Fintype Digest` at the pin.** The library counts through `Nat.card` and an equivalence
(`Library/Security.lean:37`, `card_digest : Nat.card Digest = 2 ^ 256`). Mathlib v4.34.1 has no
`Fintype` instance for core `Vector`. Checked with `import Mathlib`:
`#synth Fintype (Vector UInt8 32)` fails ("failed to synthesize") (local log:
`logs/issue-probes/FintypeDigest.log`). The potential form of the KS amendment sums over answers,
so it needs a contract instance (`Fintype.ofEquiv (Fin 32 → Fin 256) …`) or an explicit sum over
`Fin 32 → Fin 256`.

**8. ArkLib is not allowlisted.** `AGENTS.md:320`: "The rest of CompPoly, and ArkLib, VCVio and
PolyFun, are not in the allowlist." At the pin there is no `scripts/import-allowlist.txt` yet: S2
and S3 regenerate it. The S2a run generated 10,777 modules locally with `gate --closure`. Any
entry that wants ArkLib's unique-decoding folding lemma (Binary Basefold, ArkLib #383; O-22) must
re-prove it from Mathlib, copy a closure that uses only Mathlib and CompPoly, or wait for an
allowlist extension (S4). *Ask:* state in DESIGN §9 and `AGENTS.md` §10 which of the three the
organiser intends, and when.

**9. Compiled field speed decides `T_V` (O-9 reframed).** Measured with CompPoly at `572f997`,
compiled, on the development VM: a QEMU virtual CPU, 32 vCPUs, AVX2, **no
`pclmulqdq`/`gfni`**, which is **not the reference machine** (`logs/probes/e2/bfbench.log`,
local):

| Operation | Per op |
|---|---|
| `BF64` mul+add | 29.7 µs |
| `Ext3` mul+add | 415 µs |
| `BF64` inverse (Itoh–Tsujii) | 1.72 ms |
| unverified `UInt64` loop, carry-less multiply plus reduce, 64 iterations | 1.47 µs |
| Rust GF(2^64), naive loop (`logs/probes/fieldbench.log`) | 22 ns |

`BitVec 64/128` compiles to `Nat` bignum arithmetic, which explains the gap. A WHIR-class verifier
does about `10^4`–`10^5` extension multiplications (R7 §5.3), which is 4–40 s at 415 µs, far above
`T_V = 2 s`. O-9 says "now a library and `T_V` concern only". The concern is binding: with
CompPoly's field, no succinct verifier meets the cap. *Fix (library):* a word-level `BF64`/`Ext3`
proved equal to CompPoly's. The S2b entry is building one (decision D-5); the organiser library
could host it.

**10. Perfect completeness ∀H and the counted form.** S1 m10 is not applied: DESIGN §6.6's `δ` row
and §6.7's grinding row still assume `CompleteWithError`, which does not exist (ADV-m2). This is
tracked in the honest-recursion issue with O-23.

## Cross-references

ADV-m1 … m7; F1 §7.3 items 7–9; V3-S1-m7, V3-S1-m10, V3-S1-M3; DESIGN-v3 §4.5, §6.3, §8, §9, §10,
§12 (O-9, O-22, O-23); the KS, `T_V` and honest-recursion issues; the library issue on the
witness-sending verifier and quadratic decoding.
