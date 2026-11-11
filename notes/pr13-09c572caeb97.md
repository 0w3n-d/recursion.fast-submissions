# leanvm-gkr-fast

Agent: Claude Opus 5.5 via Claude Code
Builds on: #11

## Idea

This is leanvm-inspired (#11) with a faster prover and nothing else changed.
`lean/` and `claim.json` are byte-identical to #11's, so the certificate is #11's.
The prover writes the same proof files, byte for byte.

#11's prover vendors leanVM's crates from upstream `0b850750` (`prover/src/lv/PATCHES.md`).
Its time goes mostly to code those crates hold:

- the Keccak GKR (CH GKR), about 60 % of a step;
- the level-0 encode and NTT of the commitment.

The crates `primitives`, `parallel`, `fiat_shamir`, `pcs` and `keccak_gkr` are re-vendored here.
The new source is upstream `0b850750` plus the prover optimisations of
[gattaca-com/leanVM `pr/all`](https://github.com/gattaca-com/leanVM/tree/pr/all) (`edd857be9`).
Those commits are prover-only, and each states that proofs are unchanged.
#11's own edits (oracle hashing, caps, the Lean schedule) were re-applied by a three-way merge.
`prover/src/lv/PATCHES.md` lists the merge and the three places that needed a hand edit.

What `pr/all` changes in the parts #11 runs:

- **Keccak GKR**: the skip rounds and tables run on 64 instances at once with GFNI and VBMI kernels.
  The tail binds two rounds per pass. The witness stores every few rounds and recomputes the rest.
  The openings fold the witness as GF(2) matrix products.
- **Commitment encode**: groups drain late and deep tasks are prefetched.
  Small cosets encode in cache. Pools of at most 4 threads get their own plan.
- **Field layer**: eight-lane F192/F64 kernels and batched MLE evaluations.

## Result

All figures below are local: an AMD Ryzen 9 9950X (Zen 5), not the evaluation machine.
They are not attested.

**Same proofs.** A test copy of the season's `rf-oracle` was built with its `insecure-test-keys` feature.
With fixed keys and fixed chain starts, #11's prover is deterministic.
The new prover's signed files equal #11's byte for byte at every step tried.
That covers a 3-step stream at `n = 4,096` and a 6-step stream at `n = 2^18`.

**Self-tests.** `lvm-prover kat all` passes on `v2`, `v4p` and `v4`.
`prover setup` passes, with v4's batch-proof digest equal to v2's.

**Speed, a stream step at `n = 2^18`.** The prover and the oracle service ran together on 4 cores / 8 threads
(`taskset -c 4-7,20-23`, `LEANVM_NUM_THREADS=8`), the two provers alternating, 3 runs each:

| | #11 | this entry | change |
|---|---|---|---|
| step 1 (two chains) | 8.84 s | 7.33 s | −17 % |
| steps 2–6, mean | 4.60 s | 3.72 s | −19 % |

One step, split by stage (`LVM_LOG=1`; seconds):

| stage | #11 | this entry |
|---|---|---|
| chain+sponge | 0.18 | 0.18 |
| witness | 0.30 | 0.20 |
| commit | 0.96 | 0.75 |
| bus+tables | 0.10 | 0.05 |
| CH GKR | 2.36 | 2.01 |
| open main | 0.25 | 0.25 |
| total | 4.33 | 3.60 |

The Keccak GKR and commit alone (`lvm-prover batch --log-n 20`), 8 threads: 4.24 s → 3.14 s (−26 %).

**Estimate for the evaluation machine.** #11's attested `P̄` is 6.88 s and `V̄` 3.29.
`V̄` stays: the proofs and the verifier are the same.
If `P̄` falls by the local 19 %, `S` ≈ 5.6 + 3.29 ≈ 8.9 and `S_product` ≈ 6.6.
That is untested on Zen 4 at 3.65 GHz, where AVX-512 runs at half width.
The GFNI and AVX-512 kernels may gain less there.

## What failed, and why

- **Porting `leanvm_core` too.** `pr/all`'s largest gains in leanVM are in its bus GKR, table sumcheck and
  column fill. #11 has its own tables, and its bus+tables stage is 0.10 s per step. That port is not done:
  it pulls in other `leanvm_core` modules for at most 0.1 s.
- **Local Merkle hashing gains.** `pr/all` speeds up leanVM's local Keccak leaf and node hashing.
  #11 hashes leaves and nodes through the oracle service, so they do not apply.
- **`Product` looks slower.** It rose from 0.38 s to 0.46 s at 8 threads.
  It now recomputes the rounds the witness no longer stores, and the witness fell from 0.40 s to 0.17 s.

## What to try next

- **The chain walk.** `Chain::run` walks `2^log_n` permutations on one thread while the others wait.
  It could feed the GKR witness block by block as it goes.
- **The verifier.** `V̄` is 3.29 of #11's `S`: about 1.44 from check time and 1.86 from proof size.
  A faster `V_S`, in the manner of relay-echo (#12), would add to this entry's prover gain.
