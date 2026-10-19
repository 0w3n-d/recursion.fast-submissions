The succinctness cap T_V = 2 s does not exclude the witness-sending argument, and board T rewards avoiding recursion

## Summary

DESIGN-v3 §6.5 separates SNARKs from the witness-sending argument by measuring the wall time of the
root check against `T_V = 2 s`. The design claims a margin of 10× or more. Measured: the certified
witness-sending verifier checks the whole ranked tree in about 21 s with the contract's reference
BLAKE2s. With `Task.spawn` (kernel-transparent) the same check takes 1.2–1.3 s, and an unrolled
BLAKE2s with `Task.spawn` takes 37–43 ms. Both are under the cap, so a certified entry that proves
nothing can win board T. Separately, board T does not reward recursion: a prover may send witnesses
below level `j` and recurse only above it. This saves node proofs, contrary to §5.3 and §6.7.

## The problem

**(a) The cap.** §6.3 step 4 says: "Root check … the compiled `Vb` on `(treeRoot, root.bin)`;
must accept. **Succinctness cap**: its wall time must be ≤ `T_V` (§6.5)." §6.5 calibrates it as
"`T_triv ≥ 5 · T_V` … at `r = 8`, `n = 2^14` the trivial root check takes 22–29 s". That figure
uses the reference `Contract/Hash/Blake2s.lean` at about 6 µs per compression. A submitter is not
bound to that implementation, and wall time rewards threads.

- `Task.spawn`/`Task.get` are core definitions with transparent kernel bodies. A parallel check
  is therefore *provably equal* to the sequential one, the existing certificate carries over
  unchanged, and the source rule accepts the file (0 findings).
- A BLAKE2s with its state in sixteen `UInt32` locals, fully unrolled, in core Lean with no
  `extern`, agrees with `hashlib` on a known-answer chain. It still has to be proved equal to
  `chainStep`, a finite symbolic unfolding that this probe does not do.

**(b) Recursion.** §6.7: "Recursion only near the root, concatenation below: allowed; the first
recursing node arithmetises `2^j` verifications and pays in `T_tree`." §5.3: "a prover cannot
flatten the tree". In fact, witness-sending proofs below level `j` cost nothing to produce (the
chain starts, 48 bytes per leaf). The `2^{8−j}` nodes at level `j` prove "both witness-sending
children are accepted", which is the in-circuit chain work an honest leaf proof would do anyway.
The prover makes `2^{8−j} − 1` recursive node proofs instead of 255. At `j = 8` it makes one flat
SNARK over all `2^22` compressions and no recursion at all. KS still guarantees that valid child
proofs exist, but not that they were produced by recursion.

## Why it matters

- (a) An honest, certified, non-succinct entry passes the root check. Its tree run is native
  hashing of the chains, about 2.1 ms per chain of `2^14` steps in Rust on the same VM
  (`logs/probes/fieldbench.log`), so about 20 ms on 32 cores. It beats every SNARK on board T. Raising `n` (the §6.5 calibration rule) does not close the gap. At
  `n = chainCap = 2^20` the threaded unrolled check scales to about 2.6 s (64 × 40 ms), against the
  required `5 · T_V = 10 s`.
- The calibration also depends on how well the trivial baseline is implemented. A quality
  difference of about 500× (21 s against 40 ms) is larger than any margin the rule can set.
- (b) Board T prices proving work, not recursion. The canaries and the sample checks pass. A
  level-7 witness-sending proof verifies in `2^21` compressions, about 12 s at reference speed,
  within `verify_s = 60 s`. Only memory (96 GB) and parallel efficiency bound `j`.

## Evidence (measured)

All measured on the development VM: a QEMU virtual CPU, 32 vCPUs, AVX2, **no
`pclmulqdq`/`gfni`**. This is **not the reference machine** (O-6). Whole ranked tree, `r = 8`,
`n = 2^14`, `2^22` compressions, three runs each. The logs are local to the submissions repository.

| Root check: `V`'s chain check | Time | Log |
|---|---|---|
| certified witness-sending `Vb` (S2a entry), reference BLAKE2s, sequential, end to end | **20.87 / 21.23 / 21.16 s** (about 5.0 µs per compression) | `logs/V3-S2/calibration-r8-n16384.log` |
| reference BLAKE2s, chains only, sequential | 5.6–6.1 µs per compression, about 24 s | `logs/adv-probes/refchain.log` |
| **reference BLAKE2s + `Task.spawn`**, chains only | **1.17–1.31 s** | `refchain.log` |
| unrolled BLAKE2s, sequential | 151–164 ns per compression, **0.64–0.69 s** | `logs/adv-probes/fastchain.log` |
| **unrolled BLAKE2s + `Task.spawn`** | **37–43 ms** | `fastchain.log` |

The `Task.spawn` rows are chain-only microbenchmarks (`RefChain.lean`, `FastChain.lean`). No
threaded `Vb` was built as a certified entry. The kernel fact that makes the certificate carry over
is checked (`logs/adv-probes/TaskRfl.lean`):

```lean
theorem spawn_get {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl
theorem all_par (cs : List Nat) (p : Nat → Bool) :
    ((cs.map fun c => Task.spawn fun _ => p c).all fun t => t.get) = cs.all p := by
  induction cs <;> simp_all [Task.spawn]
-- #print axioms all_par: [propext]
```

## Proposed fix (ADV1; all three parts are needed for (a))

1. **Measure CPU time** (user + system) of the root check, or run it pinned to one core. This
   removes threads. Cost: one harness change. Side effect: a verifier may no longer use
   parallelism to meet `T_V`. That was never the intent of a succinctness cap.
2. **Calibrate against the best linear verifier.** The organiser publishes an optimised
   compiled-Lean chain checker (for example `FastChain.lean`'s `stepU`, proved equal to
   `chainStep`) and sets `T_V ≤ T_triv,best / 10`. At the ranked size that is about 65 ms of CPU
   time on this VM. A FRI- or WHIR-shaped verifier with about `2^15` compressions at 160 ns plus
   about `2^16` field operations fits only if it is written with the same care. That ties `T_V` to
   compiled field speed (O-9; see the hygiene issue). If 65 ms is too tight for compiled Lean,
   change the benchmark instead: fewer and longer leaves (for example `r = 4`, `n = 2^20`).
3. **Make it deterministic**: O-18, a step count of an organiser-compiled RISC-V image of `Vb`.
   It also removes threads and machine noise.

For (b) (design decision): apply the CPU-time cap to sampled proofs **at every level**. A
witness-sending proof at level `j` costs `2^{j+14}·160 ns`: about 42 ms at `j = 4` and 84 ms at
`j = 5`. A 65 ms cap therefore forces recursion from level 5 up, but not below. Forcing it at every
level needs `n ≈ 2^20 = chainCap`. The alternative is to rank column R beside T. In either case,
correct §5.3 and the §6.7 row ("pays in `T_tree`"), and §6.5's "22–29 s" and "margin 10×".

## Cross-references

ADV-M1, ADV-M4, ADV-m4 (documentation drift), ADV-m6 (core `extern`s such as `Task.spawn` in the
trust statement; see the hygiene issue); DESIGN-v3 §5.3, §6.3 steps 4–5, §6.5, §6.7, §7.3 ("about
25 s"); O-6, O-9, O-18; S2a RESULT (submissions repository, `docs/stages/V3-S2a-RESULT.md`).
