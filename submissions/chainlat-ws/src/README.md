The prover's sources, for readers. The evaluation builds only prover/*.s
(prover.s is `gcc -S -O2 -mavx512f -mavx512vl -mbmi2 -pthread chainwalk.c` through
harness/tools/asm-compat.py).

- chainwalk.c  the prover: protocol (PROVER.md), file format (FORMAT.md), kernels,
               dispatch and per-request self-check
- gen_xmm.py   the generator of k_vec: one lane per xmm register, pi as a symbolic
               register renaming (emits xmm_kernel.h, included by chainwalk.c)
- kernels.c    the kernel development file with the three-way differential self-test
