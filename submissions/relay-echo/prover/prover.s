	.file	"prover.c"
	.text
	.p2align 4
	.type	chain_two, @function
chain_two:
.LFB7384:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	leaq	chain2_avx512vl(%rip), %rax
	movq	%rsi, %r15
	movq	%rdx, %rsi
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	movq	%rcx, %r14
	leaq	chain2_avx512vln(%rip), %rdx
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	movq	%r8, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movslq	%edi, %r12
	movq	%r15, %rdi
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	movq	%rcx, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$8, %rsp
	.cfi_def_cfa_offset 64
	movq	64(%rsp), %rbx
	cmpq	%rcx, %rbx
	movq	%r9, %rcx
	cmovbe	%rbx, %r14
	cmpl	$4, %r12d
	cmove	%rdx, %rax
	movq	%r13, %rdx
	movq	%r14, %r8
	call	*%rax
	cmpq	%rbp, %rbx
	jnb	.L3
	leaq	k_fn(%rip), %rax
	movq	%rbp, %rdx
	movq	%r15, %rsi
	movq	%r15, %rdi
	movq	(%rax,%r12,8), %rax
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	subq	%r14, %rdx
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	jmp	*%rax
	.p2align 4,,10
	.p2align 3
.L3:
	.cfi_restore_state
	cmpq	%rbx, %rbp
	jnb	.L1
	leaq	k_fn(%rip), %rax
	subq	%r14, %rbx
	movq	%r13, %rsi
	movq	%r13, %rdi
	movq	(%rax,%r12,8), %rax
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%rbx, %rdx
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	jmp	*%rax
.L1:
	.cfi_restore_state
	popq	%rax
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE7384:
	.size	chain_two, .-chain_two
	.p2align 4
	.type	k_find, @function
k_find:
.LFB7382:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	leaq	k_name(%rip), %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	xorl	%ebx, %ebx
.L11:
	movq	0(%rbp,%rbx,8), %rsi
	movq	%r12, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L10
	addq	$1, %rbx
	cmpq	$5, %rbx
	jne	.L11
	movl	$-1, %eax
.L9:
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.L10:
	.cfi_restore_state
	movl	%ebx, %eax
	jmp	.L9
	.cfi_endproc
.LFE7382:
	.size	k_find, .-k_find
	.p2align 4
	.type	chain2_avx512vln, @function
chain2_avx512vln:
.LFB7376:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %rax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	andq	$-64, %rsp
	addq	$-128, %rsp
	vmovdqu	(%rax), %ymm1
	vmovdqu	(%rcx), %ymm2
	vmovdqa	.LC0(%rip), %ymm0
	movq	%fs:40, %rsi
	movq	%rsi, 120(%rsp)
	movq	%rdx, %rsi
	movq	%rsp, %rdx
	vpermi2q	%ymm2, %ymm1, %ymm0
	vmovdqa	%ymm0, (%rsp)
	vmovdqa	.LC1(%rip), %ymm0
	vpermi2q	%ymm2, %ymm1, %ymm0
	vmovdqa	%ymm0, 32(%rsp)
	testq	%r8, %r8
	je	.L16
	leaq	vla_k(%rip), %rax
#APP
# 2625 "keccak_vlasm.inc" 1
	vmovdqu64 0(%rsp), %xmm26
	vmovdqu64 16(%rsp), %xmm27
	vmovdqu64 32(%rsp), %xmm28
	vmovdqu64 48(%rsp), %xmm29
	1:
	vpsllq $8, %xmm26, %xmm0
	vporq 384(%rax), %xmm0, %xmm0
	vpsrlq $56, %xmm26, %xmm30
	vpsllq $8, %xmm27, %xmm1
	vporq %xmm30, %xmm1, %xmm1
	vpsrlq $56, %xmm27, %xmm30
	vpsllq $8, %xmm28, %xmm2
	vporq %xmm30, %xmm2, %xmm2
	vpsrlq $56, %xmm28, %xmm30
	vpsllq $8, %xmm29, %xmm3
	vporq %xmm30, %xmm3, %xmm3
	vpsrlq $56, %xmm29, %xmm4
	vporq 400(%rax), %xmm4, %xmm4
	vmovdqa64 416(%rax), %xmm16
	vmovdqa64 %xmm0, %xmm25
	vpxorq %xmm16, %xmm1, %xmm26
	vmovdqa64 %xmm2, %xmm27
	vmovdqa64 %xmm3, %xmm28
	vmovdqa64 %xmm4, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $44, %xmm25, %xmm6
	vprolq $43, %xmm26, %xmm12
	vprolq $21, %xmm27, %xmm18
	vprolq $14, %xmm28, %xmm24
	vpandnq %xmm12, %xmm6, %xmm30
	vpxorq %xmm0, %xmm30, %xmm30
	vpandnq %xmm18, %xmm12, %xmm31
	vpxorq %xmm6, %xmm31, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm18, %xmm12
	vpternlogq $0xD2, %xmm0, %xmm24, %xmm18
	vpternlogq $0xD2, %xmm6, %xmm0, %xmm24
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $28, %xmm3, %xmm3
	vprolq $20, %xmm28, %xmm9
	vprolq $3, %xmm29, %xmm10
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $45, %xmm16, %xmm16
	vprolq $61, %xmm26, %xmm22
	vpandnq %xmm10, %xmm9, %xmm0
	vpxorq %xmm3, %xmm0, %xmm0
	vpandnq %xmm16, %xmm10, %xmm6
	vpxorq %xmm9, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm22, %xmm16, %xmm10
	vpternlogq $0xD2, %xmm3, %xmm22, %xmm16
	vpternlogq $0xD2, %xmm9, %xmm3, %xmm22
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $1, %xmm1, %xmm1
	vprolq $6, %xmm26, %xmm7
	vprolq $25, %xmm27, %xmm13
	vprolq $8, %xmm28, %xmm19
	vprolq $18, %xmm29, %xmm20
	vpandnq %xmm13, %xmm7, %xmm3
	vpxorq %xmm1, %xmm3, %xmm3
	vpandnq %xmm19, %xmm13, %xmm9
	vpxorq %xmm7, %xmm9, %xmm9
	vpternlogq $0xD2, %xmm20, %xmm19, %xmm13
	vpternlogq $0xD2, %xmm1, %xmm20, %xmm19
	vpternlogq $0xD2, %xmm7, %xmm1, %xmm20
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $27, %xmm4, %xmm4
	vprolq $36, %xmm29, %xmm5
	vprolq $10, %xmm25, %xmm11
	vprolq $15, %xmm26, %xmm17
	vprolq $56, %xmm27, %xmm23
	vpandnq %xmm11, %xmm5, %xmm1
	vpxorq %xmm4, %xmm1, %xmm1
	vpandnq %xmm17, %xmm11, %xmm7
	vpxorq %xmm5, %xmm7, %xmm7
	vpternlogq $0xD2, %xmm23, %xmm17, %xmm11
	vpternlogq $0xD2, %xmm4, %xmm23, %xmm17
	vpternlogq $0xD2, %xmm5, %xmm4, %xmm23
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $62, %xmm2, %xmm2
	vprolq $55, %xmm27, %xmm8
	vprolq $39, %xmm28, %xmm14
	vprolq $41, %xmm29, %xmm15
	vprolq $2, %xmm25, %xmm21
	vpandnq %xmm14, %xmm8, %xmm4
	vpxorq %xmm2, %xmm4, %xmm4
	vpandnq %xmm15, %xmm14, %xmm5
	vpxorq %xmm8, %xmm5, %xmm5
	vpternlogq $0xD2, %xmm21, %xmm15, %xmm14
	vpternlogq $0xD2, %xmm2, %xmm21, %xmm15
	vpternlogq $0xD2, %xmm8, %xmm2, %xmm21
	vpxorq 0(%rax), %xmm30, %xmm30
	vpxorq %xmm0, %xmm30, %xmm25
	vpxorq %xmm3, %xmm25, %xmm25
	vpternlogq $0x96, %xmm4, %xmm1, %xmm25
	vpxorq %xmm6, %xmm31, %xmm26
	vpxorq %xmm9, %xmm26, %xmm26
	vpternlogq $0x96, %xmm5, %xmm7, %xmm26
	vpxorq %xmm10, %xmm12, %xmm27
	vpxorq %xmm13, %xmm27, %xmm27
	vpternlogq $0x96, %xmm14, %xmm11, %xmm27
	vpxorq %xmm16, %xmm18, %xmm28
	vpxorq %xmm19, %xmm28, %xmm28
	vpternlogq $0x96, %xmm15, %xmm17, %xmm28
	vpxorq %xmm22, %xmm24, %xmm29
	vpxorq %xmm20, %xmm29, %xmm29
	vpternlogq $0x96, %xmm21, %xmm23, %xmm29
	vprolq $1, %xmm25, %xmm8
	vprolq $1, %xmm27, %xmm2
	vpxorq %xmm2, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm2
	vpxorq %xmm8, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm8
	vpxorq %xmm2, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm2
	vpxorq %xmm8, %xmm29, %xmm29
	vpxorq %xmm2, %xmm27, %xmm27
	vpxorq %xmm29, %xmm30, %xmm30
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $43, %xmm13, %xmm13
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $21, %xmm17, %xmm17
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $14, %xmm21, %xmm21
	vpandnq %xmm13, %xmm6, %xmm2
	vpxorq %xmm30, %xmm2, %xmm2
	vpandnq %xmm17, %xmm13, %xmm8
	vpxorq %xmm6, %xmm8, %xmm8
	vpternlogq $0xD2, %xmm21, %xmm17, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm17
	vpternlogq $0xD2, %xmm6, %xmm30, %xmm21
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $28, %xmm18, %xmm18
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $20, %xmm22, %xmm22
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $3, %xmm3, %xmm3
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $45, %xmm7, %xmm7
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $61, %xmm14, %xmm14
	vpandnq %xmm3, %xmm22, %xmm30
	vpxorq %xmm18, %xmm30, %xmm30
	vpandnq %xmm7, %xmm3, %xmm6
	vpxorq %xmm22, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm14, %xmm7, %xmm3
	vpternlogq $0xD2, %xmm18, %xmm14, %xmm7
	vpternlogq $0xD2, %xmm22, %xmm18, %xmm14
	vpxorq %xmm25, %xmm31, %xmm31
	vprolq $1, %xmm31, %xmm31
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $6, %xmm10, %xmm10
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $25, %xmm19, %xmm19
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $8, %xmm23, %xmm23
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $18, %xmm4, %xmm4
	vpandnq %xmm19, %xmm10, %xmm18
	vpxorq %xmm31, %xmm18, %xmm18
	vpandnq %xmm23, %xmm19, %xmm22
	vpxorq %xmm10, %xmm22, %xmm22
	vpternlogq $0xD2, %xmm4, %xmm23, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm4, %xmm23
	vpternlogq $0xD2, %xmm10, %xmm31, %xmm4
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $27, %xmm24, %xmm24
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $36, %xmm0, %xmm0
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $10, %xmm9, %xmm9
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $15, %xmm11, %xmm11
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $56, %xmm15, %xmm15
	vpandnq %xmm9, %xmm0, %xmm31
	vpxorq %xmm24, %xmm31, %xmm31
	vpandnq %xmm11, %xmm9, %xmm10
	vpxorq %xmm0, %xmm10, %xmm10
	vpternlogq $0xD2, %xmm15, %xmm11, %xmm9
	vpternlogq $0xD2, %xmm24, %xmm15, %xmm11
	vpternlogq $0xD2, %xmm0, %xmm24, %xmm15
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $62, %xmm12, %xmm12
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $55, %xmm16, %xmm16
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $39, %xmm20, %xmm20
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $41, %xmm1, %xmm1
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $2, %xmm5, %xmm5
	vpandnq %xmm20, %xmm16, %xmm24
	vpxorq %xmm12, %xmm24, %xmm24
	vpandnq %xmm1, %xmm20, %xmm0
	vpxorq %xmm16, %xmm0, %xmm0
	vpternlogq $0xD2, %xmm5, %xmm1, %xmm20
	vpternlogq $0xD2, %xmm12, %xmm5, %xmm1
	vpternlogq $0xD2, %xmm16, %xmm12, %xmm5
	vpxorq 16(%rax), %xmm2, %xmm2
	vpxorq %xmm30, %xmm2, %xmm25
	vpxorq %xmm18, %xmm25, %xmm25
	vpternlogq $0x96, %xmm24, %xmm31, %xmm25
	vpxorq %xmm6, %xmm8, %xmm26
	vpxorq %xmm22, %xmm26, %xmm26
	vpternlogq $0x96, %xmm0, %xmm10, %xmm26
	vpxorq %xmm3, %xmm13, %xmm27
	vpxorq %xmm19, %xmm27, %xmm27
	vpternlogq $0x96, %xmm20, %xmm9, %xmm27
	vpxorq %xmm7, %xmm17, %xmm28
	vpxorq %xmm23, %xmm28, %xmm28
	vpternlogq $0x96, %xmm1, %xmm11, %xmm28
	vpxorq %xmm14, %xmm21, %xmm29
	vpxorq %xmm4, %xmm29, %xmm29
	vpternlogq $0x96, %xmm5, %xmm15, %xmm29
	vprolq $1, %xmm25, %xmm16
	vprolq $1, %xmm27, %xmm12
	vpxorq %xmm12, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm12
	vpxorq %xmm16, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm16
	vpxorq %xmm12, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm12
	vpxorq %xmm16, %xmm29, %xmm29
	vpxorq %xmm12, %xmm27, %xmm27
	vpxorq %xmm29, %xmm2, %xmm2
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $43, %xmm19, %xmm19
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $21, %xmm11, %xmm11
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $14, %xmm5, %xmm5
	vpandnq %xmm19, %xmm6, %xmm12
	vpxorq %xmm2, %xmm12, %xmm12
	vpandnq %xmm11, %xmm19, %xmm16
	vpxorq %xmm6, %xmm16, %xmm16
	vpternlogq $0xD2, %xmm5, %xmm11, %xmm19
	vpternlogq $0xD2, %xmm2, %xmm5, %xmm11
	vpternlogq $0xD2, %xmm6, %xmm2, %xmm5
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $28, %xmm17, %xmm17
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $20, %xmm14, %xmm14
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $3, %xmm18, %xmm18
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $45, %xmm10, %xmm10
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $61, %xmm20, %xmm20
	vpandnq %xmm18, %xmm14, %xmm2
	vpxorq %xmm17, %xmm2, %xmm2
	vpandnq %xmm10, %xmm18, %xmm6
	vpxorq %xmm14, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm20, %xmm10, %xmm18
	vpternlogq $0xD2, %xmm17, %xmm20, %xmm10
	vpternlogq $0xD2, %xmm14, %xmm17, %xmm20
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $1, %xmm8, %xmm8
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $6, %xmm3, %xmm3
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $25, %xmm23, %xmm23
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $8, %xmm15, %xmm15
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $18, %xmm24, %xmm24
	vpandnq %xmm23, %xmm3, %xmm17
	vpxorq %xmm8, %xmm17, %xmm17
	vpandnq %xmm15, %xmm23, %xmm14
	vpxorq %xmm3, %xmm14, %xmm14
	vpternlogq $0xD2, %xmm24, %xmm15, %xmm23
	vpternlogq $0xD2, %xmm8, %xmm24, %xmm15
	vpternlogq $0xD2, %xmm3, %xmm8, %xmm24
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $27, %xmm21, %xmm21
	vpxorq %xmm29, %xmm30, %xmm30
	vprolq $36, %xmm30, %xmm30
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $10, %xmm22, %xmm22
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $15, %xmm9, %xmm9
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $56, %xmm1, %xmm1
	vpandnq %xmm22, %xmm30, %xmm8
	vpxorq %xmm21, %xmm8, %xmm8
	vpandnq %xmm9, %xmm22, %xmm3
	vpxorq %xmm30, %xmm3, %xmm3
	vpternlogq $0xD2, %xmm1, %xmm9, %xmm22
	vpternlogq $0xD2, %xmm21, %xmm1, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm1
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $62, %xmm13, %xmm13
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $55, %xmm7, %xmm7
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $39, %xmm4, %xmm4
	vpxorq %xmm29, %xmm31, %xmm31
	vprolq $41, %xmm31, %xmm31
	vpxorq %xmm25, %xmm0, %xmm0
	vprolq $2, %xmm0, %xmm0
	vpandnq %xmm4, %xmm7, %xmm21
	vpxorq %xmm13, %xmm21, %xmm21
	vpandnq %xmm31, %xmm4, %xmm30
	vpxorq %xmm7, %xmm30, %xmm30
	vpternlogq $0xD2, %xmm0, %xmm31, %xmm4
	vpternlogq $0xD2, %xmm13, %xmm0, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm13, %xmm0
	vpxorq 32(%rax), %xmm12, %xmm12
	vpxorq %xmm2, %xmm12, %xmm25
	vpxorq %xmm17, %xmm25, %xmm25
	vpternlogq $0x96, %xmm21, %xmm8, %xmm25
	vpxorq %xmm6, %xmm16, %xmm26
	vpxorq %xmm14, %xmm26, %xmm26
	vpternlogq $0x96, %xmm30, %xmm3, %xmm26
	vpxorq %xmm18, %xmm19, %xmm27
	vpxorq %xmm23, %xmm27, %xmm27
	vpternlogq $0x96, %xmm4, %xmm22, %xmm27
	vpxorq %xmm10, %xmm11, %xmm28
	vpxorq %xmm15, %xmm28, %xmm28
	vpternlogq $0x96, %xmm31, %xmm9, %xmm28
	vpxorq %xmm20, %xmm5, %xmm29
	vpxorq %xmm24, %xmm29, %xmm29
	vpternlogq $0x96, %xmm0, %xmm1, %xmm29
	vprolq $1, %xmm25, %xmm7
	vprolq $1, %xmm27, %xmm13
	vpxorq %xmm13, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm13
	vpxorq %xmm7, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm7
	vpxorq %xmm13, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm13
	vpxorq %xmm7, %xmm29, %xmm29
	vpxorq %xmm13, %xmm27, %xmm27
	vpxorq %xmm29, %xmm12, %xmm12
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $43, %xmm23, %xmm23
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $21, %xmm9, %xmm9
	vpxorq %xmm28, %xmm0, %xmm0
	vprolq $14, %xmm0, %xmm0
	vpandnq %xmm23, %xmm6, %xmm13
	vpxorq %xmm12, %xmm13, %xmm13
	vpandnq %xmm9, %xmm23, %xmm7
	vpxorq %xmm6, %xmm7, %xmm7
	vpternlogq $0xD2, %xmm0, %xmm9, %xmm23
	vpternlogq $0xD2, %xmm12, %xmm0, %xmm9
	vpternlogq $0xD2, %xmm6, %xmm12, %xmm0
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $28, %xmm11, %xmm11
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $20, %xmm20, %xmm20
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $3, %xmm17, %xmm17
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $45, %xmm3, %xmm3
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $61, %xmm4, %xmm4
	vpandnq %xmm17, %xmm20, %xmm12
	vpxorq %xmm11, %xmm12, %xmm12
	vpandnq %xmm3, %xmm17, %xmm6
	vpxorq %xmm20, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm4, %xmm3, %xmm17
	vpternlogq $0xD2, %xmm11, %xmm4, %xmm3
	vpternlogq $0xD2, %xmm20, %xmm11, %xmm4
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $1, %xmm16, %xmm16
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $6, %xmm18, %xmm18
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $25, %xmm15, %xmm15
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $8, %xmm1, %xmm1
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $18, %xmm21, %xmm21
	vpandnq %xmm15, %xmm18, %xmm11
	vpxorq %xmm16, %xmm11, %xmm11
	vpandnq %xmm1, %xmm15, %xmm20
	vpxorq %xmm18, %xmm20, %xmm20
	vpternlogq $0xD2, %xmm21, %xmm1, %xmm15
	vpternlogq $0xD2, %xmm16, %xmm21, %xmm1
	vpternlogq $0xD2, %xmm18, %xmm16, %xmm21
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $27, %xmm5, %xmm5
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $36, %xmm2, %xmm2
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $10, %xmm14, %xmm14
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $15, %xmm22, %xmm22
	vpxorq %xmm27, %xmm31, %xmm31
	vprolq $56, %xmm31, %xmm31
	vpandnq %xmm14, %xmm2, %xmm16
	vpxorq %xmm5, %xmm16, %xmm16
	vpandnq %xmm22, %xmm14, %xmm18
	vpxorq %xmm2, %xmm18, %xmm18
	vpternlogq $0xD2, %xmm31, %xmm22, %xmm14
	vpternlogq $0xD2, %xmm5, %xmm31, %xmm22
	vpternlogq $0xD2, %xmm2, %xmm5, %xmm31
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $62, %xmm19, %xmm19
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $55, %xmm10, %xmm10
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $39, %xmm24, %xmm24
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $41, %xmm8, %xmm8
	vpxorq %xmm25, %xmm30, %xmm30
	vprolq $2, %xmm30, %xmm30
	vpandnq %xmm24, %xmm10, %xmm5
	vpxorq %xmm19, %xmm5, %xmm5
	vpandnq %xmm8, %xmm24, %xmm2
	vpxorq %xmm10, %xmm2, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm24
	vpternlogq $0xD2, %xmm19, %xmm30, %xmm8
	vpternlogq $0xD2, %xmm10, %xmm19, %xmm30
	vpxorq 48(%rax), %xmm13, %xmm13
	vpxorq %xmm12, %xmm13, %xmm25
	vpxorq %xmm11, %xmm25, %xmm25
	vpternlogq $0x96, %xmm5, %xmm16, %xmm25
	vpxorq %xmm6, %xmm7, %xmm26
	vpxorq %xmm20, %xmm26, %xmm26
	vpternlogq $0x96, %xmm2, %xmm18, %xmm26
	vpxorq %xmm17, %xmm23, %xmm27
	vpxorq %xmm15, %xmm27, %xmm27
	vpternlogq $0x96, %xmm24, %xmm14, %xmm27
	vpxorq %xmm3, %xmm9, %xmm28
	vpxorq %xmm1, %xmm28, %xmm28
	vpternlogq $0x96, %xmm8, %xmm22, %xmm28
	vpxorq %xmm4, %xmm0, %xmm29
	vpxorq %xmm21, %xmm29, %xmm29
	vpternlogq $0x96, %xmm30, %xmm31, %xmm29
	vprolq $1, %xmm25, %xmm10
	vprolq $1, %xmm27, %xmm19
	vpxorq %xmm19, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm19
	vpxorq %xmm10, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm10
	vpxorq %xmm19, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm19
	vpxorq %xmm10, %xmm29, %xmm29
	vpxorq %xmm19, %xmm27, %xmm27
	vpxorq %xmm29, %xmm13, %xmm13
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $43, %xmm15, %xmm15
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $21, %xmm22, %xmm22
	vpxorq %xmm28, %xmm30, %xmm30
	vprolq $14, %xmm30, %xmm30
	vpandnq %xmm15, %xmm6, %xmm19
	vpxorq %xmm13, %xmm19, %xmm19
	vpandnq %xmm22, %xmm15, %xmm10
	vpxorq %xmm6, %xmm10, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm15
	vpternlogq $0xD2, %xmm13, %xmm30, %xmm22
	vpternlogq $0xD2, %xmm6, %xmm13, %xmm30
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $28, %xmm9, %xmm9
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $20, %xmm4, %xmm4
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $3, %xmm11, %xmm11
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $45, %xmm18, %xmm18
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $61, %xmm24, %xmm24
	vpandnq %xmm11, %xmm4, %xmm13
	vpxorq %xmm9, %xmm13, %xmm13
	vpandnq %xmm18, %xmm11, %xmm6
	vpxorq %xmm4, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm24, %xmm18, %xmm11
	vpternlogq $0xD2, %xmm9, %xmm24, %xmm18
	vpternlogq $0xD2, %xmm4, %xmm9, %xmm24
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $1, %xmm7, %xmm7
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $6, %xmm17, %xmm17
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $25, %xmm1, %xmm1
	vpxorq %xmm28, %xmm31, %xmm31
	vprolq $8, %xmm31, %xmm31
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $18, %xmm5, %xmm5
	vpandnq %xmm1, %xmm17, %xmm9
	vpxorq %xmm7, %xmm9, %xmm9
	vpandnq %xmm31, %xmm1, %xmm4
	vpxorq %xmm17, %xmm4, %xmm4
	vpternlogq $0xD2, %xmm5, %xmm31, %xmm1
	vpternlogq $0xD2, %xmm7, %xmm5, %xmm31
	vpternlogq $0xD2, %xmm17, %xmm7, %xmm5
	vpxorq %xmm28, %xmm0, %xmm0
	vprolq $27, %xmm0, %xmm0
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $36, %xmm12, %xmm12
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $10, %xmm20, %xmm20
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $15, %xmm14, %xmm14
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $56, %xmm8, %xmm8
	vpandnq %xmm20, %xmm12, %xmm7
	vpxorq %xmm0, %xmm7, %xmm7
	vpandnq %xmm14, %xmm20, %xmm17
	vpxorq %xmm12, %xmm17, %xmm17
	vpternlogq $0xD2, %xmm8, %xmm14, %xmm20
	vpternlogq $0xD2, %xmm0, %xmm8, %xmm14
	vpternlogq $0xD2, %xmm12, %xmm0, %xmm8
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $62, %xmm23, %xmm23
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $55, %xmm3, %xmm3
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $39, %xmm21, %xmm21
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $41, %xmm16, %xmm16
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $2, %xmm2, %xmm2
	vpandnq %xmm21, %xmm3, %xmm0
	vpxorq %xmm23, %xmm0, %xmm0
	vpandnq %xmm16, %xmm21, %xmm12
	vpxorq %xmm3, %xmm12, %xmm12
	vpternlogq $0xD2, %xmm2, %xmm16, %xmm21
	vpternlogq $0xD2, %xmm23, %xmm2, %xmm16
	vpternlogq $0xD2, %xmm3, %xmm23, %xmm2
	vpxorq 64(%rax), %xmm19, %xmm19
	vpxorq %xmm13, %xmm19, %xmm25
	vpxorq %xmm9, %xmm25, %xmm25
	vpternlogq $0x96, %xmm0, %xmm7, %xmm25
	vpxorq %xmm6, %xmm10, %xmm26
	vpxorq %xmm4, %xmm26, %xmm26
	vpternlogq $0x96, %xmm12, %xmm17, %xmm26
	vpxorq %xmm11, %xmm15, %xmm27
	vpxorq %xmm1, %xmm27, %xmm27
	vpternlogq $0x96, %xmm21, %xmm20, %xmm27
	vpxorq %xmm18, %xmm22, %xmm28
	vpxorq %xmm31, %xmm28, %xmm28
	vpternlogq $0x96, %xmm16, %xmm14, %xmm28
	vpxorq %xmm24, %xmm30, %xmm29
	vpxorq %xmm5, %xmm29, %xmm29
	vpternlogq $0x96, %xmm2, %xmm8, %xmm29
	vprolq $1, %xmm25, %xmm3
	vprolq $1, %xmm27, %xmm23
	vpxorq %xmm23, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm23
	vpxorq %xmm3, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm3
	vpxorq %xmm23, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm23
	vpxorq %xmm3, %xmm29, %xmm29
	vpxorq %xmm23, %xmm27, %xmm27
	vpxorq %xmm29, %xmm19, %xmm19
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $43, %xmm1, %xmm1
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $21, %xmm14, %xmm14
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $14, %xmm2, %xmm2
	vpandnq %xmm1, %xmm6, %xmm23
	vpxorq %xmm19, %xmm23, %xmm23
	vpandnq %xmm14, %xmm1, %xmm3
	vpxorq %xmm6, %xmm3, %xmm3
	vpternlogq $0xD2, %xmm2, %xmm14, %xmm1
	vpternlogq $0xD2, %xmm19, %xmm2, %xmm14
	vpternlogq $0xD2, %xmm6, %xmm19, %xmm2
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $28, %xmm22, %xmm22
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $20, %xmm24, %xmm24
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $3, %xmm9, %xmm9
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $45, %xmm17, %xmm17
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $61, %xmm21, %xmm21
	vpandnq %xmm9, %xmm24, %xmm19
	vpxorq %xmm22, %xmm19, %xmm19
	vpandnq %xmm17, %xmm9, %xmm6
	vpxorq %xmm24, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm21, %xmm17, %xmm9
	vpternlogq $0xD2, %xmm22, %xmm21, %xmm17
	vpternlogq $0xD2, %xmm24, %xmm22, %xmm21
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $1, %xmm10, %xmm10
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $6, %xmm11, %xmm11
	vpxorq %xmm27, %xmm31, %xmm31
	vprolq $25, %xmm31, %xmm31
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $8, %xmm8, %xmm8
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $18, %xmm0, %xmm0
	vpandnq %xmm31, %xmm11, %xmm22
	vpxorq %xmm10, %xmm22, %xmm22
	vpandnq %xmm8, %xmm31, %xmm24
	vpxorq %xmm11, %xmm24, %xmm24
	vpternlogq $0xD2, %xmm0, %xmm8, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm0, %xmm8
	vpternlogq $0xD2, %xmm11, %xmm10, %xmm0
	vpxorq %xmm28, %xmm30, %xmm30
	vprolq $27, %xmm30, %xmm30
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $36, %xmm13, %xmm13
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $10, %xmm4, %xmm4
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $15, %xmm20, %xmm20
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $56, %xmm16, %xmm16
	vpandnq %xmm4, %xmm13, %xmm10
	vpxorq %xmm30, %xmm10, %xmm10
	vpandnq %xmm20, %xmm4, %xmm11
	vpxorq %xmm13, %xmm11, %xmm11
	vpternlogq $0xD2, %xmm16, %xmm20, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm20
	vpternlogq $0xD2, %xmm13, %xmm30, %xmm16
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $62, %xmm15, %xmm15
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $55, %xmm18, %xmm18
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $39, %xmm5, %xmm5
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $41, %xmm7, %xmm7
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $2, %xmm12, %xmm12
	vpandnq %xmm5, %xmm18, %xmm30
	vpxorq %xmm15, %xmm30, %xmm30
	vpandnq %xmm7, %xmm5, %xmm13
	vpxorq %xmm18, %xmm13, %xmm13
	vpternlogq $0xD2, %xmm12, %xmm7, %xmm5
	vpternlogq $0xD2, %xmm15, %xmm12, %xmm7
	vpternlogq $0xD2, %xmm18, %xmm15, %xmm12
	vpxorq 80(%rax), %xmm23, %xmm23
	vpxorq %xmm19, %xmm23, %xmm25
	vpxorq %xmm22, %xmm25, %xmm25
	vpternlogq $0x96, %xmm30, %xmm10, %xmm25
	vpxorq %xmm6, %xmm3, %xmm26
	vpxorq %xmm24, %xmm26, %xmm26
	vpternlogq $0x96, %xmm13, %xmm11, %xmm26
	vpxorq %xmm9, %xmm1, %xmm27
	vpxorq %xmm31, %xmm27, %xmm27
	vpternlogq $0x96, %xmm5, %xmm4, %xmm27
	vpxorq %xmm17, %xmm14, %xmm28
	vpxorq %xmm8, %xmm28, %xmm28
	vpternlogq $0x96, %xmm7, %xmm20, %xmm28
	vpxorq %xmm21, %xmm2, %xmm29
	vpxorq %xmm0, %xmm29, %xmm29
	vpternlogq $0x96, %xmm12, %xmm16, %xmm29
	vprolq $1, %xmm25, %xmm18
	vprolq $1, %xmm27, %xmm15
	vpxorq %xmm15, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm15
	vpxorq %xmm18, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm18
	vpxorq %xmm15, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm15
	vpxorq %xmm18, %xmm29, %xmm29
	vpxorq %xmm15, %xmm27, %xmm27
	vpxorq %xmm29, %xmm23, %xmm23
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm31, %xmm31
	vprolq $43, %xmm31, %xmm31
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $21, %xmm20, %xmm20
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $14, %xmm12, %xmm12
	vpandnq %xmm31, %xmm6, %xmm15
	vpxorq %xmm23, %xmm15, %xmm15
	vpandnq %xmm20, %xmm31, %xmm18
	vpxorq %xmm6, %xmm18, %xmm18
	vpternlogq $0xD2, %xmm12, %xmm20, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm12, %xmm20
	vpternlogq $0xD2, %xmm6, %xmm23, %xmm12
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $28, %xmm14, %xmm14
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $20, %xmm21, %xmm21
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $3, %xmm22, %xmm22
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $45, %xmm11, %xmm11
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $61, %xmm5, %xmm5
	vpandnq %xmm22, %xmm21, %xmm23
	vpxorq %xmm14, %xmm23, %xmm23
	vpandnq %xmm11, %xmm22, %xmm6
	vpxorq %xmm21, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm5, %xmm11, %xmm22
	vpternlogq $0xD2, %xmm14, %xmm5, %xmm11
	vpternlogq $0xD2, %xmm21, %xmm14, %xmm5
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $1, %xmm3, %xmm3
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $6, %xmm9, %xmm9
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $25, %xmm8, %xmm8
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $8, %xmm16, %xmm16
	vpxorq %xmm29, %xmm30, %xmm30
	vprolq $18, %xmm30, %xmm30
	vpandnq %xmm8, %xmm9, %xmm14
	vpxorq %xmm3, %xmm14, %xmm14
	vpandnq %xmm16, %xmm8, %xmm21
	vpxorq %xmm9, %xmm21, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm8
	vpternlogq $0xD2, %xmm3, %xmm30, %xmm16
	vpternlogq $0xD2, %xmm9, %xmm3, %xmm30
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $27, %xmm2, %xmm2
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $36, %xmm19, %xmm19
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $10, %xmm24, %xmm24
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $15, %xmm4, %xmm4
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $56, %xmm7, %xmm7
	vpandnq %xmm24, %xmm19, %xmm3
	vpxorq %xmm2, %xmm3, %xmm3
	vpandnq %xmm4, %xmm24, %xmm9
	vpxorq %xmm19, %xmm9, %xmm9
	vpternlogq $0xD2, %xmm7, %xmm4, %xmm24
	vpternlogq $0xD2, %xmm2, %xmm7, %xmm4
	vpternlogq $0xD2, %xmm19, %xmm2, %xmm7
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $62, %xmm1, %xmm1
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $55, %xmm17, %xmm17
	vpxorq %xmm28, %xmm0, %xmm0
	vprolq $39, %xmm0, %xmm0
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $41, %xmm10, %xmm10
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $2, %xmm13, %xmm13
	vpandnq %xmm0, %xmm17, %xmm2
	vpxorq %xmm1, %xmm2, %xmm2
	vpandnq %xmm10, %xmm0, %xmm19
	vpxorq %xmm17, %xmm19, %xmm19
	vpternlogq $0xD2, %xmm13, %xmm10, %xmm0
	vpternlogq $0xD2, %xmm1, %xmm13, %xmm10
	vpternlogq $0xD2, %xmm17, %xmm1, %xmm13
	vpxorq 96(%rax), %xmm15, %xmm15
	vpxorq %xmm23, %xmm15, %xmm25
	vpxorq %xmm14, %xmm25, %xmm25
	vpternlogq $0x96, %xmm2, %xmm3, %xmm25
	vpxorq %xmm6, %xmm18, %xmm26
	vpxorq %xmm21, %xmm26, %xmm26
	vpternlogq $0x96, %xmm19, %xmm9, %xmm26
	vpxorq %xmm22, %xmm31, %xmm27
	vpxorq %xmm8, %xmm27, %xmm27
	vpternlogq $0x96, %xmm0, %xmm24, %xmm27
	vpxorq %xmm11, %xmm20, %xmm28
	vpxorq %xmm16, %xmm28, %xmm28
	vpternlogq $0x96, %xmm10, %xmm4, %xmm28
	vpxorq %xmm5, %xmm12, %xmm29
	vpxorq %xmm30, %xmm29, %xmm29
	vpternlogq $0x96, %xmm13, %xmm7, %xmm29
	vprolq $1, %xmm25, %xmm17
	vprolq $1, %xmm27, %xmm1
	vpxorq %xmm1, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm1
	vpxorq %xmm17, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm17
	vpxorq %xmm1, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm1
	vpxorq %xmm17, %xmm29, %xmm29
	vpxorq %xmm1, %xmm27, %xmm27
	vpxorq %xmm29, %xmm15, %xmm15
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $43, %xmm8, %xmm8
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $21, %xmm4, %xmm4
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $14, %xmm13, %xmm13
	vpandnq %xmm8, %xmm6, %xmm1
	vpxorq %xmm15, %xmm1, %xmm1
	vpandnq %xmm4, %xmm8, %xmm17
	vpxorq %xmm6, %xmm17, %xmm17
	vpternlogq $0xD2, %xmm13, %xmm4, %xmm8
	vpternlogq $0xD2, %xmm15, %xmm13, %xmm4
	vpternlogq $0xD2, %xmm6, %xmm15, %xmm13
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $28, %xmm20, %xmm20
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $20, %xmm5, %xmm5
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $3, %xmm14, %xmm14
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $45, %xmm9, %xmm9
	vpxorq %xmm26, %xmm0, %xmm0
	vprolq $61, %xmm0, %xmm0
	vpandnq %xmm14, %xmm5, %xmm15
	vpxorq %xmm20, %xmm15, %xmm15
	vpandnq %xmm9, %xmm14, %xmm6
	vpxorq %xmm5, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm0, %xmm9, %xmm14
	vpternlogq $0xD2, %xmm20, %xmm0, %xmm9
	vpternlogq $0xD2, %xmm5, %xmm20, %xmm0
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $1, %xmm18, %xmm18
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $6, %xmm22, %xmm22
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $25, %xmm16, %xmm16
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $8, %xmm7, %xmm7
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $18, %xmm2, %xmm2
	vpandnq %xmm16, %xmm22, %xmm20
	vpxorq %xmm18, %xmm20, %xmm20
	vpandnq %xmm7, %xmm16, %xmm5
	vpxorq %xmm22, %xmm5, %xmm5
	vpternlogq $0xD2, %xmm2, %xmm7, %xmm16
	vpternlogq $0xD2, %xmm18, %xmm2, %xmm7
	vpternlogq $0xD2, %xmm22, %xmm18, %xmm2
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $27, %xmm12, %xmm12
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $36, %xmm23, %xmm23
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $10, %xmm21, %xmm21
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $15, %xmm24, %xmm24
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $56, %xmm10, %xmm10
	vpandnq %xmm21, %xmm23, %xmm18
	vpxorq %xmm12, %xmm18, %xmm18
	vpandnq %xmm24, %xmm21, %xmm22
	vpxorq %xmm23, %xmm22, %xmm22
	vpternlogq $0xD2, %xmm10, %xmm24, %xmm21
	vpternlogq $0xD2, %xmm12, %xmm10, %xmm24
	vpternlogq $0xD2, %xmm23, %xmm12, %xmm10
	vpxorq %xmm26, %xmm31, %xmm31
	vprolq $62, %xmm31, %xmm31
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $55, %xmm11, %xmm11
	vpxorq %xmm28, %xmm30, %xmm30
	vprolq $39, %xmm30, %xmm30
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $41, %xmm3, %xmm3
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $2, %xmm19, %xmm19
	vpandnq %xmm30, %xmm11, %xmm12
	vpxorq %xmm31, %xmm12, %xmm12
	vpandnq %xmm3, %xmm30, %xmm23
	vpxorq %xmm11, %xmm23, %xmm23
	vpternlogq $0xD2, %xmm19, %xmm3, %xmm30
	vpternlogq $0xD2, %xmm31, %xmm19, %xmm3
	vpternlogq $0xD2, %xmm11, %xmm31, %xmm19
	vpxorq 112(%rax), %xmm1, %xmm1
	vpxorq %xmm15, %xmm1, %xmm25
	vpxorq %xmm20, %xmm25, %xmm25
	vpternlogq $0x96, %xmm12, %xmm18, %xmm25
	vpxorq %xmm6, %xmm17, %xmm26
	vpxorq %xmm5, %xmm26, %xmm26
	vpternlogq $0x96, %xmm23, %xmm22, %xmm26
	vpxorq %xmm14, %xmm8, %xmm27
	vpxorq %xmm16, %xmm27, %xmm27
	vpternlogq $0x96, %xmm30, %xmm21, %xmm27
	vpxorq %xmm9, %xmm4, %xmm28
	vpxorq %xmm7, %xmm28, %xmm28
	vpternlogq $0x96, %xmm3, %xmm24, %xmm28
	vpxorq %xmm0, %xmm13, %xmm29
	vpxorq %xmm2, %xmm29, %xmm29
	vpternlogq $0x96, %xmm19, %xmm10, %xmm29
	vprolq $1, %xmm25, %xmm11
	vprolq $1, %xmm27, %xmm31
	vpxorq %xmm31, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm31
	vpxorq %xmm11, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm11
	vpxorq %xmm31, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm31
	vpxorq %xmm11, %xmm29, %xmm29
	vpxorq %xmm31, %xmm27, %xmm27
	vpxorq %xmm29, %xmm1, %xmm1
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $43, %xmm16, %xmm16
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $21, %xmm24, %xmm24
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $14, %xmm19, %xmm19
	vpandnq %xmm16, %xmm6, %xmm31
	vpxorq %xmm1, %xmm31, %xmm31
	vpandnq %xmm24, %xmm16, %xmm11
	vpxorq %xmm6, %xmm11, %xmm11
	vpternlogq $0xD2, %xmm19, %xmm24, %xmm16
	vpternlogq $0xD2, %xmm1, %xmm19, %xmm24
	vpternlogq $0xD2, %xmm6, %xmm1, %xmm19
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $28, %xmm4, %xmm4
	vpxorq %xmm28, %xmm0, %xmm0
	vprolq $20, %xmm0, %xmm0
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $3, %xmm20, %xmm20
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $45, %xmm22, %xmm22
	vpxorq %xmm26, %xmm30, %xmm30
	vprolq $61, %xmm30, %xmm30
	vpandnq %xmm20, %xmm0, %xmm1
	vpxorq %xmm4, %xmm1, %xmm1
	vpandnq %xmm22, %xmm20, %xmm6
	vpxorq %xmm0, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm20
	vpternlogq $0xD2, %xmm4, %xmm30, %xmm22
	vpternlogq $0xD2, %xmm0, %xmm4, %xmm30
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $1, %xmm17, %xmm17
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $6, %xmm14, %xmm14
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $25, %xmm7, %xmm7
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $8, %xmm10, %xmm10
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $18, %xmm12, %xmm12
	vpandnq %xmm7, %xmm14, %xmm4
	vpxorq %xmm17, %xmm4, %xmm4
	vpandnq %xmm10, %xmm7, %xmm0
	vpxorq %xmm14, %xmm0, %xmm0
	vpternlogq $0xD2, %xmm12, %xmm10, %xmm7
	vpternlogq $0xD2, %xmm17, %xmm12, %xmm10
	vpternlogq $0xD2, %xmm14, %xmm17, %xmm12
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $27, %xmm13, %xmm13
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $36, %xmm15, %xmm15
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $10, %xmm5, %xmm5
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $15, %xmm21, %xmm21
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $56, %xmm3, %xmm3
	vpandnq %xmm5, %xmm15, %xmm17
	vpxorq %xmm13, %xmm17, %xmm17
	vpandnq %xmm21, %xmm5, %xmm14
	vpxorq %xmm15, %xmm14, %xmm14
	vpternlogq $0xD2, %xmm3, %xmm21, %xmm5
	vpternlogq $0xD2, %xmm13, %xmm3, %xmm21
	vpternlogq $0xD2, %xmm15, %xmm13, %xmm3
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $62, %xmm8, %xmm8
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $55, %xmm9, %xmm9
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $39, %xmm2, %xmm2
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $41, %xmm18, %xmm18
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $2, %xmm23, %xmm23
	vpandnq %xmm2, %xmm9, %xmm13
	vpxorq %xmm8, %xmm13, %xmm13
	vpandnq %xmm18, %xmm2, %xmm15
	vpxorq %xmm9, %xmm15, %xmm15
	vpternlogq $0xD2, %xmm23, %xmm18, %xmm2
	vpternlogq $0xD2, %xmm8, %xmm23, %xmm18
	vpternlogq $0xD2, %xmm9, %xmm8, %xmm23
	vpxorq 128(%rax), %xmm31, %xmm31
	vpxorq %xmm1, %xmm31, %xmm25
	vpxorq %xmm4, %xmm25, %xmm25
	vpternlogq $0x96, %xmm13, %xmm17, %xmm25
	vpxorq %xmm6, %xmm11, %xmm26
	vpxorq %xmm0, %xmm26, %xmm26
	vpternlogq $0x96, %xmm15, %xmm14, %xmm26
	vpxorq %xmm20, %xmm16, %xmm27
	vpxorq %xmm7, %xmm27, %xmm27
	vpternlogq $0x96, %xmm2, %xmm5, %xmm27
	vpxorq %xmm22, %xmm24, %xmm28
	vpxorq %xmm10, %xmm28, %xmm28
	vpternlogq $0x96, %xmm18, %xmm21, %xmm28
	vpxorq %xmm30, %xmm19, %xmm29
	vpxorq %xmm12, %xmm29, %xmm29
	vpternlogq $0x96, %xmm23, %xmm3, %xmm29
	vprolq $1, %xmm25, %xmm9
	vprolq $1, %xmm27, %xmm8
	vpxorq %xmm8, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm8
	vpxorq %xmm9, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm9
	vpxorq %xmm8, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm8
	vpxorq %xmm9, %xmm29, %xmm29
	vpxorq %xmm8, %xmm27, %xmm27
	vpxorq %xmm29, %xmm31, %xmm31
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $43, %xmm7, %xmm7
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $21, %xmm21, %xmm21
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $14, %xmm23, %xmm23
	vpandnq %xmm7, %xmm6, %xmm8
	vpxorq %xmm31, %xmm8, %xmm8
	vpandnq %xmm21, %xmm7, %xmm9
	vpxorq %xmm6, %xmm9, %xmm9
	vpternlogq $0xD2, %xmm23, %xmm21, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm23, %xmm21
	vpternlogq $0xD2, %xmm6, %xmm31, %xmm23
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $28, %xmm24, %xmm24
	vpxorq %xmm28, %xmm30, %xmm30
	vprolq $20, %xmm30, %xmm30
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $3, %xmm4, %xmm4
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $45, %xmm14, %xmm14
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $61, %xmm2, %xmm2
	vpandnq %xmm4, %xmm30, %xmm31
	vpxorq %xmm24, %xmm31, %xmm31
	vpandnq %xmm14, %xmm4, %xmm6
	vpxorq %xmm30, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm2, %xmm14, %xmm4
	vpternlogq $0xD2, %xmm24, %xmm2, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm2
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $1, %xmm11, %xmm11
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $6, %xmm20, %xmm20
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $25, %xmm10, %xmm10
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $8, %xmm3, %xmm3
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $18, %xmm13, %xmm13
	vpandnq %xmm10, %xmm20, %xmm24
	vpxorq %xmm11, %xmm24, %xmm24
	vpandnq %xmm3, %xmm10, %xmm30
	vpxorq %xmm20, %xmm30, %xmm30
	vpternlogq $0xD2, %xmm13, %xmm3, %xmm10
	vpternlogq $0xD2, %xmm11, %xmm13, %xmm3
	vpternlogq $0xD2, %xmm20, %xmm11, %xmm13
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $27, %xmm19, %xmm19
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $36, %xmm1, %xmm1
	vpxorq %xmm25, %xmm0, %xmm0
	vprolq $10, %xmm0, %xmm0
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $15, %xmm5, %xmm5
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $56, %xmm18, %xmm18
	vpandnq %xmm0, %xmm1, %xmm11
	vpxorq %xmm19, %xmm11, %xmm11
	vpandnq %xmm5, %xmm0, %xmm20
	vpxorq %xmm1, %xmm20, %xmm20
	vpternlogq $0xD2, %xmm18, %xmm5, %xmm0
	vpternlogq $0xD2, %xmm19, %xmm18, %xmm5
	vpternlogq $0xD2, %xmm1, %xmm19, %xmm18
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $62, %xmm16, %xmm16
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $55, %xmm22, %xmm22
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $39, %xmm12, %xmm12
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $41, %xmm17, %xmm17
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $2, %xmm15, %xmm15
	vpandnq %xmm12, %xmm22, %xmm19
	vpxorq %xmm16, %xmm19, %xmm19
	vpandnq %xmm17, %xmm12, %xmm1
	vpxorq %xmm22, %xmm1, %xmm1
	vpternlogq $0xD2, %xmm15, %xmm17, %xmm12
	vpternlogq $0xD2, %xmm16, %xmm15, %xmm17
	vpternlogq $0xD2, %xmm22, %xmm16, %xmm15
	vpxorq 144(%rax), %xmm8, %xmm8
	vpxorq %xmm31, %xmm8, %xmm25
	vpxorq %xmm24, %xmm25, %xmm25
	vpternlogq $0x96, %xmm19, %xmm11, %xmm25
	vpxorq %xmm6, %xmm9, %xmm26
	vpxorq %xmm30, %xmm26, %xmm26
	vpternlogq $0x96, %xmm1, %xmm20, %xmm26
	vpxorq %xmm4, %xmm7, %xmm27
	vpxorq %xmm10, %xmm27, %xmm27
	vpternlogq $0x96, %xmm12, %xmm0, %xmm27
	vpxorq %xmm14, %xmm21, %xmm28
	vpxorq %xmm3, %xmm28, %xmm28
	vpternlogq $0x96, %xmm17, %xmm5, %xmm28
	vpxorq %xmm2, %xmm23, %xmm29
	vpxorq %xmm13, %xmm29, %xmm29
	vpternlogq $0x96, %xmm15, %xmm18, %xmm29
	vprolq $1, %xmm25, %xmm22
	vprolq $1, %xmm27, %xmm16
	vpxorq %xmm16, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm16
	vpxorq %xmm22, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm22
	vpxorq %xmm16, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm16
	vpxorq %xmm22, %xmm29, %xmm29
	vpxorq %xmm16, %xmm27, %xmm27
	vpxorq %xmm29, %xmm8, %xmm8
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $43, %xmm10, %xmm10
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $21, %xmm5, %xmm5
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $14, %xmm15, %xmm15
	vpandnq %xmm10, %xmm6, %xmm16
	vpxorq %xmm8, %xmm16, %xmm16
	vpandnq %xmm5, %xmm10, %xmm22
	vpxorq %xmm6, %xmm22, %xmm22
	vpternlogq $0xD2, %xmm15, %xmm5, %xmm10
	vpternlogq $0xD2, %xmm8, %xmm15, %xmm5
	vpternlogq $0xD2, %xmm6, %xmm8, %xmm15
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $28, %xmm21, %xmm21
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $20, %xmm2, %xmm2
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $3, %xmm24, %xmm24
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $45, %xmm20, %xmm20
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $61, %xmm12, %xmm12
	vpandnq %xmm24, %xmm2, %xmm8
	vpxorq %xmm21, %xmm8, %xmm8
	vpandnq %xmm20, %xmm24, %xmm6
	vpxorq %xmm2, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm12, %xmm20, %xmm24
	vpternlogq $0xD2, %xmm21, %xmm12, %xmm20
	vpternlogq $0xD2, %xmm2, %xmm21, %xmm12
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $1, %xmm9, %xmm9
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $6, %xmm4, %xmm4
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $25, %xmm3, %xmm3
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $8, %xmm18, %xmm18
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $18, %xmm19, %xmm19
	vpandnq %xmm3, %xmm4, %xmm21
	vpxorq %xmm9, %xmm21, %xmm21
	vpandnq %xmm18, %xmm3, %xmm2
	vpxorq %xmm4, %xmm2, %xmm2
	vpternlogq $0xD2, %xmm19, %xmm18, %xmm3
	vpternlogq $0xD2, %xmm9, %xmm19, %xmm18
	vpternlogq $0xD2, %xmm4, %xmm9, %xmm19
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $27, %xmm23, %xmm23
	vpxorq %xmm29, %xmm31, %xmm31
	vprolq $36, %xmm31, %xmm31
	vpxorq %xmm25, %xmm30, %xmm30
	vprolq $10, %xmm30, %xmm30
	vpxorq %xmm26, %xmm0, %xmm0
	vprolq $15, %xmm0, %xmm0
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $56, %xmm17, %xmm17
	vpandnq %xmm30, %xmm31, %xmm9
	vpxorq %xmm23, %xmm9, %xmm9
	vpandnq %xmm0, %xmm30, %xmm4
	vpxorq %xmm31, %xmm4, %xmm4
	vpternlogq $0xD2, %xmm17, %xmm0, %xmm30
	vpternlogq $0xD2, %xmm23, %xmm17, %xmm0
	vpternlogq $0xD2, %xmm31, %xmm23, %xmm17
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $62, %xmm7, %xmm7
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $55, %xmm14, %xmm14
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $39, %xmm13, %xmm13
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $41, %xmm11, %xmm11
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $2, %xmm1, %xmm1
	vpandnq %xmm13, %xmm14, %xmm23
	vpxorq %xmm7, %xmm23, %xmm23
	vpandnq %xmm11, %xmm13, %xmm31
	vpxorq %xmm14, %xmm31, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm11, %xmm13
	vpternlogq $0xD2, %xmm7, %xmm1, %xmm11
	vpternlogq $0xD2, %xmm14, %xmm7, %xmm1
	vpxorq 160(%rax), %xmm16, %xmm16
	vpxorq %xmm8, %xmm16, %xmm25
	vpxorq %xmm21, %xmm25, %xmm25
	vpternlogq $0x96, %xmm23, %xmm9, %xmm25
	vpxorq %xmm6, %xmm22, %xmm26
	vpxorq %xmm2, %xmm26, %xmm26
	vpternlogq $0x96, %xmm31, %xmm4, %xmm26
	vpxorq %xmm24, %xmm10, %xmm27
	vpxorq %xmm3, %xmm27, %xmm27
	vpternlogq $0x96, %xmm13, %xmm30, %xmm27
	vpxorq %xmm20, %xmm5, %xmm28
	vpxorq %xmm18, %xmm28, %xmm28
	vpternlogq $0x96, %xmm11, %xmm0, %xmm28
	vpxorq %xmm12, %xmm15, %xmm29
	vpxorq %xmm19, %xmm29, %xmm29
	vpternlogq $0x96, %xmm1, %xmm17, %xmm29
	vprolq $1, %xmm25, %xmm14
	vprolq $1, %xmm27, %xmm7
	vpxorq %xmm7, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm7
	vpxorq %xmm14, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm14
	vpxorq %xmm7, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm7
	vpxorq %xmm14, %xmm29, %xmm29
	vpxorq %xmm7, %xmm27, %xmm27
	vpxorq %xmm29, %xmm16, %xmm16
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $43, %xmm3, %xmm3
	vpxorq %xmm27, %xmm0, %xmm0
	vprolq $21, %xmm0, %xmm0
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $14, %xmm1, %xmm1
	vpandnq %xmm3, %xmm6, %xmm7
	vpxorq %xmm16, %xmm7, %xmm7
	vpandnq %xmm0, %xmm3, %xmm14
	vpxorq %xmm6, %xmm14, %xmm14
	vpternlogq $0xD2, %xmm1, %xmm0, %xmm3
	vpternlogq $0xD2, %xmm16, %xmm1, %xmm0
	vpternlogq $0xD2, %xmm6, %xmm16, %xmm1
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $28, %xmm5, %xmm5
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $20, %xmm12, %xmm12
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $3, %xmm21, %xmm21
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $45, %xmm4, %xmm4
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $61, %xmm13, %xmm13
	vpandnq %xmm21, %xmm12, %xmm16
	vpxorq %xmm5, %xmm16, %xmm16
	vpandnq %xmm4, %xmm21, %xmm6
	vpxorq %xmm12, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm13, %xmm4, %xmm21
	vpternlogq $0xD2, %xmm5, %xmm13, %xmm4
	vpternlogq $0xD2, %xmm12, %xmm5, %xmm13
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $1, %xmm22, %xmm22
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $6, %xmm24, %xmm24
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $25, %xmm18, %xmm18
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $8, %xmm17, %xmm17
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $18, %xmm23, %xmm23
	vpandnq %xmm18, %xmm24, %xmm5
	vpxorq %xmm22, %xmm5, %xmm5
	vpandnq %xmm17, %xmm18, %xmm12
	vpxorq %xmm24, %xmm12, %xmm12
	vpternlogq $0xD2, %xmm23, %xmm17, %xmm18
	vpternlogq $0xD2, %xmm22, %xmm23, %xmm17
	vpternlogq $0xD2, %xmm24, %xmm22, %xmm23
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $27, %xmm15, %xmm15
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $36, %xmm8, %xmm8
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $10, %xmm2, %xmm2
	vpxorq %xmm26, %xmm30, %xmm30
	vprolq $15, %xmm30, %xmm30
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $56, %xmm11, %xmm11
	vpandnq %xmm2, %xmm8, %xmm22
	vpxorq %xmm15, %xmm22, %xmm22
	vpandnq %xmm30, %xmm2, %xmm24
	vpxorq %xmm8, %xmm24, %xmm24
	vpternlogq $0xD2, %xmm11, %xmm30, %xmm2
	vpternlogq $0xD2, %xmm15, %xmm11, %xmm30
	vpternlogq $0xD2, %xmm8, %xmm15, %xmm11
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $62, %xmm10, %xmm10
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $55, %xmm20, %xmm20
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $39, %xmm19, %xmm19
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $41, %xmm9, %xmm9
	vpxorq %xmm25, %xmm31, %xmm31
	vprolq $2, %xmm31, %xmm31
	vpandnq %xmm19, %xmm20, %xmm15
	vpxorq %xmm10, %xmm15, %xmm15
	vpandnq %xmm9, %xmm19, %xmm8
	vpxorq %xmm20, %xmm8, %xmm8
	vpternlogq $0xD2, %xmm31, %xmm9, %xmm19
	vpternlogq $0xD2, %xmm10, %xmm31, %xmm9
	vpternlogq $0xD2, %xmm20, %xmm10, %xmm31
	vpxorq 176(%rax), %xmm7, %xmm7
	vpxorq %xmm16, %xmm7, %xmm25
	vpxorq %xmm5, %xmm25, %xmm25
	vpternlogq $0x96, %xmm15, %xmm22, %xmm25
	vpxorq %xmm6, %xmm14, %xmm26
	vpxorq %xmm12, %xmm26, %xmm26
	vpternlogq $0x96, %xmm8, %xmm24, %xmm26
	vpxorq %xmm21, %xmm3, %xmm27
	vpxorq %xmm18, %xmm27, %xmm27
	vpternlogq $0x96, %xmm19, %xmm2, %xmm27
	vpxorq %xmm4, %xmm0, %xmm28
	vpxorq %xmm17, %xmm28, %xmm28
	vpternlogq $0x96, %xmm9, %xmm30, %xmm28
	vpxorq %xmm13, %xmm1, %xmm29
	vpxorq %xmm23, %xmm29, %xmm29
	vpternlogq $0x96, %xmm31, %xmm11, %xmm29
	vprolq $1, %xmm25, %xmm20
	vprolq $1, %xmm27, %xmm10
	vpxorq %xmm10, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm10
	vpxorq %xmm20, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm20
	vpxorq %xmm10, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm10
	vpxorq %xmm20, %xmm29, %xmm29
	vpxorq %xmm10, %xmm27, %xmm27
	vpxorq %xmm29, %xmm7, %xmm7
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $43, %xmm18, %xmm18
	vpxorq %xmm27, %xmm30, %xmm30
	vprolq $21, %xmm30, %xmm30
	vpxorq %xmm28, %xmm31, %xmm31
	vprolq $14, %xmm31, %xmm31
	vpandnq %xmm18, %xmm6, %xmm10
	vpxorq %xmm7, %xmm10, %xmm10
	vpandnq %xmm30, %xmm18, %xmm20
	vpxorq %xmm6, %xmm20, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpternlogq $0xD2, %xmm7, %xmm31, %xmm30
	vpternlogq $0xD2, %xmm6, %xmm7, %xmm31
	vpxorq %xmm27, %xmm0, %xmm0
	vprolq $28, %xmm0, %xmm0
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $20, %xmm13, %xmm13
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $3, %xmm5, %xmm5
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $45, %xmm24, %xmm24
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $61, %xmm19, %xmm19
	vpandnq %xmm5, %xmm13, %xmm7
	vpxorq %xmm0, %xmm7, %xmm7
	vpandnq %xmm24, %xmm5, %xmm6
	vpxorq %xmm13, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm19, %xmm24, %xmm5
	vpternlogq $0xD2, %xmm0, %xmm19, %xmm24
	vpternlogq $0xD2, %xmm13, %xmm0, %xmm19
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $1, %xmm14, %xmm14
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $6, %xmm21, %xmm21
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $25, %xmm17, %xmm17
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $8, %xmm11, %xmm11
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $18, %xmm15, %xmm15
	vpandnq %xmm17, %xmm21, %xmm0
	vpxorq %xmm14, %xmm0, %xmm0
	vpandnq %xmm11, %xmm17, %xmm13
	vpxorq %xmm21, %xmm13, %xmm13
	vpternlogq $0xD2, %xmm15, %xmm11, %xmm17
	vpternlogq $0xD2, %xmm14, %xmm15, %xmm11
	vpternlogq $0xD2, %xmm21, %xmm14, %xmm15
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $27, %xmm1, %xmm1
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $36, %xmm16, %xmm16
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $10, %xmm12, %xmm12
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $15, %xmm2, %xmm2
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $56, %xmm9, %xmm9
	vpandnq %xmm12, %xmm16, %xmm14
	vpxorq %xmm1, %xmm14, %xmm14
	vpandnq %xmm2, %xmm12, %xmm21
	vpxorq %xmm16, %xmm21, %xmm21
	vpternlogq $0xD2, %xmm9, %xmm2, %xmm12
	vpternlogq $0xD2, %xmm1, %xmm9, %xmm2
	vpternlogq $0xD2, %xmm16, %xmm1, %xmm9
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $62, %xmm3, %xmm3
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $55, %xmm4, %xmm4
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $39, %xmm23, %xmm23
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $41, %xmm22, %xmm22
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $2, %xmm8, %xmm8
	vpandnq %xmm23, %xmm4, %xmm1
	vpxorq %xmm3, %xmm1, %xmm1
	vpandnq %xmm22, %xmm23, %xmm16
	vpxorq %xmm4, %xmm16, %xmm16
	vpternlogq $0xD2, %xmm8, %xmm22, %xmm23
	vpternlogq $0xD2, %xmm3, %xmm8, %xmm22
	vpternlogq $0xD2, %xmm4, %xmm3, %xmm8
	vpxorq 192(%rax), %xmm10, %xmm10
	vpxorq %xmm7, %xmm10, %xmm25
	vpxorq %xmm0, %xmm25, %xmm25
	vpternlogq $0x96, %xmm1, %xmm14, %xmm25
	vpxorq %xmm6, %xmm20, %xmm26
	vpxorq %xmm13, %xmm26, %xmm26
	vpternlogq $0x96, %xmm16, %xmm21, %xmm26
	vpxorq %xmm5, %xmm18, %xmm27
	vpxorq %xmm17, %xmm27, %xmm27
	vpternlogq $0x96, %xmm23, %xmm12, %xmm27
	vpxorq %xmm24, %xmm30, %xmm28
	vpxorq %xmm11, %xmm28, %xmm28
	vpternlogq $0x96, %xmm22, %xmm2, %xmm28
	vpxorq %xmm19, %xmm31, %xmm29
	vpxorq %xmm15, %xmm29, %xmm29
	vpternlogq $0x96, %xmm8, %xmm9, %xmm29
	vprolq $1, %xmm25, %xmm4
	vprolq $1, %xmm27, %xmm3
	vpxorq %xmm3, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm3
	vpxorq %xmm4, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm4
	vpxorq %xmm3, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm3
	vpxorq %xmm4, %xmm29, %xmm29
	vpxorq %xmm3, %xmm27, %xmm27
	vpxorq %xmm29, %xmm10, %xmm10
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $43, %xmm17, %xmm17
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $21, %xmm2, %xmm2
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $14, %xmm8, %xmm8
	vpandnq %xmm17, %xmm6, %xmm3
	vpxorq %xmm10, %xmm3, %xmm3
	vpandnq %xmm2, %xmm17, %xmm4
	vpxorq %xmm6, %xmm4, %xmm4
	vpternlogq $0xD2, %xmm8, %xmm2, %xmm17
	vpternlogq $0xD2, %xmm10, %xmm8, %xmm2
	vpternlogq $0xD2, %xmm6, %xmm10, %xmm8
	vpxorq %xmm27, %xmm30, %xmm30
	vprolq $28, %xmm30, %xmm30
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $20, %xmm19, %xmm19
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $3, %xmm0, %xmm0
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $45, %xmm21, %xmm21
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $61, %xmm23, %xmm23
	vpandnq %xmm0, %xmm19, %xmm10
	vpxorq %xmm30, %xmm10, %xmm10
	vpandnq %xmm21, %xmm0, %xmm6
	vpxorq %xmm19, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm23, %xmm21, %xmm0
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm21
	vpternlogq $0xD2, %xmm19, %xmm30, %xmm23
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $1, %xmm20, %xmm20
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $6, %xmm5, %xmm5
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $25, %xmm11, %xmm11
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $8, %xmm9, %xmm9
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $18, %xmm1, %xmm1
	vpandnq %xmm11, %xmm5, %xmm30
	vpxorq %xmm20, %xmm30, %xmm30
	vpandnq %xmm9, %xmm11, %xmm19
	vpxorq %xmm5, %xmm19, %xmm19
	vpternlogq $0xD2, %xmm1, %xmm9, %xmm11
	vpternlogq $0xD2, %xmm20, %xmm1, %xmm9
	vpternlogq $0xD2, %xmm5, %xmm20, %xmm1
	vpxorq %xmm28, %xmm31, %xmm31
	vprolq $27, %xmm31, %xmm31
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $36, %xmm7, %xmm7
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $10, %xmm13, %xmm13
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $15, %xmm12, %xmm12
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $56, %xmm22, %xmm22
	vpandnq %xmm13, %xmm7, %xmm20
	vpxorq %xmm31, %xmm20, %xmm20
	vpandnq %xmm12, %xmm13, %xmm5
	vpxorq %xmm7, %xmm5, %xmm5
	vpternlogq $0xD2, %xmm22, %xmm12, %xmm13
	vpternlogq $0xD2, %xmm31, %xmm22, %xmm12
	vpternlogq $0xD2, %xmm7, %xmm31, %xmm22
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $62, %xmm18, %xmm18
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $55, %xmm24, %xmm24
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $39, %xmm15, %xmm15
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $41, %xmm14, %xmm14
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $2, %xmm16, %xmm16
	vpandnq %xmm15, %xmm24, %xmm31
	vpxorq %xmm18, %xmm31, %xmm31
	vpandnq %xmm14, %xmm15, %xmm7
	vpxorq %xmm24, %xmm7, %xmm7
	vpternlogq $0xD2, %xmm16, %xmm14, %xmm15
	vpternlogq $0xD2, %xmm18, %xmm16, %xmm14
	vpternlogq $0xD2, %xmm24, %xmm18, %xmm16
	vpxorq 208(%rax), %xmm3, %xmm3
	vpxorq %xmm10, %xmm3, %xmm25
	vpxorq %xmm30, %xmm25, %xmm25
	vpternlogq $0x96, %xmm31, %xmm20, %xmm25
	vpxorq %xmm6, %xmm4, %xmm26
	vpxorq %xmm19, %xmm26, %xmm26
	vpternlogq $0x96, %xmm7, %xmm5, %xmm26
	vpxorq %xmm0, %xmm17, %xmm27
	vpxorq %xmm11, %xmm27, %xmm27
	vpternlogq $0x96, %xmm15, %xmm13, %xmm27
	vpxorq %xmm21, %xmm2, %xmm28
	vpxorq %xmm9, %xmm28, %xmm28
	vpternlogq $0x96, %xmm14, %xmm12, %xmm28
	vpxorq %xmm23, %xmm8, %xmm29
	vpxorq %xmm1, %xmm29, %xmm29
	vpternlogq $0x96, %xmm16, %xmm22, %xmm29
	vprolq $1, %xmm25, %xmm24
	vprolq $1, %xmm27, %xmm18
	vpxorq %xmm18, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm18
	vpxorq %xmm24, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm24
	vpxorq %xmm18, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm18
	vpxorq %xmm24, %xmm29, %xmm29
	vpxorq %xmm18, %xmm27, %xmm27
	vpxorq %xmm29, %xmm3, %xmm3
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $43, %xmm11, %xmm11
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $21, %xmm12, %xmm12
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $14, %xmm16, %xmm16
	vpandnq %xmm11, %xmm6, %xmm18
	vpxorq %xmm3, %xmm18, %xmm18
	vpandnq %xmm12, %xmm11, %xmm24
	vpxorq %xmm6, %xmm24, %xmm24
	vpternlogq $0xD2, %xmm16, %xmm12, %xmm11
	vpternlogq $0xD2, %xmm3, %xmm16, %xmm12
	vpternlogq $0xD2, %xmm6, %xmm3, %xmm16
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $28, %xmm2, %xmm2
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $20, %xmm23, %xmm23
	vpxorq %xmm29, %xmm30, %xmm30
	vprolq $3, %xmm30, %xmm30
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $45, %xmm5, %xmm5
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $61, %xmm15, %xmm15
	vpandnq %xmm30, %xmm23, %xmm3
	vpxorq %xmm2, %xmm3, %xmm3
	vpandnq %xmm5, %xmm30, %xmm6
	vpxorq %xmm23, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm15, %xmm5, %xmm30
	vpternlogq $0xD2, %xmm2, %xmm15, %xmm5
	vpternlogq $0xD2, %xmm23, %xmm2, %xmm15
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $1, %xmm4, %xmm4
	vpxorq %xmm26, %xmm0, %xmm0
	vprolq $6, %xmm0, %xmm0
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $25, %xmm9, %xmm9
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $8, %xmm22, %xmm22
	vpxorq %xmm29, %xmm31, %xmm31
	vprolq $18, %xmm31, %xmm31
	vpandnq %xmm9, %xmm0, %xmm2
	vpxorq %xmm4, %xmm2, %xmm2
	vpandnq %xmm22, %xmm9, %xmm23
	vpxorq %xmm0, %xmm23, %xmm23
	vpternlogq $0xD2, %xmm31, %xmm22, %xmm9
	vpternlogq $0xD2, %xmm4, %xmm31, %xmm22
	vpternlogq $0xD2, %xmm0, %xmm4, %xmm31
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $27, %xmm8, %xmm8
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $36, %xmm10, %xmm10
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $10, %xmm19, %xmm19
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $15, %xmm13, %xmm13
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $56, %xmm14, %xmm14
	vpandnq %xmm19, %xmm10, %xmm4
	vpxorq %xmm8, %xmm4, %xmm4
	vpandnq %xmm13, %xmm19, %xmm0
	vpxorq %xmm10, %xmm0, %xmm0
	vpternlogq $0xD2, %xmm14, %xmm13, %xmm19
	vpternlogq $0xD2, %xmm8, %xmm14, %xmm13
	vpternlogq $0xD2, %xmm10, %xmm8, %xmm14
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $62, %xmm17, %xmm17
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $55, %xmm21, %xmm21
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $39, %xmm1, %xmm1
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $41, %xmm20, %xmm20
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $2, %xmm7, %xmm7
	vpandnq %xmm1, %xmm21, %xmm8
	vpxorq %xmm17, %xmm8, %xmm8
	vpandnq %xmm20, %xmm1, %xmm10
	vpxorq %xmm21, %xmm10, %xmm10
	vpternlogq $0xD2, %xmm7, %xmm20, %xmm1
	vpternlogq $0xD2, %xmm17, %xmm7, %xmm20
	vpternlogq $0xD2, %xmm21, %xmm17, %xmm7
	vpxorq 224(%rax), %xmm18, %xmm18
	vpxorq %xmm3, %xmm18, %xmm25
	vpxorq %xmm2, %xmm25, %xmm25
	vpternlogq $0x96, %xmm8, %xmm4, %xmm25
	vpxorq %xmm6, %xmm24, %xmm26
	vpxorq %xmm23, %xmm26, %xmm26
	vpternlogq $0x96, %xmm10, %xmm0, %xmm26
	vpxorq %xmm30, %xmm11, %xmm27
	vpxorq %xmm9, %xmm27, %xmm27
	vpternlogq $0x96, %xmm1, %xmm19, %xmm27
	vpxorq %xmm5, %xmm12, %xmm28
	vpxorq %xmm22, %xmm28, %xmm28
	vpternlogq $0x96, %xmm20, %xmm13, %xmm28
	vpxorq %xmm15, %xmm16, %xmm29
	vpxorq %xmm31, %xmm29, %xmm29
	vpternlogq $0x96, %xmm7, %xmm14, %xmm29
	vprolq $1, %xmm25, %xmm21
	vprolq $1, %xmm27, %xmm17
	vpxorq %xmm17, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm17
	vpxorq %xmm21, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm21
	vpxorq %xmm17, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm17
	vpxorq %xmm21, %xmm29, %xmm29
	vpxorq %xmm17, %xmm27, %xmm27
	vpxorq %xmm29, %xmm18, %xmm18
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $43, %xmm9, %xmm9
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $21, %xmm13, %xmm13
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $14, %xmm7, %xmm7
	vpandnq %xmm9, %xmm6, %xmm17
	vpxorq %xmm18, %xmm17, %xmm17
	vpandnq %xmm13, %xmm9, %xmm21
	vpxorq %xmm6, %xmm21, %xmm21
	vpternlogq $0xD2, %xmm7, %xmm13, %xmm9
	vpternlogq $0xD2, %xmm18, %xmm7, %xmm13
	vpternlogq $0xD2, %xmm6, %xmm18, %xmm7
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $28, %xmm12, %xmm12
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $20, %xmm15, %xmm15
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $3, %xmm2, %xmm2
	vpxorq %xmm25, %xmm0, %xmm0
	vprolq $45, %xmm0, %xmm0
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $61, %xmm1, %xmm1
	vpandnq %xmm2, %xmm15, %xmm18
	vpxorq %xmm12, %xmm18, %xmm18
	vpandnq %xmm0, %xmm2, %xmm6
	vpxorq %xmm15, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm1, %xmm0, %xmm2
	vpternlogq $0xD2, %xmm12, %xmm1, %xmm0
	vpternlogq $0xD2, %xmm15, %xmm12, %xmm1
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $1, %xmm24, %xmm24
	vpxorq %xmm26, %xmm30, %xmm30
	vprolq $6, %xmm30, %xmm30
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $25, %xmm22, %xmm22
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $8, %xmm14, %xmm14
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $18, %xmm8, %xmm8
	vpandnq %xmm22, %xmm30, %xmm12
	vpxorq %xmm24, %xmm12, %xmm12
	vpandnq %xmm14, %xmm22, %xmm15
	vpxorq %xmm30, %xmm15, %xmm15
	vpternlogq $0xD2, %xmm8, %xmm14, %xmm22
	vpternlogq $0xD2, %xmm24, %xmm8, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm8
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $27, %xmm16, %xmm16
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $36, %xmm3, %xmm3
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $10, %xmm23, %xmm23
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $15, %xmm19, %xmm19
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $56, %xmm20, %xmm20
	vpandnq %xmm23, %xmm3, %xmm24
	vpxorq %xmm16, %xmm24, %xmm24
	vpandnq %xmm19, %xmm23, %xmm30
	vpxorq %xmm3, %xmm30, %xmm30
	vpternlogq $0xD2, %xmm20, %xmm19, %xmm23
	vpternlogq $0xD2, %xmm16, %xmm20, %xmm19
	vpternlogq $0xD2, %xmm3, %xmm16, %xmm20
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $62, %xmm11, %xmm11
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $55, %xmm5, %xmm5
	vpxorq %xmm28, %xmm31, %xmm31
	vprolq $39, %xmm31, %xmm31
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $41, %xmm4, %xmm4
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $2, %xmm10, %xmm10
	vpandnq %xmm31, %xmm5, %xmm16
	vpxorq %xmm11, %xmm16, %xmm16
	vpandnq %xmm4, %xmm31, %xmm3
	vpxorq %xmm5, %xmm3, %xmm3
	vpternlogq $0xD2, %xmm10, %xmm4, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm10, %xmm4
	vpternlogq $0xD2, %xmm5, %xmm11, %xmm10
	vpxorq 240(%rax), %xmm17, %xmm17
	vpxorq %xmm18, %xmm17, %xmm25
	vpxorq %xmm12, %xmm25, %xmm25
	vpternlogq $0x96, %xmm16, %xmm24, %xmm25
	vpxorq %xmm6, %xmm21, %xmm26
	vpxorq %xmm15, %xmm26, %xmm26
	vpternlogq $0x96, %xmm3, %xmm30, %xmm26
	vpxorq %xmm2, %xmm9, %xmm27
	vpxorq %xmm22, %xmm27, %xmm27
	vpternlogq $0x96, %xmm31, %xmm23, %xmm27
	vpxorq %xmm0, %xmm13, %xmm28
	vpxorq %xmm14, %xmm28, %xmm28
	vpternlogq $0x96, %xmm4, %xmm19, %xmm28
	vpxorq %xmm1, %xmm7, %xmm29
	vpxorq %xmm8, %xmm29, %xmm29
	vpternlogq $0x96, %xmm10, %xmm20, %xmm29
	vprolq $1, %xmm25, %xmm5
	vprolq $1, %xmm27, %xmm11
	vpxorq %xmm11, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm11
	vpxorq %xmm5, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm5
	vpxorq %xmm11, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm11
	vpxorq %xmm5, %xmm29, %xmm29
	vpxorq %xmm11, %xmm27, %xmm27
	vpxorq %xmm29, %xmm17, %xmm17
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $43, %xmm22, %xmm22
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $21, %xmm19, %xmm19
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $14, %xmm10, %xmm10
	vpandnq %xmm22, %xmm6, %xmm11
	vpxorq %xmm17, %xmm11, %xmm11
	vpandnq %xmm19, %xmm22, %xmm5
	vpxorq %xmm6, %xmm5, %xmm5
	vpternlogq $0xD2, %xmm10, %xmm19, %xmm22
	vpternlogq $0xD2, %xmm17, %xmm10, %xmm19
	vpternlogq $0xD2, %xmm6, %xmm17, %xmm10
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $28, %xmm13, %xmm13
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $20, %xmm1, %xmm1
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $3, %xmm12, %xmm12
	vpxorq %xmm25, %xmm30, %xmm30
	vprolq $45, %xmm30, %xmm30
	vpxorq %xmm26, %xmm31, %xmm31
	vprolq $61, %xmm31, %xmm31
	vpandnq %xmm12, %xmm1, %xmm17
	vpxorq %xmm13, %xmm17, %xmm17
	vpandnq %xmm30, %xmm12, %xmm6
	vpxorq %xmm1, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpternlogq $0xD2, %xmm13, %xmm31, %xmm30
	vpternlogq $0xD2, %xmm1, %xmm13, %xmm31
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $1, %xmm21, %xmm21
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $6, %xmm2, %xmm2
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $25, %xmm14, %xmm14
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $8, %xmm20, %xmm20
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $18, %xmm16, %xmm16
	vpandnq %xmm14, %xmm2, %xmm13
	vpxorq %xmm21, %xmm13, %xmm13
	vpandnq %xmm20, %xmm14, %xmm1
	vpxorq %xmm2, %xmm1, %xmm1
	vpternlogq $0xD2, %xmm16, %xmm20, %xmm14
	vpternlogq $0xD2, %xmm21, %xmm16, %xmm20
	vpternlogq $0xD2, %xmm2, %xmm21, %xmm16
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $27, %xmm7, %xmm7
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $36, %xmm18, %xmm18
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $10, %xmm15, %xmm15
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $15, %xmm23, %xmm23
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $56, %xmm4, %xmm4
	vpandnq %xmm15, %xmm18, %xmm21
	vpxorq %xmm7, %xmm21, %xmm21
	vpandnq %xmm23, %xmm15, %xmm2
	vpxorq %xmm18, %xmm2, %xmm2
	vpternlogq $0xD2, %xmm4, %xmm23, %xmm15
	vpternlogq $0xD2, %xmm7, %xmm4, %xmm23
	vpternlogq $0xD2, %xmm18, %xmm7, %xmm4
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $62, %xmm9, %xmm9
	vpxorq %xmm27, %xmm0, %xmm0
	vprolq $55, %xmm0, %xmm0
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $39, %xmm8, %xmm8
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $41, %xmm24, %xmm24
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $2, %xmm3, %xmm3
	vpandnq %xmm8, %xmm0, %xmm7
	vpxorq %xmm9, %xmm7, %xmm7
	vpandnq %xmm24, %xmm8, %xmm18
	vpxorq %xmm0, %xmm18, %xmm18
	vpternlogq $0xD2, %xmm3, %xmm24, %xmm8
	vpternlogq $0xD2, %xmm9, %xmm3, %xmm24
	vpternlogq $0xD2, %xmm0, %xmm9, %xmm3
	vpxorq 256(%rax), %xmm11, %xmm11
	vpxorq %xmm17, %xmm11, %xmm25
	vpxorq %xmm13, %xmm25, %xmm25
	vpternlogq $0x96, %xmm7, %xmm21, %xmm25
	vpxorq %xmm6, %xmm5, %xmm26
	vpxorq %xmm1, %xmm26, %xmm26
	vpternlogq $0x96, %xmm18, %xmm2, %xmm26
	vpxorq %xmm12, %xmm22, %xmm27
	vpxorq %xmm14, %xmm27, %xmm27
	vpternlogq $0x96, %xmm8, %xmm15, %xmm27
	vpxorq %xmm30, %xmm19, %xmm28
	vpxorq %xmm20, %xmm28, %xmm28
	vpternlogq $0x96, %xmm24, %xmm23, %xmm28
	vpxorq %xmm31, %xmm10, %xmm29
	vpxorq %xmm16, %xmm29, %xmm29
	vpternlogq $0x96, %xmm3, %xmm4, %xmm29
	vprolq $1, %xmm25, %xmm0
	vprolq $1, %xmm27, %xmm9
	vpxorq %xmm9, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm9
	vpxorq %xmm0, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm0
	vpxorq %xmm9, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm9
	vpxorq %xmm0, %xmm29, %xmm29
	vpxorq %xmm9, %xmm27, %xmm27
	vpxorq %xmm29, %xmm11, %xmm11
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $43, %xmm14, %xmm14
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $21, %xmm23, %xmm23
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $14, %xmm3, %xmm3
	vpandnq %xmm14, %xmm6, %xmm9
	vpxorq %xmm11, %xmm9, %xmm9
	vpandnq %xmm23, %xmm14, %xmm0
	vpxorq %xmm6, %xmm0, %xmm0
	vpternlogq $0xD2, %xmm3, %xmm23, %xmm14
	vpternlogq $0xD2, %xmm11, %xmm3, %xmm23
	vpternlogq $0xD2, %xmm6, %xmm11, %xmm3
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $28, %xmm19, %xmm19
	vpxorq %xmm28, %xmm31, %xmm31
	vprolq $20, %xmm31, %xmm31
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $3, %xmm13, %xmm13
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $45, %xmm2, %xmm2
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $61, %xmm8, %xmm8
	vpandnq %xmm13, %xmm31, %xmm11
	vpxorq %xmm19, %xmm11, %xmm11
	vpandnq %xmm2, %xmm13, %xmm6
	vpxorq %xmm31, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm8, %xmm2, %xmm13
	vpternlogq $0xD2, %xmm19, %xmm8, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm19, %xmm8
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $1, %xmm5, %xmm5
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $6, %xmm12, %xmm12
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $25, %xmm20, %xmm20
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $8, %xmm4, %xmm4
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $18, %xmm7, %xmm7
	vpandnq %xmm20, %xmm12, %xmm19
	vpxorq %xmm5, %xmm19, %xmm19
	vpandnq %xmm4, %xmm20, %xmm31
	vpxorq %xmm12, %xmm31, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm4, %xmm20
	vpternlogq $0xD2, %xmm5, %xmm7, %xmm4
	vpternlogq $0xD2, %xmm12, %xmm5, %xmm7
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $27, %xmm10, %xmm10
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $36, %xmm17, %xmm17
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $10, %xmm1, %xmm1
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $15, %xmm15, %xmm15
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $56, %xmm24, %xmm24
	vpandnq %xmm1, %xmm17, %xmm5
	vpxorq %xmm10, %xmm5, %xmm5
	vpandnq %xmm15, %xmm1, %xmm12
	vpxorq %xmm17, %xmm12, %xmm12
	vpternlogq $0xD2, %xmm24, %xmm15, %xmm1
	vpternlogq $0xD2, %xmm10, %xmm24, %xmm15
	vpternlogq $0xD2, %xmm17, %xmm10, %xmm24
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $62, %xmm22, %xmm22
	vpxorq %xmm27, %xmm30, %xmm30
	vprolq $55, %xmm30, %xmm30
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $39, %xmm16, %xmm16
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $41, %xmm21, %xmm21
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $2, %xmm18, %xmm18
	vpandnq %xmm16, %xmm30, %xmm10
	vpxorq %xmm22, %xmm10, %xmm10
	vpandnq %xmm21, %xmm16, %xmm17
	vpxorq %xmm30, %xmm17, %xmm17
	vpternlogq $0xD2, %xmm18, %xmm21, %xmm16
	vpternlogq $0xD2, %xmm22, %xmm18, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm18
	vpxorq 272(%rax), %xmm9, %xmm9
	vpxorq %xmm11, %xmm9, %xmm25
	vpxorq %xmm19, %xmm25, %xmm25
	vpternlogq $0x96, %xmm10, %xmm5, %xmm25
	vpxorq %xmm6, %xmm0, %xmm26
	vpxorq %xmm31, %xmm26, %xmm26
	vpternlogq $0x96, %xmm17, %xmm12, %xmm26
	vpxorq %xmm13, %xmm14, %xmm27
	vpxorq %xmm20, %xmm27, %xmm27
	vpternlogq $0x96, %xmm16, %xmm1, %xmm27
	vpxorq %xmm2, %xmm23, %xmm28
	vpxorq %xmm4, %xmm28, %xmm28
	vpternlogq $0x96, %xmm21, %xmm15, %xmm28
	vpxorq %xmm8, %xmm3, %xmm29
	vpxorq %xmm7, %xmm29, %xmm29
	vpternlogq $0x96, %xmm18, %xmm24, %xmm29
	vprolq $1, %xmm25, %xmm30
	vprolq $1, %xmm27, %xmm22
	vpxorq %xmm22, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm22
	vpxorq %xmm30, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm30
	vpxorq %xmm22, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm22
	vpxorq %xmm30, %xmm29, %xmm29
	vpxorq %xmm22, %xmm27, %xmm27
	vpxorq %xmm29, %xmm9, %xmm9
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $43, %xmm20, %xmm20
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $21, %xmm15, %xmm15
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $14, %xmm18, %xmm18
	vpandnq %xmm20, %xmm6, %xmm22
	vpxorq %xmm9, %xmm22, %xmm22
	vpandnq %xmm15, %xmm20, %xmm30
	vpxorq %xmm6, %xmm30, %xmm30
	vpternlogq $0xD2, %xmm18, %xmm15, %xmm20
	vpternlogq $0xD2, %xmm9, %xmm18, %xmm15
	vpternlogq $0xD2, %xmm6, %xmm9, %xmm18
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $28, %xmm23, %xmm23
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $20, %xmm8, %xmm8
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $3, %xmm19, %xmm19
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $45, %xmm12, %xmm12
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $61, %xmm16, %xmm16
	vpandnq %xmm19, %xmm8, %xmm9
	vpxorq %xmm23, %xmm9, %xmm9
	vpandnq %xmm12, %xmm19, %xmm6
	vpxorq %xmm8, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm16, %xmm12, %xmm19
	vpternlogq $0xD2, %xmm23, %xmm16, %xmm12
	vpternlogq $0xD2, %xmm8, %xmm23, %xmm16
	vpxorq %xmm25, %xmm0, %xmm0
	vprolq $1, %xmm0, %xmm0
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $6, %xmm13, %xmm13
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $25, %xmm4, %xmm4
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $8, %xmm24, %xmm24
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $18, %xmm10, %xmm10
	vpandnq %xmm4, %xmm13, %xmm23
	vpxorq %xmm0, %xmm23, %xmm23
	vpandnq %xmm24, %xmm4, %xmm8
	vpxorq %xmm13, %xmm8, %xmm8
	vpternlogq $0xD2, %xmm10, %xmm24, %xmm4
	vpternlogq $0xD2, %xmm0, %xmm10, %xmm24
	vpternlogq $0xD2, %xmm13, %xmm0, %xmm10
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $27, %xmm3, %xmm3
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $36, %xmm11, %xmm11
	vpxorq %xmm25, %xmm31, %xmm31
	vprolq $10, %xmm31, %xmm31
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $15, %xmm1, %xmm1
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $56, %xmm21, %xmm21
	vpandnq %xmm31, %xmm11, %xmm0
	vpxorq %xmm3, %xmm0, %xmm0
	vpandnq %xmm1, %xmm31, %xmm13
	vpxorq %xmm11, %xmm13, %xmm13
	vpternlogq $0xD2, %xmm21, %xmm1, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm21, %xmm1
	vpternlogq $0xD2, %xmm11, %xmm3, %xmm21
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $62, %xmm14, %xmm14
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $55, %xmm2, %xmm2
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $39, %xmm7, %xmm7
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $41, %xmm5, %xmm5
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $2, %xmm17, %xmm17
	vpandnq %xmm7, %xmm2, %xmm3
	vpxorq %xmm14, %xmm3, %xmm3
	vpandnq %xmm5, %xmm7, %xmm11
	vpxorq %xmm2, %xmm11, %xmm11
	vpternlogq $0xD2, %xmm17, %xmm5, %xmm7
	vpternlogq $0xD2, %xmm14, %xmm17, %xmm5
	vpternlogq $0xD2, %xmm2, %xmm14, %xmm17
	vpxorq 288(%rax), %xmm22, %xmm22
	vpxorq %xmm9, %xmm22, %xmm25
	vpxorq %xmm23, %xmm25, %xmm25
	vpternlogq $0x96, %xmm3, %xmm0, %xmm25
	vpxorq %xmm6, %xmm30, %xmm26
	vpxorq %xmm8, %xmm26, %xmm26
	vpternlogq $0x96, %xmm11, %xmm13, %xmm26
	vpxorq %xmm19, %xmm20, %xmm27
	vpxorq %xmm4, %xmm27, %xmm27
	vpternlogq $0x96, %xmm7, %xmm31, %xmm27
	vpxorq %xmm12, %xmm15, %xmm28
	vpxorq %xmm24, %xmm28, %xmm28
	vpternlogq $0x96, %xmm5, %xmm1, %xmm28
	vpxorq %xmm16, %xmm18, %xmm29
	vpxorq %xmm10, %xmm29, %xmm29
	vpternlogq $0x96, %xmm17, %xmm21, %xmm29
	vprolq $1, %xmm25, %xmm2
	vprolq $1, %xmm27, %xmm14
	vpxorq %xmm14, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm14
	vpxorq %xmm2, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm2
	vpxorq %xmm14, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm14
	vpxorq %xmm2, %xmm29, %xmm29
	vpxorq %xmm14, %xmm27, %xmm27
	vpxorq %xmm29, %xmm22, %xmm22
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $43, %xmm4, %xmm4
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $21, %xmm1, %xmm1
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $14, %xmm17, %xmm17
	vpandnq %xmm4, %xmm6, %xmm14
	vpxorq %xmm22, %xmm14, %xmm14
	vpandnq %xmm1, %xmm4, %xmm2
	vpxorq %xmm6, %xmm2, %xmm2
	vpternlogq $0xD2, %xmm17, %xmm1, %xmm4
	vpternlogq $0xD2, %xmm22, %xmm17, %xmm1
	vpternlogq $0xD2, %xmm6, %xmm22, %xmm17
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $28, %xmm15, %xmm15
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $20, %xmm16, %xmm16
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $3, %xmm23, %xmm23
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $45, %xmm13, %xmm13
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $61, %xmm7, %xmm7
	vpandnq %xmm23, %xmm16, %xmm22
	vpxorq %xmm15, %xmm22, %xmm22
	vpandnq %xmm13, %xmm23, %xmm6
	vpxorq %xmm16, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm7, %xmm13, %xmm23
	vpternlogq $0xD2, %xmm15, %xmm7, %xmm13
	vpternlogq $0xD2, %xmm16, %xmm15, %xmm7
	vpxorq %xmm25, %xmm30, %xmm30
	vprolq $1, %xmm30, %xmm30
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $6, %xmm19, %xmm19
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $25, %xmm24, %xmm24
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $8, %xmm21, %xmm21
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $18, %xmm3, %xmm3
	vpandnq %xmm24, %xmm19, %xmm15
	vpxorq %xmm30, %xmm15, %xmm15
	vpandnq %xmm21, %xmm24, %xmm16
	vpxorq %xmm19, %xmm16, %xmm16
	vpternlogq $0xD2, %xmm3, %xmm21, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm21
	vpternlogq $0xD2, %xmm19, %xmm30, %xmm3
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $27, %xmm18, %xmm18
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $36, %xmm9, %xmm9
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $10, %xmm8, %xmm8
	vpxorq %xmm26, %xmm31, %xmm31
	vprolq $15, %xmm31, %xmm31
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $56, %xmm5, %xmm5
	vpandnq %xmm8, %xmm9, %xmm30
	vpxorq %xmm18, %xmm30, %xmm30
	vpandnq %xmm31, %xmm8, %xmm19
	vpxorq %xmm9, %xmm19, %xmm19
	vpternlogq $0xD2, %xmm5, %xmm31, %xmm8
	vpternlogq $0xD2, %xmm18, %xmm5, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm18, %xmm5
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $62, %xmm20, %xmm20
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $55, %xmm12, %xmm12
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $39, %xmm10, %xmm10
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $41, %xmm0, %xmm0
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $2, %xmm11, %xmm11
	vpandnq %xmm10, %xmm12, %xmm18
	vpxorq %xmm20, %xmm18, %xmm18
	vpandnq %xmm0, %xmm10, %xmm9
	vpxorq %xmm12, %xmm9, %xmm9
	vpternlogq $0xD2, %xmm11, %xmm0, %xmm10
	vpternlogq $0xD2, %xmm20, %xmm11, %xmm0
	vpternlogq $0xD2, %xmm12, %xmm20, %xmm11
	vpxorq 304(%rax), %xmm14, %xmm14
	vpxorq %xmm22, %xmm14, %xmm25
	vpxorq %xmm15, %xmm25, %xmm25
	vpternlogq $0x96, %xmm18, %xmm30, %xmm25
	vpxorq %xmm6, %xmm2, %xmm26
	vpxorq %xmm16, %xmm26, %xmm26
	vpternlogq $0x96, %xmm9, %xmm19, %xmm26
	vpxorq %xmm23, %xmm4, %xmm27
	vpxorq %xmm24, %xmm27, %xmm27
	vpternlogq $0x96, %xmm10, %xmm8, %xmm27
	vpxorq %xmm13, %xmm1, %xmm28
	vpxorq %xmm21, %xmm28, %xmm28
	vpternlogq $0x96, %xmm0, %xmm31, %xmm28
	vpxorq %xmm7, %xmm17, %xmm29
	vpxorq %xmm3, %xmm29, %xmm29
	vpternlogq $0x96, %xmm11, %xmm5, %xmm29
	vprolq $1, %xmm25, %xmm12
	vprolq $1, %xmm27, %xmm20
	vpxorq %xmm20, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm20
	vpxorq %xmm12, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm12
	vpxorq %xmm20, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm20
	vpxorq %xmm12, %xmm29, %xmm29
	vpxorq %xmm20, %xmm27, %xmm27
	vpxorq %xmm29, %xmm14, %xmm14
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $43, %xmm24, %xmm24
	vpxorq %xmm27, %xmm31, %xmm31
	vprolq $21, %xmm31, %xmm31
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $14, %xmm11, %xmm11
	vpandnq %xmm24, %xmm6, %xmm20
	vpxorq %xmm14, %xmm20, %xmm20
	vpandnq %xmm31, %xmm24, %xmm12
	vpxorq %xmm6, %xmm12, %xmm12
	vpternlogq $0xD2, %xmm11, %xmm31, %xmm24
	vpternlogq $0xD2, %xmm14, %xmm11, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm14, %xmm11
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $28, %xmm1, %xmm1
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $20, %xmm7, %xmm7
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $3, %xmm15, %xmm15
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $45, %xmm19, %xmm19
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $61, %xmm10, %xmm10
	vpandnq %xmm15, %xmm7, %xmm14
	vpxorq %xmm1, %xmm14, %xmm14
	vpandnq %xmm19, %xmm15, %xmm6
	vpxorq %xmm7, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm10, %xmm19, %xmm15
	vpternlogq $0xD2, %xmm1, %xmm10, %xmm19
	vpternlogq $0xD2, %xmm7, %xmm1, %xmm10
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $1, %xmm2, %xmm2
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $6, %xmm23, %xmm23
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $25, %xmm21, %xmm21
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $8, %xmm5, %xmm5
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $18, %xmm18, %xmm18
	vpandnq %xmm21, %xmm23, %xmm1
	vpxorq %xmm2, %xmm1, %xmm1
	vpandnq %xmm5, %xmm21, %xmm7
	vpxorq %xmm23, %xmm7, %xmm7
	vpternlogq $0xD2, %xmm18, %xmm5, %xmm21
	vpternlogq $0xD2, %xmm2, %xmm18, %xmm5
	vpternlogq $0xD2, %xmm23, %xmm2, %xmm18
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $27, %xmm17, %xmm17
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $36, %xmm22, %xmm22
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $10, %xmm16, %xmm16
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $15, %xmm8, %xmm8
	vpxorq %xmm27, %xmm0, %xmm0
	vprolq $56, %xmm0, %xmm0
	vpandnq %xmm16, %xmm22, %xmm2
	vpxorq %xmm17, %xmm2, %xmm2
	vpandnq %xmm8, %xmm16, %xmm23
	vpxorq %xmm22, %xmm23, %xmm23
	vpternlogq $0xD2, %xmm0, %xmm8, %xmm16
	vpternlogq $0xD2, %xmm17, %xmm0, %xmm8
	vpternlogq $0xD2, %xmm22, %xmm17, %xmm0
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $62, %xmm4, %xmm4
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $55, %xmm13, %xmm13
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $39, %xmm3, %xmm3
	vpxorq %xmm29, %xmm30, %xmm30
	vprolq $41, %xmm30, %xmm30
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $2, %xmm9, %xmm9
	vpandnq %xmm3, %xmm13, %xmm17
	vpxorq %xmm4, %xmm17, %xmm17
	vpandnq %xmm30, %xmm3, %xmm22
	vpxorq %xmm13, %xmm22, %xmm22
	vpternlogq $0xD2, %xmm9, %xmm30, %xmm3
	vpternlogq $0xD2, %xmm4, %xmm9, %xmm30
	vpternlogq $0xD2, %xmm13, %xmm4, %xmm9
	vpxorq 320(%rax), %xmm20, %xmm20
	vpxorq %xmm14, %xmm20, %xmm25
	vpxorq %xmm1, %xmm25, %xmm25
	vpternlogq $0x96, %xmm17, %xmm2, %xmm25
	vpxorq %xmm6, %xmm12, %xmm26
	vpxorq %xmm7, %xmm26, %xmm26
	vpternlogq $0x96, %xmm22, %xmm23, %xmm26
	vpxorq %xmm15, %xmm24, %xmm27
	vpxorq %xmm21, %xmm27, %xmm27
	vpternlogq $0x96, %xmm3, %xmm16, %xmm27
	vpxorq %xmm19, %xmm31, %xmm28
	vpxorq %xmm5, %xmm28, %xmm28
	vpternlogq $0x96, %xmm30, %xmm8, %xmm28
	vpxorq %xmm10, %xmm11, %xmm29
	vpxorq %xmm18, %xmm29, %xmm29
	vpternlogq $0x96, %xmm9, %xmm0, %xmm29
	vprolq $1, %xmm25, %xmm13
	vprolq $1, %xmm27, %xmm4
	vpxorq %xmm4, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm4
	vpxorq %xmm13, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm13
	vpxorq %xmm4, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm4
	vpxorq %xmm13, %xmm29, %xmm29
	vpxorq %xmm4, %xmm27, %xmm27
	vpxorq %xmm29, %xmm20, %xmm20
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $43, %xmm21, %xmm21
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $21, %xmm8, %xmm8
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $14, %xmm9, %xmm9
	vpandnq %xmm21, %xmm6, %xmm4
	vpxorq %xmm20, %xmm4, %xmm4
	vpandnq %xmm8, %xmm21, %xmm13
	vpxorq %xmm6, %xmm13, %xmm13
	vpternlogq $0xD2, %xmm9, %xmm8, %xmm21
	vpternlogq $0xD2, %xmm20, %xmm9, %xmm8
	vpternlogq $0xD2, %xmm6, %xmm20, %xmm9
	vpxorq %xmm27, %xmm31, %xmm31
	vprolq $28, %xmm31, %xmm31
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $20, %xmm10, %xmm10
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $3, %xmm1, %xmm1
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $45, %xmm23, %xmm23
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $61, %xmm3, %xmm3
	vpandnq %xmm1, %xmm10, %xmm20
	vpxorq %xmm31, %xmm20, %xmm20
	vpandnq %xmm23, %xmm1, %xmm6
	vpxorq %xmm10, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm3, %xmm23, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm3, %xmm23
	vpternlogq $0xD2, %xmm10, %xmm31, %xmm3
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $1, %xmm12, %xmm12
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $6, %xmm15, %xmm15
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $25, %xmm5, %xmm5
	vpxorq %xmm28, %xmm0, %xmm0
	vprolq $8, %xmm0, %xmm0
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $18, %xmm17, %xmm17
	vpandnq %xmm5, %xmm15, %xmm31
	vpxorq %xmm12, %xmm31, %xmm31
	vpandnq %xmm0, %xmm5, %xmm10
	vpxorq %xmm15, %xmm10, %xmm10
	vpternlogq $0xD2, %xmm17, %xmm0, %xmm5
	vpternlogq $0xD2, %xmm12, %xmm17, %xmm0
	vpternlogq $0xD2, %xmm15, %xmm12, %xmm17
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $27, %xmm11, %xmm11
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $36, %xmm14, %xmm14
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $10, %xmm7, %xmm7
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $15, %xmm16, %xmm16
	vpxorq %xmm27, %xmm30, %xmm30
	vprolq $56, %xmm30, %xmm30
	vpandnq %xmm7, %xmm14, %xmm12
	vpxorq %xmm11, %xmm12, %xmm12
	vpandnq %xmm16, %xmm7, %xmm15
	vpxorq %xmm14, %xmm15, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm7
	vpternlogq $0xD2, %xmm11, %xmm30, %xmm16
	vpternlogq $0xD2, %xmm14, %xmm11, %xmm30
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $62, %xmm24, %xmm24
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $55, %xmm19, %xmm19
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $39, %xmm18, %xmm18
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $41, %xmm2, %xmm2
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $2, %xmm22, %xmm22
	vpandnq %xmm18, %xmm19, %xmm11
	vpxorq %xmm24, %xmm11, %xmm11
	vpandnq %xmm2, %xmm18, %xmm14
	vpxorq %xmm19, %xmm14, %xmm14
	vpternlogq $0xD2, %xmm22, %xmm2, %xmm18
	vpternlogq $0xD2, %xmm24, %xmm22, %xmm2
	vpternlogq $0xD2, %xmm19, %xmm24, %xmm22
	vpxorq 336(%rax), %xmm4, %xmm4
	vpxorq %xmm20, %xmm4, %xmm25
	vpxorq %xmm31, %xmm25, %xmm25
	vpternlogq $0x96, %xmm11, %xmm12, %xmm25
	vpxorq %xmm6, %xmm13, %xmm26
	vpxorq %xmm10, %xmm26, %xmm26
	vpternlogq $0x96, %xmm14, %xmm15, %xmm26
	vpxorq %xmm1, %xmm21, %xmm27
	vpxorq %xmm5, %xmm27, %xmm27
	vpternlogq $0x96, %xmm18, %xmm7, %xmm27
	vpxorq %xmm23, %xmm8, %xmm28
	vpxorq %xmm0, %xmm28, %xmm28
	vpternlogq $0x96, %xmm2, %xmm16, %xmm28
	vpxorq %xmm3, %xmm9, %xmm29
	vpxorq %xmm17, %xmm29, %xmm29
	vpternlogq $0x96, %xmm22, %xmm30, %xmm29
	vprolq $1, %xmm25, %xmm19
	vprolq $1, %xmm27, %xmm24
	vpxorq %xmm24, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm24
	vpxorq %xmm19, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm19
	vpxorq %xmm24, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm24
	vpxorq %xmm19, %xmm29, %xmm29
	vpxorq %xmm24, %xmm27, %xmm27
	vpxorq %xmm29, %xmm4, %xmm4
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $43, %xmm5, %xmm5
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $21, %xmm16, %xmm16
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $14, %xmm22, %xmm22
	vpandnq %xmm5, %xmm6, %xmm24
	vpxorq %xmm4, %xmm24, %xmm24
	vpandnq %xmm16, %xmm5, %xmm19
	vpxorq %xmm6, %xmm19, %xmm19
	vpternlogq $0xD2, %xmm22, %xmm16, %xmm5
	vpternlogq $0xD2, %xmm4, %xmm22, %xmm16
	vpternlogq $0xD2, %xmm6, %xmm4, %xmm22
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $28, %xmm8, %xmm8
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $20, %xmm3, %xmm3
	vpxorq %xmm29, %xmm31, %xmm31
	vprolq $3, %xmm31, %xmm31
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $45, %xmm15, %xmm15
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $61, %xmm18, %xmm18
	vpandnq %xmm31, %xmm3, %xmm4
	vpxorq %xmm8, %xmm4, %xmm4
	vpandnq %xmm15, %xmm31, %xmm6
	vpxorq %xmm3, %xmm6, %xmm6
	vpternlogq $0xD2, %xmm18, %xmm15, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm18, %xmm15
	vpternlogq $0xD2, %xmm3, %xmm8, %xmm18
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $1, %xmm13, %xmm13
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $6, %xmm1, %xmm1
	vpxorq %xmm27, %xmm0, %xmm0
	vprolq $25, %xmm0, %xmm0
	vpxorq %xmm28, %xmm30, %xmm30
	vprolq $8, %xmm30, %xmm30
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $18, %xmm11, %xmm11
	vpandnq %xmm0, %xmm1, %xmm8
	vpxorq %xmm13, %xmm8, %xmm8
	vpandnq %xmm30, %xmm0, %xmm3
	vpxorq %xmm1, %xmm3, %xmm3
	vpternlogq $0xD2, %xmm11, %xmm30, %xmm0
	vpternlogq $0xD2, %xmm13, %xmm11, %xmm30
	vpternlogq $0xD2, %xmm1, %xmm13, %xmm11
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $27, %xmm9, %xmm9
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $36, %xmm20, %xmm20
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $10, %xmm10, %xmm10
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $15, %xmm7, %xmm7
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $56, %xmm2, %xmm2
	vpandnq %xmm10, %xmm20, %xmm13
	vpxorq %xmm9, %xmm13, %xmm13
	vpandnq %xmm7, %xmm10, %xmm1
	vpxorq %xmm20, %xmm1, %xmm1
	vpternlogq $0xD2, %xmm2, %xmm7, %xmm10
	vpternlogq $0xD2, %xmm9, %xmm2, %xmm7
	vpternlogq $0xD2, %xmm20, %xmm9, %xmm2
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $62, %xmm21, %xmm21
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $55, %xmm23, %xmm23
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $39, %xmm17, %xmm17
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $41, %xmm12, %xmm12
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $2, %xmm14, %xmm14
	vpandnq %xmm17, %xmm23, %xmm9
	vpxorq %xmm21, %xmm9, %xmm9
	vpandnq %xmm12, %xmm17, %xmm20
	vpxorq %xmm23, %xmm20, %xmm20
	vpternlogq $0xD2, %xmm14, %xmm12, %xmm17
	vpternlogq $0xD2, %xmm21, %xmm14, %xmm12
	vpternlogq $0xD2, %xmm23, %xmm21, %xmm14
	vpxorq 352(%rax), %xmm24, %xmm24
	vpxorq %xmm4, %xmm24, %xmm25
	vpxorq %xmm8, %xmm25, %xmm25
	vpternlogq $0x96, %xmm9, %xmm13, %xmm25
	vpxorq %xmm6, %xmm19, %xmm26
	vpxorq %xmm3, %xmm26, %xmm26
	vpternlogq $0x96, %xmm20, %xmm1, %xmm26
	vpxorq %xmm31, %xmm5, %xmm27
	vpxorq %xmm0, %xmm27, %xmm27
	vpternlogq $0x96, %xmm17, %xmm10, %xmm27
	vpxorq %xmm15, %xmm16, %xmm28
	vpxorq %xmm30, %xmm28, %xmm28
	vpternlogq $0x96, %xmm12, %xmm7, %xmm28
	vpxorq %xmm18, %xmm22, %xmm29
	vpxorq %xmm11, %xmm29, %xmm29
	vpternlogq $0x96, %xmm14, %xmm2, %xmm29
	vprolq $1, %xmm25, %xmm23
	vprolq $1, %xmm27, %xmm21
	vpxorq %xmm21, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm21
	vpxorq %xmm23, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm23
	vpxorq %xmm21, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm21
	vpxorq %xmm23, %xmm29, %xmm29
	vpxorq %xmm21, %xmm27, %xmm27
	vpxorq %xmm29, %xmm24, %xmm24
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $44, %xmm6, %xmm6
	vpxorq %xmm26, %xmm0, %xmm0
	vprolq $43, %xmm0, %xmm0
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $21, %xmm7, %xmm7
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $14, %xmm14, %xmm14
	vpandnq %xmm0, %xmm6, %xmm21
	vpxorq %xmm24, %xmm21, %xmm21
	vpandnq %xmm7, %xmm0, %xmm23
	vpxorq %xmm6, %xmm23, %xmm23
	vpternlogq $0xD2, %xmm14, %xmm7, %xmm0
	vpternlogq $0xD2, %xmm24, %xmm14, %xmm7
	vpxorq 368(%rax), %xmm21, %xmm21
	vmovdqa64 %xmm21, %xmm26
	vmovdqa64 %xmm23, %xmm27
	vmovdqa64 %xmm0, %xmm28
	vmovdqa64 %xmm7, %xmm29
	decq %r8
	jnz 1b
	vmovdqu64 %xmm26, 0(%rsp)
	vmovdqu64 %xmm27, 16(%rsp)
	vmovdqu64 %xmm28, 32(%rsp)
	vmovdqu64 %xmm29, 48(%rsp)
	
# 0 "" 2
#NO_APP
.L16:
	xorl	%eax, %eax
.L17:
	movq	(%rdx), %rcx
	addq	$16, %rdx
	movq	%rcx, (%rdi,%rax)
	movq	-8(%rdx), %rcx
	movq	%rcx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	$32, %rax
	jne	.L17
	movq	120(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L26
	vzeroupper
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L26:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7376:
	.size	chain2_avx512vln, .-chain2_avx512vln
	.p2align 4
	.type	chain_avx512vln, @function
chain_avx512vln:
.LFB7377:
	.cfi_startproc
	endbr64
	subq	$56, %rsp
	.cfi_def_cfa_offset 64
	movq	%rsi, %rcx
	movq	%fs:40, %r8
	movq	%r8, 40(%rsp)
	movq	%rdx, %r8
	movq	%rsp, %rdx
	call	chain2_avx512vln
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L31
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L31:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7377:
	.size	chain_avx512vln, .-chain_avx512vln
	.p2align 4
	.type	chain2_avx512vl, @function
chain2_avx512vl:
.LFB7374:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %rax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	andq	$-64, %rsp
	addq	$-128, %rsp
	vmovdqu	(%rax), %ymm1
	vmovdqu	(%rcx), %ymm2
	vmovdqa	.LC0(%rip), %ymm0
	movq	%fs:40, %rsi
	movq	%rsi, 120(%rsp)
	movq	%rdx, %rsi
	movq	%rsp, %rdx
	vpermi2q	%ymm2, %ymm1, %ymm0
	vmovdqa	%ymm0, (%rsp)
	vmovdqa	.LC1(%rip), %ymm0
	vpermi2q	%ymm2, %ymm1, %ymm0
	vmovdqa	%ymm0, 32(%rsp)
	testq	%r8, %r8
	je	.L33
	leaq	vla_k(%rip), %rax
#APP
# 38 "keccak_vlasm.inc" 1
	vmovdqu64 0(%rsp), %xmm26
	vmovdqu64 16(%rsp), %xmm27
	vmovdqu64 32(%rsp), %xmm28
	vmovdqu64 48(%rsp), %xmm29
	1:
	vpsllq $8, %xmm26, %xmm0
	vporq 384(%rax), %xmm0, %xmm0
	vpsrlq $56, %xmm26, %xmm30
	vpsllq $8, %xmm27, %xmm1
	vporq %xmm30, %xmm1, %xmm1
	vpsrlq $56, %xmm27, %xmm30
	vpsllq $8, %xmm28, %xmm2
	vporq %xmm30, %xmm2, %xmm2
	vpsrlq $56, %xmm28, %xmm30
	vpsllq $8, %xmm29, %xmm3
	vporq %xmm30, %xmm3, %xmm3
	vpsrlq $56, %xmm29, %xmm4
	vporq 400(%rax), %xmm4, %xmm4
	vmovdqa64 416(%rax), %xmm16
	vmovdqa64 %xmm0, %xmm25
	vpxorq %xmm16, %xmm1, %xmm26
	vmovdqa64 %xmm2, %xmm27
	vmovdqa64 %xmm3, %xmm28
	vmovdqa64 %xmm4, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vprolq $44, %xmm25, %xmm6
	vprolq $43, %xmm26, %xmm12
	vprolq $21, %xmm27, %xmm18
	vprolq $14, %xmm28, %xmm24
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm6, %xmm31
	vpternlogq $0xD2, %xmm12, %xmm6, %xmm0
	vpternlogq $0xD2, %xmm18, %xmm12, %xmm6
	vpternlogq $0xD2, %xmm24, %xmm18, %xmm12
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm18
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm24
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $28, %xmm3, %xmm3
	vprolq $20, %xmm28, %xmm9
	vprolq $3, %xmm29, %xmm10
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $45, %xmm16, %xmm16
	vprolq $61, %xmm26, %xmm22
	vmovdqa64 %xmm3, %xmm30
	vmovdqa64 %xmm9, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm9, %xmm3
	vpternlogq $0xD2, %xmm16, %xmm10, %xmm9
	vpternlogq $0xD2, %xmm22, %xmm16, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm16
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm22
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $1, %xmm1, %xmm1
	vprolq $6, %xmm26, %xmm7
	vprolq $25, %xmm27, %xmm13
	vprolq $8, %xmm28, %xmm19
	vprolq $18, %xmm29, %xmm20
	vmovdqa64 %xmm1, %xmm30
	vmovdqa64 %xmm7, %xmm31
	vpternlogq $0xD2, %xmm13, %xmm7, %xmm1
	vpternlogq $0xD2, %xmm19, %xmm13, %xmm7
	vpternlogq $0xD2, %xmm20, %xmm19, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm20, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm20
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $27, %xmm4, %xmm4
	vprolq $36, %xmm29, %xmm5
	vprolq $10, %xmm25, %xmm11
	vprolq $15, %xmm26, %xmm17
	vprolq $56, %xmm27, %xmm23
	vmovdqa64 %xmm4, %xmm30
	vmovdqa64 %xmm5, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm5, %xmm4
	vpternlogq $0xD2, %xmm17, %xmm11, %xmm5
	vpternlogq $0xD2, %xmm23, %xmm17, %xmm11
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm17
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm23
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $62, %xmm2, %xmm2
	vprolq $55, %xmm27, %xmm8
	vprolq $39, %xmm28, %xmm14
	vprolq $41, %xmm29, %xmm15
	vprolq $2, %xmm25, %xmm21
	vmovdqa64 %xmm2, %xmm30
	vmovdqa64 %xmm8, %xmm31
	vpternlogq $0xD2, %xmm14, %xmm8, %xmm2
	vpternlogq $0xD2, %xmm15, %xmm14, %xmm8
	vpternlogq $0xD2, %xmm21, %xmm15, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm15
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm21
	vpxorq 0(%rax), %xmm0, %xmm0
	vpxorq %xmm3, %xmm0, %xmm25
	vpxorq %xmm1, %xmm25, %xmm25
	vpternlogq $0x96, %xmm2, %xmm4, %xmm25
	vpxorq %xmm9, %xmm6, %xmm26
	vpxorq %xmm7, %xmm26, %xmm26
	vpternlogq $0x96, %xmm8, %xmm5, %xmm26
	vpxorq %xmm10, %xmm12, %xmm27
	vpxorq %xmm13, %xmm27, %xmm27
	vpternlogq $0x96, %xmm14, %xmm11, %xmm27
	vpxorq %xmm16, %xmm18, %xmm28
	vpxorq %xmm19, %xmm28, %xmm28
	vpternlogq $0x96, %xmm15, %xmm17, %xmm28
	vpxorq %xmm22, %xmm24, %xmm29
	vpxorq %xmm20, %xmm29, %xmm29
	vpternlogq $0x96, %xmm21, %xmm23, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $44, %xmm9, %xmm9
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $43, %xmm13, %xmm13
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $21, %xmm17, %xmm17
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $14, %xmm21, %xmm21
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm9, %xmm31
	vpternlogq $0xD2, %xmm13, %xmm9, %xmm0
	vpternlogq $0xD2, %xmm17, %xmm13, %xmm9
	vpternlogq $0xD2, %xmm21, %xmm17, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm17
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm21
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $28, %xmm18, %xmm18
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $20, %xmm22, %xmm22
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $3, %xmm1, %xmm1
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $45, %xmm5, %xmm5
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $61, %xmm14, %xmm14
	vmovdqa64 %xmm18, %xmm30
	vmovdqa64 %xmm22, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm22, %xmm18
	vpternlogq $0xD2, %xmm5, %xmm1, %xmm22
	vpternlogq $0xD2, %xmm14, %xmm5, %xmm1
	vpternlogq $0xD2, %xmm30, %xmm14, %xmm5
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm14
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $1, %xmm6, %xmm6
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $6, %xmm10, %xmm10
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $25, %xmm19, %xmm19
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $8, %xmm23, %xmm23
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $18, %xmm2, %xmm2
	vmovdqa64 %xmm6, %xmm30
	vmovdqa64 %xmm10, %xmm31
	vpternlogq $0xD2, %xmm19, %xmm10, %xmm6
	vpternlogq $0xD2, %xmm23, %xmm19, %xmm10
	vpternlogq $0xD2, %xmm2, %xmm23, %xmm19
	vpternlogq $0xD2, %xmm30, %xmm2, %xmm23
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm2
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $27, %xmm24, %xmm24
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $36, %xmm3, %xmm3
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $10, %xmm7, %xmm7
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $15, %xmm11, %xmm11
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $56, %xmm15, %xmm15
	vmovdqa64 %xmm24, %xmm30
	vmovdqa64 %xmm3, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm3, %xmm24
	vpternlogq $0xD2, %xmm11, %xmm7, %xmm3
	vpternlogq $0xD2, %xmm15, %xmm11, %xmm7
	vpternlogq $0xD2, %xmm30, %xmm15, %xmm11
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm15
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $62, %xmm12, %xmm12
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $55, %xmm16, %xmm16
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $39, %xmm20, %xmm20
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $41, %xmm4, %xmm4
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $2, %xmm8, %xmm8
	vmovdqa64 %xmm12, %xmm30
	vmovdqa64 %xmm16, %xmm31
	vpternlogq $0xD2, %xmm20, %xmm16, %xmm12
	vpternlogq $0xD2, %xmm4, %xmm20, %xmm16
	vpternlogq $0xD2, %xmm8, %xmm4, %xmm20
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm4
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm8
	vpxorq 16(%rax), %xmm0, %xmm0
	vpxorq %xmm18, %xmm0, %xmm25
	vpxorq %xmm6, %xmm25, %xmm25
	vpternlogq $0x96, %xmm12, %xmm24, %xmm25
	vpxorq %xmm22, %xmm9, %xmm26
	vpxorq %xmm10, %xmm26, %xmm26
	vpternlogq $0x96, %xmm16, %xmm3, %xmm26
	vpxorq %xmm1, %xmm13, %xmm27
	vpxorq %xmm19, %xmm27, %xmm27
	vpternlogq $0x96, %xmm20, %xmm7, %xmm27
	vpxorq %xmm5, %xmm17, %xmm28
	vpxorq %xmm23, %xmm28, %xmm28
	vpternlogq $0x96, %xmm4, %xmm11, %xmm28
	vpxorq %xmm14, %xmm21, %xmm29
	vpxorq %xmm2, %xmm29, %xmm29
	vpternlogq $0x96, %xmm8, %xmm15, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $44, %xmm22, %xmm22
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $43, %xmm19, %xmm19
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $21, %xmm11, %xmm11
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $14, %xmm8, %xmm8
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm22, %xmm31
	vpternlogq $0xD2, %xmm19, %xmm22, %xmm0
	vpternlogq $0xD2, %xmm11, %xmm19, %xmm22
	vpternlogq $0xD2, %xmm8, %xmm11, %xmm19
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm11
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm8
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $28, %xmm17, %xmm17
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $20, %xmm14, %xmm14
	vpxorq %xmm29, %xmm6, %xmm6
	vprolq $3, %xmm6, %xmm6
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $45, %xmm3, %xmm3
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $61, %xmm20, %xmm20
	vmovdqa64 %xmm17, %xmm30
	vmovdqa64 %xmm14, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm14, %xmm17
	vpternlogq $0xD2, %xmm3, %xmm6, %xmm14
	vpternlogq $0xD2, %xmm20, %xmm3, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm20, %xmm3
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm20
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $1, %xmm9, %xmm9
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $6, %xmm1, %xmm1
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $25, %xmm23, %xmm23
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $8, %xmm15, %xmm15
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $18, %xmm12, %xmm12
	vmovdqa64 %xmm9, %xmm30
	vmovdqa64 %xmm1, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm1, %xmm9
	vpternlogq $0xD2, %xmm15, %xmm23, %xmm1
	vpternlogq $0xD2, %xmm12, %xmm15, %xmm23
	vpternlogq $0xD2, %xmm30, %xmm12, %xmm15
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $27, %xmm21, %xmm21
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $36, %xmm18, %xmm18
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $10, %xmm10, %xmm10
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $15, %xmm7, %xmm7
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $56, %xmm4, %xmm4
	vmovdqa64 %xmm21, %xmm30
	vmovdqa64 %xmm18, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm18, %xmm21
	vpternlogq $0xD2, %xmm7, %xmm10, %xmm18
	vpternlogq $0xD2, %xmm4, %xmm7, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm4, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm4
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $62, %xmm13, %xmm13
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $55, %xmm5, %xmm5
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $39, %xmm2, %xmm2
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $41, %xmm24, %xmm24
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $2, %xmm16, %xmm16
	vmovdqa64 %xmm13, %xmm30
	vmovdqa64 %xmm5, %xmm31
	vpternlogq $0xD2, %xmm2, %xmm5, %xmm13
	vpternlogq $0xD2, %xmm24, %xmm2, %xmm5
	vpternlogq $0xD2, %xmm16, %xmm24, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm24
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm16
	vpxorq 32(%rax), %xmm0, %xmm0
	vpxorq %xmm17, %xmm0, %xmm25
	vpxorq %xmm9, %xmm25, %xmm25
	vpternlogq $0x96, %xmm13, %xmm21, %xmm25
	vpxorq %xmm14, %xmm22, %xmm26
	vpxorq %xmm1, %xmm26, %xmm26
	vpternlogq $0x96, %xmm5, %xmm18, %xmm26
	vpxorq %xmm6, %xmm19, %xmm27
	vpxorq %xmm23, %xmm27, %xmm27
	vpternlogq $0x96, %xmm2, %xmm10, %xmm27
	vpxorq %xmm3, %xmm11, %xmm28
	vpxorq %xmm15, %xmm28, %xmm28
	vpternlogq $0x96, %xmm24, %xmm7, %xmm28
	vpxorq %xmm20, %xmm8, %xmm29
	vpxorq %xmm12, %xmm29, %xmm29
	vpternlogq $0x96, %xmm16, %xmm4, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $44, %xmm14, %xmm14
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $43, %xmm23, %xmm23
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $21, %xmm7, %xmm7
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $14, %xmm16, %xmm16
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm14, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm14, %xmm0
	vpternlogq $0xD2, %xmm7, %xmm23, %xmm14
	vpternlogq $0xD2, %xmm16, %xmm7, %xmm23
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm16
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $28, %xmm11, %xmm11
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $20, %xmm20, %xmm20
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $3, %xmm9, %xmm9
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $45, %xmm18, %xmm18
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $61, %xmm2, %xmm2
	vmovdqa64 %xmm11, %xmm30
	vmovdqa64 %xmm20, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm20, %xmm11
	vpternlogq $0xD2, %xmm18, %xmm9, %xmm20
	vpternlogq $0xD2, %xmm2, %xmm18, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm2, %xmm18
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm2
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $1, %xmm22, %xmm22
	vpxorq %xmm26, %xmm6, %xmm6
	vprolq $6, %xmm6, %xmm6
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $25, %xmm15, %xmm15
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $8, %xmm4, %xmm4
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $18, %xmm13, %xmm13
	vmovdqa64 %xmm22, %xmm30
	vmovdqa64 %xmm6, %xmm31
	vpternlogq $0xD2, %xmm15, %xmm6, %xmm22
	vpternlogq $0xD2, %xmm4, %xmm15, %xmm6
	vpternlogq $0xD2, %xmm13, %xmm4, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm13, %xmm4
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm13
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $27, %xmm8, %xmm8
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $36, %xmm17, %xmm17
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $10, %xmm1, %xmm1
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $15, %xmm10, %xmm10
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $56, %xmm24, %xmm24
	vmovdqa64 %xmm8, %xmm30
	vmovdqa64 %xmm17, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm17, %xmm8
	vpternlogq $0xD2, %xmm10, %xmm1, %xmm17
	vpternlogq $0xD2, %xmm24, %xmm10, %xmm1
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm10
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm24
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $62, %xmm19, %xmm19
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $55, %xmm3, %xmm3
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $39, %xmm12, %xmm12
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $41, %xmm21, %xmm21
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $2, %xmm5, %xmm5
	vmovdqa64 %xmm19, %xmm30
	vmovdqa64 %xmm3, %xmm31
	vpternlogq $0xD2, %xmm12, %xmm3, %xmm19
	vpternlogq $0xD2, %xmm21, %xmm12, %xmm3
	vpternlogq $0xD2, %xmm5, %xmm21, %xmm12
	vpternlogq $0xD2, %xmm30, %xmm5, %xmm21
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm5
	vpxorq 48(%rax), %xmm0, %xmm0
	vpxorq %xmm11, %xmm0, %xmm25
	vpxorq %xmm22, %xmm25, %xmm25
	vpternlogq $0x96, %xmm19, %xmm8, %xmm25
	vpxorq %xmm20, %xmm14, %xmm26
	vpxorq %xmm6, %xmm26, %xmm26
	vpternlogq $0x96, %xmm3, %xmm17, %xmm26
	vpxorq %xmm9, %xmm23, %xmm27
	vpxorq %xmm15, %xmm27, %xmm27
	vpternlogq $0x96, %xmm12, %xmm1, %xmm27
	vpxorq %xmm18, %xmm7, %xmm28
	vpxorq %xmm4, %xmm28, %xmm28
	vpternlogq $0x96, %xmm21, %xmm10, %xmm28
	vpxorq %xmm2, %xmm16, %xmm29
	vpxorq %xmm13, %xmm29, %xmm29
	vpternlogq $0x96, %xmm5, %xmm24, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $44, %xmm20, %xmm20
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $43, %xmm15, %xmm15
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $21, %xmm10, %xmm10
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $14, %xmm5, %xmm5
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm20, %xmm31
	vpternlogq $0xD2, %xmm15, %xmm20, %xmm0
	vpternlogq $0xD2, %xmm10, %xmm15, %xmm20
	vpternlogq $0xD2, %xmm5, %xmm10, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm5, %xmm10
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm5
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $28, %xmm7, %xmm7
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $20, %xmm2, %xmm2
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $3, %xmm22, %xmm22
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $45, %xmm17, %xmm17
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $61, %xmm12, %xmm12
	vmovdqa64 %xmm7, %xmm30
	vmovdqa64 %xmm2, %xmm31
	vpternlogq $0xD2, %xmm22, %xmm2, %xmm7
	vpternlogq $0xD2, %xmm17, %xmm22, %xmm2
	vpternlogq $0xD2, %xmm12, %xmm17, %xmm22
	vpternlogq $0xD2, %xmm30, %xmm12, %xmm17
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $1, %xmm14, %xmm14
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $6, %xmm9, %xmm9
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $25, %xmm4, %xmm4
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $8, %xmm24, %xmm24
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $18, %xmm19, %xmm19
	vmovdqa64 %xmm14, %xmm30
	vmovdqa64 %xmm9, %xmm31
	vpternlogq $0xD2, %xmm4, %xmm9, %xmm14
	vpternlogq $0xD2, %xmm24, %xmm4, %xmm9
	vpternlogq $0xD2, %xmm19, %xmm24, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm19, %xmm24
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm19
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $27, %xmm16, %xmm16
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $36, %xmm11, %xmm11
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $10, %xmm6, %xmm6
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $15, %xmm1, %xmm1
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $56, %xmm21, %xmm21
	vmovdqa64 %xmm16, %xmm30
	vmovdqa64 %xmm11, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm11, %xmm16
	vpternlogq $0xD2, %xmm1, %xmm6, %xmm11
	vpternlogq $0xD2, %xmm21, %xmm1, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm21
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $62, %xmm23, %xmm23
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $55, %xmm18, %xmm18
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $39, %xmm13, %xmm13
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $41, %xmm8, %xmm8
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $2, %xmm3, %xmm3
	vmovdqa64 %xmm23, %xmm30
	vmovdqa64 %xmm18, %xmm31
	vpternlogq $0xD2, %xmm13, %xmm18, %xmm23
	vpternlogq $0xD2, %xmm8, %xmm13, %xmm18
	vpternlogq $0xD2, %xmm3, %xmm8, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm8
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm3
	vpxorq 64(%rax), %xmm0, %xmm0
	vpxorq %xmm7, %xmm0, %xmm25
	vpxorq %xmm14, %xmm25, %xmm25
	vpternlogq $0x96, %xmm23, %xmm16, %xmm25
	vpxorq %xmm2, %xmm20, %xmm26
	vpxorq %xmm9, %xmm26, %xmm26
	vpternlogq $0x96, %xmm18, %xmm11, %xmm26
	vpxorq %xmm22, %xmm15, %xmm27
	vpxorq %xmm4, %xmm27, %xmm27
	vpternlogq $0x96, %xmm13, %xmm6, %xmm27
	vpxorq %xmm17, %xmm10, %xmm28
	vpxorq %xmm24, %xmm28, %xmm28
	vpternlogq $0x96, %xmm8, %xmm1, %xmm28
	vpxorq %xmm12, %xmm5, %xmm29
	vpxorq %xmm19, %xmm29, %xmm29
	vpternlogq $0x96, %xmm3, %xmm21, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $44, %xmm2, %xmm2
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $43, %xmm4, %xmm4
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $21, %xmm1, %xmm1
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $14, %xmm3, %xmm3
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm2, %xmm31
	vpternlogq $0xD2, %xmm4, %xmm2, %xmm0
	vpternlogq $0xD2, %xmm1, %xmm4, %xmm2
	vpternlogq $0xD2, %xmm3, %xmm1, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm3
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $28, %xmm10, %xmm10
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $20, %xmm12, %xmm12
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $3, %xmm14, %xmm14
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $45, %xmm11, %xmm11
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $61, %xmm13, %xmm13
	vmovdqa64 %xmm10, %xmm30
	vmovdqa64 %xmm12, %xmm31
	vpternlogq $0xD2, %xmm14, %xmm12, %xmm10
	vpternlogq $0xD2, %xmm11, %xmm14, %xmm12
	vpternlogq $0xD2, %xmm13, %xmm11, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm13, %xmm11
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm13
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $1, %xmm20, %xmm20
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $6, %xmm22, %xmm22
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $25, %xmm24, %xmm24
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $8, %xmm21, %xmm21
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $18, %xmm23, %xmm23
	vmovdqa64 %xmm20, %xmm30
	vmovdqa64 %xmm22, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm22, %xmm20
	vpternlogq $0xD2, %xmm21, %xmm24, %xmm22
	vpternlogq $0xD2, %xmm23, %xmm21, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm21
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm23
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $27, %xmm5, %xmm5
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $36, %xmm7, %xmm7
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $10, %xmm9, %xmm9
	vpxorq %xmm26, %xmm6, %xmm6
	vprolq $15, %xmm6, %xmm6
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $56, %xmm8, %xmm8
	vmovdqa64 %xmm5, %xmm30
	vmovdqa64 %xmm7, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm7, %xmm5
	vpternlogq $0xD2, %xmm6, %xmm9, %xmm7
	vpternlogq $0xD2, %xmm8, %xmm6, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm8
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $62, %xmm15, %xmm15
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $55, %xmm17, %xmm17
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $39, %xmm19, %xmm19
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $41, %xmm16, %xmm16
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $2, %xmm18, %xmm18
	vmovdqa64 %xmm15, %xmm30
	vmovdqa64 %xmm17, %xmm31
	vpternlogq $0xD2, %xmm19, %xmm17, %xmm15
	vpternlogq $0xD2, %xmm16, %xmm19, %xmm17
	vpternlogq $0xD2, %xmm18, %xmm16, %xmm19
	vpternlogq $0xD2, %xmm30, %xmm18, %xmm16
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpxorq 80(%rax), %xmm0, %xmm0
	vpxorq %xmm10, %xmm0, %xmm25
	vpxorq %xmm20, %xmm25, %xmm25
	vpternlogq $0x96, %xmm15, %xmm5, %xmm25
	vpxorq %xmm12, %xmm2, %xmm26
	vpxorq %xmm22, %xmm26, %xmm26
	vpternlogq $0x96, %xmm17, %xmm7, %xmm26
	vpxorq %xmm14, %xmm4, %xmm27
	vpxorq %xmm24, %xmm27, %xmm27
	vpternlogq $0x96, %xmm19, %xmm9, %xmm27
	vpxorq %xmm11, %xmm1, %xmm28
	vpxorq %xmm21, %xmm28, %xmm28
	vpternlogq $0x96, %xmm16, %xmm6, %xmm28
	vpxorq %xmm13, %xmm3, %xmm29
	vpxorq %xmm23, %xmm29, %xmm29
	vpternlogq $0x96, %xmm18, %xmm8, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $44, %xmm12, %xmm12
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $43, %xmm24, %xmm24
	vpxorq %xmm27, %xmm6, %xmm6
	vprolq $21, %xmm6, %xmm6
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $14, %xmm18, %xmm18
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm12, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm12, %xmm0
	vpternlogq $0xD2, %xmm6, %xmm24, %xmm12
	vpternlogq $0xD2, %xmm18, %xmm6, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm18, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $28, %xmm1, %xmm1
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $20, %xmm13, %xmm13
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $3, %xmm20, %xmm20
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $45, %xmm7, %xmm7
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $61, %xmm19, %xmm19
	vmovdqa64 %xmm1, %xmm30
	vmovdqa64 %xmm13, %xmm31
	vpternlogq $0xD2, %xmm20, %xmm13, %xmm1
	vpternlogq $0xD2, %xmm7, %xmm20, %xmm13
	vpternlogq $0xD2, %xmm19, %xmm7, %xmm20
	vpternlogq $0xD2, %xmm30, %xmm19, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm19
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $1, %xmm2, %xmm2
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $6, %xmm14, %xmm14
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $25, %xmm21, %xmm21
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $8, %xmm8, %xmm8
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $18, %xmm15, %xmm15
	vmovdqa64 %xmm2, %xmm30
	vmovdqa64 %xmm14, %xmm31
	vpternlogq $0xD2, %xmm21, %xmm14, %xmm2
	vpternlogq $0xD2, %xmm8, %xmm21, %xmm14
	vpternlogq $0xD2, %xmm15, %xmm8, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm15, %xmm8
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm15
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $27, %xmm3, %xmm3
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $36, %xmm10, %xmm10
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $10, %xmm22, %xmm22
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $15, %xmm9, %xmm9
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $56, %xmm16, %xmm16
	vmovdqa64 %xmm3, %xmm30
	vmovdqa64 %xmm10, %xmm31
	vpternlogq $0xD2, %xmm22, %xmm10, %xmm3
	vpternlogq $0xD2, %xmm9, %xmm22, %xmm10
	vpternlogq $0xD2, %xmm16, %xmm9, %xmm22
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm9
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm16
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $62, %xmm4, %xmm4
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $55, %xmm11, %xmm11
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $39, %xmm23, %xmm23
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $41, %xmm5, %xmm5
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $2, %xmm17, %xmm17
	vmovdqa64 %xmm4, %xmm30
	vmovdqa64 %xmm11, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm11, %xmm4
	vpternlogq $0xD2, %xmm5, %xmm23, %xmm11
	vpternlogq $0xD2, %xmm17, %xmm5, %xmm23
	vpternlogq $0xD2, %xmm30, %xmm17, %xmm5
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm17
	vpxorq 96(%rax), %xmm0, %xmm0
	vpxorq %xmm1, %xmm0, %xmm25
	vpxorq %xmm2, %xmm25, %xmm25
	vpternlogq $0x96, %xmm4, %xmm3, %xmm25
	vpxorq %xmm13, %xmm12, %xmm26
	vpxorq %xmm14, %xmm26, %xmm26
	vpternlogq $0x96, %xmm11, %xmm10, %xmm26
	vpxorq %xmm20, %xmm24, %xmm27
	vpxorq %xmm21, %xmm27, %xmm27
	vpternlogq $0x96, %xmm23, %xmm22, %xmm27
	vpxorq %xmm7, %xmm6, %xmm28
	vpxorq %xmm8, %xmm28, %xmm28
	vpternlogq $0x96, %xmm5, %xmm9, %xmm28
	vpxorq %xmm19, %xmm18, %xmm29
	vpxorq %xmm15, %xmm29, %xmm29
	vpternlogq $0x96, %xmm17, %xmm16, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $44, %xmm13, %xmm13
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $43, %xmm21, %xmm21
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $21, %xmm9, %xmm9
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $14, %xmm17, %xmm17
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm13, %xmm31
	vpternlogq $0xD2, %xmm21, %xmm13, %xmm0
	vpternlogq $0xD2, %xmm9, %xmm21, %xmm13
	vpternlogq $0xD2, %xmm17, %xmm9, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm17, %xmm9
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm17
	vpxorq %xmm27, %xmm6, %xmm6
	vprolq $28, %xmm6, %xmm6
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $20, %xmm19, %xmm19
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $3, %xmm2, %xmm2
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $45, %xmm10, %xmm10
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $61, %xmm23, %xmm23
	vmovdqa64 %xmm6, %xmm30
	vmovdqa64 %xmm19, %xmm31
	vpternlogq $0xD2, %xmm2, %xmm19, %xmm6
	vpternlogq $0xD2, %xmm10, %xmm2, %xmm19
	vpternlogq $0xD2, %xmm23, %xmm10, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm10
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm23
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $1, %xmm12, %xmm12
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $6, %xmm20, %xmm20
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $25, %xmm8, %xmm8
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $8, %xmm16, %xmm16
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $18, %xmm4, %xmm4
	vmovdqa64 %xmm12, %xmm30
	vmovdqa64 %xmm20, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm20, %xmm12
	vpternlogq $0xD2, %xmm16, %xmm8, %xmm20
	vpternlogq $0xD2, %xmm4, %xmm16, %xmm8
	vpternlogq $0xD2, %xmm30, %xmm4, %xmm16
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm4
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $27, %xmm18, %xmm18
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $36, %xmm1, %xmm1
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $10, %xmm14, %xmm14
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $15, %xmm22, %xmm22
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $56, %xmm5, %xmm5
	vmovdqa64 %xmm18, %xmm30
	vmovdqa64 %xmm1, %xmm31
	vpternlogq $0xD2, %xmm14, %xmm1, %xmm18
	vpternlogq $0xD2, %xmm22, %xmm14, %xmm1
	vpternlogq $0xD2, %xmm5, %xmm22, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm5, %xmm22
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm5
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $62, %xmm24, %xmm24
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $55, %xmm7, %xmm7
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $39, %xmm15, %xmm15
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $41, %xmm3, %xmm3
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $2, %xmm11, %xmm11
	vmovdqa64 %xmm24, %xmm30
	vmovdqa64 %xmm7, %xmm31
	vpternlogq $0xD2, %xmm15, %xmm7, %xmm24
	vpternlogq $0xD2, %xmm3, %xmm15, %xmm7
	vpternlogq $0xD2, %xmm11, %xmm3, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm11, %xmm3
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm11
	vpxorq 112(%rax), %xmm0, %xmm0
	vpxorq %xmm6, %xmm0, %xmm25
	vpxorq %xmm12, %xmm25, %xmm25
	vpternlogq $0x96, %xmm24, %xmm18, %xmm25
	vpxorq %xmm19, %xmm13, %xmm26
	vpxorq %xmm20, %xmm26, %xmm26
	vpternlogq $0x96, %xmm7, %xmm1, %xmm26
	vpxorq %xmm2, %xmm21, %xmm27
	vpxorq %xmm8, %xmm27, %xmm27
	vpternlogq $0x96, %xmm15, %xmm14, %xmm27
	vpxorq %xmm10, %xmm9, %xmm28
	vpxorq %xmm16, %xmm28, %xmm28
	vpternlogq $0x96, %xmm3, %xmm22, %xmm28
	vpxorq %xmm23, %xmm17, %xmm29
	vpxorq %xmm4, %xmm29, %xmm29
	vpternlogq $0x96, %xmm11, %xmm5, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $44, %xmm19, %xmm19
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $43, %xmm8, %xmm8
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $21, %xmm22, %xmm22
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $14, %xmm11, %xmm11
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm19, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm19, %xmm0
	vpternlogq $0xD2, %xmm22, %xmm8, %xmm19
	vpternlogq $0xD2, %xmm11, %xmm22, %xmm8
	vpternlogq $0xD2, %xmm30, %xmm11, %xmm22
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm11
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $28, %xmm9, %xmm9
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $20, %xmm23, %xmm23
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $3, %xmm12, %xmm12
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $45, %xmm1, %xmm1
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $61, %xmm15, %xmm15
	vmovdqa64 %xmm9, %xmm30
	vmovdqa64 %xmm23, %xmm31
	vpternlogq $0xD2, %xmm12, %xmm23, %xmm9
	vpternlogq $0xD2, %xmm1, %xmm12, %xmm23
	vpternlogq $0xD2, %xmm15, %xmm1, %xmm12
	vpternlogq $0xD2, %xmm30, %xmm15, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm15
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $1, %xmm13, %xmm13
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $6, %xmm2, %xmm2
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $25, %xmm16, %xmm16
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $8, %xmm5, %xmm5
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $18, %xmm24, %xmm24
	vmovdqa64 %xmm13, %xmm30
	vmovdqa64 %xmm2, %xmm31
	vpternlogq $0xD2, %xmm16, %xmm2, %xmm13
	vpternlogq $0xD2, %xmm5, %xmm16, %xmm2
	vpternlogq $0xD2, %xmm24, %xmm5, %xmm16
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm5
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm24
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $27, %xmm17, %xmm17
	vpxorq %xmm29, %xmm6, %xmm6
	vprolq $36, %xmm6, %xmm6
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $10, %xmm20, %xmm20
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $15, %xmm14, %xmm14
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $56, %xmm3, %xmm3
	vmovdqa64 %xmm17, %xmm30
	vmovdqa64 %xmm6, %xmm31
	vpternlogq $0xD2, %xmm20, %xmm6, %xmm17
	vpternlogq $0xD2, %xmm14, %xmm20, %xmm6
	vpternlogq $0xD2, %xmm3, %xmm14, %xmm20
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm14
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm3
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $62, %xmm21, %xmm21
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $55, %xmm10, %xmm10
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $39, %xmm4, %xmm4
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $41, %xmm18, %xmm18
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $2, %xmm7, %xmm7
	vmovdqa64 %xmm21, %xmm30
	vmovdqa64 %xmm10, %xmm31
	vpternlogq $0xD2, %xmm4, %xmm10, %xmm21
	vpternlogq $0xD2, %xmm18, %xmm4, %xmm10
	vpternlogq $0xD2, %xmm7, %xmm18, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm7, %xmm18
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm7
	vpxorq 128(%rax), %xmm0, %xmm0
	vpxorq %xmm9, %xmm0, %xmm25
	vpxorq %xmm13, %xmm25, %xmm25
	vpternlogq $0x96, %xmm21, %xmm17, %xmm25
	vpxorq %xmm23, %xmm19, %xmm26
	vpxorq %xmm2, %xmm26, %xmm26
	vpternlogq $0x96, %xmm10, %xmm6, %xmm26
	vpxorq %xmm12, %xmm8, %xmm27
	vpxorq %xmm16, %xmm27, %xmm27
	vpternlogq $0x96, %xmm4, %xmm20, %xmm27
	vpxorq %xmm1, %xmm22, %xmm28
	vpxorq %xmm5, %xmm28, %xmm28
	vpternlogq $0x96, %xmm18, %xmm14, %xmm28
	vpxorq %xmm15, %xmm11, %xmm29
	vpxorq %xmm24, %xmm29, %xmm29
	vpternlogq $0x96, %xmm7, %xmm3, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $44, %xmm23, %xmm23
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $43, %xmm16, %xmm16
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $21, %xmm14, %xmm14
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $14, %xmm7, %xmm7
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm23, %xmm31
	vpternlogq $0xD2, %xmm16, %xmm23, %xmm0
	vpternlogq $0xD2, %xmm14, %xmm16, %xmm23
	vpternlogq $0xD2, %xmm7, %xmm14, %xmm16
	vpternlogq $0xD2, %xmm30, %xmm7, %xmm14
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm7
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $28, %xmm22, %xmm22
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $20, %xmm15, %xmm15
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $3, %xmm13, %xmm13
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $45, %xmm6, %xmm6
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $61, %xmm4, %xmm4
	vmovdqa64 %xmm22, %xmm30
	vmovdqa64 %xmm15, %xmm31
	vpternlogq $0xD2, %xmm13, %xmm15, %xmm22
	vpternlogq $0xD2, %xmm6, %xmm13, %xmm15
	vpternlogq $0xD2, %xmm4, %xmm6, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm4, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm4
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $1, %xmm19, %xmm19
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $6, %xmm12, %xmm12
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $25, %xmm5, %xmm5
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $8, %xmm3, %xmm3
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $18, %xmm21, %xmm21
	vmovdqa64 %xmm19, %xmm30
	vmovdqa64 %xmm12, %xmm31
	vpternlogq $0xD2, %xmm5, %xmm12, %xmm19
	vpternlogq $0xD2, %xmm3, %xmm5, %xmm12
	vpternlogq $0xD2, %xmm21, %xmm3, %xmm5
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm3
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm21
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $27, %xmm11, %xmm11
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $36, %xmm9, %xmm9
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $10, %xmm2, %xmm2
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $15, %xmm20, %xmm20
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $56, %xmm18, %xmm18
	vmovdqa64 %xmm11, %xmm30
	vmovdqa64 %xmm9, %xmm31
	vpternlogq $0xD2, %xmm2, %xmm9, %xmm11
	vpternlogq $0xD2, %xmm20, %xmm2, %xmm9
	vpternlogq $0xD2, %xmm18, %xmm20, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm18, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $62, %xmm8, %xmm8
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $55, %xmm1, %xmm1
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $39, %xmm24, %xmm24
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $41, %xmm17, %xmm17
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $2, %xmm10, %xmm10
	vmovdqa64 %xmm8, %xmm30
	vmovdqa64 %xmm1, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm1, %xmm8
	vpternlogq $0xD2, %xmm17, %xmm24, %xmm1
	vpternlogq $0xD2, %xmm10, %xmm17, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm10, %xmm17
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm10
	vpxorq 144(%rax), %xmm0, %xmm0
	vpxorq %xmm22, %xmm0, %xmm25
	vpxorq %xmm19, %xmm25, %xmm25
	vpternlogq $0x96, %xmm8, %xmm11, %xmm25
	vpxorq %xmm15, %xmm23, %xmm26
	vpxorq %xmm12, %xmm26, %xmm26
	vpternlogq $0x96, %xmm1, %xmm9, %xmm26
	vpxorq %xmm13, %xmm16, %xmm27
	vpxorq %xmm5, %xmm27, %xmm27
	vpternlogq $0x96, %xmm24, %xmm2, %xmm27
	vpxorq %xmm6, %xmm14, %xmm28
	vpxorq %xmm3, %xmm28, %xmm28
	vpternlogq $0x96, %xmm17, %xmm20, %xmm28
	vpxorq %xmm4, %xmm7, %xmm29
	vpxorq %xmm21, %xmm29, %xmm29
	vpternlogq $0x96, %xmm10, %xmm18, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $44, %xmm15, %xmm15
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $43, %xmm5, %xmm5
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $21, %xmm20, %xmm20
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $14, %xmm10, %xmm10
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm15, %xmm31
	vpternlogq $0xD2, %xmm5, %xmm15, %xmm0
	vpternlogq $0xD2, %xmm20, %xmm5, %xmm15
	vpternlogq $0xD2, %xmm10, %xmm20, %xmm5
	vpternlogq $0xD2, %xmm30, %xmm10, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm10
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $28, %xmm14, %xmm14
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $20, %xmm4, %xmm4
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $3, %xmm19, %xmm19
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $45, %xmm9, %xmm9
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $61, %xmm24, %xmm24
	vmovdqa64 %xmm14, %xmm30
	vmovdqa64 %xmm4, %xmm31
	vpternlogq $0xD2, %xmm19, %xmm4, %xmm14
	vpternlogq $0xD2, %xmm9, %xmm19, %xmm4
	vpternlogq $0xD2, %xmm24, %xmm9, %xmm19
	vpternlogq $0xD2, %xmm30, %xmm24, %xmm9
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm24
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $1, %xmm23, %xmm23
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $6, %xmm13, %xmm13
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $25, %xmm3, %xmm3
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $8, %xmm18, %xmm18
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $18, %xmm8, %xmm8
	vmovdqa64 %xmm23, %xmm30
	vmovdqa64 %xmm13, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm13, %xmm23
	vpternlogq $0xD2, %xmm18, %xmm3, %xmm13
	vpternlogq $0xD2, %xmm8, %xmm18, %xmm3
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm18
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm8
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $27, %xmm7, %xmm7
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $36, %xmm22, %xmm22
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $10, %xmm12, %xmm12
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $15, %xmm2, %xmm2
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $56, %xmm17, %xmm17
	vmovdqa64 %xmm7, %xmm30
	vmovdqa64 %xmm22, %xmm31
	vpternlogq $0xD2, %xmm12, %xmm22, %xmm7
	vpternlogq $0xD2, %xmm2, %xmm12, %xmm22
	vpternlogq $0xD2, %xmm17, %xmm2, %xmm12
	vpternlogq $0xD2, %xmm30, %xmm17, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm17
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $62, %xmm16, %xmm16
	vpxorq %xmm27, %xmm6, %xmm6
	vprolq $55, %xmm6, %xmm6
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $39, %xmm21, %xmm21
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $41, %xmm11, %xmm11
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $2, %xmm1, %xmm1
	vmovdqa64 %xmm16, %xmm30
	vmovdqa64 %xmm6, %xmm31
	vpternlogq $0xD2, %xmm21, %xmm6, %xmm16
	vpternlogq $0xD2, %xmm11, %xmm21, %xmm6
	vpternlogq $0xD2, %xmm1, %xmm11, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm1, %xmm11
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm1
	vpxorq 160(%rax), %xmm0, %xmm0
	vpxorq %xmm14, %xmm0, %xmm25
	vpxorq %xmm23, %xmm25, %xmm25
	vpternlogq $0x96, %xmm16, %xmm7, %xmm25
	vpxorq %xmm4, %xmm15, %xmm26
	vpxorq %xmm13, %xmm26, %xmm26
	vpternlogq $0x96, %xmm6, %xmm22, %xmm26
	vpxorq %xmm19, %xmm5, %xmm27
	vpxorq %xmm3, %xmm27, %xmm27
	vpternlogq $0x96, %xmm21, %xmm12, %xmm27
	vpxorq %xmm9, %xmm20, %xmm28
	vpxorq %xmm18, %xmm28, %xmm28
	vpternlogq $0x96, %xmm11, %xmm2, %xmm28
	vpxorq %xmm24, %xmm10, %xmm29
	vpxorq %xmm8, %xmm29, %xmm29
	vpternlogq $0x96, %xmm1, %xmm17, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $44, %xmm4, %xmm4
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $43, %xmm3, %xmm3
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $21, %xmm2, %xmm2
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $14, %xmm1, %xmm1
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm4, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm4, %xmm0
	vpternlogq $0xD2, %xmm2, %xmm3, %xmm4
	vpternlogq $0xD2, %xmm1, %xmm2, %xmm3
	vpternlogq $0xD2, %xmm30, %xmm1, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm1
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $28, %xmm20, %xmm20
	vpxorq %xmm28, %xmm24, %xmm24
	vprolq $20, %xmm24, %xmm24
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $3, %xmm23, %xmm23
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $45, %xmm22, %xmm22
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $61, %xmm21, %xmm21
	vmovdqa64 %xmm20, %xmm30
	vmovdqa64 %xmm24, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm24, %xmm20
	vpternlogq $0xD2, %xmm22, %xmm23, %xmm24
	vpternlogq $0xD2, %xmm21, %xmm22, %xmm23
	vpternlogq $0xD2, %xmm30, %xmm21, %xmm22
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm21
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $1, %xmm15, %xmm15
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $6, %xmm19, %xmm19
	vpxorq %xmm27, %xmm18, %xmm18
	vprolq $25, %xmm18, %xmm18
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $8, %xmm17, %xmm17
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $18, %xmm16, %xmm16
	vmovdqa64 %xmm15, %xmm30
	vmovdqa64 %xmm19, %xmm31
	vpternlogq $0xD2, %xmm18, %xmm19, %xmm15
	vpternlogq $0xD2, %xmm17, %xmm18, %xmm19
	vpternlogq $0xD2, %xmm16, %xmm17, %xmm18
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm17
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm16
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $27, %xmm10, %xmm10
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $36, %xmm14, %xmm14
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $10, %xmm13, %xmm13
	vpxorq %xmm26, %xmm12, %xmm12
	vprolq $15, %xmm12, %xmm12
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $56, %xmm11, %xmm11
	vmovdqa64 %xmm10, %xmm30
	vmovdqa64 %xmm14, %xmm31
	vpternlogq $0xD2, %xmm13, %xmm14, %xmm10
	vpternlogq $0xD2, %xmm12, %xmm13, %xmm14
	vpternlogq $0xD2, %xmm11, %xmm12, %xmm13
	vpternlogq $0xD2, %xmm30, %xmm11, %xmm12
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm11
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $62, %xmm5, %xmm5
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $55, %xmm9, %xmm9
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $39, %xmm8, %xmm8
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $41, %xmm7, %xmm7
	vpxorq %xmm25, %xmm6, %xmm6
	vprolq $2, %xmm6, %xmm6
	vmovdqa64 %xmm5, %xmm30
	vmovdqa64 %xmm9, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm9, %xmm5
	vpternlogq $0xD2, %xmm7, %xmm8, %xmm9
	vpternlogq $0xD2, %xmm6, %xmm7, %xmm8
	vpternlogq $0xD2, %xmm30, %xmm6, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm6
	vpxorq 176(%rax), %xmm0, %xmm0
	vpxorq %xmm20, %xmm0, %xmm25
	vpxorq %xmm15, %xmm25, %xmm25
	vpternlogq $0x96, %xmm5, %xmm10, %xmm25
	vpxorq %xmm24, %xmm4, %xmm26
	vpxorq %xmm19, %xmm26, %xmm26
	vpternlogq $0x96, %xmm9, %xmm14, %xmm26
	vpxorq %xmm23, %xmm3, %xmm27
	vpxorq %xmm18, %xmm27, %xmm27
	vpternlogq $0x96, %xmm8, %xmm13, %xmm27
	vpxorq %xmm22, %xmm2, %xmm28
	vpxorq %xmm17, %xmm28, %xmm28
	vpternlogq $0x96, %xmm7, %xmm12, %xmm28
	vpxorq %xmm21, %xmm1, %xmm29
	vpxorq %xmm16, %xmm29, %xmm29
	vpternlogq $0x96, %xmm6, %xmm11, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $44, %xmm24, %xmm24
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $43, %xmm18, %xmm18
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $21, %xmm12, %xmm12
	vpxorq %xmm28, %xmm6, %xmm6
	vprolq $14, %xmm6, %xmm6
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm24, %xmm31
	vpternlogq $0xD2, %xmm18, %xmm24, %xmm0
	vpternlogq $0xD2, %xmm12, %xmm18, %xmm24
	vpternlogq $0xD2, %xmm6, %xmm12, %xmm18
	vpternlogq $0xD2, %xmm30, %xmm6, %xmm12
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm6
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $28, %xmm2, %xmm2
	vpxorq %xmm28, %xmm21, %xmm21
	vprolq $20, %xmm21, %xmm21
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $3, %xmm15, %xmm15
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $45, %xmm14, %xmm14
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $61, %xmm8, %xmm8
	vmovdqa64 %xmm2, %xmm30
	vmovdqa64 %xmm21, %xmm31
	vpternlogq $0xD2, %xmm15, %xmm21, %xmm2
	vpternlogq $0xD2, %xmm14, %xmm15, %xmm21
	vpternlogq $0xD2, %xmm8, %xmm14, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm8, %xmm14
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm8
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $1, %xmm4, %xmm4
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $6, %xmm23, %xmm23
	vpxorq %xmm27, %xmm17, %xmm17
	vprolq $25, %xmm17, %xmm17
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $8, %xmm11, %xmm11
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $18, %xmm5, %xmm5
	vmovdqa64 %xmm4, %xmm30
	vmovdqa64 %xmm23, %xmm31
	vpternlogq $0xD2, %xmm17, %xmm23, %xmm4
	vpternlogq $0xD2, %xmm11, %xmm17, %xmm23
	vpternlogq $0xD2, %xmm5, %xmm11, %xmm17
	vpternlogq $0xD2, %xmm30, %xmm5, %xmm11
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm5
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $27, %xmm1, %xmm1
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $36, %xmm20, %xmm20
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $10, %xmm19, %xmm19
	vpxorq %xmm26, %xmm13, %xmm13
	vprolq $15, %xmm13, %xmm13
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $56, %xmm7, %xmm7
	vmovdqa64 %xmm1, %xmm30
	vmovdqa64 %xmm20, %xmm31
	vpternlogq $0xD2, %xmm19, %xmm20, %xmm1
	vpternlogq $0xD2, %xmm13, %xmm19, %xmm20
	vpternlogq $0xD2, %xmm7, %xmm13, %xmm19
	vpternlogq $0xD2, %xmm30, %xmm7, %xmm13
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm7
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $62, %xmm3, %xmm3
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $55, %xmm22, %xmm22
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $39, %xmm16, %xmm16
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $41, %xmm10, %xmm10
	vpxorq %xmm25, %xmm9, %xmm9
	vprolq $2, %xmm9, %xmm9
	vmovdqa64 %xmm3, %xmm30
	vmovdqa64 %xmm22, %xmm31
	vpternlogq $0xD2, %xmm16, %xmm22, %xmm3
	vpternlogq $0xD2, %xmm10, %xmm16, %xmm22
	vpternlogq $0xD2, %xmm9, %xmm10, %xmm16
	vpternlogq $0xD2, %xmm30, %xmm9, %xmm10
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm9
	vpxorq 192(%rax), %xmm0, %xmm0
	vpxorq %xmm2, %xmm0, %xmm25
	vpxorq %xmm4, %xmm25, %xmm25
	vpternlogq $0x96, %xmm3, %xmm1, %xmm25
	vpxorq %xmm21, %xmm24, %xmm26
	vpxorq %xmm23, %xmm26, %xmm26
	vpternlogq $0x96, %xmm22, %xmm20, %xmm26
	vpxorq %xmm15, %xmm18, %xmm27
	vpxorq %xmm17, %xmm27, %xmm27
	vpternlogq $0x96, %xmm16, %xmm19, %xmm27
	vpxorq %xmm14, %xmm12, %xmm28
	vpxorq %xmm11, %xmm28, %xmm28
	vpternlogq $0x96, %xmm10, %xmm13, %xmm28
	vpxorq %xmm8, %xmm6, %xmm29
	vpxorq %xmm5, %xmm29, %xmm29
	vpternlogq $0x96, %xmm9, %xmm7, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $44, %xmm21, %xmm21
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $43, %xmm17, %xmm17
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $21, %xmm13, %xmm13
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $14, %xmm9, %xmm9
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm21, %xmm31
	vpternlogq $0xD2, %xmm17, %xmm21, %xmm0
	vpternlogq $0xD2, %xmm13, %xmm17, %xmm21
	vpternlogq $0xD2, %xmm9, %xmm13, %xmm17
	vpternlogq $0xD2, %xmm30, %xmm9, %xmm13
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm9
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $28, %xmm12, %xmm12
	vpxorq %xmm28, %xmm8, %xmm8
	vprolq $20, %xmm8, %xmm8
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $3, %xmm4, %xmm4
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $45, %xmm20, %xmm20
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $61, %xmm16, %xmm16
	vmovdqa64 %xmm12, %xmm30
	vmovdqa64 %xmm8, %xmm31
	vpternlogq $0xD2, %xmm4, %xmm8, %xmm12
	vpternlogq $0xD2, %xmm20, %xmm4, %xmm8
	vpternlogq $0xD2, %xmm16, %xmm20, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm16, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm16
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $1, %xmm24, %xmm24
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $6, %xmm15, %xmm15
	vpxorq %xmm27, %xmm11, %xmm11
	vprolq $25, %xmm11, %xmm11
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $8, %xmm7, %xmm7
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $18, %xmm3, %xmm3
	vmovdqa64 %xmm24, %xmm30
	vmovdqa64 %xmm15, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm15, %xmm24
	vpternlogq $0xD2, %xmm7, %xmm11, %xmm15
	vpternlogq $0xD2, %xmm3, %xmm7, %xmm11
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm7
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm3
	vpxorq %xmm28, %xmm6, %xmm6
	vprolq $27, %xmm6, %xmm6
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $36, %xmm2, %xmm2
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $10, %xmm23, %xmm23
	vpxorq %xmm26, %xmm19, %xmm19
	vprolq $15, %xmm19, %xmm19
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $56, %xmm10, %xmm10
	vmovdqa64 %xmm6, %xmm30
	vmovdqa64 %xmm2, %xmm31
	vpternlogq $0xD2, %xmm23, %xmm2, %xmm6
	vpternlogq $0xD2, %xmm19, %xmm23, %xmm2
	vpternlogq $0xD2, %xmm10, %xmm19, %xmm23
	vpternlogq $0xD2, %xmm30, %xmm10, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm10
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $62, %xmm18, %xmm18
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $55, %xmm14, %xmm14
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $39, %xmm5, %xmm5
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $41, %xmm1, %xmm1
	vpxorq %xmm25, %xmm22, %xmm22
	vprolq $2, %xmm22, %xmm22
	vmovdqa64 %xmm18, %xmm30
	vmovdqa64 %xmm14, %xmm31
	vpternlogq $0xD2, %xmm5, %xmm14, %xmm18
	vpternlogq $0xD2, %xmm1, %xmm5, %xmm14
	vpternlogq $0xD2, %xmm22, %xmm1, %xmm5
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm22
	vpxorq 208(%rax), %xmm0, %xmm0
	vpxorq %xmm12, %xmm0, %xmm25
	vpxorq %xmm24, %xmm25, %xmm25
	vpternlogq $0x96, %xmm18, %xmm6, %xmm25
	vpxorq %xmm8, %xmm21, %xmm26
	vpxorq %xmm15, %xmm26, %xmm26
	vpternlogq $0x96, %xmm14, %xmm2, %xmm26
	vpxorq %xmm4, %xmm17, %xmm27
	vpxorq %xmm11, %xmm27, %xmm27
	vpternlogq $0x96, %xmm5, %xmm23, %xmm27
	vpxorq %xmm20, %xmm13, %xmm28
	vpxorq %xmm7, %xmm28, %xmm28
	vpternlogq $0x96, %xmm1, %xmm19, %xmm28
	vpxorq %xmm16, %xmm9, %xmm29
	vpxorq %xmm3, %xmm29, %xmm29
	vpternlogq $0x96, %xmm22, %xmm10, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $44, %xmm8, %xmm8
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $43, %xmm11, %xmm11
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $21, %xmm19, %xmm19
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $14, %xmm22, %xmm22
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm8, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm8, %xmm0
	vpternlogq $0xD2, %xmm19, %xmm11, %xmm8
	vpternlogq $0xD2, %xmm22, %xmm19, %xmm11
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm22
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $28, %xmm13, %xmm13
	vpxorq %xmm28, %xmm16, %xmm16
	vprolq $20, %xmm16, %xmm16
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $3, %xmm24, %xmm24
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $45, %xmm2, %xmm2
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $61, %xmm5, %xmm5
	vmovdqa64 %xmm13, %xmm30
	vmovdqa64 %xmm16, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm16, %xmm13
	vpternlogq $0xD2, %xmm2, %xmm24, %xmm16
	vpternlogq $0xD2, %xmm5, %xmm2, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm5, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm5
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $1, %xmm21, %xmm21
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $6, %xmm4, %xmm4
	vpxorq %xmm27, %xmm7, %xmm7
	vprolq $25, %xmm7, %xmm7
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $8, %xmm10, %xmm10
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $18, %xmm18, %xmm18
	vmovdqa64 %xmm21, %xmm30
	vmovdqa64 %xmm4, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm4, %xmm21
	vpternlogq $0xD2, %xmm10, %xmm7, %xmm4
	vpternlogq $0xD2, %xmm18, %xmm10, %xmm7
	vpternlogq $0xD2, %xmm30, %xmm18, %xmm10
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $27, %xmm9, %xmm9
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $36, %xmm12, %xmm12
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $10, %xmm15, %xmm15
	vpxorq %xmm26, %xmm23, %xmm23
	vprolq $15, %xmm23, %xmm23
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $56, %xmm1, %xmm1
	vmovdqa64 %xmm9, %xmm30
	vmovdqa64 %xmm12, %xmm31
	vpternlogq $0xD2, %xmm15, %xmm12, %xmm9
	vpternlogq $0xD2, %xmm23, %xmm15, %xmm12
	vpternlogq $0xD2, %xmm1, %xmm23, %xmm15
	vpternlogq $0xD2, %xmm30, %xmm1, %xmm23
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm1
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $62, %xmm17, %xmm17
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $55, %xmm20, %xmm20
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $39, %xmm3, %xmm3
	vpxorq %xmm29, %xmm6, %xmm6
	vprolq $41, %xmm6, %xmm6
	vpxorq %xmm25, %xmm14, %xmm14
	vprolq $2, %xmm14, %xmm14
	vmovdqa64 %xmm17, %xmm30
	vmovdqa64 %xmm20, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm20, %xmm17
	vpternlogq $0xD2, %xmm6, %xmm3, %xmm20
	vpternlogq $0xD2, %xmm14, %xmm6, %xmm3
	vpternlogq $0xD2, %xmm30, %xmm14, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm14
	vpxorq 224(%rax), %xmm0, %xmm0
	vpxorq %xmm13, %xmm0, %xmm25
	vpxorq %xmm21, %xmm25, %xmm25
	vpternlogq $0x96, %xmm17, %xmm9, %xmm25
	vpxorq %xmm16, %xmm8, %xmm26
	vpxorq %xmm4, %xmm26, %xmm26
	vpternlogq $0x96, %xmm20, %xmm12, %xmm26
	vpxorq %xmm24, %xmm11, %xmm27
	vpxorq %xmm7, %xmm27, %xmm27
	vpternlogq $0x96, %xmm3, %xmm15, %xmm27
	vpxorq %xmm2, %xmm19, %xmm28
	vpxorq %xmm10, %xmm28, %xmm28
	vpternlogq $0x96, %xmm6, %xmm23, %xmm28
	vpxorq %xmm5, %xmm22, %xmm29
	vpxorq %xmm18, %xmm29, %xmm29
	vpternlogq $0x96, %xmm14, %xmm1, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $44, %xmm16, %xmm16
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $43, %xmm7, %xmm7
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $21, %xmm23, %xmm23
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $14, %xmm14, %xmm14
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm16, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm16, %xmm0
	vpternlogq $0xD2, %xmm23, %xmm7, %xmm16
	vpternlogq $0xD2, %xmm14, %xmm23, %xmm7
	vpternlogq $0xD2, %xmm30, %xmm14, %xmm23
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm14
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $28, %xmm19, %xmm19
	vpxorq %xmm28, %xmm5, %xmm5
	vprolq $20, %xmm5, %xmm5
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $3, %xmm21, %xmm21
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $45, %xmm12, %xmm12
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $61, %xmm3, %xmm3
	vmovdqa64 %xmm19, %xmm30
	vmovdqa64 %xmm5, %xmm31
	vpternlogq $0xD2, %xmm21, %xmm5, %xmm19
	vpternlogq $0xD2, %xmm12, %xmm21, %xmm5
	vpternlogq $0xD2, %xmm3, %xmm12, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm3, %xmm12
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm3
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $1, %xmm8, %xmm8
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $6, %xmm24, %xmm24
	vpxorq %xmm27, %xmm10, %xmm10
	vprolq $25, %xmm10, %xmm10
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $8, %xmm1, %xmm1
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $18, %xmm17, %xmm17
	vmovdqa64 %xmm8, %xmm30
	vmovdqa64 %xmm24, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm24, %xmm8
	vpternlogq $0xD2, %xmm1, %xmm10, %xmm24
	vpternlogq $0xD2, %xmm17, %xmm1, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm17, %xmm1
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm17
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $27, %xmm22, %xmm22
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $36, %xmm13, %xmm13
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $10, %xmm4, %xmm4
	vpxorq %xmm26, %xmm15, %xmm15
	vprolq $15, %xmm15, %xmm15
	vpxorq %xmm27, %xmm6, %xmm6
	vprolq $56, %xmm6, %xmm6
	vmovdqa64 %xmm22, %xmm30
	vmovdqa64 %xmm13, %xmm31
	vpternlogq $0xD2, %xmm4, %xmm13, %xmm22
	vpternlogq $0xD2, %xmm15, %xmm4, %xmm13
	vpternlogq $0xD2, %xmm6, %xmm15, %xmm4
	vpternlogq $0xD2, %xmm30, %xmm6, %xmm15
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm6
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $62, %xmm11, %xmm11
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $55, %xmm2, %xmm2
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $39, %xmm18, %xmm18
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $41, %xmm9, %xmm9
	vpxorq %xmm25, %xmm20, %xmm20
	vprolq $2, %xmm20, %xmm20
	vmovdqa64 %xmm11, %xmm30
	vmovdqa64 %xmm2, %xmm31
	vpternlogq $0xD2, %xmm18, %xmm2, %xmm11
	vpternlogq $0xD2, %xmm9, %xmm18, %xmm2
	vpternlogq $0xD2, %xmm20, %xmm9, %xmm18
	vpternlogq $0xD2, %xmm30, %xmm20, %xmm9
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm20
	vpxorq 240(%rax), %xmm0, %xmm0
	vpxorq %xmm19, %xmm0, %xmm25
	vpxorq %xmm8, %xmm25, %xmm25
	vpternlogq $0x96, %xmm11, %xmm22, %xmm25
	vpxorq %xmm5, %xmm16, %xmm26
	vpxorq %xmm24, %xmm26, %xmm26
	vpternlogq $0x96, %xmm2, %xmm13, %xmm26
	vpxorq %xmm21, %xmm7, %xmm27
	vpxorq %xmm10, %xmm27, %xmm27
	vpternlogq $0x96, %xmm18, %xmm4, %xmm27
	vpxorq %xmm12, %xmm23, %xmm28
	vpxorq %xmm1, %xmm28, %xmm28
	vpternlogq $0x96, %xmm9, %xmm15, %xmm28
	vpxorq %xmm3, %xmm14, %xmm29
	vpxorq %xmm17, %xmm29, %xmm29
	vpternlogq $0x96, %xmm20, %xmm6, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $44, %xmm5, %xmm5
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $43, %xmm10, %xmm10
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $21, %xmm15, %xmm15
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $14, %xmm20, %xmm20
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm5, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm5, %xmm0
	vpternlogq $0xD2, %xmm15, %xmm10, %xmm5
	vpternlogq $0xD2, %xmm20, %xmm15, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm20, %xmm15
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm20
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $28, %xmm23, %xmm23
	vpxorq %xmm28, %xmm3, %xmm3
	vprolq $20, %xmm3, %xmm3
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $3, %xmm8, %xmm8
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $45, %xmm13, %xmm13
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $61, %xmm18, %xmm18
	vmovdqa64 %xmm23, %xmm30
	vmovdqa64 %xmm3, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm3, %xmm23
	vpternlogq $0xD2, %xmm13, %xmm8, %xmm3
	vpternlogq $0xD2, %xmm18, %xmm13, %xmm8
	vpternlogq $0xD2, %xmm30, %xmm18, %xmm13
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm18
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $1, %xmm16, %xmm16
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $6, %xmm21, %xmm21
	vpxorq %xmm27, %xmm1, %xmm1
	vprolq $25, %xmm1, %xmm1
	vpxorq %xmm28, %xmm6, %xmm6
	vprolq $8, %xmm6, %xmm6
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $18, %xmm11, %xmm11
	vmovdqa64 %xmm16, %xmm30
	vmovdqa64 %xmm21, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm21, %xmm16
	vpternlogq $0xD2, %xmm6, %xmm1, %xmm21
	vpternlogq $0xD2, %xmm11, %xmm6, %xmm1
	vpternlogq $0xD2, %xmm30, %xmm11, %xmm6
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm11
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $27, %xmm14, %xmm14
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $36, %xmm19, %xmm19
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $10, %xmm24, %xmm24
	vpxorq %xmm26, %xmm4, %xmm4
	vprolq $15, %xmm4, %xmm4
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $56, %xmm9, %xmm9
	vmovdqa64 %xmm14, %xmm30
	vmovdqa64 %xmm19, %xmm31
	vpternlogq $0xD2, %xmm24, %xmm19, %xmm14
	vpternlogq $0xD2, %xmm4, %xmm24, %xmm19
	vpternlogq $0xD2, %xmm9, %xmm4, %xmm24
	vpternlogq $0xD2, %xmm30, %xmm9, %xmm4
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm9
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $62, %xmm7, %xmm7
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $55, %xmm12, %xmm12
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $39, %xmm17, %xmm17
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $41, %xmm22, %xmm22
	vpxorq %xmm25, %xmm2, %xmm2
	vprolq $2, %xmm2, %xmm2
	vmovdqa64 %xmm7, %xmm30
	vmovdqa64 %xmm12, %xmm31
	vpternlogq $0xD2, %xmm17, %xmm12, %xmm7
	vpternlogq $0xD2, %xmm22, %xmm17, %xmm12
	vpternlogq $0xD2, %xmm2, %xmm22, %xmm17
	vpternlogq $0xD2, %xmm30, %xmm2, %xmm22
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm2
	vpxorq 256(%rax), %xmm0, %xmm0
	vpxorq %xmm23, %xmm0, %xmm25
	vpxorq %xmm16, %xmm25, %xmm25
	vpternlogq $0x96, %xmm7, %xmm14, %xmm25
	vpxorq %xmm3, %xmm5, %xmm26
	vpxorq %xmm21, %xmm26, %xmm26
	vpternlogq $0x96, %xmm12, %xmm19, %xmm26
	vpxorq %xmm8, %xmm10, %xmm27
	vpxorq %xmm1, %xmm27, %xmm27
	vpternlogq $0x96, %xmm17, %xmm24, %xmm27
	vpxorq %xmm13, %xmm15, %xmm28
	vpxorq %xmm6, %xmm28, %xmm28
	vpternlogq $0x96, %xmm22, %xmm4, %xmm28
	vpxorq %xmm18, %xmm20, %xmm29
	vpxorq %xmm11, %xmm29, %xmm29
	vpternlogq $0x96, %xmm2, %xmm9, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $44, %xmm3, %xmm3
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $43, %xmm1, %xmm1
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $21, %xmm4, %xmm4
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $14, %xmm2, %xmm2
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm3, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm3, %xmm0
	vpternlogq $0xD2, %xmm4, %xmm1, %xmm3
	vpternlogq $0xD2, %xmm2, %xmm4, %xmm1
	vpternlogq $0xD2, %xmm30, %xmm2, %xmm4
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm2
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $28, %xmm15, %xmm15
	vpxorq %xmm28, %xmm18, %xmm18
	vprolq $20, %xmm18, %xmm18
	vpxorq %xmm29, %xmm16, %xmm16
	vprolq $3, %xmm16, %xmm16
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $45, %xmm19, %xmm19
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $61, %xmm17, %xmm17
	vmovdqa64 %xmm15, %xmm30
	vmovdqa64 %xmm18, %xmm31
	vpternlogq $0xD2, %xmm16, %xmm18, %xmm15
	vpternlogq $0xD2, %xmm19, %xmm16, %xmm18
	vpternlogq $0xD2, %xmm17, %xmm19, %xmm16
	vpternlogq $0xD2, %xmm30, %xmm17, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm17
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $1, %xmm5, %xmm5
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $6, %xmm8, %xmm8
	vpxorq %xmm27, %xmm6, %xmm6
	vprolq $25, %xmm6, %xmm6
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $8, %xmm9, %xmm9
	vpxorq %xmm29, %xmm7, %xmm7
	vprolq $18, %xmm7, %xmm7
	vmovdqa64 %xmm5, %xmm30
	vmovdqa64 %xmm8, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm8, %xmm5
	vpternlogq $0xD2, %xmm9, %xmm6, %xmm8
	vpternlogq $0xD2, %xmm7, %xmm9, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm7, %xmm9
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm7
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $27, %xmm20, %xmm20
	vpxorq %xmm29, %xmm23, %xmm23
	vprolq $36, %xmm23, %xmm23
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $10, %xmm21, %xmm21
	vpxorq %xmm26, %xmm24, %xmm24
	vprolq $15, %xmm24, %xmm24
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $56, %xmm22, %xmm22
	vmovdqa64 %xmm20, %xmm30
	vmovdqa64 %xmm23, %xmm31
	vpternlogq $0xD2, %xmm21, %xmm23, %xmm20
	vpternlogq $0xD2, %xmm24, %xmm21, %xmm23
	vpternlogq $0xD2, %xmm22, %xmm24, %xmm21
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm24
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm22
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $62, %xmm10, %xmm10
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $55, %xmm13, %xmm13
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $39, %xmm11, %xmm11
	vpxorq %xmm29, %xmm14, %xmm14
	vprolq $41, %xmm14, %xmm14
	vpxorq %xmm25, %xmm12, %xmm12
	vprolq $2, %xmm12, %xmm12
	vmovdqa64 %xmm10, %xmm30
	vmovdqa64 %xmm13, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm13, %xmm10
	vpternlogq $0xD2, %xmm14, %xmm11, %xmm13
	vpternlogq $0xD2, %xmm12, %xmm14, %xmm11
	vpternlogq $0xD2, %xmm30, %xmm12, %xmm14
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpxorq 272(%rax), %xmm0, %xmm0
	vpxorq %xmm15, %xmm0, %xmm25
	vpxorq %xmm5, %xmm25, %xmm25
	vpternlogq $0x96, %xmm10, %xmm20, %xmm25
	vpxorq %xmm18, %xmm3, %xmm26
	vpxorq %xmm8, %xmm26, %xmm26
	vpternlogq $0x96, %xmm13, %xmm23, %xmm26
	vpxorq %xmm16, %xmm1, %xmm27
	vpxorq %xmm6, %xmm27, %xmm27
	vpternlogq $0x96, %xmm11, %xmm21, %xmm27
	vpxorq %xmm19, %xmm4, %xmm28
	vpxorq %xmm9, %xmm28, %xmm28
	vpternlogq $0x96, %xmm14, %xmm24, %xmm28
	vpxorq %xmm17, %xmm2, %xmm29
	vpxorq %xmm7, %xmm29, %xmm29
	vpternlogq $0x96, %xmm12, %xmm22, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $44, %xmm18, %xmm18
	vpxorq %xmm26, %xmm6, %xmm6
	vprolq $43, %xmm6, %xmm6
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $21, %xmm24, %xmm24
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $14, %xmm12, %xmm12
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm18, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm18, %xmm0
	vpternlogq $0xD2, %xmm24, %xmm6, %xmm18
	vpternlogq $0xD2, %xmm12, %xmm24, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm12, %xmm24
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $28, %xmm4, %xmm4
	vpxorq %xmm28, %xmm17, %xmm17
	vprolq $20, %xmm17, %xmm17
	vpxorq %xmm29, %xmm5, %xmm5
	vprolq $3, %xmm5, %xmm5
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $45, %xmm23, %xmm23
	vpxorq %xmm26, %xmm11, %xmm11
	vprolq $61, %xmm11, %xmm11
	vmovdqa64 %xmm4, %xmm30
	vmovdqa64 %xmm17, %xmm31
	vpternlogq $0xD2, %xmm5, %xmm17, %xmm4
	vpternlogq $0xD2, %xmm23, %xmm5, %xmm17
	vpternlogq $0xD2, %xmm11, %xmm23, %xmm5
	vpternlogq $0xD2, %xmm30, %xmm11, %xmm23
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm11
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $1, %xmm3, %xmm3
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $6, %xmm16, %xmm16
	vpxorq %xmm27, %xmm9, %xmm9
	vprolq $25, %xmm9, %xmm9
	vpxorq %xmm28, %xmm22, %xmm22
	vprolq $8, %xmm22, %xmm22
	vpxorq %xmm29, %xmm10, %xmm10
	vprolq $18, %xmm10, %xmm10
	vmovdqa64 %xmm3, %xmm30
	vmovdqa64 %xmm16, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm16, %xmm3
	vpternlogq $0xD2, %xmm22, %xmm9, %xmm16
	vpternlogq $0xD2, %xmm10, %xmm22, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm10, %xmm22
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm10
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $27, %xmm2, %xmm2
	vpxorq %xmm29, %xmm15, %xmm15
	vprolq $36, %xmm15, %xmm15
	vpxorq %xmm25, %xmm8, %xmm8
	vprolq $10, %xmm8, %xmm8
	vpxorq %xmm26, %xmm21, %xmm21
	vprolq $15, %xmm21, %xmm21
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $56, %xmm14, %xmm14
	vmovdqa64 %xmm2, %xmm30
	vmovdqa64 %xmm15, %xmm31
	vpternlogq $0xD2, %xmm8, %xmm15, %xmm2
	vpternlogq $0xD2, %xmm21, %xmm8, %xmm15
	vpternlogq $0xD2, %xmm14, %xmm21, %xmm8
	vpternlogq $0xD2, %xmm30, %xmm14, %xmm21
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm14
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $62, %xmm1, %xmm1
	vpxorq %xmm27, %xmm19, %xmm19
	vprolq $55, %xmm19, %xmm19
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $39, %xmm7, %xmm7
	vpxorq %xmm29, %xmm20, %xmm20
	vprolq $41, %xmm20, %xmm20
	vpxorq %xmm25, %xmm13, %xmm13
	vprolq $2, %xmm13, %xmm13
	vmovdqa64 %xmm1, %xmm30
	vmovdqa64 %xmm19, %xmm31
	vpternlogq $0xD2, %xmm7, %xmm19, %xmm1
	vpternlogq $0xD2, %xmm20, %xmm7, %xmm19
	vpternlogq $0xD2, %xmm13, %xmm20, %xmm7
	vpternlogq $0xD2, %xmm30, %xmm13, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm13
	vpxorq 288(%rax), %xmm0, %xmm0
	vpxorq %xmm4, %xmm0, %xmm25
	vpxorq %xmm3, %xmm25, %xmm25
	vpternlogq $0x96, %xmm1, %xmm2, %xmm25
	vpxorq %xmm17, %xmm18, %xmm26
	vpxorq %xmm16, %xmm26, %xmm26
	vpternlogq $0x96, %xmm19, %xmm15, %xmm26
	vpxorq %xmm5, %xmm6, %xmm27
	vpxorq %xmm9, %xmm27, %xmm27
	vpternlogq $0x96, %xmm7, %xmm8, %xmm27
	vpxorq %xmm23, %xmm24, %xmm28
	vpxorq %xmm22, %xmm28, %xmm28
	vpternlogq $0x96, %xmm20, %xmm21, %xmm28
	vpxorq %xmm11, %xmm12, %xmm29
	vpxorq %xmm10, %xmm29, %xmm29
	vpternlogq $0x96, %xmm13, %xmm14, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $44, %xmm17, %xmm17
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $43, %xmm9, %xmm9
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $21, %xmm21, %xmm21
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $14, %xmm13, %xmm13
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm17, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm17, %xmm0
	vpternlogq $0xD2, %xmm21, %xmm9, %xmm17
	vpternlogq $0xD2, %xmm13, %xmm21, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm13, %xmm21
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm13
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $28, %xmm24, %xmm24
	vpxorq %xmm28, %xmm11, %xmm11
	vprolq $20, %xmm11, %xmm11
	vpxorq %xmm29, %xmm3, %xmm3
	vprolq $3, %xmm3, %xmm3
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $45, %xmm15, %xmm15
	vpxorq %xmm26, %xmm7, %xmm7
	vprolq $61, %xmm7, %xmm7
	vmovdqa64 %xmm24, %xmm30
	vmovdqa64 %xmm11, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm11, %xmm24
	vpternlogq $0xD2, %xmm15, %xmm3, %xmm11
	vpternlogq $0xD2, %xmm7, %xmm15, %xmm3
	vpternlogq $0xD2, %xmm30, %xmm7, %xmm15
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm7
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $1, %xmm18, %xmm18
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $6, %xmm5, %xmm5
	vpxorq %xmm27, %xmm22, %xmm22
	vprolq $25, %xmm22, %xmm22
	vpxorq %xmm28, %xmm14, %xmm14
	vprolq $8, %xmm14, %xmm14
	vpxorq %xmm29, %xmm1, %xmm1
	vprolq $18, %xmm1, %xmm1
	vmovdqa64 %xmm18, %xmm30
	vmovdqa64 %xmm5, %xmm31
	vpternlogq $0xD2, %xmm22, %xmm5, %xmm18
	vpternlogq $0xD2, %xmm14, %xmm22, %xmm5
	vpternlogq $0xD2, %xmm1, %xmm14, %xmm22
	vpternlogq $0xD2, %xmm30, %xmm1, %xmm14
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm1
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $27, %xmm12, %xmm12
	vpxorq %xmm29, %xmm4, %xmm4
	vprolq $36, %xmm4, %xmm4
	vpxorq %xmm25, %xmm16, %xmm16
	vprolq $10, %xmm16, %xmm16
	vpxorq %xmm26, %xmm8, %xmm8
	vprolq $15, %xmm8, %xmm8
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $56, %xmm20, %xmm20
	vmovdqa64 %xmm12, %xmm30
	vmovdqa64 %xmm4, %xmm31
	vpternlogq $0xD2, %xmm16, %xmm4, %xmm12
	vpternlogq $0xD2, %xmm8, %xmm16, %xmm4
	vpternlogq $0xD2, %xmm20, %xmm8, %xmm16
	vpternlogq $0xD2, %xmm30, %xmm20, %xmm8
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm20
	vpxorq %xmm26, %xmm6, %xmm6
	vprolq $62, %xmm6, %xmm6
	vpxorq %xmm27, %xmm23, %xmm23
	vprolq $55, %xmm23, %xmm23
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $39, %xmm10, %xmm10
	vpxorq %xmm29, %xmm2, %xmm2
	vprolq $41, %xmm2, %xmm2
	vpxorq %xmm25, %xmm19, %xmm19
	vprolq $2, %xmm19, %xmm19
	vmovdqa64 %xmm6, %xmm30
	vmovdqa64 %xmm23, %xmm31
	vpternlogq $0xD2, %xmm10, %xmm23, %xmm6
	vpternlogq $0xD2, %xmm2, %xmm10, %xmm23
	vpternlogq $0xD2, %xmm19, %xmm2, %xmm10
	vpternlogq $0xD2, %xmm30, %xmm19, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm19
	vpxorq 304(%rax), %xmm0, %xmm0
	vpxorq %xmm24, %xmm0, %xmm25
	vpxorq %xmm18, %xmm25, %xmm25
	vpternlogq $0x96, %xmm6, %xmm12, %xmm25
	vpxorq %xmm11, %xmm17, %xmm26
	vpxorq %xmm5, %xmm26, %xmm26
	vpternlogq $0x96, %xmm23, %xmm4, %xmm26
	vpxorq %xmm3, %xmm9, %xmm27
	vpxorq %xmm22, %xmm27, %xmm27
	vpternlogq $0x96, %xmm10, %xmm16, %xmm27
	vpxorq %xmm15, %xmm21, %xmm28
	vpxorq %xmm14, %xmm28, %xmm28
	vpternlogq $0x96, %xmm2, %xmm8, %xmm28
	vpxorq %xmm7, %xmm13, %xmm29
	vpxorq %xmm1, %xmm29, %xmm29
	vpternlogq $0x96, %xmm19, %xmm20, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $44, %xmm11, %xmm11
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $43, %xmm22, %xmm22
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $21, %xmm8, %xmm8
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $14, %xmm19, %xmm19
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm11, %xmm31
	vpternlogq $0xD2, %xmm22, %xmm11, %xmm0
	vpternlogq $0xD2, %xmm8, %xmm22, %xmm11
	vpternlogq $0xD2, %xmm19, %xmm8, %xmm22
	vpternlogq $0xD2, %xmm30, %xmm19, %xmm8
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm19
	vpxorq %xmm27, %xmm21, %xmm21
	vprolq $28, %xmm21, %xmm21
	vpxorq %xmm28, %xmm7, %xmm7
	vprolq $20, %xmm7, %xmm7
	vpxorq %xmm29, %xmm18, %xmm18
	vprolq $3, %xmm18, %xmm18
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $45, %xmm4, %xmm4
	vpxorq %xmm26, %xmm10, %xmm10
	vprolq $61, %xmm10, %xmm10
	vmovdqa64 %xmm21, %xmm30
	vmovdqa64 %xmm7, %xmm31
	vpternlogq $0xD2, %xmm18, %xmm7, %xmm21
	vpternlogq $0xD2, %xmm4, %xmm18, %xmm7
	vpternlogq $0xD2, %xmm10, %xmm4, %xmm18
	vpternlogq $0xD2, %xmm30, %xmm10, %xmm4
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm10
	vpxorq %xmm25, %xmm17, %xmm17
	vprolq $1, %xmm17, %xmm17
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $6, %xmm3, %xmm3
	vpxorq %xmm27, %xmm14, %xmm14
	vprolq $25, %xmm14, %xmm14
	vpxorq %xmm28, %xmm20, %xmm20
	vprolq $8, %xmm20, %xmm20
	vpxorq %xmm29, %xmm6, %xmm6
	vprolq $18, %xmm6, %xmm6
	vmovdqa64 %xmm17, %xmm30
	vmovdqa64 %xmm3, %xmm31
	vpternlogq $0xD2, %xmm14, %xmm3, %xmm17
	vpternlogq $0xD2, %xmm20, %xmm14, %xmm3
	vpternlogq $0xD2, %xmm6, %xmm20, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm6, %xmm20
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm6
	vpxorq %xmm28, %xmm13, %xmm13
	vprolq $27, %xmm13, %xmm13
	vpxorq %xmm29, %xmm24, %xmm24
	vprolq $36, %xmm24, %xmm24
	vpxorq %xmm25, %xmm5, %xmm5
	vprolq $10, %xmm5, %xmm5
	vpxorq %xmm26, %xmm16, %xmm16
	vprolq $15, %xmm16, %xmm16
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $56, %xmm2, %xmm2
	vmovdqa64 %xmm13, %xmm30
	vmovdqa64 %xmm24, %xmm31
	vpternlogq $0xD2, %xmm5, %xmm24, %xmm13
	vpternlogq $0xD2, %xmm16, %xmm5, %xmm24
	vpternlogq $0xD2, %xmm2, %xmm16, %xmm5
	vpternlogq $0xD2, %xmm30, %xmm2, %xmm16
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm2
	vpxorq %xmm26, %xmm9, %xmm9
	vprolq $62, %xmm9, %xmm9
	vpxorq %xmm27, %xmm15, %xmm15
	vprolq $55, %xmm15, %xmm15
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $39, %xmm1, %xmm1
	vpxorq %xmm29, %xmm12, %xmm12
	vprolq $41, %xmm12, %xmm12
	vpxorq %xmm25, %xmm23, %xmm23
	vprolq $2, %xmm23, %xmm23
	vmovdqa64 %xmm9, %xmm30
	vmovdqa64 %xmm15, %xmm31
	vpternlogq $0xD2, %xmm1, %xmm15, %xmm9
	vpternlogq $0xD2, %xmm12, %xmm1, %xmm15
	vpternlogq $0xD2, %xmm23, %xmm12, %xmm1
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm12
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm23
	vpxorq 320(%rax), %xmm0, %xmm0
	vpxorq %xmm21, %xmm0, %xmm25
	vpxorq %xmm17, %xmm25, %xmm25
	vpternlogq $0x96, %xmm9, %xmm13, %xmm25
	vpxorq %xmm7, %xmm11, %xmm26
	vpxorq %xmm3, %xmm26, %xmm26
	vpternlogq $0x96, %xmm15, %xmm24, %xmm26
	vpxorq %xmm18, %xmm22, %xmm27
	vpxorq %xmm14, %xmm27, %xmm27
	vpternlogq $0x96, %xmm1, %xmm5, %xmm27
	vpxorq %xmm4, %xmm8, %xmm28
	vpxorq %xmm20, %xmm28, %xmm28
	vpternlogq $0x96, %xmm12, %xmm16, %xmm28
	vpxorq %xmm10, %xmm19, %xmm29
	vpxorq %xmm6, %xmm29, %xmm29
	vpternlogq $0x96, %xmm23, %xmm2, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $44, %xmm7, %xmm7
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $43, %xmm14, %xmm14
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $21, %xmm16, %xmm16
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $14, %xmm23, %xmm23
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm7, %xmm31
	vpternlogq $0xD2, %xmm14, %xmm7, %xmm0
	vpternlogq $0xD2, %xmm16, %xmm14, %xmm7
	vpternlogq $0xD2, %xmm23, %xmm16, %xmm14
	vpternlogq $0xD2, %xmm30, %xmm23, %xmm16
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm23
	vpxorq %xmm27, %xmm8, %xmm8
	vprolq $28, %xmm8, %xmm8
	vpxorq %xmm28, %xmm10, %xmm10
	vprolq $20, %xmm10, %xmm10
	vpxorq %xmm29, %xmm17, %xmm17
	vprolq $3, %xmm17, %xmm17
	vpxorq %xmm25, %xmm24, %xmm24
	vprolq $45, %xmm24, %xmm24
	vpxorq %xmm26, %xmm1, %xmm1
	vprolq $61, %xmm1, %xmm1
	vmovdqa64 %xmm8, %xmm30
	vmovdqa64 %xmm10, %xmm31
	vpternlogq $0xD2, %xmm17, %xmm10, %xmm8
	vpternlogq $0xD2, %xmm24, %xmm17, %xmm10
	vpternlogq $0xD2, %xmm1, %xmm24, %xmm17
	vpternlogq $0xD2, %xmm30, %xmm1, %xmm24
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm1
	vpxorq %xmm25, %xmm11, %xmm11
	vprolq $1, %xmm11, %xmm11
	vpxorq %xmm26, %xmm18, %xmm18
	vprolq $6, %xmm18, %xmm18
	vpxorq %xmm27, %xmm20, %xmm20
	vprolq $25, %xmm20, %xmm20
	vpxorq %xmm28, %xmm2, %xmm2
	vprolq $8, %xmm2, %xmm2
	vpxorq %xmm29, %xmm9, %xmm9
	vprolq $18, %xmm9, %xmm9
	vmovdqa64 %xmm11, %xmm30
	vmovdqa64 %xmm18, %xmm31
	vpternlogq $0xD2, %xmm20, %xmm18, %xmm11
	vpternlogq $0xD2, %xmm2, %xmm20, %xmm18
	vpternlogq $0xD2, %xmm9, %xmm2, %xmm20
	vpternlogq $0xD2, %xmm30, %xmm9, %xmm2
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm9
	vpxorq %xmm28, %xmm19, %xmm19
	vprolq $27, %xmm19, %xmm19
	vpxorq %xmm29, %xmm21, %xmm21
	vprolq $36, %xmm21, %xmm21
	vpxorq %xmm25, %xmm3, %xmm3
	vprolq $10, %xmm3, %xmm3
	vpxorq %xmm26, %xmm5, %xmm5
	vprolq $15, %xmm5, %xmm5
	vpxorq %xmm27, %xmm12, %xmm12
	vprolq $56, %xmm12, %xmm12
	vmovdqa64 %xmm19, %xmm30
	vmovdqa64 %xmm21, %xmm31
	vpternlogq $0xD2, %xmm3, %xmm21, %xmm19
	vpternlogq $0xD2, %xmm5, %xmm3, %xmm21
	vpternlogq $0xD2, %xmm12, %xmm5, %xmm3
	vpternlogq $0xD2, %xmm30, %xmm12, %xmm5
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm12
	vpxorq %xmm26, %xmm22, %xmm22
	vprolq $62, %xmm22, %xmm22
	vpxorq %xmm27, %xmm4, %xmm4
	vprolq $55, %xmm4, %xmm4
	vpxorq %xmm28, %xmm6, %xmm6
	vprolq $39, %xmm6, %xmm6
	vpxorq %xmm29, %xmm13, %xmm13
	vprolq $41, %xmm13, %xmm13
	vpxorq %xmm25, %xmm15, %xmm15
	vprolq $2, %xmm15, %xmm15
	vmovdqa64 %xmm22, %xmm30
	vmovdqa64 %xmm4, %xmm31
	vpternlogq $0xD2, %xmm6, %xmm4, %xmm22
	vpternlogq $0xD2, %xmm13, %xmm6, %xmm4
	vpternlogq $0xD2, %xmm15, %xmm13, %xmm6
	vpternlogq $0xD2, %xmm30, %xmm15, %xmm13
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm15
	vpxorq 336(%rax), %xmm0, %xmm0
	vpxorq %xmm8, %xmm0, %xmm25
	vpxorq %xmm11, %xmm25, %xmm25
	vpternlogq $0x96, %xmm22, %xmm19, %xmm25
	vpxorq %xmm10, %xmm7, %xmm26
	vpxorq %xmm18, %xmm26, %xmm26
	vpternlogq $0x96, %xmm4, %xmm21, %xmm26
	vpxorq %xmm17, %xmm14, %xmm27
	vpxorq %xmm20, %xmm27, %xmm27
	vpternlogq $0x96, %xmm6, %xmm3, %xmm27
	vpxorq %xmm24, %xmm16, %xmm28
	vpxorq %xmm2, %xmm28, %xmm28
	vpternlogq $0x96, %xmm13, %xmm5, %xmm28
	vpxorq %xmm1, %xmm23, %xmm29
	vpxorq %xmm9, %xmm29, %xmm29
	vpternlogq $0x96, %xmm15, %xmm12, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm10, %xmm10
	vprolq $44, %xmm10, %xmm10
	vpxorq %xmm26, %xmm20, %xmm20
	vprolq $43, %xmm20, %xmm20
	vpxorq %xmm27, %xmm5, %xmm5
	vprolq $21, %xmm5, %xmm5
	vpxorq %xmm28, %xmm15, %xmm15
	vprolq $14, %xmm15, %xmm15
	vmovdqa64 %xmm0, %xmm30
	vmovdqa64 %xmm10, %xmm31
	vpternlogq $0xD2, %xmm20, %xmm10, %xmm0
	vpternlogq $0xD2, %xmm5, %xmm20, %xmm10
	vpternlogq $0xD2, %xmm15, %xmm5, %xmm20
	vpternlogq $0xD2, %xmm30, %xmm15, %xmm5
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm15
	vpxorq %xmm27, %xmm16, %xmm16
	vprolq $28, %xmm16, %xmm16
	vpxorq %xmm28, %xmm1, %xmm1
	vprolq $20, %xmm1, %xmm1
	vpxorq %xmm29, %xmm11, %xmm11
	vprolq $3, %xmm11, %xmm11
	vpxorq %xmm25, %xmm21, %xmm21
	vprolq $45, %xmm21, %xmm21
	vpxorq %xmm26, %xmm6, %xmm6
	vprolq $61, %xmm6, %xmm6
	vmovdqa64 %xmm16, %xmm30
	vmovdqa64 %xmm1, %xmm31
	vpternlogq $0xD2, %xmm11, %xmm1, %xmm16
	vpternlogq $0xD2, %xmm21, %xmm11, %xmm1
	vpternlogq $0xD2, %xmm6, %xmm21, %xmm11
	vpternlogq $0xD2, %xmm30, %xmm6, %xmm21
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm6
	vpxorq %xmm25, %xmm7, %xmm7
	vprolq $1, %xmm7, %xmm7
	vpxorq %xmm26, %xmm17, %xmm17
	vprolq $6, %xmm17, %xmm17
	vpxorq %xmm27, %xmm2, %xmm2
	vprolq $25, %xmm2, %xmm2
	vpxorq %xmm28, %xmm12, %xmm12
	vprolq $8, %xmm12, %xmm12
	vpxorq %xmm29, %xmm22, %xmm22
	vprolq $18, %xmm22, %xmm22
	vmovdqa64 %xmm7, %xmm30
	vmovdqa64 %xmm17, %xmm31
	vpternlogq $0xD2, %xmm2, %xmm17, %xmm7
	vpternlogq $0xD2, %xmm12, %xmm2, %xmm17
	vpternlogq $0xD2, %xmm22, %xmm12, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm22, %xmm12
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm22
	vpxorq %xmm28, %xmm23, %xmm23
	vprolq $27, %xmm23, %xmm23
	vpxorq %xmm29, %xmm8, %xmm8
	vprolq $36, %xmm8, %xmm8
	vpxorq %xmm25, %xmm18, %xmm18
	vprolq $10, %xmm18, %xmm18
	vpxorq %xmm26, %xmm3, %xmm3
	vprolq $15, %xmm3, %xmm3
	vpxorq %xmm27, %xmm13, %xmm13
	vprolq $56, %xmm13, %xmm13
	vmovdqa64 %xmm23, %xmm30
	vmovdqa64 %xmm8, %xmm31
	vpternlogq $0xD2, %xmm18, %xmm8, %xmm23
	vpternlogq $0xD2, %xmm3, %xmm18, %xmm8
	vpternlogq $0xD2, %xmm13, %xmm3, %xmm18
	vpternlogq $0xD2, %xmm30, %xmm13, %xmm3
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm13
	vpxorq %xmm26, %xmm14, %xmm14
	vprolq $62, %xmm14, %xmm14
	vpxorq %xmm27, %xmm24, %xmm24
	vprolq $55, %xmm24, %xmm24
	vpxorq %xmm28, %xmm9, %xmm9
	vprolq $39, %xmm9, %xmm9
	vpxorq %xmm29, %xmm19, %xmm19
	vprolq $41, %xmm19, %xmm19
	vpxorq %xmm25, %xmm4, %xmm4
	vprolq $2, %xmm4, %xmm4
	vmovdqa64 %xmm14, %xmm30
	vmovdqa64 %xmm24, %xmm31
	vpternlogq $0xD2, %xmm9, %xmm24, %xmm14
	vpternlogq $0xD2, %xmm19, %xmm9, %xmm24
	vpternlogq $0xD2, %xmm4, %xmm19, %xmm9
	vpternlogq $0xD2, %xmm30, %xmm4, %xmm19
	vpternlogq $0xD2, %xmm31, %xmm30, %xmm4
	vpxorq 352(%rax), %xmm0, %xmm0
	vpxorq %xmm16, %xmm0, %xmm25
	vpxorq %xmm7, %xmm25, %xmm25
	vpternlogq $0x96, %xmm14, %xmm23, %xmm25
	vpxorq %xmm1, %xmm10, %xmm26
	vpxorq %xmm17, %xmm26, %xmm26
	vpternlogq $0x96, %xmm24, %xmm8, %xmm26
	vpxorq %xmm11, %xmm20, %xmm27
	vpxorq %xmm2, %xmm27, %xmm27
	vpternlogq $0x96, %xmm9, %xmm18, %xmm27
	vpxorq %xmm21, %xmm5, %xmm28
	vpxorq %xmm12, %xmm28, %xmm28
	vpternlogq $0x96, %xmm19, %xmm3, %xmm28
	vpxorq %xmm6, %xmm15, %xmm29
	vpxorq %xmm22, %xmm29, %xmm29
	vpternlogq $0x96, %xmm4, %xmm13, %xmm29
	vprolq $1, %xmm25, %xmm31
	vprolq $1, %xmm27, %xmm30
	vpxorq %xmm30, %xmm25, %xmm25
	vprolq $1, %xmm28, %xmm30
	vpxorq %xmm31, %xmm28, %xmm28
	vprolq $1, %xmm26, %xmm31
	vpxorq %xmm30, %xmm26, %xmm26
	vprolq $1, %xmm29, %xmm30
	vpxorq %xmm31, %xmm29, %xmm29
	vpxorq %xmm30, %xmm27, %xmm27
	vpxorq %xmm29, %xmm0, %xmm0
	vpxorq %xmm25, %xmm1, %xmm1
	vprolq $44, %xmm1, %xmm1
	vpxorq %xmm26, %xmm2, %xmm2
	vprolq $43, %xmm2, %xmm2
	vpxorq %xmm27, %xmm3, %xmm3
	vprolq $21, %xmm3, %xmm3
	vpxorq %xmm28, %xmm4, %xmm4
	vprolq $14, %xmm4, %xmm4
	vmovdqa64 %xmm0, %xmm30
	vpternlogq $0xD2, %xmm2, %xmm1, %xmm0
	vpternlogq $0xD2, %xmm3, %xmm2, %xmm1
	vpternlogq $0xD2, %xmm4, %xmm3, %xmm2
	vpternlogq $0xD2, %xmm30, %xmm4, %xmm3
	vpxorq 368(%rax), %xmm0, %xmm0
	vmovdqa64 %xmm0, %xmm26
	vmovdqa64 %xmm1, %xmm27
	vmovdqa64 %xmm2, %xmm28
	vmovdqa64 %xmm3, %xmm29
	decq %r8
	jnz 1b
	vmovdqu64 %xmm26, 0(%rsp)
	vmovdqu64 %xmm27, 16(%rsp)
	vmovdqu64 %xmm28, 32(%rsp)
	vmovdqu64 %xmm29, 48(%rsp)
	
# 0 "" 2
#NO_APP
.L33:
	xorl	%eax, %eax
.L34:
	movq	(%rdx), %rcx
	addq	$16, %rdx
	movq	%rcx, (%rdi,%rax)
	movq	-8(%rdx), %rcx
	movq	%rcx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	$32, %rax
	jne	.L34
	movq	120(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L42
	vzeroupper
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L42:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7374:
	.size	chain2_avx512vl, .-chain2_avx512vl
	.p2align 4
	.type	chain_avx512vl, @function
chain_avx512vl:
.LFB7375:
	.cfi_startproc
	endbr64
	subq	$56, %rsp
	.cfi_def_cfa_offset 64
	movq	%rsi, %rcx
	movq	%fs:40, %r8
	movq	%r8, 40(%rsp)
	movq	%rdx, %r8
	movq	%rsp, %rdx
	call	chain2_avx512vl
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L47
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L47:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7375:
	.size	chain_avx512vl, .-chain_avx512vl
	.p2align 4
	.type	chain_bmi, @function
chain_bmi:
.LFB98:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	addq	$-128, %rsp
	.cfi_def_cfa_offset 184
	movdqu	(%rsi), %xmm3
	movdqu	16(%rsi), %xmm2
	movq	%rdx, 104(%rsp)
	testq	%rdx, %rdx
	je	.L55
	movq	%rdi, 112(%rsp)
	movhlps	%xmm3, %xmm4
	movhlps	%xmm2, %xmm5
	movq	%xmm3, %rsi
	movq	%xmm4, %r8
	movq	%xmm2, %rcx
	movq	%xmm5, %rax
	movq	$0, -72(%rsp)
	.p2align 4
	.p2align 3
.L50:
	movq	%r8, %rbx
	movq	%rsi, %rdi
	movq	%rax, %rdx
	shrq	$56, %rax
	shldq	$8, %rsi, %rbx
	orb	$1, %ah
	salq	$8, %rdi
	movq	%rcx, %r9
	shldq	$8, %r8, %r9
	orq	$67, %rdi
	shldq	$8, %rcx, %rdx
	movabsq	$-9223372036854775808, %rsi
	xorq	%rbx, %rsi
	rorx	$63, %r9, %r11
	rorx	$63, %rdx, %rcx
	xorq	%rdi, %r11
	rorx	$63, %rsi, %r8
	xorq	%rax, %r8
	xorq	%rsi, %rcx
	rorx	$63, %rdi, %rsi
	xorq	%r8, %rdi
	rorx	$28, %r8, %r13
	rorx	$20, %r11, %r12
	rorx	$61, %r8, %r14
	rorx	$23, %r8, %r15
	movq	%r14, -80(%rsp)
	rorx	$46, %r8, %r8
	rorx	$21, %rcx, %r14
	movq	%r8, -24(%rsp)
	xorq	%r11, %rbx
	rorx	$63, %rax, %r10
	xorq	%r9, %r10
	movq	%r15, -16(%rsp)
	rorx	$54, %r11, %r15
	xorq	%rcx, %r9
	xorq	%rdx, %rsi
	movq	%r15, -8(%rsp)
	andn	%r14, %r12, %r15
	xorq	%rdi, %r15
	rorx	$63, %rbx, %rbp
	xorq	$1, %r15
	movq	%rbp, -32(%rsp)
	rorx	$44, %rsi, %rbx
	xorq	%r10, %rdx
	movq	%r15, -120(%rsp)
	xorq	%rsi, %rax
	rorx	$36, %rdx, %rdx
	movabsq	$-9223372036854775808, %r8
	xorq	%r11, %r8
	rorx	$62, %r11, %r11
	movq	%r11, 8(%rsp)
	rorx	$49, %rcx, %r11
	rorx	$19, %r8, %rbp
	rorx	$2, %r9, %r8
	rorx	$58, %rcx, %r9
	rorx	$3, %rcx, %rcx
	movq	%rcx, -56(%rsp)
	rorx	$43, %r10, %rcx
	andn	%rcx, %r14, %r15
	xorq	%r12, %r15
	movq	%rbp, -64(%rsp)
	rorx	$9, %r10, %rbp
	rorx	$37, %rax, %rax
	movq	%r11, (%rsp)
	rorx	$39, %r10, %r11
	movq	%r8, 16(%rsp)
	rorx	$8, %r10, %r8
	rorx	$25, %rsi, %r10
	movq	%r15, -112(%rsp)
	movq	%r10, 24(%rsp)
	rorx	$56, %rsi, %r10
	rorx	$50, %rsi, %rsi
	andn	%rsi, %rcx, %r15
	xorq	%r14, %r15
	andn	%rdi, %rsi, %r14
	andn	%r12, %rdi, %rdi
	xorq	%rcx, %r14
	xorq	%rsi, %rdi
	movq	%r14, -96(%rsp)
	movq	-64(%rsp), %r14
	movq	%rdi, -88(%rsp)
	movq	-80(%rsp), %rdi
	movq	-32(%rsp), %rcx
	movq	%r15, -104(%rsp)
	andn	%rdi, %rbx, %rsi
	xorq	%rdx, %rsi
	andn	%r14, %rdi, %r12
	xorq	%rbx, %r12
	movq	%r12, -64(%rsp)
	movq	-56(%rsp), %r12
	movq	%rsi, -80(%rsp)
	movq	(%rsp), %r15
	andn	%r12, %r14, %rsi
	xorq	%rsi, %rdi
	andn	%rdx, %r12, %rsi
	andn	%rbx, %rdx, %rdx
	xorq	%rdx, %r12
	movq	-24(%rsp), %rbx
	andn	%r11, %r9, %rdx
	xorq	%rsi, %r14
	movq	%r12, -40(%rsp)
	movq	%rcx, %r12
	movq	-8(%rsp), %rsi
	xorq	%rdx, %r12
	andn	%r10, %r11, %rdx
	xorq	%r9, %rdx
	movq	%rdi, -56(%rsp)
	movq	%rdx, -32(%rsp)
	andn	%rbx, %r10, %rdx
	xorq	%rdx, %r11
	andn	%rcx, %rbx, %rdx
	xorq	%r10, %rdx
	movq	%r14, -48(%rsp)
	movq	24(%rsp), %r14
	movq	%rdx, -24(%rsp)
	andn	%r9, %rcx, %rdx
	xorq	%rdx, %rbx
	andn	%r8, %r15, %rcx
	movq	%rbx, %r10
	andn	%rsi, %r13, %rdx
	andn	%r15, %rsi, %rbx
	xorq	%rcx, %rsi
	andn	%rax, %r8, %rcx
	xorq	%rcx, %r15
	xorq	%rax, %rdx
	xorq	%r13, %rbx
	andn	%r13, %rax, %rax
	movq	%r15, (%rsp)
	movq	16(%rsp), %r15
	xorq	%rax, %r8
	movq	8(%rsp), %r9
	movq	-16(%rsp), %r13
	andn	%r14, %rbp, %rdi
	movq	%rsi, -8(%rsp)
	xorq	%r15, %rdi
	movq	%r10, -16(%rsp)
	andn	%r13, %r14, %rax
	xorq	%rbp, %rax
	andn	%r9, %r13, %rcx
	xorq	%rcx, %r14
	andn	%r15, %r9, %rcx
	xorq	%rcx, %r13
	andn	%rbp, %r15, %rcx
	movq	%r9, %rbp
	movq	-104(%rsp), %r9
	xorq	%rcx, %rbp
	movq	%r14, 8(%rsp)
	movq	-112(%rsp), %rcx
	xorq	-32(%rsp), %rcx
	movq	%rbp, 24(%rsp)
	xorq	%r11, %r9
	movq	-80(%rsp), %rbp
	movq	%rcx, %r15
	movq	%r13, 16(%rsp)
	movq	%r9, %r14
	xorq	%rbx, %r15
	movq	-96(%rsp), %r13
	xorq	-48(%rsp), %r13
	xorq	%rsi, %r14
	movq	-88(%rsp), %rsi
	xorq	-40(%rsp), %rsi
	xorq	%r12, %rbp
	xorq	%r10, %rsi
	xorq	%rax, %r15
	xorq	-56(%rsp), %r14
	xorq	-64(%rsp), %r15
	xorq	8(%rsp), %r14
	xorq	(%rsp), %r13
	xorq	%r8, %rsi
	xorq	%rdi, %rbp
	xorq	24(%rsp), %rsi
	xorq	16(%rsp), %r13
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	-24(%rsp), %r13
	xorq	%rsi, %r9
	xorq	-120(%rsp), %rbp
	rorx	$63, %rsi, %rsi
	rorx	$63, %r13, %r10
	xorq	%r14, %rsi
	xorq	%r15, %r10
	movq	-80(%rsp), %r14
	movq	-120(%rsp), %r15
	xorq	%rdx, %rbp
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%r13, %rbp
	xorq	%r9, %r15
	xorq	%r9, %r14
	xorq	%r9, %r12
	xorq	%r9, %rdx
	rorx	$28, %r14, %r14
	xorq	%rcx, %rax
	xorq	%r9, %rdi
	xorq	%r10, %r11
	movq	%r14, 32(%rsp)
	rorx	$61, %r12, %r14
	rorx	$23, %rdx, %r12
	rorx	$46, %rdi, %r9
	movq	-112(%rsp), %rdx
	movq	%r15, -120(%rsp)
	xorq	%rcx, %rbx
	xorq	%rbp, %r8
	movq	%r14, 40(%rsp)
	rorx	$21, %r11, %r14
	rorx	$19, %rbx, %rbx
	rorx	$56, %r8, %r8
	xorq	%rcx, %rdx
	movq	%r12, 48(%rsp)
	rorx	$63, %rdx, %rdi
	movq	%r9, 56(%rsp)
	movq	%rdi, 64(%rsp)
	movq	-104(%rsp), %r15
	rorx	$62, %rax, %rdi
	movq	-64(%rsp), %r12
	movq	-8(%rsp), %rax
	movq	%rdi, 80(%rsp)
	movq	(%rsp), %r13
	movq	-56(%rsp), %rdi
	xorq	%r10, %r15
	xorq	%r10, %rax
	xorq	%rcx, %r12
	movq	-32(%rsp), %rdx
	movq	-24(%rsp), %r11
	xorq	%r10, %rdi
	xorq	%rsi, %r13
	xorq	8(%rsp), %r10
	rorx	$20, %r12, %r12
	rorx	$2, %r15, %r15
	rorx	$43, %r13, %r13
	xorq	%rsi, %r11
	xorq	%rcx, %rdx
	movq	%r13, -104(%rsp)
	rorx	$39, %r11, %r9
	rorx	$54, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	movq	-40(%rsp), %r11
	movq	-16(%rsp), %rcx
	movq	%r15, -112(%rsp)
	rorx	$49, %rax, %r15
	rorx	$3, %r10, %rax
	movq	%r15, -8(%rsp)
	andn	%r14, %r12, %r15
	xorq	-120(%rsp), %r15
	movq	%rax, -32(%rsp)
	movq	-48(%rsp), %rax
	movq	%r15, %r13
	xorq	%rbp, %r11
	xorq	$32898, %r13
	movq	%rdx, 72(%rsp)
	xorq	%rbp, %rcx
	movq	-96(%rsp), %rdx
	xorq	%rsi, %rax
	movq	%r13, -96(%rsp)
	rorx	$44, %r11, %r11
	rorx	$25, %rcx, %rcx
	rorx	$9, %rax, %r10
	andn	-104(%rsp), %r14, %r13
	movq	-88(%rsp), %rax
	xorq	%r12, %r13
	movq	%r13, -88(%rsp)
	movq	-104(%rsp), %r13
	xorq	%rsi, %rdx
	xorq	%rbp, %rax
	xorq	24(%rsp), %rbp
	xorq	16(%rsp), %rsi
	rorx	$36, %rdx, %rdx
	rorx	$50, %rbp, %rbp
	andn	%rbp, %r13, %r15
	xorq	%r14, %r15
	rorx	$8, %rsi, %rsi
	movq	%r15, -104(%rsp)
	movq	-120(%rsp), %r15
	rorx	$37, %rax, %rax
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r12
	xorq	%rbp, %r12
	movq	%r14, -120(%rsp)
	movq	40(%rsp), %r14
	movq	%r12, -80(%rsp)
	andn	%r14, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%rbp, -64(%rsp)
	andn	%rbx, %r14, %rbp
	xorq	%r11, %rbp
	movq	%rbp, -56(%rsp)
	movq	-32(%rsp), %r13
	movq	-8(%rsp), %r15
	movq	72(%rsp), %r12
	andn	%r13, %rbx, %rbp
	xorq	%rbp, %r14
	andn	%rdx, %r13, %rbp
	xorq	%rbx, %rbp
	movq	%rbp, -48(%rsp)
	movq	64(%rsp), %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r13
	movq	56(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r13, -40(%rsp)
	movq	%rbp, %r11
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%rdx, %r8
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%r15, %r12, %rdi
	movq	%r9, -24(%rsp)
	movq	%rbp, %rbx
	andn	%r12, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r15, %rdi
	xorq	%rdi, %r12
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %r15
	andn	%rbp, %rax, %rax
	movq	48(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r15, -8(%rsp)
	movq	80(%rsp), %r15
	andn	%rcx, %r10, %rdi
	movq	%rax, (%rsp)
	andn	%rbp, %rcx, %rax
	xorq	%r10, %rax
	xorq	-112(%rsp), %rdi
	andn	%r15, %rbp, %rsi
	xorq	%rcx, %rsi
	movq	%r12, -16(%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r15, %rsi
	movq	-112(%rsp), %r15
	movq	%r14, -112(%rsp)
	xorq	-32(%rsp), %r14
	andn	%r15, %rsi, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %r15, %rcx
	xorq	%rcx, %rsi
	movq	%rsi, %r10
	movq	%rbp, 16(%rsp)
	movq	-88(%rsp), %rsi
	xorq	%r12, %r14
	xorq	-56(%rsp), %rsi
	movq	-64(%rsp), %rbp
	movq	%rsi, %r15
	movq	(%rsp), %rsi
	movq	-120(%rsp), %r12
	xorq	%r11, %rbp
	xorq	%rbx, %r15
	xorq	-48(%rsp), %r12
	xorq	8(%rsp), %r14
	xorq	%rdx, %rbp
	xorq	-104(%rsp), %r14
	xorq	-96(%rsp), %rbp
	xorq	%rax, %r15
	xorq	%r8, %r12
	xorq	%r9, %rsi
	xorq	16(%rsp), %r12
	xorq	-8(%rsp), %r12
	xorq	-80(%rsp), %rsi
	xorq	%r13, %r15
	xorq	%rdi, %rbp
	movq	%r10, 24(%rsp)
	xorq	%r10, %rsi
	xorq	-40(%rsp), %rsi
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	%rsi, %r9
	rorx	$63, %r12, %r10
	xorq	%rbp, %rcx
	xorq	%r15, %r10
	movq	-96(%rsp), %r15
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%rcx, %rax
	rorx	$62, %rax, %rax
	movq	%rax, 72(%rsp)
	movq	-104(%rsp), %rax
	xorq	%rcx, %r13
	xorq	%r9, %r15
	xorq	%rcx, %rbx
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	%r15, -96(%rsp)
	movq	-64(%rsp), %r15
	xorq	%r10, %rax
	xorq	%rsi, %r8
	movq	-32(%rsp), %r14
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r9, %r11
	xorq	%r9, %r15
	rorx	$61, %r11, %r11
	rorx	$39, %r8, %r9
	movq	%r11, -64(%rsp)
	rorx	$28, %r15, %r15
	xorq	%r10, %r14
	movq	%r15, 32(%rsp)
	rorx	$23, %rdx, %r15
	rorx	$46, %rdi, %rdx
	movq	%rdx, 48(%rsp)
	movq	-88(%rsp), %rdx
	rorx	$21, %r14, %r14
	movq	%r15, 40(%rsp)
	movq	-40(%rsp), %r11
	rorx	$19, %rbx, %rbx
	xorq	%rcx, %rdx
	movq	(%rsp), %r8
	rorx	$63, %rdx, %rdi
	rorx	$2, %rax, %rdx
	movq	%rdi, 56(%rsp)
	movq	-16(%rsp), %rax
	movq	-56(%rsp), %rdi
	movq	%rdx, -104(%rsp)
	xorq	%rbp, %r11
	xorq	%rbp, %r8
	xorq	%r10, %rax
	movq	-120(%rsp), %rdx
	rorx	$44, %r11, %r11
	rorx	$56, %r8, %r8
	xorq	%rcx, %rdi
	rorx	$49, %rax, %rax
	movq	-80(%rsp), %rcx
	movq	%rax, -16(%rsp)
	rorx	$20, %rdi, %r12
	movq	-48(%rsp), %rax
	rorx	$54, %r13, %rdi
	xorq	%rsi, %rdx
	movq	%rdi, 64(%rsp)
	movq	-112(%rsp), %rdi
	xorq	%rbp, %rcx
	rorx	$36, %rdx, %rdx
	xorq	%rsi, %rax
	movq	-8(%rsp), %r13
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	rorx	$3, %r10, %r15
	rorx	$9, %rax, %r10
	rorx	$37, %rcx, %rax
	xorq	%rsi, %r13
	movq	-24(%rsp), %rcx
	xorq	16(%rsp), %rsi
	rorx	$43, %r13, %r13
	rorx	$58, %rdi, %rdi
	movq	%r15, -32(%rsp)
	rorx	$8, %rsi, %r15
	movabsq	$-9223372036854742902, %rsi
	xorq	%rbp, %rcx
	movq	%r15, -8(%rsp)
	xorq	24(%rsp), %rbp
	andn	%r14, %r12, %r15
	xorq	-96(%rsp), %r15
	rorx	$50, %rbp, %rbp
	rorx	$25, %rcx, %rcx
	xorq	%r15, %rsi
	movq	-96(%rsp), %r15
	movq	%rsi, -120(%rsp)
	andn	%r13, %r14, %rsi
	xorq	%r12, %rsi
	movq	%rsi, -112(%rsp)
	andn	%rbp, %r13, %rsi
	xorq	%r14, %rsi
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-64(%rsp), %r12
	xorq	%rbp, %r13
	movq	-32(%rsp), %r15
	movq	%r13, -80(%rsp)
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%rsi, -88(%rsp)
	movq	-16(%rsp), %rsi
	movq	%rbp, -64(%rsp)
	andn	%rbx, %r12, %rbp
	movq	%rbp, %r13
	andn	%r15, %rbx, %rbp
	xorq	%r11, %r13
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	andn	%r11, %rdx, %rdx
	movq	%r13, -56(%rsp)
	movq	%rbp, %r13
	movq	56(%rsp), %rbp
	xorq	%rdx, %r15
	xorq	%rbx, %r13
	movq	48(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r14, -96(%rsp)
	movq	%rbp, %r11
	movq	%r13, -48(%rsp)
	movq	64(%rsp), %r14
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	-8(%rsp), %r15
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%rdx, %r8
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	movq	%rbx, %r9
	andn	%rsi, %r14, %rdi
	xorq	%rdx, %r9
	movq	%rbp, %rbx
	andn	%r14, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%r15, %rsi, %rdi
	xorq	%rdi, %r14
	andn	%rax, %r15, %rdi
	xorq	%rdi, %rsi
	andn	%rbp, %rax, %rdi
	movq	40(%rsp), %rbp
	xorq	%r15, %rdi
	movq	72(%rsp), %r15
	movq	%rsi, -8(%rsp)
	andn	%rbp, %rcx, %rax
	movq	%rdi, (%rsp)
	andn	%rcx, %r10, %rdi
	xorq	%r10, %rax
	andn	%r15, %rbp, %rsi
	xorq	%rcx, %rsi
	xorq	-104(%rsp), %rdi
	movq	%rsi, 8(%rsp)
	movq	-104(%rsp), %rsi
	andn	%rsi, %r15, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %rsi, %rcx
	xorq	%rcx, %r15
	movq	%rbp, 16(%rsp)
	movq	-64(%rsp), %rbp
	movq	%r15, 24(%rsp)
	xorq	%r11, %rbp
	xorq	%rdx, %rbp
	xorq	%rdi, %rbp
	xorq	-120(%rsp), %rbp
	movq	-112(%rsp), %rcx
	movq	%r14, -16(%rsp)
	movq	-32(%rsp), %r10
	xorq	-56(%rsp), %rcx
	movq	%r12, -104(%rsp)
	movq	%rcx, %r15
	movq	-80(%rsp), %rsi
	movq	%r9, -24(%rsp)
	xorq	%r14, %r10
	movq	8(%rsp), %r14
	xorq	%rax, %r15
	xorq	%r13, %r15
	xorq	%r10, %r14
	xorq	-88(%rsp), %r14
	xorq	%rbx, %r15
	xorq	%r12, %r14
	movq	-96(%rsp), %r12
	xorq	-48(%rsp), %r12
	xorq	%r8, %r12
	xorq	-8(%rsp), %r12
	xorq	16(%rsp), %r12
	rorx	$63, %r14, %rcx
	xorq	(%rsp), %rsi
	xorq	24(%rsp), %rsi
	xorq	%rbp, %rcx
	rorx	$63, %r12, %r10
	xorq	%rcx, %rax
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r15, %r10
	xorq	-40(%rsp), %rsi
	xorq	%rcx, %r13
	xorq	%rcx, %rbx
	xorq	%r9, %rsi
	rorx	$63, %r15, %r9
	movq	-120(%rsp), %r15
	rorx	$19, %rbx, %rbx
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-64(%rsp), %r14
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%r9, %r15
	xorq	%r9, %r11
	xorq	%r9, %r14
	movq	%r15, -120(%rsp)
	rorx	$61, %r11, %r11
	xorq	%rsi, %r8
	rorx	$28, %r14, %r14
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$46, %rdi, %rdx
	movq	-56(%rsp), %rdi
	movq	%rdx, 48(%rsp)
	rorx	$39, %r8, %r9
	movq	-112(%rsp), %rdx
	movq	%r11, -64(%rsp)
	xorq	%rcx, %rdi
	movq	%r14, 40(%rsp)
	rorx	$54, %r13, %r14
	rorx	$20, %rdi, %r12
	rorx	$62, %rax, %rdi
	movq	-88(%rsp), %rax
	xorq	%rcx, %rdx
	movq	%rdi, 64(%rsp)
	rorx	$63, %rdx, %r15
	xorq	%r10, %rax
	movq	%r15, 56(%rsp)
	rorx	$2, %rax, %rdi
	movq	-32(%rsp), %rax
	movq	%r14, -56(%rsp)
	movq	%rdi, 72(%rsp)
	movq	-104(%rsp), %rdi
	xorq	%r10, %rax
	rorx	$21, %rax, %r14
	movq	-16(%rsp), %rax
	xorq	%r10, %rdi
	movq	-24(%rsp), %rcx
	movq	-96(%rsp), %rdx
	movq	-40(%rsp), %r11
	rorx	$58, %rdi, %rdi
	xorq	%r10, %rax
	xorq	8(%rsp), %r10
	movq	-8(%rsp), %r13
	xorq	%rbp, %rcx
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	rorx	$3, %r10, %r15
	movq	(%rsp), %r8
	movq	-48(%rsp), %rax
	movq	%r15, -32(%rsp)
	xorq	%rsi, %rdx
	xorq	%rsi, %r13
	xorq	%rbp, %r11
	rorx	$25, %rcx, %rcx
	movq	%rcx, -24(%rsp)
	rorx	$43, %r13, %r13
	xorq	%rsi, %rax
	xorq	16(%rsp), %rsi
	rorx	$44, %r11, %r11
	rorx	$36, %rdx, %rdx
	rorx	$9, %rax, %r10
	movq	-80(%rsp), %rax
	rorx	$8, %rsi, %rsi
	movabsq	$-9223372034707259392, %rcx
	xorq	%rbp, %rax
	xorq	%rbp, %r8
	andn	%r14, %r12, %r15
	xorq	-120(%rsp), %r15
	xorq	%r15, %rcx
	movq	-120(%rsp), %r15
	xorq	24(%rsp), %rbp
	rorx	$56, %r8, %r8
	movq	%rcx, -112(%rsp)
	andn	%r13, %r14, %rcx
	xorq	%r12, %rcx
	rorx	$50, %rbp, %rbp
	movq	%rcx, -104(%rsp)
	andn	%rbp, %r13, %rcx
	xorq	%r14, %rcx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-64(%rsp), %r12
	xorq	%rbp, %r13
	movq	-32(%rsp), %r15
	movq	%r13, -88(%rsp)
	rorx	$37, %rax, %rax
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%rcx, -96(%rsp)
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	movq	%rbp, %r13
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	movq	%r15, -40(%rsp)
	movq	56(%rsp), %r15
	xorq	%r11, %r13
	xorq	%rbx, %rbp
	movq	48(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r13, -64(%rsp)
	movq	%r15, %r11
	movq	%rbp, -48(%rsp)
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%r14, -120(%rsp)
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%r15, %rbx, %rdx
	xorq	%rdx, %r8
	andn	%rdi, %r15, %rdx
	movq	32(%rsp), %r15
	xorq	%rdx, %r9
	movq	%r9, 48(%rsp)
	movq	-56(%rsp), %r14
	movq	-16(%rsp), %rcx
	movq	%r15, %rbx
	movq	40(%rsp), %rbp
	movq	%r12, -56(%rsp)
	andn	%r14, %r15, %rdx
	xorq	%rax, %rdx
	andn	%rcx, %r14, %rdi
	xorq	%rdi, %rbx
	andn	%rsi, %rcx, %rdi
	xorq	%rdi, %r14
	andn	%rax, %rsi, %rdi
	andn	%r15, %rax, %rax
	xorq	%rsi, %rax
	xorq	%rdi, %rcx
	movq	-24(%rsp), %rsi
	movq	64(%rsp), %r15
	movq	%rcx, -8(%rsp)
	movq	72(%rsp), %rcx
	movq	%rax, (%rsp)
	movq	%rsi, %r9
	andn	%rsi, %r10, %rdi
	andn	%rbp, %rsi, %rax
	andn	%r15, %rbp, %rsi
	xorq	%r9, %rsi
	xorq	%rcx, %rdi
	xorq	%r10, %rax
	movq	%r14, -16(%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r15, %rsi
	movq	%rcx, %r15
	andn	%rcx, %rsi, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %r15, %rcx
	movq	-104(%rsp), %r10
	xorq	-64(%rsp), %r10
	movq	%rbp, 16(%rsp)
	xorq	%rcx, %rsi
	movq	%r10, %r15
	movq	-32(%rsp), %r10
	movq	-80(%rsp), %rbp
	movq	%rsi, %r9
	xorq	%rax, %r15
	movq	-88(%rsp), %rcx
	movq	%r9, 24(%rsp)
	xorq	%r14, %r10
	movq	8(%rsp), %r14
	xorq	%r11, %rbp
	xorq	%r13, %r15
	xorq	%rdx, %rbp
	xorq	%rbx, %r15
	xorq	%r10, %r14
	xorq	-96(%rsp), %r14
	xorq	%rdi, %rbp
	xorq	-112(%rsp), %rbp
	xorq	%r12, %r14
	xorq	(%rsp), %rcx
	movq	-120(%rsp), %r12
	movq	%rcx, %rsi
	movq	48(%rsp), %rcx
	xorq	-48(%rsp), %r12
	xorq	%r9, %rsi
	xorq	-40(%rsp), %rsi
	xorq	%r8, %r12
	xorq	-8(%rsp), %r12
	xorq	%rcx, %rsi
	xorq	16(%rsp), %r12
	movq	%rcx, -24(%rsp)
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	%rsi, %r9
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	movq	-112(%rsp), %r15
	movq	-80(%rsp), %r14
	xorq	%rbp, %rcx
	xorq	%rsi, %r8
	xorq	%rcx, %rax
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%rcx, %r13
	xorq	%r9, %r15
	xorq	%r9, %r14
	xorq	%r9, %r11
	xorq	%rcx, %rbx
	rorx	$28, %r14, %r14
	rorx	$39, %r8, %r9
	rorx	$61, %r11, %r11
	rorx	$19, %rbx, %rbx
	movq	%r15, -112(%rsp)
	rorx	$62, %rax, %r15
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$46, %rdi, %rdx
	movq	-96(%rsp), %rax
	movq	%rdx, 56(%rsp)
	movq	-104(%rsp), %rdx
	xorq	%r10, %rax
	movq	%r14, 48(%rsp)
	rorx	$54, %r13, %r14
	movq	-8(%rsp), %r13
	xorq	%rcx, %rdx
	movq	%r14, 72(%rsp)
	movq	(%rsp), %r8
	rorx	$63, %rdx, %rdi
	movq	%rdi, 64(%rsp)
	movq	-64(%rsp), %rdi
	movq	-120(%rsp), %rdx
	movq	%r15, 80(%rsp)
	xorq	%rcx, %rdi
	movq	%r11, 40(%rsp)
	movq	-24(%rsp), %rcx
	rorx	$20, %rdi, %r12
	rorx	$2, %rax, %rdi
	movq	-32(%rsp), %rax
	xorq	%rsi, %rdx
	movq	%rdi, -104(%rsp)
	movq	-56(%rsp), %rdi
	rorx	$36, %rdx, %rdx
	xorq	%r10, %rax
	movq	-40(%rsp), %r11
	rorx	$21, %rax, %r14
	movq	-16(%rsp), %rax
	xorq	%r10, %rdi
	rorx	$58, %rdi, %rdi
	xorq	%r10, %rax
	xorq	8(%rsp), %r10
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	rorx	$3, %r10, %r15
	movq	%r15, -32(%rsp)
	xorq	%rsi, %rax
	xorq	%rsi, %r13
	xorq	16(%rsp), %rsi
	xorq	%rbp, %r11
	rorx	$8, %rsi, %r15
	movq	%r15, -8(%rsp)
	andn	%r14, %r12, %r15
	rorx	$9, %rax, %r10
	xorq	-112(%rsp), %r15
	movq	-88(%rsp), %rax
	xorq	%rbp, %rcx
	xorq	%rbp, %r8
	movq	%r15, %rsi
	rorx	$43, %r13, %r13
	rorx	$44, %r11, %r11
	rorx	$56, %r8, %r8
	movq	-112(%rsp), %r15
	xorq	$32907, %rsi
	xorq	%rbp, %rax
	xorq	24(%rsp), %rbp
	movq	%rsi, -120(%rsp)
	andn	%r13, %r14, %rsi
	xorq	%r12, %rsi
	rorx	$50, %rbp, %rbp
	movq	%rsi, -96(%rsp)
	andn	%rbp, %r13, %rsi
	xorq	%r14, %rsi
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	xorq	%rbp, %r13
	movq	%rsi, -88(%rsp)
	movq	%r14, -112(%rsp)
	rorx	$37, %rax, %rax
	rorx	$25, %rcx, %rcx
	movq	%r13, -80(%rsp)
	movq	40(%rsp), %r12
	movq	-32(%rsp), %r15
	movq	-16(%rsp), %rsi
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	72(%rsp), %r14
	movq	%rbp, -64(%rsp)
	andn	%rbx, %r12, %rbp
	movq	%rbp, %r13
	andn	%r15, %rbx, %rbp
	xorq	%r11, %r13
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	andn	%r11, %rdx, %rdx
	movq	%r13, -56(%rsp)
	movq	%rbp, %r13
	movq	64(%rsp), %rbp
	xorq	%rdx, %r15
	xorq	%rbx, %r13
	movq	56(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	%rbp, %r11
	movq	%r13, -48(%rsp)
	movq	-8(%rsp), %r15
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%rdx, %r8
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%rsi, %r14, %rdi
	movq	%rbp, %rbx
	andn	%r14, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%r15, %rsi, %rdi
	xorq	%rdi, %r14
	andn	%rax, %r15, %rdi
	andn	%rbp, %rax, %rax
	movq	48(%rsp), %rbp
	xorq	%r15, %rax
	movq	80(%rsp), %r15
	xorq	%rdi, %rsi
	movq	%rax, (%rsp)
	andn	%rcx, %r10, %rdi
	xorq	-104(%rsp), %rdi
	movq	%rsi, -8(%rsp)
	andn	%r15, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%rbp, %rcx, %rax
	movq	%rsi, 8(%rsp)
	movq	-104(%rsp), %rsi
	xorq	%r10, %rax
	movq	%r14, -16(%rsp)
	andn	%rsi, %r15, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %rsi, %rcx
	xorq	%rcx, %r15
	movq	-96(%rsp), %rcx
	movq	-32(%rsp), %r10
	movq	%rbp, 16(%rsp)
	movq	-64(%rsp), %rbp
	movq	%r15, 24(%rsp)
	movq	-56(%rsp), %r15
	xorq	%rax, %rcx
	movq	%r12, -104(%rsp)
	xorq	%r11, %rbp
	xorq	%rdx, %rbp
	xorq	%rcx, %r15
	xorq	%rdi, %rbp
	xorq	-120(%rsp), %rbp
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-88(%rsp), %r14
	xorq	%rbx, %r15
	xorq	%r10, %r14
	xorq	%r12, %r14
	movq	-112(%rsp), %r12
	xorq	8(%rsp), %r14
	xorq	-48(%rsp), %r12
	movq	-80(%rsp), %rsi
	movq	%r9, -24(%rsp)
	rorx	$63, %r14, %rcx
	xorq	(%rsp), %rsi
	xorq	24(%rsp), %rsi
	xorq	%r8, %r12
	xorq	%rbp, %rcx
	xorq	-40(%rsp), %rsi
	xorq	-8(%rsp), %r12
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	xorq	16(%rsp), %r12
	xorq	%r9, %rsi
	rorx	$63, %r15, %r9
	rorx	$63, %rbp, %rbp
	xorq	%rsi, %r9
	rorx	$63, %r12, %r10
	rorx	$63, %rsi, %rsi
	xorq	%r15, %r10
	xorq	%r14, %rsi
	movq	-120(%rsp), %r15
	movq	-64(%rsp), %r14
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%r12, %rbp
	xorq	%r9, %r11
	xorq	%rcx, %rbx
	xorq	%r9, %r15
	xorq	%r9, %r14
	rorx	$61, %r11, %r11
	movq	%r11, -64(%rsp)
	movq	%r15, -120(%rsp)
	rorx	$28, %r14, %r15
	movq	%r8, %r9
	movq	-32(%rsp), %r14
	movq	%r15, 32(%rsp)
	rorx	$23, %rdx, %r15
	rorx	$46, %rdi, %rdx
	rorx	$19, %rbx, %rbx
	movq	%rdx, 48(%rsp)
	movq	-96(%rsp), %rdx
	xorq	%r10, %r14
	movq	%r15, 40(%rsp)
	rorx	$21, %r14, %r14
	xorq	%rcx, %rdx
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	movq	-56(%rsp), %rdi
	movq	-112(%rsp), %rdx
	xorq	%rcx, %rdi
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	-88(%rsp), %rax
	movq	%rdi, -56(%rsp)
	movq	-104(%rsp), %rdi
	xorq	%r10, %rax
	movq	%r13, 64(%rsp)
	movq	-8(%rsp), %r13
	rorx	$2, %rax, %r11
	movq	-16(%rsp), %rax
	xorq	%r10, %rdi
	movq	%r11, 72(%rsp)
	rorx	$58, %rdi, %rdi
	xorq	%r10, %rax
	xorq	8(%rsp), %r10
	xorq	%rsi, %rdx
	xorq	%rsi, %r9
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	xorq	%rsi, %r13
	rorx	$3, %r10, %r15
	rorx	$43, %r13, %r13
	rorx	$36, %rdx, %rdx
	rorx	$39, %r9, %r9
	xorq	%rsi, %rax
	movq	%r15, -32(%rsp)
	xorq	16(%rsp), %rsi
	andn	%r14, %r12, %r15
	rorx	$9, %rax, %r10
	movq	-80(%rsp), %rax
	movq	-24(%rsp), %rcx
	rorx	$8, %rsi, %rsi
	movq	-40(%rsp), %r11
	movq	(%rsp), %r8
	xorq	%rbp, %rcx
	xorq	-120(%rsp), %r15
	xorq	%rbp, %rax
	xorq	%rbp, %r11
	xorq	%rbp, %r8
	rorx	$25, %rcx, %rcx
	xorq	24(%rsp), %rbp
	rorx	$50, %rbp, %rbp
	rorx	$44, %r11, %r11
	rorx	$56, %r8, %r8
	rorx	$37, %rax, %rax
	movq	%rcx, 8(%rsp)
	movl	$2147483649, %ecx
	xorq	%r15, %rcx
	andn	%rbp, %r13, %r15
	xorq	%r14, %r15
	movq	%r15, -96(%rsp)
	movq	-120(%rsp), %r15
	movq	%rcx, -112(%rsp)
	andn	%r13, %r14, %rcx
	xorq	%r12, %rcx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-64(%rsp), %r12
	movq	-32(%rsp), %r15
	xorq	%rbp, %r13
	movq	%rcx, -104(%rsp)
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%r13, -88(%rsp)
	movq	-56(%rsp), %rcx
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	movq	%rbp, %r13
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	xorq	%rbx, %rbp
	xorq	%r11, %r13
	movq	%rbp, -48(%rsp)
	movq	56(%rsp), %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	movq	48(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r13, -64(%rsp)
	movq	%rbp, %r11
	movq	%r14, -120(%rsp)
	movq	64(%rsp), %r14
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%r8, %rdx
	movq	-16(%rsp), %r8
	movq	%rdx, -24(%rsp)
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%r8, %rcx, %rdi
	movq	72(%rsp), %r15
	movq	%rbp, %rbx
	andn	%rcx, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rcx
	andn	%rax, %rsi, %rdi
	movq	%rcx, -8(%rsp)
	andn	%rbp, %rax, %rax
	movq	8(%rsp), %rcx
	xorq	%rdi, %r8
	movq	40(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r8, (%rsp)
	andn	%rcx, %r10, %rdi
	movq	%rax, %r8
	xorq	%r15, %rdi
	andn	%rbp, %rcx, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r10, %r15, %rcx
	xorq	%r10, %rax
	movq	%rbp, %rsi
	movq	-80(%rsp), %rbp
	movq	-96(%rsp), %r10
	xorq	%rcx, %r14
	movq	%r12, -56(%rsp)
	movq	-104(%rsp), %r15
	xorq	%r11, %rbp
	movq	%rsi, 16(%rsp)
	xorq	%rdx, %rbp
	xorq	%r12, %r10
	movq	-120(%rsp), %r12
	xorq	-48(%rsp), %r12
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	movq	%r14, 24(%rsp)
	xorq	%rdi, %rbp
	xorq	%rsi, %r12
	xorq	-64(%rsp), %r15
	movq	-40(%rsp), %rsi
	movq	%r9, -16(%rsp)
	xorq	%r13, %r15
	movq	-32(%rsp), %r14
	xorq	-112(%rsp), %rbp
	xorq	%r9, %rsi
	xorq	%rbx, %r15
	xorq	-88(%rsp), %rsi
	xorq	%rax, %r15
	xorq	%r10, %r14
	xorq	%r8, %rsi
	xorq	-8(%rsp), %r14
	xorq	24(%rsp), %rsi
	xorq	8(%rsp), %r14
	rorx	$63, %r15, %r9
	rorx	$63, %r12, %r10
	xorq	%rsi, %r9
	rorx	$63, %r14, %rcx
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-112(%rsp), %r14
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%rbp, %rcx
	xorq	%r15, %r10
	xorq	%r9, %r11
	xorq	%rcx, %r13
	rorx	$63, %rbp, %rbp
	xorq	%r9, %r14
	xorq	%r12, %rbp
	rorx	$61, %r11, %r15
	movq	%r14, -112(%rsp)
	movq	-80(%rsp), %r14
	movq	%r15, -80(%rsp)
	xorq	%r9, %r14
	rorx	$28, %r14, %r14
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$46, %rdi, %rdx
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	movq	%r14, 40(%rsp)
	xorq	%rcx, %rdx
	rorx	$63, %rdx, %rdi
	movq	-96(%rsp), %rdx
	movq	%rdi, 56(%rsp)
	movq	-64(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	%rcx, %rbx
	xorq	%rcx, %rax
	xorq	%r10, %rdx
	rorx	$20, %rdi, %r12
	rorx	$2, %rdx, %rdx
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	%rdi, 64(%rsp)
	xorq	%rbp, %r8
	rorx	$19, %rbx, %rbx
	movq	%r13, 72(%rsp)
	rorx	$56, %r8, %r8
	movq	%rdx, 80(%rsp)
	movq	-8(%rsp), %rax
	movq	-32(%rsp), %r15
	movq	-56(%rsp), %rdi
	xorq	%r10, %rax
	movq	-88(%rsp), %r11
	movq	(%rsp), %r13
	rorx	$49, %rax, %rcx
	movq	%rcx, -56(%rsp)
	xorq	%r10, %r15
	movq	-48(%rsp), %rcx
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	rorx	$21, %r15, %r14
	xorq	%rbp, %r11
	xorq	%rsi, %rcx
	rorx	$3, %r10, %r15
	xorq	%rsi, %r13
	movq	%r15, -32(%rsp)
	rorx	$9, %rcx, %r10
	andn	%r14, %r12, %r15
	rorx	$37, %r11, %rax
	rorx	$43, %r13, %r13
	movq	-24(%rsp), %rcx
	xorq	-112(%rsp), %r15
	movq	%rax, -8(%rsp)
	movabsq	$-9223372034707259263, %rax
	xorq	%r15, %rax
	movq	-40(%rsp), %r11
	andn	%r13, %r14, %r15
	xorq	%r12, %r15
	xorq	%rsi, %rcx
	movq	%r15, -104(%rsp)
	movq	-112(%rsp), %r15
	rorx	$58, %rdi, %rdi
	rorx	$39, %rcx, %r9
	movq	-16(%rsp), %rcx
	movq	-120(%rsp), %rdx
	xorq	%rbp, %r11
	movq	%rax, -120(%rsp)
	rorx	$44, %r11, %r11
	xorq	%rbp, %rcx
	xorq	24(%rsp), %rbp
	xorq	%rsi, %rdx
	xorq	16(%rsp), %rsi
	rorx	$50, %rbp, %rbp
	andn	%rbp, %r13, %rax
	xorq	%r14, %rax
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	movq	-32(%rsp), %r15
	xorq	%rbp, %r13
	rorx	$36, %rdx, %rdx
	movq	%rax, -96(%rsp)
	movq	48(%rsp), %rax
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	rorx	$8, %rsi, %rsi
	rorx	$25, %rcx, %rcx
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	movq	%r13, -88(%rsp)
	movq	%rbp, -64(%rsp)
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	movq	%rbp, %r13
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	andn	%r9, %rdi, %rdx
	xorq	%rbx, %r13
	movq	56(%rsp), %rbx
	movq	%r14, -112(%rsp)
	movq	%r13, -48(%rsp)
	movq	%rbx, %r11
	movq	%r15, -40(%rsp)
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rax, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rax, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbx, %rax, %rdx
	xorq	%r8, %rdx
	movq	%rdx, -24(%rsp)
	movq	32(%rsp), %r15
	andn	%rdi, %rbx, %rdx
	xorq	%rdx, %r9
	movq	-8(%rsp), %r14
	movq	-56(%rsp), %r8
	movq	%r12, -56(%rsp)
	movq	64(%rsp), %rax
	movq	%r15, %rbx
	movq	40(%rsp), %rbp
	movq	%r9, -16(%rsp)
	andn	%r8, %rax, %rdi
	andn	%rax, %r15, %rdx
	xorq	%rdi, %rbx
	xorq	%r14, %rdx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rax
	andn	%r14, %rsi, %rdi
	xorq	%rdi, %r8
	andn	%r15, %r14, %rdi
	movq	80(%rsp), %r15
	xorq	%rsi, %rdi
	movq	72(%rsp), %r14
	movq	%rax, -8(%rsp)
	andn	%rbp, %rcx, %rax
	xorq	%r10, %rax
	andn	%r14, %rbp, %rsi
	movq	%r8, (%rsp)
	xorq	%rcx, %rsi
	movq	%rdi, %r8
	andn	%rcx, %r10, %rdi
	xorq	%r15, %rdi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %r15, %rcx
	movq	-96(%rsp), %r10
	xorq	%rcx, %r14
	movq	%rsi, 8(%rsp)
	movq	-104(%rsp), %rcx
	movq	%rbp, %rsi
	xorq	-64(%rsp), %rcx
	movq	%r14, 24(%rsp)
	xorq	%r12, %r10
	movq	-112(%rsp), %r12
	xorq	-48(%rsp), %r12
	movq	%rcx, %r15
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	movq	%rsi, 16(%rsp)
	xorq	%r13, %r15
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	movq	-80(%rsp), %rbp
	xorq	%rbx, %r15
	movq	-32(%rsp), %r14
	xorq	%rax, %r15
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	xorq	%r11, %rbp
	rorx	$63, %r15, %r9
	xorq	%r10, %r14
	xorq	%r8, %rsi
	xorq	-8(%rsp), %r14
	xorq	24(%rsp), %rsi
	xorq	8(%rsp), %r14
	xorq	%rsi, %r9
	xorq	%rdx, %rbp
	rorx	$63, %r12, %r10
	rorx	$63, %r14, %rcx
	xorq	%r15, %r10
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-80(%rsp), %r15
	movq	-120(%rsp), %r14
	xorq	%rdi, %rbp
	xorq	%r9, %r11
	xorq	-120(%rsp), %rbp
	xorq	%rbp, %rcx
	xorq	%r9, %r14
	xorq	%r9, %r15
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	movq	%r14, -120(%rsp)
	rorx	$28, %r15, %r14
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	xorq	%rcx, %rbx
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$46, %rdi, %rdx
	xorq	%rbp, %r8
	movq	%rdx, 48(%rsp)
	rorx	$61, %r11, %r15
	rorx	$19, %rbx, %rbx
	rorx	$56, %r8, %r8
	movq	-104(%rsp), %rdx
	movq	-88(%rsp), %r11
	movq	%r15, -80(%rsp)
	movq	-32(%rsp), %r15
	movq	%r14, 40(%rsp)
	xorq	%rcx, %rdx
	xorq	%rbp, %r11
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	movq	-64(%rsp), %rdi
	xorq	%r10, %r15
	movq	-96(%rsp), %rdx
	rorx	$21, %r15, %r14
	xorq	%rcx, %rdi
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	-8(%rsp), %rax
	movq	%rdi, 64(%rsp)
	movq	-56(%rsp), %rdi
	xorq	%r10, %rdx
	xorq	%r10, %rax
	movq	%r13, 72(%rsp)
	movq	(%rsp), %r13
	rorx	$2, %rdx, %rdx
	rorx	$49, %rax, %rcx
	movq	%rcx, -56(%rsp)
	xorq	%r10, %rdi
	movq	-48(%rsp), %rcx
	xorq	8(%rsp), %r10
	xorq	%rsi, %r13
	rorx	$37, %r11, %rax
	movq	%rax, -8(%rsp)
	xorq	%rsi, %rcx
	rorx	$3, %r10, %r15
	movq	%r15, -32(%rsp)
	movabsq	$-9223372036854743031, %rax
	rorx	$9, %rcx, %r10
	movq	-24(%rsp), %rcx
	andn	%r14, %r12, %r15
	xorq	-120(%rsp), %r15
	xorq	%r15, %rax
	rorx	$43, %r13, %r13
	movq	-40(%rsp), %r11
	andn	%r13, %r14, %r15
	xorq	%rsi, %rcx
	xorq	%r12, %r15
	movq	%rdx, 80(%rsp)
	movq	-112(%rsp), %rdx
	rorx	$39, %rcx, %r9
	movq	-16(%rsp), %rcx
	movq	%r15, -104(%rsp)
	xorq	%rbp, %r11
	movq	-120(%rsp), %r15
	xorq	%rsi, %rdx
	rorx	$44, %r11, %r11
	rorx	$58, %rdi, %rdi
	xorq	%rbp, %rcx
	xorq	24(%rsp), %rbp
	xorq	16(%rsp), %rsi
	rorx	$36, %rdx, %rdx
	rorx	$50, %rbp, %rbp
	movq	%rax, -112(%rsp)
	andn	%rbp, %r13, %rax
	xorq	%r14, %rax
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	xorq	%rbp, %r13
	movq	%rax, -96(%rsp)
	rorx	$8, %rsi, %rsi
	rorx	$25, %rcx, %rcx
	movq	%r14, -120(%rsp)
	movq	%r13, -88(%rsp)
	movq	-80(%rsp), %r12
	movq	-32(%rsp), %r15
	movq	48(%rsp), %rax
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	-8(%rsp), %r14
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	movq	%rbp, -64(%rsp)
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	movq	%rbp, %r13
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	andn	%r9, %rdi, %rdx
	xorq	%rbx, %r13
	movq	56(%rsp), %rbx
	movq	%r15, -40(%rsp)
	movq	32(%rsp), %r15
	movq	40(%rsp), %rbp
	movq	%r13, -48(%rsp)
	movq	%rbx, %r11
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rax, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rax, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbx, %rax, %rdx
	movq	64(%rsp), %rax
	xorq	%r8, %rdx
	movq	-56(%rsp), %r8
	movq	%rdx, -24(%rsp)
	andn	%rdi, %rbx, %rdx
	movq	%r15, %rbx
	xorq	%rdx, %r9
	andn	%rax, %r15, %rdx
	xorq	%r14, %rdx
	movq	%r12, -56(%rsp)
	andn	%r8, %rax, %rdi
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rax
	andn	%r14, %rsi, %rdi
	xorq	%rdi, %r8
	andn	%r15, %r14, %rdi
	movq	80(%rsp), %r15
	movq	72(%rsp), %r14
	xorq	%rsi, %rdi
	movq	%rax, -8(%rsp)
	movq	%r8, (%rsp)
	movq	%rdi, %r8
	andn	%rcx, %r10, %rdi
	xorq	%r15, %rdi
	andn	%rbp, %rcx, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r10, %r15, %rcx
	xorq	%r10, %rax
	movq	%rbp, %rsi
	movq	-80(%rsp), %rbp
	xorq	%rcx, %r14
	movq	-96(%rsp), %r10
	movq	%r14, 24(%rsp)
	movq	-32(%rsp), %r14
	xorq	%r11, %rbp
	xorq	%r12, %r10
	movq	-104(%rsp), %rcx
	movq	-120(%rsp), %r12
	xorq	%rdx, %rbp
	xorq	-64(%rsp), %rcx
	xorq	%r10, %r14
	xorq	-48(%rsp), %r12
	xorq	%rdi, %rbp
	xorq	-8(%rsp), %r14
	xorq	-112(%rsp), %rbp
	movq	%rcx, %r15
	xorq	8(%rsp), %r14
	xorq	-24(%rsp), %r12
	movq	%rsi, 16(%rsp)
	xorq	%r13, %r15
	xorq	(%rsp), %r12
	xorq	%rbx, %r15
	movq	%r9, -16(%rsp)
	rorx	$63, %r14, %rcx
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	xorq	%rax, %r15
	xorq	%rbp, %rcx
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	rorx	$63, %rbp, %rbp
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	rorx	$63, %r15, %r9
	movq	-80(%rsp), %r15
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%rcx, %r13
	movq	-112(%rsp), %r14
	xorq	%r9, %r15
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%rcx, %rax
	xorq	%r12, %rbp
	xorq	%r9, %r11
	xorq	%rcx, %rbx
	xorq	%r9, %r14
	xorq	%rbp, %r8
	rorx	$19, %rbx, %rbx
	movq	%r14, -112(%rsp)
	rorx	$28, %r15, %r14
	rorx	$61, %r11, %r15
	rorx	$56, %r8, %r8
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$46, %rdi, %rdx
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	movq	%r15, -80(%rsp)
	movq	-32(%rsp), %r15
	xorq	%rcx, %rdx
	movq	%r14, 40(%rsp)
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	movq	-64(%rsp), %rdi
	xorq	%r10, %r15
	movq	-96(%rsp), %rdx
	rorx	$21, %r15, %r14
	xorq	%rcx, %rdi
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	-8(%rsp), %rax
	movq	%rdi, 64(%rsp)
	movq	-56(%rsp), %rdi
	xorq	%r10, %rdx
	xorq	%r10, %rax
	movq	%r13, 72(%rsp)
	rorx	$2, %rdx, %rdx
	movq	(%rsp), %r13
	rorx	$49, %rax, %rcx
	movq	%rcx, -56(%rsp)
	movq	-48(%rsp), %rcx
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	movq	%rdx, 80(%rsp)
	xorq	%rsi, %r13
	rorx	$58, %rdi, %rdi
	xorq	%rsi, %rcx
	rorx	$3, %r10, %r15
	movq	-120(%rsp), %rdx
	movq	%r15, -32(%rsp)
	rorx	$9, %rcx, %r10
	movq	-24(%rsp), %rcx
	andn	%r14, %r12, %r15
	rorx	$43, %r13, %r13
	xorq	%rsi, %rdx
	xorq	%rsi, %rcx
	xorq	16(%rsp), %rsi
	movq	-88(%rsp), %r11
	rorx	$36, %rdx, %rdx
	xorq	-112(%rsp), %r15
	rorx	$39, %rcx, %r9
	movq	-16(%rsp), %rcx
	rorx	$8, %rsi, %rsi
	xorq	%rbp, %r11
	xorb	$-118, %r15b
	rorx	$37, %r11, %rax
	movq	-40(%rsp), %r11
	movq	%r15, -120(%rsp)
	xorq	%rbp, %rcx
	movq	-112(%rsp), %r15
	movq	%rax, -8(%rsp)
	andn	%r13, %r14, %rax
	xorq	%r12, %rax
	xorq	%rbp, %r11
	xorq	24(%rsp), %rbp
	movq	%rax, -104(%rsp)
	rorx	$25, %rcx, %rcx
	rorx	$50, %rbp, %rbp
	andn	%rbp, %r13, %rax
	xorq	%r14, %rax
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	movq	-32(%rsp), %r15
	xorq	%rbp, %r13
	rorx	$44, %r11, %r11
	movq	%rax, -96(%rsp)
	movq	48(%rsp), %rax
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%r13, -88(%rsp)
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	movq	%rbp, -64(%rsp)
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	movq	%rbp, %r13
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	andn	%r9, %rdi, %rdx
	xorq	%rbx, %r13
	movq	56(%rsp), %rbx
	movq	%r15, -40(%rsp)
	movq	32(%rsp), %r15
	movq	40(%rsp), %rbp
	movq	%r13, -48(%rsp)
	movq	%rbx, %r11
	movq	%r14, -112(%rsp)
	movq	-8(%rsp), %r14
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rax, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rax, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbx, %rax, %rdx
	movq	64(%rsp), %rax
	xorq	%r8, %rdx
	movq	-56(%rsp), %r8
	movq	%rdx, -24(%rsp)
	andn	%rdi, %rbx, %rdx
	movq	%r15, %rbx
	xorq	%rdx, %r9
	andn	%rax, %r15, %rdx
	xorq	%r14, %rdx
	andn	%r8, %rax, %rdi
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rax
	andn	%r14, %rsi, %rdi
	xorq	%rdi, %r8
	andn	%r15, %r14, %rdi
	movq	80(%rsp), %r15
	movq	72(%rsp), %r14
	xorq	%rsi, %rdi
	movq	%rax, -8(%rsp)
	andn	%rbp, %rcx, %rax
	movq	%r8, (%rsp)
	movq	%rdi, %r8
	andn	%rcx, %r10, %rdi
	xorq	%r10, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %r15, %rcx
	xorq	%rcx, %r14
	movq	%rsi, 8(%rsp)
	movq	%rbp, %rsi
	movq	%r14, 24(%rsp)
	movq	-96(%rsp), %r10
	xorq	%r15, %rdi
	movq	-80(%rsp), %rbp
	movq	-104(%rsp), %rcx
	movq	%r12, -56(%rsp)
	xorq	-64(%rsp), %rcx
	xorq	%r12, %r10
	movq	-112(%rsp), %r12
	movq	%rsi, 16(%rsp)
	xorq	-48(%rsp), %r12
	xorq	-24(%rsp), %r12
	movq	%rcx, %r15
	xorq	%r11, %rbp
	xorq	(%rsp), %r12
	xorq	%r13, %r15
	movq	-32(%rsp), %r14
	xorq	%rdx, %rbp
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	xorq	%rbx, %r15
	xorq	%rdi, %rbp
	xorq	%rax, %r15
	xorq	-120(%rsp), %rbp
	xorq	%r10, %r14
	xorq	-8(%rsp), %r14
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	xorq	8(%rsp), %r14
	rorx	$63, %r12, %r10
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	movq	%r9, -16(%rsp)
	xorq	%r15, %r10
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-120(%rsp), %r14
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r9, %r14
	xorq	%rcx, %rbx
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	movq	%r14, 32(%rsp)
	movq	-80(%rsp), %r14
	rorx	$19, %rbx, %rbx
	xorq	%rbp, %r8
	movq	%rbx, 88(%rsp)
	movq	-96(%rsp), %rbx
	rorx	$56, %r8, %r8
	xorq	%r9, %r14
	rorx	$28, %r14, %r15
	movq	%r15, 40(%rsp)
	rorx	$61, %r11, %r15
	xorq	%r10, %rbx
	rorx	$23, %rdx, %r11
	rorx	$46, %rdi, %rdx
	movq	%rdx, 64(%rsp)
	movq	-104(%rsp), %rdx
	movq	%r15, 48(%rsp)
	rorx	$62, %rax, %r15
	xorq	%rcx, %rdx
	movq	%r11, 56(%rsp)
	rorx	$63, %rdx, %rdi
	movq	%rdi, 72(%rsp)
	movq	-64(%rsp), %rdi
	rorx	$2, %rbx, %rdx
	movq	%r15, 96(%rsp)
	xorq	%rcx, %rdi
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	movq	%rdi, 80(%rsp)
	movq	%rdx, -120(%rsp)
	movq	-24(%rsp), %r11
	movq	-88(%rsp), %rcx
	movq	-32(%rsp), %r14
	xorq	%rsi, %r11
	movq	-56(%rsp), %rdi
	movq	-8(%rsp), %rax
	xorq	%rbp, %rcx
	rorx	$39, %r11, %r9
	movq	(%rsp), %r13
	movq	-112(%rsp), %rdx
	movq	-48(%rsp), %rbx
	movq	-40(%rsp), %r11
	xorq	%r10, %r14
	xorq	%r10, %rdi
	rorx	$37, %rcx, %r15
	rorx	$21, %r14, %r14
	xorq	%r10, %rax
	xorq	%rsi, %rdx
	movq	-16(%rsp), %rcx
	xorq	8(%rsp), %r10
	xorq	%rsi, %rbx
	xorq	%rsi, %r13
	xorq	%rbp, %r11
	rorx	$43, %r13, %r13
	rorx	$49, %rax, %rax
	rorx	$3, %r10, %r10
	xorq	16(%rsp), %rsi
	xorq	%rbp, %rcx
	movq	%r15, -24(%rsp)
	rorx	$44, %r11, %r11
	rorx	$36, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	rorx	$8, %rsi, %rsi
	rorx	$25, %rcx, %rcx
	xorq	24(%rsp), %rbp
	andn	%r14, %r12, %r15
	xorq	32(%rsp), %r15
	movq	%rax, -8(%rsp)
	xorb	$-120, %r15b
	andn	%r13, %r14, %rax
	xorq	%r12, %rax
	rorx	$50, %rbp, %rbp
	movq	%r15, -112(%rsp)
	movq	32(%rsp), %r15
	rorx	$9, %rbx, %rbx
	movq	%rax, -104(%rsp)
	andn	%rbp, %r13, %rax
	xorq	%r14, %rax
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	movq	48(%rsp), %r13
	andn	%r12, %r15, %r12
	movq	%r14, -88(%rsp)
	movq	88(%rsp), %r14
	xorq	%rbp, %r12
	movq	%r12, -80(%rsp)
	andn	%r13, %r11, %rbp
	movq	%rbp, %r12
	andn	%r14, %r13, %rbp
	xorq	%r11, %rbp
	movq	%rax, -96(%rsp)
	xorq	%rdx, %r12
	movq	%rbp, -56(%rsp)
	andn	%r10, %r14, %rbp
	xorq	%rbp, %r13
	andn	%rdx, %r10, %rbp
	xorq	%rbp, %r14
	movq	72(%rsp), %rbp
	movq	64(%rsp), %rax
	andn	%r11, %rdx, %rdx
	xorq	%r10, %rdx
	movq	%r14, -48(%rsp)
	movq	40(%rsp), %r14
	movq	%rbp, %r10
	movq	%rdx, -40(%rsp)
	andn	%r9, %rdi, %rdx
	xorq	%rdx, %r10
	andn	%rax, %r8, %rdx
	xorq	%r9, %rdx
	movq	%r12, -64(%rsp)
	movq	%rdx, -32(%rsp)
	andn	%r8, %r9, %r12
	andn	%rbp, %rax, %rdx
	movq	%rax, %r9
	xorq	%rdx, %r8
	andn	%rdi, %rbp, %rdx
	movq	%r14, %r11
	xorq	%rdx, %r9
	movq	80(%rsp), %rbp
	movq	-24(%rsp), %r15
	xorq	%rdi, %r12
	movq	%r9, -24(%rsp)
	movq	-8(%rsp), %rax
	andn	%rbp, %r14, %rdx
	xorq	%r15, %rdx
	andn	%rax, %rbp, %rdi
	xorq	%rdi, %r11
	andn	%rsi, %rax, %rdi
	xorq	%rdi, %rbp
	andn	%r15, %rsi, %rdi
	xorq	%rdi, %rax
	andn	%r14, %r15, %rdi
	movq	56(%rsp), %r14
	movq	96(%rsp), %r15
	xorq	%rsi, %rdi
	movq	%rax, -8(%rsp)
	movq	%rdi, (%rsp)
	andn	%r14, %rcx, %rax
	andn	%rcx, %rbx, %rdi
	xorq	%rbx, %rax
	andn	%r15, %r14, %rsi
	xorq	%rcx, %rsi
	andn	-120(%rsp), %r15, %rcx
	xorq	-120(%rsp), %rdi
	movq	%rsi, 8(%rsp)
	movq	%r14, %rsi
	movq	-96(%rsp), %r14
	xorq	%rcx, %rsi
	movq	-120(%rsp), %rcx
	movq	%rbp, -16(%rsp)
	movq	%rsi, 16(%rsp)
	xorq	%r13, %r14
	movq	-40(%rsp), %rsi
	andn	%rbx, %rcx, %rcx
	movq	%r15, %rbx
	xorq	-32(%rsp), %r14
	movq	%r13, -120(%rsp)
	xorq	%rcx, %rbx
	movq	-104(%rsp), %rcx
	xorq	-56(%rsp), %rcx
	xorq	%rbp, %r14
	movq	%rbx, 24(%rsp)
	movq	-64(%rsp), %rbx
	movq	%rcx, %r15
	xorq	%r12, %r15
	movq	(%rsp), %rbp
	movq	-88(%rsp), %r13
	xorq	%r10, %rbx
	xorq	%r11, %r15
	xorq	-48(%rsp), %r13
	xorq	8(%rsp), %r14
	xorq	%rdx, %rbx
	xorq	%rax, %r15
	rorx	$63, %r14, %rcx
	xorq	%rdi, %rbx
	xorq	-112(%rsp), %rbx
	xorq	%r8, %r13
	xorq	%r9, %rsi
	xorq	-8(%rsp), %r13
	xorq	-80(%rsp), %rsi
	xorq	%rbx, %rcx
	rorx	$63, %rbx, %rbx
	xorq	16(%rsp), %r13
	xorq	%rbp, %rsi
	rorx	$63, %r15, %rbp
	xorq	24(%rsp), %rsi
	rorx	$63, %r13, %r9
	xorq	%r15, %r9
	xorq	%rsi, %rbp
	xorq	%rcx, %r11
	xorq	%rbp, %rdi
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%rbp, %rdx
	rorx	$46, %rdi, %rdi
	xorq	%rcx, %rax
	xorq	%rbp, %r10
	xorq	%rcx, %r12
	movq	-112(%rsp), %r15
	xorq	%r13, %rbx
	rorx	$61, %r10, %r10
	xorq	%rsi, %r8
	rorx	$39, %r8, %r8
	xorq	%rbp, %r15
	movq	%r15, -112(%rsp)
	movq	-64(%rsp), %r14
	movl	$2147516425, %r15d
	movq	%rdi, 48(%rsp)
	movq	-56(%rsp), %rdi
	xorq	%rbp, %r14
	movq	%r10, -64(%rsp)
	movq	-40(%rsp), %r10
	xorq	%rcx, %rdi
	rorx	$28, %r14, %r14
	movq	%r14, 32(%rsp)
	rorx	$23, %rdx, %r14
	rorx	$20, %rdi, %rbp
	movq	%r14, 40(%rsp)
	rorx	$62, %rax, %rdi
	rorx	$19, %r11, %r14
	movq	-120(%rsp), %rax
	movq	-96(%rsp), %r11
	movq	%rdi, 72(%rsp)
	movq	-104(%rsp), %rdx
	movq	(%rsp), %rdi
	movq	%r14, -56(%rsp)
	xorq	%r9, %rax
	xorq	%r9, %r11
	rorx	$2, %r11, %r11
	movq	%r11, -104(%rsp)
	rorx	$58, %rax, %r11
	xorq	%rcx, %rdx
	movq	-16(%rsp), %rax
	rorx	$63, %rdx, %rdx
	movq	%rdx, 56(%rsp)
	rorx	$54, %r12, %rdx
	movq	-32(%rsp), %r12
	movq	-24(%rsp), %rcx
	movq	%rdx, 64(%rsp)
	xorq	%r9, %rax
	movq	-88(%rsp), %rdx
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	xorq	%r9, %r12
	rorx	$21, %r12, %r13
	movq	-8(%rsp), %r12
	xorq	8(%rsp), %r9
	xorq	%rsi, %rdx
	xorq	%rsi, %rax
	rorx	$36, %rdx, %rdx
	rorx	$3, %r9, %r9
	rorx	$9, %rax, %rax
	movq	%rax, -120(%rsp)
	movq	-80(%rsp), %rax
	xorq	%rsi, %r12
	xorq	16(%rsp), %rsi
	rorx	$43, %r12, %r12
	xorq	%rbx, %rax
	andn	%r13, %rbp, %r14
	xorq	%rbx, %r10
	xorq	%rbx, %rcx
	xorq	-112(%rsp), %r14
	xorq	%rbx, %rdi
	rorx	$44, %r10, %r10
	rorx	$8, %rsi, %rsi
	xorq	%r14, %r15
	andn	%r12, %r13, %r14
	xorq	24(%rsp), %rbx
	xorq	%rbp, %r14
	rorx	$50, %rbx, %rbx
	rorx	$56, %rdi, %rdi
	rorx	$37, %rax, %rax
	rorx	$25, %rcx, %rcx
	movq	%r14, -96(%rsp)
	andn	%rbx, %r12, %r14
	xorq	%r13, %r14
	movq	%r14, -88(%rsp)
	movq	-112(%rsp), %r14
	andn	%r14, %rbx, %r13
	xorq	%r12, %r13
	andn	%rbp, %r14, %rbp
	movq	%rbp, %r12
	movq	%r13, -112(%rsp)
	movq	-64(%rsp), %rbp
	xorq	%rbx, %r12
	movq	-56(%rsp), %r14
	movq	56(%rsp), %r13
	movq	%r12, -80(%rsp)
	andn	%rbp, %r10, %r12
	xorq	%rdx, %r12
	movq	%r12, -64(%rsp)
	andn	%r14, %rbp, %r12
	xorq	%r10, %r12
	andn	%r10, %rdx, %r10
	xorq	%r9, %r10
	andn	%r9, %r14, %rbx
	xorq	%rbx, %rbp
	andn	%rdx, %r9, %rbx
	movq	%r10, -40(%rsp)
	movq	48(%rsp), %r9
	movq	%r13, %r10
	xorq	%rbx, %r14
	andn	%r8, %r11, %rdx
	xorq	%rdx, %r10
	andn	%rdi, %r8, %rdx
	xorq	%r11, %rdx
	movq	%r12, -56(%rsp)
	movq	%rdx, %r12
	andn	%r9, %rdi, %rdx
	xorq	%r8, %rdx
	movq	%r14, -48(%rsp)
	movq	32(%rsp), %r14
	andn	%r13, %r9, %r8
	xorq	%rdi, %r8
	movq	-16(%rsp), %rbx
	movq	%rdx, -32(%rsp)
	andn	%r11, %r13, %rdx
	xorq	%rdx, %r9
	movq	64(%rsp), %r13
	movq	%r14, %r11
	andn	%rbx, %r13, %rdi
	andn	%r13, %r14, %rdx
	xorq	%rdi, %r11
	andn	%rsi, %rbx, %rdi
	xorq	%rdi, %r13
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %rbx
	xorq	%rax, %rdx
	movq	%rbx, -8(%rsp)
	andn	%r14, %rax, %rax
	movq	40(%rsp), %rbx
	xorq	%rsi, %rax
	movq	72(%rsp), %r14
	movq	-120(%rsp), %rsi
	movq	%rax, (%rsp)
	andn	%rbx, %rcx, %rax
	movq	%r13, -16(%rsp)
	xorq	%rsi, %rax
	andn	%rcx, %rsi, %rdi
	andn	%r14, %rbx, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 8(%rsp)
	movq	%r14, %rsi
	movq	-104(%rsp), %r14
	xorq	-104(%rsp), %rdi
	movq	%rbp, -104(%rsp)
	andn	%r14, %rsi, %rcx
	xorq	%rcx, %rbx
	andn	-120(%rsp), %r14, %rcx
	xorq	%rcx, %rsi
	movq	-96(%rsp), %rcx
	xorq	-56(%rsp), %rcx
	movq	%rbx, 16(%rsp)
	movq	-64(%rsp), %rbx
	movq	-88(%rsp), %r14
	movq	%r15, -120(%rsp)
	movq	%rsi, 24(%rsp)
	xorq	%r10, %rbx
	xorq	%rdx, %rbx
	xorq	%rdi, %rbx
	xorq	%r15, %rbx
	movq	%rcx, %r15
	xorq	%r12, %r15
	xorq	%r11, %r15
	xorq	%rax, %r15
	xorq	%rbp, %r14
	xorq	-32(%rsp), %r14
	movq	8(%rsp), %rbp
	xorq	%r13, %r14
	movq	-40(%rsp), %rsi
	movq	-112(%rsp), %r13
	movq	%r9, -24(%rsp)
	xorq	%rbp, %r14
	movq	-80(%rsp), %rbp
	xorq	-48(%rsp), %r13
	xorq	%r9, %rsi
	xorq	%r8, %r13
	rorx	$63, %r14, %rcx
	xorq	-8(%rsp), %r13
	xorq	%rbp, %rsi
	xorq	(%rsp), %rsi
	xorq	24(%rsp), %rsi
	rorx	$63, %r15, %rbp
	xorq	%rsi, %rbp
	xorq	16(%rsp), %r13
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%rbp, %rdi
	xorq	%rbx, %rcx
	rorx	$63, %r13, %r9
	xorq	%r15, %r9
	rorx	$46, %rdi, %rdi
	xorq	%rcx, %r11
	xorq	%rcx, %rax
	xorq	%rbp, %r10
	movq	-64(%rsp), %r14
	movq	%rdi, 56(%rsp)
	xorq	%rbp, %rdx
	xorq	%rcx, %r12
	movq	-56(%rsp), %rdi
	rorx	$23, %rdx, %rdx
	rorx	$63, %rbx, %rbx
	xorq	%r13, %rbx
	movq	-120(%rsp), %r15
	xorq	%rbp, %r14
	movq	%rdx, 48(%rsp)
	rorx	$61, %r10, %r10
	xorq	%rcx, %rdi
	rorx	$28, %r14, %r14
	movq	%r14, 40(%rsp)
	rorx	$19, %r11, %r14
	xorq	%rbp, %r15
	movq	-88(%rsp), %r11
	rorx	$20, %rdi, %rbp
	rorx	$62, %rax, %rdi
	movq	-104(%rsp), %rax
	movq	-96(%rsp), %rdx
	movq	%r15, 32(%rsp)
	movl	$2147483658, %r15d
	xorq	%r9, %r11
	movq	%r10, -64(%rsp)
	xorq	%r9, %rax
	rorx	$2, %r11, %r11
	movq	%r11, -96(%rsp)
	xorq	%rcx, %rdx
	rorx	$58, %rax, %r11
	movq	-16(%rsp), %rax
	rorx	$63, %rdx, %rdx
	movq	%rdx, 64(%rsp)
	rorx	$54, %r12, %rdx
	movq	-32(%rsp), %r12
	movq	%rdx, 72(%rsp)
	xorq	%r9, %rax
	movq	-112(%rsp), %rdx
	movq	%r14, -56(%rsp)
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	xorq	%r9, %r12
	xorq	8(%rsp), %r9
	xorq	%rsi, %rdx
	rorx	$21, %r12, %r13
	xorq	%rsi, %r8
	xorq	%rsi, %rax
	andn	%r13, %rbp, %r14
	rorx	$36, %rdx, %rdx
	rorx	$3, %r9, %r9
	movq	%rdi, 80(%rsp)
	rorx	$9, %rax, %rax
	rorx	$39, %r8, %r8
	movq	%rax, -120(%rsp)
	movq	-8(%rsp), %r12
	movq	-80(%rsp), %rax
	movq	-40(%rsp), %r10
	movq	(%rsp), %rdi
	movq	-24(%rsp), %rcx
	xorq	%rsi, %r12
	xorq	32(%rsp), %r14
	rorx	$43, %r12, %r12
	xorq	%rbx, %rax
	xorq	%rbx, %r10
	xorq	%r14, %r15
	xorq	%rbx, %rcx
	andn	%r12, %r13, %r14
	xorq	%rbx, %rdi
	xorq	%rbp, %r14
	rorx	$44, %r10, %r10
	xorq	24(%rsp), %rbx
	rorx	$56, %rdi, %rdi
	rorx	$50, %rbx, %rbx
	movq	%r14, -112(%rsp)
	andn	%rbx, %r12, %r14
	xorq	%r13, %r14
	movq	%r14, -104(%rsp)
	movq	32(%rsp), %r14
	rorx	$37, %rax, %rax
	rorx	$25, %rcx, %rcx
	xorq	16(%rsp), %rsi
	andn	%r14, %rbx, %r13
	andn	%rbp, %r14, %rbp
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	-64(%rsp), %rbp
	movq	-56(%rsp), %r14
	xorq	%rbx, %r12
	movq	%r13, -88(%rsp)
	movq	%r12, -80(%rsp)
	movq	64(%rsp), %r13
	rorx	$8, %rsi, %rsi
	andn	%rbp, %r10, %r12
	xorq	%rdx, %r12
	andn	%r9, %r14, %rbx
	movq	%r12, -64(%rsp)
	andn	%r14, %rbp, %r12
	xorq	%r10, %r12
	andn	%r10, %rdx, %r10
	xorq	%r9, %r10
	xorq	%rbx, %rbp
	andn	%rdx, %r9, %rbx
	movq	56(%rsp), %r9
	movq	%r10, -40(%rsp)
	movq	%r13, %r10
	xorq	%rbx, %r14
	andn	%r8, %r11, %rdx
	xorq	%rdx, %r10
	andn	%rdi, %r8, %rdx
	xorq	%r11, %rdx
	movq	%r12, -56(%rsp)
	movq	%r14, -48(%rsp)
	movq	%rdx, %r12
	movq	40(%rsp), %r14
	andn	%r9, %rdi, %rdx
	xorq	%r8, %rdx
	movq	-16(%rsp), %rbx
	andn	%r13, %r9, %r8
	xorq	%rdi, %r8
	movq	%rdx, -32(%rsp)
	andn	%r11, %r13, %rdx
	movq	%r14, %r11
	xorq	%rdx, %r9
	movq	72(%rsp), %r13
	andn	%rbx, %r13, %rdi
	andn	%r13, %r14, %rdx
	xorq	%rdi, %r11
	andn	%rsi, %rbx, %rdi
	xorq	%rdi, %r13
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %rbx
	xorq	%rax, %rdx
	movq	%rbx, -8(%rsp)
	andn	%r14, %rax, %rax
	movq	48(%rsp), %rbx
	xorq	%rsi, %rax
	movq	80(%rsp), %r14
	movq	-120(%rsp), %rsi
	movq	%rax, (%rsp)
	andn	%rbx, %rcx, %rax
	andn	%rcx, %rsi, %rdi
	xorq	%rsi, %rax
	andn	%r14, %rbx, %rsi
	xorq	%rcx, %rsi
	xorq	-96(%rsp), %rdi
	movq	%rsi, 8(%rsp)
	movq	%r14, %rsi
	movq	-96(%rsp), %r14
	movq	%rbp, -96(%rsp)
	movq	%r13, -16(%rsp)
	andn	%r14, %rsi, %rcx
	xorq	%rcx, %rbx
	andn	-120(%rsp), %r14, %rcx
	xorq	%rcx, %rsi
	movq	-104(%rsp), %r14
	movq	-112(%rsp), %rcx
	movq	%rbx, 16(%rsp)
	movq	-64(%rsp), %rbx
	movq	%r15, -120(%rsp)
	movq	%rsi, 24(%rsp)
	movq	-40(%rsp), %rsi
	xorq	%r10, %rbx
	movq	%r9, -24(%rsp)
	xorq	%rdx, %rbx
	xorq	%rdi, %rbx
	xorq	%r15, %rbx
	xorq	-56(%rsp), %rcx
	xorq	%rbp, %r14
	movq	8(%rsp), %rbp
	xorq	-32(%rsp), %r14
	movq	%rcx, %r15
	xorq	%r9, %rsi
	xorq	%r12, %r15
	xorq	%r13, %r14
	movq	-88(%rsp), %r13
	xorq	-48(%rsp), %r13
	xorq	%rbp, %r14
	xorq	%r11, %r15
	movq	-80(%rsp), %rbp
	xorq	%r8, %r13
	xorq	%rax, %r15
	xorq	-8(%rsp), %r13
	xorq	16(%rsp), %r13
	rorx	$63, %r14, %rcx
	xorq	%rbp, %rsi
	rorx	$63, %r13, %r9
	xorq	(%rsp), %rsi
	xorq	%r15, %r9
	xorq	24(%rsp), %rsi
	rorx	$63, %r15, %rbp
	movq	-120(%rsp), %r15
	xorq	%rbx, %rcx
	xorq	%rsi, %rbp
	xorq	%rcx, %r12
	xorq	%rcx, %r11
	xorq	%rcx, %rax
	xorq	%rbp, %r15
	xorq	%rbp, %rdx
	xorq	%rbp, %r10
	xorq	%rbp, %rdi
	rorx	$61, %r10, %r10
	rorx	$46, %rdi, %rdi
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	%r15, -120(%rsp)
	movq	-64(%rsp), %r15
	rorx	$19, %r11, %r14
	rorx	$62, %rax, %r11
	movq	%r10, -64(%rsp)
	rorx	$23, %rdx, %r10
	movq	-112(%rsp), %rdx
	rorx	$63, %rbx, %rbx
	xorq	%rbp, %r15
	movq	%r10, 40(%rsp)
	xorq	%r13, %rbx
	xorq	%rcx, %rdx
	movq	%rdi, 48(%rsp)
	rorx	$28, %r15, %r15
	rorx	$63, %rdx, %rdx
	movq	%rdx, 56(%rsp)
	movq	-56(%rsp), %rdx
	movq	%r15, 32(%rsp)
	xorq	%rcx, %rdx
	rorx	$20, %rdx, %rbp
	rorx	$54, %r12, %rdx
	movq	%rdx, -56(%rsp)
	movq	-96(%rsp), %rax
	movq	-40(%rsp), %rdi
	movq	-32(%rsp), %r15
	movq	%r11, 72(%rsp)
	movq	-104(%rsp), %r11
	movq	-24(%rsp), %rcx
	movq	%r14, 64(%rsp)
	movq	-88(%rsp), %rdx
	xorq	%r9, %r11
	xorq	%r9, %rax
	xorq	%r9, %r15
	xorq	%rbx, %rdi
	rorx	$58, %rax, %r12
	rorx	$21, %r15, %r13
	movq	-16(%rsp), %rax
	movq	%r12, 80(%rsp)
	movq	-8(%rsp), %r12
	rorx	$44, %rdi, %r10
	xorq	%rbx, %rcx
	xorq	%rsi, %rdx
	xorq	%r9, %rax
	movq	(%rsp), %rdi
	xorq	8(%rsp), %r9
	xorq	%rsi, %r8
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	andn	%r13, %rbp, %r14
	xorq	%rsi, %r12
	xorq	-120(%rsp), %r14
	xorq	%rbx, %rdi
	rorx	$36, %rdx, %rdx
	xorq	%rsi, %rax
	rorx	$43, %r12, %r12
	rorx	$3, %r9, %r9
	rorx	$39, %r8, %r8
	rorx	$9, %rax, %r15
	rorx	$56, %rdi, %rdi
	rorx	$2, %r11, %r11
	rorx	$25, %rcx, %rcx
	movq	-80(%rsp), %rax
	xorq	16(%rsp), %rsi
	movq	%r15, 8(%rsp)
	movl	$2147516555, %r15d
	xorq	%r14, %r15
	andn	%r12, %r13, %r14
	xorq	%rbp, %r14
	rorx	$8, %rsi, %rsi
	xorq	%rbx, %rax
	xorq	24(%rsp), %rbx
	movq	%r14, -104(%rsp)
	rorx	$50, %rbx, %rbx
	andn	%rbx, %r12, %r14
	xorq	%r13, %r14
	rorx	$37, %rax, %rax
	movq	%r14, -96(%rsp)
	movq	-120(%rsp), %r14
	movq	%r15, -112(%rsp)
	andn	%r14, %rbx, %r13
	xorq	%r12, %r13
	movq	-64(%rsp), %r12
	andn	%rbp, %r14, %rbp
	movq	%r13, -120(%rsp)
	movq	64(%rsp), %r14
	movq	%rbp, %r13
	xorq	%rbx, %r13
	andn	%r12, %r10, %rbx
	xorq	%rdx, %rbx
	movq	%rbx, -80(%rsp)
	andn	%r14, %r12, %rbx
	xorq	%r10, %rbx
	movq	%rbx, -64(%rsp)
	andn	%r9, %r14, %rbx
	xorq	%rbx, %r12
	andn	%rdx, %r9, %rbx
	andn	%r10, %rdx, %rdx
	xorq	%rbx, %r14
	xorq	%r9, %rdx
	movq	%r13, -88(%rsp)
	movq	%r14, -48(%rsp)
	movq	%rdx, -40(%rsp)
	movq	80(%rsp), %rbp
	movq	56(%rsp), %rbx
	movq	48(%rsp), %r10
	movq	%rbp, %r13
	andn	%r8, %rbp, %rdx
	movq	-16(%rsp), %r15
	movq	72(%rsp), %r14
	movq	%rbx, %r9
	xorq	%rdx, %r9
	andn	%rdi, %r8, %rdx
	xorq	%rdx, %r13
	andn	%r10, %rdi, %rdx
	xorq	%r8, %rdx
	andn	%rbx, %r10, %r8
	xorq	%rdi, %r8
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r10
	movq	%r8, -24(%rsp)
	movq	-56(%rsp), %r8
	movq	%rbp, %rbx
	movq	%r12, -56(%rsp)
	andn	%r15, %r8, %rdi
	andn	%r8, %rbp, %rdx
	xorq	%rdi, %rbx
	xorq	%rax, %rdx
	andn	%rsi, %r15, %rdi
	xorq	%rdi, %r8
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %r15
	movq	%r15, (%rsp)
	andn	%rbp, %rax, %rax
	movq	8(%rsp), %r15
	xorq	%rsi, %rax
	movq	40(%rsp), %rbp
	movq	%r8, -8(%rsp)
	movq	%rax, %r8
	andn	%rcx, %r15, %rdi
	xorq	%r11, %rdi
	movq	%r10, -16(%rsp)
	andn	%rbp, %rcx, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r11, %r14, %rcx
	xorq	%rcx, %rbp
	xorq	%r15, %rax
	movq	%rsi, 8(%rsp)
	andn	%r15, %r11, %rcx
	movq	%rbp, 16(%rsp)
	movq	-104(%rsp), %r11
	movq	%r14, %rsi
	xorq	-64(%rsp), %r11
	movq	-80(%rsp), %rbp
	xorq	%rcx, %rsi
	movq	%r11, %r15
	movq	%rsi, 24(%rsp)
	movq	-96(%rsp), %r14
	xorq	%r9, %rbp
	xorq	%r13, %r15
	movq	-40(%rsp), %rsi
	xorq	%rdx, %rbp
	xorq	%rbx, %r15
	xorq	%r12, %r14
	movq	-120(%rsp), %r12
	xorq	%rax, %r15
	xorq	%rdi, %rbp
	xorq	-32(%rsp), %r14
	xorq	-112(%rsp), %rbp
	xorq	-8(%rsp), %r14
	xorq	-48(%rsp), %r12
	xorq	%r10, %rsi
	rorx	$63, %r15, %r11
	xorq	8(%rsp), %r14
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	xorq	16(%rsp), %r12
	rorx	$63, %r14, %rcx
	xorq	%rbp, %rcx
	xorq	-88(%rsp), %rsi
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	rorx	$63, %rbp, %rbp
	movq	-112(%rsp), %r15
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	%r12, %rbp
	xorq	%rsi, %r11
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%r11, %r15
	xorq	%r11, %rdx
	xorq	%r11, %rdi
	xorq	%r11, %r9
	movq	%r15, -112(%rsp)
	rorx	$61, %r9, %r9
	movq	-80(%rsp), %r15
	movq	%r9, -80(%rsp)
	rorx	$23, %rdx, %r9
	rorx	$46, %rdi, %rdx
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	xorq	%r11, %r15
	movq	%r9, 40(%rsp)
	movq	-40(%rsp), %r11
	rorx	$28, %r15, %r15
	xorq	%rcx, %rdx
	xorq	%rcx, %rax
	xorq	%rcx, %r13
	xorq	%rcx, %rbx
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	xorq	%rbp, %r11
	xorq	%rbp, %r8
	rorx	$54, %r13, %r14
	movq	-64(%rsp), %rdi
	movq	-32(%rsp), %r13
	movq	%r14, 64(%rsp)
	movq	-96(%rsp), %r14
	rorx	$44, %r11, %r11
	rorx	$19, %rbx, %rbx
	rorx	$56, %r8, %r8
	xorq	%rcx, %rdi
	xorq	%r10, %r13
	movq	-16(%rsp), %rcx
	movq	%r15, 32(%rsp)
	rorx	$20, %rdi, %r12
	rorx	$62, %rax, %rdi
	movq	-8(%rsp), %rax
	xorq	%r10, %r14
	movq	%rdi, 72(%rsp)
	movq	-56(%rsp), %rdi
	rorx	$2, %r14, %rdx
	rorx	$21, %r13, %r14
	xorq	%r10, %rax
	movq	%rdx, 80(%rsp)
	movq	-24(%rsp), %r9
	xorq	%rbp, %rcx
	rorx	$49, %rax, %rax
	movq	%rax, -56(%rsp)
	movq	-48(%rsp), %rax
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	movq	-120(%rsp), %rdx
	xorq	%rsi, %r9
	rorx	$25, %rcx, %rcx
	xorq	%rsi, %rax
	rorx	$3, %r10, %r15
	movq	(%rsp), %r13
	movq	%r15, -32(%rsp)
	rorx	$9, %rax, %r10
	movq	-88(%rsp), %rax
	andn	%r14, %r12, %r15
	xorq	%rsi, %rdx
	xorq	%rsi, %r13
	rorx	$36, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	rorx	$39, %r9, %r9
	xorq	16(%rsp), %rsi
	xorq	%rbp, %rax
	movq	%rcx, -16(%rsp)
	rorx	$43, %r13, %r13
	xorq	24(%rsp), %rbp
	xorq	-112(%rsp), %r15
	rorx	$8, %rsi, %rsi
	rorx	$37, %rax, %rax
	movabsq	$-9223372036854775669, %rcx
	rorx	$50, %rbp, %rbp
	xorq	%r15, %rcx
	andn	%r13, %r14, %r15
	xorq	%r12, %r15
	movq	%r15, -104(%rsp)
	movq	-112(%rsp), %r15
	movq	%rcx, -120(%rsp)
	andn	%rbp, %r13, %rcx
	xorq	%r14, %rcx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	xorq	%rbp, %r13
	movq	-32(%rsp), %r15
	movq	%rcx, -96(%rsp)
	andn	%r12, %r11, %rbp
	movq	%r13, -88(%rsp)
	movq	%rbp, %r13
	movq	64(%rsp), %rcx
	xorq	%rdx, %r13
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	movq	%r14, -112(%rsp)
	movq	%r13, -80(%rsp)
	movq	72(%rsp), %r14
	movq	%rbp, -64(%rsp)
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	movq	%rbp, %r13
	movq	56(%rsp), %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	xorq	%rbx, %r13
	movq	48(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	%rbp, %r11
	movq	%r13, -48(%rsp)
	movq	80(%rsp), %r15
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%r8, %rdx
	movq	-56(%rsp), %r8
	movq	%rdx, -24(%rsp)
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%r8, %rcx, %rdi
	movq	%rbp, %rbx
	andn	%rcx, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rcx
	andn	%rax, %rsi, %rdi
	movq	%rcx, -8(%rsp)
	andn	%rbp, %rax, %rax
	movq	-16(%rsp), %rcx
	xorq	%rdi, %r8
	movq	40(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r8, (%rsp)
	andn	%rcx, %r10, %rdi
	movq	%rax, %r8
	xorq	%r15, %rdi
	andn	%rbp, %rcx, %rax
	xorq	%r10, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r10, %r15, %rcx
	movq	%rbp, %rsi
	movq	-80(%rsp), %rbp
	xorq	%rcx, %r14
	movq	-104(%rsp), %r15
	movq	%r14, 24(%rsp)
	xorq	-64(%rsp), %r15
	xorq	%r11, %rbp
	xorq	%r13, %r15
	xorq	%rdx, %rbp
	xorq	%rbx, %r15
	xorq	%rdi, %rbp
	xorq	-120(%rsp), %rbp
	movq	-96(%rsp), %r10
	xorq	%rax, %r15
	movq	%r12, -56(%rsp)
	movq	-32(%rsp), %r14
	xorq	%r12, %r10
	movq	-112(%rsp), %r12
	xorq	-48(%rsp), %r12
	movq	%rsi, 16(%rsp)
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	xorq	%r10, %r14
	movq	%r9, -16(%rsp)
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	xorq	-8(%rsp), %r14
	xorq	8(%rsp), %r14
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-120(%rsp), %r14
	xorq	%r12, %rbp
	xorq	%r9, %r14
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	rorx	$61, %r11, %r15
	xorq	%rcx, %rax
	xorq	%rcx, %r13
	xorq	%rcx, %rbx
	movq	%r14, -120(%rsp)
	rorx	$23, %rdx, %r11
	rorx	$46, %rdi, %rdx
	xorq	%rbp, %r8
	movq	-80(%rsp), %r14
	movq	%r15, -80(%rsp)
	rorx	$19, %rbx, %rbx
	rorx	$56, %r8, %r8
	movq	-104(%rsp), %r15
	movq	-64(%rsp), %rdi
	movq	%r11, 40(%rsp)
	xorq	%r9, %r14
	movq	%rdx, 48(%rsp)
	xorq	%rcx, %r15
	xorq	%rcx, %rdi
	rorx	$28, %r14, %r14
	movq	%r14, 32(%rsp)
	rorx	$63, %r15, %r15
	movq	%r15, 56(%rsp)
	rorx	$62, %rax, %r15
	movq	-96(%rsp), %rax
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	movq	%rdi, 64(%rsp)
	movq	-32(%rsp), %r14
	xorq	%r10, %rax
	movq	%r15, 72(%rsp)
	rorx	$2, %rax, %rdi
	movq	-8(%rsp), %rax
	movq	%rdi, 80(%rsp)
	xorq	%r10, %r14
	movq	-56(%rsp), %rdi
	rorx	$21, %r14, %r14
	andn	%r14, %r12, %r15
	xorq	%r10, %rax
	xorq	%r10, %rdi
	rorx	$49, %rax, %rax
	movq	%rax, -56(%rsp)
	xorq	8(%rsp), %r10
	movq	-48(%rsp), %r13
	rorx	$3, %r10, %rax
	movq	-112(%rsp), %rdx
	movq	%rax, -32(%rsp)
	xorq	-120(%rsp), %r15
	movq	-88(%rsp), %rax
	rorx	$58, %rdi, %rdi
	xorq	%rsi, %r13
	xorq	%rsi, %rdx
	movq	-40(%rsp), %r11
	movq	-16(%rsp), %rcx
	rorx	$9, %r13, %r10
	movq	-24(%rsp), %r13
	rorx	$36, %rdx, %rdx
	xorq	%rbp, %rax
	movq	%rdx, -64(%rsp)
	xorq	%rbp, %r11
	xorq	%rbp, %rcx
	xorq	24(%rsp), %rbp
	xorq	%rsi, %r13
	rorx	$50, %rbp, %rbp
	rorx	$44, %r11, %r11
	rorx	$37, %rax, %rax
	rorx	$39, %r13, %r9
	movq	(%rsp), %r13
	rorx	$25, %rcx, %rcx
	movabsq	$-9223372036854742903, %rdx
	xorq	%r15, %rdx
	movq	-120(%rsp), %r15
	xorq	%rsi, %r13
	movq	%rdx, -112(%rsp)
	xorq	16(%rsp), %rsi
	rorx	$43, %r13, %r13
	andn	%r13, %r14, %rdx
	xorq	%r12, %rdx
	rorx	$8, %rsi, %rsi
	movq	%rdx, -104(%rsp)
	andn	%rbp, %r13, %rdx
	xorq	%r14, %rdx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	xorq	%rbp, %r13
	movq	%rdx, -96(%rsp)
	movq	-64(%rsp), %rdx
	andn	%r12, %r11, %rbp
	movq	%r14, -120(%rsp)
	movq	-32(%rsp), %r14
	movq	%r13, -88(%rsp)
	movq	%rbp, %r13
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	xorq	%rdx, %r13
	movq	%rbp, -64(%rsp)
	andn	%r14, %rbx, %rbp
	xorq	%rbp, %r12
	movq	%r13, -80(%rsp)
	andn	%rdx, %r14, %rbp
	movq	%rbp, %r13
	andn	%r11, %rdx, %rdx
	movq	56(%rsp), %rbp
	xorq	%rbx, %r13
	andn	%r8, %r9, %rbx
	xorq	%rdi, %rbx
	movq	%r13, -48(%rsp)
	movq	%rbx, %r13
	movq	48(%rsp), %rbx
	xorq	%rdx, %r14
	movq	%rbp, %r11
	andn	%r9, %rdi, %rdx
	movq	%r14, -40(%rsp)
	xorq	%rdx, %r11
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rbp, %rbx
	andn	%rbp, %r9, %rbp
	xorq	%r8, %rbp
	movq	%rdx, -32(%rsp)
	movq	%rbp, -24(%rsp)
	movq	32(%rsp), %rbp
	andn	%rdi, %rbx, %rdx
	xorq	%rdx, %r9
	movq	64(%rsp), %r8
	movq	-56(%rsp), %r15
	movq	%r12, -56(%rsp)
	movq	%rbp, %rbx
	movq	80(%rsp), %r14
	movq	%r9, -16(%rsp)
	andn	%r15, %r8, %rdi
	andn	%r8, %rbp, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r15, %rdi
	xorq	%rdi, %r8
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %r15
	xorq	%rax, %rdx
	movq	%r15, (%rsp)
	andn	%rbp, %rax, %rax
	xorq	%rsi, %rax
	movq	40(%rsp), %rbp
	movq	72(%rsp), %r15
	andn	%rcx, %r10, %rdi
	movq	%r8, -8(%rsp)
	xorq	%r14, %rdi
	movq	%rax, %r8
	andn	%rbp, %rcx, %rax
	xorq	%r10, %rax
	andn	%r15, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r14, %r15, %rcx
	xorq	%rcx, %rbp
	andn	%r10, %r14, %rcx
	movq	-96(%rsp), %r14
	movq	%rsi, 8(%rsp)
	movq	%rbp, %rsi
	movq	%r15, %rbp
	movq	-104(%rsp), %r10
	xorq	-64(%rsp), %r10
	movq	%rsi, 16(%rsp)
	xorq	%rcx, %rbp
	xorq	%r12, %r14
	movq	-120(%rsp), %r12
	xorq	-48(%rsp), %r12
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	movq	%rbp, 24(%rsp)
	movq	%r10, %r15
	xorq	%rsi, %r12
	movq	-80(%rsp), %rbp
	movq	-40(%rsp), %rsi
	xorq	%r13, %r15
	xorq	%rbx, %r15
	xorq	-32(%rsp), %r14
	rorx	$63, %r12, %r10
	xorq	-8(%rsp), %r14
	xorq	%r11, %rbp
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	xorq	%rax, %r15
	xorq	%rdx, %rbp
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	8(%rsp), %r14
	xorq	%rdi, %rbp
	rorx	$63, %r15, %r9
	xorq	-112(%rsp), %rbp
	xorq	%rsi, %r9
	xorq	%r15, %r10
	movq	-112(%rsp), %r15
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	rorx	$63, %r14, %rcx
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%r9, %r15
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	movq	%r15, -112(%rsp)
	movq	-80(%rsp), %r15
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	xorq	%rcx, %rbx
	xorq	%rbp, %r8
	xorq	%r9, %r15
	rorx	$19, %rbx, %rbx
	rorx	$56, %r8, %r8
	rorx	$28, %r15, %r14
	movq	%r14, 32(%rsp)
	rorx	$61, %r11, %r14
	rorx	$23, %rdx, %r11
	movq	%r14, -80(%rsp)
	rorx	$46, %rdi, %rdx
	movq	%r11, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	movq	-96(%rsp), %r14
	movq	-32(%rsp), %r15
	xorq	%rcx, %rdx
	movq	-24(%rsp), %r9
	movq	-40(%rsp), %r11
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	xorq	%r10, %r14
	xorq	%r10, %r15
	movq	-64(%rsp), %rdi
	rorx	$2, %r14, %rdx
	rorx	$21, %r15, %r14
	xorq	%rsi, %r9
	movq	%rdx, 80(%rsp)
	movq	-120(%rsp), %rdx
	xorq	%rbp, %r11
	rorx	$39, %r9, %r9
	xorq	%rcx, %rdi
	movq	-16(%rsp), %rcx
	rorx	$44, %r11, %r11
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	-8(%rsp), %rax
	movq	%rdi, 64(%rsp)
	movq	-56(%rsp), %rdi
	xorq	%rbp, %rcx
	xorq	%rsi, %rdx
	xorq	%r10, %rax
	movq	%r13, 72(%rsp)
	movq	(%rsp), %r13
	rorx	$25, %rcx, %rcx
	rorx	$49, %rax, %rax
	movq	%rax, -56(%rsp)
	movq	-48(%rsp), %rax
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	xorq	%rsi, %r13
	rorx	$36, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	xorq	%rsi, %rax
	rorx	$3, %r10, %r15
	movq	%rcx, -16(%rsp)
	movabsq	$-9223372036854743037, %rcx
	rorx	$9, %rax, %r10
	movq	-88(%rsp), %rax
	movq	%r15, -32(%rsp)
	andn	%r14, %r12, %r15
	xorq	-112(%rsp), %r15
	rorx	$43, %r13, %r13
	xorq	16(%rsp), %rsi
	xorq	%rbp, %rax
	xorq	24(%rsp), %rbp
	xorq	%r15, %rcx
	andn	%r13, %r14, %r15
	xorq	%r12, %r15
	rorx	$50, %rbp, %rbp
	rorx	$8, %rsi, %rsi
	rorx	$37, %rax, %rax
	movq	%r15, -104(%rsp)
	movq	-112(%rsp), %r15
	movq	%rcx, -120(%rsp)
	andn	%rbp, %r13, %rcx
	xorq	%r14, %rcx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	xorq	%rbp, %r13
	movq	%rcx, -96(%rsp)
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%r13, -88(%rsp)
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	movq	%rbp, %r13
	xorq	%r11, %r13
	movq	%r14, -112(%rsp)
	movq	%r13, -64(%rsp)
	movq	-32(%rsp), %r15
	movq	64(%rsp), %rcx
	movq	72(%rsp), %r14
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	xorq	%rbx, %rbp
	movq	%rbp, -48(%rsp)
	movq	56(%rsp), %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	movq	48(%rsp), %rbx
	andn	%r9, %rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	%rbp, %r11
	movq	80(%rsp), %r15
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	xorq	%r8, %rdx
	movq	-56(%rsp), %r8
	movq	%rdx, -24(%rsp)
	andn	%rdi, %rbp, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%r8, %rcx, %rdi
	movq	%r12, -56(%rsp)
	movq	%rbp, %rbx
	andn	%rcx, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rcx
	andn	%rax, %rsi, %rdi
	movq	%rcx, -8(%rsp)
	andn	%rbp, %rax, %rax
	movq	-16(%rsp), %rcx
	xorq	%rdi, %r8
	movq	40(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r8, (%rsp)
	andn	%rcx, %r10, %rdi
	movq	%rax, %r8
	xorq	%r15, %rdi
	andn	%rbp, %rcx, %rax
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r10, %r15, %rcx
	xorq	%r10, %rax
	movq	%rbp, %rsi
	movq	-80(%rsp), %rbp
	xorq	%rcx, %r14
	movq	-104(%rsp), %r15
	movq	-96(%rsp), %r10
	xorq	-64(%rsp), %r15
	movq	%r14, 24(%rsp)
	xorq	%r11, %rbp
	xorq	%r13, %r15
	movq	-32(%rsp), %r14
	movq	%rsi, 16(%rsp)
	xorq	%r12, %r10
	xorq	%rdx, %rbp
	xorq	%rbx, %r15
	movq	-112(%rsp), %r12
	xorq	-48(%rsp), %r12
	xorq	-24(%rsp), %r12
	xorq	%rax, %r15
	xorq	%rdi, %rbp
	xorq	(%rsp), %r12
	xorq	-120(%rsp), %rbp
	xorq	%r10, %r14
	xorq	-8(%rsp), %r14
	xorq	8(%rsp), %r14
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	rorx	$63, %r14, %rcx
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	movq	%r9, -16(%rsp)
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r9, %rsi
	rorx	$63, %r15, %r9
	xorq	%rcx, %rax
	xorq	%rcx, %r13
	xorq	-88(%rsp), %rsi
	xorq	%rcx, %rbx
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	rorx	$19, %rbx, %rbx
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-120(%rsp), %r14
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	xorq	%r9, %r14
	rorx	$61, %r11, %r15
	rorx	$23, %rdx, %r11
	rorx	$46, %rdi, %rdx
	movq	%r14, -120(%rsp)
	movq	-80(%rsp), %r14
	movq	%r15, -80(%rsp)
	movq	-104(%rsp), %r15
	movq	-64(%rsp), %rdi
	xorq	%r9, %r14
	movq	%rdx, 48(%rsp)
	xorq	%rcx, %r15
	rorx	$28, %r14, %r14
	movq	%r14, 32(%rsp)
	movq	-32(%rsp), %r14
	rorx	$63, %r15, %r15
	movq	%r15, 56(%rsp)
	rorx	$62, %rax, %r15
	movq	-96(%rsp), %rax
	xorq	%rcx, %rdi
	xorq	%r10, %r14
	movq	-112(%rsp), %rdx
	movq	%r11, 40(%rsp)
	xorq	%r10, %rax
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	movq	-48(%rsp), %r13
	movq	%rdi, 64(%rsp)
	rorx	$2, %rax, %rdi
	xorq	%rsi, %rdx
	movq	-8(%rsp), %rax
	movq	%rdi, 80(%rsp)
	xorq	%rsi, %r13
	movq	-56(%rsp), %rdi
	rorx	$36, %rdx, %rdx
	xorq	%r10, %rax
	movq	%r15, 72(%rsp)
	movq	-40(%rsp), %r11
	rorx	$21, %r14, %r14
	xorq	%r10, %rdi
	xorq	8(%rsp), %r10
	rorx	$49, %rax, %rax
	movq	%rax, -56(%rsp)
	rorx	$3, %r10, %rax
	rorx	$9, %r13, %r10
	movq	-24(%rsp), %r13
	movq	%rax, -32(%rsp)
	movq	%rdx, -64(%rsp)
	movq	-88(%rsp), %rax
	xorq	%rbp, %r11
	rorx	$58, %rdi, %rdi
	xorq	%rsi, %r13
	rorx	$44, %r11, %r11
	movabsq	$-9223372036854743038, %rdx
	rorx	$39, %r13, %r9
	movq	(%rsp), %r13
	xorq	%rbp, %rax
	rorx	$37, %rax, %rax
	xorq	%rsi, %r13
	xorq	16(%rsp), %rsi
	movq	-16(%rsp), %rcx
	rorx	$43, %r13, %r13
	rorx	$8, %rsi, %rsi
	xorq	%rbp, %rcx
	andn	%r14, %r12, %r15
	xorq	-120(%rsp), %r15
	xorq	%rbp, %r8
	xorq	%r15, %rdx
	movq	-120(%rsp), %r15
	xorq	24(%rsp), %rbp
	rorx	$56, %r8, %r8
	movq	%rdx, -112(%rsp)
	andn	%r13, %r14, %rdx
	xorq	%r12, %rdx
	rorx	$50, %rbp, %rbp
	movq	%rdx, -104(%rsp)
	andn	%rbp, %r13, %rdx
	xorq	%r14, %rdx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	xorq	%rbp, %r13
	movq	%rdx, -96(%rsp)
	movq	-64(%rsp), %rdx
	rorx	$25, %rcx, %rcx
	andn	%r12, %r11, %rbp
	movq	%r14, -120(%rsp)
	movq	-32(%rsp), %r14
	movq	%r13, -88(%rsp)
	movq	%rbp, %r13
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	xorq	%rdx, %r13
	movq	%rbp, -64(%rsp)
	andn	%r14, %rbx, %rbp
	xorq	%rbp, %r12
	movq	%r13, -80(%rsp)
	andn	%rdx, %r14, %rbp
	movq	%rbp, %r13
	movq	56(%rsp), %rbp
	xorq	%rbx, %r13
	andn	%r8, %r9, %rbx
	xorq	%rdi, %rbx
	andn	%r11, %rdx, %rdx
	movq	%r13, -48(%rsp)
	movq	%rbx, %r13
	movq	48(%rsp), %rbx
	movq	%rbp, %r11
	xorq	%rdx, %r14
	andn	%r9, %rdi, %rdx
	xorq	%rdx, %r11
	movq	-56(%rsp), %r15
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rbp, %rbx
	andn	%rbp, %r9, %rbp
	xorq	%r8, %rbp
	movq	64(%rsp), %r8
	movq	%rdx, -32(%rsp)
	movq	%rbp, -24(%rsp)
	movq	32(%rsp), %rbp
	andn	%rdi, %rbx, %rdx
	xorq	%rdx, %r9
	andn	%r15, %r8, %rdi
	movq	%r14, -40(%rsp)
	movq	80(%rsp), %r14
	movq	%rbp, %rbx
	andn	%r8, %rbp, %rdx
	xorq	%rax, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r15, %rdi
	xorq	%rdi, %r8
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %r15
	andn	%rbp, %rax, %rax
	movq	40(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r15, (%rsp)
	movq	72(%rsp), %r15
	andn	%rcx, %r10, %rdi
	xorq	%r14, %rdi
	movq	%r8, -8(%rsp)
	movq	%rax, %r8
	andn	%rbp, %rcx, %rax
	xorq	%r10, %rax
	andn	%r15, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r14, %r15, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	movq	%rbp, %rsi
	movq	%r15, %rbp
	andn	%r10, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rbp, 24(%rsp)
	movq	-80(%rsp), %rbp
	xorq	%r11, %rbp
	xorq	%rdx, %rbp
	xorq	%rdi, %rbp
	xorq	-112(%rsp), %rbp
	movq	-104(%rsp), %r10
	movq	%r12, -56(%rsp)
	xorq	-64(%rsp), %r10
	movq	-96(%rsp), %r14
	movq	%rsi, 16(%rsp)
	movq	%r10, %r15
	movq	%r9, -16(%rsp)
	xorq	%r13, %r15
	xorq	%r12, %r14
	movq	-120(%rsp), %r12
	xorq	-32(%rsp), %r14
	xorq	%rbx, %r15
	xorq	%rax, %r15
	xorq	-8(%rsp), %r14
	xorq	-48(%rsp), %r12
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	xorq	8(%rsp), %r14
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	rorx	$63, %r14, %rcx
	xorq	%rbp, %rcx
	xorq	%r9, %rsi
	rorx	$63, %r15, %r9
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	xorq	-88(%rsp), %rsi
	movq	-112(%rsp), %r15
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	%rcx, %rbx
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	rorx	$19, %rbx, %rbx
	xorq	%r9, %r15
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	movq	%r15, -112(%rsp)
	movq	-80(%rsp), %r15
	xorq	%r9, %r15
	rorx	$28, %r15, %r14
	movq	%r14, 32(%rsp)
	rorx	$61, %r11, %r14
	rorx	$23, %rdx, %r11
	rorx	$46, %rdi, %rdx
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	movq	%r14, -80(%rsp)
	movq	-96(%rsp), %r14
	xorq	%rcx, %rdx
	movq	%r11, 40(%rsp)
	movq	-32(%rsp), %r15
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	movq	-64(%rsp), %rdi
	xorq	%r10, %r14
	rorx	$2, %r14, %r11
	movq	%r11, 80(%rsp)
	xorq	%r10, %r15
	xorq	%rcx, %rdi
	rorx	$21, %r15, %r14
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	rorx	$62, %rax, %r13
	movq	%rdi, 64(%rsp)
	movq	%r13, 72(%rsp)
	movq	-56(%rsp), %rdi
	movq	-8(%rsp), %rax
	movq	-120(%rsp), %rdx
	movq	-24(%rsp), %r9
	movq	-16(%rsp), %rcx
	xorq	%r10, %rdi
	xorq	%r10, %rax
	movq	(%rsp), %r13
	xorq	8(%rsp), %r10
	xorq	%rsi, %rdx
	rorx	$49, %rax, %rax
	rorx	$3, %r10, %r15
	rorx	$36, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	movq	%rax, -56(%rsp)
	movq	-48(%rsp), %rax
	movq	%r15, -32(%rsp)
	movq	-40(%rsp), %r11
	xorq	%rsi, %rax
	xorq	%rsi, %r9
	xorq	%rbp, %rcx
	andn	%r14, %r12, %r15
	xorq	%rsi, %r13
	xorq	-112(%rsp), %r15
	rorx	$25, %rcx, %rcx
	xorq	%rbp, %r11
	movq	%rcx, -16(%rsp)
	rorx	$9, %rax, %r10
	rorx	$43, %r13, %r13
	movq	-88(%rsp), %rax
	xorq	%rbp, %r8
	rorx	$44, %r11, %r11
	rorx	$39, %r9, %r9
	movabsq	$-9223372036854775680, %rcx
	xorq	%r15, %rcx
	andn	%r13, %r14, %r15
	xorq	%r12, %r15
	xorq	%rbp, %rax
	movq	%r15, -104(%rsp)
	movq	-112(%rsp), %r15
	rorx	$56, %r8, %r8
	rorx	$37, %rax, %rax
	xorq	24(%rsp), %rbp
	xorq	16(%rsp), %rsi
	movq	%rcx, -120(%rsp)
	rorx	$50, %rbp, %rbp
	andn	%rbp, %r13, %rcx
	xorq	%r14, %rcx
	andn	%r15, %rbp, %r14
	xorq	%r13, %r14
	andn	%r12, %r15, %r13
	movq	-80(%rsp), %r12
	xorq	%rbp, %r13
	movq	-32(%rsp), %r15
	movq	%r13, -88(%rsp)
	rorx	$8, %rsi, %rsi
	andn	%r12, %r11, %rbp
	xorq	%rdx, %rbp
	movq	%r14, -112(%rsp)
	movq	%rbp, -80(%rsp)
	andn	%rbx, %r12, %rbp
	xorq	%r11, %rbp
	movq	%rbp, -64(%rsp)
	andn	%r15, %rbx, %rbp
	xorq	%rbp, %r12
	andn	%rdx, %r15, %rbp
	andn	%r11, %rdx, %rdx
	xorq	%rdx, %r15
	movq	%rbp, %r13
	andn	%r9, %rdi, %rdx
	movq	%r15, -40(%rsp)
	movq	56(%rsp), %r15
	xorq	%rbx, %r13
	movq	48(%rsp), %rbx
	movq	%r13, -48(%rsp)
	movq	%r15, %r11
	movq	%rcx, -96(%rsp)
	xorq	%rdx, %r11
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, %r13
	andn	%rbx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rbx, %r9
	movq	%rdx, -32(%rsp)
	andn	%r15, %rbx, %rdx
	xorq	%r8, %rdx
	movq	%rdx, -24(%rsp)
	andn	%rdi, %r15, %rdx
	movq	32(%rsp), %r15
	xorq	%rdx, %r9
	movq	64(%rsp), %rcx
	movq	-56(%rsp), %r8
	movq	%r12, -56(%rsp)
	movq	%r15, %rbx
	movq	40(%rsp), %rbp
	movq	72(%rsp), %r14
	andn	%r8, %rcx, %rdi
	andn	%rcx, %r15, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r8, %rdi
	xorq	%rdi, %rcx
	xorq	%rax, %rdx
	andn	%rax, %rsi, %rdi
	andn	%r15, %rax, %rax
	movq	%rcx, -8(%rsp)
	movq	80(%rsp), %r15
	xorq	%rdi, %r8
	xorq	%rsi, %rax
	movq	-16(%rsp), %rcx
	andn	%r14, %rbp, %rsi
	movq	%r8, (%rsp)
	movq	%rax, %r8
	movq	%r9, -16(%rsp)
	xorq	%rcx, %rsi
	andn	%rcx, %r10, %rdi
	andn	%rbp, %rcx, %rax
	andn	%r15, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r10, %r15, %rcx
	xorq	%r10, %rax
	movq	%rbp, %rsi
	movq	-80(%rsp), %rbp
	movq	-96(%rsp), %r10
	xorq	%r15, %rdi
	movq	-104(%rsp), %r15
	xorq	-64(%rsp), %r15
	xorq	%rcx, %r14
	movq	%rsi, 16(%rsp)
	xorq	%r11, %rbp
	movq	%r14, 24(%rsp)
	movq	-32(%rsp), %r14
	xorq	%rdx, %rbp
	xorq	%rdi, %rbp
	xorq	-120(%rsp), %rbp
	xorq	%r13, %r15
	xorq	%r12, %r10
	movq	-112(%rsp), %r12
	xorq	-48(%rsp), %r12
	xorq	%rbx, %r15
	xorq	%r10, %r14
	xorq	-24(%rsp), %r12
	xorq	(%rsp), %r12
	xorq	%rax, %r15
	xorq	%rsi, %r12
	movq	-40(%rsp), %rsi
	xorq	-8(%rsp), %r14
	xorq	8(%rsp), %r14
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	xorq	%r9, %rsi
	xorq	-88(%rsp), %rsi
	rorx	$63, %r15, %r9
	rorx	$63, %r14, %rcx
	xorq	%r8, %rsi
	xorq	24(%rsp), %rsi
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%rsi, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%rcx, %r13
	movq	-120(%rsp), %r14
	xorq	%r9, %r11
	xorq	%r9, %rdx
	xorq	%r9, %rdi
	rorx	$61, %r11, %r15
	rorx	$23, %rdx, %r11
	xorq	%rcx, %rax
	xorq	%rcx, %rbx
	xorq	%r9, %r14
	rorx	$46, %rdi, %rdx
	xorq	%r12, %rbp
	rorx	$19, %rbx, %rbx
	movq	%r14, 32(%rsp)
	movq	-80(%rsp), %r14
	xorq	%r9, %r14
	rorx	$28, %r14, %r14
	movq	%r14, 40(%rsp)
	movq	%r15, 48(%rsp)
	movq	-32(%rsp), %r14
	movq	%rdx, 64(%rsp)
	movq	-104(%rsp), %rdx
	movq	%r11, 56(%rsp)
	movq	-24(%rsp), %r11
	xorq	%rcx, %rdx
	movq	%rbx, 88(%rsp)
	rorx	$62, %rax, %rbx
	movq	-96(%rsp), %rax
	rorx	$63, %rdx, %rdi
	movq	%rdi, 72(%rsp)
	movq	-64(%rsp), %rdi
	xorq	%r10, %rax
	movq	-112(%rsp), %rdx
	movq	%rbx, 96(%rsp)
	xorq	%rcx, %rdi
	movq	-88(%rsp), %rcx
	rorx	$2, %rax, %rax
	movq	%rax, -120(%rsp)
	rorx	$20, %rdi, %r12
	rorx	$54, %r13, %rdi
	movq	%rdi, 80(%rsp)
	movq	-56(%rsp), %rdi
	movq	(%rsp), %r13
	movq	-8(%rsp), %rax
	xorq	%r10, %rdi
	xorq	%r10, %r14
	xorq	%rsi, %r11
	xorq	%rbp, %rcx
	rorx	$39, %r11, %r9
	xorq	%rsi, %r13
	xorq	%rbp, %r8
	xorq	%r10, %rax
	rorx	$37, %rcx, %r15
	movq	-40(%rsp), %r11
	rorx	$21, %r14, %r14
	xorq	%rsi, %rdx
	movq	-16(%rsp), %rcx
	movq	%r15, -24(%rsp)
	andn	%r14, %r12, %r15
	rorx	$43, %r13, %r13
	xorq	32(%rsp), %r15
	xorq	%rbp, %r11
	movq	-48(%rsp), %rbx
	rorx	$49, %rax, %rax
	xorq	%rbp, %rcx
	xorq	$32778, %r15
	xorq	24(%rsp), %rbp
	movq	%rax, -8(%rsp)
	rorx	$50, %rbp, %rbp
	andn	%r13, %r14, %rax
	movq	%r15, -112(%rsp)
	andn	%rbp, %r13, %r15
	xorq	%r14, %r15
	xorq	%r12, %rax
	xorq	8(%rsp), %r10
	xorq	%rsi, %rbx
	rorx	$44, %r11, %r11
	rorx	$3, %r10, %r10
	rorx	$36, %rdx, %rdx
	rorx	$58, %rdi, %rdi
	movq	%r15, -96(%rsp)
	rorx	$56, %r8, %r8
	rorx	$25, %rcx, %rcx
	rorx	$9, %rbx, %rbx
	movq	32(%rsp), %r15
	xorq	16(%rsp), %rsi
	movq	%rax, -104(%rsp)
	rorx	$8, %rsi, %rsi
	andn	%r15, %rbp, %r14
	andn	%r12, %r15, %r12
	xorq	%r13, %r14
	xorq	%rbp, %r12
	movq	%r14, -88(%rsp)
	movq	%r12, -80(%rsp)
	movq	48(%rsp), %r13
	movq	88(%rsp), %r14
	movq	64(%rsp), %rax
	andn	%r13, %r11, %rbp
	movq	%rbp, %r12
	movq	-24(%rsp), %r15
	andn	%r14, %r13, %rbp
	xorq	%r11, %rbp
	xorq	%rdx, %r12
	movq	%rbp, -56(%rsp)
	andn	%r10, %r14, %rbp
	xorq	%rbp, %r13
	andn	%rdx, %r10, %rbp
	xorq	%rbp, %r14
	movq	72(%rsp), %rbp
	andn	%r11, %rdx, %rdx
	xorq	%r10, %rdx
	movq	%rdx, -40(%rsp)
	andn	%r9, %rdi, %rdx
	movq	%rbp, %r10
	movq	%r12, -64(%rsp)
	xorq	%rdx, %r10
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%r14, -48(%rsp)
	movq	%rdx, %r12
	movq	40(%rsp), %r14
	andn	%rax, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rax, %r9
	andn	%rbp, %rax, %rdx
	xorq	%rdx, %r8
	movq	-8(%rsp), %rax
	andn	%rdi, %rbp, %rdx
	movq	%r14, %r11
	xorq	%rdx, %r9
	movq	80(%rsp), %rbp
	andn	%rax, %rbp, %rdi
	andn	%rbp, %r14, %rdx
	xorq	%rdi, %r11
	xorq	%r15, %rdx
	andn	%rsi, %rax, %rdi
	xorq	%rdi, %rbp
	andn	%r15, %rsi, %rdi
	xorq	%rdi, %rax
	andn	%r14, %r15, %rdi
	movq	56(%rsp), %r14
	movq	96(%rsp), %r15
	xorq	%rsi, %rdi
	movq	%rax, -8(%rsp)
	andn	%r15, %r14, %rsi
	xorq	%rcx, %rsi
	andn	%r14, %rcx, %rax
	movq	%rdi, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r14, %rsi
	andn	%rcx, %rbx, %rdi
	xorq	%rbx, %rax
	andn	-120(%rsp), %r15, %rcx
	xorq	%rcx, %rsi
	movq	-120(%rsp), %rcx
	movq	-96(%rsp), %r14
	xorq	-120(%rsp), %rdi
	movq	%rsi, 16(%rsp)
	andn	%rbx, %rcx, %rcx
	movq	%r15, %rbx
	movq	%rbp, -16(%rsp)
	xorq	%rcx, %rbx
	movq	-104(%rsp), %rcx
	movq	%r13, -120(%rsp)
	movq	%rbx, 24(%rsp)
	movq	-64(%rsp), %rbx
	xorq	%r10, %rbx
	xorq	-56(%rsp), %rcx
	xorq	%r13, %r14
	xorq	-32(%rsp), %r14
	xorq	%rdx, %rbx
	movq	%rcx, %r15
	xorq	%rbp, %r14
	xorq	8(%rsp), %r14
	xorq	%rdi, %rbx
	xorq	%r12, %r15
	xorq	-112(%rsp), %rbx
	movq	-88(%rsp), %r13
	movq	-40(%rsp), %rsi
	movq	(%rsp), %rbp
	xorq	%r11, %r15
	movq	%r9, -24(%rsp)
	xorq	-48(%rsp), %r13
	xorq	%rax, %r15
	rorx	$63, %r14, %rcx
	xorq	%rbx, %rcx
	xorq	%r8, %r13
	xorq	%r9, %rsi
	xorq	-8(%rsp), %r13
	xorq	-80(%rsp), %rsi
	xorq	16(%rsp), %r13
	xorq	%rbp, %rsi
	rorx	$63, %r15, %rbp
	rorx	$63, %rbx, %rbx
	xorq	24(%rsp), %rsi
	rorx	$63, %r13, %r9
	xorq	%r15, %r9
	xorq	%r13, %rbx
	movq	-112(%rsp), %r15
	xorq	%rsi, %rbp
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	xorq	%rbp, %rdx
	xorq	%rbp, %r10
	xorq	%rbp, %rdi
	xorq	%rbp, %r15
	rorx	$61, %r10, %r10
	rorx	$46, %rdi, %rdi
	movq	%rdi, 48(%rsp)
	movq	%r15, -112(%rsp)
	movq	-64(%rsp), %r15
	movq	%r10, -64(%rsp)
	rorx	$23, %rdx, %r10
	movq	-104(%rsp), %rdx
	xorq	%rbp, %r15
	movq	%r10, 40(%rsp)
	xorq	%rcx, %rdx
	rorx	$28, %r15, %r15
	movq	%r15, 32(%rsp)
	rorx	$63, %rdx, %rdx
	movq	%rdx, 56(%rsp)
	movq	-56(%rsp), %rdx
	xorq	%rcx, %rdx
	xorq	%rcx, %r12
	xorq	%rcx, %r11
	xorq	%rcx, %rax
	rorx	$19, %r11, %r14
	rorx	$62, %rax, %r11
	movq	-120(%rsp), %rax
	rorx	$20, %rdx, %rbp
	movq	%r11, 72(%rsp)
	movq	-96(%rsp), %r11
	rorx	$54, %r12, %rdx
	xorq	%rsi, %r8
	xorq	%r9, %rax
	movq	%rdx, -56(%rsp)
	movq	-88(%rsp), %rdx
	rorx	$39, %r8, %r8
	rorx	$58, %rax, %r13
	movq	-16(%rsp), %rax
	movq	%r13, 80(%rsp)
	xorq	%r9, %r11
	movq	-32(%rsp), %r13
	movq	%r14, 64(%rsp)
	xorq	%rsi, %rdx
	rorx	$2, %r11, %r11
	xorq	%r9, %rax
	rorx	$36, %rdx, %rdx
	rorx	$49, %rax, %rax
	movq	%rax, -16(%rsp)
	movq	-48(%rsp), %rax
	xorq	%r9, %r13
	xorq	8(%rsp), %r9
	rorx	$21, %r13, %r13
	andn	%r13, %rbp, %r14
	xorq	%rsi, %rax
	rorx	$3, %r9, %r9
	rorx	$9, %rax, %r15
	movq	%r15, 8(%rsp)
	movq	-8(%rsp), %r12
	movabsq	$-9223372034707292150, %r15
	movq	-40(%rsp), %rdi
	movq	-80(%rsp), %rax
	movq	-24(%rsp), %rcx
	xorq	-112(%rsp), %r14
	xorq	%rsi, %r12
	xorq	%rbx, %rdi
	xorq	%r14, %r15
	rorx	$43, %r12, %r12
	xorq	%rbx, %rax
	rorx	$44, %rdi, %r10
	movq	(%rsp), %rdi
	andn	%r12, %r13, %r14
	xorq	%rbx, %rcx
	xorq	%rbp, %r14
	xorq	16(%rsp), %rsi
	rorx	$37, %rax, %rax
	rorx	$25, %rcx, %rcx
	xorq	%rbx, %rdi
	xorq	24(%rsp), %rbx
	movq	%r14, -104(%rsp)
	rorx	$8, %rsi, %rsi
	rorx	$50, %rbx, %rbx
	andn	%rbx, %r12, %r14
	xorq	%r13, %r14
	rorx	$56, %rdi, %rdi
	movq	%r14, -96(%rsp)
	movq	-112(%rsp), %r14
	movq	%r15, -120(%rsp)
	movq	-16(%rsp), %r15
	andn	%r14, %rbx, %r13
	xorq	%r12, %r13
	movq	-64(%rsp), %r12
	andn	%rbp, %r14, %rbp
	movq	64(%rsp), %r14
	xorq	%rbx, %rbp
	movq	%r13, -112(%rsp)
	andn	%r12, %r10, %rbx
	xorq	%rdx, %rbx
	movq	%rbp, -88(%rsp)
	movq	80(%rsp), %rbp
	movq	%rbx, -80(%rsp)
	andn	%r14, %r12, %rbx
	xorq	%r10, %rbx
	movq	%rbx, -64(%rsp)
	andn	%r9, %r14, %rbx
	xorq	%rbx, %r12
	andn	%rdx, %r9, %rbx
	xorq	%rbx, %r14
	movq	56(%rsp), %rbx
	andn	%r10, %rdx, %rdx
	movq	%rbp, %r13
	movq	48(%rsp), %r10
	xorq	%r9, %rdx
	movq	%r14, -48(%rsp)
	movq	%rbx, %r9
	movq	%rdx, -40(%rsp)
	andn	%r8, %rbp, %rdx
	xorq	%rdx, %r9
	andn	%rdi, %r8, %rdx
	xorq	%rdx, %r13
	andn	%r10, %rdi, %rdx
	xorq	%r8, %rdx
	andn	%rbx, %r10, %r8
	xorq	%rdi, %r8
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rbx, %rdx
	movq	32(%rsp), %rbp
	xorq	%rdx, %r10
	movq	%r8, -24(%rsp)
	movq	-56(%rsp), %r8
	movq	%rbp, %rbx
	andn	%r15, %r8, %rdi
	andn	%r8, %rbp, %rdx
	xorq	%rdi, %rbx
	andn	%rsi, %r15, %rdi
	xorq	%rdi, %r8
	andn	%rax, %rsi, %rdi
	xorq	%rdi, %r15
	xorq	%rax, %rdx
	movq	%r8, -8(%rsp)
	andn	%rbp, %rax, %rax
	movq	40(%rsp), %rbp
	xorq	%rsi, %rax
	movq	%r15, (%rsp)
	movq	8(%rsp), %r15
	movq	%rax, %r8
	movq	72(%rsp), %r14
	andn	%rbp, %rcx, %rax
	movq	%r12, -56(%rsp)
	xorq	%r15, %rax
	andn	%rcx, %r15, %rdi
	xorq	%r11, %rdi
	movq	%r10, -16(%rsp)
	andn	%r14, %rbp, %rsi
	xorq	%rcx, %rsi
	andn	%r11, %r14, %rcx
	xorq	%rcx, %rbp
	movq	%rsi, 8(%rsp)
	andn	%r15, %r11, %rcx
	movq	%r14, %rsi
	movq	-104(%rsp), %r11
	xorq	-64(%rsp), %r11
	xorq	%rcx, %rsi
	movq	-96(%rsp), %r14
	movq	%rbp, 16(%rsp)
	movq	%r11, %r15
	movq	%rsi, 24(%rsp)
	movq	-40(%rsp), %rsi
	xorq	%r13, %r15
	movq	-80(%rsp), %rbp
	xorq	%r12, %r14
	movq	-112(%rsp), %r12
	xorq	%rbx, %r15
	xorq	-48(%rsp), %r12
	xorq	%r10, %rsi
	xorq	-24(%rsp), %r12
	xorq	%rax, %r15
	xorq	(%rsp), %r12
	xorq	-88(%rsp), %rsi
	xorq	%r9, %rbp
	xorq	16(%rsp), %r12
	xorq	%r8, %rsi
	rorx	$63, %r15, %r11
	xorq	%rdx, %rbp
	xorq	24(%rsp), %rsi
	rorx	$63, %r12, %r10
	xorq	%r15, %r10
	movq	-120(%rsp), %r15
	xorq	%rsi, %r11
	xorq	%rdi, %rbp
	xorq	-120(%rsp), %rbp
	xorq	-32(%rsp), %r14
	xorq	%r11, %r15
	xorq	-8(%rsp), %r14
	xorq	8(%rsp), %r14
	rorx	$63, %rsi, %rsi
	movq	%r15, -120(%rsp)
	movq	-80(%rsp), %r15
	xorq	%r14, %rsi
	rorx	$63, %r14, %rcx
	xorq	%rbp, %rcx
	rorx	$63, %rbp, %rbp
	xorq	%r12, %rbp
	xorq	%r11, %r15
	xorq	%r11, %r9
	xorq	%r11, %rdx
	xorq	%r11, %rdi
	rorx	$61, %r9, %r9
	xorq	%rcx, %r13
	xorq	%rcx, %rax
	xorq	%rcx, %rbx
	movq	%r9, -80(%rsp)
	rorx	$23, %rdx, %r9
	rorx	$46, %rdi, %rdx
	rorx	$54, %r13, %r14
	movq	%rdx, 48(%rsp)
	movq	-104(%rsp), %rdx
	rorx	$28, %r15, %r15
	rorx	$19, %rbx, %rbx
	movq	%r15, 32(%rsp)
	xorq	%rbp, %r8
	xorq	%rcx, %rdx
	movq	%r9, 40(%rsp)
	rorx	$56, %r8, %r8
	rorx	$63, %rdx, %rdi
	movq	%rdi, 56(%rsp)
	movq	-64(%rsp), %rdi
	movq	%r14, 64(%rsp)
	movq	-96(%rsp), %r14
	movq	%rbx, -64(%rsp)
	rorx	$62, %rax, %rbx
	movq	-8(%rsp), %rax
	xorq	%rcx, %rdi
	xorq	%r10, %r14
	rorx	$20, %rdi, %r12
	movq	-16(%rsp), %rcx
	movq	(%rsp), %r13
	xorq	%r10, %rax
	rorx	$2, %r14, %rdi
	movq	-32(%rsp), %r14
	movq	%rdi, 80(%rsp)
	rorx	$49, %rax, %rax
	movq	-56(%rsp), %rdi
	movq	%rax, -56(%rsp)
	xorq	%rbp, %rcx
	movq	-48(%rsp), %rax
	xorq	%r10, %r14
	movq	-24(%rsp), %r9
	xorq	%rsi, %r13
	rorx	$21, %r14, %r14
	rorx	$25, %rcx, %rcx
	andn	%r14, %r12, %r15
	movq	%rcx, -24(%rsp)
	xorq	-120(%rsp), %r15
	xorq	%rsi, %rax
	rorx	$43, %r13, %r13
	movabsq	$-9223372034707259263, %rcx
	xorq	%r15, %rcx
	movq	-40(%rsp), %r11
	andn	%r13, %r14, %r15
	movq	%rbx, 72(%rsp)
	xorq	%r12, %r15
	rorx	$9, %rax, %rbx
	movq	-88(%rsp), %rax
	xorq	%r10, %rdi
	movq	-112(%rsp), %rdx
	movq	%r15, -104(%rsp)
	xorq	%rbp, %r11
	xorq	%rsi, %r9
	movq	-120(%rsp), %r15
	xorq	%rbp, %rax
	xorq	24(%rsp), %rbp
	movq	%rcx, -112(%rsp)
	rorx	$50, %rbp, %rbp
	xorq	8(%rsp), %r10
	andn	%rbp, %r13, %rcx
	xorq	%rsi, %rdx
	xorq	%r14, %rcx
	andn	%r15, %rbp, %r14
	xorq	16(%rsp), %rsi
	xorq	%r13, %r14
	andn	%r12, %r15, %r12
	movq	-80(%rsp), %r13
	movq	-64(%rsp), %r15
	xorq	%rbp, %r12
	rorx	$44, %r11, %r11
	rorx	$3, %r10, %r10
	movq	%r12, -88(%rsp)
	rorx	$36, %rdx, %rdx
	andn	%r13, %r11, %rbp
	movq	%rbp, %r12
	andn	%r15, %r13, %rbp
	xorq	%r11, %rbp
	xorq	%rdx, %r12
	andn	%r11, %rdx, %r11
	movq	%rbp, -64(%rsp)
	xorq	%r10, %r11
	andn	%r10, %r15, %rbp
	xorq	%rbp, %r13
	andn	%rdx, %r10, %rbp
	xorq	%rbp, %r15
	movq	%rcx, -96(%rsp)
	rorx	$58, %rdi, %rdi
	rorx	$39, %r9, %r9
	andn	%r9, %rdi, %rdx
	movq	%r14, -120(%rsp)
	rorx	$8, %rsi, %rsi
	rorx	$37, %rax, %rax
	movq	%r12, -80(%rsp)
	movq	%r15, -48(%rsp)
	movq	%r11, -40(%rsp)
	movq	56(%rsp), %rbp
	movq	48(%rsp), %rcx
	movq	32(%rsp), %r15
	movq	%rbp, %r10
	movq	-56(%rsp), %r14
	movq	%r13, -56(%rsp)
	xorq	%rdx, %r10
	andn	%r8, %r9, %rdx
	xorq	%rdi, %rdx
	movq	%r15, %r11
	movq	%rdx, %r12
	andn	%rcx, %r8, %rdx
	xorq	%r9, %rdx
	movq	%rcx, %r9
	movq	%rdx, -32(%rsp)
	andn	%rbp, %rcx, %rdx
	xorq	%rdx, %r8
	andn	%rdi, %rbp, %rdx
	movq	64(%rsp), %rbp
	xorq	%rdx, %r9
	andn	%r14, %rbp, %rdi
	andn	%rbp, %r15, %rdx
	xorq	%rdi, %r11
	xorq	%rax, %rdx
	andn	%rsi, %r14, %rdi
	xorq	%rdi, %rbp
	andn	%rax, %rsi, %rdi
	andn	%r15, %rax, %rax
	xorq	%rdi, %r14
	xorq	%rsi, %rax
	movq	-24(%rsp), %rsi
	movq	40(%rsp), %r15
	movq	%r14, (%rsp)
	movq	72(%rsp), %r14
	movq	%rdx, -16(%rsp)
	movq	%rsi, %rdx
	andn	%rsi, %rbx, %rdi
	xorq	80(%rsp), %rdi
	movq	%rax, 8(%rsp)
	andn	%r15, %rsi, %rax
	andn	%r14, %r15, %rsi
	xorq	%rdx, %rsi
	movq	80(%rsp), %rdx
	movq	%rsi, 16(%rsp)
	movq	%r15, %rsi
	xorq	%rbx, %rax
	movq	%rbp, -8(%rsp)
	movq	-104(%rsp), %r15
	andn	%rdx, %r14, %rcx
	xorq	%rcx, %rsi
	andn	%rbx, %rdx, %rcx
	movq	%r14, %rbx
	xorq	%rcx, %rbx
	movq	-96(%rsp), %rcx
	movq	-32(%rsp), %r14
	movq	%rsi, 24(%rsp)
	movq	%rbx, %rdx
	movq	-80(%rsp), %rbx
	movq	-40(%rsp), %rsi
	movq	%r9, -24(%rsp)
	xorq	%r13, %rcx
	movq	-120(%rsp), %r13
	xorq	-48(%rsp), %r13
	xorq	%rcx, %r14
	xorq	%r10, %rbx
	xorq	-16(%rsp), %rbx
	xorq	-64(%rsp), %r15
	xorq	%rbp, %r14
	movq	16(%rsp), %rbp
	xorq	%rdi, %rbx
	xorq	%r8, %r13
	xorq	-112(%rsp), %rbx
	xorq	(%rsp), %r13
	xorq	%r9, %rsi
	xorq	%r12, %r15
	xorq	%rbp, %r14
	xorq	24(%rsp), %r13
	xorq	-88(%rsp), %rsi
	xorq	%r11, %r15
	movq	8(%rsp), %rbp
	xorq	%rax, %r15
	rorx	$63, %r14, %rcx
	rorx	$63, %r13, %r9
	xorq	%rbx, %rcx
	movq	%rdx, 32(%rsp)
	rorx	$63, %rbx, %rbx
	xorq	%rbp, %rsi
	rorx	$63, %r15, %rbp
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	xorq	%rsi, %rbp
	xorq	%r15, %r9
	rorx	$63, %rsi, %rsi
	xorq	%r14, %rsi
	movq	-112(%rsp), %r14
	xorq	%rbp, %rdx
	xorq	%rbp, %r10
	xorq	%rcx, %r12
	rorx	$61, %r10, %r10
	xorq	%rcx, %rax
	xorq	%rbp, %rdi
	xorq	%r13, %rbx
	xorq	%rbp, %r14
	movq	%r10, 40(%rsp)
	rorx	$46, %rdi, %rdi
	xorq	%rcx, %r11
	movq	%r14, -112(%rsp)
	movq	-80(%rsp), %r14
	xorq	%rsi, %r8
	rorx	$19, %r11, %r11
	movq	%rdi, 48(%rsp)
	movq	-96(%rsp), %rdi
	rorx	$39, %r8, %r8
	xorq	%rbp, %r14
	rorx	$28, %r14, %r14
	movq	%r14, -80(%rsp)
	rorx	$23, %rdx, %r14
	xorq	%r9, %rdi
	movq	-104(%rsp), %rdx
	rorx	$2, %rdi, %r15
	movq	%r15, 80(%rsp)
	movq	-32(%rsp), %rdi
	movq	%r14, -16(%rsp)
	xorq	%rcx, %rdx
	rorx	$63, %rdx, %r10
	movq	-64(%rsp), %rdx
	xorq	%r9, %rdi
	movq	%r10, 56(%rsp)
	rorx	$21, %rdi, %r13
	movq	-40(%rsp), %r10
	xorq	%rcx, %rdx
	movq	-24(%rsp), %rcx
	rorx	$20, %rdx, %rbp
	rorx	$54, %r12, %rdx
	rorx	$62, %rax, %r12
	movq	-56(%rsp), %rax
	movq	%rdx, 64(%rsp)
	movq	-120(%rsp), %rdx
	andn	%r13, %rbp, %r14
	xorq	%rbx, %r10
	xorq	%r9, %rax
	movq	%r12, 72(%rsp)
	movq	(%rsp), %r12
	xorq	%rbx, %rcx
	rorx	$58, %rax, %r15
	movq	-8(%rsp), %rax
	movq	%r15, 88(%rsp)
	xorq	%rsi, %rdx
	xorq	%rsi, %r12
	rorx	$44, %r10, %r10
	rorx	$36, %rdx, %rdx
	rorx	$25, %rcx, %rcx
	xorq	%r9, %rax
	xorq	16(%rsp), %r9
	rorx	$43, %r12, %r12
	rorx	$49, %rax, %r15
	movq	-48(%rsp), %rax
	movq	%r15, -8(%rsp)
	rorx	$3, %r9, %r9
	movabsq	$-9223372036854742912, %r15
	xorq	%rsi, %rax
	xorq	24(%rsp), %rsi
	rorx	$9, %rax, %rax
	movq	%rax, -120(%rsp)
	movq	-88(%rsp), %rax
	rorx	$8, %rsi, %rsi
	movq	8(%rsp), %rdi
	xorq	-112(%rsp), %r14
	xorq	%r14, %r15
	xorq	%rbx, %rax
	andn	%r12, %r13, %r14
	xorq	%rbx, %rdi
	xorq	32(%rsp), %rbx
	xorq	%rbp, %r14
	rorx	$37, %rax, %rax
	rorx	$50, %rbx, %rbx
	movq	%r14, -104(%rsp)
	andn	%rbx, %r12, %r14
	xorq	%r13, %r14
	movq	%r14, -96(%rsp)
	movq	-112(%rsp), %r14
	rorx	$56, %rdi, %rdi
	andn	%rbp, %r14, %rbp
	xorq	%rbx, %rbp
	andn	%r14, %rbx, %r13
	xorq	%r12, %r13
	movq	%rbp, -56(%rsp)
	movq	40(%rsp), %rbp
	andn	%rdx, %r9, %r12
	xorq	%r11, %r12
	movq	%r12, -48(%rsp)
	movq	-16(%rsp), %r14
	andn	%rbp, %r10, %rbx
	xorq	%rdx, %rbx
	andn	%r10, %rdx, %rdx
	xorq	%r9, %rdx
	movq	%rbx, -112(%rsp)
	andn	%r11, %rbp, %rbx
	xorq	%r10, %rbx
	movq	56(%rsp), %r10
	movq	%rbx, -88(%rsp)
	andn	%r9, %r11, %rbx
	movq	88(%rsp), %r9
	xorq	%rbx, %rbp
	movq	48(%rsp), %rbx
	movq	%r10, %r11
	movq	%rdx, -40(%rsp)
	movq	%r9, %r12
	andn	%r8, %r9, %rdx
	xorq	%rdx, %r11
	andn	%rdi, %r8, %rdx
	xorq	%rdx, %r12
	andn	%rbx, %rdi, %rdx
	xorq	%r8, %rdx
	movq	%r13, -64(%rsp)
	movq	-8(%rsp), %r8
	movq	-80(%rsp), %r13
	movq	%rdx, -32(%rsp)
	andn	%r10, %rbx, %rdx
	xorq	%rdi, %rdx
	movq	%rdx, -24(%rsp)
	andn	%r9, %r10, %rdx
	movq	64(%rsp), %r9
	xorq	%rdx, %rbx
	andn	%rsi, %r8, %rdx
	andn	%r9, %r13, %r10
	andn	%r8, %r9, %rdi
	xorq	%rax, %r10
	xorq	%r13, %rdi
	xorq	%rdx, %r9
	andn	%rax, %rsi, %rdx
	xorq	%rdx, %r8
	andn	%r13, %rax, %rax
	movq	-120(%rsp), %rdx
	movq	72(%rsp), %r13
	movq	%r8, (%rsp)
	xorq	%rsi, %rax
	movq	80(%rsp), %r8
	movq	%rax, 8(%rsp)
	andn	%r14, %rcx, %rax
	andn	%rcx, %rdx, %rsi
	xorq	%rdx, %rax
	andn	%r13, %r14, %rdx
	xorq	%rcx, %rdx
	xorq	%r8, %rsi
	andn	%r8, %r13, %rcx
	xorq	%rcx, %r14
	andn	-120(%rsp), %r8, %rcx
	movq	-112(%rsp), %r8
	xorq	%rcx, %r13
	movq	%r14, 16(%rsp)
	movq	%r13, 24(%rsp)
	xorq	%r11, %r8
	movq	%r15, -120(%rsp)
	movq	-104(%rsp), %rcx
	movq	-96(%rsp), %r14
	xorq	%r10, %r8
	xorq	-88(%rsp), %rcx
	movq	%r9, -8(%rsp)
	xorq	%rsi, %r8
	movq	%rbp, -80(%rsp)
	movq	-64(%rsp), %r13
	xorq	%rbp, %r14
	xorq	-32(%rsp), %r14
	xorq	%r15, %r8
	movq	%rcx, %r15
	xorq	%r9, %r14
	movq	-40(%rsp), %r9
	movq	-56(%rsp), %rbp
	xorq	%r12, %r15
	xorq	%rdi, %r15
	xorq	%rdx, %r14
	xorq	-48(%rsp), %r13
	xorq	-24(%rsp), %r13
	xorq	%rbx, %r9
	xorq	%rax, %r15
	xorq	(%rsp), %r13
	xorq	16(%rsp), %r13
	xorq	%rbp, %r9
	movq	24(%rsp), %rbp
	xorq	8(%rsp), %r9
	movq	%rbx, -16(%rsp)
	rorx	$63, %r13, %rcx
	rorx	$63, %r14, %rbx
	xorq	%r8, %rbx
	rorx	$63, %r8, %r8
	xorq	%rbp, %r9
	rorx	$63, %r15, %rbp
	xorq	%r13, %r8
	xorq	%rbx, %rax
	xorq	%r9, %rbp
	xorq	%rbx, %rdi
	rorx	$63, %r9, %r9
	xorq	%r14, %r9
	xorq	%rbp, %r10
	xorq	%rbp, %rsi
	xorq	%rbp, %r11
	movq	-112(%rsp), %r13
	rorx	$61, %r11, %r11
	movq	%r11, -112(%rsp)
	rorx	$23, %r10, %r11
	rorx	$46, %rsi, %r10
	movq	-104(%rsp), %rsi
	rorx	$62, %rax, %r14
	xorq	%r15, %rcx
	xorq	%rbp, %r13
	movq	%r11, 64(%rsp)
	movq	-80(%rsp), %rax
	xorq	%rcx, %rdx
	xorq	%rbx, %r12
	xorq	%rbx, %rsi
	rorx	$19, %rdi, %rdi
	movq	%rdi, 48(%rsp)
	movq	-96(%rsp), %rdi
	rorx	$63, %rsi, %r11
	xorq	%rcx, %rax
	movq	-88(%rsp), %rsi
	movq	-120(%rsp), %r15
	xorq	%rcx, %rdi
	rorx	$28, %r13, %r13
	rorx	$58, %rax, %rax
	movq	%r13, -120(%rsp)
	xorq	%rbx, %rsi
	movq	%r11, 40(%rsp)
	rorx	$2, %rdi, %rdi
	xorq	%rbp, %r15
	movq	%r14, 56(%rsp)
	rorx	$20, %rsi, %rsi
	rorx	$54, %r12, %r12
	movq	%rsi, -104(%rsp)
	movq	%rdi, -96(%rsp)
	movq	%rax, -88(%rsp)
	movq	%r10, 32(%rsp)
	movq	-32(%rsp), %r10
	movq	-8(%rsp), %rax
	movq	-64(%rsp), %rsi
	movq	%r15, -64(%rsp)
	xorq	%rcx, %r10
	movq	-48(%rsp), %r13
	movq	-40(%rsp), %rdi
	xorq	%rcx, %rax
	rorx	$21, %r10, %rbp
	movq	(%rsp), %r11
	xorq	%r9, %rsi
	movq	-56(%rsp), %rcx
	movq	-16(%rsp), %rbx
	xorq	%r9, %r13
	xorq	%r8, %rdi
	rorx	$49, %rax, %r14
	rorx	$3, %rdx, %r10
	xorq	%r9, %r11
	rorx	$44, %rdi, %rdi
	movq	%r14, -80(%rsp)
	movq	-24(%rsp), %rdx
	xorq	%r8, %rcx
	xorq	%r8, %rbx
	rorx	$37, %rcx, %rcx
	rorx	$9, %r13, %r13
	rorx	$36, %rsi, %rsi
	rorx	$25, %rbx, %rbx
	movq	%r10, -32(%rsp)
	movq	-104(%rsp), %r14
	xorq	%r9, %rdx
	rorx	$43, %r11, %r11
	movq	8(%rsp), %r10
	xorq	16(%rsp), %r9
	rorx	$39, %rdx, %rdx
	movq	-112(%rsp), %rax
	rorx	$8, %r9, %r9
	xorq	%r8, %r10
	xorq	24(%rsp), %r8
	andn	%rbp, %r14, %r14
	xorq	%r15, %r14
	movl	$2147483649, %r15d
	rorx	$56, %r10, %r10
	rorx	$50, %r8, %r8
	xorq	%r14, %r15
	andn	48(%rsp), %rax, %r14
	xorq	%rdi, %r14
	movq	%r15, -56(%rsp)
	andn	%rcx, %r9, %r15
	xorq	-80(%rsp), %r15
	movq	%r15, -24(%rsp)
	movq	-96(%rsp), %r15
	movq	%r14, -48(%rsp)
	andn	32(%rsp), %r10, %r14
	xorq	%rdx, %r14
	movq	%r14, -40(%rsp)
	andn	%r13, %r15, %r14
	movq	56(%rsp), %r15
	xorq	%r14, %r15
	movq	40(%rsp), %r14
	xorq	-96(%rsp), %r14
	xorq	%rsi, %r14
	movq	%r15, -16(%rsp)
	andn	%rax, %rdi, %r15
	movq	-88(%rsp), %rax
	xorq	%rcx, %r14
	xorq	%r15, %r14
	andn	%rdx, %rax, %r15
	movq	-120(%rsp), %rax
	xorq	%r14, %r15
	andn	%r12, %rax, %r14
	xorq	%r15, %r14
	andn	%rbx, %r13, %r15
	xorq	%r15, %r14
	movq	-56(%rsp), %r15
	xorq	%r14, %r15
	movq	-104(%rsp), %r14
	xorq	%rax, %r14
	xorq	-88(%rsp), %r14
	movq	-80(%rsp), %rax
	xorq	%r14, %r13
	andn	%r11, %rbp, %r14
	xorq	%r14, %r13
	andn	%r10, %rdx, %r14
	andn	-80(%rsp), %r12, %rdx
	xorq	%r13, %r14
	xorq	%r14, %rdx
	xorq	-112(%rsp), %r12
	movq	64(%rsp), %r14
	andn	%r9, %rax, %rax
	xorq	%rbp, %r12
	andn	%r8, %r11, %rbp
	xorq	%rbx, %r12
	andn	%r14, %rbx, %r13
	xorq	%r13, %rdx
	movq	48(%rsp), %r13
	xorq	%r12, %rbp
	movq	-32(%rsp), %r12
	xorq	-48(%rsp), %rdx
	andn	%r12, %r13, %rbx
	xorq	%rbp, %rbx
	movq	%r14, %rbp
	movq	56(%rsp), %r14
	xorq	%rbx, %rax
	andn	%r14, %rbp, %rbx
	xorq	%rbx, %rax
	movq	%r13, %rbx
	xorq	-40(%rsp), %rax
	xorq	%rbp, %rbx
	movq	40(%rsp), %rbp
	xorq	%r11, %rbx
	movq	-64(%rsp), %r11
	xorq	%r10, %rbx
	andn	%r11, %r8, %r10
	xorq	%rbx, %r10
	andn	%rsi, %r12, %rbx
	xorq	32(%rsp), %r12
	xorq	%r10, %rbx
	movq	32(%rsp), %r10
	andn	%rbp, %r10, %r10
	xorq	%r10, %rbx
	andn	-96(%rsp), %r14, %r10
	movq	-24(%rsp), %r14
	xorq	%r10, %rbx
	movq	%r12, %r10
	xorq	%r9, %r10
	xorq	%r14, %rbx
	xorq	%r8, %r10
	andn	-104(%rsp), %r11, %r8
	movq	-16(%rsp), %r11
	xorq	%r8, %r10
	andn	%rdi, %rsi, %rsi
	andn	-120(%rsp), %rcx, %rcx
	rorx	$63, %rdx, %rdi
	xorq	%rsi, %r10
	andn	-88(%rsp), %rbp, %rsi
	rorx	$63, %rax, %r8
	xorq	%r14, %rax
	xorq	%r10, %rsi
	addq	$1, -72(%rsp)
	xorq	%rcx, %rsi
	movq	-56(%rsp), %rcx
	xorq	%r11, %rsi
	xorq	%rsi, %rcx
	rorx	$63, %rsi, %rsi
	xorq	%rax, %rsi
	rorx	$63, %r15, %rax
	xorq	%rcx, %rdi
	movq	-48(%rsp), %rcx
	rorx	$43, %rsi, %r9
	xorq	%r15, %rcx
	xorq	%rcx, %r8
	movq	-40(%rsp), %rcx
	rorx	$20, %r8, %r8
	xorq	%rdx, %rcx
	rorx	$63, %rbx, %rdx
	xorq	%rcx, %rdx
	movq	%r11, %rcx
	xorq	%rbx, %rcx
	rorx	$21, %rdx, %rdx
	andn	%rdx, %r8, %rsi
	xorq	%rdi, %rsi
	xorq	%rcx, %rax
	movabsq	$-9223372034707259384, %rcx
	rorx	$50, %rax, %rax
	xorq	%rcx, %rsi
	andn	%r9, %rdx, %rcx
	xorq	%rcx, %r8
	andn	%rax, %r9, %rcx
	andn	%rdi, %rax, %rax
	xorq	%rdx, %rcx
	movq	-72(%rsp), %rdi
	xorq	%r9, %rax
	cmpq	%rdi, 104(%rsp)
	jne	.L50
	movq	%rsi, %xmm1
	movq	%r8, %xmm6
	movq	%rcx, %xmm0
	movq	112(%rsp), %rdi
	movq	%rax, %xmm7
	punpcklqdq	%xmm6, %xmm1
	punpcklqdq	%xmm7, %xmm0
.L49:
	movups	%xmm1, (%rdi)
	movups	%xmm0, 16(%rdi)
	subq	$-128, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L55:
	.cfi_restore_state
	movdqa	%xmm3, %xmm1
	movdqa	%xmm2, %xmm0
	jmp	.L49
	.cfi_endproc
.LFE98:
	.size	chain_bmi, .-chain_bmi
	.p2align 4
	.type	chain_scalar, @function
chain_scalar:
.LFB96:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	addq	$-128, %rsp
	.cfi_def_cfa_offset 184
	movdqu	(%rsi), %xmm3
	movdqu	16(%rsi), %xmm2
	movq	%rdx, 104(%rsp)
	testq	%rdx, %rdx
	je	.L65
	movq	%rdi, 112(%rsp)
	movhlps	%xmm3, %xmm4
	movhlps	%xmm2, %xmm5
	movq	%xmm2, %rsi
	movq	%xmm4, %rcx
	movq	%xmm5, %r8
	movq	%xmm3, %rdx
	movq	$0, -64(%rsp)
	.p2align 4
	.p2align 3
.L60:
	movq	%rsi, %r11
	movq	%rdx, %rdi
	movq	%rcx, %r9
	movq	%r8, %rax
	shldq	$8, %rcx, %r11
	shldq	$8, %rdx, %r9
	movq	%r8, %rdx
	movabsq	$9223372036854775807, %r8
	salq	$8, %rdi
	movq	%r11, %r13
	xorq	%r9, %r8
	shldq	$8, %rsi, %rdx
	orq	$67, %rdi
	notq	%r13
	shrq	$56, %rax
	movq	%r8, %r12
	movq	%rdi, %rcx
	movq	%r13, %r10
	orb	$1, %ah
	movq	%rdx, %rbp
	notq	%rcx
	rolq	%r12
	notq	%rbp
	movq	%rax, %rbx
	rolq	%r10
	xorq	%rax, %r12
	movq	%rbp, %rsi
	rolq	%rbx
	xorq	%rcx, %r10
	movq	%r12, %r14
	rolq	%rsi
	movq	%r12, %r15
	xorq	%r10, %r9
	rorq	$28, %r14
	xorq	%r8, %rsi
	movq	%rbx, %r8
	rolq	%rcx
	notq	%r9
	movq	%r14, (%rsp)
	movq	%r12, %r14
	xorq	%rbp, %rcx
	rolq	%r9
	movq	%r10, %rbp
	xorq	%r13, %r8
	movq	%r9, -32(%rsp)
	xorq	%rsi, %r13
	rolq	$3, %r15
	xorq	%r12, %rdi
	rorq	$23, %r14
	rolq	$10, %rbp
	movq	%r15, -80(%rsp)
	notq	%r12
	movq	%rbp, 16(%rsp)
	movq	%r10, %r15
	movq	%r13, %rbp
	rolq	$18, %r12
	movq	%r14, 8(%rsp)
	movq	%r10, %r14
	rorq	$2, %rbp
	movq	%rsi, %r13
	rorq	$20, %r15
	rolq	$2, %r14
	notq	%r13
	movabsq	$-9223372036854775808, %r9
	xorq	%r10, %r9
	movq	%rsi, %r10
	movq	%r14, 24(%rsp)
	movq	%r13, %r14
	rorq	$19, %r9
	rolq	$6, %r10
	xorq	%rcx, %rax
	xorq	%rbx, %r11
	rolq	$27, %rax
	movq	%r8, %rbx
	rorq	$21, %r14
	movq	%r15, -112(%rsp)
	movq	%rax, 56(%rsp)
	movq	%rcx, %rax
	rolq	$15, %r13
	orq	%r14, %r15
	rolq	$21, %rbx
	rolq	$20, %rax
	movq	%r13, 32(%rsp)
	xorq	%rdi, %r15
	rorq	$9, %r11
	movq	%rbx, %r13
	movq	%rax, %rbx
	movq	%rcx, %rax
	rorq	$25, %rax
	xorq	%r8, %rdx
	movq	%r11, 40(%rsp)
	movq	%r8, %r11
	movq	%rax, 64(%rsp)
	rorq	$8, %r8
	movq	%r15, %rax
	movq	%r14, %r15
	xorq	$1, %rax
	notq	%r15
	movq	%r8, 48(%rsp)
	movq	%rcx, %r8
	movq	%rax, -104(%rsp)
	rolq	$14, %rcx
	orq	%r13, %r15
	rolq	$28, %rdx
	movq	-112(%rsp), %rax
	rorq	$3, %rsi
	rolq	$25, %r11
	rolq	$8, %r8
	xorq	%r15, %rax
	movq	%r13, %r15
	andq	%rcx, %r15
	movq	%rax, -96(%rsp)
	xorq	%r14, %r15
	movq	%rdi, %r14
	andq	-112(%rsp), %rdi
	xorq	%rcx, %rdi
	orq	%rcx, %r14
	movq	%rdi, -112(%rsp)
	movq	-80(%rsp), %rdi
	movq	%r14, %rax
	xorq	%r13, %rax
	movq	-32(%rsp), %r13
	movq	%rdi, %rcx
	movq	%rax, -88(%rsp)
	orq	%rbx, %rcx
	xorq	%rdx, %rcx
	movq	%rcx, -80(%rsp)
	movq	%rdi, %rcx
	andq	%r9, %rcx
	xorq	%rbx, %rcx
	movq	%rcx, -72(%rsp)
	movq	%rsi, %rcx
	notq	%rcx
	orq	%r9, %rcx
	xorq	%rcx, %rdi
	movq	%rsi, %rcx
	orq	%rdx, %rcx
	andq	%rbx, %rdx
	movq	%r12, %rbx
	movq	%rdi, -56(%rsp)
	xorq	%rsi, %rdx
	movq	%r8, %rsi
	xorq	%r9, %rcx
	andq	%r11, %r8
	notq	%rsi
	movq	%rdx, -40(%rsp)
	xorq	%r10, %r8
	movq	%rsi, %rdx
	movq	%r10, %rsi
	movq	%rcx, -48(%rsp)
	orq	%r11, %rsi
	andq	%rdx, %rbx
	movq	%r8, -32(%rsp)
	movq	%rsi, %rcx
	movq	%r13, %rsi
	xorq	%r11, %rbx
	movq	32(%rsp), %r11
	xorq	%rcx, %rsi
	movq	%r13, %rcx
	andq	%r10, %r13
	movq	%rbx, -24(%rsp)
	orq	%r12, %rcx
	movq	16(%rsp), %r10
	movq	%rcx, %r9
	movq	%r11, %rcx
	xorq	%rdx, %r9
	movq	%r13, %rdx
	movq	(%rsp), %r13
	notq	%rcx
	xorq	%r12, %rdx
	movq	%r9, -16(%rsp)
	orq	%r10, %r11
	movq	%rdx, -8(%rsp)
	movq	56(%rsp), %rax
	movq	%r13, %rdx
	movq	%r11, %rdi
	movq	48(%rsp), %r9
	andq	%r10, %rdx
	movq	%r13, %r11
	movq	64(%rsp), %r12
	xorq	%rax, %rdx
	movq	24(%rsp), %r14
	xorq	%rdi, %r11
	movq	%r9, %rbx
	movq	%r12, %r8
	orq	%rcx, %rbx
	xorq	%rbx, %r10
	movq	%r9, %rbx
	andq	%rax, %rbx
	movq	%r10, (%rsp)
	orq	%r13, %rax
	movq	40(%rsp), %r13
	movq	%rbx, %r10
	movq	8(%rsp), %rbx
	xorq	%rax, %r9
	xorq	%rcx, %r10
	movq	%r13, %rcx
	movq	%r9, 8(%rsp)
	movq	%rbx, %rax
	notq	%rcx
	orq	%r12, %rax
	andq	%rcx, %r8
	xorq	%rcx, %rax
	movq	%rbx, %rcx
	xorq	%rbp, %r8
	andq	%r14, %rcx
	xorq	%rcx, %r12
	movq	%r14, %rcx
	orq	%rbp, %rcx
	andq	%rbp, %r13
	movq	-104(%rsp), %rbp
	movq	%r12, 16(%rsp)
	xorq	%r13, %r14
	movq	-80(%rsp), %r13
	xorq	%rcx, %rbx
	movq	-112(%rsp), %rcx
	movq	%rbx, 24(%rsp)
	xorq	-40(%rsp), %rcx
	xorq	%rdx, %r13
	movq	%r14, 32(%rsp)
	movq	-32(%rsp), %r14
	xorq	%r9, %rcx
	movq	%r13, %rbx
	movq	%r12, %r13
	movq	-88(%rsp), %r12
	xorq	%r8, %rbx
	xorq	%rax, %r14
	xorq	-72(%rsp), %r14
	xorq	%r15, %r13
	xorq	%rsi, %rbx
	xorq	%r11, %r14
	xorq	-56(%rsp), %r13
	xorq	-24(%rsp), %r13
	xorq	%rbp, %rbx
	movq	-96(%rsp), %rbp
	xorq	(%rsp), %r13
	xorq	%rbp, %r14
	movq	-48(%rsp), %rbp
	movq	%r14, %r9
	xorq	%rbp, %r12
	movq	32(%rsp), %rbp
	rolq	%r9
	xorq	%r10, %r12
	xorq	24(%rsp), %r12
	xorq	-16(%rsp), %r12
	xorq	%rbp, %rcx
	movq	%r9, %rbp
	movq	%r13, %r9
	xorq	-8(%rsp), %rcx
	rolq	%r9
	xorq	%rcx, %rbp
	rolq	%rcx
	movq	%r9, %rdi
	movq	%r12, %r9
	xorq	%r13, %rcx
	movq	-80(%rsp), %r13
	rolq	%r9
	xorq	%rbx, %rdi
	xorq	%r14, %r9
	rolq	%rbx
	xorq	%rbp, %rsi
	xorq	%rbp, %rdx
	rolq	$3, %rsi
	xorq	%rbp, %r13
	xorq	%rbp, %r8
	xorq	%rdi, %rax
	movq	%rsi, -80(%rsp)
	movq	%rdx, %rsi
	rorq	$28, %r13
	xorq	%rdi, %r11
	rorq	$23, %rsi
	rolq	$18, %r8
	movq	%r13, 40(%rsp)
	xorq	%r9, %r15
	movq	%rsi, 48(%rsp)
	rolq	$2, %rax
	rorq	$2, %r15
	xorq	%r12, %rbx
	movq	-104(%rsp), %r14
	movq	%r8, 56(%rsp)
	rorq	$19, %r11
	movq	-96(%rsp), %rdx
	movq	-24(%rsp), %r13
	movq	%rax, 80(%rsp)
	movq	(%rsp), %rax
	xorq	%rbp, %r14
	movq	-72(%rsp), %rbp
	movq	%r15, 88(%rsp)
	xorq	%rdi, %rdx
	xorq	%r9, %r13
	movq	-48(%rsp), %r12
	movq	-112(%rsp), %rsi
	rolq	%rdx
	xorq	%r9, %rax
	xorq	%rdi, %rbp
	rorq	$21, %r13
	movq	%rdx, 64(%rsp)
	movq	-32(%rsp), %rdx
	rolq	$15, %rax
	rorq	$20, %rbp
	movq	%rbp, %r15
	movq	-16(%rsp), %r8
	xorq	%rdi, %rdx
	movq	-56(%rsp), %rdi
	movq	%rax, -56(%rsp)
	movq	-88(%rsp), %rax
	rolq	$10, %rdx
	xorq	%r9, %rdi
	xorq	16(%rsp), %r9
	movq	%rdx, 72(%rsp)
	rolq	$6, %rdi
	xorq	%rcx, %rax
	rorq	$3, %r9
	movq	-8(%rsp), %rdx
	rolq	$28, %rax
	orq	%r13, %r15
	xorq	%rcx, %r12
	xorq	%rcx, %r10
	xorq	%r14, %r15
	rorq	$9, %r12
	xorq	%rbx, %rdx
	xorq	%rbx, %rsi
	rorq	$25, %rdx
	movq	%r12, (%rsp)
	movq	%r10, %r12
	movq	-40(%rsp), %r10
	rolq	$21, %r12
	movq	%rdx, -8(%rsp)
	xorq	%rcx, %r8
	rolq	$27, %rsi
	xorq	$32898, %r15
	movq	8(%rsp), %rdx
	xorq	%rbx, %r10
	rolq	$25, %r8
	movq	%r15, -112(%rsp)
	movq	%r13, %r15
	rolq	$20, %r10
	xorq	24(%rsp), %rcx
	notq	%r15
	xorq	%rbx, %rdx
	xorq	32(%rsp), %rbx
	rorq	$8, %rcx
	rolq	$14, %rbx
	orq	%r12, %r15
	rolq	$8, %rdx
	xorq	%rbp, %r15
	movq	%r15, -104(%rsp)
	movq	%r12, %r15
	andq	%rbx, %r15
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	movq	-80(%rsp), %rbp
	xorq	%rbx, %r14
	orq	%rbx, %r13
	movq	%rbp, %rbx
	xorq	%r12, %r13
	movq	%r14, -88(%rsp)
	orq	%r10, %rbx
	movq	%r13, -96(%rsp)
	xorq	%rax, %rbx
	movq	%rbx, -80(%rsp)
	movq	%rbp, %rbx
	andq	%r11, %rbx
	movq	%rbx, %r12
	movq	%r9, %rbx
	notq	%rbx
	xorq	%r10, %r12
	orq	%r11, %rbx
	movq	%r12, -72(%rsp)
	xorq	%rbx, %rbp
	movq	%r9, %rbx
	orq	%rax, %rbx
	andq	%r10, %rax
	xorq	%r11, %rbx
	xorq	%r9, %rax
	movq	%rdx, %r9
	andq	%r8, %rdx
	movq	%rbx, -48(%rsp)
	xorq	%rdi, %rdx
	notq	%r9
	movq	%rax, -40(%rsp)
	movq	64(%rsp), %r11
	movq	%r9, %rax
	movq	%rdi, %r9
	movq	56(%rsp), %r10
	movq	%rdx, -32(%rsp)
	orq	%r8, %r9
	xorq	%r11, %r9
	movq	72(%rsp), %r12
	movq	40(%rsp), %r14
	movq	%r10, %rdx
	movq	(%rsp), %r13
	movq	80(%rsp), %rbx
	andq	%rax, %rdx
	xorq	%r8, %rdx
	movq	%rdx, -24(%rsp)
	movq	%r10, %rdx
	orq	%r11, %rdx
	andq	%rdi, %r11
	xorq	%r11, %r10
	movq	-56(%rsp), %r11
	movq	%rdx, %r8
	movq	%rbp, -56(%rsp)
	xorq	%rax, %r8
	movq	%r11, %rdi
	orq	%r12, %r11
	movq	%r8, -16(%rsp)
	movq	48(%rsp), %r8
	notq	%rdi
	movq	%r11, %rax
	movq	%rcx, %r11
	movq	%rdi, %rdx
	movq	%r14, %rdi
	xorq	%r14, %rax
	orq	%rdx, %r11
	andq	%r12, %rdi
	xorq	%r11, %r12
	movq	%rcx, %r11
	xorq	%rsi, %rdi
	andq	%rsi, %r11
	movq	%r12, (%rsp)
	xorq	%rdx, %r11
	movq	%r14, %rdx
	movq	88(%rsp), %r14
	orq	%rsi, %rdx
	movq	%r11, 8(%rsp)
	movq	-8(%rsp), %rsi
	movq	%rdx, %r11
	movq	%r13, %rdx
	movq	%r10, -8(%rsp)
	xorq	%rcx, %r11
	movq	%r8, %rcx
	notq	%rdx
	orq	%rsi, %rcx
	movq	%r11, 16(%rsp)
	movq	%rsi, %r11
	xorq	%rdx, %rcx
	andq	%rdx, %r11
	movq	%r8, %rdx
	xorq	%r14, %r11
	andq	%rbx, %rdx
	xorq	%rsi, %rdx
	movq	%rbx, %rsi
	orq	%r14, %rsi
	andq	%r13, %r14
	movq	%r15, %r13
	xorq	%rdx, %r13
	xorq	%rsi, %r8
	movq	-96(%rsp), %rsi
	xorq	%r14, %rbx
	xorq	%rbp, %r13
	movq	-24(%rsp), %rbp
	movq	-72(%rsp), %r14
	movq	%rbx, 32(%rsp)
	xorq	-32(%rsp), %r14
	movq	-80(%rsp), %rbx
	movq	%r8, 24(%rsp)
	xorq	%rbp, %r13
	movq	-48(%rsp), %rbp
	xorq	%rax, %r14
	xorq	%r12, %r13
	movq	-16(%rsp), %r12
	xorq	%rcx, %r14
	xorq	-104(%rsp), %r14
	xorq	%rbp, %rsi
	movq	8(%rsp), %rbp
	xorq	%r9, %rbx
	xorq	%rsi, %r12
	movq	-88(%rsp), %rsi
	xorq	-40(%rsp), %rsi
	xorq	%rdi, %rbx
	xorq	%rbp, %r12
	xorq	-112(%rsp), %rbx
	xorq	%r10, %rsi
	xorq	16(%rsp), %rsi
	xorq	%r8, %r12
	movq	%r14, %r8
	xorq	%r11, %rbx
	xorq	32(%rsp), %rsi
	rolq	%r8
	movq	%r12, %r10
	movq	%r8, %rbp
	movq	%r13, %r8
	rolq	%r10
	rolq	%r8
	xorq	%rsi, %rbp
	xorq	%r14, %r10
	movq	-112(%rsp), %r14
	xorq	%rbx, %r8
	rolq	%rsi
	xorq	%rbp, %r9
	xorq	%rbp, %r11
	xorq	%r13, %rsi
	movq	-80(%rsp), %r13
	rolq	$3, %r9
	xorq	%rbp, %r14
	movq	%r9, 48(%rsp)
	movq	-72(%rsp), %r9
	rolq	%rbx
	xorq	%rbp, %rdi
	xorq	%rbp, %r13
	rolq	$18, %r11
	xorq	%r12, %rbx
	movq	(%rsp), %r12
	rorq	$28, %r13
	xorq	%r8, %r9
	movq	%r11, 64(%rsp)
	xorq	%r8, %rcx
	movq	%r13, 40(%rsp)
	movq	-32(%rsp), %r13
	movq	%r9, %rbp
	xorq	%r10, %r12
	movq	-104(%rsp), %r11
	rolq	$2, %rcx
	xorq	%r8, %rax
	rorq	$20, %rbp
	movq	-24(%rsp), %r9
	rorq	$19, %rax
	xorq	%r8, %r13
	rorq	$23, %rdi
	xorq	%r8, %r11
	rolq	$10, %r13
	movq	-56(%rsp), %r8
	movq	%rcx, 88(%rsp)
	xorq	%r10, %r9
	movq	%r13, 80(%rsp)
	movq	%r15, %rcx
	movq	-88(%rsp), %r15
	movq	%r9, %r13
	movq	%r12, %r9
	movq	-48(%rsp), %r12
	xorq	%r10, %rcx
	rorq	$21, %r13
	xorq	%r10, %r8
	xorq	%rdx, %r10
	rolq	%r11
	rorq	$2, %rcx
	rolq	$6, %r8
	movq	%rdi, 56(%rsp)
	movq	-96(%rsp), %rdx
	rolq	$15, %r9
	rorq	$3, %r10
	xorq	%rsi, %r12
	xorq	%rbx, %r15
	movq	%rcx, 96(%rsp)
	movq	%r15, %rdi
	movq	%r12, %rcx
	movq	-40(%rsp), %r15
	rorq	$9, %rcx
	movq	%r11, 72(%rsp)
	xorq	%rsi, %rdx
	rolq	$27, %rdi
	xorq	%rbx, %r15
	movq	8(%rsp), %r12
	movq	%r9, (%rsp)
	rolq	$28, %rdx
	movq	%rcx, -112(%rsp)
	movq	-8(%rsp), %rcx
	movq	%r15, %r11
	movq	16(%rsp), %r15
	movq	%r8, -56(%rsp)
	xorq	%rsi, %r12
	rolq	$20, %r11
	xorq	%rbx, %rcx
	rolq	$21, %r12
	movq	-16(%rsp), %r9
	movabsq	$-9223372036854742902, %r8
	xorq	%rbx, %r15
	rorq	$25, %rcx
	xorq	32(%rsp), %rbx
	movq	%rcx, -8(%rsp)
	movq	%r15, %rcx
	movq	%rbp, %r15
	rolq	$14, %rbx
	orq	%r13, %r15
	xorq	%rsi, %r9
	xorq	24(%rsp), %rsi
	rolq	$8, %rcx
	rolq	$25, %r9
	xorq	%r14, %r15
	rorq	$8, %rsi
	xorq	%r15, %r8
	movq	%r13, %r15
	notq	%r15
	movq	%r8, -104(%rsp)
	movq	%r14, %r8
	andq	%rbp, %r14
	orq	%r12, %r15
	orq	%rbx, %r8
	xorq	%rbx, %r14
	xorq	%rbp, %r15
	movq	48(%rsp), %rbp
	movq	%r14, -80(%rsp)
	movq	%r15, -96(%rsp)
	movq	%r12, %r15
	movq	40(%rsp), %r14
	andq	%rbx, %r15
	movq	%rbp, %rbx
	xorq	%r13, %r15
	movq	%r8, %r13
	movq	%r10, %r8
	xorq	%r12, %r13
	orq	%r11, %rbx
	notq	%r8
	xorq	%rdx, %rbx
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r8, %rbx
	movq	%r10, %r8
	orq	%rdx, %r8
	andq	%r11, %rdx
	orq	%rax, %rbx
	xorq	%r10, %rdx
	xorq	%rbx, %rbp
	movq	72(%rsp), %rbx
	xorq	%rax, %r8
	movq	%rdx, -40(%rsp)
	movq	-56(%rsp), %rdx
	movq	%rcx, %rax
	andq	%r9, %rcx
	movq	%rbx, %r11
	movq	64(%rsp), %r10
	notq	%rax
	movq	%r8, -48(%rsp)
	orq	%r9, %rdx
	movq	%r14, %r8
	xorq	%rdx, %r11
	movq	%rcx, %rdx
	movq	-56(%rsp), %rcx
	movq	%rbp, -56(%rsp)
	xorq	%rcx, %rdx
	movq	%rdx, -32(%rsp)
	movq	%r10, %rdx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rsi, %r9
	movq	%rdx, -24(%rsp)
	movq	%r10, %rdx
	orq	%rbx, %rdx
	movq	%rdx, %r12
	xorq	%rax, %r12
	movq	%rbx, %rax
	movq	88(%rsp), %rbx
	andq	%rcx, %rax
	movq	%r12, -16(%rsp)
	movq	80(%rsp), %r12
	xorq	%rax, %r10
	movq	(%rsp), %rax
	andq	%r12, %r8
	movq	%rax, %rdx
	orq	%r12, %rax
	xorq	%rdi, %r8
	notq	%rdx
	xorq	%r14, %rax
	orq	%rdx, %r9
	xorq	%r9, %r12
	movq	%rsi, %r9
	andq	%rdi, %r9
	xorq	%rdx, %r9
	movq	%r14, %rdx
	movq	96(%rsp), %r14
	orq	%rdi, %rdx
	movq	%r9, 8(%rsp)
	movq	56(%rsp), %rdi
	movq	%rdx, %r9
	movq	-112(%rsp), %rdx
	xorq	%rsi, %r9
	movq	-8(%rsp), %rsi
	movq	%rdi, %rcx
	notq	%rdx
	movq	%r9, 16(%rsp)
	movq	%rsi, %r9
	andq	%rdx, %r9
	xorq	%r14, %r9
	orq	%rsi, %rcx
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rsi, %rdx
	movq	%rbx, %rsi
	orq	%r14, %rsi
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	movq	-72(%rsp), %r14
	xorq	-32(%rsp), %r14
	xorq	%rsi, %rdi
	movq	%rbx, 32(%rsp)
	movq	%r13, %rbx
	movq	%r15, %r13
	xorq	%rax, %r14
	xorq	%r11, %rbx
	xorq	%rdx, %r13
	xorq	%rcx, %r14
	xorq	-96(%rsp), %r14
	xorq	%r8, %rbx
	xorq	%rbp, %r13
	xorq	-104(%rsp), %rbx
	movq	-24(%rsp), %rbp
	movq	-88(%rsp), %rsi
	movq	%r12, (%rsp)
	xorq	%r9, %rbx
	xorq	%rbp, %r13
	movq	-48(%rsp), %rbp
	movq	%rdi, 24(%rsp)
	xorq	%r12, %r13
	movq	-16(%rsp), %r12
	movq	%r10, -8(%rsp)
	xorq	%rbp, %rsi
	movq	8(%rsp), %rbp
	xorq	%rsi, %r12
	movq	-80(%rsp), %rsi
	xorq	%rbp, %r12
	movq	-40(%rsp), %rbp
	xorq	%rdi, %r12
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	rolq	%rdi
	xorq	%r10, %rsi
	movq	%rdi, %rbp
	xorq	16(%rsp), %rsi
	movq	%r13, %rdi
	xorq	32(%rsp), %rsi
	rolq	%rdi
	movq	%r12, %r10
	xorq	%rsi, %rbp
	xorq	%rbx, %rdi
	rolq	%r10
	xorq	%rbp, %r8
	xorq	%rbp, %r11
	rolq	%rsi
	xorq	%rbp, %r9
	rorq	$23, %r8
	xorq	%r13, %rsi
	rolq	$3, %r11
	movq	-112(%rsp), %r13
	movq	%r8, 56(%rsp)
	movq	-96(%rsp), %r8
	xorq	%r14, %r10
	rolq	%rbx
	rolq	$18, %r9
	movq	%r11, 48(%rsp)
	xorq	%rbp, %r13
	xorq	%r12, %rbx
	xorq	%rdi, %r8
	movq	%r9, 64(%rsp)
	movq	-72(%rsp), %r9
	xorq	%rdi, %rcx
	movq	%r8, %r11
	movq	-32(%rsp), %r8
	rorq	$28, %r13
	movq	(%rsp), %r12
	movq	-104(%rsp), %r14
	xorq	%rdi, %r9
	movq	%r13, 40(%rsp)
	rolq	%r11
	xorq	%rdi, %r8
	xorq	%r10, %r12
	xorq	%rdi, %rax
	movq	%r11, 72(%rsp)
	movq	%r8, %r13
	movq	%r15, %r8
	xorq	%rbp, %r14
	movq	%r9, %rbp
	xorq	%r10, %r8
	movq	-24(%rsp), %r9
	rolq	$10, %r13
	movq	%rcx, %r11
	movq	%r13, 80(%rsp)
	rorq	$20, %rbp
	movq	%r8, %r15
	rorq	$19, %rax
	movq	-56(%rsp), %r8
	rolq	$2, %r11
	xorq	%r10, %r9
	rorq	$2, %r15
	movq	%r9, %r13
	movq	%r12, %r9
	movq	-48(%rsp), %rcx
	movq	%r11, 88(%rsp)
	xorq	%r10, %r8
	rorq	$21, %r13
	movq	%r15, 96(%rsp)
	rolq	$6, %r8
	rolq	$15, %r9
	xorq	%rdx, %r10
	movq	-88(%rsp), %rdx
	xorq	%rsi, %rcx
	movq	%r9, -56(%rsp)
	rorq	$3, %r10
	xorq	%rsi, %rdx
	rorq	$9, %rcx
	rolq	$28, %rdx
	movq	%rdx, -72(%rsp)
	movq	%rbp, %rdx
	movq	%rcx, -112(%rsp)
	movq	-40(%rsp), %r15
	orq	%r13, %rdx
	movq	-8(%rsp), %rcx
	movq	8(%rsp), %r12
	xorq	%rbx, %r15
	movq	-80(%rsp), %rdi
	movq	-16(%rsp), %r9
	movq	%r15, %r11
	movq	16(%rsp), %r15
	xorq	%rbx, %rcx
	xorq	%rsi, %r12
	rorq	$25, %rcx
	rolq	$21, %r12
	xorq	%rbx, %rdi
	xorq	%rsi, %r9
	movq	%rcx, -8(%rsp)
	rolq	$25, %r9
	xorq	%rbx, %r15
	rolq	$27, %rdi
	movq	%r15, %rcx
	movq	%rdx, %r15
	xorq	32(%rsp), %rbx
	rolq	$20, %r11
	rolq	$14, %rbx
	xorq	%r14, %r15
	xorq	24(%rsp), %rsi
	rolq	$8, %rcx
	movabsq	$-9223372034707259392, %rdx
	rorq	$8, %rsi
	xorq	%r15, %rdx
	movq	%r13, %r15
	notq	%r15
	movq	%rdx, -104(%rsp)
	movq	%r12, %rdx
	orq	%r12, %r15
	andq	%rbx, %rdx
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rdx, %r15
	movq	%r14, %rdx
	orq	%rbx, %rdx
	xorq	%r13, %r15
	movq	%rdx, %r13
	xorq	%r12, %r13
	andq	%rbp, %r14
	movq	48(%rsp), %rbp
	movq	%r14, %rdx
	movq	%r13, -88(%rsp)
	movq	40(%rsp), %r14
	xorq	%rbx, %rdx
	movq	%rbp, %rbx
	movq	%rdx, -80(%rsp)
	movq	-72(%rsp), %rdx
	orq	%r11, %rbx
	xorq	%rdx, %rbx
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r10, %rbx
	notq	%rbx
	orq	%rax, %rbx
	xorq	%rbx, %rbp
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	72(%rsp), %r11
	xorq	%rax, %rbx
	xorq	%r10, %rdx
	movq	%rcx, %rax
	movq	%r8, %r10
	andq	%r9, %rcx
	orq	%r9, %r10
	movq	%rdx, -40(%rsp)
	notq	%rax
	movq	%rcx, %r12
	movq	64(%rsp), %rcx
	movq	%r10, %rdx
	movq	%r11, %r10
	xorq	%rdx, %r10
	xorq	%r8, %r12
	movq	%rbx, -48(%rsp)
	movq	%rcx, %rdx
	movq	%r12, -32(%rsp)
	movq	80(%rsp), %r12
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%r11, %r9
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	movq	%rdx, %r11
	xorq	%rax, %r11
	movq	%r9, %rax
	movq	%r14, %r9
	andq	%r8, %rax
	movq	%r11, -16(%rsp)
	movq	%rsi, %r11
	andq	%r12, %r9
	xorq	%rax, %rcx
	movq	-56(%rsp), %rax
	xorq	%rdi, %r9
	movq	%rcx, %r8
	movq	-8(%rsp), %rcx
	movq	%rax, %rdx
	orq	%r12, %rax
	notq	%rdx
	xorq	%r14, %rax
	orq	%rdx, %r11
	xorq	%r11, %r12
	movq	%rsi, %r11
	andq	%rdi, %r11
	xorq	%rdx, %r11
	movq	%r14, %rdx
	movq	96(%rsp), %r14
	orq	%rdi, %rdx
	movq	%r11, 8(%rsp)
	movq	%rdx, %rdi
	xorq	%rsi, %rdi
	movq	-112(%rsp), %rsi
	movq	%rdi, 16(%rsp)
	movq	56(%rsp), %rdi
	notq	%rsi
	movq	88(%rsp), %rbx
	movq	%rbp, -56(%rsp)
	movq	%rsi, %rdx
	movq	%rcx, %rsi
	movq	%r12, (%rsp)
	andq	%rdx, %rsi
	movq	%r8, -8(%rsp)
	movq	%rsi, %r11
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%rcx, %rdi
	movq	-96(%rsp), %r14
	xorq	-72(%rsp), %r14
	movq	%rbx, %rcx
	movq	%r13, %rbx
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	xorq	-32(%rsp), %r14
	movq	%rdi, 24(%rsp)
	xorq	%r9, %rbx
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%rax, %r14
	xorq	%r15, %r13
	xorq	%rsi, %r14
	xorq	%r10, %rbx
	movq	%rcx, 32(%rsp)
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%r11, %rbx
	xorq	%rdx, %r13
	xorq	-104(%rsp), %rbx
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rbp, %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	16(%rsp), %rdi
	rolq	%r8
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%r8
	xorq	%rbp, %r9
	rolq	%rdi
	xorq	%rbx, %r8
	xorq	%rbp, %r10
	rorq	$23, %r9
	xorq	%r13, %rdi
	movq	-112(%rsp), %r13
	rolq	%rcx
	movq	%r9, 56(%rsp)
	movq	-96(%rsp), %r9
	xorq	%r14, %rcx
	xorq	%r8, %rsi
	xorq	%rbp, %r13
	xorq	%rcx, %r15
	rolq	$2, %rsi
	xorq	%rbp, %r11
	xorq	%r8, %r9
	rorq	$28, %r13
	movq	%rsi, 88(%rsp)
	movq	%r15, %rsi
	rolq	%r9
	movq	%r13, 40(%rsp)
	movq	-72(%rsp), %r13
	rolq	%rbx
	movq	%r9, 72(%rsp)
	movq	-32(%rsp), %r9
	xorq	%r12, %rbx
	xorq	%r8, %rax
	movq	-104(%rsp), %r14
	rolq	$3, %r10
	xorq	%r8, %r13
	rolq	$18, %r11
	rorq	$2, %rsi
	xorq	%r8, %r9
	movq	%r10, 48(%rsp)
	rorq	$19, %rax
	rolq	$10, %r9
	xorq	%rbp, %r14
	movq	%r11, 64(%rsp)
	movq	%r13, %rbp
	movq	%r9, 80(%rsp)
	rorq	$20, %rbp
	movq	%rsi, 96(%rsp)
	movq	-56(%rsp), %r9
	movq	-24(%rsp), %r13
	movq	-8(%rsp), %rsi
	xorq	%rcx, %r9
	movq	(%rsp), %r12
	movq	-88(%rsp), %r10
	xorq	%rcx, %r13
	rolq	$6, %r9
	movq	-80(%rsp), %r8
	movq	-40(%rsp), %r11
	rorq	$21, %r13
	xorq	%rbx, %rsi
	xorq	%rcx, %r12
	xorq	%rdi, %r10
	movq	%rsi, %r15
	rolq	$15, %r12
	xorq	%rcx, %rdx
	movq	%r10, %rcx
	rorq	$25, %r15
	movq	%r12, (%rsp)
	movq	8(%rsp), %r12
	xorq	%rbx, %r8
	movq	%r15, -8(%rsp)
	movq	%rbp, %r15
	movq	-48(%rsp), %r10
	xorq	%rbx, %r11
	orq	%r13, %r15
	xorq	%rdi, %r12
	movq	16(%rsp), %rsi
	rorq	$3, %rdx
	rolq	$21, %r12
	xorq	%r14, %r15
	xorq	%rdi, %r10
	rolq	$27, %r8
	xorq	$32907, %r15
	rorq	$9, %r10
	xorq	%rbx, %rsi
	xorq	32(%rsp), %rbx
	movq	%r15, -104(%rsp)
	rolq	$14, %rbx
	movq	%r13, %r15
	rolq	$20, %r11
	movq	%r10, -112(%rsp)
	rolq	$28, %rcx
	notq	%r15
	rolq	$8, %rsi
	orq	%r12, %r15
	movq	-16(%rsp), %r10
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%r12, %r15
	xorq	%rdi, %r10
	xorq	24(%rsp), %rdi
	rolq	$25, %r10
	andq	%rbx, %r15
	rorq	$8, %rdi
	xorq	%r13, %r15
	movq	%r14, %r13
	orq	%rbx, %r13
	andq	%rbp, %r14
	movq	48(%rsp), %rbp
	xorq	%rbx, %r14
	xorq	%r12, %r13
	movq	%rdx, %r12
	movq	%rbp, %rbx
	notq	%r12
	movq	%r14, -80(%rsp)
	movq	40(%rsp), %r14
	orq	%r11, %rbx
	movq	%r13, -88(%rsp)
	xorq	%rcx, %rbx
	movq	%rbx, -72(%rsp)
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -56(%rsp)
	movq	%r12, %rbx
	movq	%rdx, %r12
	orq	%rcx, %r12
	andq	%r11, %rcx
	orq	%rax, %rbx
	xorq	%rax, %r12
	movq	%rcx, %rax
	movq	72(%rsp), %rcx
	xorq	%rbx, %rbp
	xorq	%rdx, %rax
	movq	%r9, %rdx
	movq	%r12, -48(%rsp)
	orq	%r10, %rdx
	movq	%rax, -40(%rsp)
	movq	%rcx, %r11
	movq	%rsi, %rax
	andq	%r10, %rsi
	xorq	%rdx, %r11
	notq	%rax
	movq	%rsi, %rdx
	movq	64(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rsi, %r10
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%rcx, %r10
	movq	%rdi, %rcx
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	movq	80(%rsp), %r12
	movq	-8(%rsp), %r13
	movq	%r10, -8(%rsp)
	notq	%rdx
	movq	88(%rsp), %rbx
	andq	%r12, %rax
	orq	%rdx, %rcx
	movq	%rax, %r9
	movq	(%rsp), %rax
	movq	%rbx, %rsi
	xorq	%r8, %r9
	orq	%r12, %rax
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	andq	%r8, %rcx
	xorq	%r14, %rax
	movq	%r12, (%rsp)
	xorq	%rdx, %rcx
	movq	%r14, %rdx
	movq	96(%rsp), %r14
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %r8
	movq	-112(%rsp), %rdx
	orq	%r14, %rsi
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	movq	%r8, 16(%rsp)
	notq	%rdx
	movq	%r13, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%r13, %rcx
	xorq	%r14, %r8
	andq	-112(%rsp), %r14
	movq	%rbp, -112(%rsp)
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	xorq	%rsi, %rdi
	movq	-88(%rsp), %rsi
	andq	%rbx, %rdx
	xorq	%r14, %rbx
	movq	-56(%rsp), %r14
	xorq	-32(%rsp), %r14
	xorq	%r13, %rdx
	movq	%r15, %r13
	movq	%rbx, 32(%rsp)
	xorq	%rax, %r14
	xorq	%rdx, %r13
	movq	-72(%rsp), %rbx
	xorq	%rcx, %r14
	xorq	-96(%rsp), %r14
	xorq	%rbp, %r13
	movq	-48(%rsp), %rbp
	xorq	-24(%rsp), %r13
	movq	%rdi, 24(%rsp)
	xorq	%r12, %r13
	xorq	%r11, %rbx
	xorq	%rbp, %rsi
	movq	-16(%rsp), %rbp
	xorq	%r9, %rbx
	xorq	-104(%rsp), %rbx
	movq	%rsi, %r12
	movq	-80(%rsp), %rsi
	xorq	%r8, %rbx
	xorq	%rbp, %r12
	movq	-40(%rsp), %rbp
	xorq	8(%rsp), %r12
	xorq	%rdi, %r12
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	xorq	%r10, %rsi
	xorq	16(%rsp), %rsi
	xorq	32(%rsp), %rsi
	rolq	%rdi
	movq	%rdi, %rbp
	movq	%r13, %rdi
	movq	%r12, %r10
	rolq	%rdi
	xorq	%rsi, %rbp
	rolq	%rsi
	xorq	%r13, %rsi
	movq	-72(%rsp), %r13
	xorq	%rbp, %r11
	xorq	%rbx, %rdi
	rolq	$3, %r11
	xorq	%rbp, %r9
	rolq	%r10
	xorq	%rbp, %r8
	xorq	%rbp, %r13
	xorq	%r14, %r10
	rorq	$23, %r9
	xorq	%rdi, %rax
	rorq	$28, %r13
	movq	-104(%rsp), %r14
	rolq	$18, %r8
	xorq	%rdi, %rcx
	movq	%r13, 40(%rsp)
	rorq	$19, %rax
	rolq	%rbx
	movq	%r11, -72(%rsp)
	movq	-96(%rsp), %r11
	xorq	%r12, %rbx
	xorq	%rbp, %r14
	movq	-32(%rsp), %r13
	movq	(%rsp), %r12
	movq	%r9, 48(%rsp)
	movq	-56(%rsp), %r9
	movq	%rax, -32(%rsp)
	xorq	%rdi, %r11
	movq	%r15, %rax
	movq	%r8, 56(%rsp)
	movq	-112(%rsp), %r8
	xorq	%r10, %rax
	rolq	%r11
	xorq	%rdi, %r9
	xorq	%rdi, %r13
	movq	%r11, 64(%rsp)
	movq	%rax, %r15
	movq	%r9, %rbp
	movq	%rcx, %r11
	xorq	%r10, %r8
	rolq	$10, %r13
	rorq	$20, %rbp
	rolq	$2, %r11
	movq	%r13, -56(%rsp)
	movq	-24(%rsp), %r13
	rorq	$2, %r15
	rolq	$6, %r8
	xorq	%r10, %r12
	movq	%r11, 72(%rsp)
	movq	%r15, 80(%rsp)
	movq	%r12, %rcx
	movq	-40(%rsp), %r15
	xorq	%r10, %r13
	rolq	$15, %rcx
	rorq	$21, %r13
	movq	-48(%rsp), %r9
	movq	%rbp, %rax
	xorq	%rbx, %r15
	movq	%rcx, (%rsp)
	movq	-8(%rsp), %rcx
	orq	%r13, %rax
	movq	%r15, %r11
	movq	16(%rsp), %r15
	xorq	%rsi, %r9
	movq	8(%rsp), %r12
	xorq	%rbx, %rcx
	movq	-80(%rsp), %rdi
	rorq	$9, %r9
	xorq	%rdx, %r10
	xorq	%rbx, %r15
	rorq	$25, %rcx
	movq	-88(%rsp), %rdx
	xorq	%rsi, %r12
	movq	%rcx, -8(%rsp)
	movq	%r15, %rcx
	movq	%rax, %r15
	movl	$2147483649, %eax
	xorq	%r14, %r15
	movq	%r9, -112(%rsp)
	movq	-16(%rsp), %r9
	xorq	%rbx, %rdi
	xorq	%r15, %rax
	movq	%r13, %r15
	rolq	$21, %r12
	xorq	32(%rsp), %rbx
	notq	%r15
	rolq	$14, %rbx
	xorq	%rsi, %rdx
	xorq	%rsi, %r9
	movq	%rax, -104(%rsp)
	xorq	24(%rsp), %rsi
	orq	%r12, %r15
	movq	%r12, %rax
	rorq	$3, %r10
	rolq	$25, %r9
	xorq	%rbp, %r15
	rorq	$8, %rsi
	rolq	$27, %rdi
	movq	%r15, -96(%rsp)
	rolq	$20, %r11
	rolq	$28, %rdx
	rolq	$8, %rcx
	andq	%rbx, %rax
	movq	%rax, %r15
	movq	%r14, %rax
	andq	%rbp, %r14
	movq	-72(%rsp), %rbp
	orq	%rbx, %rax
	xorq	%r13, %r15
	movq	%rax, %r13
	movq	%r14, %rax
	xorq	%rbx, %rax
	movq	%rbp, %rbx
	xorq	%r12, %r13
	orq	%r11, %rbx
	movq	%rax, -80(%rsp)
	movq	-32(%rsp), %rax
	xorq	%rdx, %rbx
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r10, %rbx
	movq	40(%rsp), %r14
	notq	%rbx
	movq	-56(%rsp), %r12
	orq	%rax, %rbx
	xorq	%rbx, %rbp
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	64(%rsp), %r11
	movq	%rbp, -56(%rsp)
	xorq	%r10, %rdx
	movq	%rcx, %r10
	xorq	%rax, %rbx
	andq	%r9, %rcx
	movq	%rdx, -40(%rsp)
	notq	%r10
	movq	%r8, %rdx
	movq	%r10, %rax
	orq	%r9, %rdx
	movq	%r11, %r10
	movq	%rbx, -48(%rsp)
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	movq	56(%rsp), %rcx
	movq	72(%rsp), %rbx
	xorq	%r8, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rcx, %rdx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	xorq	%rax, %rdx
	movq	%r11, %rax
	movq	%rsi, %r11
	andq	%r8, %rax
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	xorq	%rax, %rcx
	movq	%r14, %rax
	andq	%r12, %rax
	notq	%rdx
	movq	%rcx, %r8
	movq	-8(%rsp), %rcx
	movq	%rax, %r9
	movq	(%rsp), %rax
	orq	%rdx, %r11
	xorq	%rdi, %r9
	orq	%r12, %rax
	xorq	%r11, %r12
	movq	%rsi, %r11
	xorq	%r14, %rax
	andq	%rdi, %r11
	movq	%r12, (%rsp)
	xorq	%rdx, %r11
	movq	%r14, %rdx
	movq	80(%rsp), %r14
	orq	%rdi, %rdx
	movq	%r11, 8(%rsp)
	movq	48(%rsp), %rdi
	movq	%rdx, %r11
	xorq	%rsi, %r11
	movq	-112(%rsp), %rsi
	movq	%r11, 16(%rsp)
	notq	%rsi
	movq	%rsi, %rdx
	movq	%rcx, %rsi
	andq	%rdx, %rsi
	movq	%rsi, %r11
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%rcx, %rdi
	movq	-96(%rsp), %r14
	xorq	-72(%rsp), %r14
	movq	%rbx, %rcx
	movq	%r13, %rbx
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	xorq	%r9, %rbx
	xorq	-32(%rsp), %r14
	movq	%rdi, 24(%rsp)
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%r10, %rbx
	xorq	%r15, %r13
	xorq	%r11, %rbx
	xorq	-104(%rsp), %rbx
	xorq	%rax, %r14
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%rsi, %r14
	xorq	%rdx, %r13
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rbp, %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	movq	%r8, -8(%rsp)
	movq	%rcx, 32(%rsp)
	xorq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	16(%rsp), %rdi
	rolq	%rcx
	rolq	%r8
	xorq	%r14, %rcx
	movq	-104(%rsp), %r14
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%r8
	xorq	%rbp, %r9
	rolq	%rdi
	xorq	%rbx, %r8
	xorq	%rbp, %r10
	rorq	$23, %r9
	xorq	%r13, %rdi
	movq	-112(%rsp), %r13
	xorq	%r8, %rax
	movq	%r9, 56(%rsp)
	movq	-96(%rsp), %r9
	xorq	%r8, %rsi
	rolq	%rbx
	xorq	%rbp, %r13
	rorq	$19, %rax
	xorq	%r12, %rbx
	xorq	%rbp, %r14
	xorq	%r8, %r9
	rorq	$28, %r13
	movq	(%rsp), %r12
	xorq	%rbp, %r11
	rolq	%r9
	movq	%r13, 40(%rsp)
	movq	-72(%rsp), %r13
	rolq	$3, %r10
	movq	%r9, 72(%rsp)
	movq	-32(%rsp), %r9
	rolq	$2, %rsi
	rolq	$18, %r11
	movq	%rax, -32(%rsp)
	movq	%r15, %rax
	xorq	%r8, %r13
	xorq	%r8, %r9
	xorq	%rcx, %rax
	movq	%r10, 48(%rsp)
	movq	-88(%rsp), %r10
	rolq	$10, %r9
	movq	%rsi, 88(%rsp)
	movq	%r13, %rbp
	movq	%rax, %rsi
	movq	%r9, 80(%rsp)
	movq	-24(%rsp), %r13
	rorq	$20, %rbp
	rorq	$2, %rsi
	movq	-56(%rsp), %r9
	xorq	%rdi, %r10
	xorq	%rcx, %r12
	xorq	%rcx, %rdx
	xorq	%rcx, %r13
	movq	%rsi, 96(%rsp)
	movq	-8(%rsp), %rsi
	movq	%rbp, %rax
	rolq	$15, %r12
	xorq	%rcx, %r9
	movq	%r10, %rcx
	movq	-48(%rsp), %r10
	xorq	%rbx, %rsi
	rorq	$21, %r13
	movq	%r12, (%rsp)
	movq	8(%rsp), %r12
	xorq	%rdi, %r10
	movq	%rsi, %r15
	orq	%r13, %rax
	movq	%r11, 64(%rsp)
	rorq	$9, %r10
	rorq	$25, %r15
	xorq	%rdi, %r12
	movq	-80(%rsp), %r8
	movq	%r10, -112(%rsp)
	movq	-16(%rsp), %r10
	rolq	$21, %r12
	rolq	$6, %r9
	movq	-40(%rsp), %r11
	rorq	$3, %rdx
	xorq	%rbx, %r8
	rolq	$28, %rcx
	xorq	%rdi, %r10
	xorq	24(%rsp), %rdi
	movq	%r15, -8(%rsp)
	movq	%rax, %r15
	xorq	%r14, %r15
	movq	16(%rsp), %rsi
	xorq	%rbx, %r11
	rolq	$25, %r10
	movabsq	$-9223372034707259263, %rax
	rorq	$8, %rdi
	rolq	$27, %r8
	xorq	%r15, %rax
	movq	%r13, %r15
	xorq	%rbx, %rsi
	rolq	$20, %r11
	xorq	32(%rsp), %rbx
	notq	%r15
	rolq	$8, %rsi
	rolq	$14, %rbx
	movq	%rax, -104(%rsp)
	orq	%r12, %r15
	movq	%r12, %rax
	xorq	%rbp, %r15
	andq	%rbx, %rax
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	movq	%r14, %rax
	andq	%rbp, %r14
	movq	48(%rsp), %rbp
	orq	%rbx, %rax
	xorq	%rbx, %r14
	xorq	%r13, %r15
	movq	%r14, -80(%rsp)
	movq	-32(%rsp), %r14
	movq	%rax, %r13
	movq	%rdx, %rax
	movq	%rbp, %rbx
	notq	%rax
	xorq	%r12, %r13
	movq	80(%rsp), %r12
	orq	%r11, %rbx
	movq	%r13, -88(%rsp)
	movq	-8(%rsp), %r13
	xorq	%rcx, %rbx
	movq	%rbx, -72(%rsp)
	movq	%rbp, %rbx
	andq	%r14, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -56(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rax
	orq	%rcx, %rax
	andq	%r11, %rcx
	orq	%r14, %rbx
	xorq	%rdx, %rcx
	movq	%rsi, %rdx
	xorq	%r14, %rax
	andq	%r10, %rsi
	movq	%rcx, -40(%rsp)
	notq	%rdx
	movq	72(%rsp), %rcx
	xorq	%rbx, %rbp
	movq	40(%rsp), %r14
	movq	88(%rsp), %rbx
	movq	%rax, -48(%rsp)
	movq	%rdx, %rax
	movq	%r9, %rdx
	movq	%rcx, %r11
	orq	%r10, %rdx
	xorq	%rdx, %r11
	movq	%rsi, %rdx
	movq	64(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rsi, %r10
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	movq	%rbx, %rsi
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%rcx, %r10
	movq	%rdi, %rcx
	andq	%r12, %rax
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	movq	%rax, %r9
	movq	(%rsp), %rax
	notq	%rdx
	xorq	%r8, %r9
	orq	%r12, %rax
	xorq	%r14, %rax
	orq	%rdx, %rcx
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	andq	%r8, %rcx
	xorq	%rdx, %rcx
	movq	%r14, %rdx
	movq	96(%rsp), %r14
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %r8
	movq	-112(%rsp), %rdx
	orq	%r14, %rsi
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	notq	%rdx
	movq	%r8, 16(%rsp)
	movq	%r13, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%r13, %rcx
	xorq	%r14, %r8
	andq	-112(%rsp), %r14
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	xorq	%rsi, %rdi
	andq	%rbx, %rdx
	xorq	%r14, %rbx
	movq	%rbx, 32(%rsp)
	movq	-72(%rsp), %rbx
	xorq	%r13, %rdx
	movq	%r15, %r13
	xorq	%rdx, %r13
	xorq	%r11, %rbx
	xorq	%rbp, %r13
	xorq	%r9, %rbx
	xorq	-104(%rsp), %rbx
	movq	-56(%rsp), %r14
	movq	%rbp, -112(%rsp)
	movq	-88(%rsp), %rsi
	movq	-48(%rsp), %rbp
	movq	%r12, (%rsp)
	xorq	%r8, %rbx
	xorq	-32(%rsp), %r14
	xorq	-24(%rsp), %r13
	movq	%rdi, 24(%rsp)
	xorq	%rbp, %rsi
	movq	-16(%rsp), %rbp
	xorq	%r12, %r13
	xorq	%rax, %r14
	movq	%rsi, %r12
	xorq	%rcx, %r14
	movq	-80(%rsp), %rsi
	xorq	-96(%rsp), %r14
	xorq	%rbp, %r12
	movq	-40(%rsp), %rbp
	xorq	8(%rsp), %r12
	movq	%r10, -8(%rsp)
	xorq	%rdi, %r12
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	rolq	%rdi
	xorq	%r10, %rsi
	movq	%rdi, %rbp
	xorq	16(%rsp), %rsi
	xorq	32(%rsp), %rsi
	xorq	%rsi, %rbp
	rolq	%rsi
	movq	%r13, %rdi
	movq	%r12, %r10
	xorq	%r13, %rsi
	xorq	%rbp, %r11
	movq	-72(%rsp), %r13
	xorq	%rbp, %r9
	rolq	$3, %r11
	rorq	$23, %r9
	xorq	%rbp, %r8
	movq	%r11, -72(%rsp)
	xorq	%rbp, %r13
	movq	-96(%rsp), %r11
	rolq	%rdi
	rorq	$28, %r13
	xorq	%rbx, %rdi
	movq	%r9, 48(%rsp)
	rolq	%r10
	movq	-56(%rsp), %r9
	xorq	%r14, %r10
	xorq	%rdi, %r11
	xorq	%rdi, %rax
	movq	%r13, 40(%rsp)
	movq	-104(%rsp), %r14
	xorq	%rdi, %rcx
	rolq	%r11
	movq	-32(%rsp), %r13
	xorq	%rdi, %r9
	movq	%r11, 64(%rsp)
	rolq	%rbx
	rorq	$19, %rax
	xorq	%rbp, %r14
	movq	%rcx, %r11
	movq	%r9, %rbp
	xorq	%rdi, %r13
	movq	%rax, -32(%rsp)
	movq	%r15, %rax
	xorq	%r12, %rbx
	rorq	$20, %rbp
	rolq	$18, %r8
	rolq	$10, %r13
	rolq	$2, %r11
	xorq	%r10, %rax
	movq	%r8, 56(%rsp)
	movq	%rax, %r15
	movq	%r13, -56(%rsp)
	movq	-112(%rsp), %r8
	movq	%rbp, %rax
	rorq	$2, %r15
	movq	%r11, 72(%rsp)
	movq	-24(%rsp), %r13
	movq	%r15, 80(%rsp)
	movq	(%rsp), %r12
	xorq	%r10, %r8
	movq	-48(%rsp), %r9
	movq	-40(%rsp), %r15
	xorq	%r10, %r13
	rolq	$6, %r8
	xorq	%r10, %r12
	rorq	$21, %r13
	movq	-80(%rsp), %rdi
	xorq	%rdx, %r10
	movq	%r12, %rcx
	xorq	%rbx, %r15
	xorq	%rsi, %r9
	movq	-88(%rsp), %rdx
	rolq	$15, %rcx
	rorq	$9, %r9
	movq	%r15, %r11
	movq	16(%rsp), %r15
	movq	%rcx, (%rsp)
	movq	-8(%rsp), %rcx
	orq	%r13, %rax
	xorq	%rsi, %rdx
	movq	%r9, -112(%rsp)
	movq	8(%rsp), %r12
	xorq	%rbx, %r15
	xorq	%rbx, %rdi
	movq	-16(%rsp), %r9
	rorq	$3, %r10
	xorq	%rbx, %rcx
	rolq	$27, %rdi
	rorq	$25, %rcx
	xorq	%rsi, %r12
	xorq	32(%rsp), %rbx
	rolq	$20, %r11
	movq	%rcx, -8(%rsp)
	xorq	%rsi, %r9
	movq	%r15, %rcx
	xorq	24(%rsp), %rsi
	rolq	$25, %r9
	movq	%rax, %r15
	rolq	$21, %r12
	movabsq	$-9223372036854743031, %rax
	rorq	$8, %rsi
	rolq	$14, %rbx
	rolq	$28, %rdx
	rolq	$8, %rcx
	xorq	%r14, %r15
	xorq	%r15, %rax
	movq	%r13, %r15
	notq	%r15
	movq	%rax, -104(%rsp)
	movq	%r12, %rax
	orq	%r12, %r15
	andq	%rbx, %rax
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	movq	%r14, %rax
	andq	%rbp, %r14
	orq	%rbx, %rax
	movq	-72(%rsp), %rbp
	xorq	%r13, %r15
	movq	%rax, %r13
	movq	%r14, %rax
	movq	40(%rsp), %r14
	xorq	%rbx, %rax
	movq	%rbp, %rbx
	xorq	%r12, %r13
	movq	-56(%rsp), %r12
	orq	%r11, %rbx
	movq	%rax, -80(%rsp)
	movq	-32(%rsp), %rax
	xorq	%rdx, %rbx
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r10, %rbx
	notq	%rbx
	orq	%rax, %rbx
	xorq	%rbx, %rbp
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	64(%rsp), %r11
	xorq	%r10, %rdx
	movq	%rcx, %r10
	xorq	%rax, %rbx
	andq	%r9, %rcx
	movq	%rdx, -40(%rsp)
	notq	%r10
	movq	%r8, %rdx
	movq	%r10, %rax
	orq	%r9, %rdx
	movq	%r11, %r10
	movq	%rbx, -48(%rsp)
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	movq	56(%rsp), %rcx
	xorq	%r8, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rcx, %rdx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	xorq	%rax, %rdx
	movq	%r11, %rax
	movq	%rsi, %r11
	andq	%r8, %rax
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	xorq	%rax, %rcx
	movq	%r14, %rax
	andq	%r12, %rax
	notq	%rdx
	movq	%rcx, %r8
	movq	%rax, %r9
	movq	(%rsp), %rax
	xorq	%rdi, %r9
	orq	%r12, %rax
	orq	%rdx, %r11
	xorq	%r11, %r12
	movq	%rsi, %r11
	xorq	%r14, %rax
	andq	%rdi, %r11
	xorq	%rdx, %r11
	movq	%r14, %rdx
	orq	%rdi, %rdx
	movq	%r11, 8(%rsp)
	movq	-8(%rsp), %rcx
	movq	%rdx, %r11
	movq	48(%rsp), %rdi
	movq	72(%rsp), %rbx
	movq	%rbp, -56(%rsp)
	xorq	%rsi, %r11
	movq	-112(%rsp), %rsi
	movq	80(%rsp), %r14
	movq	%r12, (%rsp)
	movq	%r11, 16(%rsp)
	notq	%rsi
	movq	%r8, -8(%rsp)
	movq	%rsi, %rdx
	movq	%rcx, %rsi
	andq	%rdx, %rsi
	movq	%rsi, %r11
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%rcx, %rdi
	movq	-96(%rsp), %r14
	xorq	-72(%rsp), %r14
	movq	%rbx, %rcx
	movq	%r13, %rbx
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	xorq	%r9, %rbx
	xorq	-32(%rsp), %r14
	movq	%rdi, 24(%rsp)
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%r10, %rbx
	xorq	%r15, %r13
	xorq	%rax, %r14
	xorq	%r11, %rbx
	xorq	-104(%rsp), %rbx
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%rsi, %r14
	xorq	%rdx, %r13
	movq	%rcx, 32(%rsp)
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rbp, %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	16(%rsp), %rdi
	rolq	%rcx
	rolq	%r8
	xorq	%r14, %rcx
	movq	-104(%rsp), %r14
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%rdi
	xorq	%rbp, %r9
	xorq	%r13, %rdi
	rolq	%r8
	movq	-112(%rsp), %r13
	rorq	$23, %r9
	xorq	%rbx, %r8
	xorq	%rbp, %r10
	xorq	%rbp, %r11
	movq	%r9, 56(%rsp)
	movq	-96(%rsp), %r9
	xorq	%rbp, %r13
	xorq	%rbp, %r14
	rorq	$28, %r13
	rolq	$3, %r10
	xorq	%r8, %rax
	rolq	$18, %r11
	xorq	%r8, %r9
	movq	%r13, 40(%rsp)
	rolq	%rbx
	rolq	%r9
	movq	%r10, 48(%rsp)
	xorq	%r12, %rbx
	movq	%r11, 64(%rsp)
	movq	%r9, 72(%rsp)
	movq	-72(%rsp), %r13
	movq	-32(%rsp), %r9
	movq	-88(%rsp), %r10
	xorq	%r8, %r13
	movq	(%rsp), %r12
	movq	-40(%rsp), %r11
	xorq	%r8, %r9
	movq	%r13, %rbp
	movq	-24(%rsp), %r13
	rorq	$20, %rbp
	rolq	$10, %r9
	rorq	$19, %rax
	xorq	%r8, %rsi
	xorq	%rcx, %r15
	movq	%r9, 80(%rsp)
	rolq	$2, %rsi
	movq	-56(%rsp), %r9
	xorq	%rdi, %r10
	xorq	%rcx, %r13
	movq	%rsi, 88(%rsp)
	movq	%r15, %rsi
	xorq	%rcx, %r12
	xorq	%rcx, %rdx
	rorq	$2, %rsi
	xorq	%rcx, %r9
	movq	%r10, %rcx
	movq	-48(%rsp), %r10
	movq	%rsi, 96(%rsp)
	rolq	$15, %r12
	rorq	$21, %r13
	xorq	%rbx, %r11
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r10
	movq	%r12, (%rsp)
	rolq	$6, %r9
	rorq	$9, %r10
	movq	-80(%rsp), %r8
	movq	8(%rsp), %r12
	rorq	$3, %rdx
	movq	%r10, -112(%rsp)
	rolq	$20, %r11
	xorq	%rbx, %rsi
	rolq	$28, %rcx
	movq	-16(%rsp), %r10
	movq	%rsi, %r15
	movq	16(%rsp), %rsi
	xorq	%rdi, %r12
	rorq	$25, %r15
	xorq	%rbx, %r8
	rolq	$21, %r12
	xorq	%rdi, %r10
	xorq	%rbx, %rsi
	xorq	24(%rsp), %rdi
	movq	%r15, -8(%rsp)
	rolq	$25, %r10
	xorq	32(%rsp), %rbx
	movq	%rbp, %r15
	rorq	$8, %rdi
	rolq	$27, %r8
	rolq	$8, %rsi
	rolq	$14, %rbx
	orq	%r13, %r15
	xorq	%r14, %r15
	xorb	$-118, %r15b
	movq	%r15, -104(%rsp)
	movq	%r13, %r15
	notq	%r15
	orq	%r12, %r15
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%r12, %r15
	andq	%rbx, %r15
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	movq	48(%rsp), %rbp
	xorq	%rbx, %r14
	orq	%rbx, %r13
	movq	%rbp, %rbx
	xorq	%r12, %r13
	movq	%rdx, %r12
	movq	%r14, -80(%rsp)
	orq	%r11, %rbx
	notq	%r12
	movq	%r13, -88(%rsp)
	xorq	%rcx, %rbx
	movq	%rbx, -72(%rsp)
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -56(%rsp)
	movq	%r12, %rbx
	movq	%rdx, %r12
	orq	%rcx, %r12
	andq	%r11, %rcx
	orq	%rax, %rbx
	xorq	%rax, %r12
	movq	%rcx, %rax
	movq	72(%rsp), %rcx
	xorq	%rbx, %rbp
	xorq	%rdx, %rax
	movq	%r9, %rdx
	movq	%r12, -48(%rsp)
	orq	%r10, %rdx
	movq	%rax, -40(%rsp)
	movq	%rcx, %r11
	movq	%rsi, %rax
	andq	%r10, %rsi
	xorq	%rdx, %r11
	notq	%rax
	movq	%rsi, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	64(%rsp), %rsi
	movq	40(%rsp), %r14
	movq	80(%rsp), %r12
	movq	%rsi, %rdx
	movq	-8(%rsp), %r13
	movq	88(%rsp), %rbx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rsi, %r10
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	movq	%rbx, %rsi
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%rcx, %r10
	movq	%rdi, %rcx
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	andq	%r12, %rax
	movq	%rax, %r9
	movq	(%rsp), %rax
	movq	%r10, -8(%rsp)
	notq	%rdx
	xorq	%r8, %r9
	orq	%rdx, %rcx
	orq	%r12, %rax
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	xorq	%r14, %rax
	andq	%r8, %rcx
	movq	%r12, (%rsp)
	xorq	%rdx, %rcx
	movq	%r14, %rdx
	movq	96(%rsp), %r14
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %r8
	movq	-112(%rsp), %rdx
	orq	%r14, %rsi
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	notq	%rdx
	movq	%r8, 16(%rsp)
	movq	%r13, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%r13, %rcx
	xorq	%r14, %r8
	andq	-112(%rsp), %r14
	movq	%rbp, -112(%rsp)
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	xorq	%rsi, %rdi
	movq	-88(%rsp), %rsi
	andq	%rbx, %rdx
	xorq	%r14, %rbx
	movq	-56(%rsp), %r14
	xorq	-32(%rsp), %r14
	xorq	%r13, %rdx
	movq	%r15, %r13
	movq	%rbx, 32(%rsp)
	xorq	%rax, %r14
	xorq	%rdx, %r13
	movq	-72(%rsp), %rbx
	xorq	%rcx, %r14
	xorq	-96(%rsp), %r14
	xorq	%rbp, %r13
	movq	-24(%rsp), %rbp
	movq	%rdi, 24(%rsp)
	xorq	%r11, %rbx
	xorq	%rbp, %r13
	xorq	%r9, %rbx
	xorq	-104(%rsp), %rbx
	movq	8(%rsp), %rbp
	xorq	%r12, %r13
	movq	-16(%rsp), %r12
	xorq	%r8, %rbx
	xorq	-48(%rsp), %rsi
	xorq	%rsi, %r12
	movq	-80(%rsp), %rsi
	xorq	%rbp, %r12
	movq	-40(%rsp), %rbp
	xorq	%rdi, %r12
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	rolq	%rdi
	xorq	%r10, %rsi
	movq	%rdi, %rbp
	xorq	16(%rsp), %rsi
	xorq	32(%rsp), %rsi
	xorq	%rsi, %rbp
	rolq	%rsi
	movq	%r13, %rdi
	movq	%r12, %r10
	xorq	%r13, %rsi
	movq	-72(%rsp), %r13
	xorq	%rbp, %r9
	xorq	%rbp, %r11
	rorq	$23, %r9
	rolq	$3, %r11
	xorq	%rbp, %r8
	movq	%r9, 48(%rsp)
	xorq	%rbp, %r13
	movq	-56(%rsp), %r9
	rolq	%rdi
	rorq	$28, %r13
	rolq	%r10
	xorq	%rbx, %rdi
	movq	%r11, -72(%rsp)
	xorq	%r14, %r10
	movq	%r13, 40(%rsp)
	movq	-104(%rsp), %r14
	xorq	%rdi, %r9
	movq	-96(%rsp), %r11
	movq	-32(%rsp), %r13
	rolq	%rbx
	rolq	$18, %r8
	xorq	%rbp, %r14
	movq	%r9, %rbp
	xorq	%r12, %rbx
	movq	-48(%rsp), %r12
	xorq	%rdi, %r11
	xorq	%rdi, %r13
	rorq	$20, %rbp
	movq	%r8, 56(%rsp)
	rolq	%r11
	rolq	$10, %r13
	xorq	%rdi, %rcx
	movq	-112(%rsp), %r8
	movq	%r11, 64(%rsp)
	movq	%rcx, %r11
	movq	%r15, %rcx
	movq	(%rsp), %r15
	xorq	%r10, %rcx
	rolq	$2, %r11
	xorq	%rsi, %r12
	xorq	%rdi, %rax
	xorq	%r10, %r15
	movq	%rcx, %r9
	rorq	$9, %r12
	movq	%r11, 72(%rsp)
	rorq	$2, %r9
	movq	%r15, %rcx
	movq	-40(%rsp), %r15
	xorq	%r10, %r8
	rolq	$15, %rcx
	movq	%r9, 80(%rsp)
	movq	-24(%rsp), %r9
	rorq	$19, %rax
	xorq	%rbx, %r15
	movq	%rcx, (%rsp)
	movq	-8(%rsp), %rcx
	rolq	$6, %r8
	xorq	%r10, %r9
	movq	%r15, %r11
	movq	16(%rsp), %r15
	xorq	%rdx, %r10
	movq	%r13, -56(%rsp)
	xorq	%rbx, %rcx
	movq	-88(%rsp), %rdx
	movq	%r9, %r13
	movq	%r12, 88(%rsp)
	movq	-16(%rsp), %r9
	xorq	%rbx, %r15
	rorq	$25, %rcx
	movq	8(%rsp), %r12
	rorq	$21, %r13
	xorq	%rsi, %rdx
	rorq	$3, %r10
	movq	-80(%rsp), %rdi
	rolq	$20, %r11
	xorq	%rsi, %r9
	rolq	$28, %rdx
	xorq	%rsi, %r12
	movq	%rcx, -8(%rsp)
	xorq	24(%rsp), %rsi
	movq	%r15, %rcx
	rolq	$25, %r9
	xorq	%rbx, %rdi
	movq	%rbp, %r15
	rolq	$21, %r12
	rorq	$8, %rsi
	rolq	$27, %rdi
	rolq	$8, %rcx
	orq	%r13, %r15
	xorq	32(%rsp), %rbx
	xorq	%r14, %r15
	rolq	$14, %rbx
	xorb	$-120, %r15b
	movq	%r15, -112(%rsp)
	movq	%r13, %r15
	notq	%r15
	orq	%r12, %r15
	xorq	%rbp, %r15
	movq	%r15, -104(%rsp)
	movq	%r12, %r15
	andq	%rbx, %r15
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	orq	%rbx, %r13
	xorq	%rbx, %r14
	movq	%r15, -96(%rsp)
	movq	72(%rsp), %r15
	xorq	%r12, %r13
	movq	-72(%rsp), %r12
	movq	%r13, -88(%rsp)
	movq	80(%rsp), %r13
	movq	%r12, %rbx
	orq	%r11, %rbx
	xorq	%rdx, %rbx
	movq	%rbx, -80(%rsp)
	movq	%r12, %rbx
	andq	%rax, %rbx
	movq	%rbx, %rbp
	movq	%r10, %rbx
	notq	%rbx
	xorq	%r11, %rbp
	orq	%rax, %rbx
	movq	%rbp, -72(%rsp)
	movq	40(%rsp), %rbp
	xorq	%rbx, %r12
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	64(%rsp), %r11
	xorq	%r10, %rdx
	xorq	%rax, %rbx
	movq	%rcx, %rax
	andq	%r9, %rcx
	movq	%rdx, -40(%rsp)
	movq	%r8, %rdx
	movq	%r11, %r10
	notq	%rax
	orq	%r9, %rdx
	movq	%rbx, -48(%rsp)
	movq	-56(%rsp), %rbx
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	movq	56(%rsp), %rcx
	movq	%r12, -56(%rsp)
	xorq	%r8, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rcx, %rdx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	xorq	%rax, %rdx
	movq	%r11, %rax
	movq	88(%rsp), %r11
	andq	%r8, %rax
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	xorq	%rax, %rcx
	movq	%rbp, %rax
	andq	%rbx, %rax
	movq	%rcx, %r8
	notq	%rdx
	movq	%rsi, %rcx
	movq	%rax, %r9
	movq	(%rsp), %rax
	orq	%rdx, %rcx
	xorq	%rdi, %r9
	orq	%rbx, %rax
	xorq	%rcx, %rbx
	movq	%rsi, %rcx
	andq	%rdi, %rcx
	xorq	%rbp, %rax
	movq	%rbx, (%rsp)
	xorq	%rdx, %rcx
	movq	%rbp, %rdx
	orq	%rdi, %rdx
	movq	%rcx, 8(%rsp)
	movq	-8(%rsp), %rcx
	movq	%rdx, %rbp
	movq	48(%rsp), %rdi
	xorq	%rsi, %rbp
	movq	%r11, %rsi
	notq	%rsi
	movq	%rbp, 16(%rsp)
	movq	%rcx, %rbp
	movq	%rsi, %rdx
	andq	%rsi, %rbp
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r13, %rbp
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%r15, %rdx
	xorq	%rcx, %rdx
	movq	%r15, %rcx
	orq	%r13, %rcx
	andq	%r11, %r13
	movq	-80(%rsp), %r11
	xorq	%r13, %r15
	movq	-24(%rsp), %r13
	xorq	%rcx, %rdi
	xorq	%r9, %r11
	movq	%r15, %rcx
	movq	-104(%rsp), %r15
	xorq	-72(%rsp), %r15
	xorq	-32(%rsp), %r15
	xorq	%r10, %r11
	xorq	%r12, %r13
	xorq	-96(%rsp), %r13
	xorq	%rax, %r15
	xorq	%rbp, %r11
	xorq	-112(%rsp), %r11
	xorq	%rsi, %r15
	xorq	%rbx, %r13
	movq	-88(%rsp), %rbx
	xorq	-48(%rsp), %rbx
	xorq	8(%rsp), %rbx
	xorq	-16(%rsp), %rbx
	movq	%rdi, 24(%rsp)
	xorq	%rdx, %r13
	xorq	%rdi, %rbx
	movq	-40(%rsp), %rdi
	movq	%rcx, 32(%rsp)
	movq	%r8, -8(%rsp)
	xorq	%rcx, %rdi
	movq	%r15, %rcx
	xorq	%r14, %rdi
	rolq	%rcx
	xorq	%r8, %rdi
	movq	%rcx, %r12
	xorq	16(%rsp), %rdi
	movq	%rbx, %rcx
	xorq	%rdi, %r12
	rolq	%rcx
	movq	%r13, %r8
	xorq	%r12, %r9
	xorq	%r12, %rbp
	rolq	%rdi
	xorq	%r15, %rcx
	xorq	%r13, %rdi
	movq	-112(%rsp), %r15
	rorq	$23, %r9
	xorq	%r12, %r10
	rolq	$18, %rbp
	movq	-80(%rsp), %r13
	movq	%r9, 56(%rsp)
	rolq	%r8
	movq	%rbp, 64(%rsp)
	movq	-104(%rsp), %r9
	xorq	%r11, %r8
	xorq	%r12, %r15
	movq	-72(%rsp), %rbp
	rolq	%r11
	xorq	%r12, %r13
	rolq	$3, %r10
	xorq	%rbx, %r11
	xorq	%r8, %r9
	movq	%r15, %rbx
	movq	%r13, %r15
	xorq	%r8, %rbp
	rorq	$28, %r15
	movq	-96(%rsp), %r13
	movq	(%rsp), %r12
	rolq	%r9
	rorq	$20, %rbp
	xorq	%r8, %rsi
	xorq	%rcx, %rdx
	rolq	$2, %rsi
	movq	%r15, 40(%rsp)
	xorq	%rcx, %r13
	xorq	%rcx, %r12
	movq	-32(%rsp), %r15
	movq	%rsi, 80(%rsp)
	xorq	%r11, %r14
	xorq	%r8, %rax
	movq	-56(%rsp), %rsi
	movq	%r9, 72(%rsp)
	rorq	$19, %rax
	rorq	$3, %rdx
	xorq	%r8, %r15
	movq	-16(%rsp), %r9
	movq	%r10, 48(%rsp)
	movq	%r14, %r8
	rolq	$10, %r15
	xorq	%rcx, %rsi
	rolq	$27, %r8
	movq	%r15, -32(%rsp)
	movq	%r13, %r15
	movq	%rsi, %r13
	movq	%r12, %rsi
	rolq	$6, %r13
	movq	-88(%rsp), %r12
	rolq	$15, %rsi
	xorq	%rdi, %r9
	movq	%r13, 88(%rsp)
	movq	-24(%rsp), %r13
	rorq	$2, %r15
	rolq	$25, %r9
	xorq	%rdi, %r12
	movq	%rsi, (%rsp)
	xorq	%rcx, %r13
	movq	%r12, %rcx
	movq	-48(%rsp), %r12
	rorq	$21, %r13
	rolq	$28, %rcx
	xorq	%rdi, %r12
	rorq	$9, %r12
	movq	%r12, -112(%rsp)
	movq	8(%rsp), %r12
	xorq	%rdi, %r12
	xorq	24(%rsp), %rdi
	movq	-8(%rsp), %rsi
	movq	%r8, 8(%rsp)
	movq	-40(%rsp), %r10
	rolq	$21, %r12
	rorq	$8, %rdi
	movq	%rbp, %r8
	xorq	%r11, %rsi
	xorq	%r11, %r10
	movq	%rsi, %r14
	rolq	$20, %r10
	rorq	$25, %r14
	orq	%r13, %r8
	movq	%r14, -8(%rsp)
	movq	16(%rsp), %r14
	xorq	%r11, %r14
	xorq	32(%rsp), %r11
	movq	%r14, %rsi
	movq	%r8, %r14
	movl	$2147516425, %r8d
	rolq	$14, %r11
	xorq	%rbx, %r14
	rolq	$8, %rsi
	xorq	%r14, %r8
	movq	%r13, %r14
	notq	%r14
	movq	%r8, -104(%rsp)
	movq	%r12, %r8
	orq	%r12, %r14
	andq	%r11, %r8
	xorq	%rbp, %r14
	movq	%r14, -96(%rsp)
	movq	%r8, %r14
	movq	%rdx, %r8
	xorq	%r13, %r14
	movq	%rbx, %r13
	andq	%rbp, %rbx
	notq	%r8
	xorq	%r11, %rbx
	orq	%r11, %r13
	movq	%rbx, -80(%rsp)
	movq	48(%rsp), %rbx
	xorq	%r12, %r13
	movq	%r13, -88(%rsp)
	movq	-32(%rsp), %r12
	movq	%rbx, %r11
	orq	%r10, %r11
	xorq	%rcx, %r11
	movq	%r11, -72(%rsp)
	movq	%rbx, %r11
	andq	%rax, %r11
	movq	%r11, %rbp
	movq	%r8, %r11
	movq	%rdx, %r8
	orq	%rcx, %r8
	andq	%r10, %rcx
	orq	%rax, %r11
	xorq	%r10, %rbp
	xorq	%rax, %r8
	movq	%rcx, %rax
	movq	88(%rsp), %rcx
	movq	72(%rsp), %r10
	xorq	%rdx, %rax
	movq	%rsi, %rdx
	andq	%r9, %rsi
	movq	%rbp, -56(%rsp)
	notq	%rdx
	movq	%rcx, %r13
	movq	%rax, -40(%rsp)
	movq	%r10, %rbp
	xorq	%rsi, %r13
	movq	%rdx, %rax
	movq	64(%rsp), %rsi
	movq	%rcx, %rdx
	orq	%r9, %rdx
	xorq	%r11, %rbx
	movq	%r8, -48(%rsp)
	movq	8(%rsp), %r8
	xorq	%rdx, %rbp
	movq	%rsi, %rdx
	movq	80(%rsp), %r11
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rsi, %r9
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	movq	40(%rsp), %rsi
	orq	%r10, %rdx
	andq	%rcx, %r10
	movq	%rdi, %rcx
	xorq	%rax, %rdx
	movq	(%rsp), %rax
	xorq	%r10, %r9
	movq	%rsi, %r10
	movq	%rdx, -16(%rsp)
	andq	%r12, %r10
	movq	%rax, %rdx
	orq	%r12, %rax
	xorq	%r8, %r10
	notq	%rdx
	xorq	%rsi, %rax
	orq	%rdx, %rcx
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	andq	%r8, %rcx
	xorq	%rdx, %rcx
	movq	%rsi, %rdx
	movq	-8(%rsp), %rsi
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %rcx
	movq	-112(%rsp), %rdx
	movq	%rsi, %r8
	xorq	%rdi, %rcx
	movq	56(%rsp), %rdi
	movq	%rcx, 16(%rsp)
	notq	%rdx
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%rsi, %rcx
	xorq	%r15, %r8
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%r11, %rdx
	xorq	%rsi, %rdx
	movq	%r11, %rsi
	orq	%r15, %rsi
	xorq	%rsi, %rdi
	movq	-112(%rsp), %rsi
	andq	%r15, %rsi
	xorq	%rsi, %r11
	movq	%r11, 32(%rsp)
	movq	-72(%rsp), %r15
	movq	-56(%rsp), %rsi
	movq	%r13, -32(%rsp)
	xorq	%rbp, %r15
	movq	%rbx, -112(%rsp)
	xorq	%r13, %rsi
	movq	%r15, %r11
	movq	%r14, %r13
	movq	%r9, -8(%rsp)
	movq	%rsi, %r15
	xorq	%r10, %r11
	xorq	-104(%rsp), %r11
	movq	-88(%rsp), %rsi
	xorq	%rax, %r15
	xorq	%r8, %r11
	movq	%r12, (%rsp)
	xorq	%rcx, %r15
	xorq	-96(%rsp), %r15
	xorq	%rdx, %r13
	xorq	-48(%rsp), %rsi
	xorq	%rbx, %r13
	movq	-16(%rsp), %rbx
	xorq	-24(%rsp), %r13
	movq	%rdi, 24(%rsp)
	xorq	%r12, %r13
	xorq	%rsi, %rbx
	movq	-80(%rsp), %rsi
	xorq	-40(%rsp), %rsi
	xorq	%r9, %rsi
	movq	%r15, %r9
	xorq	8(%rsp), %rbx
	xorq	16(%rsp), %rsi
	rolq	%r9
	xorq	32(%rsp), %rsi
	xorq	%rdi, %rbx
	movq	%r13, %rdi
	movq	%r9, %r12
	movq	%rbx, %r9
	rolq	%rdi
	xorq	%rsi, %r12
	rolq	%r9
	xorq	%r11, %rdi
	xorq	%r12, %r8
	xorq	%r15, %r9
	rolq	%rsi
	movq	-72(%rsp), %r15
	rolq	$18, %r8
	rolq	%r11
	xorq	%r13, %rsi
	movq	-32(%rsp), %r13
	movq	%r8, 56(%rsp)
	movq	-96(%rsp), %r8
	xorq	%rbx, %r11
	xorq	%r12, %r15
	movq	-104(%rsp), %rbx
	xorq	%r12, %rbp
	xorq	%r12, %r10
	rorq	$28, %r15
	rolq	$3, %rbp
	xorq	%rdi, %r8
	rorq	$23, %r10
	movq	%r15, 40(%rsp)
	xorq	%r12, %rbx
	rolq	%r8
	xorq	%rdi, %r13
	xorq	%rdi, %rcx
	movq	%r13, %r15
	movq	%rcx, %r13
	movq	-112(%rsp), %rcx
	xorq	%r9, %r14
	rolq	$10, %r15
	movq	%r10, 48(%rsp)
	rolq	$2, %r13
	xorq	%rdi, %rax
	xorq	%r9, %rcx
	movq	-56(%rsp), %r10
	movq	%r15, -56(%rsp)
	movq	%r14, %r15
	movq	%rbp, -72(%rsp)
	rorq	$19, %rax
	movq	%rcx, %r14
	rorq	$2, %r15
	rolq	$6, %r14
	movq	%r8, 64(%rsp)
	xorq	%rdi, %r10
	movq	%r14, 72(%rsp)
	movq	%r10, %rbp
	movq	%r13, -32(%rsp)
	movq	-24(%rsp), %r13
	rorq	$20, %rbp
	movq	(%rsp), %r12
	movq	-80(%rsp), %rdi
	xorq	%r9, %r13
	movq	-40(%rsp), %r10
	movq	16(%rsp), %r14
	xorq	%r9, %r12
	xorq	%rdx, %r9
	movq	-88(%rsp), %rdx
	xorq	%r11, %rdi
	rolq	$15, %r12
	xorq	%r11, %r10
	rorq	$21, %r13
	movq	%r12, (%rsp)
	movq	-48(%rsp), %r12
	xorq	%rsi, %rdx
	rorq	$3, %r9
	rolq	$28, %rdx
	rolq	$27, %rdi
	xorq	%rsi, %r12
	movq	%rdx, -24(%rsp)
	movq	%rbp, %rdx
	movq	%r12, %rcx
	movq	-16(%rsp), %r12
	rorq	$9, %rcx
	xorq	%rsi, %r12
	movq	%rcx, 80(%rsp)
	movq	-8(%rsp), %rcx
	movq	%r12, %r8
	movq	8(%rsp), %r12
	rolq	$25, %r8
	xorq	%rsi, %r12
	xorq	24(%rsp), %rsi
	rolq	$21, %r12
	rorq	$8, %rsi
	rolq	$20, %r10
	xorq	%r11, %rcx
	xorq	%r11, %r14
	orq	%r13, %rdx
	rorq	$25, %rcx
	xorq	32(%rsp), %r11
	movq	%rcx, -8(%rsp)
	movq	%r14, %rcx
	movq	%rdx, %r14
	movl	$2147483658, %edx
	rolq	$14, %r11
	xorq	%rbx, %r14
	rolq	$8, %rcx
	xorq	%r14, %rdx
	movq	%r13, %r14
	notq	%r14
	movq	%rdx, -112(%rsp)
	movq	%r12, %rdx
	orq	%r12, %r14
	andq	%r11, %rdx
	xorq	%rbp, %r14
	movq	%r14, -104(%rsp)
	movq	%rdx, %r14
	movq	%rbx, %rdx
	andq	%rbp, %rbx
	orq	%r11, %rdx
	xorq	%r13, %r14
	movq	%rdx, %r13
	movq	%rbx, %rdx
	movq	-72(%rsp), %rbx
	xorq	%r11, %rdx
	xorq	%r12, %r13
	movq	%rbx, %r11
	movq	%rdx, -88(%rsp)
	movq	%r9, %rdx
	orq	%r10, %r11
	movq	%r13, -96(%rsp)
	notq	%rdx
	movq	-24(%rsp), %r13
	movq	%r11, %r12
	movq	%rbx, %r11
	andq	%rax, %r11
	xorq	%r13, %r12
	movq	%r11, %rbp
	movq	%rdx, %r11
	movq	%r9, %rdx
	movq	%r12, -80(%rsp)
	orq	%r13, %rdx
	andq	%r10, %r13
	orq	%rax, %r11
	xorq	%r10, %rbp
	xorq	%rax, %rdx
	xorq	%r11, %rbx
	movq	64(%rsp), %r11
	movq	%rcx, %rax
	movq	%rdx, -48(%rsp)
	movq	%r13, %rdx
	andq	%r8, %rcx
	notq	%rax
	xorq	%r9, %rdx
	movq	72(%rsp), %r9
	movq	%r11, %r10
	movq	%rbp, -72(%rsp)
	movq	%rdx, -40(%rsp)
	movq	%r9, %rdx
	movq	%r9, %r12
	orq	%r8, %rdx
	xorq	%rcx, %r12
	movq	%r11, %rcx
	xorq	%rdx, %r10
	movq	56(%rsp), %rdx
	andq	%rax, %rdx
	xorq	%r8, %rdx
	movq	56(%rsp), %r8
	movq	%rdx, -24(%rsp)
	movq	%r8, %rdx
	orq	%r11, %rdx
	movq	%rdx, %r11
	xorq	%rax, %r11
	movq	%rcx, %rax
	movq	%rsi, %rcx
	andq	%r9, %rax
	movq	%r11, -16(%rsp)
	xorq	%rax, %r8
	movq	(%rsp), %rax
	movq	40(%rsp), %rbp
	movq	-56(%rsp), %r11
	movq	-32(%rsp), %r13
	movq	%rbx, -56(%rsp)
	movq	%rax, %rdx
	movq	%rbp, %r9
	movq	%r12, -32(%rsp)
	notq	%rdx
	andq	%r11, %r9
	orq	%r11, %rax
	orq	%rdx, %rcx
	xorq	%rdi, %r9
	xorq	%rbp, %rax
	xorq	%rcx, %r11
	movq	-8(%rsp), %rcx
	movq	%r8, -8(%rsp)
	movq	%r11, (%rsp)
	movq	%rsi, %r11
	andq	%rdi, %r11
	xorq	%rdx, %r11
	movq	%rbp, %rdx
	orq	%rdi, %rdx
	movq	48(%rsp), %rdi
	movq	%r11, 8(%rsp)
	movq	%rdx, %rbp
	movq	80(%rsp), %rdx
	xorq	%rsi, %rbp
	movq	%rdi, %rsi
	movq	%rbp, 16(%rsp)
	notq	%rdx
	orq	%rcx, %rsi
	movq	%rcx, %rbp
	xorq	%rdx, %rsi
	andq	%rdx, %rbp
	movq	%rdi, %rdx
	andq	%r13, %rdx
	xorq	%r15, %rbp
	xorq	%rcx, %rdx
	movq	%r13, %rcx
	orq	%r15, %rcx
	xorq	%rcx, %rdi
	movq	80(%rsp), %rcx
	movq	%rdi, 24(%rsp)
	andq	%r15, %rcx
	movq	-80(%rsp), %r15
	xorq	%rcx, %r13
	xorq	%r9, %r15
	movq	%r13, 32(%rsp)
	movq	-24(%rsp), %r13
	movq	%r15, %r11
	movq	-104(%rsp), %r15
	xorq	-72(%rsp), %r15
	xorq	%r10, %r11
	xorq	%r12, %r15
	xorq	%rbp, %r11
	xorq	-112(%rsp), %r11
	xorq	%rax, %r15
	xorq	%rbx, %r13
	movq	-96(%rsp), %rbx
	xorq	-48(%rsp), %rbx
	xorq	%rsi, %r15
	xorq	%r14, %r13
	xorq	8(%rsp), %rbx
	xorq	-16(%rsp), %rbx
	xorq	%rdi, %rbx
	movq	-40(%rsp), %rdi
	xorq	32(%rsp), %rdi
	xorq	-88(%rsp), %rdi
	xorq	(%rsp), %r13
	movq	%rbx, %rcx
	xorq	%r8, %rdi
	movq	%r15, %r8
	xorq	16(%rsp), %rdi
	xorq	%rdx, %r13
	rolq	%r8
	rolq	%rcx
	movq	%r8, %r12
	movq	%r13, %r8
	xorq	%r15, %rcx
	xorq	%rdi, %r12
	rolq	%rdi
	xorq	%r13, %rdi
	movq	-80(%rsp), %r13
	rolq	%r8
	xorq	%r12, %r9
	xorq	%r11, %r8
	rolq	%r11
	xorq	%r12, %rbp
	xorq	%r12, %r10
	xorq	%r12, %r13
	xorq	%rbx, %r11
	movq	-112(%rsp), %rbx
	rolq	$3, %r10
	movq	%r13, %r15
	rorq	$28, %r15
	xorq	%r12, %rbx
	movq	%r15, 40(%rsp)
	movq	%r9, %r15
	movq	-104(%rsp), %r9
	rorq	$23, %r15
	movq	-24(%rsp), %r13
	movq	%r10, 48(%rsp)
	movq	%r15, 56(%rsp)
	movq	%rbp, %r15
	movq	-72(%rsp), %rbp
	rolq	$18, %r15
	xorq	%r8, %r9
	xorq	%r8, %rsi
	xorq	%r8, %rax
	rolq	%r9
	rolq	$2, %rsi
	xorq	%r8, %rbp
	xorq	%rcx, %r13
	movq	%r9, 72(%rsp)
	rorq	$20, %rbp
	xorq	%rcx, %rdx
	rorq	$19, %rax
	movq	-32(%rsp), %r9
	movq	%rsi, 80(%rsp)
	movq	%r14, %rsi
	rorq	$21, %r13
	xorq	%rcx, %rsi
	movq	%r15, 64(%rsp)
	movq	16(%rsp), %r15
	movq	%rbp, %r14
	rorq	$2, %rsi
	xorq	%r8, %r9
	movq	-88(%rsp), %r8
	rorq	$3, %rdx
	movq	%r9, %r12
	movq	(%rsp), %r9
	movq	%rsi, 88(%rsp)
	movq	-56(%rsp), %rsi
	rolq	$10, %r12
	xorq	%r11, %r8
	movq	-40(%rsp), %r10
	xorq	%rcx, %r9
	movq	%r12, -32(%rsp)
	movq	8(%rsp), %r12
	rolq	$15, %r9
	xorq	%rcx, %rsi
	movq	-96(%rsp), %rcx
	movq	%r9, (%rsp)
	movq	-48(%rsp), %r9
	rolq	$6, %rsi
	xorq	%rdi, %r12
	movq	%rsi, 96(%rsp)
	xorq	%rdi, %rcx
	rolq	$21, %r12
	xorq	%rdi, %r9
	rolq	$28, %rcx
	movq	%r9, %rsi
	movq	-16(%rsp), %r9
	rorq	$9, %rsi
	movq	%rsi, -112(%rsp)
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r9
	xorq	24(%rsp), %rdi
	rolq	$25, %r9
	rorq	$8, %rdi
	rolq	$27, %r8
	xorq	%r11, %rsi
	xorq	%r11, %r15
	rorq	$25, %rsi
	orq	%r13, %r14
	xorq	%r11, %r10
	xorq	32(%rsp), %r11
	movq	%rsi, -8(%rsp)
	xorq	%rbx, %r14
	movq	%r15, %rsi
	rolq	$14, %r11
	rolq	$20, %r10
	movl	$2147516555, %r15d
	rolq	$8, %rsi
	xorq	%r14, %r15
	movq	%r13, %r14
	notq	%r14
	orq	%r12, %r14
	xorq	%rbp, %r14
	movq	%r14, -104(%rsp)
	movq	%r12, %r14
	andq	%r11, %r14
	xorq	%r13, %r14
	movq	%rbx, %r13
	andq	%rbp, %rbx
	movq	48(%rsp), %rbp
	orq	%r11, %r13
	movq	%r14, -96(%rsp)
	xorq	%r12, %r13
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	xorq	%r11, %r13
	movq	%rbp, %r11
	orq	%r10, %r11
	movq	%r13, -80(%rsp)
	xorq	%rcx, %r11
	movq	%r11, -72(%rsp)
	movq	%rbp, %r11
	movq	96(%rsp), %rbx
	andq	%rax, %r11
	movq	40(%rsp), %r14
	movq	-32(%rsp), %r12
	xorq	%r10, %r11
	movq	%rbx, %r13
	movq	%r11, -56(%rsp)
	movq	%rdx, %r11
	notq	%r11
	orq	%rax, %r11
	xorq	%r11, %rbp
	movq	%rdx, %r11
	orq	%rcx, %r11
	andq	%r10, %rcx
	movq	64(%rsp), %r10
	xorq	%rdx, %rcx
	xorq	%rax, %r11
	movq	%rbx, %rdx
	movq	%rsi, %rax
	movq	%rcx, -40(%rsp)
	movq	72(%rsp), %rcx
	orq	%r9, %rdx
	notq	%rax
	movq	%r11, -48(%rsp)
	movq	%rcx, %r11
	xorq	%rdx, %r11
	movq	%r10, %rdx
	andq	%r9, %rsi
	andq	%rax, %rdx
	xorq	%rsi, %r13
	movq	-8(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%r14, %r9
	movq	%r13, -32(%rsp)
	movq	%rdx, -24(%rsp)
	movq	%r10, %rdx
	andq	%r12, %r9
	orq	%rcx, %rdx
	andq	%rbx, %rcx
	xorq	%r8, %r9
	movq	80(%rsp), %rbx
	xorq	%rax, %rdx
	movq	(%rsp), %rax
	xorq	%rcx, %r10
	movq	%rdi, %rcx
	movq	%rdx, -16(%rsp)
	movq	%rax, %rdx
	orq	%r12, %rax
	notq	%rdx
	xorq	%r14, %rax
	orq	%rdx, %rcx
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	andq	%r8, %rcx
	movq	%r12, (%rsp)
	xorq	%rdx, %rcx
	movq	%r14, %rdx
	movq	88(%rsp), %r14
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %r8
	movq	-112(%rsp), %rdx
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	notq	%rdx
	movq	%r8, 16(%rsp)
	movq	%rsi, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%rsi, %rcx
	xorq	%r14, %r8
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rsi, %rdx
	movq	%rbx, %rsi
	orq	%r14, %rsi
	andq	-112(%rsp), %r14
	movq	%rbp, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%rsi, %rdi
	movq	-56(%rsp), %r14
	movq	-96(%rsp), %rsi
	movq	%rbx, 32(%rsp)
	movq	-72(%rsp), %rbx
	xorq	%r11, %rbx
	xorq	%r9, %rbx
	xorq	%r15, %rbx
	xorq	%r8, %rbx
	xorq	%r13, %r14
	xorq	%rdx, %rsi
	movq	%rsi, %r13
	movq	-88(%rsp), %rsi
	xorq	%rax, %r14
	xorq	%rbp, %r13
	movq	-48(%rsp), %rbp
	xorq	-24(%rsp), %r13
	xorq	%rcx, %r14
	xorq	%r12, %r13
	xorq	-104(%rsp), %r14
	xorq	%rbp, %rsi
	movq	-16(%rsp), %rbp
	movq	%rsi, %r12
	xorq	%rbp, %r12
	xorq	8(%rsp), %r12
	movq	%rdi, 24(%rsp)
	movq	-40(%rsp), %rbp
	movq	-80(%rsp), %rsi
	xorq	%rdi, %r12
	movq	%r10, -8(%rsp)
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	rolq	%rdi
	xorq	%r10, %rsi
	movq	%r12, %r10
	xorq	16(%rsp), %rsi
	movq	%rdi, %rbp
	rolq	%r10
	xorq	32(%rsp), %rsi
	movq	%r13, %rdi
	xorq	%r14, %r10
	movq	%r15, %r14
	movq	-72(%rsp), %r15
	xorq	%rsi, %rbp
	rolq	%rdi
	rolq	%rsi
	xorq	%rbp, %r11
	xorq	%rbp, %r9
	xorq	%rbp, %r15
	xorq	%rbx, %rdi
	rolq	%rbx
	xorq	%r13, %rsi
	rorq	$28, %r15
	xorq	%r12, %rbx
	movq	(%rsp), %r12
	movq	-32(%rsp), %r13
	movq	%r15, 40(%rsp)
	movq	-56(%rsp), %r15
	xorq	%rbp, %r14
	rolq	$3, %r11
	rorq	$23, %r9
	xorq	%rdi, %rcx
	xorq	%r10, %r12
	xorq	%rbp, %r8
	xorq	%rdi, %r15
	xorq	%rdi, %r13
	movq	%r9, 48(%rsp)
	movq	-96(%rsp), %r9
	movq	%r15, %rbp
	movq	%rcx, %r15
	movq	%r12, %rcx
	movq	-48(%rsp), %r12
	rolq	$18, %r8
	rolq	$10, %r13
	xorq	%r10, %r9
	movq	%r11, -72(%rsp)
	xorq	%rsi, %r12
	movq	%r8, 56(%rsp)
	movq	-112(%rsp), %r8
	xorq	%rdi, %rax
	movq	%r13, -56(%rsp)
	movq	-24(%rsp), %r13
	rorq	$2, %r9
	rorq	$9, %r12
	rolq	$15, %rcx
	xorq	%r10, %r8
	movq	%r9, 80(%rsp)
	rorq	$20, %rbp
	xorq	%r10, %r13
	movq	%r12, -112(%rsp)
	xorq	%rdx, %r10
	movq	-104(%rsp), %r11
	movq	-88(%rsp), %rdx
	movq	%rcx, (%rsp)
	rolq	$6, %r8
	rorq	$21, %r13
	movq	-16(%rsp), %r9
	rorq	$3, %r10
	xorq	%rdi, %r11
	rorq	$19, %rax
	movq	8(%rsp), %r12
	movq	-8(%rsp), %rcx
	xorq	%rsi, %rdx
	rolq	%r11
	rolq	$28, %rdx
	xorq	%rsi, %r9
	rolq	$2, %r15
	movq	%r11, 64(%rsp)
	xorq	%rsi, %r12
	xorq	24(%rsp), %rsi
	rolq	$25, %r9
	movq	%rax, -32(%rsp)
	rolq	$21, %r12
	rorq	$8, %rsi
	xorq	%rbx, %rcx
	movq	%rbp, %rax
	rorq	$25, %rcx
	movq	%r15, 72(%rsp)
	movq	-80(%rsp), %rdi
	orq	%r13, %rax
	movq	-40(%rsp), %r11
	movq	%rcx, -8(%rsp)
	movq	16(%rsp), %r15
	xorq	%rbx, %rdi
	xorq	%rbx, %r11
	rolq	$27, %rdi
	xorq	%rbx, %r15
	xorq	32(%rsp), %rbx
	rolq	$20, %r11
	movq	%r15, %rcx
	movq	%rax, %r15
	rolq	$14, %rbx
	movabsq	$-9223372036854775669, %rax
	xorq	%r14, %r15
	rolq	$8, %rcx
	xorq	%r15, %rax
	movq	%rax, -104(%rsp)
	movq	%r13, %rax
	notq	%rax
	movq	%rax, %r15
	movq	%r12, %rax
	orq	%r12, %r15
	andq	%rbx, %rax
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	movq	-72(%rsp), %rbp
	movq	%r14, %rax
	orq	%rbx, %r13
	movq	40(%rsp), %r14
	xorq	%rbx, %rax
	movq	%rbp, %rbx
	xorq	%r12, %r13
	movq	-56(%rsp), %r12
	orq	%r11, %rbx
	movq	%rax, -80(%rsp)
	movq	-32(%rsp), %rax
	xorq	%rdx, %rbx
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r10, %rbx
	notq	%rbx
	orq	%rax, %rbx
	xorq	%rbx, %rbp
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	64(%rsp), %r11
	xorq	%r10, %rdx
	movq	%rcx, %r10
	xorq	%rax, %rbx
	movq	%rdx, -40(%rsp)
	notq	%r10
	movq	%r8, %rdx
	orq	%r9, %rdx
	movq	%r10, %rax
	andq	%r9, %rcx
	movq	%r11, %r10
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	movq	56(%rsp), %rcx
	movq	%rbx, -48(%rsp)
	xorq	%r8, %rdx
	movq	72(%rsp), %rbx
	movq	%rdx, -32(%rsp)
	movq	%rcx, %rdx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	andq	%r8, %r11
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%r11, %rcx
	movq	%rsi, %r11
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	andq	%r12, %rax
	movq	%rcx, %r8
	movq	%rax, %r9
	movq	(%rsp), %rax
	movq	-8(%rsp), %rcx
	notq	%rdx
	xorq	%rdi, %r9
	orq	%rdx, %r11
	orq	%r12, %rax
	xorq	%r11, %r12
	movq	%rsi, %r11
	xorq	%r14, %rax
	andq	%rdi, %r11
	xorq	%rdx, %r11
	movq	%r14, %rdx
	movq	80(%rsp), %r14
	orq	%rdi, %rdx
	movq	%r11, 8(%rsp)
	movq	48(%rsp), %rdi
	movq	%rdx, %r11
	xorq	%rsi, %r11
	movq	-112(%rsp), %rsi
	movq	%r11, 16(%rsp)
	movq	%rcx, %r11
	notq	%rsi
	movq	%rsi, %rdx
	andq	%rsi, %r11
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%rcx, %rdi
	movq	-96(%rsp), %r14
	movq	%rbx, %rcx
	movq	%r13, %rbx
	movq	%rbp, %r13
	xorq	%r9, %rbx
	xorq	%r10, %rbx
	xorq	%r11, %rbx
	xorq	-72(%rsp), %r14
	xorq	-104(%rsp), %rbx
	xorq	-32(%rsp), %r14
	movq	%rbp, -56(%rsp)
	movq	-24(%rsp), %rbp
	movq	%r12, (%rsp)
	xorq	%rax, %r14
	movq	%rdi, 24(%rsp)
	xorq	%rsi, %r14
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	movq	%r8, -8(%rsp)
	xorq	%r15, %r13
	movq	%rcx, 32(%rsp)
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%rdx, %r13
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rbp, %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	16(%rsp), %rdi
	rolq	%rcx
	rolq	%r8
	xorq	%r14, %rcx
	movq	-104(%rsp), %r14
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%rdi
	xorq	%r13, %rdi
	movq	-112(%rsp), %r13
	rolq	%r8
	xorq	%rbp, %r10
	xorq	%rbx, %r8
	rolq	%rbx
	xorq	%rbp, %r14
	xorq	%rbp, %r13
	xorq	%r12, %rbx
	movq	(%rsp), %r12
	rorq	$28, %r13
	rolq	$3, %r10
	xorq	%rbp, %r9
	xorq	%r8, %rax
	rorq	$23, %r9
	rorq	$19, %rax
	xorq	%r8, %rsi
	movq	%r13, 40(%rsp)
	movq	%r9, 56(%rsp)
	movq	-96(%rsp), %r9
	xorq	%rbp, %r11
	xorq	%rcx, %r12
	rolq	$2, %rsi
	movq	-72(%rsp), %r13
	rolq	$18, %r11
	xorq	%rcx, %rdx
	movq	%rsi, 88(%rsp)
	rolq	$15, %r12
	xorq	%r8, %r9
	rorq	$3, %rdx
	rolq	%r9
	xorq	%r8, %r13
	movq	%r11, 64(%rsp)
	movq	%r9, 72(%rsp)
	movq	-32(%rsp), %r9
	movq	%r13, %rbp
	movq	%rax, -32(%rsp)
	movq	%r15, %rax
	movq	-24(%rsp), %r13
	rorq	$20, %rbp
	xorq	%rcx, %rax
	xorq	%r8, %r9
	movq	%r12, (%rsp)
	movq	%rax, %rsi
	rolq	$10, %r9
	movq	%r10, 48(%rsp)
	xorq	%rcx, %r13
	rorq	$2, %rsi
	movq	%r9, 80(%rsp)
	rorq	$21, %r13
	movq	%rbp, %rax
	movq	%rsi, 96(%rsp)
	movq	-56(%rsp), %r9
	movq	-88(%rsp), %r10
	movq	8(%rsp), %r12
	xorq	%rcx, %r9
	movq	-8(%rsp), %rsi
	movq	-80(%rsp), %r8
	xorq	%rdi, %r10
	xorq	%rdi, %r12
	rolq	$6, %r9
	movq	-40(%rsp), %r11
	movq	%r10, %rcx
	movq	-48(%rsp), %r10
	rolq	$28, %rcx
	xorq	%rdi, %r10
	rorq	$9, %r10
	movq	%r10, -112(%rsp)
	movq	-16(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$25, %r10
	rolq	$21, %r12
	xorq	%rbx, %rsi
	orq	%r13, %rax
	movq	%rsi, %r15
	movq	16(%rsp), %rsi
	xorq	%rbx, %r8
	xorq	%rbx, %r11
	rorq	$25, %r15
	rolq	$20, %r11
	xorq	24(%rsp), %rdi
	movq	%r15, -8(%rsp)
	movq	%rax, %r15
	xorq	%rbx, %rsi
	xorq	32(%rsp), %rbx
	rolq	$14, %rbx
	xorq	%r14, %r15
	rorq	$8, %rdi
	movabsq	$-9223372036854742903, %rax
	rolq	$27, %r8
	xorq	%r15, %rax
	movq	%r13, %r15
	rolq	$8, %rsi
	notq	%r15
	movq	%rax, -104(%rsp)
	movq	%r12, %rax
	orq	%r12, %r15
	andq	%rbx, %rax
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	movq	%r14, %rax
	andq	%rbp, %r14
	movq	48(%rsp), %rbp
	orq	%rbx, %rax
	xorq	%rbx, %r14
	xorq	%r13, %r15
	movq	%r14, -80(%rsp)
	movq	-32(%rsp), %r14
	movq	%rax, %r13
	movq	%rdx, %rax
	movq	%rbp, %rbx
	notq	%rax
	xorq	%r12, %r13
	movq	80(%rsp), %r12
	orq	%r11, %rbx
	movq	%r13, -88(%rsp)
	xorq	%rcx, %rbx
	movq	%rbx, -72(%rsp)
	movq	%rbp, %rbx
	andq	%r14, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -56(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rax
	orq	%r14, %rbx
	orq	%rcx, %rax
	xorq	%rbx, %rbp
	xorq	%r14, %rax
	andq	%r11, %rcx
	movq	40(%rsp), %r14
	xorq	%rdx, %rcx
	movq	%rsi, %rdx
	movq	%rax, -48(%rsp)
	andq	%r10, %rsi
	movq	%rcx, -40(%rsp)
	notq	%rdx
	movq	72(%rsp), %rcx
	movq	%rdx, %rax
	movq	%r9, %rdx
	orq	%r10, %rdx
	movq	%rcx, %r11
	xorq	%rdx, %r11
	movq	%rsi, %rdx
	movq	64(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rsi, %r10
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%rcx, %r10
	movq	%rdi, %rcx
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	andq	%r12, %rax
	movq	%rax, %r9
	movq	(%rsp), %rax
	notq	%rdx
	xorq	%r8, %r9
	orq	%rdx, %rcx
	orq	%r12, %rax
	xorq	%rcx, %r12
	movq	%rdi, %rcx
	xorq	%r14, %rax
	andq	%r8, %rcx
	xorq	%rdx, %rcx
	movq	%r14, %rdx
	orq	%r8, %rdx
	movq	%rcx, 8(%rsp)
	movq	%rdx, %r8
	xorq	%rdi, %r8
	movq	%r8, 16(%rsp)
	movq	-8(%rsp), %r13
	movq	56(%rsp), %rdi
	movq	-112(%rsp), %rdx
	movq	%r12, (%rsp)
	movq	88(%rsp), %rbx
	movq	96(%rsp), %r14
	movq	%r13, %r8
	movq	%r10, -8(%rsp)
	notq	%rdx
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%r13, %rcx
	movq	%rbx, %rsi
	xorq	%r14, %r8
	xorq	%rdx, %rcx
	orq	%r14, %rsi
	movq	%rdi, %rdx
	andq	-112(%rsp), %r14
	andq	%rbx, %rdx
	xorq	%rsi, %rdi
	movq	%rbp, -112(%rsp)
	xorq	%r14, %rbx
	xorq	%r13, %rdx
	movq	%r15, %r13
	movq	-88(%rsp), %rsi
	movq	%rbx, 32(%rsp)
	movq	-72(%rsp), %rbx
	movq	-56(%rsp), %r14
	movq	%rdi, 24(%rsp)
	xorq	%r11, %rbx
	xorq	%rdx, %r13
	xorq	-32(%rsp), %r14
	xorq	%rbp, %r13
	movq	-48(%rsp), %rbp
	xorq	-24(%rsp), %r13
	xorq	%rax, %r14
	xorq	%r12, %r13
	xorq	%rcx, %r14
	xorq	-96(%rsp), %r14
	xorq	%r9, %rbx
	xorq	%rbp, %rsi
	movq	-16(%rsp), %rbp
	xorq	-104(%rsp), %rbx
	movq	%rsi, %r12
	movq	-80(%rsp), %rsi
	xorq	%r8, %rbx
	xorq	%rbp, %r12
	movq	-40(%rsp), %rbp
	xorq	8(%rsp), %r12
	xorq	%rdi, %r12
	movq	%r14, %rdi
	xorq	%rbp, %rsi
	rolq	%rdi
	xorq	%r10, %rsi
	movq	%rdi, %rbp
	xorq	16(%rsp), %rsi
	xorq	32(%rsp), %rsi
	xorq	%rsi, %rbp
	movq	%r12, %r10
	rolq	%rsi
	movq	%r13, %rdi
	rolq	%r10
	xorq	%r13, %rsi
	movq	-72(%rsp), %r13
	rolq	%rdi
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	xorq	%rbx, %rdi
	rolq	%rbx
	xorq	%rbp, %r13
	xorq	%r12, %rbx
	xorq	%rbp, %r14
	rorq	$28, %r13
	xorq	%rbp, %r11
	xorq	%rbp, %r9
	rolq	$3, %r11
	xorq	%rbp, %r8
	rorq	$23, %r9
	movq	%r13, 40(%rsp)
	movq	%r11, -72(%rsp)
	movq	-96(%rsp), %r11
	xorq	%rdi, %rax
	xorq	%rdi, %rcx
	rolq	$18, %r8
	movq	%r9, 48(%rsp)
	rorq	$19, %rax
	xorq	%rdi, %r11
	movq	%r8, 56(%rsp)
	rolq	%r11
	movq	%r11, 64(%rsp)
	movq	-32(%rsp), %r13
	movq	-56(%rsp), %r9
	movq	(%rsp), %r12
	movq	%rax, -32(%rsp)
	movq	%r15, %rax
	xorq	%rdi, %r13
	xorq	%r10, %rax
	movq	-112(%rsp), %r8
	xorq	%rdi, %r9
	rolq	$10, %r13
	xorq	%r10, %r12
	movq	%rax, %r15
	movq	%r13, -56(%rsp)
	movq	%r9, %rbp
	movq	-24(%rsp), %r13
	movq	%rcx, %r9
	rolq	$2, %r9
	rorq	$2, %r15
	xorq	%r10, %r8
	movq	%r12, %rcx
	movq	%r9, 72(%rsp)
	rolq	$15, %rcx
	xorq	%r10, %r13
	xorq	%rdx, %r10
	movq	-48(%rsp), %r12
	movq	-88(%rsp), %rdx
	movq	%r15, 80(%rsp)
	rorq	$20, %rbp
	movq	-16(%rsp), %r9
	rolq	$6, %r8
	rorq	$21, %r13
	movq	%rbp, %rax
	movq	-40(%rsp), %r15
	xorq	%rsi, %rdx
	xorq	%rsi, %r12
	rorq	$3, %r10
	xorq	%rsi, %r9
	rolq	$28, %rdx
	movq	%rcx, (%rsp)
	movq	-8(%rsp), %rcx
	rorq	$9, %r12
	rolq	$25, %r9
	xorq	%rbx, %r15
	orq	%r13, %rax
	movq	%r15, %r11
	movq	16(%rsp), %r15
	xorq	%rbx, %rcx
	movq	%r12, -112(%rsp)
	rorq	$25, %rcx
	movq	8(%rsp), %r12
	movq	-80(%rsp), %rdi
	rolq	$20, %r11
	xorq	%rbx, %r15
	movq	%rcx, -8(%rsp)
	movq	%r15, %rcx
	movq	%rax, %r15
	xorq	%rsi, %r12
	xorq	%rbx, %rdi
	rolq	$21, %r12
	xorq	%r14, %r15
	xorq	32(%rsp), %rbx
	rolq	$27, %rdi
	rolq	$14, %rbx
	xorq	24(%rsp), %rsi
	rolq	$8, %rcx
	movabsq	$-9223372036854743037, %rax
	xorq	%r15, %rax
	movq	%r13, %r15
	rorq	$8, %rsi
	notq	%r15
	movq	%rax, -104(%rsp)
	movq	%r12, %rax
	orq	%r12, %r15
	andq	%rbx, %rax
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	movq	%r14, %rax
	andq	%rbp, %r14
	orq	%rbx, %rax
	movq	-72(%rsp), %rbp
	xorq	%r13, %r15
	movq	%rax, %r13
	movq	%r14, %rax
	xorq	%rbx, %rax
	movq	%rbp, %rbx
	xorq	%r12, %r13
	orq	%r11, %rbx
	movq	%rax, -80(%rsp)
	movq	-32(%rsp), %rax
	xorq	%rdx, %rbx
	movq	%r13, -88(%rsp)
	movq	%rbx, %r13
	movq	%rbp, %rbx
	andq	%rax, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -72(%rsp)
	movq	%r10, %rbx
	notq	%rbx
	orq	%rax, %rbx
	xorq	%rbx, %rbp
	movq	%r10, %rbx
	orq	%rdx, %rbx
	andq	%r11, %rdx
	movq	64(%rsp), %r11
	xorq	%r10, %rdx
	movq	%rcx, %r10
	xorq	%rax, %rbx
	andq	%r9, %rcx
	movq	%rdx, -40(%rsp)
	notq	%r10
	movq	%r8, %rdx
	movq	%r10, %rax
	orq	%r9, %rdx
	movq	%r11, %r10
	movq	%rbx, -48(%rsp)
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	xorq	%r8, %rdx
	movq	%rdx, -32(%rsp)
	movq	56(%rsp), %rcx
	movq	40(%rsp), %r14
	movq	-56(%rsp), %r12
	movq	%rbp, -56(%rsp)
	movq	%rcx, %rdx
	movq	72(%rsp), %rbx
	andq	%rax, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	orq	%r11, %rdx
	andq	%r8, %r11
	xorq	%rax, %rdx
	movq	%r14, %rax
	xorq	%r11, %rcx
	movq	%rsi, %r11
	movq	%rdx, -16(%rsp)
	movq	(%rsp), %rdx
	andq	%r12, %rax
	movq	%rcx, %r8
	movq	%rax, %r9
	movq	(%rsp), %rax
	movq	-8(%rsp), %rcx
	movq	%r8, -8(%rsp)
	notq	%rdx
	xorq	%rdi, %r9
	orq	%rdx, %r11
	orq	%r12, %rax
	xorq	%r11, %r12
	movq	%rsi, %r11
	xorq	%r14, %rax
	andq	%rdi, %r11
	movq	%r12, (%rsp)
	xorq	%rdx, %r11
	movq	%r14, %rdx
	movq	80(%rsp), %r14
	orq	%rdi, %rdx
	movq	%r11, 8(%rsp)
	movq	48(%rsp), %rdi
	movq	%rdx, %r11
	xorq	%rsi, %r11
	movq	-112(%rsp), %rsi
	movq	%r11, 16(%rsp)
	movq	%rcx, %r11
	notq	%rsi
	movq	%rsi, %rdx
	andq	%rsi, %r11
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	xorq	%rcx, %rdi
	andq	-112(%rsp), %r14
	movq	%r13, -112(%rsp)
	xorq	%r14, %rbx
	movq	%rdi, 24(%rsp)
	movq	-96(%rsp), %r14
	movq	%rbx, %rcx
	movq	%r13, %rbx
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	xorq	-72(%rsp), %r14
	xorq	-32(%rsp), %r14
	xorq	%r9, %rbx
	movq	%rcx, 32(%rsp)
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%rax, %r14
	xorq	%r15, %r13
	xorq	%rsi, %r14
	xorq	%r10, %rbx
	xorq	%r12, %r13
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%r11, %rbx
	xorq	%rdx, %r13
	xorq	-104(%rsp), %rbx
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rbp, %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	rolq	%rcx
	xorq	16(%rsp), %rdi
	rolq	%r8
	xorq	%r14, %rcx
	movq	-104(%rsp), %r14
	movq	%r8, %rbp
	movq	%r13, %r8
	rolq	%r8
	xorq	%rdi, %rbp
	rolq	%rdi
	xorq	%rbx, %r8
	rolq	%rbx
	xorq	%r13, %rdi
	movq	-112(%rsp), %r13
	xorq	%r12, %rbx
	xorq	%rbp, %r14
	xorq	%rbp, %r10
	xorq	%rbp, %r9
	rolq	$3, %r10
	rorq	$23, %r9
	xorq	%rbp, %r13
	xorq	%rbp, %r11
	movq	%r10, 48(%rsp)
	movq	-72(%rsp), %r10
	xorq	%r8, %rax
	xorq	%r8, %rsi
	movq	%r9, 56(%rsp)
	movq	(%rsp), %r12
	rolq	$18, %r11
	xorq	%rcx, %rdx
	movq	-96(%rsp), %r9
	rorq	$28, %r13
	xorq	%r8, %r10
	rorq	$19, %rax
	movq	%r10, %rbp
	movq	-32(%rsp), %r10
	xorq	%rcx, %r12
	movq	%r11, 64(%rsp)
	rolq	$15, %r12
	xorq	%r8, %r9
	movq	-88(%rsp), %r11
	rorq	$20, %rbp
	rolq	%r9
	xorq	%r8, %r10
	movq	%r13, 40(%rsp)
	movq	-24(%rsp), %r13
	movq	%r9, 72(%rsp)
	movq	%r10, %r9
	movq	%rsi, %r10
	xorq	%rdi, %r11
	rolq	$10, %r9
	movq	%rax, -72(%rsp)
	movq	%r15, %rax
	rolq	$2, %r10
	movq	%r9, 80(%rsp)
	movq	-56(%rsp), %r9
	xorq	%rcx, %rax
	xorq	%rcx, %r13
	movq	%r12, -56(%rsp)
	movq	-48(%rsp), %r12
	rorq	$21, %r13
	rorq	$3, %rdx
	xorq	%rcx, %r9
	movq	%r10, 88(%rsp)
	movq	%r11, %rcx
	movq	%rax, %r10
	xorq	%rdi, %r12
	rolq	$6, %r9
	movq	16(%rsp), %r15
	movq	%rbp, %rax
	rolq	$28, %rcx
	movq	%r12, %rsi
	rorq	$2, %r10
	movq	8(%rsp), %r12
	rorq	$9, %rsi
	xorq	%rbx, %r15
	orq	%r13, %rax
	movq	-80(%rsp), %r8
	movq	%rsi, -112(%rsp)
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r12
	movq	-40(%rsp), %r11
	rolq	$21, %r12
	xorq	%rbx, %r8
	movq	%r10, 96(%rsp)
	xorq	%rbx, %rsi
	movq	-16(%rsp), %r10
	rolq	$27, %r8
	rorq	$25, %rsi
	xorq	%rbx, %r11
	xorq	32(%rsp), %rbx
	movq	%rsi, -8(%rsp)
	movq	%r15, %rsi
	movq	%rax, %r15
	rolq	$14, %rbx
	rolq	$20, %r11
	xorq	%r14, %r15
	xorq	%rdi, %r10
	xorq	24(%rsp), %rdi
	movabsq	$-9223372036854743038, %rax
	rolq	$25, %r10
	rorq	$8, %rdi
	xorq	%r15, %rax
	movq	%r13, %r15
	rolq	$8, %rsi
	notq	%r15
	movq	%rax, -104(%rsp)
	movq	%r12, %rax
	orq	%r12, %r15
	andq	%rbx, %rax
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%rax, %r15
	movq	-72(%rsp), %rax
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	orq	%rbx, %r13
	xorq	%rbx, %r14
	movq	%r15, -88(%rsp)
	movq	88(%rsp), %r15
	xorq	%r12, %r13
	movq	48(%rsp), %r12
	movq	%r13, -80(%rsp)
	movq	%r12, %rbx
	orq	%r11, %rbx
	movq	%rbx, %rbp
	movq	%r12, %rbx
	xorq	%rcx, %rbp
	andq	%rax, %rbx
	movq	%rbp, %r13
	movq	%rbx, %rbp
	movq	%rdx, %rbx
	notq	%rbx
	xorq	%r11, %rbp
	orq	%rax, %rbx
	movq	%rbp, -72(%rsp)
	xorq	%rbx, %r12
	movq	%rdx, %rbx
	orq	%rcx, %rbx
	andq	%r11, %rcx
	xorq	%rax, %rbx
	movq	%rcx, %rax
	movq	72(%rsp), %rcx
	xorq	%rdx, %rax
	movq	%rsi, %rdx
	andq	%r10, %rsi
	movq	%rbx, -48(%rsp)
	notq	%rdx
	movq	%rax, -40(%rsp)
	movq	%rcx, %rbp
	movq	80(%rsp), %rbx
	movq	%rdx, %rax
	movq	%r9, %rdx
	orq	%r10, %rdx
	xorq	%rdx, %rbp
	movq	%rsi, %rdx
	movq	64(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rcx, %rsi
	movq	%rdx, %r11
	movq	-56(%rsp), %rdx
	movq	%rdi, %rcx
	movq	%rsi, %r9
	movq	40(%rsp), %rsi
	xorq	%rax, %r11
	notq	%rdx
	movq	%r11, -16(%rsp)
	movq	96(%rsp), %r11
	movq	%rsi, %rax
	orq	%rdx, %rcx
	andq	%rbx, %rax
	movq	%rax, %r10
	movq	-56(%rsp), %rax
	movq	%r12, -56(%rsp)
	xorq	%r8, %r10
	orq	%rbx, %rax
	xorq	%rcx, %rbx
	movq	%rdi, %rcx
	xorq	%rsi, %rax
	orq	%r8, %rsi
	andq	%r8, %rcx
	movq	%rsi, %r8
	xorq	%rdx, %rcx
	movq	-8(%rsp), %rsi
	movq	-112(%rsp), %rdx
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	movq	%rcx, 8(%rsp)
	notq	%rdx
	movq	%r8, 16(%rsp)
	movq	%rsi, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%rsi, %rcx
	xorq	%r11, %r8
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%r15, %rdx
	xorq	%rsi, %rdx
	movq	%r15, %rsi
	orq	%r11, %rsi
	andq	-112(%rsp), %r11
	movq	%r13, -112(%rsp)
	xorq	%rsi, %rdi
	xorq	%r11, %r15
	movq	-72(%rsp), %rsi
	movq	%r13, %r11
	xorq	-32(%rsp), %rsi
	movq	-88(%rsp), %r13
	movq	%r15, 32(%rsp)
	xorq	%rbp, %r11
	movq	%rsi, %r15
	xorq	%r10, %r11
	xorq	-104(%rsp), %r11
	xorq	%rax, %r15
	xorq	%rdx, %r13
	xorq	%r8, %r11
	xorq	%rcx, %r15
	xorq	%r12, %r13
	xorq	-96(%rsp), %r15
	xorq	-24(%rsp), %r13
	xorq	%rbx, %r13
	movq	%rbx, (%rsp)
	movq	-16(%rsp), %rbx
	movq	-80(%rsp), %rsi
	xorq	-48(%rsp), %rsi
	movq	%rdi, 24(%rsp)
	xorq	%rsi, %rbx
	movq	-40(%rsp), %rsi
	xorq	8(%rsp), %rbx
	movq	%r9, -8(%rsp)
	xorq	%rdi, %rbx
	movq	%r15, %rdi
	xorq	%r14, %rsi
	rolq	%rdi
	xorq	%r9, %rsi
	movq	%rdi, %r12
	xorq	16(%rsp), %rsi
	movq	%r13, %rdi
	xorq	32(%rsp), %rsi
	movq	%rbx, %r9
	rolq	%rdi
	xorq	%rsi, %r12
	rolq	%r9
	xorq	%r11, %rdi
	rolq	%rsi
	xorq	%r15, %r9
	xorq	%r13, %rsi
	rolq	%r11
	xorq	%r12, %r8
	movq	-112(%rsp), %r13
	rolq	$18, %r8
	xorq	%r12, %r10
	xorq	%rbx, %r11
	xorq	%rdi, %rcx
	movq	%r8, 64(%rsp)
	movq	-96(%rsp), %r8
	xorq	%r12, %r13
	xorq	%r12, %rbp
	rorq	$23, %r10
	rorq	$28, %r13
	movq	-104(%rsp), %rbx
	xorq	%rdi, %rax
	movq	%r10, 56(%rsp)
	rolq	$3, %rbp
	xorq	%rdi, %r8
	rorq	$19, %rax
	movq	-88(%rsp), %r10
	movq	%r13, 40(%rsp)
	movq	%r8, %r15
	movq	%rcx, %r13
	xorq	%r12, %rbx
	rolq	%r15
	movq	-24(%rsp), %r12
	movq	-32(%rsp), %r8
	xorq	%r9, %r10
	rolq	$2, %r13
	movq	%r15, 72(%rsp)
	movq	-72(%rsp), %r15
	movq	%r13, 80(%rsp)
	movq	%r10, %r13
	xorq	%r9, %r12
	xorq	%rdi, %r8
	rorq	$2, %r13
	xorq	%rdi, %r15
	movq	-56(%rsp), %rcx
	movq	%r14, %rdi
	movq	%r13, 88(%rsp)
	movq	%r12, %r13
	movq	(%rsp), %r12
	movq	%rbp, 48(%rsp)
	movq	%r15, %rbp
	movq	%r8, %r15
	xorq	%r9, %rcx
	rolq	$10, %r15
	xorq	%r9, %r12
	xorq	%rdx, %r9
	movq	-80(%rsp), %rdx
	movq	%r15, -32(%rsp)
	rorq	$20, %rbp
	movq	%rcx, %r15
	movq	-48(%rsp), %rcx
	rorq	$21, %r13
	xorq	%rsi, %rdx
	rorq	$3, %r9
	movq	%rbp, %r14
	rolq	$6, %r15
	rolq	$15, %r12
	rolq	$28, %rdx
	xorq	%rsi, %rcx
	movq	%r15, -56(%rsp)
	orq	%r13, %r14
	movq	%rcx, %r10
	movq	%r12, (%rsp)
	xorq	%rbx, %r14
	xorq	%r11, %rdi
	rorq	$9, %r10
	rolq	$27, %rdi
	movabsq	$-9223372036854775680, %r15
	movq	%r10, 96(%rsp)
	movq	-8(%rsp), %rcx
	xorq	%r14, %r15
	movq	%r13, %r14
	movq	8(%rsp), %r12
	movq	-40(%rsp), %r10
	notq	%r14
	xorq	%r11, %rcx
	movq	-16(%rsp), %r8
	xorq	%rsi, %r12
	rorq	$25, %rcx
	xorq	%r11, %r10
	rolq	$21, %r12
	movq	%rcx, -8(%rsp)
	rolq	$20, %r10
	xorq	%rsi, %r8
	movq	16(%rsp), %rcx
	orq	%r12, %r14
	xorq	24(%rsp), %rsi
	rolq	$25, %r8
	xorq	%rbp, %r14
	rorq	$8, %rsi
	xorq	%r11, %rcx
	xorq	32(%rsp), %r11
	movq	%r14, -112(%rsp)
	movq	%r12, %r14
	rolq	$14, %r11
	rolq	$8, %rcx
	andq	%r11, %r14
	xorq	%r13, %r14
	movq	88(%rsp), %r13
	movq	%r14, -104(%rsp)
	movq	%rbx, %r14
	andq	%rbp, %rbx
	movq	48(%rsp), %rbp
	orq	%r11, %r14
	xorq	%r12, %r14
	movq	%rbx, %r12
	movq	-56(%rsp), %rbx
	xorq	%r11, %r12
	movq	%rbp, %r11
	movq	%r14, -96(%rsp)
	orq	%r10, %r11
	movq	%r12, -88(%rsp)
	movq	%r9, %r12
	xorq	%rdx, %r11
	notq	%r12
	movq	%r11, -80(%rsp)
	movq	%rbp, %r11
	andq	%rax, %r11
	xorq	%r10, %r11
	movq	%r11, -72(%rsp)
	movq	%r12, %r11
	movq	%r9, %r12
	orq	%rdx, %r12
	andq	%r10, %rdx
	orq	%rax, %r11
	xorq	%rax, %r12
	xorq	%r9, %rdx
	movq	%rcx, %rax
	movq	72(%rsp), %r9
	andq	%r8, %rcx
	movq	%r12, -48(%rsp)
	movq	%rbx, %r12
	notq	%rax
	xorq	%rcx, %r12
	movq	%rdx, -40(%rsp)
	movq	64(%rsp), %rcx
	movq	%rbx, %rdx
	orq	%r8, %rdx
	movq	%r9, %r10
	xorq	%r11, %rbp
	movq	40(%rsp), %r11
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	andq	%rax, %rdx
	xorq	%r8, %rdx
	movq	%rcx, %r8
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	movq	%rsi, %rcx
	orq	%r9, %rdx
	andq	%rbx, %r9
	movq	-32(%rsp), %rbx
	xorq	%rax, %rdx
	movq	(%rsp), %rax
	xorq	%r9, %r8
	movq	%r11, %r9
	movq	%rdx, -16(%rsp)
	andq	%rbx, %r9
	movq	%rax, %rdx
	orq	%rbx, %rax
	xorq	%rdi, %r9
	notq	%rdx
	xorq	%r11, %rax
	orq	%rdx, %rcx
	xorq	%rcx, %rbx
	movq	-8(%rsp), %rcx
	movq	%rbx, (%rsp)
	movq	%rsi, %rbx
	andq	%rdi, %rbx
	xorq	%rdx, %rbx
	movq	%r11, %rdx
	movq	%rcx, %r11
	movq	%rbx, 8(%rsp)
	movq	96(%rsp), %rbx
	orq	%rdi, %rdx
	xorq	%rsi, %rdx
	movq	56(%rsp), %rdi
	movq	%rbx, %rsi
	movq	%rdx, 16(%rsp)
	movq	80(%rsp), %r14
	notq	%rsi
	movq	%rbp, -56(%rsp)
	movq	%rsi, %rdx
	andq	%rsi, %r11
	movq	%rdi, %rsi
	movq	%r12, -32(%rsp)
	orq	%rcx, %rsi
	xorq	%r13, %r11
	movq	%r8, -8(%rsp)
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%r14, %rdx
	xorq	%rcx, %rdx
	movq	%r14, %rcx
	orq	%r13, %rcx
	andq	%rbx, %r13
	movq	-80(%rsp), %rbx
	xorq	%r13, %r14
	movq	-112(%rsp), %r13
	xorq	-72(%rsp), %r13
	xorq	%rcx, %rdi
	movq	%r14, 32(%rsp)
	movq	%r13, %r14
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	xorq	%r12, %r14
	movq	%rdi, 24(%rsp)
	xorq	%r9, %rbx
	xorq	%rbp, %r13
	movq	-96(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%rax, %r14
	movq	%rbp, %r12
	movq	8(%rsp), %rbp
	xorq	%rsi, %r14
	xorq	-104(%rsp), %r13
	xorq	(%rsp), %r13
	xorq	%r10, %rbx
	xorq	%rbp, %r12
	movq	-16(%rsp), %rbp
	xorq	%rdx, %r13
	xorq	%r11, %rbx
	xorq	%r15, %rbx
	xorq	%rbp, %r12
	movq	-88(%rsp), %rbp
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	xorq	32(%rsp), %rdi
	xorq	%rbp, %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	16(%rsp), %rdi
	rolq	%rcx
	rolq	%r8
	xorq	%r14, %rcx
	movq	%r15, %r14
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%r8
	xorq	%rbx, %r8
	rolq	%rdi
	xorq	%rbp, %r10
	xorq	%rbp, %r9
	rolq	$3, %r10
	rolq	%rbx
	xorq	%r13, %rdi
	xorq	%rbp, %r11
	movq	%r10, 48(%rsp)
	movq	-112(%rsp), %r10
	xorq	%r12, %rbx
	xorq	%r8, %rsi
	movq	-80(%rsp), %r12
	rorq	$23, %r9
	rolq	$18, %r11
	xorq	%rbp, %r14
	xorq	%r8, %r10
	movq	%r9, 56(%rsp)
	movq	-32(%rsp), %r9
	xorq	%r8, %rax
	xorq	%rbp, %r12
	rolq	%r10
	movq	%r11, 64(%rsp)
	xorq	%rcx, %rdx
	movq	%r10, 72(%rsp)
	movq	%r12, %r13
	movq	-72(%rsp), %r10
	xorq	%r8, %r9
	movq	-104(%rsp), %r12
	rorq	$28, %r13
	rolq	$10, %r9
	xorq	%r8, %r10
	movq	%r13, 40(%rsp)
	rorq	$19, %rax
	xorq	%rcx, %r12
	movq	%r10, %rbp
	movq	%rsi, %r10
	movq	%r9, 80(%rsp)
	rolq	$2, %r10
	movq	%r12, %r11
	rorq	$20, %rbp
	rorq	$2, %r11
	movq	%r10, 88(%rsp)
	movq	%r11, 96(%rsp)
	movq	(%rsp), %r15
	movq	-56(%rsp), %r9
	movq	-24(%rsp), %r13
	xorq	%rcx, %r15
	movq	-88(%rsp), %r8
	movq	-40(%rsp), %r11
	movq	%r15, %r12
	xorq	%rcx, %r9
	xorq	%rcx, %r13
	movq	16(%rsp), %r15
	rolq	$15, %r12
	rolq	$6, %r9
	movq	-96(%rsp), %rcx
	movq	-16(%rsp), %r10
	movq	%r12, -56(%rsp)
	movq	-48(%rsp), %r12
	rorq	$21, %r13
	rorq	$3, %rdx
	xorq	%rbx, %r15
	xorq	%rbx, %r8
	xorq	%rbx, %r11
	xorq	%rdi, %rcx
	rolq	$20, %r11
	xorq	%rdi, %r12
	xorq	%rdi, %r10
	rolq	$27, %r8
	rolq	$25, %r10
	movq	%r12, %rsi
	movq	8(%rsp), %r12
	rolq	$28, %rcx
	rorq	$9, %rsi
	movq	%rsi, -112(%rsp)
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r12
	rolq	$21, %r12
	xorq	24(%rsp), %rdi
	xorq	%rbx, %rsi
	xorq	32(%rsp), %rbx
	rorq	$8, %rdi
	rorq	$25, %rsi
	rolq	$14, %rbx
	movq	%rsi, -8(%rsp)
	movq	%r15, %rsi
	movq	%rbp, %r15
	orq	%r13, %r15
	rolq	$8, %rsi
	xorq	%r14, %r15
	xorq	$32778, %r15
	movq	%r15, -104(%rsp)
	movq	%r13, %r15
	notq	%r15
	orq	%r12, %r15
	xorq	%rbp, %r15
	movq	%r15, -96(%rsp)
	movq	%r12, %r15
	andq	%rbx, %r15
	xorq	%r13, %r15
	movq	%r14, %r13
	andq	%rbp, %r14
	orq	%rbx, %r13
	xorq	%rbx, %r14
	movq	%r15, -88(%rsp)
	xorq	%r12, %r13
	movq	48(%rsp), %r12
	movq	%r13, -80(%rsp)
	movq	%r12, %rbx
	orq	%r11, %rbx
	movq	%rbx, %rbp
	movq	%r12, %rbx
	xorq	%rcx, %rbp
	andq	%rax, %rbx
	movq	%rbp, %r13
	movq	%rbx, %rbp
	movq	%rdx, %rbx
	notq	%rbx
	xorq	%r11, %rbp
	orq	%rax, %rbx
	movq	%rbp, -72(%rsp)
	xorq	%rbx, %r12
	movq	%rdx, %rbx
	orq	%rcx, %rbx
	andq	%r11, %rcx
	xorq	%rax, %rbx
	movq	%rcx, %rax
	movq	72(%rsp), %rcx
	xorq	%rdx, %rax
	movq	%r9, %rdx
	movq	%rbx, -48(%rsp)
	movq	80(%rsp), %rbx
	orq	%r10, %rdx
	movq	%rax, -40(%rsp)
	movq	%rcx, %rbp
	movq	%rsi, %rax
	andq	%r10, %rsi
	xorq	%rdx, %rbp
	notq	%rax
	movq	%rsi, %rdx
	movq	64(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rcx, %rsi
	movq	%rdx, %r10
	movq	-56(%rsp), %rdx
	movq	%rdi, %rcx
	movq	%rsi, %r9
	movq	40(%rsp), %rsi
	xorq	%rax, %r10
	notq	%rdx
	movq	%r10, -16(%rsp)
	movq	%rsi, %rax
	orq	%rdx, %rcx
	andq	%rbx, %rax
	movq	%rax, %r10
	movq	-56(%rsp), %rax
	movq	96(%rsp), %r11
	movq	%r12, -56(%rsp)
	xorq	%r8, %r10
	movq	88(%rsp), %r15
	orq	%rbx, %rax
	xorq	%rcx, %rbx
	movq	%rdi, %rcx
	xorq	%rsi, %rax
	andq	%r8, %rcx
	orq	%r8, %rsi
	movq	%rbx, (%rsp)
	xorq	%rdx, %rcx
	movq	%rsi, %r8
	movq	-112(%rsp), %rdx
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r8
	movq	56(%rsp), %rdi
	movq	%rcx, 8(%rsp)
	movq	%r8, 16(%rsp)
	notq	%rdx
	movq	%rsi, %r8
	andq	%rdx, %r8
	movq	%rdi, %rcx
	movq	%r9, -8(%rsp)
	xorq	%r11, %r8
	orq	%rsi, %rcx
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%r15, %rdx
	xorq	%rsi, %rdx
	movq	%r15, %rsi
	orq	%r11, %rsi
	andq	-112(%rsp), %r11
	movq	%r13, -112(%rsp)
	xorq	%r11, %r15
	movq	%r13, %r11
	movq	-88(%rsp), %r13
	xorq	%rsi, %rdi
	movq	-72(%rsp), %rsi
	xorq	-32(%rsp), %rsi
	movq	%r15, 32(%rsp)
	xorq	%rbp, %r11
	xorq	%rdx, %r13
	movq	%rsi, %r15
	movq	-80(%rsp), %rsi
	xorq	-48(%rsp), %rsi
	xorq	%r12, %r13
	xorq	-24(%rsp), %r13
	xorq	%rax, %r15
	movq	%rdi, 24(%rsp)
	xorq	%rbx, %r13
	movq	-16(%rsp), %rbx
	xorq	%rcx, %r15
	xorq	-96(%rsp), %r15
	xorq	%r10, %r11
	xorq	-104(%rsp), %r11
	xorq	%rsi, %rbx
	xorq	8(%rsp), %rbx
	movq	-40(%rsp), %rsi
	xorq	%r8, %r11
	xorq	%rdi, %rbx
	movq	%r15, %rdi
	rolq	%rdi
	xorq	%r14, %rsi
	movq	%rdi, %r12
	movq	%r13, %rdi
	xorq	%r9, %rsi
	movq	%rbx, %r9
	xorq	16(%rsp), %rsi
	rolq	%rdi
	xorq	32(%rsp), %rsi
	xorq	%rsi, %r12
	xorq	%r11, %rdi
	rolq	%r9
	rolq	%rsi
	xorq	%r12, %rbp
	xorq	%r12, %r10
	xorq	%r12, %r8
	xorq	%r13, %rsi
	movq	-112(%rsp), %r13
	rolq	$3, %rbp
	xorq	%r15, %r9
	rorq	$23, %r10
	rolq	$18, %r8
	movq	%rbp, 48(%rsp)
	xorq	%rdi, %rcx
	xorq	%r12, %r13
	rolq	%r11
	xorq	%rdi, %rax
	rorq	$28, %r13
	xorq	%rbx, %r11
	movq	-104(%rsp), %rbx
	rorq	$19, %rax
	movq	%r13, 40(%rsp)
	movq	%rcx, %r13
	movq	%r10, 56(%rsp)
	xorq	%r12, %rbx
	movq	-88(%rsp), %r10
	rolq	$2, %r13
	movq	-56(%rsp), %rcx
	movq	(%rsp), %r12
	movq	%r8, 64(%rsp)
	movq	-96(%rsp), %r8
	movq	%r13, 80(%rsp)
	xorq	%r9, %r10
	movq	-24(%rsp), %r13
	xorq	%r9, %rcx
	xorq	%r9, %r12
	xorq	%rdi, %r8
	movq	%r8, %r15
	movq	-32(%rsp), %r8
	xorq	%r9, %r13
	rolq	%r15
	rorq	$21, %r13
	movq	%r15, 72(%rsp)
	movq	-72(%rsp), %r15
	xorq	%rdi, %r8
	xorq	%rdi, %r15
	movq	%r14, %rdi
	movq	%r15, %rbp
	movq	%r8, %r15
	movq	%r10, %r8
	rolq	$10, %r15
	rorq	$20, %rbp
	movq	%r15, -32(%rsp)
	movq	%rcx, %r15
	movq	%r12, %rcx
	rorq	$2, %r8
	rolq	$6, %r15
	rolq	$15, %rcx
	movq	%rbp, %r14
	xorq	%r11, %rdi
	movq	%rcx, (%rsp)
	movq	-48(%rsp), %r12
	orq	%r13, %r14
	xorq	%rdx, %r9
	movq	%r15, -56(%rsp)
	movq	-8(%rsp), %rcx
	xorq	%rbx, %r14
	rorq	$3, %r9
	movq	16(%rsp), %r15
	xorq	%rsi, %r12
	movq	-80(%rsp), %rdx
	movq	%r8, 88(%rsp)
	xorq	%r11, %rcx
	movq	%r12, %r10
	movq	8(%rsp), %r12
	movq	-16(%rsp), %r8
	rorq	$25, %rcx
	xorq	%r11, %r15
	rorq	$9, %r10
	xorq	%rsi, %rdx
	movq	%rcx, -8(%rsp)
	movq	%r15, %rcx
	xorq	%rsi, %r12
	xorq	%rsi, %r8
	rolq	$21, %r12
	movq	%r10, 96(%rsp)
	movq	-40(%rsp), %r10
	movabsq	$-9223372034707292150, %r15
	rolq	$25, %r8
	xorq	%r14, %r15
	movq	%r13, %r14
	xorq	24(%rsp), %rsi
	rorq	$8, %rsi
	notq	%r14
	xorq	%r11, %r10
	xorq	32(%rsp), %r11
	rolq	$14, %r11
	orq	%r12, %r14
	rolq	$27, %rdi
	rolq	$20, %r10
	xorq	%rbp, %r14
	rolq	$28, %rdx
	movq	%r14, -112(%rsp)
	movq	%r12, %r14
	rolq	$8, %rcx
	andq	%r11, %r14
	xorq	%r13, %r14
	movq	%rbx, %r13
	orq	%r11, %r13
	movq	%r14, -104(%rsp)
	xorq	%r12, %r13
	andq	%rbp, %rbx
	movq	48(%rsp), %rbp
	movq	%rbx, %r12
	movq	%r13, -96(%rsp)
	xorq	%r11, %r12
	movq	%rbp, %r11
	orq	%r10, %r11
	movq	%r12, -88(%rsp)
	xorq	%rdx, %r11
	movq	%r11, -80(%rsp)
	movq	%rbp, %r11
	andq	%rax, %r11
	xorq	%r10, %r11
	movq	%r11, -72(%rsp)
	movq	%r9, %r11
	notq	%r11
	orq	%rax, %r11
	xorq	%r11, %rbp
	movq	%r9, %r11
	orq	%rdx, %r11
	andq	%r10, %rdx
	xorq	%rax, %r11
	xorq	%r9, %rdx
	movq	%r11, -48(%rsp)
	movq	-56(%rsp), %rbx
	movq	72(%rsp), %r9
	movq	-32(%rsp), %r12
	movq	%rdx, -40(%rsp)
	movq	%rcx, %rdx
	notq	%rdx
	andq	%r8, %rcx
	movq	%rbx, %r13
	movq	40(%rsp), %r14
	xorq	%rcx, %r13
	movq	%rdx, %rax
	movq	64(%rsp), %rcx
	movq	%rbx, %rdx
	orq	%r8, %rdx
	movq	%r9, %r10
	movq	%r13, -32(%rsp)
	xorq	%rdx, %r10
	movq	%rcx, %rdx
	movq	%rbp, -56(%rsp)
	andq	%rax, %rdx
	xorq	%r8, %rdx
	movq	%rcx, %r8
	movq	%rdx, -24(%rsp)
	movq	%rcx, %rdx
	movq	-8(%rsp), %rcx
	orq	%r9, %rdx
	andq	%rbx, %r9
	xorq	%rax, %rdx
	movq	(%rsp), %rax
	xorq	%r9, %r8
	movq	%r14, %r9
	movq	%rdx, -16(%rsp)
	andq	%r12, %r9
	movq	%rcx, %r11
	movq	%rax, %rdx
	orq	%r12, %rax
	xorq	%rdi, %r9
	xorq	%r14, %rax
	notq	%rdx
	movq	%rax, (%rsp)
	movq	%rsi, %rax
	orq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rsi, %rax
	andq	%rdi, %rax
	movq	%r12, 8(%rsp)
	xorq	%rdx, %rax
	movq	%r14, %rdx
	movq	88(%rsp), %r14
	orq	%rdi, %rdx
	movq	%rax, 16(%rsp)
	movq	96(%rsp), %rax
	movq	%rdx, %rbx
	movq	56(%rsp), %rdi
	xorq	%rsi, %rbx
	movq	%rax, %rsi
	notq	%rsi
	movq	%rbx, 24(%rsp)
	movq	80(%rsp), %rbx
	andq	%rsi, %r11
	movq	%rsi, %rdx
	movq	%rdi, %rsi
	orq	%rcx, %rsi
	xorq	%r14, %r11
	xorq	%rdx, %rsi
	movq	%rdi, %rdx
	andq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rbx, %rcx
	orq	%r14, %rcx
	andq	%rax, %r14
	xorq	%r14, %rbx
	movq	-112(%rsp), %r14
	xorq	-72(%rsp), %r14
	xorq	%rcx, %rdi
	xorq	%r13, %r14
	movq	%rbp, %r13
	movq	-24(%rsp), %rbp
	movq	%rdi, 32(%rsp)
	movq	%rbx, %rcx
	xorq	(%rsp), %r14
	movq	-80(%rsp), %rbx
	xorq	%rbp, %r13
	movq	-104(%rsp), %rbp
	xorq	%rsi, %r14
	xorq	%r9, %rbx
	xorq	%rbp, %r13
	movq	-96(%rsp), %rbp
	xorq	-48(%rsp), %rbp
	xorq	%r10, %rbx
	xorq	%r12, %r13
	movq	16(%rsp), %r12
	xorq	%r11, %rbx
	xorq	%rdx, %r13
	xorq	%r15, %rbx
	xorq	%rbp, %r12
	xorq	-16(%rsp), %r12
	xorq	%rdi, %r12
	movq	-40(%rsp), %rdi
	movq	%rcx, 40(%rsp)
	movq	%r8, -8(%rsp)
	movq	-72(%rsp), %rax
	xorq	%rcx, %rdi
	xorq	-88(%rsp), %rdi
	movq	%r12, %rcx
	xorq	%r8, %rdi
	movq	%r14, %r8
	xorq	24(%rsp), %rdi
	rolq	%r8
	movq	%r8, %rbp
	movq	%r13, %r8
	xorq	%rdi, %rbp
	rolq	%r8
	xorq	%rbp, %r9
	rolq	%rdi
	xorq	%rbp, %r10
	xorq	%rbx, %r8
	rorq	$23, %r9
	xorq	%r13, %rdi
	rolq	%rcx
	movq	-104(%rsp), %r13
	movq	%r9, 64(%rsp)
	movq	-32(%rsp), %r9
	xorq	%r14, %rcx
	movq	%r15, %r14
	rolq	$3, %r10
	xorq	%rcx, %r13
	movq	-80(%rsp), %r15
	xorq	%r8, %rax
	xorq	%r8, %r9
	movq	%r10, 56(%rsp)
	movq	-112(%rsp), %r10
	xorq	%rbp, %r14
	rolq	$10, %r9
	rorq	$2, %r13
	xorq	%rbp, %r15
	xorq	%rbp, %r11
	xorq	%r8, %r10
	movq	%r9, 88(%rsp)
	rolq	%rbx
	movq	-56(%rsp), %r9
	movq	%r13, 96(%rsp)
	movq	%rax, %rbp
	movq	-24(%rsp), %r13
	xorq	%r12, %rbx
	movq	(%rsp), %rax
	xorq	%r8, %rsi
	rolq	%r10
	movq	8(%rsp), %r12
	xorq	%rcx, %r9
	movq	%r10, 80(%rsp)
	xorq	%rcx, %r13
	movq	%rsi, %r10
	rorq	$20, %rbp
	xorq	%r8, %rax
	rolq	$6, %r9
	movq	-88(%rsp), %r8
	rorq	$28, %r15
	rolq	$18, %r11
	rorq	$19, %rax
	rolq	$2, %r10
	movq	%r11, 72(%rsp)
	movq	-96(%rsp), %r11
	rorq	$21, %r13
	xorq	%rcx, %r12
	movq	%r10, (%rsp)
	xorq	%rcx, %rdx
	rolq	$15, %r12
	movq	-16(%rsp), %r10
	xorq	%rdi, %r11
	xorq	%rbx, %r8
	movq	%r12, -56(%rsp)
	rorq	$3, %rdx
	movq	%r11, %rcx
	rolq	$27, %r8
	movq	-48(%rsp), %r12
	xorq	%rdi, %r10
	movq	%rax, -72(%rsp)
	movq	%rbp, %rax
	movq	-40(%rsp), %r11
	rolq	$25, %r10
	orq	%r13, %rax
	rolq	$28, %rcx
	xorq	%rdi, %r12
	movq	%r15, 48(%rsp)
	movq	%r12, %rsi
	movq	16(%rsp), %r12
	xorq	%rbx, %r11
	rorq	$9, %rsi
	rolq	$20, %r11
	movq	%rsi, -112(%rsp)
	movq	-8(%rsp), %rsi
	xorq	%rdi, %r12
	xorq	32(%rsp), %rdi
	rolq	$21, %r12
	xorq	%rbx, %rsi
	rorq	$8, %rdi
	rorq	$25, %rsi
	movq	%rsi, -8(%rsp)
	movq	24(%rsp), %r15
	xorq	%rbx, %r15
	xorq	40(%rsp), %rbx
	movq	%r15, %rsi
	movq	%rax, %r15
	rolq	$14, %rbx
	movabsq	$-9223372034707259263, %rax
	xorq	%r14, %r15
	rolq	$8, %rsi
	xorq	%r15, %rax
	movq	%rax, -104(%rsp)
	movq	%r13, %rax
	notq	%rax
	movq	%rax, %r15
	orq	%r12, %r15
	movq	%r15, %rax
	movq	%r12, %r15
	andq	%rbx, %r15
	xorq	%rbp, %rax
	xorq	%r13, %r15
	movq	%r14, %r13
	movq	%rax, -96(%rsp)
	movq	-72(%rsp), %rax
	orq	%rbx, %r13
	andq	%rbp, %r14
	movq	%r15, -88(%rsp)
	movq	(%rsp), %r15
	xorq	%r12, %r13
	movq	56(%rsp), %r12
	xorq	%rbx, %r14
	movq	%r13, -80(%rsp)
	movq	%r12, %rbx
	orq	%r11, %rbx
	movq	%rbx, %rbp
	movq	%r12, %rbx
	xorq	%rcx, %rbp
	andq	%rax, %rbx
	movq	%rbp, %r13
	movq	%rbx, %rbp
	movq	%rdx, %rbx
	notq	%rbx
	xorq	%r11, %rbp
	orq	%rax, %rbx
	movq	%rbp, -72(%rsp)
	xorq	%rbx, %r12
	movq	%rdx, %rbx
	orq	%rcx, %rbx
	andq	%r11, %rcx
	movq	96(%rsp), %r11
	xorq	%rax, %rbx
	movq	%rcx, %rax
	movq	80(%rsp), %rcx
	xorq	%rdx, %rax
	movq	%rsi, %rdx
	andq	%r10, %rsi
	movq	%rbx, -48(%rsp)
	notq	%rdx
	movq	%rax, -40(%rsp)
	movq	%rcx, %rbp
	movq	88(%rsp), %rbx
	movq	%rdx, %rax
	movq	%r9, %rdx
	orq	%r10, %rdx
	xorq	%rdx, %rbp
	movq	%rsi, %rdx
	movq	72(%rsp), %rsi
	xorq	%r9, %rdx
	movq	%rdx, -32(%rsp)
	movq	%rsi, %rdx
	andq	%rax, %rdx
	xorq	%r10, %rdx
	movq	%rdx, -24(%rsp)
	movq	%rsi, %rdx
	orq	%rcx, %rdx
	andq	%r9, %rcx
	xorq	%rcx, %rsi
	movq	%rdx, %r10
	movq	-56(%rsp), %rdx
	movq	%rdi, %rcx
	movq	%rsi, %r9
	movq	48(%rsp), %rsi
	xorq	%rax, %r10
	notq	%rdx
	movq	%r10, -16(%rsp)
	movq	%rsi, %rax
	orq	%rdx, %rcx
	andq	%rbx, %rax
	movq	%rax, %r10
	movq	-56(%rsp), %rax
	xorq	%r8, %r10
	orq	%rbx, %rax
	xorq	%rcx, %rbx
	movq	%rdi, %rcx
	andq	%r8, %rcx
	xorq	%rsi, %rax
	xorq	%rdx, %rcx
	orq	%r8, %rsi
	movq	-112(%rsp), %rdx
	movq	%rsi, %r8
	movq	-8(%rsp), %rsi
	movq	%rcx, 8(%rsp)
	xorq	%rdi, %r8
	movq	64(%rsp), %rdi
	notq	%rdx
	movq	%r8, 16(%rsp)
	movq	%rsi, %r8
	movq	%rdi, %rcx
	andq	%rdx, %r8
	orq	%rsi, %rcx
	xorq	%r11, %r8
	xorq	%rdx, %rcx
	movq	%rdi, %rdx
	andq	%r15, %rdx
	xorq	%rsi, %rdx
	movq	%r15, %rsi
	orq	%r11, %rsi
	andq	-112(%rsp), %r11
	movq	%r13, -112(%rsp)
	xorq	%r11, %r15
	movq	%r13, %r11
	xorq	%rsi, %rdi
	movq	-72(%rsp), %rsi
	xorq	%rbp, %r11
	movq	%r15, 32(%rsp)
	xorq	%r10, %r11
	xorq	-104(%rsp), %r11
	xorq	-32(%rsp), %rsi
	movq	%rbx, (%rsp)
	movq	-88(%rsp), %r13
	movq	%rsi, %r15
	movq	-80(%rsp), %rsi
	xorq	%r8, %r11
	xorq	-48(%rsp), %rsi
	xorq	%rax, %r15
	movq	%rdi, 24(%rsp)
	xorq	%rdx, %r13
	xorq	%rcx, %r15
	xorq	-96(%rsp), %r15
	movq	%r9, -8(%rsp)
	xorq	%r12, %r13
	xorq	-24(%rsp), %r13
	movq	%r12, -56(%rsp)
	xorq	%rbx, %r13
	movq	-16(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	-40(%rsp), %rsi
	xorq	8(%rsp), %rbx
	xorq	%rdi, %rbx
	movq	%r15, %rdi
	xorq	%r14, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %r9
	xorq	16(%rsp), %rsi
	xorq	32(%rsp), %rsi
	rolq	%rdi
	rolq	%r9
	movq	%rdi, %r12
	movq	%r13, %rdi
	xorq	%r15, %r9
	movq	-72(%rsp), %r15
	xorq	%rsi, %r12
	rolq	%rdi
	xorq	%r11, %rdi
	xorq	%r12, %rbp
	rolq	%rsi
	xorq	%r12, %r8
	xorq	%r13, %rsi
	xorq	%rdi, %r15
	rolq	$3, %rbp
	movq	-112(%rsp), %r13
	rolq	%r11
	xorq	%rdi, %rcx
	rolq	$18, %r8
	xorq	%rdi, %rax
	xorq	%rbx, %r11
	movq	-104(%rsp), %rbx
	movq	%rbp, -104(%rsp)
	movq	%r15, %rbp
	movq	-32(%rsp), %r15
	xorq	%r12, %r13
	rorq	$19, %rax
	xorq	%r12, %r10
	rorq	$28, %r13
	movq	%r8, 56(%rsp)
	xorq	%r12, %rbx
	rorq	$20, %rbp
	xorq	%rdi, %r15
	movq	%r13, 40(%rsp)
	movq	-96(%rsp), %r8
	rorq	$23, %r10
	movq	%r15, %r13
	movq	%rcx, %r15
	movq	-88(%rsp), %rcx
	movq	%rax, -32(%rsp)
	rolq	$2, %r15
	movq	-24(%rsp), %rax
	xorq	%rdi, %r8
	rolq	$10, %r13
	xorq	%r9, %rcx
	movq	%r15, 72(%rsp)
	rolq	%r8
	movq	%rcx, %r15
	movq	-56(%rsp), %rcx
	movq	%r10, 48(%rsp)
	rorq	$2, %r15
	movq	%r8, -96(%rsp)
	xorq	%r9, %rcx
	movq	%r13, 64(%rsp)
	rolq	$6, %rcx
	xorq	%r9, %rax
	xorq	%r11, %r14
	movq	%rcx, 80(%rsp)
	movq	%rax, %r13
	movq	(%rsp), %rax
	movq	%r14, %rdi
	movq	-48(%rsp), %rcx
	movq	-40(%rsp), %r10
	rorq	$21, %r13
	rolq	$27, %rdi
	xorq	%r9, %rax
	movq	8(%rsp), %r12
	movq	-16(%rsp), %r8
	xorq	%rdx, %r9
	xorq	%rsi, %rcx
	rolq	$15, %rax
	movq	-80(%rsp), %rdx
	xorq	%r11, %r10
	rorq	$9, %rcx
	movq	%rax, -24(%rsp)
	xorq	%rsi, %r12
	xorq	%rsi, %r8
	movq	%rcx, (%rsp)
	movq	-8(%rsp), %rcx
	rolq	$21, %r12
	xorq	%rsi, %rdx
	rorq	$3, %r9
	xorq	24(%rsp), %rsi
	rolq	$25, %r8
	movabsq	$-9223372036854742912, %rax
	rorq	$8, %rsi
	xorq	%r11, %rcx
	rolq	$20, %r10
	movq	%rcx, %r14
	rolq	$28, %rdx
	rorq	$25, %r14
	movq	%r14, -40(%rsp)
	movq	16(%rsp), %r14
	xorq	%r11, %r14
	xorq	32(%rsp), %r11
	movq	%r14, %rcx
	movq	%rbp, %r14
	rolq	$14, %r11
	orq	%r13, %r14
	rolq	$8, %rcx
	xorq	%rbx, %r14
	xorq	%r14, %rax
	movq	%r13, %r14
	notq	%r14
	movq	%rax, -112(%rsp)
	movq	%rbx, %rax
	orq	%r12, %r14
	xorq	%rbp, %r14
	movq	%r14, -88(%rsp)
	movq	%r12, %r14
	andq	%r11, %r14
	andq	%rbp, %rbx
	orq	%r11, %rax
	movq	%r9, %rbp
	xorq	%r12, %rax
	movq	%rbx, %r12
	movq	-104(%rsp), %rbx
	notq	%rbp
	xorq	%r11, %r12
	movq	%rax, -72(%rsp)
	movq	-32(%rsp), %rax
	xorq	%r13, %r14
	movq	%rbx, %r11
	movq	%r14, -80(%rsp)
	movq	64(%rsp), %r13
	orq	%r10, %r11
	movq	%r12, -56(%rsp)
	xorq	%rdx, %r11
	movq	%r11, -104(%rsp)
	movq	%rbx, %r11
	andq	%rax, %r11
	xorq	%r10, %r11
	movq	%r11, -48(%rsp)
	movq	%rbp, %r11
	movq	%r9, %rbp
	orq	%rdx, %rbp
	andq	%r10, %rdx
	movq	-96(%rsp), %r10
	orq	%rax, %r11
	xorq	%rax, %rbp
	xorq	%r9, %rdx
	movq	80(%rsp), %r9
	xorq	%r11, %rbx
	movq	%rbp, 32(%rsp)
	movq	56(%rsp), %rbp
	movq	%rdx, -32(%rsp)
	movq	%r9, %r14
	movq	%rcx, %rdx
	andq	%r8, %rcx
	xorq	%rcx, %r14
	notq	%rdx
	movq	%rbp, %rcx
	movq	%r9, %rax
	andq	%rdx, %rcx
	orq	%r8, %rax
	movq	40(%rsp), %r11
	xorq	%r8, %rcx
	xorq	%r10, %rax
	movq	%rcx, -16(%rsp)
	movq	%rbp, %rcx
	orq	%r10, %rcx
	movq	%rcx, %r8
	xorq	%rdx, %r8
	movq	%r10, %rdx
	movq	%rsi, %r10
	andq	%r9, %rdx
	movq	%r8, -8(%rsp)
	movq	%r11, %r8
	xorq	%rdx, %rbp
	movq	-24(%rsp), %rdx
	andq	%r13, %r8
	xorq	%rdi, %r8
	movq	%rdx, %rcx
	orq	%r13, %rdx
	notq	%rcx
	xorq	%r11, %rdx
	orq	%rcx, %r10
	xorq	%r10, %r13
	movq	%rsi, %r10
	andq	%rdi, %r10
	movq	%r10, %r9
	xorq	%rcx, %r9
	movq	%r11, %rcx
	orq	%rdi, %rcx
	movq	%r9, 16(%rsp)
	movq	48(%rsp), %rdi
	movq	%rcx, %r10
	movq	(%rsp), %rcx
	movq	72(%rsp), %r12
	movq	%r14, -24(%rsp)
	xorq	%rsi, %r10
	movq	-40(%rsp), %rsi
	movq	32(%rsp), %r9
	movq	%rbx, -40(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdi, %r10
	notq	%rcx
	orq	%rsi, %r10
	movq	%rsi, %r11
	movq	%r13, 8(%rsp)
	xorq	%rcx, %r10
	andq	%rcx, %r11
	movq	%rdi, %rcx
	andq	%r12, %rcx
	xorq	%r15, %r11
	xorq	%rsi, %rcx
	movq	%r12, %rsi
	orq	%r15, %rsi
	xorq	%rsi, %rdi
	movq	(%rsp), %rsi
	movq	%rbp, (%rsp)
	movq	%rdi, 32(%rsp)
	andq	%r15, %rsi
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r14, %r15
	movq	-16(%rsp), %r14
	xorq	%rsi, %r12
	movq	-104(%rsp), %rsi
	xorq	%rdx, %r15
	movq	%r12, 40(%rsp)
	xorq	%rbx, %r14
	movq	-72(%rsp), %rbx
	xorq	-80(%rsp), %r14
	xorq	%r8, %rsi
	xorq	%r13, %r14
	movq	16(%rsp), %r13
	xorq	%rax, %rsi
	xorq	%r10, %r15
	xorq	%r9, %rbx
	xorq	%rcx, %r14
	xorq	%r11, %rsi
	xorq	-112(%rsp), %rsi
	xorq	%rbx, %r13
	xorq	-8(%rsp), %r13
	xorq	%rdi, %r13
	movq	-32(%rsp), %rdi
	movq	%r13, %rbx
	xorq	%r12, %rdi
	xorq	-56(%rsp), %rdi
	xorq	%rbp, %rdi
	movq	24(%rsp), %rbp
	rolq	%rbx
	xorq	%r15, %rbx
	xorq	%rbp, %rdi
	movq	%r15, %rbp
	movq	-112(%rsp), %r15
	rolq	%rbp
	movq	%rbp, %r12
	movq	%r14, %rbp
	xorq	%rdi, %r12
	rolq	%rbp
	xorq	%r12, %r15
	rolq	%rdi
	xorq	%rsi, %rbp
	xorq	%r12, %rax
	xorq	%r14, %rdi
	rolq	%rsi
	movq	%r15, %r14
	movq	-88(%rsp), %r15
	xorq	%r13, %rsi
	movq	-104(%rsp), %r13
	rolq	$3, %rax
	xorq	%r12, %r8
	xorq	%rbp, %r15
	xorq	%r12, %r11
	movq	%rax, -96(%rsp)
	rorq	$23, %r8
	xorq	%r12, %r13
	movq	%r15, %rax
	rolq	$18, %r11
	movq	%r8, 64(%rsp)
	rorq	$28, %r13
	rolq	%rax
	movq	%r11, 48(%rsp)
	xorq	%rbp, %r10
	movq	%r13, -104(%rsp)
	xorq	%rbp, %rdx
	movq	%rax, 56(%rsp)
	movq	-48(%rsp), %r15
	rorq	$19, %rdx
	movq	-24(%rsp), %r11
	movq	-40(%rsp), %rax
	movq	%rdx, -48(%rsp)
	xorq	%rbp, %r15
	movq	8(%rsp), %rdx
	rorq	$20, %r15
	xorq	%rbp, %r11
	movq	%r15, -88(%rsp)
	movq	%r10, %r15
	movq	-80(%rsp), %r10
	rolq	$10, %r11
	rolq	$2, %r15
	movq	-88(%rsp), %r12
	xorq	%rbx, %r10
	movq	%r10, %r8
	rorq	$2, %r8
	xorq	%rbx, %rax
	xorq	%rbx, %rdx
	xorq	%rbx, %rcx
	movq	%rax, %r10
	xorq	%rdi, %r9
	rorq	$3, %rcx
	movq	%r8, -112(%rsp)
	rolq	$6, %r10
	movq	%r9, %rbp
	movq	16(%rsp), %r9
	rolq	$15, %rdx
	movq	%r10, -80(%rsp)
	movq	-16(%rsp), %r10
	rorq	$9, %rbp
	xorq	%rdi, %r9
	movq	%rcx, 72(%rsp)
	movq	-32(%rsp), %rcx
	xorq	%rbx, %r10
	movq	-72(%rsp), %rbx
	movq	%r9, %r8
	movq	(%rsp), %r9
	rorq	$21, %r10
	xorq	%rsi, %rcx
	rolq	$21, %r8
	xorq	%rdi, %rbx
	orq	%r10, %r12
	xorq	%rsi, %r9
	rolq	$20, %rcx
	movq	%rbx, %r13
	movq	-56(%rsp), %rbx
	xorq	%r14, %r12
	rorq	$25, %r9
	rolq	$28, %r13
	movq	%r9, -32(%rsp)
	xorq	%rsi, %rbx
	movq	%r13, -24(%rsp)
	movq	-8(%rsp), %r13
	rolq	$27, %rbx
	movq	%r14, -56(%rsp)
	movq	%rbx, -72(%rsp)
	movq	24(%rsp), %rbx
	xorq	%rdi, %r13
	movq	%r13, %rax
	xorq	32(%rsp), %rdi
	movl	$2147483649, %r13d
	movq	-72(%rsp), %r14
	rorq	$8, %rdi
	xorq	%rsi, %rbx
	xorq	40(%rsp), %rsi
	rolq	$25, %rax
	rolq	$14, %rsi
	rolq	$8, %rbx
	xorq	%r12, %r13
	movq	-96(%rsp), %r12
	andq	-48(%rsp), %r12
	movq	%rbx, %r9
	andq	%rdi, %r14
	xorq	%rcx, %r12
	notq	%r9
	movq	%r12, -8(%rsp)
	movq	48(%rsp), %r12
	movq	%r9, (%rsp)
	andq	%r9, %r12
	movq	%r12, %r9
	xorq	%rax, %r9
	movq	%r9, 8(%rsp)
	movq	%rdx, %r9
	orq	%r11, %rdx
	notq	%r9
	xorq	%r9, %r14
	movq	%r9, %r12
	movq	%rbp, %r9
	notq	%r9
	movq	%r9, 16(%rsp)
	movq	-112(%rsp), %r9
	movq	%r15, -40(%rsp)
	andq	%r9, %rbp
	movq	%r13, -16(%rsp)
	xorq	%rbp, %r15
	movq	56(%rsp), %rbp
	movq	%r15, 24(%rsp)
	movq	-96(%rsp), %r15
	xorq	%r9, %rbp
	xorq	-24(%rsp), %rbp
	xorq	-72(%rsp), %rbp
	orq	%rcx, %r15
	movq	16(%rsp), %r9
	andq	-32(%rsp), %r9
	xorq	%r15, %rbp
	movq	-80(%rsp), %r15
	orq	%rax, %r15
	andq	%rbx, %rax
	movq	-32(%rsp), %rbx
	xorq	%rbp, %r15
	movq	-104(%rsp), %rbp
	andq	%r11, %rbp
	xorq	%r15, %rbp
	xorq	%r9, %rbp
	movq	%r8, %r9
	xorq	%rbp, %r13
	movq	-88(%rsp), %rbp
	xorq	-104(%rsp), %rbp
	xorq	-80(%rsp), %rbp
	movq	%r13, %r15
	movq	-24(%rsp), %r13
	xorq	%rbp, %rax
	movq	64(%rsp), %rbp
	xorq	%rdx, %rax
	xorq	16(%rsp), %rax
	movq	%rbp, %rdx
	orq	%rbx, %rdx
	xorq	%rdx, %rax
	movq	%r10, %rdx
	notq	%rdx
	orq	%r8, %rdx
	xorq	%rdx, %rax
	movq	-96(%rsp), %rdx
	xorq	-8(%rsp), %rax
	xorq	%r11, %rdx
	andq	%rsi, %r9
	orq	%rdi, %r12
	andq	%r13, %rcx
	xorq	%r10, %rdx
	movq	-48(%rsp), %r10
	xorq	%rbx, %rdx
	movq	-40(%rsp), %rbx
	xorq	%r9, %rdx
	movq	%rbp, %r9
	xorq	%r10, %rbp
	andq	%rbx, %r9
	xorq	%rbp, %r8
	movq	56(%rsp), %rbp
	xorq	%r9, %rdx
	movq	72(%rsp), %r9
	notq	%r9
	orq	%r10, %r9
	xorq	%rdx, %r9
	movq	-56(%rsp), %rdx
	xorq	%r12, %r9
	movq	72(%rsp), %r12
	xorq	8(%rsp), %r9
	orq	%rsi, %rdx
	xorq	%r8, %rdx
	movq	%r12, %r8
	orq	%r13, %r8
	xorq	%r8, %rdx
	movq	48(%rsp), %r8
	xorq	(%rsp), %rdx
	orq	%rbp, %r8
	xorq	%r8, %rdx
	movq	-112(%rsp), %r8
	orq	%rbx, %r8
	xorq	%r8, %rdx
	movq	48(%rsp), %r8
	xorq	%r14, %rdx
	xorq	%r12, %r8
	movq	%rdx, %r10
	xorq	%rdi, %r8
	xorq	%rsi, %r8
	movq	-56(%rsp), %rsi
	andq	-88(%rsp), %rsi
	xorq	%rsi, %r8
	movq	-72(%rsp), %rdi
	movq	%r9, %rsi
	xorq	%rcx, %r8
	movq	-80(%rsp), %rcx
	andq	%rbp, %rcx
	xorq	%r8, %rcx
	orq	-104(%rsp), %rdi
	movq	%rax, %r8
	rolq	%r10
	rolq	%r8
	xorq	%rdi, %rcx
	movq	24(%rsp), %rdi
	xorq	8(%rsp), %rax
	xorq	%rax, %r10
	movq	%r14, %rax
	rolq	%rsi
	xorq	%rcx, %rdi
	movq	-16(%rsp), %rcx
	xorq	%r9, %rax
	rorq	$21, %r10
	xorq	%rdi, %rcx
	rolq	%rdi
	xorq	%rcx, %r8
	movq	-8(%rsp), %rcx
	xorq	%rax, %rdi
	movq	24(%rsp), %rax
	rolq	$21, %rdi
	xorq	%r15, %rcx
	xorq	%rdx, %rax
	rolq	%r15
	xorq	%rcx, %rsi
	xorq	%rax, %r15
	movq	%r10, %rcx
	movabsq	$-9223372034707259384, %rax
	rorq	$20, %rsi
	rolq	$14, %r15
	notq	%rcx
	movq	%rsi, %rdx
	orq	%rdi, %rcx
	orq	%r10, %rdx
	xorq	%rsi, %rcx
	xorq	%r8, %rdx
	orq	%r15, %r8
	notq	%rcx
	xorq	%rdi, %r8
	andq	%r15, %rdi
	xorq	%rax, %rdx
	xorq	%r10, %rdi
	addq	$1, -64(%rsp)
	movq	-64(%rsp), %rax
	notq	%rdi
	movq	%rdi, %rsi
	cmpq	%rax, 104(%rsp)
	jne	.L60
	movq	%rdx, %xmm1
	movq	%rcx, %xmm6
	movq	%rsi, %xmm0
	movq	112(%rsp), %rdi
	movq	%r8, %xmm7
	punpcklqdq	%xmm6, %xmm1
	punpcklqdq	%xmm7, %xmm0
.L59:
	movups	%xmm1, (%rdi)
	movups	%xmm0, 16(%rdi)
	subq	$-128, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L65:
	.cfi_restore_state
	movdqa	%xmm3, %xmm1
	movdqa	%xmm2, %xmm0
	jmp	.L59
	.cfi_endproc
.LFE96:
	.size	chain_scalar, .-chain_scalar
	.p2align 4
	.type	chain_avx512, @function
chain_avx512:
.LFB7373:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	andq	$-64, %rsp
	subq	$64, %rsp
	vmovdqu	(%rsi), %ymm0
	movq	%fs:40, %rax
	movq	%rax, 56(%rsp)
	xorl	%eax, %eax
	movl	$15, %eax
	vmovdqu	%ymm0, 16(%rsp)
	kmovw	%eax, %k6
	vmovdqu64	16(%rsp), %zmm5{%k6}{z}
	testq	%rdx, %rdx
	je	.L68
	movl	$15, %ecx
	movl	$8, %esi
	vmovdqa64	.LC4(%rip), %zmm22
	vmovdqa64	.LC5(%rip), %zmm9
	kmovw	%ecx, %k7
	kmovw	%esi, %k5
	movl	$30, %ecx
	movl	$12, %esi
	kmovw	%ecx, %k6
	kmovw	%esi, %k2
	movl	$2, %ecx
	vmovdqa64	.LC6(%rip), %zmm0
	vmovdqa64	.LC7(%rip), %zmm8
	kmovw	%ecx, %k4
	vmovdqa64	.LC8(%rip), %zmm4
	movl	$16, %ecx
	vmovdqa64	.LC9(%rip), %zmm7
	xorl	%eax, %eax
	vmovdqa64	.LC10(%rip), %zmm3
	movl	$3, %esi
	vmovdqa64	.LC11(%rip), %zmm2
	vpxord	%zmm21, %zmm21, %zmm21
	vmovdqa64	.LC12(%rip), %zmm20
	kmovw	%ecx, %k1
	vmovdqa64	.LC13(%rip), %zmm19
	kmovw	%esi, %k3
	vmovdqa64	.LC14(%rip), %zmm18
	vmovdqa64	.LC15(%rip), %zmm17
	vmovdqa64	.LC16(%rip), %zmm16
	vmovdqa64	.LC17(%rip), %zmm15
	vmovdqa64	.LC18(%rip), %zmm14
	vmovdqa64	.LC19(%rip), %zmm13
	vmovdqa64	.LC20(%rip), %zmm12
	vmovdqa64	.LC21(%rip), %zmm11
	vmovdqa64	.LC22(%rip), %zmm10
	vmovdqa64	.LC23(%rip), %zmm1
	.p2align 4
	.p2align 3
.L69:
	vmovdqa64	.LC2(%rip), %zmm31
	vpsllq	$8, %zmm5, %zmm6{%k7}{z}
	vpsrlq	$56, %zmm5, %zmm5
	addq	$1, %rax
	vmovdqa64	%zmm22, %zmm26
	vpermq	%zmm5, %zmm31, %zmm23{%k6}{z}
	vpternlogq	$254, .LC3(%rip), %zmm23, %zmm6
	vmovdqa64	%zmm21, %zmm23
	vmovdqa64	%zmm6, %zmm5
	vpternlogq	$150, %zmm21, %zmm21, %zmm6
	vpternlogq	$150, %zmm21, %zmm22, %zmm6
	vpermq	%zmm6, %zmm9, %zmm24
	vpermq	%zmm6, %zmm0, %zmm6
	vprolq	$1, %zmm6, %zmm6
	vpternlogq	$150, %zmm6, %zmm24, %zmm23
	vpternlogq	$150, %zmm6, %zmm24, %zmm5
	vpternlogq	$150, %zmm6, %zmm24, %zmm26
	vprolvq	%zmm7, %zmm23, %zmm25
	vprolvq	%zmm8, %zmm5, %zmm5
	vprolvq	%zmm4, %zmm23, %zmm30
	vprolvq	%zmm3, %zmm26, %zmm29
	vprolvq	%zmm2, %zmm23, %zmm28
	vmovdqa64	%zmm25, %zmm24
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vmovdqa64	%zmm5, %zmm6
	vmovdqa64	%zmm5, %zmm26
	vprolvq	%zmm4, %zmm23, %zmm6{%k4}
	vpermt2q	%zmm30, %zmm20, %zmm26{%k3}{z}
	vpermq	%zmm28, %zmm21, %zmm27{%k1}{z}
	vpermq	%zmm28, %zmm13, %zmm31{%k1}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vprolvq	%zmm2, %zmm23, %zmm6{%k1}
	vpermq	%zmm28, %zmm18, %zmm23{%k1}{z}
	vmovdqa64	%zmm6, %zmm24
	vmovdqa64	%zmm25, %zmm6
	vpermt2q	%zmm29, %zmm19, %zmm6{%k2}{z}
	vpternlogq	$254, %zmm23, %zmm6, %zmm26
	vmovdqa64	%zmm5, %zmm23
	vmovdqa64	%zmm25, %zmm6
	vpermt2q	%zmm29, %zmm16, %zmm6{%k2}{z}
	vpermt2q	%zmm30, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm27, %zmm6, %zmm23
	vmovdqa64	%zmm5, %zmm27
	vmovdqa64	%zmm25, %zmm6
	vpermt2q	%zmm29, %zmm14, %zmm6{%k2}{z}
	vpermt2q	%zmm30, %zmm15, %zmm27{%k3}{z}
	vpermt2q	%zmm30, %zmm12, %zmm5{%k3}{z}
	vpternlogq	$254, %zmm31, %zmm6, %zmm27
	vmovdqa64	%zmm25, %zmm6
	vpermq	%zmm28, %zmm10, %zmm25{%k1}{z}
	vpermt2q	%zmm29, %zmm11, %zmm6{%k2}{z}
	vpermq	%zmm24, %zmm1, %zmm28
	vpternlogq	$254, %zmm25, %zmm6, %zmm5
	vpermq	%zmm24, %zmm0, %zmm25
	vmovdqa64	%zmm24, %zmm6
	vpternlogq	$210, %zmm28, %zmm25, %zmm6
	vpermq	%zmm26, %zmm0, %zmm24
	vpermq	%zmm26, %zmm1, %zmm25
	vpxord	.LC24(%rip), %zmm6, %zmm6
	vpternlogq	$210, %zmm25, %zmm24, %zmm26
	vpermq	%zmm23, %zmm1, %zmm25
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm25, %zmm24, %zmm23
	vpermq	%zmm27, %zmm1, %zmm25
	vpermq	%zmm27, %zmm0, %zmm24
	vpternlogq	$210, %zmm25, %zmm24, %zmm27
	vpermq	%zmm5, %zmm1, %zmm25
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm25, %zmm24, %zmm5
	vmovdqa64	%zmm6, %zmm24
	vpternlogq	$150, %zmm23, %zmm26, %zmm24
	vpternlogq	$150, %zmm5, %zmm27, %zmm24
	vpermq	%zmm24, %zmm9, %zmm28
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm28, %zmm6
	vpternlogq	$150, %zmm24, %zmm28, %zmm23
	vpternlogq	$150, %zmm24, %zmm28, %zmm26
	vprolvq	%zmm8, %zmm6, %zmm25
	vpternlogq	$150, %zmm24, %zmm28, %zmm27
	vpternlogq	$150, %zmm24, %zmm28, %zmm5
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm4, %zmm26, %zmm29
	vprolvq	%zmm3, %zmm27, %zmm30
	vprolvq	%zmm2, %zmm5, %zmm28
	vmovdqa64	%zmm25, %zmm6
	vprolvq	%zmm4, %zmm26, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm3, %zmm27, %zmm24{%k5}
	vmovdqa64	%zmm25, %zmm27
	vpermt2q	%zmm29, %zmm20, %zmm27{%k3}{z}
	vpermq	%zmm28, %zmm21, %zmm26{%k1}{z}
	vpermq	%zmm28, %zmm13, %zmm31{%k1}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vpermq	%zmm28, %zmm18, %zmm24{%k1}{z}
	vprolvq	%zmm2, %zmm5, %zmm6{%k1}
	vmovdqa64	%zmm23, %zmm5
	vpermt2q	%zmm30, %zmm19, %zmm5{%k2}{z}
	vpternlogq	$254, %zmm24, %zmm5, %zmm27
	vmovdqa64	%zmm25, %zmm24
	vmovdqa64	%zmm23, %zmm5
	vpermt2q	%zmm30, %zmm16, %zmm5{%k2}{z}
	vpermt2q	%zmm29, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm26, %zmm5, %zmm24
	vmovdqa64	%zmm25, %zmm26
	vmovdqa64	%zmm23, %zmm5
	vpermt2q	%zmm30, %zmm14, %zmm5{%k2}{z}
	vpermt2q	%zmm29, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm30, %zmm11, %zmm23{%k2}{z}
	vpternlogq	$254, %zmm31, %zmm5, %zmm26
	vmovdqa64	%zmm25, %zmm5
	vpermq	%zmm28, %zmm10, %zmm25{%k1}{z}
	vpermt2q	%zmm29, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm1, %zmm28
	vpternlogq	$254, %zmm25, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm25
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm25, %zmm23, %zmm6
	vpermq	%zmm27, %zmm0, %zmm23
	vmovdqa64	%zmm27, %zmm25
	vpternlogq	$210, %zmm28, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpermq	%zmm24, %zmm0, %zmm23
	vpxord	.LC25(%rip), %zmm6, %zmm6
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC26(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC27(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC28(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC29(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC30(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC31(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC32(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC33(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC34(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC35(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC36(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC37(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC38(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC39(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC40(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC41(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC42(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC43(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm23, %zmm25
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm23
	vmovdqa64	%zmm6, %zmm26
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC30(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm25, %zmm24
	vpternlogq	$150, %zmm6, %zmm26, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vmovdqa64	%zmm6, %zmm30
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm2, %zmm6, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm5, %zmm6
	vprolvq	%zmm4, %zmm25, %zmm6{%k4}
	vmovdqa64	%zmm23, %zmm24
	vmovdqa64	%zmm5, %zmm25
	vprolvq	%zmm3, %zmm26, %zmm24{%k5}
	vpermq	%zmm27, %zmm18, %zmm26{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm25{%k3}{z}
	vmovdqa64	%zmm24, %zmm6{%k2}
	vmovdqa64	%zmm23, %zmm24
	vprolvq	%zmm2, %zmm30, %zmm6{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm26, %zmm24, %zmm25
	vmovdqa64	%zmm5, %zmm24
	vmovdqa64	%zmm23, %zmm26
	vpermt2q	%zmm29, %zmm16, %zmm26{%k2}{z}
	vpermt2q	%zmm28, %zmm17, %zmm24{%k3}{z}
	vpternlogq	$254, %zmm30, %zmm26, %zmm24
	vmovdqa64	%zmm5, %zmm26
	vmovdqa64	%zmm23, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm26{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm23{%k2}{z}
	vpermt2q	%zmm28, %zmm12, %zmm5{%k3}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm23, %zmm5
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm6
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm23
	vpternlogq	$254, %zmm31, %zmm30, %zmm26
	vpternlogq	$210, %zmm27, %zmm23, %zmm25
	vpermq	%zmm24, %zmm1, %zmm27
	vpxord	.LC44(%rip), %zmm6, %zmm6
	vpermq	%zmm24, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm24
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm26
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm23
	vpternlogq	$210, %zmm27, %zmm23, %zmm5
	vmovdqa64	%zmm6, %zmm23
	vpternlogq	$150, %zmm24, %zmm25, %zmm23
	vpternlogq	$150, %zmm5, %zmm26, %zmm23
	vpermq	%zmm23, %zmm9, %zmm27
	vpermq	%zmm23, %zmm0, %zmm23
	vprolq	$1, %zmm23, %zmm23
	vpternlogq	$150, %zmm23, %zmm27, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm24
	vpternlogq	$150, %zmm23, %zmm27, %zmm5
	vprolvq	%zmm8, %zmm6, %zmm6
	vpternlogq	$150, %zmm23, %zmm27, %zmm25
	vpternlogq	$150, %zmm23, %zmm27, %zmm26
	vmovdqa64	%zmm5, %zmm30
	vprolvq	%zmm7, %zmm24, %zmm24
	vprolvq	%zmm2, %zmm5, %zmm27
	vprolvq	%zmm4, %zmm25, %zmm28
	vprolvq	%zmm3, %zmm26, %zmm29
	vmovdqa64	%zmm6, %zmm5
	vprolvq	%zmm4, %zmm25, %zmm5{%k4}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm3, %zmm26, %zmm23{%k5}
	vmovdqa64	%zmm6, %zmm26
	vpermq	%zmm27, %zmm18, %zmm25{%k1}{z}
	vpermq	%zmm27, %zmm13, %zmm31{%k1}{z}
	vpermt2q	%zmm28, %zmm20, %zmm26{%k3}{z}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vmovdqa64	%zmm24, %zmm23
	vprolvq	%zmm2, %zmm30, %zmm5{%k1}
	vpermt2q	%zmm29, %zmm19, %zmm23{%k2}{z}
	vpermq	%zmm27, %zmm21, %zmm30{%k1}{z}
	vpternlogq	$254, %zmm25, %zmm23, %zmm26
	vmovdqa64	%zmm6, %zmm23
	vmovdqa64	%zmm24, %zmm25
	vpermt2q	%zmm28, %zmm17, %zmm23{%k3}{z}
	vpermt2q	%zmm29, %zmm16, %zmm25{%k2}{z}
	vpternlogq	$254, %zmm30, %zmm25, %zmm23
	vmovdqa64	%zmm6, %zmm25
	vmovdqa64	%zmm24, %zmm30
	vpermt2q	%zmm28, %zmm15, %zmm25{%k3}{z}
	vpermt2q	%zmm28, %zmm12, %zmm6{%k3}{z}
	vpermt2q	%zmm29, %zmm11, %zmm24{%k2}{z}
	vpermq	%zmm27, %zmm10, %zmm28{%k1}{z}
	vpermt2q	%zmm29, %zmm14, %zmm30{%k2}{z}
	vpternlogq	$254, %zmm28, %zmm24, %zmm6
	vpermq	%zmm5, %zmm1, %zmm27
	vpermq	%zmm5, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm5
	vpermq	%zmm26, %zmm1, %zmm27
	vpermq	%zmm26, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm26
	vpternlogq	$254, %zmm31, %zmm30, %zmm25
	vpermq	%zmm23, %zmm1, %zmm27
	vpxord	.LC29(%rip), %zmm5, %zmm5
	vpermq	%zmm23, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm23
	vpermq	%zmm25, %zmm1, %zmm27
	vpermq	%zmm25, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm25
	vpermq	%zmm6, %zmm1, %zmm27
	vpermq	%zmm6, %zmm0, %zmm24
	vpternlogq	$210, %zmm27, %zmm24, %zmm6
	vmovdqa64	%zmm5, %zmm24
	vpternlogq	$150, %zmm23, %zmm26, %zmm24
	vpternlogq	$150, %zmm6, %zmm25, %zmm24
	vpermq	%zmm24, %zmm9, %zmm27
	vpermq	%zmm24, %zmm0, %zmm24
	vprolq	$1, %zmm24, %zmm24
	vpternlogq	$150, %zmm24, %zmm27, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm23
	vpternlogq	$150, %zmm24, %zmm27, %zmm26
	vprolvq	%zmm8, %zmm5, %zmm5
	vpternlogq	$150, %zmm24, %zmm27, %zmm25
	vpternlogq	$150, %zmm24, %zmm27, %zmm6
	vprolvq	%zmm7, %zmm23, %zmm23
	vprolvq	%zmm4, %zmm26, %zmm5{%k4}
	vprolvq	%zmm3, %zmm25, %zmm23{%k5}
	vmovdqa64	%zmm23, %zmm5{%k2}
	vprolvq	%zmm2, %zmm6, %zmm5{%k1}
	vpermq	%zmm5, %zmm1, %zmm23
	vpermq	%zmm5, %zmm0, %zmm6
	vpternlogq	$210, %zmm23, %zmm6, %zmm5
	vpxord	.LC45(%rip), %zmm5, %zmm5
	cmpq	%rax, %rdx
	jne	.L69
.L68:
	movl	$15, %eax
	kmovw	%eax, %k7
	vmovdqu64	%zmm5, 16(%rsp){%k7}
	vmovdqu	16(%rsp), %ymm0
	vmovdqu	%ymm0, (%rdi)
	movq	56(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L78
	vzeroupper
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L78:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7373:
	.size	chain_avx512, .-chain_avx512
	.p2align 4
	.type	k_usable, @function
k_usable:
.LFB7385:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$232, %rsp
	.cfi_def_cfa_offset 256
	movq	%fs:40, %rax
	movq	%rax, 216(%rsp)
	xorl	%eax, %eax
	cmpl	$-1, %edi
	je	.L81
	movl	%edi, %r10d
#APP
# 309 "/usr/lib/gcc/x86_64-linux-gnu/15/include/cpuid.h" 1
	cpuid
	
# 0 "" 2
#NO_APP
	cmpl	$6, %eax
	jbe	.L82
	movl	$1, %eax
#APP
# 42 "chain.h" 1
	cpuid
	
# 0 "" 2
#NO_APP
	notl	%ecx
	andl	$402653184, %ecx
	je	.L83
	movl	$7, %eax
	xorl	%ecx, %ecx
#APP
# 44 "chain.h" 1
	cpuid
	
# 0 "" 2
#NO_APP
	movl	%ebx, %esi
	cmpl	$2, %edi
	je	.L81
	jg	.L81
.L103:
	cmpl	$1, %r10d
	jne	.L89
	notl	%esi
	andl	$264, %esi
	je	.L89
	.p2align 4
	.p2align 3
.L81:
	xorl	%eax, %eax
.L79:
	movq	216(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L121
	addq	$232, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L82:
	.cfi_restore_state
	cmpl	$2, %edi
	je	.L81
	jg	.L81
	cmpl	$1, %edi
	je	.L81
	.p2align 4
	.p2align 3
.L89:
	leaq	16(%rsp), %rsi
	leaq	80(%rsp), %rdi
	movl	$300, %edx
	movdqa	.LC46(%rip), %xmm0
	movl	%r10d, 12(%rsp)
	movaps	%xmm0, 16(%rsp)
	movdqa	.LC47(%rip), %xmm0
	movq	%rsi, (%rsp)
	movaps	%xmm0, 48(%rsp)
	movdqa	.LC48(%rip), %xmm0
	movaps	%xmm0, 32(%rsp)
	movdqa	.LC49(%rip), %xmm0
	movaps	%xmm0, 64(%rsp)
	call	chain_scalar
	movslq	12(%rsp), %r10
	leaq	k_fn(%rip), %rax
	movl	$300, %edx
	movq	(%rsp), %rsi
	leaq	144(%rsp), %rdi
	call	*(%rax,%r10,8)
	movq	144(%rsp), %rax
	movq	152(%rsp), %rdx
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rdx
	orq	%rdx, %rax
	jne	.L81
	movq	160(%rsp), %rax
	movq	168(%rsp), %rdx
	xorq	96(%rsp), %rax
	xorq	104(%rsp), %rdx
	orq	%rdx, %rax
	movl	$1, %eax
	jne	.L81
	jmp	.L79
.L83:
	xorl	%ecx, %ecx
#APP
# 32 "chain.h" 1
	xgetbv
# 0 "" 2
#NO_APP
	movl	%eax, %edi
	movl	$7, %eax
	andl	$230, %edi
#APP
# 44 "chain.h" 1
	cpuid
	
# 0 "" 2
#NO_APP
	movl	%ebx, %r8d
	movl	%ebx, %esi
	cmpl	$2, %r10d
	je	.L86
	jle	.L103
	cmpq	$230, %rdi
	jne	.L81
	notl	%r8d
	andl	$-2147418112, %r8d
	jne	.L81
	leaq	80(%rsp), %rdi
	movl	$300, %edx
	leaq	16(%rsp), %rsi
	movdqa	.LC46(%rip), %xmm0
	movl	%r10d, (%rsp)
	movaps	%xmm0, 16(%rsp)
	movdqa	.LC47(%rip), %xmm0
	movaps	%xmm0, 48(%rsp)
	movdqa	.LC48(%rip), %xmm0
	movaps	%xmm0, 32(%rsp)
	movdqa	.LC49(%rip), %xmm0
	movaps	%xmm0, 64(%rsp)
	call	chain_scalar
	movslq	(%rsp), %rax
	movl	$300, %edx
	leaq	144(%rsp), %rdi
	leaq	k_fn(%rip), %rcx
	movq	%rdi, %r14
	leaq	16(%rsp), %rsi
	call	*(%rcx,%rax,8)
	movq	144(%rsp), %rax
	movq	152(%rsp), %rdx
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rdx
	orq	%rdx, %rax
	movl	(%rsp), %r10d
	jne	.L81
	movq	160(%rsp), %rax
	movq	168(%rsp), %rdx
	xorq	96(%rsp), %rax
	xorq	104(%rsp), %rdx
	orq	%rdx, %rax
	jne	.L81
	leaq	48(%rsp), %r9
	leaq	112(%rsp), %rdi
	movl	$290, %edx
	movl	%r10d, 12(%rsp)
	movq	%r9, %rsi
	movq	%r9, (%rsp)
	call	chain_scalar
	leaq	16(%rsp), %rdx
	subq	$8, %rsp
	.cfi_def_cfa_offset 264
	movq	%r14, %rsi
	pushq	$290
	.cfi_def_cfa_offset 272
	movq	16(%rsp), %r9
	movl	$300, %ecx
	movl	28(%rsp), %edi
	leaq	192(%rsp), %r8
	call	chain_two
	popq	%rax
	.cfi_def_cfa_offset 264
	popq	%rdx
	.cfi_def_cfa_offset 256
	movq	144(%rsp), %rax
	movq	152(%rsp), %rdx
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rdx
	orq	%rdx, %rax
	jne	.L81
	movq	160(%rsp), %rax
	movq	168(%rsp), %rdx
	xorq	96(%rsp), %rax
	xorq	104(%rsp), %rdx
	orq	%rdx, %rax
	jne	.L81
	movq	176(%rsp), %rax
	movq	184(%rsp), %rdx
	xorq	112(%rsp), %rax
	xorq	120(%rsp), %rdx
	orq	%rdx, %rax
	je	.L122
.L92:
	movl	$1, %eax
.L93:
	xorl	$1, %eax
	jmp	.L79
.L122:
	movq	192(%rsp), %rax
	movq	200(%rsp), %rdx
	xorq	128(%rsp), %rax
	xorq	136(%rsp), %rdx
	orq	%rdx, %rax
	jne	.L92
	xorl	%eax, %eax
	jmp	.L93
.L121:
	call	__stack_chk_fail@PLT
.L86:
	cmpq	$230, %rdi
	jne	.L81
	andl	$65536, %r8d
	jne	.L89
	jmp	.L81
	.cfi_endproc
.LFE7385:
	.size	k_usable, .-k_usable
	.p2align 4
	.type	helper_main, @function
helper_main:
.LFB7406:
	.cfi_startproc
	endbr64
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	movq	%rdi, %rbx
	.p2align 4
	.p2align 3
.L124:
	movq	%rbx, %rdi
	call	sem_wait@PLT
	testl	%eax, %eax
	jne	.L124
	movq	40(%rbx), %rdi
	movq	32(%rbx), %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	jmp	*%rax
	.cfi_endproc
.LFE7406:
	.size	helper_main, .-helper_main
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC50:
	.string	"prover: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB7388:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC50(%rip), %rdx
	movl	$2, %esi
	xorl	%eax, %eax
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	%rdi, %rcx
	movq	stderr(%rip), %rdi
	call	__fprintf_chk@PLT
	movl	$1, %edi
	call	exit@PLT
	.cfi_endproc
.LFE7388:
	.size	die, .-die
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC51:
	.string	"/sys/devices/system/cpu/cpu%d/topology/thread_siblings_list"
	.section	.rodata.str1.1
.LC52:
	.string	"r"
.LC53:
	.string	"thread setup"
.LC54:
	.string	"pthread_create"
.LC55:
	.string	"ready"
.LC56:
	.string	"go"
.LC57:
	.string	"no go"
.LC58:
	.string	"sem_post"
	.text
	.p2align 4
	.type	handshake, @function
handshake:
.LFB7413:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$552, %rsp
	.cfi_def_cfa_offset 608
	movq	%rdi, 8(%rsp)
	movl	%esi, 20(%rsp)
	movq	%fs:40, %rax
	movq	%rax, 536(%rsp)
	xorl	%eax, %eax
	call	sched_getcpu@PLT
	testl	%eax, %eax
	js	.L142
	leaq	48(%rsp), %r14
	movl	$128, %esi
	xorl	%edi, %edi
	movl	%eax, %r13d
	movq	%r14, %rdx
	call	sched_getaffinity@PLT
	movl	%eax, %ebx
	testl	%eax, %eax
	je	.L187
.L142:
	movslq	20(%rsp), %rbp
	movq	8(%rsp), %r12
	leaq	48(%rsp), %r13
	imulq	$56, %rbp, %rbp
	movq	%r12, %rbx
	addq	%r12, %rbp
	jmp	.L148
	.p2align 4,,10
	.p2align 3
.L145:
	leaq	48(%rbx), %rdi
.L154:
	xorl	%esi, %esi
	movq	%rbx, %rcx
	leaq	helper_main(%rip), %rdx
	call	pthread_create@PLT
	testl	%eax, %eax
	jne	.L188
.L147:
	movq	%r13, %rdi
	addq	$56, %rbx
	call	pthread_attr_destroy@PLT
	cmpq	%rbp, %rbx
	je	.L189
.L148:
	xorl	%edx, %edx
	xorl	%esi, %esi
	movq	%rbx, %rdi
	call	sem_init@PLT
	testl	%eax, %eax
	jne	.L144
	movq	%r13, %rdi
	call	pthread_attr_init@PLT
	testl	%eax, %eax
	jne	.L144
	movl	placed(%rip), %eax
	testl	%eax, %eax
	je	.L145
	leaq	rest_set(%rip), %rdx
	movl	$128, %esi
	movq	%r13, %rdi
	call	pthread_attr_setaffinity_np@PLT
	testl	%eax, %eax
	jne	.L145
	leaq	48(%rbx), %rdi
	movq	%rbx, %rcx
	leaq	helper_main(%rip), %rdx
	movq	%r13, %rsi
	movq	%rdi, 8(%rsp)
	call	pthread_create@PLT
	movq	8(%rsp), %rdi
	testl	%eax, %eax
	jne	.L154
	jmp	.L147
	.p2align 4,,10
	.p2align 3
.L189:
	leaq	.LC55(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movl	$64, %esi
	leaq	272(%rsp), %rdi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L149
	cmpw	$28519, 272(%rsp)
	je	.L152
.L149:
	leaq	.LC57(%rip), %rdi
	call	die
	.p2align 4,,10
	.p2align 3
.L152:
	movq	%r12, %rdi
	call	sem_post@PLT
	testl	%eax, %eax
	jne	.L190
	addq	$56, %r12
	cmpq	%rbp, %r12
	jne	.L152
	movq	536(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L191
	addq	$552, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L187:
	.cfi_restore_state
	movl	%r13d, %r9d
	movl	$96, %ecx
	movl	$2, %edx
	xorl	%eax, %eax
	leaq	.LC51(%rip), %r8
	movl	$96, %esi
	leaq	176(%rsp), %rdi
	call	__snprintf_chk@PLT
	leaq	.LC52(%rip), %rsi
	leaq	176(%rsp), %rdi
	call	fopen@PLT
	movq	%rax, %r12
	testq	%rax, %rax
	je	.L142
	leaq	272(%rsp), %rbp
	movq	%rax, %rdx
	movl	$256, %esi
	movq	%rbp, %rdi
	call	fgets@PLT
	movq	%r12, %rdi
	movq	%rax, %r15
	call	fclose@PLT
	testq	%r15, %r15
	je	.L142
	leaq	core_set(%rip), %r15
	movl	$32, %ecx
	movl	%ebx, %eax
	movq	%r15, %rdi
	leaq	40(%rsp), %r12
	rep stosl
	.p2align 4
	.p2align 3
.L138:
	movq	%rbp, %rdi
	movl	$10, %edx
	movq	%r12, %rsi
	call	__isoc23_strtol@PLT
	movq	40(%rsp), %rdi
	movq	%rax, %r8
	testq	%rax, %rax
	js	.L142
	cmpq	%rdi, %rbp
	je	.L142
	cmpb	$45, (%rdi)
	je	.L192
.L132:
	movl	$1023, %edx
	cmpq	%rdx, %rax
	cmovg	%rdx, %rax
	leaq	1(%rax), %rsi
	cmpq	%rax, %r8
	jg	.L137
	.p2align 5
	.p2align 4
	.p2align 3
.L136:
	movq	%r8, %rax
	movl	%r8d, %ecx
	movl	$1, %edx
	addq	$1, %r8
	shrq	$6, %rax
	salq	%cl, %rdx
	orq	%rdx, (%r15,%rax,8)
	cmpq	%rsi, %r8
	jne	.L136
.L137:
	cmpb	$44, (%rdi)
	jne	.L193
	leaq	1(%rdi), %rbp
	jmp	.L138
.L192:
	leaq	1(%rdi), %rbp
	movl	$10, %edx
	movq	%r12, %rsi
	movq	%rax, 24(%rsp)
	movq	%rbp, %rdi
	call	__isoc23_strtol@PLT
	movq	40(%rsp), %rdi
	cmpq	%rdi, %rbp
	je	.L142
	movq	24(%rsp), %r8
	cmpq	%rax, %r8
	jle	.L132
	jmp	.L142
.L193:
	leaq	core_set(%rip), %rdx
	xorl	%eax, %eax
.L140:
	movdqa	(%rdx), %xmm0
	pand	(%r14,%rax), %xmm0
	addq	$16, %rax
	addq	$16, %rdx
	movaps	%xmm0, -16(%rdx)
	cmpq	$128, %rax
	jne	.L140
	movslq	%r13d, %rax
	cmpq	$1023, %rax
	ja	.L142
	shrq	$6, %rax
	movq	(%r15,%rax,8), %rax
	btq	%r13, %rax
	jnc	.L142
	xorl	%eax, %eax
	leaq	rest_set(%rip), %rsi
.L141:
	movq	(%r14,%rax,8), %rdx
	xorq	(%r15,%rax,8), %rdx
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	$16, %rax
	jne	.L141
	movl	$128, %edi
	call	__sched_cpucount@PLT
	testl	%eax, %eax
	je	.L142
	movl	$1, placed(%rip)
	jmp	.L142
.L144:
	leaq	.LC53(%rip), %rdi
	call	die
.L188:
	leaq	.LC54(%rip), %rdi
	call	die
.L190:
	leaq	.LC58(%rip), %rdi
	call	die
.L191:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7413:
	.size	handshake, .-handshake
	.section	.rodata.str1.1
.LC59:
	.string	"proof.bin.tmp"
.LC60:
	.string	"proof.bin"
	.text
	.p2align 4
	.type	finish_proof, @function
finish_proof:
.LFB7414:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movl	$16, %ecx
	movq	%rdx, %rbp
	movl	$32, %edx
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	movq	%rdi, %rbx
	subq	$8, %rsp
	.cfi_def_cfa_offset 32
	movl	4(%rdi), %edi
	call	pwrite@PLT
	cmpq	$32, %rax
	jne	.L196
	movl	4(%rbx), %edi
	movl	$48, %ecx
	movl	$32, %edx
	movq	%rbp, %rsi
	call	pwrite@PLT
	cmpq	$32, %rax
	jne	.L196
	movl	4(%rbx), %edi
	leaq	.LC60(%rip), %rbx
	call	close@PLT
	testl	%eax, %eax
	jne	.L198
	movq	%rbx, %rsi
	leaq	.LC59(%rip), %rdi
	call	rename@PLT
	testl	%eax, %eax
	jne	.L198
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
.L196:
	.cfi_restore_state
	leaq	.LC59(%rip), %rdi
	call	die
.L198:
	movq	%rbx, %rdi
	call	die
	.cfi_endproc
.LFE7414:
	.size	finish_proof, .-finish_proof
	.section	.rodata.str1.1
.LC61:
	.string	"out of memory"
	.text
	.p2align 4
	.type	reserve, @function
reserve:
.LFB7389:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$8, %rsp
	.cfi_def_cfa_offset 32
	movq	8(%rdi), %rax
	movq	16(%rdi), %rbx
	leaq	1(%rax,%rsi), %rax
	cmpq	%rax, %rbx
	jnb	.L200
	testq	%rbx, %rbx
	je	.L209
	.p2align 3
	.p2align 4
	.p2align 3
.L204:
	addq	%rbx, %rbx
	cmpq	%rax, %rbx
	jb	.L204
.L203:
	movq	%rdi, %rbp
	movq	(%rdi), %rdi
	movq	%rbx, %rsi
	call	realloc@PLT
	movq	%rax, 0(%rbp)
	testq	%rax, %rax
	je	.L210
	movq	%rbx, 16(%rbp)
.L200:
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L209:
	.cfi_restore_state
	movl	$4096, %ebx
	cmpq	$4096, %rax
	jbe	.L203
	addq	%rbx, %rbx
	cmpq	%rax, %rbx
	jb	.L204
	jmp	.L203
.L210:
	leaq	.LC61(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7389:
	.size	reserve, .-reserve
	.p2align 4
	.type	leaf_stmt, @function
leaf_stmt:
.LFB89:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movq	%rsi, %rax
	movq	%rdi, %r9
	xorl	%ecx, %ecx
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$664, %rsp
	.cfi_def_cfa_offset 720
	movdqu	(%rax), %xmm0
	movq	%fs:40, %rsi
	movq	%rsi, 648(%rsp)
	movq	%rdx, %rsi
	movb	$76, 464(%rsp)
	movups	%xmm0, 465(%rsp)
	movdqu	16(%rax), %xmm0
	leaq	497(%rsp), %rax
	movups	%xmm0, 481(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L212:
	movq	%rsi, %rdx
	addq	$1, %rax
	shrq	%cl, %rdx
	addl	$8, %ecx
	movb	%dl, -1(%rax)
	cmpl	$64, %ecx
	jne	.L212
	xorl	%eax, %eax
	leaq	56(%rsp), %rdi
	movdqa	480(%rsp), %xmm0
	movl	$24, %ecx
	rep stosq
	movl	$12, %ecx
	leaq	552(%rsp), %rdi
	movdqa	464(%rsp), %xmm2
	rep stosq
	movzbl	464(%rsp), %eax
	movaps	%xmm0, 528(%rsp)
	movdqu	489(%rsp), %xmm0
	movb	$1, 553(%rsp)
	leaq	512(%rsp), %r8
	leaq	648(%rsp), %rdi
	movb	$-128, 647(%rsp)
	movq	%rax, 48(%rsp)
	leaq	513(%rsp), %rax
	movaps	%xmm2, 512(%rsp)
	movups	%xmm0, 537(%rsp)
	.p2align 6
	.p2align 4
	.p2align 3
.L213:
	movl	%eax, %ecx
	movzbl	(%rax), %esi
	addq	$1, %rax
	subl	%r8d, %ecx
	movl	%ecx, %edx
	andl	$7, %ecx
	sarl	$3, %edx
	sall	$3, %ecx
	movslq	%edx, %rdx
	salq	%cl, %rsi
	xorq	%rsi, 48(%rsp,%rdx,8)
	cmpq	%rax, %rdi
	jne	.L213
	leaq	RC(%rip), %r11
	leaq	32(%rsp), %rbx
	movl	$3435973837, %edi
	.p2align 4
	.p2align 3
.L225:
	leaq	48(%rsp), %r10
	movq	%rsp, %rdx
	movq	%r10, %rax
.L216:
	movdqu	40(%rax), %xmm0
	pxor	(%rax), %xmm0
	addq	$16, %rdx
	addq	$16, %rax
	pxor	144(%rax), %xmm0
	movdqu	104(%rax), %xmm1
	pxor	64(%rax), %xmm1
	pxor	%xmm1, %xmm0
	movaps	%xmm0, -16(%rdx)
	cmpq	%rdx, %rbx
	jne	.L216
	movq	120(%rsp), %rax
	xorq	80(%rsp), %rax
	leaq	248(%rsp), %rcx
	xorl	%esi, %esi
	xorq	160(%rsp), %rax
	xorq	200(%rsp), %rax
	xorq	240(%rsp), %rax
	movq	%rax, 32(%rsp)
.L215:
	leal	4(%rsi), %eax
	movq	%rax, %rdx
	imulq	%rdi, %rax
	shrq	$34, %rax
	leal	(%rax,%rax,4), %eax
	subl	%eax, %edx
	leal	1(%rsi), %eax
	movq	%rax, %rsi
	imulq	%rdi, %rax
	movslq	%edx, %r8
	shrq	$34, %rax
	leal	(%rax,%rax,4), %edx
	movl	%esi, %eax
	subl	%edx, %eax
	cltq
	movq	(%rsp,%rax,8), %rdx
	leaq	-160(%rcx), %rax
	rolq	%rdx
	xorq	(%rsp,%r8,8), %rdx
	xorq	%rdx, -200(%rcx)
.L218:
	xorq	%rdx, (%rax)
	xorq	%rdx, 40(%rax)
	addq	$80, %rax
	cmpq	%rcx, %rax
	jne	.L218
	leaq	8(%rax), %rcx
	cmpl	$5, %esi
	jne	.L215
	leaq	RHO(%rip), %r15
	leaq	48(%rsp), %r14
	xorl	%r13d, %r13d
.L221:
	leal	(%r13,%r13), %esi
	movq	%r15, %r12
	movq	%r14, %r8
	xorl	%edx, %edx
.L220:
	movl	%esi, %eax
	movq	(%r8), %rbp
	addq	$20, %r12
	addq	$40, %r8
	imulq	%rdi, %rax
	shrq	$34, %rax
	leal	(%rax,%rax,4), %ecx
	movl	%esi, %eax
	addl	$3, %esi
	subl	%ecx, %eax
	movl	-20(%r12), %ecx
	leal	(%rax,%rax,4), %eax
	addl	%edx, %eax
	rolq	%cl, %rbp
	addl	$1, %edx
	cltq
	movq	%rbp, 256(%rsp,%rax,8)
	cmpl	$5, %edx
	jne	.L220
	addl	$1, %r13d
	addq	$8, %r14
	addq	$4, %r15
	cmpl	$5, %r13d
	jne	.L221
	leaq	256(%rsp), %r12
	xorl	%r8d, %r8d
.L222:
	movq	8(%r12), %rax
	xorl	%ecx, %ecx
.L223:
	leal	2(%rcx), %edx
	notq	%rax
	movq	%rax, %rsi
	movq	%rdx, %rax
	imulq	%rdi, %rdx
	shrq	$34, %rdx
	leal	(%rdx,%rdx,4), %edx
	subl	%edx, %eax
	addl	%r8d, %eax
	cltq
	movq	256(%rsp,%rax,8), %rax
	andq	%rax, %rsi
	xorq	(%r12,%rcx,8), %rsi
	movq	%rsi, (%r10,%rcx,8)
	addq	$1, %rcx
	cmpq	$5, %rcx
	jne	.L223
	addl	$5, %r8d
	addq	$40, %r12
	addq	$40, %r10
	cmpl	$25, %r8d
	jne	.L222
	movq	48(%rsp), %rax
	addq	$8, %r11
	xorq	-8(%r11), %rax
	leaq	192+RC(%rip), %rsi
	movq	%rax, 48(%rsp)
	cmpq	%r11, %rsi
	jne	.L225
	movb	%al, (%r9)
	movl	$1, %eax
	.p2align 6
	.p2align 4
	.p2align 3
.L226:
	movl	%eax, %edx
	movl	%eax, %ecx
	sarl	$3, %edx
	andl	$7, %ecx
	movslq	%edx, %rdx
	sall	$3, %ecx
	movq	48(%rsp,%rdx,8), %rdx
	shrq	%cl, %rdx
	movb	%dl, (%r9,%rax)
	addq	$1, %rax
	cmpq	$32, %rax
	jne	.L226
	movq	648(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L242
	addq	$664, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L242:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE89:
	.size	leaf_stmt, .-leaf_stmt
	.p2align 4
	.type	run_chain, @function
run_chain:
.LFB7403:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	leaq	k_fn(%rip), %rax
	movq	%rdi, %rsi
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$56, %rsp
	.cfi_def_cfa_offset 80
	movslq	impl(%rip), %rcx
	movq	32(%rdi), %rdx
	movq	%fs:40, %rbx
	movq	%rbx, 40(%rsp)
	movq	%rdi, %rbx
	movq	%rsp, %rdi
	call	*(%rax,%rcx,8)
	movq	%rsp, %rsi
	movq	32(%rbx), %rdx
	leaq	40(%rbx), %rdi
	call	leaf_stmt
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L246
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
.L246:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7403:
	.size	run_chain, .-run_chain
	.section	.rodata.str1.8
	.align 8
.LC66:
	.string	"keccak %s %.1f ns per permutation\n"
	.section	.rodata.str1.1
.LC67:
	.string	"keccak %s not usable here\n"
	.text
	.p2align 4
	.type	chain_select_timed, @function
chain_select_timed:
.LFB7386:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movl	%edi, %r12d
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	movq	%rsi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	xorl	%ebx, %ebx
	subq	$232, %rsp
	.cfi_def_cfa_offset 288
	movdqa	.LC62(%rip), %xmm0
	movq	%rdx, 32(%rsp)
	movq	%fs:40, %rax
	movq	%rax, 216(%rsp)
	xorl	%eax, %eax
	leaq	64(%rsp), %rax
	movaps	%xmm0, 144(%rsp)
	movdqa	.LC63(%rip), %xmm0
	movq	%rax, 16(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 40(%rsp)
	movaps	%xmm0, 160(%rsp)
.L248:
	movl	%ebx, %edi
	call	k_usable
	movq	16(%rsp), %rcx
	movl	%eax, (%rcx,%rbx,4)
	movq	40(%rsp), %rax
	movq	.LC64(%rip), %rcx
	movq	%rcx, (%rax,%rbx,8)
	addq	$1, %rbx
	cmpq	$5, %rbx
	jne	.L248
	movl	$10, %r13d
	cmpl	$5, %r12d
	movl	$16, %eax
	movl	$3435973837, %r15d
	cmove	%r13d, %eax
	movl	$5, %r13d
	movl	%eax, 28(%rsp)
	.p2align 4
	.p2align 3
.L249:
	leal	-5(%r13), %r14d
.L251:
	movl	%r14d, %eax
	imulq	%r15, %rax
	shrq	$34, %rax
	leal	(%rax,%rax,4), %edx
	movl	%r14d, %eax
	subl	%edx, %eax
	movslq	%eax, %r12
	movl	64(%rsp,%r12,4), %eax
	testl	%eax, %eax
	je	.L250
	leaq	48(%rsp), %rsi
	movl	$1, %edi
	call	clock_gettime@PLT
	pxor	%xmm0, %xmm0
	pxor	%xmm1, %xmm1
	movq	%rbp, %rdx
	cvtsi2sdq	48(%rsp), %xmm0
	mulsd	.LC65(%rip), %xmm0
	cvtsi2sdq	56(%rsp), %xmm1
	leaq	k_fn(%rip), %rax
	leaq	144(%rsp), %rsi
	leaq	176(%rsp), %rdi
	addsd	%xmm1, %xmm0
	movsd	%xmm0, 8(%rsp)
	call	*(%rax,%r12,8)
	leaq	48(%rsp), %rsi
	movl	$1, %edi
	call	clock_gettime@PLT
	pxor	%xmm0, %xmm0
	cvtsi2sdq	48(%rsp), %xmm0
	movzbl	176(%rsp), %eax
	mulsd	.LC65(%rip), %xmm0
	pxor	%xmm1, %xmm1
	xorb	%al, 144(%rsp)
	cvtsi2sdq	56(%rsp), %xmm1
	addsd	%xmm1, %xmm0
	subsd	8(%rsp), %xmm0
	minsd	96(%rsp,%r12,8), %xmm0
	movsd	%xmm0, 96(%rsp,%r12,8)
.L250:
	addl	$1, %r14d
	cmpl	%r14d, %r13d
	jne	.L251
	addl	$1, %r13d
	cmpl	28(%rsp), %r13d
	jne	.L249
	movq	40(%rsp), %r13
	xorl	%ebx, %ebx
	xorl	%r12d, %r12d
	leaq	k_name(%rip), %r14
.L261:
	movq	16(%rsp), %rax
	movl	%ebx, %r15d
	movl	(%rax,%rbx,4), %eax
	cmpq	$0, 32(%rsp)
	je	.L253
.L257:
	movq	(%r14,%rbx,8), %rcx
	testl	%eax, %eax
	je	.L254
	movsd	0(%r13), %xmm1
	pxor	%xmm2, %xmm2
	movq	32(%rsp), %rdi
	leaq	.LC66(%rip), %rdx
	cvtsi2sdq	%rbp, %xmm2
	movl	$2, %esi
	movl	$1, %eax
	movapd	%xmm1, %xmm0
	movsd	%xmm1, 8(%rsp)
	divsd	%xmm2, %xmm0
	call	__fprintf_chk@PLT
	movsd	8(%rsp), %xmm1
.L255:
	movslq	%r12d, %rax
	movsd	96(%rsp,%rax,8), %xmm0
	comisd	%xmm1, %xmm0
	cmova	%r15d, %r12d
	addq	$1, %rbx
	addq	$8, %r13
	cmpq	$5, %rbx
	jne	.L261
.L247:
	movq	216(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L278
	addq	$232, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movl	%r12d, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L259:
	.cfi_restore_state
	addq	$2, %rbx
	cmpq	$5, %rbx
	je	.L247
	movq	16(%rsp), %rax
	addq	$16, %r13
	movl	%ebx, %r15d
	movl	(%rax,%rbx,4), %eax
.L253:
	testl	%eax, %eax
	jne	.L258
	leaq	1(%rbx), %rax
	cmpq	$4, %rbx
	je	.L247
	movq	16(%rsp), %rcx
	cmpl	$0, (%rcx,%rax,4)
	je	.L259
	addq	$8, %r13
	movl	%eax, %r15d
	movq	%rax, %rbx
.L258:
	movsd	0(%r13), %xmm1
	jmp	.L255
	.p2align 4,,10
	.p2align 3
.L254:
	movq	32(%rsp), %rdi
	movl	$2, %esi
	xorl	%eax, %eax
	addq	$1, %rbx
	leaq	.LC67(%rip), %rdx
	call	__fprintf_chk@PLT
	cmpq	$5, %rbx
	je	.L247
	movq	16(%rsp), %rax
	addq	$8, %r13
	movl	%ebx, %r15d
	movl	(%rax,%rbx,4), %eax
	jmp	.L257
.L278:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7386:
	.size	chain_select_timed, .-chain_select_timed
	.section	.rodata.str1.1
.LC68:
	.string	"forced"
.LC69:
	.string	"setup"
.LC70:
	.string	"timed"
.LC71:
	.string	"RF_SETUP"
.LC72:
	.string	"%s/keccak"
.LC73:
	.string	"RF_KECCAK"
.LC74:
	.string	"auto"
.LC75:
	.string	"%31s"
	.section	.rodata.str1.8
	.align 8
.LC76:
	.string	"RF_KECCAK names no kernel usable here"
	.section	.rodata.str1.1
.LC77:
	.string	"RF_KECCAK_LOG"
.LC78:
	.string	"prover: keccak %s (%s)\n"
	.text
	.p2align 4
	.type	choose_kernel, @function
choose_kernel:
.LFB7412:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4128
	orq	$0, (%rsp)
	subq	$48, %rsp
	.cfi_def_cfa_offset 4176
	movq	%fs:40, %rdi
	movq	%rdi, 4136(%rsp)
	leaq	.LC71(%rip), %rdi
	call	getenv@PLT
	testq	%rax, %rax
	je	.L280
	leaq	32(%rsp), %rbp
	movq	%rax, %r9
	movl	$4096, %ecx
	xorl	%eax, %eax
	leaq	.LC72(%rip), %r8
	movl	$2, %edx
	movl	$4096, %esi
	movq	%rbp, %rdi
	call	__snprintf_chk@PLT
	leaq	.LC73(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rbx
	testq	%rax, %rax
	je	.L282
	leaq	.LC74(%rip), %rsi
	movq	%rax, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L284
.L282:
	leaq	.LC52(%rip), %rsi
	movq	%rbp, %rdi
	call	fopen@PLT
	pxor	%xmm0, %xmm0
	movq	%rax, %rbx
	movaps	%xmm0, (%rsp)
	movaps	%xmm0, 16(%rsp)
	testq	%rax, %rax
	je	.L283
	movq	%rax, %rdi
	movq	%rsp, %rdx
	leaq	.LC75(%rip), %rsi
	xorl	%eax, %eax
	call	__isoc23_fscanf@PLT
	movq	%rbx, %rdi
	movl	%eax, %r14d
	call	fclose@PLT
	subl	$1, %r14d
	je	.L288
	movl	$-1, %edi
	call	k_usable
	testl	%eax, %eax
	jne	.L312
.L283:
	xorl	%edx, %edx
	movl	$5000, %esi
	movl	$5, %edi
	call	chain_select_timed
	leaq	.LC70(%rip), %rbp
	movslq	%eax, %rbx
	movl	%ebx, impl(%rip)
.L290:
	leaq	.LC77(%rip), %rdi
	call	getenv@PLT
	testq	%rax, %rax
	je	.L279
	leaq	k_name(%rip), %rax
	movq	%rbp, %r8
	movq	stderr(%rip), %rdi
	leaq	.LC78(%rip), %rdx
	movq	(%rax,%rbx,8), %rcx
	movl	$2, %esi
	xorl	%eax, %eax
	call	__fprintf_chk@PLT
.L279:
	movq	4136(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L314
	addq	$4144, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L288:
	.cfi_restore_state
	movq	%rsp, %rdi
	leaq	.LC69(%rip), %rbp
	call	k_find
	movslq	%eax, %rbx
	movl	%ebx, %edi
	call	k_usable
	testl	%eax, %eax
	je	.L283
	jmp	.L285
.L312:
	movl	$-1, impl(%rip)
.L289:
	leaq	.LC76(%rip), %rdi
	call	die
.L280:
	leaq	.LC73(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rbx
	testq	%rax, %rax
	je	.L283
	leaq	.LC74(%rip), %rsi
	movq	%rax, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L283
.L284:
	movq	%rbx, %rdi
	call	k_find
	movslq	%eax, %rbx
	movl	%ebx, %edi
	call	k_usable
	testl	%eax, %eax
	je	.L312
	leaq	.LC68(%rip), %rbp
.L285:
	movl	%ebx, impl(%rip)
	cmpl	$-1, %ebx
	jne	.L290
	jmp	.L289
.L314:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7412:
	.size	choose_kernel, .-choose_kernel
	.p2align 4
	.type	readfile, @function
readfile:
.LFB7392:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	movq	%rdi, %r14
	movq	%rsi, %rdi
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$184, %rsp
	.cfi_def_cfa_offset 240
	movq	%rsi, 8(%rsp)
	xorl	%esi, %esi
	movq	%fs:40, %rax
	movq	%rax, 168(%rsp)
	xorl	%eax, %eax
	call	open@PLT
	testl	%eax, %eax
	js	.L317
	leaq	16(%rsp), %rsi
	movl	%eax, %edi
	movl	%eax, %r13d
	call	fstat@PLT
	testl	%eax, %eax
	jne	.L317
	movq	64(%rsp), %rax
	addq	$2, %rax
	je	.L329
	movl	$4096, %ebx
	cmpq	$4096, %rax
	jbe	.L319
	.p2align 3
	.p2align 4
	.p2align 3
.L320:
	addq	%rbx, %rbx
	cmpq	%rax, %rbx
	jb	.L320
.L319:
	movq	%rbx, %rdi
	call	malloc@PLT
	movq	%rax, %r12
	testq	%rax, %rax
	je	.L325
.L318:
	xorl	%r15d, %r15d
	jmp	.L327
	.p2align 4,,10
	.p2align 3
.L321:
	movq	%rbx, %rdx
	leaq	(%r12,%r15), %rbp
	movl	%r13d, %edi
	subq	%r15, %rdx
	movq	%rbp, %rsi
	subq	$1, %rdx
	call	read@PLT
	testq	%rax, %rax
	js	.L317
	je	.L326
	addq	%rax, %r15
.L327:
	leaq	1(%r15), %rax
	cmpq	%rbx, %rax
	jne	.L321
	leaq	65537(%r15), %rax
	cmpq	%rax, %rbx
	jnb	.L321
	testq	%rbx, %rbx
	jne	.L324
	movl	$4096, %ebx
	cmpq	$4096, %rax
	je	.L323
	.p2align 3
	.p2align 4
	.p2align 3
.L324:
	addq	%rbx, %rbx
	cmpq	%rax, %rbx
	jb	.L324
.L323:
	movq	%r12, %rdi
	movq	%rbx, %rsi
	call	realloc@PLT
	movq	%rax, %r12
	testq	%rax, %rax
	jne	.L321
.L325:
	leaq	.LC61(%rip), %rdi
	call	die
	.p2align 4,,10
	.p2align 3
.L326:
	movl	%r13d, %edi
	call	close@PLT
	movb	$0, 0(%rbp)
	movq	%r12, (%r14)
	movq	%r15, 8(%r14)
	movq	%rbx, 16(%r14)
	movq	168(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L339
	addq	$184, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%r14, %rax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L329:
	.cfi_restore_state
	xorl	%ebx, %ebx
	xorl	%r12d, %r12d
	jmp	.L318
.L317:
	movq	8(%rsp), %rdi
	call	die
.L339:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7392:
	.size	readfile, .-readfile
	.section	.rodata.str1.1
.LC79:
	.string	"\"n\":"
.LC80:
	.string	"\"start\":"
.LC81:
	.string	"%2x"
	.text
	.p2align 4
	.type	parse_chain_file, @function
parse_chain_file:
.LFB7402:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$72, %rsp
	.cfi_def_cfa_offset 128
	movq	%rdi, 8(%rsp)
	movq	%rsi, (%rsp)
	movq	%fs:40, %rsi
	movq	%rsi, 56(%rsp)
	movq	%rdi, %rsi
	leaq	32(%rsp), %rdi
	call	readfile
	movq	32(%rsp), %r13
	leaq	.LC79(%rip), %rsi
	movq	%r13, %rdi
	call	strstr@PLT
	leaq	.LC80(%rip), %rsi
	movq	%r13, %rdi
	movq	%rax, %r12
	call	strstr@PLT
	testq	%r12, %r12
	je	.L343
	testq	%rax, %rax
	je	.L343
	leaq	8(%rax), %rdi
	movl	$34, %esi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L343
	movq	(%rsp), %r15
	leaq	1(%rax), %r14
	leaq	65(%rax), %rbx
	leaq	28(%rsp), %rbp
	.p2align 4
	.p2align 3
.L345:
	xorl	%eax, %eax
	movq	%rbp, %rdx
	leaq	.LC81(%rip), %rsi
	movq	%r14, %rdi
	call	__isoc23_sscanf@PLT
	cmpl	$1, %eax
	jne	.L343
	movl	28(%rsp), %eax
	addq	$2, %r14
	addq	$1, %r15
	movb	%al, -1(%r15)
	cmpq	%rbx, %r14
	jne	.L345
	leaq	4(%r12), %rdi
	movl	$10, %edx
	xorl	%esi, %esi
	call	__isoc23_strtoull@PLT
	movq	(%rsp), %rcx
	movq	%rax, 32(%rcx)
	movq	56(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L353
	addq	$72, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%r13, %rdi
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	jmp	free@PLT
	.p2align 4,,10
	.p2align 3
.L343:
	.cfi_restore_state
	movq	8(%rsp), %rdi
	call	die
.L353:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7402:
	.size	parse_chain_file, .-parse_chain_file
	.section	.rodata.str1.1
.LC82:
	.string	"chainB.json"
	.text
	.p2align 4
	.type	chain_thread, @function
chain_thread:
.LFB7411:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdi, %rsi
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$56, %rsp
	.cfi_def_cfa_offset 80
	movq	%fs:40, %rbx
	movq	%rbx, 40(%rsp)
	movq	%rdi, %rbx
	leaq	.LC82(%rip), %rdi
	call	parse_chain_file
	movslq	impl(%rip), %rcx
	leaq	k_fn(%rip), %rax
	movq	%rsp, %rdi
	movq	32(%rbx), %rdx
	movq	%rbx, %rsi
	call	*(%rax,%rcx,8)
	movq	32(%rbx), %rdx
	leaq	40(%rbx), %rdi
	movq	%rsp, %rsi
	call	leaf_stmt
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L357
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
.L357:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7411:
	.size	chain_thread, .-chain_thread
	.section	.rodata.str1.1
.LC83:
	.string	"chainA.json"
.LC84:
	.string	"done"
	.text
	.p2align 4
	.type	mode_first.isra.0, @function
mode_first.isra.0:
.LFB7425:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	movl	$14, %ecx
	pxor	%xmm0, %xmm0
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$416, %rsp
	.cfi_def_cfa_offset 448
	movq	%fs:40, %rax
	movq	%rax, 408(%rsp)
	xorl	%eax, %eax
	leaq	224(%rsp), %rbx
	leaq	16(%rsp), %rbp
	movl	$0, 52(%rsp)
	movq	%rbx, %rdi
	leaq	144(%rsp), %r12
	movups	%xmm0, 20(%rsp)
	movl	$1, 16(%rsp)
	movups	%xmm0, 36(%rsp)
	rep stosq
	leaq	prep_thread(%rip), %rax
	movq	%rbp, 264(%rsp)
	movq	%rax, 256(%rsp)
	leaq	chain_thread(%rip), %rax
	movq	%rax, 312(%rsp)
	movq	%r12, 320(%rsp)
	call	choose_kernel
	movl	impl(%rip), %eax
	subl	$3, %eax
	cmpl	$1, %eax
	jbe	.L363
	movq	%rbx, %rdi
	movl	$2, %esi
	leaq	104(%rsp), %rbx
	call	handshake
	leaq	64(%rsp), %rsi
	leaq	.LC83(%rip), %rdi
	call	parse_chain_file
	leaq	64(%rsp), %rdi
	leaq	184(%rsp), %r12
	call	run_chain
	movq	328(%rsp), %rdi
	xorl	%esi, %esi
	call	pthread_join@PLT
.L360:
	movq	272(%rsp), %rdi
	xorl	%esi, %esi
	call	pthread_join@PLT
	movq	%r12, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	finish_proof
	leaq	.LC84(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	408(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L364
	addq	$416, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.L363:
	.cfi_restore_state
	movq	%rbx, %rdi
	movl	$1, %esi
	call	handshake
	leaq	64(%rsp), %rsi
	leaq	.LC83(%rip), %rdi
	call	parse_chain_file
	movq	%r12, %rsi
	leaq	.LC82(%rip), %rdi
	call	parse_chain_file
	leaq	368(%rsp), %r8
	leaq	64(%rsp), %rdx
	movl	impl(%rip), %edi
	leaq	336(%rsp), %rsi
	pushq	%rax
	.cfi_def_cfa_offset 456
	movq	%r12, %r9
	pushq	184(%rsp)
	.cfi_def_cfa_offset 464
	movq	112(%rsp), %rcx
	movq	%r8, 24(%rsp)
	leaq	120(%rsp), %rbx
	leaq	200(%rsp), %r12
	movq	%rsi, 16(%rsp)
	call	chain_two
	movq	112(%rsp), %rdx
	movq	16(%rsp), %rsi
	movq	%rbx, %rdi
	call	leaf_stmt
	movq	192(%rsp), %rdx
	movq	24(%rsp), %rsi
	movq	%r12, %rdi
	call	leaf_stmt
	popq	%rdx
	.cfi_def_cfa_offset 456
	popq	%rcx
	.cfi_def_cfa_offset 448
	jmp	.L360
.L364:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7425:
	.size	mode_first.isra.0, .-mode_first.isra.0
	.p2align 4
	.type	app64, @function
app64:
.LFB7391:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	xorl	%ecx, %ecx
	subq	$16, %rsp
	.cfi_def_cfa_offset 32
	movq	%fs:40, %rbx
	movq	%rbx, 8(%rsp)
	movq	%rdi, %rbx
	movq	%rsp, %rax
	.p2align 5
	.p2align 4
	.p2align 3
.L366:
	movq	%rsi, %rdx
	addq	$1, %rax
	shrq	%cl, %rdx
	addl	$8, %ecx
	movb	%dl, -1(%rax)
	cmpl	$64, %ecx
	jne	.L366
	movl	$8, %esi
	movq	%rbx, %rdi
	call	reserve
	movq	8(%rbx), %rax
	movq	(%rbx), %rdx
	movq	(%rsp), %rcx
	movq	%rcx, (%rdx,%rax)
	addq	$8, 8(%rbx)
	movq	8(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L370
	addq	$16, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	ret
.L370:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7391:
	.size	app64, .-app64
	.p2align 4
	.type	ws_leaf, @function
ws_leaf:
.LFB7397:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	movq	%rsi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	movq	%rdi, %rbp
	movl	$4096, %edi
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$16, %rsp
	.cfi_def_cfa_offset 48
	movq	%fs:40, %rbx
	movq	%rbx, 8(%rsp)
	movq	%rdx, %rbx
	call	malloc@PLT
	testq	%rax, %rax
	je	.L377
	movdqu	(%r12), %xmm0
	movq	$0, (%rax)
	movq	%rax, %rsi
	xorl	%ecx, %ecx
	movups	%xmm0, 8(%rax)
	movdqu	16(%r12), %xmm0
	movups	%xmm0, 24(%rax)
	movq	%rsp, %rax
	.p2align 5
	.p2align 4
	.p2align 3
.L373:
	movq	%rbx, %rdx
	addq	$1, %rax
	shrq	%cl, %rdx
	addl	$8, %ecx
	movb	%dl, -1(%rax)
	cmpl	$64, %ecx
	jne	.L373
	movq	(%rsp), %rax
	movdqa	.LC85(%rip), %xmm0
	movq	%rsi, 0(%rbp)
	movq	%rax, 40(%rsi)
	movups	%xmm0, 8(%rbp)
	movq	8(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L378
	addq	$16, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	movq	%rbp, %rax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.L377:
	.cfi_restore_state
	leaq	.LC61(%rip), %rdi
	call	die
.L378:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7397:
	.size	ws_leaf, .-ws_leaf
	.section	.rodata.str1.1
.LC86:
	.string	"RF_ORACLE"
.LC87:
	.string	"RF_ORACLE unset"
	.section	.rodata.str1.8
	.align 8
.LC88:
	.string	"cannot connect to the oracle service"
	.section	.rodata.str1.1
.LC89:
	.string	"SIGN write"
.LC90:
	.string	"SIGN read"
.LC91:
	.string	"SIGN refused"
	.text
	.p2align 4
	.type	signed_file.isra.0, @function
signed_file.isra.0:
.LFB7427:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4152
	orq	$0, (%rsp)
	subq	$856, %rsp
	.cfi_def_cfa_offset 5008
	movq	%rdi, (%rsp)
	movl	svc(%rip), %edi
	movq	%rdx, %r12
	movq	%rsi, 8(%rsp)
	movq	%fs:40, %rbp
	movq	%rbp, 4936(%rsp)
	xorl	%ebp, %ebp
	testl	%edi, %edi
	js	.L441
.L381:
	leaq	144(%rsp), %rbx
	movl	$16, %edx
	movq	$2, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	%rbx, %rsi
	call	write@PLT
	cmpq	$16, %rax
	jne	.L442
	xorl	%ebp, %ebp
	.p2align 4
	.p2align 3
.L385:
	movl	$16, %edx
	movl	svc(%rip), %edi
	leaq	(%rbx,%rbp), %rsi
	subq	%rbp, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L390
	addq	%rax, %rbp
	cmpq	$15, %rbp
	jbe	.L385
	cmpb	$0, 144(%rsp)
	jne	.L387
	movq	%rbx, %rdx
	leaq	136(%rsp), %rbp
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L388:
	movzbl	15(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rbp
	jne	.L388
	cmpq	$4772, %rax
	jne	.L387
	xorl	%r15d, %r15d
	leaq	160(%rsp), %r14
	.p2align 4
	.p2align 3
.L389:
	movl	$4772, %edx
	movl	svc(%rip), %edi
	leaq	(%r14,%r15), %rsi
	subq	%r15, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L390
	addq	%rax, %r15
	cmpq	$4771, %r15
	jbe	.L389
	movq	%r12, %rax
	addq	$4797, %rax
	je	.L411
	movl	$4096, %r13d
	cmpq	$4096, %rax
	jbe	.L392
	.p2align 3
	.p2align 4
	.p2align 3
.L393:
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L393
.L392:
	movq	%r13, %rdi
	call	malloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
.L391:
	xorl	%ecx, %ecx
	.p2align 5
	.p2align 4
	.p2align 3
.L394:
	movq	%r12, %rax
	addq	$1, %rbx
	shrq	%cl, %rax
	addl	$8, %ecx
	movb	%al, -1(%rbx)
	cmpl	$64, %ecx
	jne	.L394
	cmpq	$8, %r13
	ja	.L443
	movq	%r14, %rdi
	movl	$4096, %esi
	call	realloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
	movq	144(%rsp), %rax
	leaq	8(%r12), %rbx
	movl	$4096, %r13d
	movq	%rax, (%r14)
	leaq	9(%r12), %rax
	cmpq	$4096, %rax
	jbe	.L396
	.p2align 3
	.p2align 4
	.p2align 3
.L399:
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L399
.L446:
	movq	%r14, %rdi
	movq	%r13, %rsi
	call	realloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
.L396:
	movq	8(%rsp), %rsi
	leaq	8(%r14), %rdi
	movq	%r12, %rdx
	call	memcpy@PLT
	leaq	17(%r12), %rax
	cmpq	%rax, %r13
	jnb	.L400
	.p2align 3
	.p2align 4
	.p2align 3
.L401:
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L401
	movq	%r14, %rdi
	movq	%r13, %rsi
	call	realloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
.L400:
	movq	$0, (%r14,%rbx)
	movl	160(%rsp), %edx
	xorl	%ecx, %ecx
	.p2align 5
	.p2align 4
	.p2align 3
.L402:
	movq	%rdx, %rax
	addq	$1, %rbp
	shrq	%cl, %rax
	addl	$8, %ecx
	movb	%al, -1(%rbp)
	cmpl	$64, %ecx
	jne	.L402
	leaq	25(%r12), %rax
	cmpq	%rax, %r13
	jnb	.L403
	.p2align 3
	.p2align 4
	.p2align 3
.L404:
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L404
	movq	%r14, %rdi
	movq	%r13, %rsi
	call	realloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
.L403:
	movq	136(%rsp), %rax
	leaq	24(%r12), %rbx
	movq	%rax, 16(%r14,%r12)
	leaq	4793(%r12), %rax
	cmpq	%rax, %r13
	jnb	.L405
	.p2align 3
	.p2align 4
	.p2align 3
.L407:
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L407
	movq	%r14, %rdi
	movq	%r13, %rsi
	call	realloc@PLT
	movq	%rax, %r14
	testq	%rax, %rax
	je	.L398
.L405:
	movq	164(%rsp), %rax
	leaq	(%r14,%rbx), %rcx
	leaq	164(%rsp), %rsi
	addq	$4792, %r12
	leaq	8(%rcx), %rdi
	movq	%rax, (%rcx)
	movq	4924(%rsp), %rax
	andq	$-8, %rdi
	movq	%rax, 4760(%rcx)
	subq	%rdi, %rcx
	subq	%rcx, %rsi
	addl	$4768, %ecx
	shrl	$3, %ecx
	rep movsq
	movq	(%rsp), %rax
	movq	%r14, (%rax)
	movq	%r12, 8(%rax)
	movq	%r13, 16(%rax)
	movq	4936(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L444
	movq	(%rsp), %rax
	addq	$4952, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L441:
	.cfi_restore_state
	leaq	.LC86(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.L445
	leaq	24(%rsp), %rdi
	leaq	18(%rsp), %rcx
	movq	%rbp, %rax
	movq	$0, 18(%rsp)
	subq	%rdi, %rcx
	movl	$107, %edx
	movq	$0, 118(%rsp)
	addl	$108, %ecx
	shrl	$3, %ecx
	rep stosq
	movl	$1, %eax
	leaq	18(%rsp), %rdi
	movw	%ax, 16(%rsp)
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, svc(%rip)
	testl	%eax, %eax
	js	.L384
	movl	$110, %edx
	leaq	16(%rsp), %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	jne	.L384
	movl	svc(%rip), %edi
	jmp	.L381
	.p2align 4,,10
	.p2align 3
.L443:
	movq	144(%rsp), %rax
	leaq	8(%r12), %rbx
	movq	%rax, (%r14)
	leaq	9(%r12), %rax
	cmpq	%rax, %r13
	jnb	.L396
	addq	%r13, %r13
	cmpq	%rax, %r13
	jb	.L399
	jmp	.L446
	.p2align 4,,10
	.p2align 3
.L411:
	xorl	%r13d, %r13d
	xorl	%r14d, %r14d
	jmp	.L391
.L390:
	leaq	.LC90(%rip), %rdi
	call	die
.L398:
	leaq	.LC61(%rip), %rdi
	call	die
.L444:
	call	__stack_chk_fail@PLT
.L387:
	leaq	.LC91(%rip), %rdi
	call	die
.L442:
	leaq	.LC89(%rip), %rdi
	call	die
.L445:
	leaq	.LC87(%rip), %rdi
	call	die
.L384:
	leaq	.LC88(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7427:
	.size	signed_file.isra.0, .-signed_file.isra.0
	.section	.rodata.str1.1
.LC92:
	.string	"malformed child file"
	.section	.rodata.str1.8
	.align 8
.LC93:
	.string	"trailing bytes in a child file"
	.text
	.p2align 4
	.type	app_signed_words.isra.0, @function
app_signed_words.isra.0:
.LFB7428:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	movq	%fs:40, %rax
	movq	%rax, 40(%rsp)
	xorl	%eax, %eax
	cmpq	$7, %rdx
	jbe	.L450
	movq	%rdi, %r15
	movq	%rsi, %rbx
	movq	%rdx, %r12
	xorl	%r14d, %r14d
	leaq	7(%rsi), %rax
	leaq	-1(%rsi), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L449:
	movzbl	(%rax), %edx
	salq	$8, %r14
	subq	$1, %rax
	orq	%rdx, %r14
	cmpq	%rcx, %rax
	jne	.L449
	leaq	-8(%r12), %r13
	cmpq	%r14, %r13
	jb	.L450
	movq	%r14, %rsi
	movq	%r15, %rdi
	movq	%r14, %rbp
	call	app64
	movq	%r14, %rsi
	movq	%r15, %rdi
	negq	%rbp
	call	reserve
	movq	8(%r15), %rdi
	leaq	8(%rbx), %rsi
	addq	(%r15), %rdi
	movq	%r14, %rdx
	andl	$7, %ebp
	call	memcpy@PLT
	addq	%r14, 8(%r15)
	movq	%rbp, %rsi
	movq	%r15, %rdi
	call	reserve
	movq	8(%r15), %rax
	addq	(%r15), %rax
	testl	%ebp, %ebp
	je	.L452
	xorl	%edx, %edx
.L451:
	movl	%edx, %ecx
	leaq	ZERO8(%rip), %rdi
	addl	$1, %edx
	movzbl	(%rdi,%rcx), %esi
	movb	%sil, (%rax,%rcx)
	cmpl	%ebp, %edx
	jb	.L451
.L452:
	subq	%r14, %r13
	addq	%rbp, 8(%r15)
	cmpq	$7, %r13
	jbe	.L450
	leaq	-8(%rbx), %rdi
	leaq	(%rbx,%r14), %rax
	movq	$0, 16(%rsp)
	movq	%rdi, 24(%rsp)
	leaq	(%r14,%rdi), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L453:
	movq	16(%rsp), %r13
	movzbl	15(%rax), %edx
	subq	$1, %rax
	salq	$8, %r13
	orq	%r13, %rdx
	movq	%rdx, 16(%rsp)
	cmpq	%rax, %rcx
	jne	.L453
	movq	%rdx, %rbp
	movq	%rdx, %rsi
	movq	%r15, %rdi
	addq	$16, %r14
	call	app64
	testq	%rbp, %rbp
	je	.L454
	xorl	%ebp, %ebp
	.p2align 4
	.p2align 3
.L459:
	movq	%r12, %rax
	subq	%r14, %rax
	cmpq	$7, %rax
	jbe	.L450
	movq	24(%rsp), %rdi
	leaq	(%rbx,%r14), %rax
	xorl	%edx, %edx
	leaq	(%r14,%rdi), %rsi
	.p2align 5
	.p2align 4
	.p2align 3
.L455:
	movzbl	7(%rax), %ecx
	salq	$8, %rdx
	subq	$1, %rax
	orq	%rcx, %rdx
	cmpq	%rax, %rsi
	jne	.L455
	leaq	8(%r14), %r13
	movq	%r12, %rax
	subq	%r13, %rax
	cmpq	%rdx, %rax
	jb	.L450
	leaq	(%rbx,%r13), %r14
	leaq	32(%rsp), %rax
	xorl	%ecx, %ecx
	.p2align 5
	.p2align 4
	.p2align 3
.L456:
	movq	%rdx, %rsi
	addq	$1, %rax
	shrq	%cl, %rsi
	addl	$8, %ecx
	movb	%sil, -1(%rax)
	cmpl	$64, %ecx
	jne	.L456
	movl	$8, %esi
	movq	%r15, %rdi
	movq	%rdx, 8(%rsp)
	call	reserve
	movq	(%r15), %rcx
	movq	8(%r15), %rax
	movq	%r15, %rdi
	movq	32(%rsp), %rsi
	movq	%rsi, (%rcx,%rax)
	movq	8(%rsp), %rsi
	addq	$8, 8(%r15)
	call	reserve
	movq	8(%rsp), %rdx
	movq	%r14, %rsi
	movq	8(%r15), %rdi
	addq	(%r15), %rdi
	call	memcpy@PLT
	movq	8(%rsp), %rdx
	addq	%rdx, 8(%r15)
	movq	%r15, %rdi
	movq	%rdx, %r14
	negq	%r14
	andl	$7, %r14d
	movq	%r14, %rsi
	call	reserve
	movq	8(%r15), %rax
	addq	(%r15), %rax
	testl	%r14d, %r14d
	movq	8(%rsp), %rdx
	movq	%rax, %rcx
	je	.L458
	xorl	%eax, %eax
.L457:
	movl	%eax, %esi
	leaq	ZERO8(%rip), %rdi
	addl	$1, %eax
	movzbl	(%rdi,%rsi), %edi
	movb	%dil, (%rcx,%rsi)
	cmpl	%r14d, %eax
	jb	.L457
.L458:
	addq	%r14, 8(%r15)
	movq	%r12, %rax
	leaq	(%rdx,%r13), %r14
	subq	%r14, %rax
	cmpq	$31, %rax
	jbe	.L450
	leaq	(%rbx,%r14), %r13
	movl	$32, %esi
	movq	%r15, %rdi
	addq	$32, %r14
	call	reserve
	movdqu	0(%r13), %xmm0
	movq	8(%r15), %rax
	addq	$1, %rbp
	addq	(%r15), %rax
	movups	%xmm0, (%rax)
	movdqu	16(%r13), %xmm0
	movups	%xmm0, 16(%rax)
	addq	$32, 8(%r15)
	cmpq	%rbp, 16(%rsp)
	jne	.L459
.L454:
	movq	%r12, %rax
	subq	%r14, %rax
	cmpq	$4775, %rax
	jbe	.L450
	addq	%r14, %rbx
	movl	$4776, %esi
	movq	%r15, %rdi
	call	reserve
	movq	(%rbx), %rdx
	movq	8(%r15), %rax
	leaq	4776(%r14), %r9
	addq	(%r15), %rax
	movq	%rdx, (%rax)
	leaq	8(%rax), %rdi
	movq	4768(%rbx), %rdx
	andq	$-8, %rdi
	movq	%rdx, 4768(%rax)
	subq	%rdi, %rax
	subq	%rax, %rbx
	leal	4776(%rax), %ecx
	movq	%rbx, %rsi
	shrl	$3, %ecx
	rep movsq
	addq	$4776, 8(%r15)
	cmpq	%r12, %r9
	jne	.L473
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L474
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L450:
	.cfi_restore_state
	leaq	.LC92(%rip), %rdi
	call	die
.L473:
	leaq	.LC93(%rip), %rdi
	call	die
.L474:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7428:
	.size	app_signed_words.isra.0, .-app_signed_words.isra.0
	.section	.rodata.str1.1
.LC94:
	.string	"chain.json"
.LC95:
	.string	"prev.stmt"
.LC96:
	.string	"prev.bin"
	.text
	.p2align 4
	.type	prep_thread, @function
prep_thread:
.LFB7410:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$472, %rsp
	.cfi_def_cfa_offset 528
	movl	(%rdi), %eax
	movq	%fs:40, %rbp
	movq	%rbp, 456(%rsp)
	movq	%rdi, %rbp
	testl	%eax, %eax
	je	.L476
	leaq	256(%rsp), %rsi
	leaq	.LC83(%rip), %rdi
	call	parse_chain_file
	leaq	336(%rsp), %rsi
	leaq	.LC82(%rip), %rdi
	call	parse_chain_file
	movq	288(%rsp), %rdx
	leaq	128(%rsp), %rdi
	leaq	256(%rsp), %rsi
	call	ws_leaf
	movq	136(%rsp), %rdx
	leaq	32(%rsp), %rdi
	movq	128(%rsp), %rsi
	call	signed_file.isra.0
	movq	368(%rsp), %rdx
	leaq	160(%rsp), %rdi
	leaq	336(%rsp), %rsi
	call	ws_leaf
	movq	168(%rsp), %rdx
	leaq	64(%rsp), %rdi
	movq	160(%rsp), %rsi
	call	signed_file.isra.0
.L477:
	movq	32(%rsp), %rax
	movq	40(%rsp), %r13
	pxor	%xmm0, %xmm0
	movq	72(%rsp), %r12
	movaps	%xmm0, 416(%rsp)
	movq	%rax, 8(%rsp)
	movq	64(%rsp), %rax
	movaps	%xmm0, 432(%rsp)
	movq	%rax, 16(%rsp)
	leaq	137(%r13,%r12), %rax
	testq	%rax, %rax
	je	.L499
	movl	$4096, %ebx
	cmpq	$4096, %rax
	jbe	.L482
	.p2align 3
	.p2align 4
	.p2align 3
.L483:
	addq	%rbx, %rbx
	cmpq	%rax, %rbx
	jb	.L483
.L482:
	movq	%rbx, %rdi
	call	malloc@PLT
	testq	%rax, %rax
	je	.L488
.L481:
	leaq	224(%rsp), %rdi
	movl	$1, %esi
	movq	%rax, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	%rbx, 240(%rsp)
	call	app64
	movq	232(%rsp), %r15
	movq	240(%rsp), %r14
	movq	224(%rsp), %rdi
	leaq	33(%r15), %rax
	cmpq	%rax, %r14
	jnb	.L484
	testq	%r14, %r14
	je	.L518
	.p2align 3
	.p2align 4
	.p2align 3
.L487:
	addq	%r14, %r14
	cmpq	%rax, %r14
	jb	.L487
.L486:
	movq	%r14, %rsi
	call	realloc@PLT
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.L488
	movdqa	416(%rsp), %xmm0
	movq	432(%rsp), %r10
	leaq	32(%r15), %r8
	movq	440(%rsp), %r11
	movq	%r10, 16(%rax,%r15)
	movq	%r11, 24(%rax,%r15)
	movups	%xmm0, (%rax,%r15)
	leaq	65(%r15), %rax
	cmpq	%rax, %r14
	jnb	.L489
	.p2align 3
	.p2align 4
	.p2align 3
.L492:
	addq	%r14, %r14
	cmpq	%rax, %r14
	jb	.L492
.L491:
	movq	%r14, %rsi
	movq	%r8, 24(%rsp)
	call	realloc@PLT
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.L488
	movdqa	416(%rsp), %xmm0
	movq	432(%rsp), %r10
	movq	440(%rsp), %r11
	movq	24(%rsp), %r8
.L489:
	movq	%r10, 16(%rdi,%r8)
	movq	8(%rsp), %rsi
	leaq	64(%r15), %rcx
	movq	%r13, %rdx
	movq	%r11, 24(%rdi,%r8)
	movups	%xmm0, (%rdi,%r8)
	movq	%rdi, 224(%rsp)
	leaq	224(%rsp), %rdi
	movq	%rcx, 232(%rsp)
	movq	%r14, 240(%rsp)
	call	app_signed_words.isra.0
	movq	16(%rsp), %rsi
	movq	%r12, %rdx
	leaq	224(%rsp), %rdi
	call	app_signed_words.isra.0
	movq	232(%rsp), %rdx
	leaq	96(%rsp), %rdi
	movq	224(%rsp), %rsi
	call	signed_file.isra.0
	movl	$420, %edx
	movl	$577, %esi
	xorl	%eax, %eax
	leaq	.LC59(%rip), %rdi
	call	open@PLT
	movl	%eax, 4(%rbp)
	movl	%eax, %r12d
	testl	%eax, %eax
	js	.L495
	movq	104(%rsp), %rbx
	testq	%rbx, %rbx
	je	.L494
	movq	96(%rsp), %rbp
	.p2align 4
	.p2align 3
.L496:
	movq	%rbx, %rdx
	movq	%rbp, %rsi
	movl	%r12d, %edi
	call	write@PLT
	testq	%rax, %rax
	jle	.L495
	addq	%rax, %rbp
	subq	%rax, %rbx
	jne	.L496
.L494:
	movq	456(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L519
	addq	$472, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L476:
	.cfi_restore_state
	leaq	336(%rsp), %rax
	leaq	.LC94(%rip), %rdi
	movq	%rax, %rsi
	movq	%rax, 8(%rsp)
	call	parse_chain_file
	leaq	224(%rsp), %rdi
	leaq	.LC95(%rip), %rsi
	call	readfile
	cmpq	$63, 232(%rsp)
	jbe	.L478
	movq	224(%rsp), %r14
	leaq	8(%rbp), %r15
	movq	%r14, %rbx
	leaq	64(%r14), %r13
	.p2align 4
	.p2align 3
.L480:
	xorl	%eax, %eax
	leaq	192(%rsp), %rdx
	leaq	.LC81(%rip), %rsi
	movq	%rbx, %rdi
	call	__isoc23_sscanf@PLT
	cmpl	$1, %eax
	jne	.L478
	movl	192(%rsp), %eax
	addq	$2, %rbx
	addq	$1, %r15
	movb	%al, -1(%r15)
	cmpq	%rbx, %r13
	jne	.L480
	movq	%r14, %rdi
	call	free@PLT
	leaq	32(%rsp), %rdi
	leaq	.LC96(%rip), %rsi
	call	readfile
	movq	368(%rsp), %rdx
	movq	8(%rsp), %rsi
	leaq	192(%rsp), %rdi
	call	ws_leaf
	movq	200(%rsp), %rdx
	leaq	64(%rsp), %rdi
	movq	192(%rsp), %rsi
	call	signed_file.isra.0
	jmp	.L477
	.p2align 4,,10
	.p2align 3
.L518:
	movl	$4096, %r14d
	cmpq	$4096, %rax
	jbe	.L486
	addq	%r14, %r14
	cmpq	%rax, %r14
	jb	.L487
	jmp	.L486
	.p2align 4,,10
	.p2align 3
.L484:
	movq	432(%rsp), %r10
	movq	440(%rsp), %r11
	leaq	65(%r15), %rax
	leaq	32(%r15), %r8
	movdqa	416(%rsp), %xmm0
	movq	%r10, 16(%rdi,%r15)
	movq	%r11, 24(%rdi,%r15)
	movups	%xmm0, (%rdi,%r15)
	cmpq	%rax, %r14
	jnb	.L489
	testq	%r14, %r14
	jne	.L492
	movl	$4096, %r14d
	cmpq	$4096, %rax
	jbe	.L491
	addq	%r14, %r14
	cmpq	%rax, %r14
	jb	.L492
	jmp	.L491
	.p2align 4,,10
	.p2align 3
.L499:
	xorl	%ebx, %ebx
	xorl	%eax, %eax
	jmp	.L481
.L495:
	leaq	.LC59(%rip), %rdi
	call	die
.L519:
	call	__stack_chk_fail@PLT
.L478:
	leaq	.LC95(%rip), %rdi
	call	die
.L488:
	leaq	.LC61(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7410:
	.size	prep_thread, .-prep_thread
	.section	.rodata.str1.8
	.align 8
.LC97:
	.string	"keccak: cannot write DIR/keccak (requests will time the kernels): %s\n"
	.section	.rodata.str1.1
.LC98:
	.string	"keccak chosen: %s\n"
	.section	.rodata.str1.8
	.align 8
.LC99:
	.string	"usage: prover setup|first|step DIR"
	.section	.rodata.str1.1
.LC100:
	.string	"cannot enter DIR"
.LC101:
	.string	"w"
.LC102:
	.string	"keccak"
.LC103:
	.string	"%s\n"
.LC104:
	.string	"first"
.LC105:
	.string	"step"
.LC106:
	.string	"unknown mode"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB7419:
	.cfi_startproc
	endbr64
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$192, %rsp
	.cfi_def_cfa_offset 224
	movq	%fs:40, %rax
	movq	%rax, 184(%rsp)
	xorl	%eax, %eax
	cmpl	$3, %edi
	jne	.L532
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L533
	movq	8(%rbx), %rbx
	leaq	.LC69(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L534
	leaq	.LC104(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L535
	leaq	.LC105(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L529
	movq	%rsp, %rdi
	movl	$10, %ecx
	leaq	112(%rsp), %rbp
	rep stosl
	leaq	48(%rsp), %rdi
	movl	$14, %ecx
	rep stosl
	leaq	prep_thread(%rip), %rax
	movq	%rsp, 88(%rsp)
	movq	%rax, 80(%rsp)
	call	choose_kernel
	leaq	48(%rsp), %rdi
	movl	$1, %esi
	call	handshake
	movq	%rbp, %rsi
	leaq	.LC94(%rip), %rdi
	call	parse_chain_file
	movq	%rbp, %rdi
	call	run_chain
	movq	96(%rsp), %rdi
	xorl	%esi, %esi
	call	pthread_join@PLT
	leaq	152(%rsp), %rdx
	leaq	8(%rsp), %rsi
	movq	%rsp, %rdi
	call	finish_proof
	leaq	.LC84(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
.L527:
	movq	184(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L536
	addq	$192, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L534:
	.cfi_restore_state
	movq	stdout(%rip), %rdx
	movl	$65536, %esi
	movl	$11, %edi
	call	chain_select_timed
	leaq	.LC101(%rip), %rsi
	leaq	.LC102(%rip), %rdi
	movslq	%eax, %rbp
	call	fopen@PLT
	movq	%rax, %rbx
	leaq	k_name(%rip), %rax
	movq	(%rax,%rbp,8), %rbp
	testq	%rbx, %rbx
	je	.L526
	movq	%rbx, %rdi
	xorl	%eax, %eax
	movq	%rbp, %rcx
	movl	$2, %esi
	leaq	.LC103(%rip), %rdx
	call	__fprintf_chk@PLT
	movq	%rbx, %rdi
	movl	%eax, %r14d
	call	fclose@PLT
	testl	%eax, %eax
	je	.L537
.L526:
	leaq	.LC97(%rip), %rsi
.L525:
	movq	%rbp, %rdx
	movl	$2, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	jmp	.L527
.L537:
	testl	%r14d, %r14d
	jle	.L526
	leaq	.LC98(%rip), %rsi
	jmp	.L525
.L535:
	call	mode_first.isra.0
	jmp	.L527
.L536:
	call	__stack_chk_fail@PLT
.L533:
	leaq	.LC100(%rip), %rdi
	call	die
.L532:
	leaq	.LC99(%rip), %rdi
	call	die
.L529:
	leaq	.LC106(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7419:
	.size	main, .-main
	.local	placed
	.comm	placed,4,4
	.local	rest_set
	.comm	rest_set,128,32
	.local	core_set
	.comm	core_set,128,32
	.local	impl
	.comm	impl,4,4
	.section	.rodata
	.align 8
	.type	ZERO8, @object
	.size	ZERO8, 8
ZERO8:
	.zero	8
	.data
	.align 4
	.type	svc, @object
	.size	svc, 4
svc:
	.long	-1
	.section	.data.rel.ro.local,"aw"
	.align 32
	.type	k_fn, @object
	.size	k_fn, 40
k_fn:
	.quad	chain_scalar
	.quad	chain_bmi
	.quad	chain_avx512
	.quad	chain_avx512vl
	.quad	chain_avx512vln
	.section	.rodata.str1.1
.LC107:
	.string	"scalar"
.LC108:
	.string	"bmi"
.LC109:
	.string	"avx512"
.LC110:
	.string	"avx512vl"
.LC111:
	.string	"avx512vln"
	.section	.data.rel.ro.local
	.align 32
	.type	k_name, @object
	.size	k_name, 40
k_name:
	.quad	.LC107
	.quad	.LC108
	.quad	.LC109
	.quad	.LC110
	.quad	.LC111
	.section	.rodata
	.align 16
	.type	vla_k, @object
	.size	vla_k, 432
vla_k:
	.quad	1
	.quad	1
	.quad	32898
	.quad	32898
	.quad	-9223372036854742902
	.quad	-9223372036854742902
	.quad	-9223372034707259392
	.quad	-9223372034707259392
	.quad	32907
	.quad	32907
	.quad	2147483649
	.quad	2147483649
	.quad	-9223372034707259263
	.quad	-9223372034707259263
	.quad	-9223372036854743031
	.quad	-9223372036854743031
	.quad	138
	.quad	138
	.quad	136
	.quad	136
	.quad	2147516425
	.quad	2147516425
	.quad	2147483658
	.quad	2147483658
	.quad	2147516555
	.quad	2147516555
	.quad	-9223372036854775669
	.quad	-9223372036854775669
	.quad	-9223372036854742903
	.quad	-9223372036854742903
	.quad	-9223372036854743037
	.quad	-9223372036854743037
	.quad	-9223372036854743038
	.quad	-9223372036854743038
	.quad	-9223372036854775680
	.quad	-9223372036854775680
	.quad	32778
	.quad	32778
	.quad	-9223372034707292150
	.quad	-9223372034707292150
	.quad	-9223372034707259263
	.quad	-9223372034707259263
	.quad	-9223372036854742912
	.quad	-9223372036854742912
	.quad	2147483649
	.quad	2147483649
	.quad	-9223372034707259384
	.quad	-9223372034707259384
	.quad	67
	.quad	67
	.quad	256
	.quad	256
	.quad	-9223372036854775808
	.quad	-9223372036854775808
	.align 32
	.type	RHO, @object
	.size	RHO, 100
RHO:
	.long	0
	.long	1
	.long	62
	.long	28
	.long	27
	.long	36
	.long	44
	.long	6
	.long	55
	.long	20
	.long	3
	.long	10
	.long	43
	.long	25
	.long	39
	.long	41
	.long	45
	.long	15
	.long	21
	.long	8
	.long	18
	.long	2
	.long	61
	.long	56
	.long	14
	.align 32
	.type	RC, @object
	.size	RC, 192
RC:
	.quad	1
	.quad	32898
	.quad	-9223372036854742902
	.quad	-9223372034707259392
	.quad	32907
	.quad	2147483649
	.quad	-9223372034707259263
	.quad	-9223372036854743031
	.quad	138
	.quad	136
	.quad	2147516425
	.quad	2147483658
	.quad	2147516555
	.quad	-9223372036854775669
	.quad	-9223372036854742903
	.quad	-9223372036854743037
	.quad	-9223372036854743038
	.quad	-9223372036854775680
	.quad	32778
	.quad	-9223372034707292150
	.quad	-9223372034707259263
	.quad	-9223372036854742912
	.quad	2147483649
	.quad	-9223372034707259384
	.section	.rodata.cst32,"aM",@progbits,32
	.align 32
.LC0:
	.quad	0
	.quad	4
	.quad	1
	.quad	5
	.align 32
.LC1:
	.quad	2
	.quad	6
	.quad	3
	.quad	7
	.section	.rodata
	.align 64
.LC2:
	.quad	7
	.quad	0
	.quad	1
	.quad	2
	.quad	3
	.quad	5
	.quad	6
	.quad	7
	.align 64
.LC3:
	.quad	67
	.quad	0
	.quad	0
	.quad	0
	.quad	256
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC4:
	.quad	0
	.quad	-9223372036854775808
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC5:
	.quad	4
	.quad	0
	.quad	1
	.quad	2
	.quad	3
	.quad	5
	.quad	6
	.quad	7
	.align 64
.LC6:
	.quad	1
	.quad	2
	.quad	3
	.quad	4
	.quad	0
	.quad	5
	.quad	6
	.quad	7
	.align 64
.LC7:
	.quad	0
	.quad	1
	.quad	62
	.quad	28
	.quad	27
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC8:
	.quad	36
	.quad	44
	.quad	6
	.quad	55
	.quad	20
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC9:
	.quad	3
	.quad	10
	.quad	43
	.quad	25
	.quad	39
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC10:
	.quad	41
	.quad	45
	.quad	15
	.quad	21
	.quad	8
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC11:
	.quad	18
	.quad	2
	.quad	61
	.quad	56
	.quad	14
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC12:
	.quad	3
	.quad	12
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC13:
	.quad	0
	.quad	0
	.quad	0
	.quad	9
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC14:
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	2
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC15:
	.quad	1
	.quad	10
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC16:
	.quad	0
	.quad	0
	.quad	3
	.quad	12
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC17:
	.quad	4
	.quad	8
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC18:
	.quad	0
	.quad	0
	.quad	1
	.quad	10
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC19:
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	3
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC20:
	.quad	2
	.quad	11
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC21:
	.quad	0
	.quad	0
	.quad	4
	.quad	8
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC22:
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.quad	1
	.quad	0
	.quad	0
	.quad	0
	.align 64
.LC23:
	.quad	2
	.quad	3
	.quad	4
	.quad	0
	.quad	1
	.quad	5
	.quad	6
	.quad	7
	.align 64
.LC24:
	.long	1
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC25:
	.long	32898
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC26:
	.long	32906
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC27:
	.long	-2147450880
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC28:
	.long	32907
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC29:
	.long	-2147483647
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC30:
	.long	-2147450751
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC31:
	.long	32777
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC32:
	.long	138
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC33:
	.long	136
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC34:
	.long	-2147450871
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC35:
	.long	-2147483638
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC36:
	.long	-2147450741
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC37:
	.long	139
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC38:
	.long	32905
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC39:
	.long	32771
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC40:
	.long	32770
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC41:
	.long	128
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC42:
	.long	32778
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC43:
	.long	-2147483638
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC44:
	.long	32896
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.align 64
.LC45:
	.long	-2147450872
	.long	-2147483648
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC46:
	.byte	11
	.byte	48
	.byte	85
	.byte	122
	.byte	-97
	.byte	-60
	.byte	-23
	.byte	14
	.byte	51
	.byte	88
	.byte	125
	.byte	-94
	.byte	-57
	.byte	-20
	.byte	17
	.byte	54
	.align 16
.LC47:
	.byte	3
	.byte	62
	.byte	121
	.byte	-76
	.byte	-17
	.byte	42
	.byte	101
	.byte	-96
	.byte	-37
	.byte	22
	.byte	81
	.byte	-116
	.byte	-57
	.byte	2
	.byte	61
	.byte	120
	.align 16
.LC48:
	.byte	91
	.byte	-128
	.byte	-91
	.byte	-54
	.byte	-17
	.byte	20
	.byte	57
	.byte	94
	.byte	-125
	.byte	-88
	.byte	-51
	.byte	-14
	.byte	23
	.byte	60
	.byte	97
	.byte	-122
	.align 16
.LC49:
	.byte	-77
	.byte	-18
	.byte	41
	.byte	100
	.byte	-97
	.byte	-38
	.byte	21
	.byte	80
	.byte	-117
	.byte	-58
	.byte	1
	.byte	60
	.byte	119
	.byte	-78
	.byte	-19
	.byte	40
	.align 16
.LC62:
	.byte	3
	.byte	8
	.byte	13
	.byte	18
	.byte	23
	.byte	28
	.byte	33
	.byte	38
	.byte	43
	.byte	48
	.byte	53
	.byte	58
	.byte	63
	.byte	68
	.byte	73
	.byte	78
	.align 16
.LC63:
	.byte	83
	.byte	88
	.byte	93
	.byte	98
	.byte	103
	.byte	108
	.byte	113
	.byte	118
	.byte	123
	.byte	-128
	.byte	-123
	.byte	-118
	.byte	-113
	.byte	-108
	.byte	-103
	.byte	-98
	.section	.rodata.cst8,"aM",@progbits,8
	.align 8
.LC64:
	.long	-2013235812
	.long	2117592124
	.align 8
.LC65:
	.long	0
	.long	1104006501
	.section	.rodata.cst16
	.align 16
.LC85:
	.quad	48
	.quad	4096
	.ident	"GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
