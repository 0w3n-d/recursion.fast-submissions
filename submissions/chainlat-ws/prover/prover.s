	.file	"chainwalk.c"
	.text
	.p2align 4
	.type	keccak_f, @function
keccak_f:
.LFB7357:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movl	$1717986919, %eax
	leaq	RC(%rip), %r10
	leaq	200(%rdi), %r11
	vpbroadcastd	%eax, %xmm4
	movl	$63, %eax
	vpxor	%xmm5, %xmm5, %xmm5
	vpbroadcastq	%rax, %xmm3
	movl	$-1, %eax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r14
	kmovw	%eax, %k1
	pushq	%r13
	.cfi_offset 14, -24
	.cfi_offset 13, -32
	leaq	192(%r10), %r13
	pushq	%r12
	.cfi_offset 12, -40
	movl	$3435973837, %r12d
	pushq	%rbx
	andq	$-64, %rsp
	subq	$256, %rsp
	.cfi_offset 3, -48
	vmovdqa	.LC0(%rip), %xmm8
	vmovdqa	.LC2(%rip), %xmm7
	movq	%fs:40, %r9
	movq	%r9, 248(%rsp)
	movq	%rdi, %r9
	vmovdqa	.LC3(%rip), %xmm6
	.p2align 4
	.p2align 3
.L2:
	vmovdqu	(%r9), %ymm0
	movq	32(%r9), %rax
	movq	%r9, %r8
	movq	%r11, %rcx
	vmovdqu	80(%r9), %ymm1
	xorq	72(%r9), %rax
	xorl	%esi, %esi
	xorq	112(%r9), %rax
	xorq	152(%r9), %rax
	vpternlogq	$150, 40(%r9), %ymm0, %ymm1
	xorq	192(%r9), %rax
	vmovdqu	160(%r9), %ymm0
	movq	%rax, 32(%rsp)
	vpternlogq	$150, 120(%r9), %ymm1, %ymm0
	vmovdqa	%ymm0, (%rsp)
.L10:
	leal	4(%rsi), %edx
	movq	%rdx, %rax
	imulq	%r12, %rdx
	shrq	$34, %rdx
	leal	(%rdx,%rdx,4), %edx
	subl	%edx, %eax
	leal	1(%rsi), %edx
	movq	%rdx, %rsi
	imulq	%r12, %rdx
	cltq
	shrq	$34, %rdx
	leal	(%rdx,%rdx,4), %edi
	movl	%esi, %edx
	subl	%edi, %edx
	movslq	%edx, %rdx
	movq	(%rsp,%rdx,8), %rdx
	rorx	$63, %rdx, %rdx
	xorq	(%rsp,%rax,8), %rdx
	xorq	%rdx, -200(%rcx)
	leaq	-160(%rcx), %rax
.L3:
	xorq	%rdx, (%rax)
	xorq	%rdx, 40(%rax)
	addq	$80, %rax
	cmpq	%rax, %rcx
	jne	.L3
	addq	$8, %rcx
	cmpl	$5, %esi
	jne	.L10
	leaq	RHO(%rip), %rdx
	movq	%r9, %rax
	xorl	%esi, %esi
.L5:
	leal	12(%rsi), %ecx
	kmovw	%k1, %k2
	vpbroadcastd	%esi, %xmm0
	addl	$2, %esi
	movq	%rcx, %rbx
	vpaddd	%xmm8, %xmm0, %xmm0
	kmovw	%k1, %k3
	leaq	48(%rsp), %rdi
	vpsrlq	$32, %xmm0, %xmm2
	imulq	%r12, %rcx
	addq	$8, %rax
	addq	$4, %rdx
	vpmuldq	%xmm4, %xmm0, %xmm1
	vpmuldq	%xmm4, %xmm2, %xmm2
	shrq	$34, %rcx
	leal	(%rcx,%rcx,4), %r14d
	subl	%r14d, %ebx
	vpermt2d	%xmm2, %xmm7, %xmm1
	leal	4(%rbx,%rbx,4), %ecx
	vpsrad	$1, %xmm1, %xmm1
	movslq	%ecx, %rbx
	vpslld	$2, %xmm1, %xmm2
	vpaddd	%xmm1, %xmm2, %xmm1
	vmovq	-8(%rax), %xmm2
	vpinsrq	$1, 32(%rax), %xmm2, %xmm10
	vpsubd	%xmm1, %xmm0, %xmm0
	vmovd	36(%rdx), %xmm2
	vpinsrd	$1, 56(%rdx), %xmm2, %xmm2
	vpslld	$2, %xmm0, %xmm1
	vpaddd	%xmm0, %xmm1, %xmm1
	vmovq	72(%rax), %xmm0
	vpinsrq	$1, 112(%rax), %xmm0, %xmm9
	vmovd	-4(%rdx), %xmm0
	vpinsrd	$1, 16(%rdx), %xmm0, %xmm0
	vpaddd	%xmm6, %xmm1, %xmm1
	vpunpcklqdq	%xmm2, %xmm0, %xmm0
	vpmovsxdq	%xmm0, %xmm11
	vpsrldq	$8, %xmm0, %xmm0
	vpsubq	%xmm11, %xmm5, %xmm2
	vpmovsxdq	%xmm0, %xmm0
	vpandq	%xmm3, %xmm2, %xmm2
	vpsrlvq	%xmm2, %xmm10, %xmm2
	vpsllvq	%xmm11, %xmm10, %xmm10
	vporq	%xmm10, %xmm2, %xmm2
	vpscatterdq	%xmm2, 48(%rsp,%xmm1,8){%k2}
	vpsubq	%xmm0, %xmm5, %xmm2
	vpshufd	$238, %xmm1, %xmm1
	vpandq	%xmm3, %xmm2, %xmm2
	vpsrlvq	%xmm2, %xmm9, %xmm2
	vpsllvq	%xmm0, %xmm9, %xmm9
	vporq	%xmm9, %xmm2, %xmm0
	vpscatterdq	%xmm0, 48(%rsp,%xmm1,8){%k3}
	movl	76(%rdx), %ecx
	movq	152(%rax), %r14
	rolq	%cl, %r14
	movq	%r14, 48(%rsp,%rbx,8)
	cmpl	$10, %esi
	jne	.L5
	xorl	%ebx, %ebx
.L6:
	movq	8(%rdi), %rax
	xorl	%ecx, %ecx
.L7:
	leal	2(%rcx), %edx
	notq	%rax
	movq	%rax, %rsi
	movq	%rdx, %rax
	imulq	%r12, %rdx
	shrq	$34, %rdx
	leal	(%rdx,%rdx,4), %edx
	subl	%edx, %eax
	addl	%ebx, %eax
	cltq
	movq	48(%rsp,%rax,8), %rax
	andq	%rax, %rsi
	xorq	(%rdi,%rcx,8), %rsi
	movq	%rsi, (%r8,%rcx,8)
	addq	$1, %rcx
	cmpq	$5, %rcx
	jne	.L7
	addl	$5, %ebx
	addq	$40, %rdi
	addq	$40, %r8
	cmpl	$25, %ebx
	jne	.L6
	movq	(%r10), %rax
	addq	$8, %r10
	xorq	%rax, (%r9)
	cmpq	%r13, %r10
	jne	.L2
	movq	248(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L20
	vzeroupper
	leaq	-32(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L20:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7357:
	.size	keccak_f, .-keccak_f
	.p2align 4
	.type	chain_words_gp, @function
chain_words_gp:
.LFB7362:
	.cfi_startproc
	endbr64
	testq	%rsi, %rsi
	je	.L30
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	leaq	-1(%rsi), %rax
	vmovq	%rdi, %xmm9
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
	movabsq	$-9223372036854742902, %rbx
	vmovq	%rbx, %xmm8
	addq	$2147483510, %rbx
	vmovq	%rbx, %xmm7
	addq	$129, %rbx
	vmovq	%rbx, %xmm0
	subq	$80, %rsp
	.cfi_def_cfa_offset 136
	movq	8(%rdi), %r9
	movabsq	$-9223372036854743031, %rbx
	vmovq	%rbx, %xmm6
	subq	$32638, %rbx
	movq	16(%rdi), %rsi
	movq	24(%rdi), %rcx
	vmovq	%rbx, %xmm5
	addq	$32766, %rbx
	movq	%rax, -72(%rsp)
	movq	(%rdi), %rax
	vmovq	%rbx, %xmm4
	subq	$134, %rbx
	vmovq	%rbx, %xmm3
	subq	$1, %rbx
	movq	%rax, %rdx
	vmovq	%rbx, %xmm2
	subq	$32642, %rbx
	vmovq	%rbx, %xmm1
	movq	%r9, %rbx
	.p2align 4
	.p2align 3
.L23:
	movq	%rbx, %r8
	movq	%rdx, %rax
	movq	%rcx, %rbp
	movabsq	$-9223372036854775808, %r10
	shldq	$8, %rdx, %r8
	shrq	$56, %rcx
	movq	%rsi, %rdx
	salq	$8, %rax
	xorq	%r8, %r10
	xorb	$1, %ch
	shldq	$8, %rbx, %rdx
	shldq	$8, %rsi, %rbp
	xorq	$67, %rax
	rorx	$63, %r10, %r9
	xorq	%rcx, %r9
	rorx	$63, %rdx, %rsi
	rorx	$63, %rbp, %rbx
	xorq	%rax, %rsi
	xorq	%r10, %rbx
	rorx	$63, %rax, %r10
	xorq	%r9, %rax
	rorx	$63, %rcx, %r11
	xorq	%rdx, %r11
	movq	%rax, -104(%rsp)
	xorq	%rbp, %r10
	xorq	%rbx, %rdx
	xorq	%r11, %rbp
	rorx	$20, %rsi, %r14
	rorx	$21, %rbx, %rdi
	rorx	$44, %r10, %r12
	rorx	$36, %rbp, %rbp
	movq	%r12, -56(%rsp)
	rorx	$58, %rbx, %r12
	rorx	$43, %r11, %r15
	xorq	%rsi, %r8
	movq	%rbp, -64(%rsp)
	rorx	$61, %r9, %rbp
	rorx	$50, %r10, %r13
	xorq	%r10, %rcx
	movq	%rbp, -48(%rsp)
	rorx	$3, %rbx, %rbp
	rorx	$63, %r8, %r8
	rorx	$37, %rcx, %rcx
	movabsq	$-9223372036854775808, %rax
	movq	%r12, -32(%rsp)
	rorx	$39, %r11, %r12
	xorq	%rsi, %rax
	rorx	$19, %rax, %rax
	movq	%rax, -40(%rsp)
	rorx	$56, %r10, %rax
	rorx	$25, %r10, %r10
	movq	%rax, -24(%rsp)
	rorx	$46, %r9, %rax
	movq	%rax, -16(%rsp)
	rorx	$28, %r9, %rax
	movq	%rax, -120(%rsp)
	rorx	$54, %rsi, %rax
	movq	%rax, -8(%rsp)
	rorx	$49, %rbx, %rax
	rorx	$2, %rdx, %rbx
	rorx	$23, %r9, %rdx
	movq	%rdx, 24(%rsp)
	rorx	$62, %rsi, %rdx
	movq	%r15, %r9
	movq	-64(%rsp), %rsi
	movq	%rdx, 32(%rsp)
	movq	%r14, %rdx
	notq	%r9
	movq	%rax, -112(%rsp)
	notq	%rdx
	rorx	$8, %r11, %rax
	rorx	$9, %r11, %r11
	movq	%rax, (%rsp)
	movq	-104(%rsp), %rax
	andq	%rdi, %rdx
	xorq	%rax, %rdx
	movq	%rdx, 40(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	%r15, %rdx
	xorq	%r14, %rdx
	movq	%rdx, -104(%rsp)
	movq	%r9, %rdx
	movq	%r13, %r9
	andq	%r13, %rdx
	notq	%r9
	xorq	%rdi, %rdx
	movq	-56(%rsp), %rdi
	movq	%rdx, -96(%rsp)
	movq	%r9, %rdx
	andq	%rax, %rdx
	notq	%rax
	andq	%r14, %rax
	movq	%rdx, %r9
	movq	%rsi, %rdx
	xorq	%r15, %r9
	movq	%rax, %r14
	movq	-48(%rsp), %r15
	movq	%rdi, %rax
	notq	%rax
	movq	%r9, -88(%rsp)
	movq	-40(%rsp), %r9
	xorq	%r13, %r14
	andq	%r15, %rax
	movq	%r14, -80(%rsp)
	movq	%rdi, %r14
	xorq	%rax, %rdx
	movq	%r15, %rax
	movq	%r9, %r13
	notq	%rax
	notq	%r13
	andq	%r9, %rax
	xorq	%rax, %r14
	movq	%r13, %rax
	movq	%rbp, %r13
	andq	%rbp, %rax
	notq	%r13
	xorq	%rax, %r15
	movq	%r13, %rax
	movq	-24(%rsp), %r13
	andq	%rsi, %rax
	notq	%rsi
	xorq	%rax, %r9
	movq	%rsi, %rax
	movq	-32(%rsp), %rsi
	andq	%rdi, %rax
	movq	%r9, -56(%rsp)
	movq	%rax, %rdi
	movq	%rsi, %rax
	notq	%rax
	xorq	%rbp, %rdi
	andq	%r12, %rax
	movq	%rdi, -48(%rsp)
	movq	-16(%rsp), %rdi
	movq	%rax, %rbp
	xorq	%r8, %rbp
	movq	%rbp, -40(%rsp)
	movq	%r12, %rbp
	notq	%rbp
	movq	%rbp, %rax
	movq	%rsi, %rbp
	andq	%r13, %rax
	xorq	%rax, %rbp
	movq	%r13, %rax
	notq	%rax
	andq	%rdi, %rax
	xorq	%rax, %r12
	movq	%rdi, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%rax, %r13
	movq	%r8, %rax
	andq	%rsi, %rax
	xorq	%rax, %rdi
	movq	-120(%rsp), %rax
	movq	%rdi, -16(%rsp)
	movq	-8(%rsp), %r8
	notq	%rax
	movq	-112(%rsp), %r9
	movq	-120(%rsp), %rdi
	movq	%rbp, -32(%rsp)
	andq	%r8, %rax
	movq	(%rsp), %rsi
	movq	%r15, -64(%rsp)
	xorq	%rcx, %rax
	movq	%r13, -24(%rsp)
	movq	%rax, -8(%rsp)
	movq	%r8, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rax, %rdi
	movq	%r9, %rax
	movq	%rsi, %r9
	notq	%rax
	notq	%r9
	andq	%rsi, %rax
	andq	%rcx, %r9
	xorq	-112(%rsp), %r9
	movq	%rdx, -112(%rsp)
	xorq	%rax, %r8
	movq	%rcx, %rax
	movq	24(%rsp), %rcx
	notq	%rax
	andq	-120(%rsp), %rax
	movq	%r8, (%rsp)
	xorq	%rax, %rsi
	movq	%r11, %rax
	notq	%rax
	movq	%rsi, 8(%rsp)
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%rax, 16(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rcx, %rax
	xorq	%r11, %rax
	movq	%rax, 24(%rsp)
	movq	%rcx, %rax
	notq	%rax
	movq	%rax, %rsi
	movq	32(%rsp), %rax
	andq	%rax, %rsi
	xorq	%r10, %rsi
	movq	%rax, %r10
	notq	%rax
	xorq	-40(%rsp), %rdx
	andq	%rbx, %rax
	notq	%rbx
	xorq	16(%rsp), %rdx
	xorq	-8(%rsp), %rdx
	xorq	%rax, %rcx
	andq	%r11, %rbx
	movq	%r10, %rax
	movq	-96(%rsp), %r11
	xorq	%rbx, %rax
	movq	-104(%rsp), %rbx
	movq	40(%rsp), %r10
	movq	%rcx, 32(%rsp)
	xorq	%r12, %r11
	xorq	%rbp, %rbx
	xorq	%r8, %r11
	movq	24(%rsp), %rbp
	movq	-88(%rsp), %r8
	xorq	-56(%rsp), %r8
	xorq	%rdi, %rbx
	xorq	$1, %r10
	xorq	%r15, %r11
	xorq	%r9, %r8
	xorq	%rbp, %rbx
	xorq	%rsi, %r11
	xorq	%r10, %rdx
	xorq	%rcx, %r8
	movq	-80(%rsp), %rcx
	xorq	-48(%rsp), %rcx
	xorq	%r14, %rbx
	xorq	-16(%rsp), %rcx
	xorq	8(%rsp), %rcx
	xorq	%r13, %r8
	movq	%r14, %rbp
	xorq	%rax, %rcx
	rorx	$63, %rbx, %r14
	rorx	$63, %r11, %r13
	rorx	$63, %r8, %r15
	xorq	%rcx, %r14
	xorq	%rdx, %r13
	xorq	%rbx, %r15
	rorx	$63, %rcx, %rcx
	xorq	%r11, %rcx
	xorq	%r14, %r10
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r13, %rbp
	xorq	%r15, %r12
	xorq	%rcx, %r9
	xorq	%r15, %rsi
	rorx	$21, %r12, %rbx
	movq	%rbx, 40(%rsp)
	rorx	$43, %r9, %rbx
	xorq	%rdx, %rax
	movq	%rbx, -120(%rsp)
	movq	-88(%rsp), %r9
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	movq	-48(%rsp), %r11
	movq	-104(%rsp), %r12
	xorq	%rcx, %r9
	rorx	$36, %r9, %r8
	movq	-40(%rsp), %r9
	xorq	%rdx, %r11
	xorq	%r13, %r12
	rorx	$44, %r11, %r11
	movq	%r11, -88(%rsp)
	xorq	%r14, %r9
	rorx	$61, %r9, %rbx
	movq	%rdi, %r9
	movq	-112(%rsp), %rdi
	xorq	%r13, %r9
	rorx	$19, %r9, %r11
	rorx	$3, %rsi, %r9
	movq	-64(%rsp), %rsi
	movq	%r9, -48(%rsp)
	rorx	$63, %r12, %r9
	xorq	%r14, %rdi
	xorq	%r15, %rsi
	rorx	$28, %rdi, %rdi
	rorx	$58, %rsi, %r12
	movq	-24(%rsp), %rsi
	movq	%r12, -40(%rsp)
	xorq	%rcx, %rsi
	rorx	$39, %rsi, %r12
	movq	8(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -24(%rsp)
	movq	16(%rsp), %rsi
	movq	%rdi, 16(%rsp)
	movq	-32(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, 8(%rsp)
	movq	-80(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, 48(%rsp)
	movq	(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-16(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, (%rsp)
	movq	32(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-56(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 32(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-8(%rsp), %rdx
	movq	%rdi, 56(%rsp)
	movq	40(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	24(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, -8(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-48(%rsp), %rdx
	movq	%r10, %rbp
	movq	-88(%rsp), %r10
	movq	%rdi, 40(%rsp)
	xorq	%rax, %rbp
	movq	%r10, %rax
	movq	%rbp, -96(%rsp)
	movq	%r10, %rbp
	notq	%rax
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rbx, %rax
	movq	%rdx, %rbx
	movq	%rax, -80(%rsp)
	movq	%rdx, %rax
	movq	8(%rsp), %rdx
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	-40(%rsp), %r11
	andq	%r10, %r8
	movq	-24(%rsp), %r10
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	48(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	16(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	32(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	56(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	movq	%r10, %rsi
	andq	%r10, %rax
	notq	%rsi
	movq	%rax, %rbx
	movq	%rsi, %rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-88(%rsp), %r14
	xorq	-48(%rsp), %r14
	movq	%r15, %rax
	movq	-8(%rsp), %r15
	xorq	%r14, %rdx
	movq	%r10, 24(%rsp)
	xorq	%rbx, %rdx
	xorq	$32898, %r15
	xorq	%r15, %rdx
	movq	%r15, %r10
	movq	-112(%rsp), %r15
	movq	%rbp, -120(%rsp)
	movq	-80(%rsp), %r13
	movq	-24(%rsp), %rcx
	movq	%r8, -40(%rsp)
	xorq	%rbp, %r15
	movq	%rdi, -8(%rsp)
	xorq	(%rsp), %rcx
	xorq	%r12, %r13
	movq	%r15, %rbp
	xorq	-96(%rsp), %rcx
	xorq	%r11, %rbp
	movq	%r13, %rbx
	xorq	16(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%r8, %rbp
	xorq	%rdi, %rbx
	movq	-64(%rsp), %r8
	movq	40(%rsp), %rdi
	xorq	-56(%rsp), %rcx
	xorq	%rsi, %rbx
	xorq	-104(%rsp), %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	24(%rsp), %r8
	xorq	%rcx, %r14
	xorq	%r9, %r8
	rorx	$63, %rbx, %r13
	rorx	$63, %rcx, %rcx
	xorq	%rdx, %r13
	xorq	%rbx, %rcx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rcx, %r9
	movq	-120(%rsp), %rbp
	xorq	%r8, %rdx
	xorq	%r15, %r12
	rorx	$43, %r9, %rbx
	xorq	%r15, %rsi
	xorq	%rcx, %rdi
	xorq	%rdx, %rax
	movq	%rbx, -120(%rsp)
	movq	-56(%rsp), %rbx
	rorx	$21, %r12, %r12
	rorx	$3, %rsi, %rsi
	movq	%r12, 32(%rsp)
	rorx	$36, %rdi, %r8
	xorq	%r14, %r10
	xorq	%r13, %rbp
	xorq	%rdx, %rbx
	movq	-80(%rsp), %r12
	movq	-88(%rsp), %rdi
	xorq	%r13, %r11
	rorx	$44, %rbx, %r9
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$19, %r11, %r11
	movq	-48(%rsp), %rbx
	movq	%rsi, -48(%rsp)
	xorq	%r15, %r12
	xorq	%r14, %rdi
	movq	-32(%rsp), %rsi
	rorx	$58, %r12, %r12
	movq	%r12, 40(%rsp)
	rorx	$28, %rdi, %rdi
	movq	%r9, -56(%rsp)
	movq	-112(%rsp), %r9
	xorq	%r14, %rbx
	xorq	%rcx, %rsi
	rorx	$61, %rbx, %rbx
	rorx	$39, %rsi, %r12
	movq	(%rsp), %rsi
	xorq	%r13, %r9
	rorx	$63, %r9, %r9
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	xorq	%r13, %rdi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	rorx	$25, %rdx, %rdx
	movq	%rdx, 48(%rsp)
	xorq	%r15, %rdi
	movq	-16(%rsp), %rdx
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$37, %rsi, %rsi
	xorq	%r14, %rdx
	xorq	-104(%rsp), %r15
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%rcx, %rdi
	rorx	$2, %r15, %r15
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	movq	32(%rsp), %rdi
	xorq	%r13, %rdx
	xorq	-64(%rsp), %rcx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	rorx	$9, %rcx, %rcx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	notq	%rdx
	movq	%rdi, -104(%rsp)
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	andq	%rbp, %r10
	xorq	%rdx, %rdi
	movq	(%rsp), %rdx
	movq	%r10, %rbp
	movq	-56(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%r10, %rax
	movq	%rbp, -96(%rsp)
	movq	%r10, %rbp
	notq	%rax
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	movq	%rbp, %rdi
	movq	-48(%rsp), %rbp
	notq	%rax
	andq	%rbp, %rax
	xorq	%rbx, %rax
	movq	8(%rsp), %rbx
	movq	%rax, -80(%rsp)
	movq	%rbp, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%r10, %r8
	movq	-32(%rsp), %r10
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbp
	movq	%r11, %rax
	movq	%rbp, -56(%rsp)
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, %rbp
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	andq	%r11, %rax
	movq	%r10, -32(%rsp)
	xorq	%rax, %rdx
	movq	%rbx, %rax
	notq	%rax
	movq	%rdx, -24(%rsp)
	andq	%r9, %rax
	movq	%rax, %r11
	movq	%r9, %rax
	xorq	%rsi, %r11
	notq	%rax
	movq	%r11, -16(%rsp)
	movq	-8(%rsp), %r10
	movq	%rbx, %r11
	movq	24(%rsp), %rdx
	movq	%rbp, -48(%rsp)
	andq	%r10, %rax
	movq	%rdi, -120(%rsp)
	xorq	%rax, %r11
	movq	%r10, %rax
	movq	%r8, -40(%rsp)
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, -8(%rsp)
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	movq	48(%rsp), %rsi
	xorq	%r10, %r9
	andq	%rbx, %rax
	movq	%rcx, %rbx
	xorq	%rdx, %rax
	notq	%rbx
	movq	%rax, (%rsp)
	movq	%rbx, %rax
	andq	%rsi, %rax
	movq	%rax, %rbx
	movq	%rsi, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rsi, %rbx
	movq	8(%rsp), %rdx
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%rbx, %rsi
	movq	%r13, %rbx
	notq	%rbx
	movq	%rbx, %rax
	movq	-88(%rsp), %rbx
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	-112(%rsp), %rcx
	xorq	%rbp, %rbx
	movq	16(%rsp), %rbp
	movq	%rax, %r10
	xorq	%rbx, %rdx
	movq	-104(%rsp), %rbx
	xorq	%r13, %r15
	xorq	%r8, %rcx
	xorq	%r14, %r10
	movq	-64(%rsp), %r8
	xorq	-16(%rsp), %rdx
	xorq	%rcx, %rbp
	movq	%r10, %r14
	movq	32(%rsp), %r10
	xorq	%r12, %rbx
	xorq	%rdi, %rbp
	movq	56(%rsp), %rdi
	xorq	-8(%rsp), %rbx
	movq	%r15, %rax
	vmovq	%xmm8, %r13
	xorq	-80(%rsp), %rbx
	xorq	%r11, %rbp
	movq	-96(%rsp), %rcx
	xorq	%rdi, %r8
	xorq	%r13, %r10
	xorq	%rsi, %rbx
	movq	%r14, 24(%rsp)
	xorq	%r9, %r8
	xorq	-32(%rsp), %r8
	xorq	%r10, %rdx
	rorx	$63, %rbx, %r13
	xorq	%r14, %r8
	xorq	-56(%rsp), %rcx
	xorq	(%rsp), %rcx
	rorx	$63, %rbp, %r14
	xorq	%r15, %rcx
	xorq	-24(%rsp), %rcx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r15, %r12
	xorq	%rcx, %r9
	rorx	$21, %r12, %rbx
	xorq	%rdx, %r13
	xorq	%r15, %rsi
	movq	%rbx, 32(%rsp)
	rorx	$43, %r9, %rbx
	movq	-56(%rsp), %r9
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %rdi
	xorq	%r14, %r10
	xorq	%rdx, %r9
	movq	-120(%rsp), %rbp
	rorx	$36, %rdi, %r8
	xorq	%rdx, %rax
	movq	%rbx, -120(%rsp)
	rorx	$44, %r9, %r9
	xorq	%r13, %r11
	rorx	$50, %rax, %rax
	movq	%r9, -56(%rsp)
	movq	-48(%rsp), %r9
	xorq	%r13, %rbp
	rorx	$19, %r11, %r11
	movq	%rsi, -48(%rsp)
	movq	-80(%rsp), %r12
	rorx	$20, %rbp, %rbp
	movq	-112(%rsp), %rsi
	xorq	%r14, %r9
	movq	-88(%rsp), %rdi
	xorq	%r15, %r12
	rorx	$61, %r9, %rbx
	xorq	%r13, %rsi
	xorq	%r14, %rdi
	rorx	$63, %rsi, %r9
	rorx	$58, %r12, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	movq	-32(%rsp), %r12
	rorx	$28, %rdi, %rdi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	xorq	%rcx, %r12
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	rorx	$39, %r12, %r12
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	%rdi, 56(%rsp)
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	xorq	%rax, %rbp
	movq	-48(%rsp), %r10
	movq	%rdx, %rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	notq	%rax
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	movq	%rbp, -120(%rsp)
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm7, %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%rbp, %rcx
	xorq	%r15, %rdx
	movq	%rcx, %rbp
	xorq	%rbx, %rdx
	xorq	%r8, %rbp
	xorq	%r10, %rdx
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	-80(%rsp), %r14
	movq	%rdi, -8(%rsp)
	movq	%r14, %rbx
	movq	-64(%rsp), %r8
	movq	-56(%rsp), %rcx
	rorx	$63, %rbp, %r14
	xorq	%r12, %rbx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	%rsi, %rbx
	xorq	-24(%rsp), %rcx
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rax, %rcx
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	%rdx, %r13
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	xorq	%rcx, %r9
	movq	-56(%rsp), %rbx
	xorq	%r15, %rsi
	movq	-120(%rsp), %rbp
	xorq	%rcx, %rdi
	rorx	$3, %rsi, %rsi
	xorq	%r15, %r12
	xorq	%r14, %r10
	xorq	%rdx, %rax
	xorq	%rdx, %rbx
	rorx	$43, %r9, %r9
	movq	%r9, -120(%rsp)
	xorq	%r13, %rbp
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	rorx	$21, %r12, %r12
	xorq	%r13, %r11
	movq	-88(%rsp), %rdi
	movq	%r12, 32(%rsp)
	xorq	%r14, %rbx
	rorx	$20, %rbp, %rbp
	xorq	%r13, %rsi
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r14, %rdi
	movq	-32(%rsp), %r12
	rorx	$28, %rdi, %rdi
	xorq	%r15, %rsi
	xorq	%rcx, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	%r15, %rdi
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	xorq	-24(%rsp), %rdx
	xorq	-104(%rsp), %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$2, %r15, %r15
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%rdx, -24(%rsp)
	movq	%r10, %r11
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	-8(%rsp), %rbx
	movq	%r9, %rax
	notq	%rax
	movq	24(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	andq	%rbx, %rax
	movq	%r8, -40(%rsp)
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	movq	-112(%rsp), %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rbp, %rcx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	$32907, %r15
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	%rbx, %rdx
	xorq	%r10, %rdx
	xorq	%r11, %rbp
	xorq	-80(%rsp), %r14
	xorq	-24(%rsp), %rcx
	movq	%r14, %rbx
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	xorq	%r12, %rbx
	xorq	16(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	rorx	$63, %rbp, %r14
	xorq	%rcx, %r14
	xorq	%rsi, %rbx
	rorx	$63, %rcx, %rcx
	xorq	%r14, %r10
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	%rbx, %rcx
	rorx	$63, %rbx, %r13
	xorq	%r9, %r8
	movq	-56(%rsp), %rbx
	xorq	24(%rsp), %r8
	xorq	%rdx, %r13
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	xorq	%r15, %r12
	xorq	%rcx, %r9
	xorq	%rdx, %rbx
	xorq	%r15, %rsi
	movq	-120(%rsp), %rbp
	rorx	$21, %r12, %r12
	rorx	$43, %r9, %r9
	xorq	%rcx, %rdi
	movq	%r12, 32(%rsp)
	rorx	$44, %rbx, %rbx
	rorx	$3, %rsi, %rsi
	xorq	%rdx, %rax
	movq	%r9, -120(%rsp)
	rorx	$36, %rdi, %r8
	xorq	%r13, %rbp
	xorq	%r13, %r11
	movq	%rbx, -56(%rsp)
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$19, %r11, %r11
	movq	-48(%rsp), %rbx
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	movq	-32(%rsp), %r12
	movq	-88(%rsp), %rdi
	xorq	%r14, %rbx
	xorq	%r13, %rsi
	xorq	%rcx, %r12
	rorx	$61, %rbx, %rbx
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	rorx	$39, %r12, %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	xorq	%r14, %rdi
	rorx	$56, %rsi, %rsi
	rorx	$28, %rdi, %rdi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	notq	%rdx
	movq	%rdi, -104(%rsp)
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	andq	%rbp, %r10
	xorq	%rdx, %rdi
	movq	%r10, %rbp
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rbp, -96(%rsp)
	movq	-56(%rsp), %rdx
	movq	-48(%rsp), %r10
	movq	%rdx, %rax
	movq	%rdx, %rbp
	notq	%rax
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	movq	%rbp, -120(%rsp)
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	movl	$2147483649, %ecx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	-80(%rsp), %r14
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%rcx, %rbp
	movq	%r14, %rbx
	xorq	%r8, %rbp
	xorq	%r12, %rbx
	xorq	%r10, %rdx
	xorq	%rdi, %rbx
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	movq	%rdi, -8(%rsp)
	movq	56(%rsp), %rdi
	movq	-64(%rsp), %r8
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	movq	-56(%rsp), %rcx
	xorq	-24(%rsp), %rcx
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	xorq	%rdi, %r8
	rorx	$63, %rdx, %rdx
	xorq	-32(%rsp), %r8
	xorq	%rax, %rcx
	xorq	%rcx, %r14
	xorq	%r9, %r8
	rorx	$63, %rcx, %rcx
	xorq	24(%rsp), %r8
	xorq	%rbx, %rcx
	movq	-56(%rsp), %rbx
	xorq	%r8, %rdx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	movq	-120(%rsp), %rbp
	xorq	%r14, %r10
	xorq	%rcx, %rdi
	xorq	%rdx, %rbx
	xorq	%r15, %r12
	xorq	%rcx, %r9
	xorq	%rdx, %rax
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	xorq	%r13, %rbp
	rorx	$43, %r9, %r9
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	rorx	$20, %rbp, %rbp
	xorq	%r14, %rbx
	xorq	%r13, %r11
	xorq	%r15, %rsi
	movq	%r9, -120(%rsp)
	rorx	$3, %rsi, %rsi
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	movq	-88(%rsp), %rdi
	movq	%r12, 32(%rsp)
	xorq	%r13, %rsi
	movq	-32(%rsp), %r12
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r14, %rdi
	rorx	$28, %rdi, %rdi
	xorq	%rcx, %r12
	xorq	%r15, %rsi
	rorx	$39, %r12, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	%r15, %rdi
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	xorq	%rcx, %rdi
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	xorq	-104(%rsp), %r15
	xorq	-24(%rsp), %rdx
	xorq	-64(%rsp), %rcx
	rorx	$2, %r15, %r15
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	rorx	$9, %rcx, %rcx
	movq	32(%rsp), %rdi
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	movq	%rax, %rsi
	notq	%r10
	xorq	%rdx, %rsi
	movq	%r10, %rax
	movq	%rsi, (%rsp)
	movq	48(%rsp), %r10
	movq	-16(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	andq	%r10, %rax
	movq	%r8, -40(%rsp)
	movq	%rax, %rbx
	movq	%r10, %rax
	movq	%rdi, -8(%rsp)
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	movq	%rax, %r10
	xorq	%r14, %r10
	andq	%rcx, %r15
	vmovq	%xmm0, %rcx
	movq	-104(%rsp), %r14
	xorq	%r13, %r15
	movq	%r10, 24(%rsp)
	xorq	-80(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	-96(%rsp), %rcx
	xorq	%r11, %rbp
	xorq	(%rsp), %rcx
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	xorq	%r10, %rdx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	%rax, %rcx
	rorx	$63, %rbp, %r14
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	%rcx, %r14
	rorx	$63, %rbx, %r13
	rorx	$63, %r8, %r15
	rorx	$63, %rcx, %rcx
	xorq	%rbp, %r15
	xorq	%rbx, %rcx
	movq	-120(%rsp), %rbp
	movq	-56(%rsp), %rbx
	xorq	%rdx, %r13
	xorq	%r14, %r10
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r15, %r12
	xorq	%r13, %rbp
	xorq	%rcx, %r9
	xorq	%rdx, %rbx
	xorq	%r15, %rsi
	rorx	$44, %rbx, %rbx
	rorx	$3, %rsi, %rsi
	rorx	$43, %r9, %r9
	xorq	%rcx, %rdi
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	xorq	%rdx, %rax
	rorx	$20, %rbp, %rbp
	movq	%r9, -120(%rsp)
	xorq	%r14, %rbx
	xorq	%r13, %r11
	rorx	$50, %rax, %rax
	xorq	%r13, %rsi
	movq	%r12, 32(%rsp)
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	movq	-88(%rsp), %rdi
	movq	-32(%rsp), %r12
	xorq	%rdx, %rsi
	xorq	%r14, %rdi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	xorq	%rcx, %r12
	movq	8(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	rorx	$39, %r12, %r12
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	movq	%rbp, -120(%rsp)
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm6, %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	%r10, %rdx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	movq	-56(%rsp), %rcx
	rorx	$63, %rdx, %rdx
	xorq	-24(%rsp), %rcx
	xorq	-96(%rsp), %rcx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	(%rsp), %rcx
	movq	-120(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r8, %rdx
	movq	-56(%rsp), %rbx
	xorq	%r15, %rsi
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	rorx	$3, %rsi, %rsi
	xorq	%r15, %r12
	xorq	%rdx, %rax
	xorq	%r14, %r10
	xorq	%rdx, %rbx
	rorx	$43, %r9, %r9
	movq	%r9, -120(%rsp)
	xorq	%r13, %rbp
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	rorx	$21, %r12, %r12
	rorx	$20, %rbp, %rbp
	movq	-88(%rsp), %rdi
	movq	%r12, 32(%rsp)
	xorq	%r14, %rbx
	xorq	%r13, %r11
	xorq	%r13, %rsi
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r14, %rdi
	movq	-32(%rsp), %r12
	rorx	$28, %rdi, %rdi
	xorq	%r15, %rsi
	xorq	%rcx, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	rorx	$9, %rcx, %rcx
	movq	%rdi, 48(%rsp)
	movq	-16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	xorq	%r14, %r10
	xorq	%r13, %r15
	movq	%r15, %rax
	movq	%r10, 24(%rsp)
	movq	32(%rsp), %r15
	movq	-16(%rsp), %rdx
	movq	-112(%rsp), %rcx
	movq	%rbx, 8(%rsp)
	xorb	$-118, %r15b
	movq	-104(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%rbp, -120(%rsp)
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%rbp, %rcx
	xorq	%r15, %rdx
	movq	%rcx, %rbp
	movq	%r8, -40(%rsp)
	movq	-56(%rsp), %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	xorq	%r8, %rbp
	movq	%rdi, -8(%rsp)
	xorq	%r12, %rbx
	movq	-64(%rsp), %r8
	xorq	%r10, %rdx
	xorq	%r11, %rbp
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	xorq	-24(%rsp), %rcx
	xorq	-96(%rsp), %rcx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	(%rsp), %rcx
	xorq	%rdx, %r13
	xorq	%rax, %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rbp, %r15
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r8, %rdx
	movq	-56(%rsp), %rbx
	xorq	%r15, %rsi
	xorq	%rcx, %r9
	movq	-120(%rsp), %rbp
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %rdi
	xorq	%r15, %r12
	xorq	%rdx, %rax
	xorq	%rdx, %rbx
	rorx	$43, %r9, %r9
	xorq	%r14, %r10
	xorq	%r13, %rbp
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	rorx	$21, %r12, %r12
	rorx	$20, %rbp, %rbp
	movq	%r9, -120(%rsp)
	xorq	%r14, %rbx
	xorq	%r13, %r11
	rorx	$50, %rax, %rax
	xorq	%r13, %rsi
	movq	%r12, 32(%rsp)
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	movq	-32(%rsp), %r12
	xorq	%r15, %rsi
	xorq	%rcx, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, -112(%rsp)
	movq	(%rsp), %rsi
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	-88(%rsp), %rdi
	movq	8(%rsp), %rsi
	xorq	%r14, %rdi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	xorq	%r13, %rdi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	rorx	$37, %rsi, %rsi
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 40(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 48(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -120(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -64(%rsp)
	movq	%rbx, -56(%rsp)
	movq	-112(%rsp), %r11
	movq	-32(%rsp), %r10
	movq	(%rsp), %rdx
	movq	%rbp, -112(%rsp)
	movq	%r11, %rax
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	40(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	movq	-104(%rsp), %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-96(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rbp, %rcx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorb	$-120, %r15b
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r11, %rbp
	xorq	%r15, %rdx
	xorq	16(%rsp), %rbp
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	rorx	$63, %rbp, %r14
	xorq	%r12, %rbx
	xorq	%r10, %rdx
	xorq	%rdi, %rbx
	movq	48(%rsp), %rdi
	xorq	%rsi, %rbx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%r13, %r11
	xorq	-120(%rsp), %rcx
	xorq	(%rsp), %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rax, %rcx
	xorq	%r8, %rdx
	xorq	%rbp, %r15
	movq	-112(%rsp), %rbp
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r15, %rsi
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	xorq	%r15, %r12
	movq	-56(%rsp), %rbx
	rorx	$43, %r9, %r9
	xorq	%r14, %r10
	xorq	%r13, %rbp
	movq	%r9, -112(%rsp)
	rorx	$36, %rdi, %r8
	movq	-88(%rsp), %rdi
	rorx	$21, %r12, %r12
	xorq	%rdx, %rbx
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	xorq	%rdx, %rax
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	xorq	%r14, %rdi
	movq	%rsi, -48(%rsp)
	movq	-104(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	xorq	%rcx, %r12
	xorq	%r14, %rbx
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$19, %r11, %r11
	xorq	%r13, %rsi
	rorx	$61, %rbx, %rbx
	rorx	$39, %r12, %r12
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-120(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	%r15, %rdi
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	xorq	%rcx, %rdi
	xorq	-96(%rsp), %r15
	xorq	-24(%rsp), %rdx
	rorx	$8, %rdi, %rdi
	movq	%rdi, -120(%rsp)
	rorx	$25, %rdx, %rdi
	rorx	$2, %r15, %r15
	movq	-16(%rsp), %rdx
	xorq	-64(%rsp), %rcx
	movq	%rdi, 24(%rsp)
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-112(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-112(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-112(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 48(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -112(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rax, %r10
	movq	%r10, -32(%rsp)
	movq	%r9, %r10
	movq	-40(%rsp), %r9
	notq	%r10
	movq	%r10, %rax
	movq	-120(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%rdx, -24(%rsp)
	movq	8(%rsp), %rdx
	movq	%rdx, %rax
	movq	%rdx, %r11
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%r10, %rax
	notq	%r10
	andq	%rsi, %r10
	notq	%rsi
	xorq	%rax, %r9
	movq	%rsi, %rax
	movq	-120(%rsp), %rsi
	movq	%r9, %rdi
	movq	24(%rsp), %r9
	andq	%rdx, %rax
	xorq	%rbx, %r10
	xorq	%rax, %rsi
	movq	%rsi, (%rsp)
	movq	%rcx, %rsi
	notq	%rsi
	movq	%rsi, %rax
	andq	%r9, %rax
	movq	%rax, %rbx
	movq	%r9, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r9, %rsi
	movq	%r13, %r9
	notq	%r9
	movq	%r9, %rax
	andq	%r15, %rax
	notq	%r15
	movq	%rax, %r9
	andq	%rcx, %r15
	xorq	%r14, %r9
	xorq	%r13, %r15
	movq	%r9, 24(%rsp)
	movl	$2147516425, %r9d
	xorq	32(%rsp), %r9
	movq	%r15, %rax
	movq	-104(%rsp), %rcx
	movq	-16(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	movq	%rbx, 8(%rsp)
	xorq	%rbp, %rcx
	xorq	%r15, %rdx
	movq	-96(%rsp), %r14
	movq	%r8, -40(%rsp)
	movq	%rcx, %rbp
	xorq	%rbx, %rdx
	movq	%rdi, -8(%rsp)
	movq	-56(%rsp), %rcx
	xorq	%r8, %rbp
	xorq	%r9, %rdx
	movq	-64(%rsp), %r8
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	-80(%rsp), %r14
	movq	%r14, %rbx
	xorq	-24(%rsp), %rcx
	xorq	-112(%rsp), %rcx
	rorx	$63, %rbp, %r14
	xorq	%r12, %rbx
	xorq	(%rsp), %rcx
	xorq	%rdi, %rbx
	movq	48(%rsp), %rdi
	xorq	%rax, %rcx
	xorq	%rsi, %rbx
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	%rbx, %rcx
	rorx	$63, %rbx, %r13
	xorq	%r10, %r8
	movq	-56(%rsp), %rbx
	xorq	24(%rsp), %r8
	xorq	%rdx, %r13
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	%rcx, %r10
	xorq	%rcx, %rdi
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r15, %rsi
	xorq	%r15, %r12
	xorq	%rdx, %rbx
	rorx	$3, %rsi, %rsi
	movq	-120(%rsp), %rbp
	rorx	$43, %r10, %r10
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$21, %r12, %r12
	rorx	$36, %rdi, %r8
	xorq	%r14, %r9
	xorq	%r13, %rbp
	xorq	%rdx, %rax
	movq	%rsi, -48(%rsp)
	movq	-104(%rsp), %rsi
	xorq	%r14, %rbx
	xorq	%r13, %r11
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	xorq	%r13, %rsi
	movq	%r10, -120(%rsp)
	rorx	$63, %rsi, %r10
	movq	-80(%rsp), %rsi
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	-88(%rsp), %rdi
	xorq	%r14, %rsi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-112(%rsp), %rsi
	xorq	%rdx, %rsi
	xorq	%r14, %rdi
	xorq	-24(%rsp), %rdx
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	rorx	$37, %rsi, %rsi
	xorq	%r13, %rdi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r9, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r9, %rdx
	notq	%r9
	xorq	%rdx, %rdi
	andq	%rbp, %r9
	movq	-56(%rsp), %rdx
	movq	%r9, %rbp
	movq	-48(%rsp), %r9
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rbx, %rax
	movq	%r9, %rbx
	movq	%rax, -80(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -64(%rsp)
	movq	%rbx, -56(%rsp)
	movq	40(%rsp), %r11
	movq	-32(%rsp), %r9
	movq	(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	movq	%r11, %rax
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r10, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r9, %rax
	xorq	%rax, %r8
	movq	%r9, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r10, %rax
	notq	%r10
	xorq	%rax, %r9
	movq	%r10, %rax
	movq	-40(%rsp), %r10
	movq	%r8, -40(%rsp)
	movq	%r9, -32(%rsp)
	movq	8(%rsp), %r9
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r9, %rax
	movq	%r9, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r10, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r10
	movq	%r10, %rdi
	movq	%rdx, %r10
	notq	%r10
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r10
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r10
	andq	%r9, %rax
	movq	%rcx, %r9
	notq	%r9
	movq	%rax, %rsi
	movq	%r9, %rax
	movq	48(%rsp), %r9
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r9, %rax
	movq	%rax, %rbx
	movq	%r9, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r9, %rsi
	movq	%r13, %r9
	notq	%r9
	movq	%r9, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r9
	movq	-112(%rsp), %rcx
	xorq	%r13, %r15
	xorq	%r14, %r9
	movq	-104(%rsp), %r14
	movq	%r15, %rax
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	movq	%r9, 24(%rsp)
	xorq	%r15, %rdx
	movl	$2147483658, %r9d
	xorq	32(%rsp), %r9
	xorq	%rbx, %rdx
	xorq	%r9, %rdx
	xorq	-80(%rsp), %r14
	xorq	%rbp, %rcx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r10, %r8
	xorq	24(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%r13, %r11
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rax, %rcx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	movq	-120(%rsp), %rbp
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r15, %rsi
	rorx	$3, %rsi, %rsi
	xorq	%r14, %r9
	xorq	%rcx, %rdi
	xorq	%r13, %rbp
	movq	-56(%rsp), %rbx
	xorq	%r15, %r12
	xorq	%rcx, %r10
	xorq	%rdx, %rax
	rorx	$43, %r10, %r10
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	rorx	$20, %rbp, %rbp
	xorq	%rdx, %rbx
	movq	%r10, -120(%rsp)
	movq	-88(%rsp), %rdi
	rorx	$50, %rax, %rax
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$19, %r11, %r11
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	xorq	%r14, %rbx
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	xorq	%r13, %rsi
	xorq	%r14, %rdi
	rorx	$61, %rbx, %rbx
	rorx	$63, %rsi, %r10
	movq	-80(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, -112(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 40(%rsp)
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r9, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r9, %rdx
	notq	%r9
	xorq	%rdx, %rdi
	andq	%rbp, %r9
	movq	-56(%rsp), %rdx
	movq	%r9, %rbp
	movq	-48(%rsp), %r9
	movq	%rdi, 48(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -120(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rbx, %rax
	movq	%r9, %rbx
	movq	%rax, -80(%rsp)
	movq	%r9, %rax
	movq	-32(%rsp), %r9
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	-112(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r10, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r9, %rax
	xorq	%rax, %r8
	movq	%r9, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r10, %rax
	notq	%r10
	xorq	%rax, %r9
	movq	%r10, %rax
	movq	-40(%rsp), %r10
	movq	%r9, -32(%rsp)
	movq	8(%rsp), %r9
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r9, %rax
	movq	%r9, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r10, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r10
	movq	%r10, %rdi
	movq	%rdx, %r10
	notq	%r10
	andq	%rsi, %r10
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r10
	andq	%r9, %rax
	movq	%rcx, %r9
	notq	%r9
	movq	%rax, %rsi
	movq	%r9, %rax
	movq	40(%rsp), %r9
	xorq	%rdx, %rsi
	movq	%rsi, (%rsp)
	andq	%r9, %rax
	movq	%rax, %rbx
	movq	%r9, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r9, %rsi
	movq	%r13, %r9
	notq	%r9
	movq	%r9, %rax
	andq	%r15, %rax
	notq	%r15
	movq	%rax, %r9
	andq	%rcx, %r15
	xorq	%r14, %r9
	xorq	%r13, %r15
	movq	%r15, %rax
	movq	%r9, 24(%rsp)
	movl	$2147516555, %r9d
	xorq	32(%rsp), %r9
	movq	-88(%rsp), %r15
	movq	-16(%rsp), %rdx
	movq	%rbx, 8(%rsp)
	xorq	-48(%rsp), %r15
	movq	-104(%rsp), %rcx
	movq	%rbp, -112(%rsp)
	xorq	%r15, %rdx
	movq	-96(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r8, -40(%rsp)
	xorq	%rbx, %rdx
	xorq	%rbp, %rcx
	movq	%r14, %rbx
	movq	%rdi, -8(%rsp)
	xorq	%r12, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	-24(%rsp), %rcx
	xorq	%r8, %rbp
	xorq	%rdi, %rbx
	movq	-64(%rsp), %r8
	movq	48(%rsp), %rdi
	xorq	-120(%rsp), %rcx
	xorq	(%rsp), %rcx
	xorq	%rsi, %rbx
	xorq	%r11, %rbp
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	16(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%r10, %r8
	xorq	24(%rsp), %r8
	xorq	%r9, %rdx
	rorx	$63, %rbp, %r14
	rorx	$63, %rbx, %r13
	xorq	%rcx, %r14
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%rdx, %r13
	rorx	$63, %rdx, %rdx
	movq	-112(%rsp), %rbp
	movq	-56(%rsp), %rbx
	xorq	%r8, %rdx
	xorq	%r14, %r9
	xorq	%r15, %r12
	xorq	%rcx, %r10
	xorq	%rdx, %rax
	xorq	%r13, %rbp
	xorq	%rcx, %rdi
	xorq	%rdx, %rbx
	xorq	%r15, %rsi
	rorx	$44, %rbx, %rbx
	rorx	$3, %rsi, %rsi
	movq	%rbx, -56(%rsp)
	rorx	$43, %r10, %r10
	movq	-48(%rsp), %rbx
	movq	%rsi, -48(%rsp)
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	movq	-104(%rsp), %rsi
	movq	%r10, -112(%rsp)
	rorx	$20, %rbp, %rbp
	xorq	%r13, %r11
	movq	%r12, 32(%rsp)
	xorq	%r14, %rbx
	movq	-32(%rsp), %r12
	rorx	$50, %rax, %rax
	xorq	%r13, %rsi
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r10
	movq	-80(%rsp), %rsi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	-88(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r14, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-120(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r13, %rdi
	rorx	$37, %rsi, %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, -120(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 24(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r9, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-112(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-112(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-112(%rsp), %rdi
	andq	%r9, %rdx
	notq	%r9
	xorq	%rdx, %rdi
	andq	%rbp, %r9
	movq	-56(%rsp), %rdx
	movq	%r9, %rbp
	movq	-48(%rsp), %r9
	movq	%rdi, 48(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -112(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rbx, %rax
	movq	%r9, %rbx
	movq	%rax, -80(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -64(%rsp)
	movq	%rbx, -56(%rsp)
	movq	40(%rsp), %r11
	movq	-32(%rsp), %r9
	movq	(%rsp), %rdx
	movq	%r11, %rax
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r10, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r9, %rax
	xorq	%rax, %r8
	movq	%r9, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rax, %r9
	movq	%r9, -32(%rsp)
	movq	%r10, %r9
	movq	-40(%rsp), %r10
	notq	%r9
	movq	%r8, -40(%rsp)
	movq	%r9, %rax
	movq	-120(%rsp), %r9
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%rdx, -24(%rsp)
	movq	8(%rsp), %rdx
	movq	%rdx, %rax
	movq	%rdx, %r11
	notq	%rax
	andq	%r10, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	xorq	%rax, %r10
	movq	%rsi, %rax
	movq	-120(%rsp), %rsi
	movq	%r10, %rdi
	movq	24(%rsp), %r10
	andq	%rdx, %rax
	xorq	%rbx, %r9
	movq	-16(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	xorq	%rax, %rsi
	movq	%rdi, -8(%rsp)
	movq	%rsi, (%rsp)
	movq	%rcx, %rsi
	notq	%rsi
	movq	%rsi, %rax
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	movq	%rax, %r10
	andq	%rcx, %r15
	movq	-104(%rsp), %rcx
	xorq	%r14, %r10
	xorq	%r13, %r15
	movq	-96(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r10, 24(%rsp)
	movq	32(%rsp), %r10
	movq	%r15, %rax
	xorq	%rbp, %rcx
	vmovq	%xmm5, %r15
	movq	%rcx, %rbp
	xorq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r8, %rbp
	xorq	%r15, %rdx
	movq	-64(%rsp), %r8
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	rorx	$63, %rbp, %r14
	xorq	%r12, %rbx
	xorq	%r10, %rdx
	xorq	%rdi, %rbx
	movq	48(%rsp), %rdi
	xorq	%rsi, %rbx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	movq	-56(%rsp), %rcx
	rorx	$63, %rdx, %rdx
	xorq	-24(%rsp), %rcx
	xorq	-112(%rsp), %rcx
	xorq	%r8, %rdx
	rorx	$63, %r8, %r15
	xorq	(%rsp), %rcx
	xorq	%rbp, %r15
	movq	-120(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	movq	-56(%rsp), %rbx
	xorq	%r14, %r10
	xorq	%r15, %rsi
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	xorq	%rdx, %rbx
	rorx	$3, %rsi, %rsi
	xorq	%r15, %r12
	xorq	%rdx, %rax
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$43, %r9, %r9
	movq	%rsi, -48(%rsp)
	movq	-104(%rsp), %rsi
	rorx	$36, %rdi, %r8
	xorq	%r13, %rbp
	movq	%r9, -120(%rsp)
	movq	-88(%rsp), %rdi
	xorq	%r14, %rbx
	xorq	%r13, %r11
	xorq	%r13, %rsi
	rorx	$21, %r12, %r12
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r14, %rdi
	rorx	$61, %rbx, %rbx
	movq	%r12, 32(%rsp)
	rorx	$28, %rdi, %rdi
	movq	-32(%rsp), %r12
	rorx	$19, %r11, %r11
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-112(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	rorx	$9, %rcx, %rcx
	movq	%rdi, 48(%rsp)
	movq	-16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	movq	-56(%rsp), %rdx
	andq	%rbp, %r10
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm4, %rcx
	xorq	%r14, %r10
	xorq	%r13, %r15
	movq	%r15, %rax
	movq	%r10, 24(%rsp)
	movq	32(%rsp), %r15
	movq	-16(%rsp), %rdx
	movq	-104(%rsp), %r14
	movq	%rbx, 8(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	xorq	-80(%rsp), %r14
	movq	%rbp, -120(%rsp)
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	movq	%r8, -40(%rsp)
	xorq	%r15, %rdx
	xorq	%rbp, %rcx
	movq	%rdi, -8(%rsp)
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	-96(%rsp), %rcx
	xorq	%r11, %rbp
	xorq	(%rsp), %rcx
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	xorq	%r10, %rdx
	xorq	%rdi, %r8
	xorq	%rax, %rcx
	xorq	-32(%rsp), %r8
	rorx	$63, %rbp, %r14
	xorq	%r9, %r8
	rorx	$63, %rbx, %r13
	xorq	24(%rsp), %r8
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	movq	-56(%rsp), %rbx
	xorq	%rdx, %r13
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r15, %rsi
	xorq	%r15, %r12
	xorq	%rdx, %rbx
	rorx	$3, %rsi, %rsi
	movq	-120(%rsp), %rbp
	rorx	$43, %r9, %r9
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	xorq	%rdx, %rax
	xorq	%r14, %r10
	xorq	%r13, %rbp
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	xorq	%r14, %rbx
	rorx	$20, %rbp, %rbp
	movq	%r9, -120(%rsp)
	xorq	%r13, %r11
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	xorq	%r13, %rsi
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%rcx, %r12
	xorq	%r15, %rsi
	rorx	$39, %r12, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	-88(%rsp), %rdi
	movq	8(%rsp), %rsi
	xorq	%r14, %rdi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	xorq	%r13, %rdi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	rorx	$37, %rsi, %rsi
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -64(%rsp)
	movq	%rbx, -56(%rsp)
	movq	40(%rsp), %r11
	movq	-32(%rsp), %r10
	movq	(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	movq	%r11, %rax
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm3, %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	%r10, %rdx
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%rdx, %r13
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rax, %rcx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	movq	-120(%rsp), %rbp
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r15, %rsi
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	xorq	%r15, %r12
	rorx	$43, %r9, %r9
	movq	-56(%rsp), %rbx
	movq	%r9, -120(%rsp)
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	xorq	%r14, %r10
	xorq	%r13, %rbp
	xorq	%r13, %r11
	xorq	%rdx, %rbx
	movq	-88(%rsp), %rdi
	movq	%r12, 32(%rsp)
	xorq	%rdx, %rax
	rorx	$44, %rbx, %rbx
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$19, %r11, %r11
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	xorq	%r14, %rdi
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	movq	-32(%rsp), %r12
	xorq	%r14, %rbx
	xorq	%r13, %rsi
	rorx	$61, %rbx, %rbx
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	xorq	-24(%rsp), %rdx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	40(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm2, %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	movq	-16(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	movq	-112(%rsp), %rcx
	xorq	-48(%rsp), %r15
	movq	%rbx, 8(%rsp)
	xorq	%r15, %rdx
	movq	-104(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r8, -40(%rsp)
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rdi, -8(%rsp)
	movq	%rcx, %rbp
	xorq	%r12, %rbx
	xorq	%r10, %rdx
	movq	-56(%rsp), %rcx
	xorq	%r8, %rbp
	movq	-64(%rsp), %r8
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	-24(%rsp), %rcx
	xorq	-96(%rsp), %rcx
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	xorq	(%rsp), %rcx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rax, %rcx
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	%rdx, %r13
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	xorq	%rcx, %r9
	movq	-56(%rsp), %rbx
	xorq	%r15, %rsi
	movq	-120(%rsp), %rbp
	xorq	%rcx, %rdi
	rorx	$3, %rsi, %rsi
	xorq	%r15, %r12
	xorq	%r14, %r10
	xorq	%rdx, %rax
	xorq	%rdx, %rbx
	rorx	$43, %r9, %r9
	movq	%r9, -120(%rsp)
	xorq	%r13, %rbp
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	rorx	$36, %rdi, %r8
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	rorx	$21, %r12, %r12
	xorq	%r13, %r11
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	xorq	%r14, %rbx
	rorx	$20, %rbp, %rbp
	xorq	%r13, %rsi
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%rcx, %r12
	rorx	$39, %r12, %r12
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	-88(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r14, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	%r13, %rdi
	xorq	-24(%rsp), %rdx
	rorx	$37, %rsi, %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 48(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -112(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -104(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 56(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -64(%rsp)
	movq	%rbx, -56(%rsp)
	movq	40(%rsp), %r11
	movq	-32(%rsp), %r10
	movq	(%rsp), %rdx
	movq	%rbp, -120(%rsp)
	movq	%r11, %rax
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r8, -40(%rsp)
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	movq	%rdi, -8(%rsp)
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	48(%rsp), %r10
	xorq	%rdx, %rsi
	movq	-16(%rsp), %rdx
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rbx, 8(%rsp)
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	vmovq	%xmm1, %rcx
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	-104(%rsp), %r14
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	%rcx, %r15
	movq	-112(%rsp), %rcx
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	xorq	%r15, %rdx
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	%r10, %rdx
	xorq	%r8, %rbp
	xorq	-80(%rsp), %r14
	movq	-64(%rsp), %r8
	movq	%r14, %rbx
	xorq	%r11, %rbp
	xorq	16(%rsp), %rbp
	xorq	%r12, %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %rbx
	movq	56(%rsp), %rdi
	xorq	%rsi, %rbx
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	-24(%rsp), %rcx
	xorq	%r13, %r11
	xorq	-96(%rsp), %rcx
	xorq	(%rsp), %rcx
	rorx	$63, %r8, %r15
	rorx	$63, %rdx, %rdx
	xorq	%rax, %rcx
	xorq	%rbp, %r15
	xorq	%r8, %rdx
	movq	-120(%rsp), %rbp
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r15, %rsi
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %r9
	xorq	%rcx, %rdi
	xorq	%r15, %r12
	movq	-56(%rsp), %rbx
	rorx	$43, %r9, %r9
	xorq	%r14, %r10
	xorq	%r13, %rbp
	movq	%r9, -120(%rsp)
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	movq	-88(%rsp), %rdi
	xorq	%rdx, %rbx
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	xorq	%rdx, %rax
	rorx	$44, %rbx, %rbx
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	rorx	$19, %r11, %r11
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	movq	%rsi, -48(%rsp)
	movq	-112(%rsp), %rsi
	xorq	%r14, %rbx
	xorq	%r13, %rsi
	rorx	$61, %rbx, %rbx
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r15, %rsi
	xorq	%rcx, %r12
	xorq	%r14, %rdi
	rorx	$58, %rsi, %rsi
	movq	%rsi, -112(%rsp)
	movq	(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	rorx	$39, %r12, %r12
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-96(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, -40(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-104(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, -8(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 40(%rsp)
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rdi
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-120(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-120(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-120(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, 48(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -120(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -80(%rsp)
	movq	%r10, %rax
	movq	-32(%rsp), %r10
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	-112(%rsp), %r11
	andq	%rdx, %r8
	movq	(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	-8(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	-40(%rsp), %r9
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%r10, %rax
	movq	%r10, %r11
	movq	%rdx, -24(%rsp)
	movq	24(%rsp), %rdx
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r9
	movq	%r9, %rdi
	movq	%rdx, %r9
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	movq	%rsi, %rax
	xorq	%rbx, %r9
	andq	%r10, %rax
	movq	%rcx, %r10
	notq	%r10
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	40(%rsp), %r10
	xorq	%rdx, %rsi
	movq	%rsi, (%rsp)
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r10
	xorq	%r13, %r15
	xorq	%r14, %r10
	movq	%r15, %rax
	movq	32(%rsp), %r15
	movq	%r10, 24(%rsp)
	xorq	$32778, %r15
	movq	%r15, %r10
	movq	-88(%rsp), %r15
	movq	-16(%rsp), %rdx
	movq	%rbx, 8(%rsp)
	xorq	-48(%rsp), %r15
	movq	-104(%rsp), %rcx
	movq	%rbp, -112(%rsp)
	xorq	%r15, %rdx
	movq	-96(%rsp), %r14
	xorq	-80(%rsp), %r14
	movq	%r8, -40(%rsp)
	xorq	%rbx, %rdx
	xorq	%rbp, %rcx
	movq	%r14, %rbx
	movq	%rdi, -8(%rsp)
	xorq	%r12, %rbx
	movq	%rcx, %rbp
	movq	-56(%rsp), %rcx
	xorq	-24(%rsp), %rcx
	xorq	%r8, %rbp
	xorq	%rdi, %rbx
	movq	-64(%rsp), %r8
	movq	48(%rsp), %rdi
	xorq	-120(%rsp), %rcx
	xorq	(%rsp), %rcx
	xorq	%rsi, %rbx
	xorq	%r11, %rbp
	xorq	%rax, %rcx
	xorq	16(%rsp), %rbp
	xorq	%rdi, %r8
	xorq	-32(%rsp), %r8
	xorq	%r10, %rdx
	xorq	%r9, %r8
	rorx	$63, %rbp, %r14
	xorq	24(%rsp), %r8
	xorq	%rcx, %r14
	rorx	$63, %rbx, %r13
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%rdx, %r13
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r14, %r10
	movq	-56(%rsp), %rbx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	%rcx, %rdi
	movq	-112(%rsp), %rbp
	xorq	%r15, %r12
	xorq	%rcx, %r9
	xorq	%rdx, %rax
	xorq	%rdx, %rbx
	rorx	$43, %r9, %r9
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	xorq	%r13, %rbp
	movq	%r9, -112(%rsp)
	rorx	$20, %rbp, %rbp
	rorx	$50, %rax, %rax
	xorq	%r14, %rbx
	xorq	%r15, %rsi
	movq	%r12, 32(%rsp)
	movq	-32(%rsp), %r12
	rorx	$3, %rsi, %rsi
	movq	%rsi, -48(%rsp)
	xorq	%r13, %r11
	movq	-104(%rsp), %rsi
	rorx	$61, %rbx, %rbx
	rorx	$19, %r11, %r11
	xorq	%rcx, %r12
	xorq	%r13, %rsi
	rorx	$39, %r12, %r12
	rorx	$63, %rsi, %r9
	movq	-80(%rsp), %rsi
	xorq	%r15, %rsi
	rorx	$58, %rsi, %rsi
	movq	%rsi, 40(%rsp)
	movq	(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -32(%rsp)
	movq	8(%rsp), %rsi
	movq	-88(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r14, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, (%rsp)
	movq	-120(%rsp), %rsi
	rorx	$28, %rdi, %rdi
	movq	%rdi, 8(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-24(%rsp), %rdx
	xorq	%r13, %rdi
	rorx	$37, %rsi, %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, 48(%rsp)
	movq	-8(%rsp), %rdi
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, 56(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, -120(%rsp)
	rorx	$25, %rdx, %rdi
	movq	-16(%rsp), %rdx
	movq	%rdi, 24(%rsp)
	movq	32(%rsp), %rdi
	rorx	$9, %rcx, %rcx
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r10, %rdx
	movq	%rdx, 16(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-112(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-112(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-112(%rsp), %rdi
	andq	%r10, %rdx
	notq	%r10
	xorq	%rdx, %rdi
	andq	%rbp, %r10
	movq	-56(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	movq	%rdi, -112(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -88(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -80(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rbx, %rax
	movq	%r10, %rbx
	movq	%rax, -64(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdx, %r8
	xorq	%r11, %rax
	xorq	%r8, %rbx
	movq	%rax, -56(%rsp)
	movq	%rbx, -48(%rsp)
	movq	40(%rsp), %r11
	movq	-32(%rsp), %r10
	movq	(%rsp), %rdx
	movq	%r11, %rax
	movq	56(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r9, %r8
	movq	%r8, -40(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r10, %rax
	xorq	%rax, %r8
	movq	%r10, %rax
	notq	%rax
	movq	%r8, -32(%rsp)
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rax, %r10
	movq	%r10, -24(%rsp)
	movq	%r9, %r10
	movq	48(%rsp), %r9
	notq	%r10
	movq	%r10, %rax
	movq	-120(%rsp), %r10
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%rdx, -16(%rsp)
	movq	8(%rsp), %rdx
	movq	%rdx, %rax
	movq	%rdx, %r11
	notq	%rax
	andq	%r9, %rax
	xorq	%rsi, %rax
	movq	%rax, -8(%rsp)
	movq	%r9, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%r10, %rax
	notq	%r10
	andq	%rsi, %r10
	notq	%rsi
	xorq	%rax, %r9
	movq	%rsi, %rax
	movq	-120(%rsp), %rsi
	movq	%r9, %rdi
	movq	24(%rsp), %r9
	andq	%rdx, %rax
	xorq	%rbx, %r10
	movq	-8(%rsp), %rdx
	movq	%rdi, (%rsp)
	xorq	%rax, %rsi
	movq	%rbp, -120(%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, %rsi
	notq	%rsi
	movq	%rsi, %rax
	andq	%r9, %rax
	movq	%rax, %rbx
	movq	%r9, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 24(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r9, %rsi
	movq	%r13, %r9
	notq	%r9
	movq	%r9, %rax
	andq	%r15, %rax
	notq	%r15
	andq	%rcx, %r15
	movq	%rax, %r9
	movq	-104(%rsp), %rcx
	xorq	%r13, %r15
	xorq	%r14, %r9
	movq	-96(%rsp), %r14
	xorq	-64(%rsp), %r14
	movq	%r15, %rax
	movq	-80(%rsp), %r15
	xorq	-40(%rsp), %r15
	xorq	%rbp, %rcx
	xorq	%r15, %rdx
	movq	%r9, 32(%rsp)
	movq	%rcx, %rbp
	movabsq	$-9223372034707292150, %r9
	xorq	%rbx, %rdx
	xorq	16(%rsp), %r9
	movq	%rbx, 16(%rsp)
	movq	%r14, %rbx
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	-56(%rsp), %r8
	xorq	%r9, %rdx
	xorq	%rdi, %rbx
	movq	-112(%rsp), %rdi
	xorq	%r11, %rbp
	xorq	24(%rsp), %rbp
	xorq	%rsi, %rbx
	rorx	$63, %rbp, %r14
	xorq	%rdi, %r8
	xorq	-24(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	%rdx, %r13
	xorq	%r10, %r8
	xorq	32(%rsp), %r8
	movq	-48(%rsp), %rcx
	rorx	$63, %rdx, %rdx
	xorq	-16(%rsp), %rcx
	xorq	-88(%rsp), %rcx
	rorx	$63, %r8, %r15
	xorq	%rbp, %r15
	xorq	8(%rsp), %rcx
	movq	-120(%rsp), %rbp
	xorq	%r8, %rdx
	xorq	%rax, %rcx
	xorq	%rcx, %r14
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	movq	-48(%rsp), %rbx
	xorq	%r14, %r9
	xorq	%r13, %rbp
	xorq	%r15, %r12
	xorq	%r15, %rsi
	xorq	%rdx, %rbx
	rorx	$3, %rsi, %rsi
	xorq	%rcx, %r10
	xorq	%rcx, %rdi
	rorx	$44, %rbx, %rbx
	movq	%rbx, -48(%rsp)
	movq	-40(%rsp), %rbx
	rorx	$43, %r10, %r10
	movq	%rsi, -40(%rsp)
	movq	-104(%rsp), %rsi
	rorx	$36, %rdi, %r8
	rorx	$21, %r12, %r12
	movq	%r10, -112(%rsp)
	movq	-80(%rsp), %rdi
	xorq	%rdx, %rax
	xorq	%r14, %rbx
	xorq	%r13, %rsi
	movq	%r12, 40(%rsp)
	movq	-24(%rsp), %r12
	rorx	$20, %rbp, %rbp
	rorx	$63, %rsi, %r10
	movq	-64(%rsp), %rsi
	xorq	%r14, %rdi
	xorq	%r13, %r11
	rorx	$28, %rdi, %rdi
	xorq	%rcx, %r12
	rorx	$50, %rax, %rax
	rorx	$61, %rbx, %rbx
	xorq	%r15, %rsi
	rorx	$19, %r11, %r11
	rorx	$39, %r12, %r12
	rorx	$58, %rsi, %rsi
	movq	%rsi, 48(%rsp)
	movq	8(%rsp), %rsi
	xorq	%rdx, %rsi
	rorx	$56, %rsi, %rsi
	movq	%rsi, -24(%rsp)
	movq	16(%rsp), %rsi
	movq	%rdi, 16(%rsp)
	movq	-32(%rsp), %rdi
	xorq	%r14, %rsi
	xorq	%r13, %rdi
	rorx	$46, %rsi, %rsi
	movq	%rsi, 8(%rsp)
	movq	-88(%rsp), %rsi
	rorx	$54, %rdi, %rdi
	movq	%rdi, 56(%rsp)
	movq	(%rsp), %rdi
	xorq	%rdx, %rsi
	xorq	-16(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$37, %rsi, %rsi
	rorx	$49, %rdi, %rdi
	movq	%rdi, (%rsp)
	movq	32(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%rcx, %rdi
	xorq	-56(%rsp), %rcx
	rorx	$8, %rdi, %rdi
	movq	%rdi, -120(%rsp)
	rorx	$25, %rdx, %rdi
	rorx	$9, %rcx, %rcx
	movq	%rdi, 32(%rsp)
	movq	-8(%rsp), %rdx
	movq	40(%rsp), %rdi
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	24(%rsp), %rdx
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	xorq	%r9, %rdx
	movq	%rdx, -8(%rsp)
	movq	%rdi, %rdx
	notq	%rdx
	andq	-112(%rsp), %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	-112(%rsp), %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%rdx, %rdi
	movq	%rax, %rdx
	movq	%rdi, -96(%rsp)
	notq	%rdx
	movq	-112(%rsp), %rdi
	andq	%r9, %rdx
	notq	%r9
	xorq	%rdx, %rdi
	andq	%rbp, %r9
	movq	-48(%rsp), %rdx
	movq	%r9, %rbp
	movq	-40(%rsp), %r9
	movq	%rdi, 40(%rsp)
	xorq	%rax, %rbp
	movq	%rdx, %rax
	notq	%rax
	movq	%rbp, -112(%rsp)
	movq	%rdx, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r11, %rax
	xorq	%rax, %rbp
	movq	%r11, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rbx, %rax
	movq	%r9, %rbx
	movq	%rax, -80(%rsp)
	movq	%r9, %rax
	movq	-24(%rsp), %r9
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%r11, %rax
	movq	48(%rsp), %r11
	andq	%rdx, %r8
	movq	8(%rsp), %rdx
	movq	%rax, -64(%rsp)
	xorq	%r8, %rbx
	movq	%r11, %rax
	movq	%rbx, -56(%rsp)
	movq	(%rsp), %rbx
	notq	%rax
	andq	%r12, %rax
	movq	%rax, %r8
	xorq	%r10, %r8
	movq	%r8, -48(%rsp)
	movq	%r12, %r8
	notq	%r8
	movq	%r8, %rax
	movq	%r11, %r8
	andq	%r9, %rax
	xorq	%rax, %r8
	movq	%r9, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rax, %r12
	movq	%rdx, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rax, %r9
	movq	%r9, -32(%rsp)
	movq	%r10, %r9
	movq	56(%rsp), %r10
	notq	%r9
	movq	%r9, %rax
	movq	-120(%rsp), %r9
	andq	%r11, %rax
	xorq	%rax, %rdx
	movq	%rdx, -24(%rsp)
	movq	16(%rsp), %rdx
	movq	%rdx, %rax
	movq	%rdx, %r11
	notq	%rax
	andq	%r10, %rax
	xorq	%rsi, %rax
	movq	%rax, -16(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	xorq	%rax, %r11
	movq	%rbx, %rax
	notq	%rax
	andq	%r9, %rax
	notq	%r9
	andq	%rsi, %r9
	notq	%rsi
	xorq	%rax, %r10
	movq	%rsi, %rax
	movq	-120(%rsp), %rsi
	movq	%r10, %rdi
	movq	32(%rsp), %r10
	andq	%rdx, %rax
	xorq	%rbx, %r9
	xorq	%rax, %rsi
	movq	%rsi, (%rsp)
	movq	%rcx, %rsi
	notq	%rsi
	movq	%rsi, %rax
	andq	%r10, %rax
	movq	%rax, %rbx
	movq	%r10, %rax
	notq	%rax
	xorq	%r15, %rbx
	andq	%r14, %rax
	movq	%rax, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 16(%rsp)
	movq	%r14, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r10, %rsi
	movq	%r13, %r10
	notq	%r10
	movq	%r10, %rax
	andq	%r15, %rax
	notq	%r15
	movq	%rax, %r10
	andq	%rcx, %r15
	xorq	%r14, %r10
	xorq	%r13, %r15
	movq	%r10, 24(%rsp)
	movq	-8(%rsp), %r10
	movq	%r15, %rax
	vmovq	%xmm0, %r15
	movq	-16(%rsp), %rdx
	movq	-104(%rsp), %rcx
	movq	%rbx, 8(%rsp)
	xorq	%r15, %r10
	movq	-88(%rsp), %r15
	xorq	-48(%rsp), %r15
	movq	%rbp, -120(%rsp)
	xorq	%r15, %rdx
	movq	-96(%rsp), %r14
	xorq	-80(%rsp), %r14
	xorq	%rbp, %rcx
	xorq	%rbx, %rdx
	movq	%r14, %rbx
	movq	%rcx, %rbp
	movq	%r8, -40(%rsp)
	xorq	%r12, %rbx
	xorq	%r8, %rbp
	movq	%rdi, -8(%rsp)
	movq	-64(%rsp), %r8
	xorq	%rdi, %rbx
	movq	40(%rsp), %rdi
	movq	-56(%rsp), %rcx
	xorq	%r10, %rdx
	xorq	-24(%rsp), %rcx
	xorq	-112(%rsp), %rcx
	xorq	%rsi, %rbx
	xorq	%r11, %rbp
	xorq	%rdi, %r8
	xorq	(%rsp), %rcx
	xorq	-32(%rsp), %r8
	rorx	$63, %rbx, %r13
	xorq	16(%rsp), %rbp
	xorq	%rax, %rcx
	xorq	%r9, %r8
	xorq	24(%rsp), %r8
	xorq	%rdx, %r13
	rorx	$63, %rbp, %r14
	rorx	$63, %r8, %r15
	xorq	%rcx, %r14
	xorq	%rbp, %r15
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%r13, %r11
	rorx	$63, %rdx, %rdx
	xorq	%r8, %rdx
	xorq	%r15, %rsi
	xorq	%rcx, %rdi
	movq	-56(%rsp), %rbx
	rorx	$19, %r11, %r11
	xorq	%rdx, %rax
	xorq	%r14, %r10
	movq	-120(%rsp), %rbp
	rorx	$3, %rsi, %rsi
	rorx	$36, %rdi, %r8
	xorq	%r15, %r12
	xorq	%rdx, %rbx
	movq	%rsi, 32(%rsp)
	movq	-104(%rsp), %rsi
	rorx	$21, %r12, %r12
	rorx	$44, %rbx, %rbx
	movq	%rbx, -56(%rsp)
	movq	-48(%rsp), %rbx
	xorq	%r13, %rbp
	movq	%r11, -48(%rsp)
	movq	-80(%rsp), %r11
	rorx	$20, %rbp, %rbp
	xorq	%r13, %rsi
	xorq	%r14, %rbx
	xorq	%rcx, %r9
	rorx	$50, %rax, %rax
	rorx	$63, %rsi, %rsi
	xorq	%r15, %r11
	rorx	$43, %r9, %r9
	rorx	$61, %rbx, %rbx
	rorx	$58, %r11, %r11
	movq	%r11, 40(%rsp)
	movq	-32(%rsp), %r11
	xorq	%rcx, %r11
	rorx	$39, %r11, %r11
	movq	%r11, -32(%rsp)
	movq	(%rsp), %r11
	xorq	%rdx, %r11
	rorx	$56, %r11, %r11
	movq	%r11, (%rsp)
	movq	8(%rsp), %r11
	movq	-88(%rsp), %rdi
	xorq	%r14, %r11
	rorx	$46, %r11, %r11
	movq	%r11, 8(%rsp)
	movq	-112(%rsp), %r11
	xorq	%r14, %rdi
	rorx	$28, %rdi, %rdi
	movq	%rdi, -112(%rsp)
	movq	-40(%rsp), %rdi
	xorq	%rdx, %r11
	xorq	-24(%rsp), %rdx
	rorx	$25, %rdx, %rdx
	movq	%rdx, 64(%rsp)
	xorq	%r13, %rdi
	movq	-16(%rsp), %rdx
	rorx	$54, %rdi, %rdi
	movq	%rdi, 48(%rsp)
	movq	-8(%rsp), %rdi
	rorx	$37, %r11, %r11
	xorq	%r14, %rdx
	rorx	$23, %rdx, %r14
	movq	16(%rsp), %rdx
	xorq	%r15, %rdi
	xorq	-96(%rsp), %r15
	rorx	$49, %rdi, %rdi
	movq	%rdi, 56(%rsp)
	movq	24(%rsp), %rdi
	rorx	$2, %r15, %r15
	xorq	%r13, %rdx
	rorx	$62, %rdx, %r13
	movq	%rbp, %rdx
	xorq	%rcx, %rdi
	xorq	-64(%rsp), %rcx
	notq	%rdx
	rorx	$8, %rdi, %rdi
	movq	%rdi, 24(%rsp)
	rorx	$9, %rcx, %rcx
	andq	%r12, %rdx
	movq	-56(%rsp), %rdi
	xorq	%r10, %rdx
	movq	%rdx, 72(%rsp)
	movq	%r12, %rdx
	notq	%rdx
	andq	%r9, %rdx
	xorq	%rbp, %rdx
	movq	%rdx, -104(%rsp)
	movq	%r9, %rdx
	notq	%rdx
	andq	%rax, %rdx
	xorq	%r12, %rdx
	movq	%rax, %r12
	notq	%r12
	movq	%rdx, -80(%rsp)
	movq	%r12, %rdx
	andq	%r10, %rdx
	notq	%r10
	andq	%rbp, %r10
	movq	%rdx, %r12
	movq	-32(%rsp), %rdx
	movq	%r10, %rbp
	movq	-48(%rsp), %r10
	xorq	%r9, %r12
	movq	(%rsp), %r9
	xorq	%rax, %rbp
	movq	%rdi, %rax
	movq	%r12, -120(%rsp)
	movq	32(%rsp), %r12
	notq	%rax
	movq	%rbp, -96(%rsp)
	movq	%rdi, %rbp
	andq	%rbx, %rax
	xorq	%r8, %rax
	movq	%rax, -88(%rsp)
	movq	%rbx, %rax
	notq	%rax
	andq	%r10, %rax
	xorq	%rax, %rbp
	movq	%r10, %rax
	notq	%rax
	andq	%r12, %rax
	xorq	%rbx, %rax
	movq	%rax, -64(%rsp)
	movq	%r12, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	andq	%rdi, %r8
	movq	40(%rsp), %rdi
	xorq	%rax, %r10
	movq	%r10, -56(%rsp)
	xorq	%r8, %r12
	movq	%rdi, %rax
	movq	%rdi, %r10
	notq	%rax
	andq	%rdx, %rax
	xorq	%rsi, %rax
	movq	%rax, -40(%rsp)
	movq	%rdx, %rax
	notq	%rax
	andq	%r9, %rax
	xorq	%rax, %r10
	movq	%r9, %rax
	movq	%r10, -32(%rsp)
	movq	8(%rsp), %r8
	notq	%rax
	movq	-112(%rsp), %rbx
	movq	24(%rsp), %r10
	movq	%rbp, -112(%rsp)
	andq	%r8, %rax
	movq	%r12, -48(%rsp)
	xorq	%rax, %rdx
	movq	%r8, %rax
	notq	%rax
	andq	%rsi, %rax
	notq	%rsi
	xorq	%rax, %r9
	movq	%rsi, %rax
	movq	%rbx, %rsi
	andq	%rdi, %rax
	notq	%rsi
	movq	48(%rsp), %rdi
	movq	%r9, -24(%rsp)
	xorq	%rax, %r8
	movq	%rsi, %rax
	movq	%r8, -16(%rsp)
	movq	56(%rsp), %r8
	andq	%rdi, %rax
	movq	%rax, %rsi
	movq	%r8, %rax
	xorq	%r11, %rsi
	notq	%rax
	movq	%rsi, -8(%rsp)
	movq	%rdi, %rsi
	andq	%r10, %rax
	notq	%rsi
	xorq	%rax, %rdi
	andq	%r8, %rsi
	movq	%rdi, (%rsp)
	movq	%r10, %rdi
	xorq	%rbx, %rsi
	notq	%rdi
	movq	%rdi, %r9
	movq	%r11, %rdi
	notq	%rdi
	andq	%r11, %r9
	movq	64(%rsp), %r11
	movq	%rdi, %rax
	movq	%r10, %rdi
	movq	%r14, %r10
	xorq	%r8, %r9
	andq	%rbx, %rax
	movq	%rcx, %r8
	notq	%r10
	xorq	%rax, %rdi
	andq	%r13, %r10
	movq	%r11, %rax
	notq	%r8
	xorq	%r11, %r10
	andq	%r11, %r8
	notq	%rax
	movq	%r13, %r11
	andq	%r14, %rax
	notq	%r11
	xorq	%r15, %r8
	movq	%rax, %rbx
	movq	%r11, %rax
	movq	-120(%rsp), %r11
	xorq	-56(%rsp), %r11
	xorq	%rcx, %rbx
	andq	%r15, %rax
	notq	%r15
	xorq	-24(%rsp), %r11
	movq	%rbx, 8(%rsp)
	movq	%rax, %rbx
	andq	%rcx, %r15
	movq	-80(%rsp), %rcx
	xorq	%r14, %rbx
	movq	-104(%rsp), %r14
	xorq	-64(%rsp), %rcx
	xorq	%r13, %r15
	movq	%rbx, 16(%rsp)
	movq	72(%rsp), %rbx
	xorq	%r9, %r11
	movabsq	$-9223372036854742912, %rax
	xorq	%rbp, %r14
	movq	-32(%rsp), %rbp
	xorq	16(%rsp), %r11
	xorq	%rax, %rbx
	movq	-88(%rsp), %rax
	xorq	-40(%rsp), %rax
	xorq	-8(%rsp), %rax
	movq	%rbx, 24(%rsp)
	xorq	%r14, %rbp
	rorx	$63, %r11, %r14
	xorq	%r8, %rax
	xorq	%rsi, %rbp
	xorq	8(%rsp), %rbp
	xorq	%rbx, %rax
	movq	%rcx, %rbx
	movq	-16(%rsp), %rcx
	rorx	$63, %rbp, %r13
	xorq	%rdx, %rbx
	xorq	(%rsp), %rbx
	xorq	%r10, %rbx
	xorq	%r12, %rcx
	xorq	-96(%rsp), %rcx
	xorq	%rbp, %r14
	xorq	%rdi, %rcx
	rorx	$63, %rbx, %r12
	xorq	%rax, %r12
	xorq	%r14, %r10
	xorq	%r15, %rcx
	rorx	$63, %rax, %rax
	xorq	%r11, %rax
	rorx	$3, %r10, %r10
	xorq	%rcx, %r13
	rorx	$63, %rcx, %rcx
	xorq	%rbx, %rcx
	xorq	%rax, %r15
	xorq	%r13, %r8
	rorx	$50, %r15, %r15
	xorq	%rcx, %r9
	xorq	%r14, %rdx
	movq	24(%rsp), %rbx
	rorx	$43, %r9, %r9
	xorq	%r12, %rsi
	rorx	$21, %rdx, %rdx
	rorx	$19, %rsi, %rsi
	xorq	%r13, %rbx
	movq	%rbx, 24(%rsp)
	movq	-112(%rsp), %r11
	movq	%r10, 64(%rsp)
	movq	-104(%rsp), %r10
	xorq	%r12, %r11
	movq	%r15, 56(%rsp)
	movq	-40(%rsp), %rbx
	rorx	$20, %r11, %rbp
	movq	%rbp, 32(%rsp)
	movq	-120(%rsp), %rbp
	xorq	%r12, %r10
	movq	-32(%rsp), %r15
	xorq	%r13, %rbx
	movq	%r9, 48(%rsp)
	xorq	%rcx, %rbp
	movq	-48(%rsp), %r9
	rorx	$61, %rbx, %rbx
	movq	%rbx, -112(%rsp)
	rorx	$36, %rbp, %r11
	movq	%r11, 40(%rsp)
	rorx	$63, %r10, %r11
	xorq	%r12, %r15
	movq	-64(%rsp), %r10
	rorx	$54, %r15, %rbx
	movq	-16(%rsp), %r15
	xorq	%rax, %r9
	rorx	$44, %r9, %rbp
	movq	-24(%rsp), %r9
	movq	%rbp, -120(%rsp)
	xorq	%r14, %r10
	xorq	%rax, %r15
	movq	16(%rsp), %rbp
	movq	%rsi, -48(%rsp)
	rorx	$58, %r10, %r10
	movq	%r10, -104(%rsp)
	movq	%rdi, %r10
	xorq	%rcx, %r9
	rorx	$46, %r8, %rdi
	movq	-96(%rsp), %r8
	movq	%rdi, -64(%rsp)
	xorq	%rax, %r10
	xorq	%rcx, %rbp
	xorq	-56(%rsp), %rcx
	rorx	$56, %r10, %r10
	rorx	$39, %r9, %r9
	xorq	%rax, %r8
	movq	32(%rsp), %rax
	rorx	$8, %rbp, %rbp
	rorx	$9, %rcx, %rcx
	rorx	$37, %r8, %rdi
	movq	-88(%rsp), %r8
	movq	%rdi, -96(%rsp)
	rorx	$25, %r15, %r15
	notq	%rax
	xorq	%r13, %r8
	xorq	-8(%rsp), %r13
	rorx	$28, %r8, %r8
	movq	%r8, -88(%rsp)
	movq	(%rsp), %r8
	rorx	$23, %r13, %r13
	xorq	%r14, %r8
	xorq	-80(%rsp), %r14
	xorq	8(%rsp), %r12
	andq	%rdx, %rax
	rorx	$62, %r12, %r12
	xorq	24(%rsp), %rax
	rorx	$2, %r14, %r14
	rorx	$49, %r8, %r8
	movq	%r12, -80(%rsp)
	movq	-112(%rsp), %rdi
	movq	%r10, %r12
	movq	-120(%rsp), %rsi
	notq	%r12
	notq	%rdi
	andq	-48(%rsp), %rdi
	xorq	%rdi, %rsi
	movq	-64(%rsp), %rdi
	movq	%rsi, -56(%rsp)
	andq	%r12, %rdi
	movq	%rdi, %r12
	movq	-96(%rsp), %rdi
	xorq	%r9, %r12
	movq	%r12, -40(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r12, %rdi
	movq	%rdi, %r12
	movq	%r14, %rdi
	notq	%rdi
	xorq	%r8, %r12
	andq	%rcx, %rdi
	xorq	-80(%rsp), %rdi
	movq	%r12, -24(%rsp)
	movq	%rdi, -16(%rsp)
	movl	$2147483649, %edi
	movq	-88(%rsp), %r12
	xorq	%rax, %rdi
	movq	40(%rsp), %rax
	movq	%rdi, %rsi
	movq	-120(%rsp), %rdi
	notq	%r12
	xorq	%r11, %rax
	xorq	-96(%rsp), %rax
	movq	%rsi, -32(%rsp)
	xorq	%r14, %rax
	notq	%rdi
	andq	-112(%rsp), %rdi
	xorq	%rdi, %rax
	movq	-104(%rsp), %rdi
	notq	%rdi
	andq	%r9, %rdi
	notq	%r9
	xorq	%rdi, %rax
	movq	%r12, %rdi
	movq	%rcx, %r12
	andq	%r10, %r9
	andq	%rbx, %rdi
	notq	%r12
	xorq	%rdi, %rax
	movq	%r12, %rdi
	movq	48(%rsp), %r12
	andq	%r15, %rdi
	xorq	%rdi, %rax
	movq	%rsi, %rdi
	movq	32(%rsp), %rsi
	xorq	%rax, %rdi
	movq	-104(%rsp), %rax
	xorq	%rsi, %rax
	xorq	-88(%rsp), %rax
	xorq	%rax, %rcx
	movq	%rdx, %rax
	notq	%rax
	andq	%r12, %rax
	xorq	%rcx, %rax
	movq	%r12, %rcx
	xorq	%rax, %r9
	movq	%rbx, %rax
	notq	%rax
	andq	%r8, %rax
	notq	%r8
	xorq	%rax, %r9
	movq	%r15, %rax
	xorq	-112(%rsp), %rdx
	andq	%rbp, %r8
	notq	%rax
	xorq	%rbx, %rdx
	xorq	-48(%rsp), %rcx
	movq	24(%rsp), %rbx
	andq	%r13, %rax
	xorq	%r15, %rdx
	movq	56(%rsp), %r15
	xorq	%rax, %r9
	movq	%r12, %rax
	movq	64(%rsp), %r12
	xorq	-56(%rsp), %r9
	notq	%rax
	andq	%r15, %rax
	xorq	%rax, %rdx
	movq	-48(%rsp), %rax
	notq	%rax
	andq	%r12, %rax
	xorq	%rdx, %rax
	movq	%r13, %rdx
	xorq	%rax, %r8
	movq	-80(%rsp), %rax
	notq	%rdx
	andq	%rdx, %rax
	movq	%r15, %rdx
	xorq	%r12, %r15
	xorq	%rax, %r8
	movq	%rcx, %rax
	notq	%rdx
	xorq	-40(%rsp), %r8
	xorq	%r10, %rax
	andq	%rbx, %rdx
	xorq	%r13, %rax
	movq	40(%rsp), %r13
	xorq	%rdx, %rax
	movq	%r12, %rdx
	notq	%rdx
	andq	%r13, %rdx
	xorq	%rdx, %rax
	movq	-64(%rsp), %rdx
	movq	-80(%rsp), %r12
	movq	-56(%rsp), %r10
	notq	%rdx
	notq	%r12
	andq	%r11, %rdx
	andq	%r14, %r12
	movq	-24(%rsp), %r14
	notq	%r11
	xorq	%rax, %rdx
	movq	-64(%rsp), %rax
	xorq	%r12, %rdx
	xorq	%r15, %rax
	xorq	%r14, %rdx
	movq	-16(%rsp), %r15
	movq	%rax, %rcx
	movq	%rbx, %rax
	movq	-32(%rsp), %rbx
	notq	%rax
	xorq	%rbp, %rcx
	andq	%rsi, %rax
	movq	-40(%rsp), %rsi
	xorq	%rcx, %rax
	movq	%r13, %rcx
	andq	-104(%rsp), %r11
	xorq	%rdi, %r10
	notq	%rcx
	andq	-120(%rsp), %rcx
	xorq	%r9, %rsi
	rorx	$63, %r9, %r9
	xorq	%rax, %rcx
	movq	-96(%rsp), %rax
	subq	$1, -72(%rsp)
	xorq	%rcx, %r11
	movq	%r14, %rcx
	notq	%rax
	andq	-88(%rsp), %rax
	xorq	%r8, %rcx
	rorx	$63, %r8, %r8
	xorq	%rax, %r11
	movq	%r15, %rax
	xorq	%r10, %r8
	rorx	$63, %rdi, %r10
	xorq	%rdx, %rax
	xorq	%r15, %r11
	rorx	$63, %rdx, %rdx
	xorq	%rsi, %rdx
	rorx	$21, %rdx, %rdx
	xorq	%r11, %rbx
	rorx	$63, %r11, %r11
	xorq	%rcx, %r11
	movq	%rdx, %rcx
	rorx	$43, %r11, %r11
	xorq	%rax, %r10
	movq	%r11, %rsi
	notq	%rcx
	rorx	$20, %r8, %r8
	movq	%r8, %rax
	xorq	%rbx, %r9
	andq	%r11, %rcx
	rorx	$50, %r10, %r10
	notq	%rax
	notq	%rsi
	xorq	%r8, %rcx
	andq	%rdx, %rax
	andq	%r10, %rsi
	movq	%rcx, %rbx
	movq	%r10, %rcx
	xorq	%r9, %rax
	xorq	%rdx, %rsi
	movabsq	$-9223372034707259384, %rdx
	notq	%rcx
	andq	%r9, %rcx
	xorq	%rax, %rdx
	xorq	%r11, %rcx
	cmpq	$-1, -72(%rsp)
	jne	.L23
	vmovq	%xmm9, %rdi
	movq	%rdx, (%rdi)
	movq	%rbx, 8(%rdi)
	movq	%rsi, 16(%rdi)
	movq	%rcx, 24(%rdi)
	addq	$80, %rsp
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
.L30:
	.cfi_restore 3
	.cfi_restore 6
	.cfi_restore 12
	.cfi_restore 13
	.cfi_restore 14
	.cfi_restore 15
	ret
	.cfi_endproc
.LFE7362:
	.size	chain_words_gp, .-chain_words_gp
	.p2align 4
	.type	chain_end, @function
chain_end:
.LFB7365:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %r8
	subq	$8, %rdi
	xorl	%esi, %esi
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$56, %rsp
	.cfi_def_cfa_offset 80
	movq	%fs:40, %rbx
	movq	%rbx, 40(%rsp)
	movq	%rdx, %rbx
	movq	%rsp, %rbp
.L34:
	addq	$8, %rdi
	xorl	%eax, %eax
	movq	%rdi, %rdx
	jmp	.L35
	.p2align 5
	.p2align 4,,10
	.p2align 3
.L41:
	subq	$1, %rdx
.L35:
	movzbl	7(%rdx), %ecx
	salq	$8, %rax
	orq	%rcx, %rax
	leaq	7(%rdx), %rcx
	cmpq	%rdi, %rcx
	jne	.L41
	movq	%rax, 0(%rbp,%rsi)
	addq	$8, %rsi
	cmpq	$32, %rsi
	jne	.L34
	movq	%rbp, %rdi
	movq	%r8, %rsi
	call	*kernel(%rip)
	xorl	%edi, %edi
.L37:
	movq	0(%rbp,%rdi), %rsi
	leaq	(%rbx,%rdi), %rdx
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L38:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L38
	addq	$8, %rdi
	cmpq	$32, %rdi
	jne	.L37
	movq	40(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L45
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
.L45:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7365:
	.size	chain_end, .-chain_end
	.p2align 4
	.type	walk, @function
walk:
.LFB7381:
	.cfi_startproc
	endbr64
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	(%rdi), %rsi
	leaq	40(%rdi), %rdx
	addq	$8, %rdi
	call	chain_end
	xorl	%eax, %eax
	addq	$8, %rsp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE7381:
	.size	walk, .-walk
	.p2align 4
	.type	chain_words_vec, @function
chain_words_vec:
.LFB7363:
	.cfi_startproc
	endbr64
	testq	%rsi, %rsi
	je	.L57
	subq	$48, %rsp
	.cfi_def_cfa_offset 56
	leaq	-1(%rsi), %r9
	movq	(%rdi), %rcx
	movq	8(%rdi), %rax
	movq	16(%rdi), %rdx
	movq	24(%rdi), %rsi
	.p2align 4
	.p2align 3
.L50:
	movq	%rcx, %r8
	salq	$8, %r8
	xorq	$67, %r8
	vmovq	%r8, %xmm10
	movq	%rdx, %r8
	vprolq	$1, %xmm10, %xmm7
	shldq	$8, %rax, %r8
	shldq	$8, %rcx, %rax
	movabsq	$-9223372034707259263, %rcx
	vmovq	%r8, %xmm4
	movq	%rsi, %r8
	shrq	$56, %rsi
	vmovq	%rax, %xmm2
	vprolq	$1, %xmm4, %xmm6
	shldq	$8, %rdx, %r8
	xorq	$256, %rsi
	vpxorq	.LC5(%rip), %xmm2, %xmm5
	vmovq	%r8, %xmm1
	vmovq	%rsi, %xmm3
	movl	$1, %eax
	vprolq	$1, %xmm1, %xmm9
	vpbroadcastq	%rax, %xmm23
	movl	$32898, %eax
	vprolq	$1, %xmm5, %xmm0
	vpxorq	%xmm1, %xmm7, %xmm7
	vprolq	$14, %xmm7, %xmm11
	vprolq	$20, %xmm7, %xmm20
	vpxorq	%xmm10, %xmm6, %xmm6
	vprolq	$44, %xmm6, %xmm18
	vpxorq	%xmm2, %xmm6, %xmm2
	vprolq	$1, %xmm2, %xmm2
	vpxorq	%xmm5, %xmm9, %xmm9
	vprolq	$1, %xmm3, %xmm5
	vpxorq	%xmm3, %xmm0, %xmm8
	vpternlogq	$150, %xmm10, %xmm3, %xmm0
	vpxorq	%xmm3, %xmm7, %xmm3
	vprolq	$43, %xmm9, %xmm14
	vprolq	$0, %xmm0, %xmm0
	vmovdqa64	%xmm11, %xmm27
	vprolq	$3, %xmm8, %xmm17
	vprolq	$6, %xmm9, %xmm16
	vprolq	$36, %xmm8, %xmm19
	vprolq	$10, %xmm6, %xmm15
	vpxorq	%xmm4, %xmm5, %xmm5
	vpxorq	%xmm9, %xmm4, %xmm4
	vprolq	$21, %xmm5, %xmm10
	vpxorq	%xmm5, %xmm1, %xmm1
	vprolq	$28, %xmm1, %xmm1
	vpternlogq	$210, %xmm18, %xmm0, %xmm27
	vprolq	$25, %xmm5, %xmm21
	vprolq	$27, %xmm3, %xmm3
	vprolq	$62, %xmm4, %xmm4
	vmovdqa64	%xmm10, %xmm31
	vpternlogq	$210, %xmm0, %xmm11, %xmm31
	vpternlogq	$210, %xmm14, %xmm18, %xmm0
	vpternlogq	$210, %xmm10, %xmm14, %xmm18
	vpternlogq	$210, %xmm11, %xmm10, %xmm14
	vpxorq	.LC5(%rip), %xmm6, %xmm10
	vprolq	$61, %xmm9, %xmm11
	vprolq	$45, %xmm10, %xmm10
	vprolq	$2, %xmm6, %xmm6
	vmovdqa64	%xmm11, %xmm30
	vmovdqa64	%xmm10, %xmm26
	vpternlogq	$210, %xmm20, %xmm1, %xmm30
	vpternlogq	$210, %xmm1, %xmm11, %xmm26
	vpternlogq	$210, %xmm17, %xmm20, %xmm1
	vpternlogq	$210, %xmm10, %xmm17, %xmm20
	vpternlogq	$210, %xmm11, %xmm10, %xmm17
	vmovdqa64	%xmm6, %xmm24
	vprolq	$8, %xmm7, %xmm10
	vprolq	$18, %xmm8, %xmm11
	vprolq	$41, %xmm8, %xmm8
	vprolq	$39, %xmm7, %xmm7
	vmovdqa64	%xmm10, %xmm29
	vmovdqa64	%xmm11, %xmm25
	vpternlogq	$210, %xmm2, %xmm11, %xmm29
	vpternlogq	$210, %xmm16, %xmm2, %xmm25
	vpternlogq	$210, %xmm21, %xmm16, %xmm2
	vpternlogq	$210, %xmm10, %xmm21, %xmm16
	vpternlogq	$210, %xmm11, %xmm10, %xmm21
	vprolq	$15, %xmm9, %xmm10
	vprolq	$56, %xmm5, %xmm11
	vprolq	$55, %xmm5, %xmm5
	vmovdqa64	%xmm10, %xmm22
	vmovdqa64	%xmm11, %xmm28
	vpternlogq	$210, %xmm3, %xmm11, %xmm22
	vpternlogq	$210, %xmm19, %xmm3, %xmm28
	vpternlogq	$210, %xmm15, %xmm19, %xmm3
	vpternlogq	$210, %xmm10, %xmm15, %xmm19
	vpternlogq	$210, %xmm11, %xmm10, %xmm15
	vmovdqa	%xmm8, %xmm11
	vpternlogq	$210, %xmm5, %xmm4, %xmm24
	vpternlogq	$210, %xmm4, %xmm6, %xmm11
	vpternlogq	$210, %xmm7, %xmm5, %xmm4
	vpternlogq	$210, %xmm8, %xmm7, %xmm5
	vmovdqa	%xmm3, %xmm13
	vmovdqa	%xmm5, %xmm9
	vmovdqa	%xmm0, %xmm3
	vmovdqa	%xmm11, -104(%rsp)
	vpxorq	%xmm1, %xmm2, %xmm5
	vmovdqa	%xmm4, %xmm10
	vmovdqa	%xmm13, -120(%rsp)
	vpternlogq	$210, %xmm6, %xmm8, %xmm7
	vpternlogq	$150, %xmm5, %xmm23, %xmm3
	vmovdqa64	%xmm19, %xmm5
	vmovdqa	%xmm15, %xmm12
	vmovdqa	%xmm9, -88(%rsp)
	vpternlogq	$150, %xmm3, %xmm13, %xmm10
	vmovdqa64	%xmm18, %xmm3
	vmovdqa64	%xmm28, %xmm6
	vpternlogq	$150, %xmm9, %xmm20, %xmm3
	vpternlogq	$150, %xmm3, %xmm16, %xmm5
	vmovdqa	%xmm14, %xmm3
	vmovdqa	%xmm5, %xmm13
	vpternlogq	$150, %xmm7, %xmm17, %xmm3
	vmovdqa64	%xmm22, %xmm5
	vprolq	$1, %xmm13, %xmm8
	vpternlogq	$150, %xmm3, %xmm21, %xmm12
	vmovdqa64	%xmm31, %xmm3
	vprolq	$1, %xmm12, %xmm9
	vpternlogq	$150, %xmm11, %xmm26, %xmm3
	vpternlogq	$150, %xmm3, %xmm29, %xmm5
	vmovdqa64	%xmm27, %xmm3
	vpternlogq	$150, %xmm24, %xmm30, %xmm3
	vmovdqa	%xmm5, %xmm11
	vpternlogq	$150, %xmm3, %xmm25, %xmm6
	vprolq	$1, %xmm5, %xmm3
	vprolq	$1, %xmm10, %xmm5
	vpxorq	%xmm6, %xmm8, %xmm8
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm8, %xmm23, %xmm0
	vmovdqa64	%xmm9, %xmm23
	vpxorq	%xmm2, %xmm8, %xmm2
	vprolq	$0, %xmm0, %xmm0
	vpternlogq	$150, %xmm20, %xmm10, %xmm23
	vpxorq	%xmm4, %xmm8, %xmm4
	vpxorq	%xmm1, %xmm8, %xmm1
	vprolq	$44, %xmm23, %xmm23
	vpxorq	-120(%rsp), %xmm8, %xmm8
	vprolq	$3, %xmm2, %xmm2
	vprolq	$18, %xmm4, %xmm4
	vmovdqa64	%xmm3, %xmm20
	vprolq	$41, %xmm8, %xmm8
	vpternlogq	$150, %xmm21, %xmm13, %xmm20
	vprolq	$43, %xmm20, %xmm20
	vmovdqa64	%xmm6, %xmm21
	vprolq	$36, %xmm1, %xmm1
	vpternlogq	$150, %xmm22, %xmm12, %xmm21
	vmovdqa64	%xmm5, %xmm22
	vprolq	$21, %xmm21, %xmm21
	vpternlogq	$150, %xmm24, %xmm11, %xmm22
	vprolq	$14, %xmm22, %xmm22
	vmovdqa64	%xmm21, %xmm24
	vpternlogq	$210, %xmm0, %xmm22, %xmm24
	vmovdqa64	%xmm24, -8(%rsp)
	vmovdqa64	%xmm22, %xmm24
	vpternlogq	$210, %xmm23, %xmm0, %xmm24
	vpternlogq	$210, %xmm20, %xmm23, %xmm0
	vpternlogq	$210, %xmm21, %xmm20, %xmm23
	vpternlogq	$210, %xmm22, %xmm21, %xmm20
	vmovdqa64	%xmm9, %xmm22
	vmovdqa64	%xmm24, -72(%rsp)
	vmovdqa64	%xmm6, %xmm21
	vpternlogq	$150, %xmm19, %xmm10, %xmm22
	vmovdqa64	%xmm20, %xmm24
	vmovdqa64	%xmm5, %xmm20
	vprolq	$45, %xmm22, %xmm19
	vmovdqa64	%xmm3, %xmm22
	vpternlogq	$150, %xmm31, %xmm12, %xmm21
	vpternlogq	$150, %xmm30, %xmm11, %xmm20
	vprolq	$28, %xmm21, %xmm21
	vpternlogq	$150, %xmm7, %xmm13, %xmm22
	vmovdqa64	%xmm9, %xmm30
	vmovdqa64	%xmm24, -120(%rsp)
	vprolq	$61, %xmm22, %xmm22
	vpternlogq	$150, %xmm18, %xmm10, %xmm30
	vmovdqa64	%xmm3, %xmm18
	vprolq	$20, %xmm20, %xmm20
	vpternlogq	$150, %xmm17, %xmm13, %xmm18
	vprolq	$1, %xmm30, %xmm30
	vprolq	$6, %xmm18, %xmm18
	vmovdqa64	%xmm19, %xmm31
	vmovdqa64	%xmm22, %xmm7
	vpternlogq	$210, %xmm21, %xmm22, %xmm31
	vpternlogq	$210, %xmm20, %xmm21, %xmm7
	vpternlogq	$210, %xmm2, %xmm20, %xmm21
	vpternlogq	$210, %xmm19, %xmm2, %xmm20
	vpternlogq	$210, %xmm22, %xmm19, %xmm2
	vmovdqa64	%xmm5, %xmm22
	vmovdqa64	%xmm6, %xmm19
	vmovdqa64	%xmm21, -56(%rsp)
	vpternlogq	$150, %xmm28, %xmm11, %xmm22
	vpternlogq	$150, %xmm29, %xmm12, %xmm19
	vmovdqa64	%xmm4, %xmm29
	vprolq	$8, %xmm22, %xmm22
	vpternlogq	$210, %xmm18, %xmm30, %xmm29
	vmovdqa64	%xmm3, %xmm28
	vpternlogq	$150, %xmm14, %xmm13, %xmm3
	vprolq	$25, %xmm19, %xmm21
	vpternlogq	$150, %xmm15, %xmm13, %xmm28
	vmovdqa64	%xmm29, -40(%rsp)
	vmovdqa	-40(%rsp), %xmm14
	vprolq	$15, %xmm28, %xmm28
	vprolq	$62, %xmm3, %xmm3
	vmovdqa64	%xmm22, %xmm19
	vpternlogq	$210, %xmm30, %xmm4, %xmm19
	vpternlogq	$210, %xmm21, %xmm18, %xmm30
	vpternlogq	$210, %xmm22, %xmm21, %xmm18
	vpternlogq	$210, %xmm4, %xmm22, %xmm21
	vmovdqa	%xmm5, %xmm4
	vmovdqa64	%xmm30, %xmm17
	vpternlogq	$150, %xmm27, %xmm11, %xmm4
	vmovdqa64	%xmm6, %xmm30
	vpternlogq	$150, %xmm25, %xmm11, %xmm5
	vprolq	$27, %xmm4, %xmm27
	vmovdqa	%xmm9, %xmm4
	vpternlogq	$150, -88(%rsp), %xmm10, %xmm9
	vpternlogq	$150, -104(%rsp), %xmm12, %xmm30
	vprolq	$2, %xmm9, %xmm9
	vpternlogq	$150, %xmm16, %xmm10, %xmm4
	vpternlogq	$150, %xmm26, %xmm12, %xmm6
	vmovdqa	%xmm8, %xmm11
	vprolq	$56, %xmm30, %xmm29
	vmovdqa64	%xmm28, %xmm16
	vmovdqa64	%xmm31, -104(%rsp)
	vprolq	$10, %xmm4, %xmm4
	vprolq	$55, %xmm6, %xmm6
	vprolq	$39, %xmm5, %xmm5
	vmovdqa64	%xmm9, %xmm30
	vpternlogq	$210, %xmm3, %xmm9, %xmm11
	vmovdqa64	%xmm29, %xmm22
	vpternlogq	$210, %xmm27, %xmm29, %xmm16
	vmovdqa	%xmm4, %xmm15
	vpternlogq	$210, %xmm1, %xmm27, %xmm22
	vpternlogq	$210, %xmm4, %xmm1, %xmm27
	vpternlogq	$210, %xmm6, %xmm3, %xmm30
	vpternlogq	$210, %xmm29, %xmm28, %xmm15
	vpternlogq	$210, %xmm28, %xmm4, %xmm1
	vmovdqa64	%xmm27, -88(%rsp)
	vpternlogq	$210, %xmm5, %xmm6, %xmm3
	vpternlogq	$210, %xmm8, %xmm5, %xmm6
	vpternlogq	$210, %xmm9, %xmm8, %xmm5
	vpxorq	-56(%rsp), %xmm17, %xmm8
	vmovdqa64	%xmm11, %xmm29
	vmovdqa	%xmm0, %xmm4
	vmovdqa	%xmm6, %xmm11
	vpbroadcastq	%rax, %xmm6
	vmovdqa64	%xmm3, %xmm25
	movabsq	$-9223372036854742902, %rax
	vpternlogq	$150, %xmm8, %xmm6, %xmm4
	vmovdqa64	%xmm1, %xmm28
	vmovdqa	%xmm15, %xmm13
	vmovdqa	%xmm11, -24(%rsp)
	vpternlogq	$150, %xmm4, %xmm27, %xmm25
	vmovdqa64	%xmm23, %xmm4
	vmovdqa64	%xmm22, %xmm9
	vprolq	$1, %xmm25, %xmm8
	vpternlogq	$150, %xmm11, %xmm20, %xmm4
	vmovdqa64	%xmm16, %xmm26
	vpternlogq	$150, %xmm4, %xmm18, %xmm28
	vmovdqa64	%xmm24, %xmm4
	vmovdqa64	-8(%rsp), %xmm24
	vprolq	$1, %xmm28, %xmm10
	vpternlogq	$150, %xmm5, %xmm2, %xmm4
	vpternlogq	$150, %xmm4, %xmm21, %xmm13
	vmovdqa	-72(%rsp), %xmm4
	vmovdqa64	%xmm13, %xmm27
	vmovdqa64	%xmm24, %xmm13
	vprolq	$1, %xmm27, %xmm12
	vpternlogq	$150, %xmm30, %xmm7, %xmm4
	vpternlogq	$150, %xmm29, %xmm31, %xmm13
	vpternlogq	$150, %xmm4, %xmm14, %xmm9
	vpternlogq	$150, %xmm13, %xmm19, %xmm26
	vprolq	$1, %xmm26, %xmm4
	vpxorq	%xmm9, %xmm10, %xmm10
	vprolq	$1, %xmm9, %xmm9
	vpternlogq	$150, %xmm10, %xmm6, %xmm0
	vpxorq	%xmm3, %xmm10, %xmm3
	vprolq	$0, %xmm0, %xmm0
	vprolq	$18, %xmm3, %xmm3
	vmovdqa	%xmm12, %xmm6
	vpternlogq	$150, %xmm20, %xmm25, %xmm6
	vprolq	$44, %xmm6, %xmm14
	vmovdqa	%xmm4, %xmm6
	vpternlogq	$150, %xmm21, %xmm28, %xmm6
	vprolq	$43, %xmm6, %xmm6
	vmovdqa	%xmm9, %xmm13
	vpternlogq	$150, %xmm16, %xmm27, %xmm13
	vmovdqa64	%xmm4, %xmm16
	vprolq	$21, %xmm13, %xmm11
	vmovdqa	%xmm8, %xmm13
	vpternlogq	$150, %xmm2, %xmm28, %xmm16
	vprolq	$6, %xmm16, %xmm16
	vpternlogq	$150, %xmm30, %xmm26, %xmm13
	vprolq	$14, %xmm13, %xmm13
	vmovdqa64	%xmm11, %xmm20
	vmovdqa64	%xmm13, %xmm30
	vpternlogq	$210, %xmm0, %xmm13, %xmm20
	vpternlogq	$210, %xmm14, %xmm0, %xmm30
	vpternlogq	$210, %xmm6, %xmm14, %xmm0
	vpternlogq	$210, %xmm11, %xmm6, %xmm14
	vpternlogq	$210, %xmm13, %xmm11, %xmm6
	vmovdqa	%xmm8, %xmm13
	vpxorq	%xmm17, %xmm10, %xmm11
	vprolq	$3, %xmm11, %xmm11
	vpternlogq	$150, %xmm7, %xmm26, %xmm13
	vmovdqa	%xmm6, -8(%rsp)
	vmovdqa	%xmm9, %xmm6
	vpternlogq	$150, %xmm24, %xmm27, %xmm6
	vmovdqa64	%xmm30, %xmm31
	vmovdqa64	%xmm9, %xmm17
	vprolq	$20, %xmm13, %xmm24
	vmovdqa	%xmm12, %xmm13
	vmovdqa64	%xmm12, %xmm30
	vpternlogq	$150, %xmm19, %xmm27, %xmm17
	vprolq	$28, %xmm6, %xmm6
	vpternlogq	$150, %xmm1, %xmm25, %xmm13
	vpternlogq	$150, %xmm23, %xmm25, %xmm30
	vpxorq	-56(%rsp), %xmm10, %xmm7
	vprolq	$45, %xmm13, %xmm1
	vmovdqa	%xmm4, %xmm13
	vpxorq	-88(%rsp), %xmm10, %xmm10
	vprolq	$25, %xmm17, %xmm17
	vpternlogq	$150, %xmm5, %xmm28, %xmm13
	vprolq	$61, %xmm13, %xmm5
	vprolq	$41, %xmm10, %xmm10
	vprolq	$36, %xmm7, %xmm7
	vmovdqa	%xmm1, %xmm13
	vmovdqa64	%xmm5, %xmm21
	vpternlogq	$210, %xmm6, %xmm5, %xmm13
	vpternlogq	$210, %xmm24, %xmm6, %xmm21
	vpternlogq	$210, %xmm11, %xmm24, %xmm6
	vpternlogq	$210, %xmm1, %xmm11, %xmm24
	vmovdqa	%xmm13, 8(%rsp)
	vpternlogq	$210, %xmm5, %xmm1, %xmm11
	vmovdqa	%xmm8, %xmm1
	vmovdqa	%xmm6, 24(%rsp)
	vprolq	$1, %xmm30, %xmm6
	vpternlogq	$150, %xmm22, %xmm26, %xmm1
	vmovdqa64	%xmm3, %xmm30
	vprolq	$8, %xmm1, %xmm1
	vpternlogq	$210, %xmm16, %xmm6, %xmm30
	vmovdqa64	%xmm1, %xmm19
	vpternlogq	$210, %xmm6, %xmm3, %xmm19
	vpternlogq	$210, %xmm17, %xmm16, %xmm6
	vpternlogq	$210, %xmm1, %xmm17, %xmm16
	vpternlogq	$210, %xmm3, %xmm1, %xmm17
	vmovdqa	%xmm8, %xmm3
	vmovdqa	%xmm4, %xmm1
	vpternlogq	$150, -72(%rsp), %xmm26, %xmm3
	vpternlogq	$150, %xmm15, %xmm28, %xmm1
	vpternlogq	$150, -120(%rsp), %xmm28, %xmm4
	vprolq	$27, %xmm3, %xmm2
	vmovdqa	%xmm12, %xmm3
	vpternlogq	$150, -24(%rsp), %xmm25, %xmm12
	vpternlogq	$150, -40(%rsp), %xmm26, %xmm8
	vprolq	$15, %xmm1, %xmm1
	vpternlogq	$150, %xmm18, %xmm25, %xmm3
	vprolq	$10, %xmm3, %xmm13
	vmovdqa	%xmm9, %xmm3
	vpternlogq	$150, -104(%rsp), %xmm27, %xmm9
	vprolq	$55, %xmm9, %xmm9
	vpternlogq	$150, %xmm29, %xmm27, %xmm3
	vmovdqa64	%xmm10, %xmm27
	vprolq	$56, %xmm3, %xmm3
	vprolq	$2, %xmm12, %xmm12
	vprolq	$62, %xmm4, %xmm4
	vmovdqa64	%xmm2, %xmm29
	vprolq	$39, %xmm8, %xmm8
	vmovdqa	%xmm1, %xmm15
	vpternlogq	$210, %xmm13, %xmm7, %xmm29
	vmovdqa64	%xmm3, %xmm22
	vpternlogq	$210, %xmm2, %xmm3, %xmm15
	vpternlogq	$210, %xmm7, %xmm2, %xmm22
	vmovdqa64	%xmm12, %xmm28
	vpternlogq	$210, %xmm1, %xmm13, %xmm7
	vpxorq	24(%rsp), %xmm6, %xmm2
	vpternlogq	$210, %xmm3, %xmm1, %xmm13
	vmovdqa	%xmm9, %xmm3
	vpternlogq	$210, %xmm4, %xmm12, %xmm27
	vpternlogq	$210, %xmm9, %xmm4, %xmm28
	vpternlogq	$210, %xmm10, %xmm8, %xmm3
	vpternlogq	$210, %xmm8, %xmm9, %xmm4
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm12, %xmm10, %xmm8
	vmovdqa	%xmm3, -120(%rsp)
	vpbroadcastq	%rax, %xmm10
	vmovdqa64	%xmm4, %xmm18
	vmovdqa64	%xmm7, %xmm26
	vpternlogq	$150, %xmm2, %xmm10, %xmm1
	vmovdqa64	%xmm13, %xmm25
	vmovdqa64	%xmm15, %xmm23
	vpternlogq	$150, %xmm1, %xmm29, %xmm18
	vmovdqa	%xmm14, %xmm1
	vmovdqa64	%xmm22, %xmm10
	vpternlogq	$150, %xmm3, %xmm24, %xmm1
	vpbroadcastq	%rax, %xmm9
	addq	$2147483510, %rax
	vpternlogq	$150, %xmm1, %xmm16, %xmm26
	vmovdqa	-8(%rsp), %xmm1
	vmovdqa	8(%rsp), %xmm2
	vprolq	$1, %xmm26, %xmm5
	vpternlogq	$150, %xmm8, %xmm11, %xmm1
	vpternlogq	$150, %xmm1, %xmm17, %xmm25
	vmovdqa64	%xmm20, %xmm1
	vpternlogq	$150, %xmm27, %xmm2, %xmm1
	vprolq	$1, %xmm18, %xmm2
	vpternlogq	$150, %xmm1, %xmm19, %xmm23
	vmovdqa64	%xmm31, %xmm1
	vpternlogq	$150, %xmm28, %xmm21, %xmm1
	vpternlogq	$150, %xmm1, %xmm30, %xmm10
	vprolq	$1, %xmm10, %xmm3
	vpxorq	%xmm10, %xmm5, %xmm5
	vprolq	$1, %xmm23, %xmm1
	vpternlogq	$150, %xmm5, %xmm9, %xmm0
	vpxorq	%xmm6, %xmm5, %xmm6
	vpxorq	%xmm4, %xmm5, %xmm4
	vprolq	$1, %xmm25, %xmm10
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm6, %xmm6
	vprolq	$18, %xmm4, %xmm4
	vmovdqa	%xmm1, %xmm9
	vmovdqa	%xmm10, %xmm12
	vpternlogq	$150, %xmm17, %xmm26, %xmm9
	vmovdqa64	%xmm3, %xmm17
	vprolq	$43, %xmm9, %xmm9
	vpternlogq	$150, %xmm24, %xmm18, %xmm12
	vmovdqa64	%xmm2, %xmm24
	vpternlogq	$150, %xmm15, %xmm25, %xmm17
	vprolq	$21, %xmm17, %xmm15
	vpternlogq	$150, %xmm28, %xmm23, %xmm24
	vprolq	$14, %xmm24, %xmm24
	vprolq	$44, %xmm12, %xmm12
	vmovdqa64	%xmm15, %xmm17
	vmovdqa64	%xmm24, %xmm28
	vpternlogq	$210, %xmm0, %xmm24, %xmm17
	vpternlogq	$210, %xmm12, %xmm0, %xmm28
	vpternlogq	$210, %xmm9, %xmm12, %xmm0
	vpternlogq	$210, %xmm15, %xmm9, %xmm12
	vpternlogq	$210, %xmm24, %xmm15, %xmm9
	vmovdqa	%xmm2, %xmm15
	vmovdqa64	%xmm28, -104(%rsp)
	vpternlogq	$150, %xmm21, %xmm23, %xmm15
	vmovdqa64	%xmm9, %xmm24
	vmovdqa	%xmm3, %xmm9
	vprolq	$20, %xmm15, %xmm21
	vmovdqa	%xmm10, %xmm15
	vpternlogq	$150, %xmm20, %xmm25, %xmm9
	vprolq	$28, %xmm9, %xmm9
	vpternlogq	$150, %xmm7, %xmm18, %xmm15
	vprolq	$45, %xmm15, %xmm7
	vmovdqa	%xmm1, %xmm15
	vpternlogq	$150, %xmm8, %xmm26, %xmm15
	vprolq	$61, %xmm15, %xmm8
	vmovdqa	%xmm7, %xmm15
	vmovdqa64	%xmm8, %xmm20
	vpternlogq	$210, %xmm9, %xmm8, %xmm15
	vpternlogq	$210, %xmm21, %xmm9, %xmm20
	vpternlogq	$210, %xmm6, %xmm21, %xmm9
	vpternlogq	$210, %xmm7, %xmm6, %xmm21
	vmovdqa	%xmm15, -88(%rsp)
	vpternlogq	$210, %xmm8, %xmm7, %xmm6
	vmovdqa	%xmm1, %xmm8
	vmovdqa	%xmm10, %xmm7
	vmovdqa	%xmm9, -72(%rsp)
	vpternlogq	$150, %xmm11, %xmm26, %xmm8
	vmovdqa	%xmm3, %xmm11
	vpternlogq	$150, %xmm14, %xmm18, %xmm7
	vprolq	$6, %xmm8, %xmm15
	vmovdqa	%xmm2, %xmm8
	vpternlogq	$150, %xmm19, %xmm25, %xmm11
	vmovdqa	%xmm10, %xmm14
	vprolq	$1, %xmm7, %xmm7
	vpternlogq	$150, %xmm22, %xmm23, %xmm8
	vmovdqa64	%xmm4, %xmm22
	vpternlogq	$150, %xmm16, %xmm18, %xmm14
	vprolq	$8, %xmm8, %xmm8
	vmovdqa64	%xmm3, %xmm16
	vpxorq	24(%rsp), %xmm5, %xmm9
	vpternlogq	$150, -120(%rsp), %xmm18, %xmm10
	vprolq	$25, %xmm11, %xmm11
	vpternlogq	$150, %xmm27, %xmm25, %xmm16
	vpternlogq	$150, 8(%rsp), %xmm25, %xmm3
	vpxorq	%xmm29, %xmm5, %xmm5
	vprolq	$56, %xmm16, %xmm16
	vmovdqa64	%xmm24, -120(%rsp)
	vprolq	$55, %xmm3, %xmm3
	vprolq	$41, %xmm5, %xmm5
	vprolq	$2, %xmm10, %xmm10
	vpternlogq	$210, %xmm15, %xmm7, %xmm22
	vprolq	$36, %xmm9, %xmm9
	vmovdqa64	%xmm8, %xmm19
	vmovdqa64	%xmm22, %xmm28
	vprolq	$10, %xmm14, %xmm14
	vpternlogq	$210, %xmm7, %xmm4, %xmm19
	vpternlogq	$210, %xmm11, %xmm15, %xmm7
	vpternlogq	$210, %xmm8, %xmm11, %xmm15
	vpternlogq	$210, %xmm4, %xmm8, %xmm11
	vmovdqa	%xmm2, %xmm8
	vpternlogq	$150, %xmm30, %xmm23, %xmm2
	vprolq	$39, %xmm2, %xmm2
	vpternlogq	$150, %xmm31, %xmm23, %xmm8
	vmovdqa64	%xmm1, %xmm31
	vpternlogq	$150, -8(%rsp), %xmm26, %xmm1
	vprolq	$27, %xmm8, %xmm8
	vpternlogq	$150, %xmm13, %xmm26, %xmm31
	vmovdqa64	%xmm16, %xmm22
	vmovdqa64	%xmm5, %xmm26
	vprolq	$15, %xmm31, %xmm4
	vmovdqa64	%xmm10, %xmm18
	vprolq	$62, %xmm1, %xmm27
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm2, %xmm29
	vpternlogq	$210, %xmm9, %xmm8, %xmm22
	vpternlogq	$210, %xmm10, %xmm5, %xmm29
	vmovdqa	%xmm4, %xmm13
	vpternlogq	$210, %xmm8, %xmm16, %xmm13
	vpternlogq	$210, %xmm14, %xmm9, %xmm8
	vpternlogq	$210, %xmm4, %xmm14, %xmm9
	vpternlogq	$210, %xmm16, %xmm4, %xmm14
	vmovdqa	%xmm3, %xmm4
	vpternlogq	$210, %xmm27, %xmm10, %xmm26
	vpternlogq	$210, %xmm3, %xmm27, %xmm18
	vpternlogq	$210, %xmm5, %xmm2, %xmm4
	vpternlogq	$210, %xmm2, %xmm3, %xmm27
	vpxorq	-72(%rsp), %xmm7, %xmm2
	vpbroadcastq	%rax, %xmm3
	vmovdqa64	%xmm27, %xmm16
	vmovdqa	%xmm4, -56(%rsp)
	vmovdqa64	%xmm9, %xmm25
	vmovdqa64	%xmm13, %xmm23
	vmovdqa64	%xmm8, %xmm31
	vpternlogq	$150, %xmm2, %xmm3, %xmm1
	vmovdqa	%xmm14, %xmm3
	vmovdqa	-88(%rsp), %xmm2
	vpbroadcastq	%rax, %xmm10
	vpternlogq	$150, %xmm1, %xmm8, %xmm16
	vmovdqa	%xmm12, %xmm1
	movl	$32907, %eax
	vpternlogq	$150, %xmm4, %xmm21, %xmm1
	vpternlogq	$150, %xmm1, %xmm15, %xmm25
	vmovdqa64	%xmm24, %xmm1
	vprolq	$1, %xmm25, %xmm4
	vpternlogq	$150, %xmm29, %xmm6, %xmm1
	vpternlogq	$150, %xmm1, %xmm11, %xmm3
	vmovdqa	-104(%rsp), %xmm1
	vmovdqa64	%xmm3, %xmm24
	vmovdqa64	%xmm17, %xmm3
	vprolq	$1, %xmm24, %xmm8
	vpternlogq	$150, %xmm26, %xmm2, %xmm3
	vpternlogq	$150, %xmm18, %xmm20, %xmm1
	vprolq	$1, %xmm16, %xmm2
	vpternlogq	$150, %xmm3, %xmm19, %xmm23
	vmovdqa64	%xmm22, %xmm3
	vpternlogq	$150, %xmm1, %xmm28, %xmm3
	vprolq	$1, %xmm23, %xmm1
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm10, %xmm0
	vpxorq	%xmm7, %xmm4, %xmm7
	vpxorq	%xmm27, %xmm4, %xmm27
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm7, %xmm7
	vmovdqa	%xmm8, %xmm10
	vprolq	$18, %xmm27, %xmm27
	vpternlogq	$150, %xmm21, %xmm16, %xmm10
	vprolq	$44, %xmm10, %xmm10
	vmovdqa	%xmm1, %xmm5
	vpternlogq	$150, %xmm11, %xmm25, %xmm5
	vmovdqa	%xmm3, %xmm11
	vprolq	$43, %xmm5, %xmm5
	vpternlogq	$150, %xmm13, %xmm24, %xmm11
	vmovdqa	%xmm2, %xmm13
	vprolq	$21, %xmm11, %xmm11
	vpternlogq	$150, %xmm18, %xmm23, %xmm13
	vprolq	$14, %xmm13, %xmm13
	vmovdqa64	%xmm11, %xmm18
	vmovdqa64	%xmm13, %xmm30
	vpternlogq	$210, %xmm0, %xmm13, %xmm18
	vpternlogq	$210, %xmm10, %xmm0, %xmm30
	vpternlogq	$210, %xmm5, %xmm10, %xmm0
	vpternlogq	$210, %xmm11, %xmm5, %xmm10
	vpternlogq	$210, %xmm13, %xmm11, %xmm5
	vmovdqa	%xmm2, %xmm13
	vmovdqa	%xmm3, %xmm11
	vpternlogq	$150, %xmm20, %xmm23, %xmm13
	vmovdqa	%xmm5, -40(%rsp)
	vpternlogq	$150, %xmm17, %xmm24, %xmm11
	vprolq	$20, %xmm13, %xmm20
	vmovdqa	%xmm8, %xmm13
	vprolq	$28, %xmm11, %xmm11
	vpternlogq	$150, %xmm9, %xmm16, %xmm13
	vmovdqa	%xmm1, %xmm9
	vprolq	$45, %xmm13, %xmm5
	vpternlogq	$150, %xmm29, %xmm25, %xmm9
	vmovdqa64	%xmm1, %xmm29
	vprolq	$61, %xmm9, %xmm9
	vpternlogq	$150, %xmm14, %xmm25, %xmm29
	vmovdqa	%xmm5, %xmm13
	vmovdqa64	%xmm9, %xmm17
	vpternlogq	$210, %xmm11, %xmm9, %xmm13
	vpternlogq	$210, %xmm20, %xmm11, %xmm17
	vpternlogq	$210, %xmm7, %xmm20, %xmm11
	vpternlogq	$210, %xmm5, %xmm7, %xmm20
	vmovdqa	%xmm13, -24(%rsp)
	vpternlogq	$210, %xmm9, %xmm5, %xmm7
	vmovdqa	%xmm8, %xmm9
	vmovdqa	%xmm11, -8(%rsp)
	vmovdqa	%xmm8, %xmm11
	vpternlogq	$150, %xmm12, %xmm16, %xmm9
	vmovdqa	%xmm3, %xmm12
	vpternlogq	$150, -56(%rsp), %xmm16, %xmm8
	vprolq	$1, %xmm9, %xmm5
	vmovdqa	%xmm1, %xmm9
	vpternlogq	$150, %xmm19, %xmm24, %xmm12
	vpternlogq	$150, -120(%rsp), %xmm25, %xmm1
	vprolq	$25, %xmm12, %xmm12
	vpternlogq	$150, %xmm6, %xmm25, %xmm9
	vpternlogq	$150, %xmm15, %xmm16, %xmm11
	vprolq	$6, %xmm9, %xmm13
	vmovdqa	%xmm2, %xmm9
	vprolq	$15, %xmm29, %xmm15
	vpternlogq	$150, %xmm22, %xmm23, %xmm9
	vmovdqa64	%xmm3, %xmm22
	vpternlogq	$150, -88(%rsp), %xmm24, %xmm3
	vprolq	$8, %xmm9, %xmm6
	vmovdqa64	%xmm27, %xmm9
	vpternlogq	$150, %xmm26, %xmm24, %xmm22
	vprolq	$56, %xmm22, %xmm22
	vprolq	$2, %xmm8, %xmm8
	vprolq	$62, %xmm1, %xmm26
	vmovdqa	%xmm0, %xmm1
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm13, %xmm5, %xmm9
	vprolq	$10, %xmm11, %xmm11
	vmovdqa	%xmm9, 8(%rsp)
	vmovdqa	%xmm2, %xmm9
	vpternlogq	$150, %xmm28, %xmm23, %xmm2
	vprolq	$39, %xmm2, %xmm28
	vmovdqa64	%xmm6, %xmm19
	vpternlogq	$150, -104(%rsp), %xmm23, %xmm9
	vmovdqa	%xmm15, %xmm14
	vprolq	$27, %xmm9, %xmm9
	vpternlogq	$210, %xmm5, %xmm27, %xmm19
	vpternlogq	$210, %xmm12, %xmm13, %xmm5
	vpternlogq	$210, %xmm6, %xmm12, %xmm13
	vpternlogq	$210, %xmm27, %xmm6, %xmm12
	vpxorq	-72(%rsp), %xmm4, %xmm6
	vpxorq	%xmm31, %xmm4, %xmm4
	vprolq	$41, %xmm4, %xmm4
	vpxorq	-8(%rsp), %xmm5, %xmm2
	vmovdqa64	%xmm22, %xmm21
	vmovdqa64	%xmm8, %xmm16
	vprolq	$36, %xmm6, %xmm6
	vpternlogq	$210, %xmm3, %xmm26, %xmm16
	vpternlogq	$210, %xmm9, %xmm22, %xmm14
	vmovdqa64	%xmm9, %xmm29
	vmovdqa64	%xmm4, %xmm25
	vpternlogq	$210, %xmm6, %xmm9, %xmm21
	vpternlogq	$210, %xmm26, %xmm8, %xmm25
	vpbroadcastq	%rax, %xmm9
	addq	$2147450742, %rax
	vpternlogq	$210, %xmm28, %xmm3, %xmm26
	vpternlogq	$210, %xmm11, %xmm6, %xmm29
	vpternlogq	$150, %xmm2, %xmm9, %xmm1
	vmovdqa	-24(%rsp), %xmm2
	vpternlogq	$210, %xmm15, %xmm11, %xmm6
	vpternlogq	$210, %xmm22, %xmm15, %xmm11
	vmovdqa64	%xmm26, %xmm15
	vpternlogq	$150, %xmm1, %xmm29, %xmm15
	vpternlogq	$210, %xmm4, %xmm28, %xmm3
	vmovdqa	%xmm10, %xmm1
	vpternlogq	$150, %xmm3, %xmm20, %xmm1
	vmovdqa64	%xmm3, %xmm31
	vmovdqa64	%xmm6, %xmm24
	vmovdqa64	%xmm18, %xmm3
	vpternlogq	$150, %xmm1, %xmm13, %xmm24
	vmovdqa64	%xmm14, %xmm22
	vmovdqa	-40(%rsp), %xmm1
	vpternlogq	$150, %xmm25, %xmm2, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm28
	vmovdqa64	%xmm11, %xmm23
	vmovdqa	8(%rsp), %xmm8
	vprolq	$1, %xmm24, %xmm4
	vpternlogq	$150, %xmm3, %xmm19, %xmm22
	vmovdqa64	%xmm30, %xmm3
	vpternlogq	$150, %xmm28, %xmm7, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm16, %xmm17, %xmm3
	vpternlogq	$150, %xmm1, %xmm12, %xmm23
	vmovdqa	%xmm3, %xmm1
	vmovdqa64	%xmm21, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm3
	vprolq	$1, %xmm23, %xmm8
	vprolq	$1, %xmm22, %xmm1
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm9, %xmm0
	vpxorq	%xmm5, %xmm4, %xmm5
	vpxorq	%xmm26, %xmm4, %xmm26
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm5, %xmm5
	vprolq	$18, %xmm26, %xmm26
	vmovdqa	%xmm8, %xmm9
	vpternlogq	$150, %xmm20, %xmm15, %xmm9
	vmovdqa64	%xmm1, %xmm20
	vprolq	$44, %xmm9, %xmm9
	vpternlogq	$150, %xmm12, %xmm24, %xmm20
	vprolq	$43, %xmm20, %xmm12
	vmovdqa64	%xmm3, %xmm20
	vpternlogq	$150, %xmm14, %xmm23, %xmm20
	vprolq	$21, %xmm20, %xmm14
	vmovdqa64	%xmm2, %xmm20
	vpternlogq	$150, %xmm16, %xmm22, %xmm20
	vprolq	$14, %xmm20, %xmm20
	vmovdqa64	%xmm14, %xmm16
	vmovdqa64	%xmm20, %xmm27
	vpternlogq	$210, %xmm0, %xmm20, %xmm16
	vpternlogq	$210, %xmm9, %xmm0, %xmm27
	vpternlogq	$210, %xmm12, %xmm9, %xmm0
	vpternlogq	$210, %xmm14, %xmm12, %xmm9
	vpternlogq	$210, %xmm20, %xmm14, %xmm12
	vmovdqa	%xmm3, %xmm14
	vmovdqa64	%xmm8, %xmm20
	vpternlogq	$150, %xmm18, %xmm23, %xmm14
	vmovdqa	%xmm12, -120(%rsp)
	vmovdqa64	%xmm2, %xmm18
	vpternlogq	$150, %xmm13, %xmm15, %xmm20
	vprolq	$28, %xmm14, %xmm12
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$150, %xmm17, %xmm22, %xmm18
	vmovdqa	%xmm1, %xmm13
	vprolq	$20, %xmm18, %xmm18
	vpternlogq	$150, %xmm6, %xmm15, %xmm14
	vpternlogq	$150, %xmm11, %xmm24, %xmm13
	vprolq	$45, %xmm14, %xmm6
	vmovdqa	%xmm1, %xmm14
	vprolq	$15, %xmm13, %xmm11
	vpternlogq	$150, %xmm28, %xmm24, %xmm14
	vmovdqa	%xmm3, %xmm13
	vprolq	$61, %xmm14, %xmm14
	vpternlogq	$150, %xmm25, %xmm23, %xmm13
	vprolq	$56, %xmm13, %xmm25
	vmovdqa64	%xmm6, %xmm17
	vmovdqa	%xmm11, %xmm13
	vpternlogq	$210, %xmm12, %xmm14, %xmm17
	vmovdqa64	%xmm17, -104(%rsp)
	vmovdqa64	%xmm14, %xmm17
	vpternlogq	$210, %xmm18, %xmm12, %xmm17
	vpternlogq	$210, %xmm5, %xmm18, %xmm12
	vpternlogq	$210, %xmm6, %xmm5, %xmm18
	vpternlogq	$210, %xmm14, %xmm6, %xmm5
	vmovdqa	%xmm1, %xmm14
	vmovdqa	%xmm8, %xmm6
	vmovdqa	%xmm12, -72(%rsp)
	vpternlogq	$150, %xmm7, %xmm24, %xmm14
	vmovdqa	%xmm2, %xmm7
	vpternlogq	$150, %xmm10, %xmm15, %xmm6
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm21, %xmm22, %xmm7
	vmovdqa	%xmm3, %xmm10
	vmovdqa64	%xmm2, %xmm21
	vprolq	$8, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm23, %xmm10
	vpternlogq	$150, %xmm30, %xmm22, %xmm21
	vpternlogq	$150, %xmm31, %xmm15, %xmm8
	vprolq	$25, %xmm10, %xmm12
	vmovdqa64	%xmm26, %xmm10
	vprolq	$6, %xmm14, %xmm14
	vprolq	$27, %xmm21, %xmm21
	vprolq	$2, %xmm8, %xmm8
	vmovdqa64	%xmm7, %xmm19
	vpternlogq	$210, %xmm6, %xmm26, %xmm19
	vpternlogq	$210, %xmm14, %xmm6, %xmm10
	vpternlogq	$210, %xmm12, %xmm14, %xmm6
	vpternlogq	$210, %xmm7, %xmm12, %xmm14
	vpternlogq	$210, %xmm26, %xmm7, %xmm12
	vpxorq	-8(%rsp), %xmm4, %xmm7
	vmovdqa	%xmm10, -88(%rsp)
	vpxorq	%xmm29, %xmm4, %xmm4
	vprolq	$10, %xmm20, %xmm10
	vpternlogq	$150, -40(%rsp), %xmm24, %xmm1
	vmovdqa64	%xmm25, %xmm20
	vpternlogq	$150, -24(%rsp), %xmm23, %xmm3
	vprolq	$36, %xmm7, %xmm7
	vpternlogq	$150, 8(%rsp), %xmm22, %xmm2
	vpternlogq	$210, %xmm21, %xmm25, %xmm13
	vmovdqa64	-72(%rsp), %xmm30
	vprolq	$41, %xmm4, %xmm4
	vmovdqa64	%xmm8, %xmm28
	vprolq	$62, %xmm1, %xmm26
	vmovdqa	%xmm0, %xmm1
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm7, %xmm21, %xmm20
	vpternlogq	$210, %xmm10, %xmm7, %xmm21
	vpternlogq	$210, %xmm11, %xmm10, %xmm7
	vpternlogq	$210, %xmm25, %xmm11, %xmm10
	vmovdqa64	%xmm4, %xmm24
	vpbroadcastq	%rax, %xmm11
	vmovdqa64	%xmm21, -72(%rsp)
	vprolq	$39, %xmm2, %xmm25
	vpternlogq	$210, %xmm26, %xmm8, %xmm24
	vpxorq	%xmm30, %xmm6, %xmm2
	vmovdqa64	%xmm7, %xmm23
	vpternlogq	$210, %xmm3, %xmm26, %xmm28
	vpternlogq	$150, %xmm2, %xmm11, %xmm1
	vmovdqa	-104(%rsp), %xmm2
	vmovdqa64	%xmm10, %xmm22
	vmovdqa	%xmm11, -56(%rsp)
	movabsq	$-9223372036854743031, %rax
	vpternlogq	$210, %xmm25, %xmm3, %xmm26
	vpternlogq	$210, %xmm4, %xmm25, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm25
	vmovdqa	-88(%rsp), %xmm4
	vmovdqa64	%xmm26, %xmm15
	vmovdqa64	%xmm3, %xmm31
	vpternlogq	$150, %xmm1, %xmm21, %xmm15
	vmovdqa	%xmm9, %xmm1
	vpternlogq	$150, %xmm3, %xmm18, %xmm1
	vmovdqa64	%xmm16, %xmm3
	vpternlogq	$150, %xmm1, %xmm14, %xmm23
	vmovdqa	-120(%rsp), %xmm1
	vpternlogq	$150, %xmm24, %xmm2, %xmm3
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm25, %xmm5, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa	%xmm3, %xmm1
	vmovdqa	%xmm13, %xmm3
	vprolq	$1, %xmm22, %xmm8
	vpternlogq	$150, %xmm1, %xmm19, %xmm3
	vmovdqa64	%xmm3, %xmm21
	vmovdqa64	%xmm27, %xmm3
	vpternlogq	$150, %xmm28, %xmm17, %xmm3
	vmovdqa	%xmm3, %xmm1
	vmovdqa64	%xmm20, %xmm3
	vpternlogq	$150, %xmm1, %xmm4, %xmm3
	vprolq	$1, %xmm23, %xmm4
	vprolq	$1, %xmm21, %xmm1
	vmovdqa64	%xmm8, %xmm29
	vpternlogq	$150, %xmm18, %xmm15, %xmm29
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vmovdqa64	%xmm1, %xmm18
	vpternlogq	$150, %xmm4, %xmm11, %xmm0
	vpxorq	%xmm6, %xmm4, %xmm6
	vprolq	$44, %xmm29, %xmm11
	vpternlogq	$150, %xmm12, %xmm23, %xmm18
	vmovdqa64	%xmm2, %xmm29
	vpxorq	%xmm26, %xmm4, %xmm26
	vprolq	$43, %xmm18, %xmm12
	vpternlogq	$150, %xmm28, %xmm21, %xmm29
	vprolq	$14, %xmm29, %xmm29
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm6, %xmm6
	vprolq	$18, %xmm26, %xmm26
	vmovdqa64	%xmm3, %xmm18
	vpternlogq	$150, %xmm13, %xmm22, %xmm18
	vprolq	$21, %xmm18, %xmm13
	vmovdqa64	%xmm29, %xmm28
	vpternlogq	$210, %xmm11, %xmm0, %xmm28
	vmovdqa64	%xmm13, %xmm18
	vpternlogq	$210, %xmm0, %xmm29, %xmm18
	vpternlogq	$210, %xmm12, %xmm11, %xmm0
	vpternlogq	$210, %xmm13, %xmm12, %xmm11
	vpternlogq	$210, %xmm29, %xmm13, %xmm12
	vmovdqa	%xmm3, %xmm13
	vpternlogq	$150, %xmm16, %xmm22, %xmm13
	vmovdqa	%xmm12, -40(%rsp)
	vprolq	$28, %xmm13, %xmm12
	vmovdqa	%xmm2, %xmm13
	vpternlogq	$150, %xmm17, %xmm21, %xmm13
	vprolq	$20, %xmm13, %xmm17
	vmovdqa	%xmm8, %xmm13
	vpternlogq	$150, %xmm7, %xmm15, %xmm13
	vprolq	$45, %xmm13, %xmm7
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm25, %xmm23, %xmm13
	vprolq	$61, %xmm13, %xmm13
	vmovdqa64	%xmm12, %xmm25
	vpternlogq	$210, %xmm6, %xmm17, %xmm25
	vmovdqa64	%xmm7, %xmm16
	vmovdqa64	%xmm13, %xmm29
	vpternlogq	$210, %xmm12, %xmm13, %xmm16
	vpternlogq	$210, %xmm17, %xmm12, %xmm29
	vpternlogq	$210, %xmm7, %xmm6, %xmm17
	vpternlogq	$210, %xmm13, %xmm7, %xmm6
	vmovdqa64	%xmm16, -24(%rsp)
	vmovdqa	%xmm1, %xmm13
	vmovdqa	%xmm8, %xmm7
	vmovdqa64	%xmm29, %xmm16
	vpternlogq	$150, %xmm5, %xmm23, %xmm13
	vmovdqa	%xmm3, %xmm5
	vpternlogq	$150, %xmm9, %xmm15, %xmm7
	vprolq	$1, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm22, %xmm5
	vmovdqa64	%xmm26, %xmm9
	vprolq	$25, %xmm5, %xmm12
	vmovdqa	%xmm2, %xmm5
	vprolq	$6, %xmm13, %xmm13
	vpternlogq	$150, %xmm20, %xmm21, %xmm5
	vprolq	$8, %xmm5, %xmm5
	vpternlogq	$210, %xmm13, %xmm7, %xmm9
	vmovdqa64	%xmm5, %xmm19
	vmovdqa	%xmm9, -8(%rsp)
	vpternlogq	$210, %xmm7, %xmm26, %xmm19
	vpternlogq	$210, %xmm12, %xmm13, %xmm7
	vpternlogq	$210, %xmm5, %xmm12, %xmm13
	vpternlogq	$210, %xmm26, %xmm5, %xmm12
	vpxorq	%xmm30, %xmm4, %xmm5
	vmovdqa64	%xmm8, %xmm30
	vprolq	$36, %xmm5, %xmm5
	vpternlogq	$150, %xmm14, %xmm15, %xmm30
	vmovdqa	%xmm1, %xmm14
	vmovdqa64	%xmm2, %xmm26
	vpternlogq	$150, %xmm10, %xmm23, %xmm14
	vpternlogq	$150, %xmm27, %xmm21, %xmm26
	vpxorq	-72(%rsp), %xmm4, %xmm4
	vprolq	$15, %xmm14, %xmm10
	vmovdqa	%xmm3, %xmm14
	vpternlogq	$150, %xmm31, %xmm15, %xmm8
	vpternlogq	$150, -120(%rsp), %xmm23, %xmm1
	vprolq	$27, %xmm26, %xmm26
	vpternlogq	$150, %xmm24, %xmm22, %xmm14
	vpternlogq	$150, -88(%rsp), %xmm21, %xmm2
	vpternlogq	$150, -104(%rsp), %xmm22, %xmm3
	vprolq	$56, %xmm14, %xmm24
	vprolq	$10, %xmm30, %xmm9
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vprolq	$39, %xmm2, %xmm27
	vmovdqa	%xmm10, %xmm14
	vpxorq	%xmm25, %xmm7, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm26, %xmm30
	vmovdqa64	%xmm24, %xmm20
	vpternlogq	$210, %xmm26, %xmm24, %xmm14
	vpternlogq	$210, %xmm5, %xmm26, %xmm20
	vpternlogq	$210, %xmm9, %xmm5, %xmm30
	vpternlogq	$210, %xmm10, %xmm9, %xmm5
	vprolq	$62, %xmm1, %xmm26
	vpternlogq	$210, %xmm24, %xmm10, %xmm9
	vmovdqa64	%xmm4, %xmm24
	vpbroadcastq	%rcx, %xmm10
	vmovdqa64	%xmm8, %xmm29
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm5, %xmm23
	vpternlogq	$150, %xmm2, %xmm10, %xmm1
	vmovdqa64	%xmm9, %xmm22
	vmovdqa	-24(%rsp), %xmm2
	vmovdqa64	%xmm14, %xmm21
	vmovdqa64	%xmm20, %xmm10
	vpternlogq	$210, %xmm26, %xmm8, %xmm24
	vpternlogq	$210, %xmm3, %xmm26, %xmm29
	vpternlogq	$210, %xmm27, %xmm3, %xmm26
	vmovdqa64	%xmm26, %xmm15
	vpternlogq	$210, %xmm4, %xmm27, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm27
	vmovdqa	-8(%rsp), %xmm4
	vpternlogq	$150, %xmm1, %xmm30, %xmm15
	vmovdqa	%xmm11, %xmm1
	vmovdqa	%xmm3, -120(%rsp)
	vpternlogq	$150, %xmm3, %xmm17, %xmm1
	vpternlogq	$150, %xmm1, %xmm13, %xmm23
	vmovdqa	-40(%rsp), %xmm1
	vpternlogq	$150, %xmm27, %xmm6, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa64	%xmm18, %xmm1
	vprolq	$1, %xmm22, %xmm8
	vpternlogq	$150, %xmm24, %xmm2, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm1, %xmm19, %xmm21
	vmovdqa64	%xmm28, %xmm1
	vpternlogq	$150, %xmm29, %xmm16, %xmm1
	vpternlogq	$150, %xmm1, %xmm4, %xmm10
	vprolq	$1, %xmm23, %xmm4
	vprolq	$1, %xmm21, %xmm1
	vprolq	$1, %xmm10, %xmm3
	vpxorq	%xmm10, %xmm4, %xmm4
	vpbroadcastq	%rcx, %xmm10
	vpternlogq	$150, %xmm4, %xmm10, %xmm0
	vmovdqa	%xmm8, %xmm10
	vpxorq	%xmm7, %xmm4, %xmm7
	vprolq	$0, %xmm0, %xmm0
	vpternlogq	$150, %xmm17, %xmm15, %xmm10
	vmovdqa64	%xmm1, %xmm17
	vpxorq	%xmm26, %xmm4, %xmm26
	vprolq	$44, %xmm10, %xmm10
	vpternlogq	$150, %xmm12, %xmm23, %xmm17
	vprolq	$43, %xmm17, %xmm12
	vmovdqa64	%xmm3, %xmm17
	vprolq	$3, %xmm7, %xmm7
	vpternlogq	$150, %xmm14, %xmm22, %xmm17
	vprolq	$21, %xmm17, %xmm14
	vmovdqa64	%xmm2, %xmm17
	vprolq	$18, %xmm26, %xmm26
	vpternlogq	$150, %xmm29, %xmm21, %xmm17
	vprolq	$14, %xmm17, %xmm29
	vmovdqa64	%xmm14, %xmm17
	vmovdqa64	%xmm29, %xmm31
	vpternlogq	$210, %xmm0, %xmm29, %xmm17
	vpternlogq	$210, %xmm10, %xmm0, %xmm31
	vpternlogq	$210, %xmm12, %xmm10, %xmm0
	vpternlogq	$210, %xmm14, %xmm12, %xmm10
	vpternlogq	$210, %xmm29, %xmm14, %xmm12
	vmovdqa	%xmm3, %xmm14
	vmovdqa64	%xmm8, %xmm29
	vpternlogq	$150, %xmm18, %xmm22, %xmm14
	vmovdqa	%xmm12, -104(%rsp)
	vmovdqa64	%xmm2, %xmm18
	vpternlogq	$150, %xmm13, %xmm15, %xmm29
	vprolq	$28, %xmm14, %xmm12
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$150, %xmm16, %xmm21, %xmm18
	vmovdqa	%xmm1, %xmm13
	vprolq	$20, %xmm18, %xmm18
	vpternlogq	$150, %xmm5, %xmm15, %xmm14
	vpternlogq	$150, %xmm9, %xmm23, %xmm13
	vprolq	$45, %xmm14, %xmm5
	vmovdqa	%xmm1, %xmm14
	vprolq	$15, %xmm13, %xmm9
	vpternlogq	$150, %xmm27, %xmm23, %xmm14
	vmovdqa	%xmm3, %xmm13
	vmovdqa64	%xmm26, %xmm27
	vprolq	$61, %xmm14, %xmm14
	vpternlogq	$150, %xmm24, %xmm22, %xmm13
	vprolq	$56, %xmm13, %xmm24
	vmovdqa64	%xmm5, %xmm16
	vmovdqa	%xmm9, %xmm13
	vpternlogq	$210, %xmm12, %xmm14, %xmm16
	vmovdqa64	%xmm16, -88(%rsp)
	vmovdqa64	%xmm14, %xmm16
	vpternlogq	$210, %xmm18, %xmm12, %xmm16
	vpternlogq	$210, %xmm7, %xmm18, %xmm12
	vpternlogq	$210, %xmm5, %xmm7, %xmm18
	vpternlogq	$210, %xmm14, %xmm5, %xmm7
	vmovdqa	%xmm1, %xmm14
	vmovdqa	%xmm12, -72(%rsp)
	vmovdqa	%xmm8, %xmm5
	vpternlogq	$150, %xmm6, %xmm23, %xmm14
	vmovdqa	%xmm3, %xmm6
	vpternlogq	$150, %xmm11, %xmm15, %xmm5
	vprolq	$1, %xmm5, %xmm5
	vpternlogq	$150, %xmm19, %xmm22, %xmm6
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm8
	vpternlogq	$150, -40(%rsp), %xmm23, %xmm1
	vprolq	$25, %xmm6, %xmm12
	vmovdqa	%xmm2, %xmm6
	vpternlogq	$150, -24(%rsp), %xmm22, %xmm3
	vprolq	$6, %xmm14, %xmm14
	vpternlogq	$150, %xmm20, %xmm21, %xmm6
	vmovdqa64	%xmm24, %xmm20
	vprolq	$8, %xmm6, %xmm6
	vprolq	$10, %xmm29, %xmm11
	vprolq	$2, %xmm8, %xmm8
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm14, %xmm5, %xmm27
	vmovdqa64	%xmm6, %xmm19
	vpternlogq	$210, %xmm5, %xmm26, %xmm19
	vpternlogq	$210, %xmm12, %xmm14, %xmm5
	vpternlogq	$210, %xmm6, %xmm12, %xmm14
	vpternlogq	$210, %xmm26, %xmm6, %xmm12
	vmovdqa64	%xmm2, %xmm26
	vpxorq	%xmm25, %xmm4, %xmm6
	vprolq	$36, %xmm6, %xmm6
	vpternlogq	$150, %xmm28, %xmm21, %xmm26
	vpxorq	%xmm30, %xmm4, %xmm4
	vpternlogq	$150, -8(%rsp), %xmm21, %xmm2
	vprolq	$27, %xmm26, %xmm26
	vmovdqa64	%xmm8, %xmm28
	vprolq	$41, %xmm4, %xmm4
	vprolq	$62, %xmm1, %xmm25
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm26, %xmm24, %xmm13
	vpternlogq	$210, %xmm6, %xmm26, %xmm20
	vmovdqa64	%xmm26, %xmm29
	vprolq	$39, %xmm2, %xmm26
	vpternlogq	$210, %xmm11, %xmm6, %xmm29
	vpxorq	-72(%rsp), %xmm5, %xmm2
	vpternlogq	$210, %xmm9, %xmm11, %xmm6
	vpternlogq	$210, %xmm24, %xmm9, %xmm11
	vmovdqa64	%xmm4, %xmm24
	vpternlogq	$210, %xmm3, %xmm25, %xmm28
	vpternlogq	$210, %xmm25, %xmm8, %xmm24
	vpbroadcastq	%rax, %xmm9
	vmovdqa64	%xmm6, %xmm23
	vpternlogq	$150, %xmm2, %xmm9, %xmm1
	vmovdqa	-88(%rsp), %xmm2
	vmovdqa64	%xmm17, %xmm9
	vmovdqa64	%xmm13, %xmm21
	vmovdqa64	%xmm11, %xmm22
	vpternlogq	$150, %xmm24, %xmm2, %xmm9
	vpternlogq	$210, %xmm26, %xmm3, %xmm25
	vpternlogq	$210, %xmm4, %xmm26, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm26
	vmovdqa64	%xmm25, %xmm15
	vpternlogq	$150, %xmm9, %xmm19, %xmm21
	vmovdqa64	%xmm31, %xmm9
	vmovdqa	%xmm3, -120(%rsp)
	vpternlogq	$150, %xmm1, %xmm29, %xmm15
	vmovdqa	%xmm10, %xmm1
	vpternlogq	$150, %xmm28, %xmm16, %xmm9
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm3, %xmm18, %xmm1
	vpternlogq	$150, %xmm1, %xmm14, %xmm23
	vmovdqa	-104(%rsp), %xmm1
	vprolq	$1, %xmm23, %xmm4
	vpternlogq	$150, %xmm26, %xmm7, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa	%xmm9, %xmm1
	vmovdqa64	%xmm20, %xmm9
	vprolq	$1, %xmm22, %xmm8
	vpternlogq	$150, %xmm1, %xmm27, %xmm9
	vprolq	$1, %xmm21, %xmm1
	vprolq	$1, %xmm9, %xmm3
	vpxorq	%xmm9, %xmm4, %xmm4
	vpbroadcastq	%rax, %xmm9
	movl	$138, %eax
	vpternlogq	$150, %xmm4, %xmm9, %xmm0
	vpxorq	%xmm5, %xmm4, %xmm5
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm5, %xmm5
	vmovdqa	%xmm8, %xmm9
	vprolq	$18, %xmm25, %xmm25
	vpternlogq	$150, %xmm18, %xmm15, %xmm9
	vmovdqa64	%xmm1, %xmm18
	vprolq	$44, %xmm9, %xmm9
	vpternlogq	$150, %xmm12, %xmm23, %xmm18
	vprolq	$43, %xmm18, %xmm12
	vmovdqa64	%xmm3, %xmm18
	vpternlogq	$150, %xmm13, %xmm22, %xmm18
	vprolq	$21, %xmm18, %xmm13
	vmovdqa64	%xmm2, %xmm18
	vpternlogq	$150, %xmm28, %xmm21, %xmm18
	vprolq	$14, %xmm18, %xmm28
	vmovdqa64	%xmm13, %xmm18
	vmovdqa64	%xmm28, %xmm30
	vpternlogq	$210, %xmm0, %xmm28, %xmm18
	vpternlogq	$210, %xmm9, %xmm0, %xmm30
	vpternlogq	$210, %xmm12, %xmm9, %xmm0
	vpternlogq	$210, %xmm13, %xmm12, %xmm9
	vpternlogq	$210, %xmm28, %xmm13, %xmm12
	vmovdqa	%xmm8, %xmm13
	vpternlogq	$150, %xmm6, %xmm15, %xmm13
	vmovdqa64	%xmm12, %xmm28
	vmovdqa	%xmm3, %xmm12
	vprolq	$45, %xmm13, %xmm6
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm17, %xmm22, %xmm12
	vmovdqa64	%xmm2, %xmm17
	vprolq	$28, %xmm12, %xmm12
	vpternlogq	$150, %xmm26, %xmm23, %xmm13
	vpternlogq	$150, %xmm16, %xmm21, %xmm17
	vprolq	$61, %xmm13, %xmm13
	vprolq	$20, %xmm17, %xmm17
	vmovdqa64	%xmm6, %xmm16
	vpternlogq	$210, %xmm12, %xmm13, %xmm16
	vmovdqa64	%xmm16, -40(%rsp)
	vmovdqa64	%xmm13, %xmm16
	vpternlogq	$210, %xmm17, %xmm12, %xmm16
	vpternlogq	$210, %xmm5, %xmm17, %xmm12
	vpternlogq	$210, %xmm6, %xmm5, %xmm17
	vpternlogq	$210, %xmm13, %xmm6, %xmm5
	vmovdqa	%xmm1, %xmm13
	vmovdqa	%xmm8, %xmm6
	vmovdqa	%xmm12, -24(%rsp)
	vpternlogq	$150, %xmm7, %xmm23, %xmm13
	vmovdqa	%xmm2, %xmm7
	vpternlogq	$150, %xmm10, %xmm15, %xmm6
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm20, %xmm21, %xmm7
	vmovdqa	%xmm3, %xmm10
	vprolq	$8, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm22, %xmm10
	vprolq	$25, %xmm10, %xmm12
	vmovdqa64	%xmm25, %xmm10
	vprolq	$6, %xmm13, %xmm13
	vmovdqa64	%xmm7, %xmm19
	vpternlogq	$210, %xmm6, %xmm25, %xmm19
	vpternlogq	$210, %xmm13, %xmm6, %xmm10
	vpternlogq	$210, %xmm12, %xmm13, %xmm6
	vpternlogq	$210, %xmm7, %xmm12, %xmm13
	vpternlogq	$210, %xmm25, %xmm7, %xmm12
	vmovdqa64	%xmm2, %xmm25
	vpxorq	-72(%rsp), %xmm4, %xmm7
	vmovdqa	%xmm10, -8(%rsp)
	vpternlogq	$150, %xmm31, %xmm21, %xmm25
	vmovdqa64	%xmm8, %xmm31
	vpxorq	%xmm29, %xmm4, %xmm4
	vprolq	$27, %xmm25, %xmm25
	vpternlogq	$150, %xmm14, %xmm15, %xmm31
	vmovdqa	%xmm1, %xmm14
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm8
	vprolq	$36, %xmm7, %xmm7
	vpternlogq	$150, %xmm11, %xmm23, %xmm14
	vpternlogq	$150, %xmm27, %xmm21, %xmm2
	vpternlogq	$150, -104(%rsp), %xmm23, %xmm1
	vprolq	$15, %xmm14, %xmm11
	vmovdqa	%xmm3, %xmm14
	vpternlogq	$150, -88(%rsp), %xmm22, %xmm3
	vmovdqa64	%xmm28, -120(%rsp)
	vprolq	$10, %xmm31, %xmm10
	vpternlogq	$150, %xmm24, %xmm22, %xmm14
	vprolq	$56, %xmm14, %xmm24
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vmovdqa64	%xmm25, %xmm31
	vprolq	$39, %xmm2, %xmm27
	vpxorq	-24(%rsp), %xmm6, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vmovdqa	%xmm11, %xmm14
	vpternlogq	$210, %xmm10, %xmm7, %xmm31
	vmovdqa64	%xmm24, %xmm20
	vpternlogq	$210, %xmm25, %xmm24, %xmm14
	vpternlogq	$210, %xmm7, %xmm25, %xmm20
	vpternlogq	$210, %xmm11, %xmm10, %xmm7
	vpternlogq	$210, %xmm24, %xmm11, %xmm10
	vprolq	$62, %xmm1, %xmm25
	vmovdqa64	%xmm4, %xmm24
	vmovdqa64	%xmm8, %xmm26
	vpbroadcastq	%rax, %xmm11
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm7, %xmm23
	movl	$136, %eax
	vpternlogq	$150, %xmm2, %xmm11, %xmm1
	vmovdqa	-40(%rsp), %xmm2
	vmovdqa64	%xmm14, %xmm21
	vmovdqa64	%xmm10, %xmm22
	vpternlogq	$210, %xmm25, %xmm8, %xmm24
	vpternlogq	$210, %xmm3, %xmm25, %xmm26
	vpternlogq	$210, %xmm27, %xmm3, %xmm25
	vpternlogq	$210, %xmm4, %xmm27, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm27
	vmovdqa	-8(%rsp), %xmm8
	vmovdqa64	%xmm3, %xmm29
	vmovdqa64	%xmm25, %xmm3
	vpternlogq	$150, %xmm1, %xmm31, %xmm3
	vmovdqa	%xmm9, %xmm1
	vmovdqa	%xmm3, %xmm15
	vpternlogq	$150, %xmm29, %xmm17, %xmm1
	vmovdqa64	%xmm18, %xmm3
	vpternlogq	$150, %xmm1, %xmm13, %xmm23
	vpternlogq	$150, %xmm24, %xmm2, %xmm3
	vmovdqa64	%xmm28, %xmm1
	vprolq	$1, %xmm23, %xmm4
	vpternlogq	$150, %xmm3, %xmm19, %xmm21
	vmovdqa64	%xmm30, %xmm3
	vpternlogq	$150, %xmm27, %xmm5, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm26, %xmm16, %xmm3
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa	%xmm3, %xmm1
	vmovdqa64	%xmm20, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm3
	vprolq	$1, %xmm22, %xmm8
	vprolq	$1, %xmm21, %xmm1
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm11, %xmm0
	vpxorq	%xmm6, %xmm4, %xmm6
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm6, %xmm6
	vprolq	$18, %xmm25, %xmm25
	vmovdqa	%xmm8, %xmm11
	vpternlogq	$150, %xmm17, %xmm15, %xmm11
	vmovdqa64	%xmm1, %xmm17
	vprolq	$44, %xmm11, %xmm11
	vpternlogq	$150, %xmm12, %xmm23, %xmm17
	vprolq	$43, %xmm17, %xmm12
	vmovdqa64	%xmm3, %xmm17
	vpternlogq	$150, %xmm14, %xmm22, %xmm17
	vprolq	$21, %xmm17, %xmm14
	vmovdqa64	%xmm2, %xmm17
	vpternlogq	$150, %xmm26, %xmm21, %xmm17
	vprolq	$14, %xmm17, %xmm28
	vmovdqa64	%xmm14, %xmm17
	vmovdqa64	%xmm28, %xmm26
	vpternlogq	$210, %xmm0, %xmm28, %xmm17
	vpternlogq	$210, %xmm11, %xmm0, %xmm26
	vpternlogq	$210, %xmm12, %xmm11, %xmm0
	vpternlogq	$210, %xmm14, %xmm12, %xmm11
	vpternlogq	$210, %xmm28, %xmm14, %xmm12
	vmovdqa	%xmm3, %xmm14
	vpternlogq	$150, %xmm18, %xmm22, %xmm14
	vmovdqa	%xmm12, -104(%rsp)
	vmovdqa64	%xmm2, %xmm18
	vprolq	$28, %xmm14, %xmm12
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$150, %xmm16, %xmm21, %xmm18
	vprolq	$20, %xmm18, %xmm18
	vpternlogq	$150, %xmm7, %xmm15, %xmm14
	vprolq	$45, %xmm14, %xmm7
	vmovdqa	%xmm1, %xmm14
	vpternlogq	$150, %xmm27, %xmm23, %xmm14
	vprolq	$61, %xmm14, %xmm14
	vmovdqa64	%xmm7, %xmm16
	vpternlogq	$210, %xmm12, %xmm14, %xmm16
	vmovdqa64	%xmm16, -88(%rsp)
	vmovdqa64	%xmm14, %xmm16
	vpternlogq	$210, %xmm18, %xmm12, %xmm16
	vpternlogq	$210, %xmm6, %xmm18, %xmm12
	vpternlogq	$210, %xmm7, %xmm6, %xmm18
	vpternlogq	$210, %xmm14, %xmm7, %xmm6
	vmovdqa	%xmm1, %xmm14
	vmovdqa	%xmm8, %xmm7
	vmovdqa	%xmm12, 8(%rsp)
	vpternlogq	$150, %xmm5, %xmm23, %xmm14
	vmovdqa	%xmm2, %xmm5
	vpternlogq	$150, %xmm9, %xmm15, %xmm7
	vprolq	$1, %xmm7, %xmm7
	vpternlogq	$150, %xmm20, %xmm21, %xmm5
	vmovdqa	%xmm3, %xmm9
	vprolq	$8, %xmm5, %xmm5
	vpternlogq	$150, %xmm19, %xmm22, %xmm9
	vprolq	$25, %xmm9, %xmm12
	vmovdqa64	%xmm25, %xmm9
	vprolq	$6, %xmm14, %xmm14
	vmovdqa64	%xmm5, %xmm19
	vpternlogq	$210, %xmm7, %xmm25, %xmm19
	vpternlogq	$210, %xmm14, %xmm7, %xmm9
	vpternlogq	$210, %xmm12, %xmm14, %xmm7
	vpternlogq	$210, %xmm5, %xmm12, %xmm14
	vpternlogq	$210, %xmm25, %xmm5, %xmm12
	vmovdqa64	%xmm2, %xmm25
	vpxorq	-24(%rsp), %xmm4, %xmm5
	vmovdqa	%xmm9, -72(%rsp)
	vpternlogq	$150, %xmm30, %xmm21, %xmm25
	vmovdqa64	%xmm8, %xmm30
	vpxorq	%xmm31, %xmm4, %xmm4
	vmovdqa64	8(%rsp), %xmm31
	vprolq	$27, %xmm25, %xmm25
	vpternlogq	$150, %xmm13, %xmm15, %xmm30
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm29, %xmm15, %xmm8
	vprolq	$36, %xmm5, %xmm5
	vpternlogq	$150, %xmm10, %xmm23, %xmm13
	vpternlogq	$150, -120(%rsp), %xmm23, %xmm1
	vpternlogq	$150, -8(%rsp), %xmm21, %xmm2
	vprolq	$15, %xmm13, %xmm10
	vmovdqa	%xmm3, %xmm13
	vpternlogq	$150, -40(%rsp), %xmm22, %xmm3
	vprolq	$10, %xmm30, %xmm9
	vpternlogq	$150, %xmm24, %xmm22, %xmm13
	vprolq	$56, %xmm13, %xmm24
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vmovdqa64	%xmm25, %xmm30
	vprolq	$39, %xmm2, %xmm28
	vpxorq	%xmm31, %xmm7, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vmovdqa	%xmm10, %xmm13
	vpternlogq	$210, %xmm9, %xmm5, %xmm30
	vmovdqa64	%xmm24, %xmm20
	vpternlogq	$210, %xmm25, %xmm24, %xmm13
	vpternlogq	$210, %xmm5, %xmm25, %xmm20
	vpternlogq	$210, %xmm10, %xmm9, %xmm5
	vpternlogq	$210, %xmm24, %xmm10, %xmm9
	vprolq	$62, %xmm1, %xmm25
	vmovdqa64	%xmm4, %xmm24
	vmovdqa64	%xmm8, %xmm27
	vpbroadcastq	%rax, %xmm10
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm5, %xmm23
	movl	$2147516425, %eax
	vpternlogq	$150, %xmm2, %xmm10, %xmm1
	vmovdqa	-88(%rsp), %xmm2
	vmovdqa64	%xmm13, %xmm21
	vmovdqa64	%xmm9, %xmm22
	vpternlogq	$210, %xmm25, %xmm8, %xmm24
	vpternlogq	$210, %xmm3, %xmm25, %xmm27
	vpternlogq	$210, %xmm28, %xmm3, %xmm25
	vmovdqa64	%xmm25, %xmm15
	vpternlogq	$210, %xmm4, %xmm28, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm28
	vmovdqa	-72(%rsp), %xmm4
	vpternlogq	$150, %xmm1, %xmm30, %xmm15
	vmovdqa	%xmm11, %xmm1
	vmovdqa64	%xmm17, %xmm8
	vmovdqa	%xmm3, -120(%rsp)
	vpternlogq	$150, %xmm3, %xmm18, %xmm1
	vpternlogq	$150, %xmm24, %xmm2, %xmm8
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm1, %xmm14, %xmm23
	vmovdqa	-104(%rsp), %xmm1
	vpternlogq	$150, %xmm8, %xmm19, %xmm21
	vmovdqa64	%xmm26, %xmm8
	vpternlogq	$150, %xmm28, %xmm6, %xmm1
	vpternlogq	$150, %xmm27, %xmm16, %xmm8
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa	%xmm8, %xmm1
	vmovdqa64	%xmm20, %xmm8
	vpternlogq	$150, %xmm1, %xmm4, %xmm8
	vprolq	$1, %xmm23, %xmm4
	vprolq	$1, %xmm8, %xmm3
	vmovdqa64	%xmm2, %xmm29
	vprolq	$1, %xmm21, %xmm1
	vpternlogq	$150, %xmm27, %xmm21, %xmm29
	vprolq	$14, %xmm29, %xmm29
	vpxorq	%xmm8, %xmm4, %xmm4
	vprolq	$1, %xmm22, %xmm8
	vpternlogq	$150, %xmm4, %xmm10, %xmm0
	vpxorq	%xmm7, %xmm4, %xmm7
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm7, %xmm7
	vmovdqa64	%xmm29, %xmm27
	vprolq	$18, %xmm25, %xmm25
	vmovdqa	%xmm8, %xmm10
	vpternlogq	$150, %xmm18, %xmm15, %xmm10
	vmovdqa64	%xmm1, %xmm18
	vprolq	$44, %xmm10, %xmm10
	vpternlogq	$150, %xmm12, %xmm23, %xmm18
	vprolq	$43, %xmm18, %xmm12
	vmovdqa64	%xmm3, %xmm18
	vpternlogq	$150, %xmm13, %xmm22, %xmm18
	vprolq	$21, %xmm18, %xmm13
	vpternlogq	$210, %xmm10, %xmm0, %xmm27
	vmovdqa64	%xmm13, %xmm18
	vpternlogq	$210, %xmm0, %xmm29, %xmm18
	vpternlogq	$210, %xmm12, %xmm10, %xmm0
	vpternlogq	$210, %xmm13, %xmm12, %xmm10
	vpternlogq	$210, %xmm29, %xmm13, %xmm12
	vmovdqa	%xmm8, %xmm13
	vpternlogq	$150, %xmm5, %xmm15, %xmm13
	vmovdqa64	%xmm12, %xmm29
	vmovdqa	%xmm3, %xmm12
	vprolq	$45, %xmm13, %xmm5
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm17, %xmm22, %xmm12
	vmovdqa64	%xmm2, %xmm17
	vprolq	$28, %xmm12, %xmm12
	vpternlogq	$150, %xmm28, %xmm23, %xmm13
	vpternlogq	$150, %xmm16, %xmm21, %xmm17
	vprolq	$61, %xmm13, %xmm13
	vprolq	$20, %xmm17, %xmm17
	vmovdqa64	%xmm5, %xmm16
	vpternlogq	$210, %xmm12, %xmm13, %xmm16
	vmovdqa64	%xmm16, -40(%rsp)
	vmovdqa64	%xmm13, %xmm16
	vpternlogq	$210, %xmm17, %xmm12, %xmm16
	vpternlogq	$210, %xmm7, %xmm17, %xmm12
	vpternlogq	$210, %xmm5, %xmm7, %xmm17
	vpternlogq	$210, %xmm13, %xmm5, %xmm7
	vmovdqa	%xmm1, %xmm13
	vmovdqa	%xmm12, -24(%rsp)
	vmovdqa	%xmm8, %xmm5
	vpternlogq	$150, %xmm6, %xmm23, %xmm13
	vmovdqa	%xmm3, %xmm6
	vpternlogq	$150, %xmm11, %xmm15, %xmm5
	vprolq	$1, %xmm5, %xmm5
	vpternlogq	$150, %xmm19, %xmm22, %xmm6
	vprolq	$25, %xmm6, %xmm12
	vmovdqa	%xmm2, %xmm6
	vprolq	$6, %xmm13, %xmm13
	vpternlogq	$150, %xmm20, %xmm21, %xmm6
	vmovdqa64	%xmm25, %xmm20
	vprolq	$8, %xmm6, %xmm6
	vpternlogq	$210, %xmm13, %xmm5, %xmm20
	vmovdqa64	%xmm6, %xmm19
	vmovdqa64	%xmm20, -8(%rsp)
	vpternlogq	$210, %xmm5, %xmm25, %xmm19
	vpternlogq	$210, %xmm12, %xmm13, %xmm5
	vpternlogq	$210, %xmm6, %xmm12, %xmm13
	vpternlogq	$210, %xmm25, %xmm6, %xmm12
	vpxorq	%xmm31, %xmm4, %xmm6
	vmovdqa64	%xmm8, %xmm31
	vprolq	$36, %xmm6, %xmm6
	vpternlogq	$150, %xmm14, %xmm15, %xmm31
	vmovdqa	%xmm1, %xmm14
	vmovdqa64	%xmm2, %xmm25
	vprolq	$10, %xmm31, %xmm11
	vpternlogq	$150, %xmm9, %xmm23, %xmm14
	vpternlogq	$150, %xmm26, %xmm21, %xmm25
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm8
	vprolq	$15, %xmm14, %xmm9
	vmovdqa	%xmm3, %xmm14
	vpxorq	%xmm30, %xmm4, %xmm4
	vpternlogq	$150, -104(%rsp), %xmm23, %xmm1
	vprolq	$27, %xmm25, %xmm25
	vpternlogq	$150, %xmm24, %xmm22, %xmm14
	vpternlogq	$150, -72(%rsp), %xmm21, %xmm2
	vpternlogq	$150, -88(%rsp), %xmm22, %xmm3
	vprolq	$56, %xmm14, %xmm24
	vmovdqa64	%xmm29, -120(%rsp)
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vprolq	$39, %xmm2, %xmm28
	vpxorq	-24(%rsp), %xmm5, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vmovdqa	%xmm9, %xmm14
	vmovdqa64	%xmm24, %xmm31
	vpternlogq	$210, %xmm25, %xmm24, %xmm14
	vpternlogq	$210, %xmm6, %xmm25, %xmm31
	vmovdqa64	%xmm14, %xmm21
	vmovdqa64	%xmm31, %xmm20
	vmovdqa64	%xmm25, %xmm31
	vmovdqa64	%xmm8, %xmm26
	vprolq	$62, %xmm1, %xmm25
	vpternlogq	$210, %xmm11, %xmm6, %xmm31
	vpternlogq	$210, %xmm9, %xmm11, %xmm6
	vpternlogq	$210, %xmm24, %xmm9, %xmm11
	vmovdqa64	%xmm4, %xmm24
	vpbroadcastq	%rax, %xmm9
	vmovdqa	%xmm0, %xmm1
	subq	$32767, %rax
	vpternlogq	$150, %xmm2, %xmm9, %xmm1
	vmovdqa	-40(%rsp), %xmm2
	vmovdqa64	%xmm6, %xmm23
	vmovdqa64	%xmm11, %xmm22
	vpternlogq	$210, %xmm25, %xmm8, %xmm24
	vpternlogq	$210, %xmm3, %xmm25, %xmm26
	vpternlogq	$210, %xmm28, %xmm3, %xmm25
	vpternlogq	$210, %xmm4, %xmm28, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm28
	vmovdqa	-8(%rsp), %xmm8
	vmovdqa64	%xmm3, %xmm30
	vmovdqa64	%xmm25, %xmm3
	vpternlogq	$150, %xmm1, %xmm31, %xmm3
	vmovdqa	%xmm10, %xmm1
	vmovdqa	%xmm3, %xmm15
	vpternlogq	$150, %xmm30, %xmm17, %xmm1
	vmovdqa64	%xmm18, %xmm3
	vpternlogq	$150, %xmm1, %xmm13, %xmm23
	vpternlogq	$150, %xmm24, %xmm2, %xmm3
	vmovdqa64	%xmm29, %xmm1
	vprolq	$1, %xmm23, %xmm4
	vpternlogq	$150, %xmm3, %xmm19, %xmm21
	vmovdqa64	%xmm27, %xmm3
	vpternlogq	$150, %xmm28, %xmm7, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm26, %xmm16, %xmm3
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa	%xmm3, %xmm1
	vmovdqa64	%xmm20, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm3
	vprolq	$1, %xmm22, %xmm8
	vprolq	$1, %xmm21, %xmm1
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm9, %xmm0
	vpxorq	%xmm5, %xmm4, %xmm5
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm5, %xmm5
	vprolq	$18, %xmm25, %xmm25
	vmovdqa	%xmm8, %xmm9
	vpternlogq	$150, %xmm17, %xmm15, %xmm9
	vmovdqa64	%xmm1, %xmm17
	vprolq	$44, %xmm9, %xmm9
	vpternlogq	$150, %xmm12, %xmm23, %xmm17
	vprolq	$43, %xmm17, %xmm12
	vmovdqa64	%xmm3, %xmm17
	vpternlogq	$150, %xmm14, %xmm22, %xmm17
	vprolq	$21, %xmm17, %xmm14
	vmovdqa64	%xmm2, %xmm17
	vpternlogq	$150, %xmm26, %xmm21, %xmm17
	vprolq	$14, %xmm17, %xmm29
	vmovdqa64	%xmm14, %xmm17
	vmovdqa64	%xmm29, %xmm26
	vpternlogq	$210, %xmm0, %xmm29, %xmm17
	vpternlogq	$210, %xmm9, %xmm0, %xmm26
	vpternlogq	$210, %xmm12, %xmm9, %xmm0
	vpternlogq	$210, %xmm14, %xmm12, %xmm9
	vpternlogq	$210, %xmm29, %xmm14, %xmm12
	vmovdqa	%xmm3, %xmm14
	vpternlogq	$150, %xmm18, %xmm22, %xmm14
	vmovdqa	%xmm12, -104(%rsp)
	vmovdqa64	%xmm2, %xmm18
	vprolq	$28, %xmm14, %xmm12
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$150, %xmm16, %xmm21, %xmm18
	vprolq	$20, %xmm18, %xmm18
	vpternlogq	$150, %xmm6, %xmm15, %xmm14
	vprolq	$45, %xmm14, %xmm6
	vmovdqa	%xmm1, %xmm14
	vpternlogq	$150, %xmm28, %xmm23, %xmm14
	vprolq	$61, %xmm14, %xmm14
	vmovdqa64	%xmm6, %xmm16
	vpternlogq	$210, %xmm12, %xmm14, %xmm16
	vmovdqa64	%xmm16, -88(%rsp)
	vmovdqa64	%xmm14, %xmm16
	vpternlogq	$210, %xmm18, %xmm12, %xmm16
	vpternlogq	$210, %xmm5, %xmm18, %xmm12
	vpternlogq	$210, %xmm6, %xmm5, %xmm18
	vpternlogq	$210, %xmm14, %xmm6, %xmm5
	vmovdqa	%xmm1, %xmm14
	vmovdqa	%xmm8, %xmm6
	vmovdqa	%xmm12, 8(%rsp)
	vpternlogq	$150, %xmm7, %xmm23, %xmm14
	vmovdqa	%xmm2, %xmm7
	vpternlogq	$150, %xmm10, %xmm15, %xmm6
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm20, %xmm21, %xmm7
	vmovdqa	%xmm3, %xmm10
	vmovdqa64	%xmm8, %xmm20
	vprolq	$8, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm22, %xmm10
	vpternlogq	$150, %xmm13, %xmm15, %xmm20
	vmovdqa	%xmm1, %xmm13
	vprolq	$25, %xmm10, %xmm12
	vpternlogq	$150, %xmm11, %xmm23, %xmm13
	vmovdqa64	%xmm25, %xmm10
	vpternlogq	$150, %xmm30, %xmm15, %xmm8
	vprolq	$6, %xmm14, %xmm14
	vpternlogq	$150, -120(%rsp), %xmm23, %xmm1
	vprolq	$15, %xmm13, %xmm11
	vmovdqa	%xmm3, %xmm13
	vpternlogq	$150, -40(%rsp), %xmm22, %xmm3
	vprolq	$2, %xmm8, %xmm8
	vpternlogq	$150, %xmm24, %xmm22, %xmm13
	vprolq	$56, %xmm13, %xmm24
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm7, %xmm19
	vpternlogq	$210, %xmm6, %xmm25, %xmm19
	vpternlogq	$210, %xmm14, %xmm6, %xmm10
	vpternlogq	$210, %xmm12, %xmm14, %xmm6
	vpternlogq	$210, %xmm7, %xmm12, %xmm14
	vpternlogq	$210, %xmm25, %xmm7, %xmm12
	vpxorq	-24(%rsp), %xmm4, %xmm7
	vmovdqa64	%xmm2, %xmm25
	vpternlogq	$150, %xmm27, %xmm21, %xmm25
	vmovdqa64	%xmm10, %xmm29
	vmovdqa	%xmm11, %xmm13
	vprolq	$10, %xmm20, %xmm10
	vpxorq	%xmm31, %xmm4, %xmm4
	vmovdqa64	%xmm24, %xmm20
	vpternlogq	$150, -8(%rsp), %xmm21, %xmm2
	vprolq	$27, %xmm25, %xmm25
	vmovdqa64	8(%rsp), %xmm31
	vmovdqa64	%xmm8, %xmm27
	vmovdqa64	%xmm3, %xmm30
	vprolq	$36, %xmm7, %xmm7
	vmovdqa64	%xmm29, -120(%rsp)
	vprolq	$41, %xmm4, %xmm4
	vprolq	$39, %xmm2, %xmm28
	vpxorq	%xmm31, %xmm6, %xmm2
	vpternlogq	$210, %xmm25, %xmm24, %xmm13
	vpternlogq	$210, %xmm7, %xmm25, %xmm20
	vpternlogq	$210, %xmm10, %xmm7, %xmm25
	vpternlogq	$210, %xmm11, %xmm10, %xmm7
	vmovdqa64	%xmm25, -72(%rsp)
	vpternlogq	$210, %xmm24, %xmm11, %xmm10
	vmovdqa64	%xmm4, %xmm24
	vpbroadcastq	%rax, %xmm11
	vprolq	$62, %xmm1, %xmm25
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm4, %xmm28, %xmm30
	vmovdqa64	%xmm7, %xmm23
	vpternlogq	$150, %xmm2, %xmm11, %xmm1
	vmovdqa64	%xmm10, %xmm22
	vmovdqa	-88(%rsp), %xmm2
	vmovdqa64	%xmm13, %xmm21
	addq	$32897, %rax
	vpternlogq	$210, %xmm25, %xmm8, %xmm24
	vpternlogq	$210, %xmm3, %xmm25, %xmm27
	vpternlogq	$210, %xmm28, %xmm3, %xmm25
	vmovdqa	-72(%rsp), %xmm3
	vmovdqa64	%xmm25, %xmm15
	vpternlogq	$210, %xmm8, %xmm4, %xmm28
	vpternlogq	$150, %xmm1, %xmm3, %xmm15
	vmovdqa	%xmm9, %xmm1
	vmovdqa64	%xmm20, %xmm3
	vpternlogq	$150, %xmm30, %xmm18, %xmm1
	vpternlogq	$150, %xmm1, %xmm14, %xmm23
	vmovdqa	-104(%rsp), %xmm1
	vprolq	$1, %xmm23, %xmm4
	vpternlogq	$150, %xmm28, %xmm5, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm22
	vmovdqa64	%xmm17, %xmm1
	vprolq	$1, %xmm22, %xmm8
	vpternlogq	$150, %xmm24, %xmm2, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm1, %xmm19, %xmm21
	vmovdqa64	%xmm26, %xmm1
	vpternlogq	$150, %xmm27, %xmm16, %xmm1
	vpternlogq	$150, %xmm1, %xmm29, %xmm3
	vprolq	$1, %xmm21, %xmm1
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm11, %xmm0
	vpxorq	%xmm6, %xmm4, %xmm6
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$0, %xmm0, %xmm0
	vmovdqa64	%xmm8, %xmm29
	vprolq	$3, %xmm6, %xmm6
	vpternlogq	$150, %xmm18, %xmm15, %xmm29
	vprolq	$44, %xmm29, %xmm11
	vmovdqa64	%xmm2, %xmm29
	vprolq	$18, %xmm25, %xmm25
	vpternlogq	$150, %xmm27, %xmm21, %xmm29
	vprolq	$14, %xmm29, %xmm29
	vmovdqa64	%xmm1, %xmm18
	vpternlogq	$150, %xmm12, %xmm23, %xmm18
	vprolq	$43, %xmm18, %xmm12
	vmovdqa64	%xmm3, %xmm18
	vpternlogq	$150, %xmm13, %xmm22, %xmm18
	vprolq	$21, %xmm18, %xmm13
	vmovdqa64	%xmm29, %xmm27
	vpternlogq	$210, %xmm11, %xmm0, %xmm27
	vmovdqa64	%xmm13, %xmm18
	vpternlogq	$210, %xmm0, %xmm29, %xmm18
	vpternlogq	$210, %xmm12, %xmm11, %xmm0
	vpternlogq	$210, %xmm13, %xmm12, %xmm11
	vpternlogq	$210, %xmm29, %xmm13, %xmm12
	vmovdqa	%xmm8, %xmm13
	vpternlogq	$150, %xmm7, %xmm15, %xmm13
	vmovdqa	%xmm12, -40(%rsp)
	vmovdqa	%xmm3, %xmm12
	vprolq	$45, %xmm13, %xmm7
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm17, %xmm22, %xmm12
	vmovdqa64	%xmm2, %xmm17
	vprolq	$28, %xmm12, %xmm12
	vpternlogq	$150, %xmm28, %xmm23, %xmm13
	vpternlogq	$150, %xmm16, %xmm21, %xmm17
	vprolq	$61, %xmm13, %xmm13
	vprolq	$20, %xmm17, %xmm17
	vmovdqa64	%xmm7, %xmm28
	vmovdqa64	%xmm13, %xmm16
	vpternlogq	$210, %xmm12, %xmm13, %xmm28
	vpternlogq	$210, %xmm17, %xmm12, %xmm16
	vpternlogq	$210, %xmm6, %xmm17, %xmm12
	vpternlogq	$210, %xmm7, %xmm6, %xmm17
	vpternlogq	$210, %xmm13, %xmm7, %xmm6
	vmovdqa	%xmm1, %xmm13
	vmovdqa	%xmm12, -8(%rsp)
	vmovdqa	%xmm8, %xmm7
	vpternlogq	$150, %xmm5, %xmm23, %xmm13
	vmovdqa	%xmm3, %xmm5
	vpternlogq	$150, %xmm9, %xmm15, %xmm7
	vprolq	$1, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm22, %xmm5
	vmovdqa64	%xmm25, %xmm9
	vprolq	$25, %xmm5, %xmm12
	vmovdqa	%xmm2, %xmm5
	vprolq	$6, %xmm13, %xmm13
	vpternlogq	$150, %xmm20, %xmm21, %xmm5
	vmovdqa64	%xmm2, %xmm20
	vpternlogq	$150, -120(%rsp), %xmm21, %xmm2
	vprolq	$8, %xmm5, %xmm5
	vpternlogq	$150, %xmm26, %xmm21, %xmm20
	vmovdqa64	%xmm28, -120(%rsp)
	vprolq	$27, %xmm20, %xmm20
	vprolq	$39, %xmm2, %xmm26
	vpternlogq	$210, %xmm13, %xmm7, %xmm9
	vmovdqa64	%xmm5, %xmm19
	vmovdqa	%xmm9, -24(%rsp)
	vpternlogq	$210, %xmm7, %xmm25, %xmm19
	vpternlogq	$210, %xmm12, %xmm13, %xmm7
	vpternlogq	$210, %xmm5, %xmm12, %xmm13
	vpternlogq	$210, %xmm25, %xmm5, %xmm12
	vpxorq	%xmm31, %xmm4, %xmm5
	vmovdqa64	%xmm8, %xmm31
	vprolq	$36, %xmm5, %xmm5
	vpternlogq	$150, %xmm14, %xmm15, %xmm31
	vmovdqa64	%xmm3, %xmm25
	vmovdqa	%xmm1, %xmm14
	vprolq	$10, %xmm31, %xmm9
	vpternlogq	$150, %xmm10, %xmm23, %xmm14
	vpternlogq	$150, %xmm24, %xmm22, %xmm25
	vpxorq	-72(%rsp), %xmm4, %xmm4
	vprolq	$15, %xmm14, %xmm10
	vpternlogq	$150, %xmm30, %xmm15, %xmm8
	vpternlogq	$150, -104(%rsp), %xmm23, %xmm1
	vpternlogq	$150, -88(%rsp), %xmm22, %xmm3
	vprolq	$56, %xmm25, %xmm25
	vmovdqa64	%xmm20, %xmm31
	vmovdqa64	-8(%rsp), %xmm30
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vpxorq	%xmm30, %xmm7, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm9, %xmm5, %xmm31
	vmovdqa	%xmm10, %xmm14
	vmovdqa64	%xmm25, %xmm24
	vpternlogq	$210, %xmm20, %xmm25, %xmm14
	vpternlogq	$210, %xmm5, %xmm20, %xmm24
	vpternlogq	$210, %xmm10, %xmm9, %xmm5
	vpternlogq	$210, %xmm25, %xmm10, %xmm9
	vprolq	$62, %xmm1, %xmm25
	vmovdqa64	%xmm4, %xmm23
	vmovdqa64	%xmm8, %xmm29
	vpbroadcastq	%rax, %xmm10
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm5, %xmm22
	vmovdqa64	%xmm14, %xmm20
	movabsq	$-9223372036854775669, %rax
	vpternlogq	$150, %xmm2, %xmm10, %xmm1
	vmovdqa64	%xmm9, %xmm21
	vmovdqa	-24(%rsp), %xmm2
	vpternlogq	$210, %xmm25, %xmm8, %xmm23
	vpternlogq	$210, %xmm3, %xmm25, %xmm29
	vpternlogq	$210, %xmm26, %xmm3, %xmm25
	vpternlogq	$210, %xmm4, %xmm26, %xmm3
	vpternlogq	$210, %xmm8, %xmm4, %xmm26
	vmovdqa64	%xmm25, %xmm4
	vpternlogq	$150, %xmm1, %xmm31, %xmm4
	vmovdqa	%xmm11, %xmm1
	vmovdqa	%xmm3, -104(%rsp)
	vmovdqa	%xmm4, %xmm15
	vpternlogq	$150, %xmm3, %xmm17, %xmm1
	vmovdqa64	%xmm18, %xmm4
	vpternlogq	$150, %xmm1, %xmm13, %xmm22
	vpternlogq	$150, %xmm23, %xmm28, %xmm4
	vmovdqa	-40(%rsp), %xmm1
	vpternlogq	$150, %xmm4, %xmm19, %xmm20
	vmovdqa64	%xmm27, %xmm4
	vpternlogq	$150, %xmm26, %xmm6, %xmm1
	vpternlogq	$150, %xmm29, %xmm16, %xmm4
	vpternlogq	$150, %xmm1, %xmm12, %xmm21
	vmovdqa	%xmm4, %xmm1
	vmovdqa64	%xmm24, %xmm4
	vprolq	$1, %xmm21, %xmm8
	vpternlogq	$150, %xmm1, %xmm2, %xmm4
	vprolq	$1, %xmm20, %xmm1
	vmovdqa	%xmm4, %xmm3
	vprolq	$1, %xmm22, %xmm4
	vprolq	$1, %xmm15, %xmm2
	vpxorq	%xmm3, %xmm4, %xmm4
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm4, %xmm10, %xmm0
	vmovdqa	%xmm8, %xmm10
	vpxorq	%xmm7, %xmm4, %xmm7
	vprolq	$0, %xmm0, %xmm0
	vpternlogq	$150, %xmm17, %xmm15, %xmm10
	vmovdqa64	%xmm1, %xmm17
	vpxorq	%xmm25, %xmm4, %xmm25
	vprolq	$44, %xmm10, %xmm10
	vpternlogq	$150, %xmm12, %xmm22, %xmm17
	vprolq	$43, %xmm17, %xmm12
	vprolq	$3, %xmm7, %xmm7
	vprolq	$18, %xmm25, %xmm25
	vmovdqa64	%xmm3, %xmm17
	vpternlogq	$150, %xmm14, %xmm21, %xmm17
	vprolq	$21, %xmm17, %xmm14
	vmovdqa64	%xmm2, %xmm17
	vpternlogq	$150, %xmm29, %xmm20, %xmm17
	vprolq	$14, %xmm17, %xmm28
	vmovdqa64	%xmm14, %xmm17
	vmovdqa64	%xmm28, %xmm29
	vpternlogq	$210, %xmm0, %xmm28, %xmm17
	vpternlogq	$210, %xmm10, %xmm0, %xmm29
	vpternlogq	$210, %xmm12, %xmm10, %xmm0
	vpternlogq	$210, %xmm14, %xmm12, %xmm10
	vpternlogq	$210, %xmm28, %xmm14, %xmm12
	vmovdqa	%xmm3, %xmm14
	vpternlogq	$150, %xmm18, %xmm21, %xmm14
	vmovdqa	%xmm12, -88(%rsp)
	vmovdqa64	%xmm2, %xmm18
	vprolq	$28, %xmm14, %xmm12
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$150, %xmm16, %xmm20, %xmm18
	vprolq	$20, %xmm18, %xmm18
	vpternlogq	$150, %xmm5, %xmm15, %xmm14
	vprolq	$45, %xmm14, %xmm5
	vmovdqa	%xmm1, %xmm14
	vpternlogq	$150, %xmm26, %xmm22, %xmm14
	vmovdqa64	%xmm25, %xmm26
	vprolq	$61, %xmm14, %xmm14
	vmovdqa64	%xmm5, %xmm16
	vpternlogq	$210, %xmm12, %xmm14, %xmm16
	vmovdqa64	%xmm16, -72(%rsp)
	vmovdqa64	%xmm14, %xmm16
	vpternlogq	$210, %xmm18, %xmm12, %xmm16
	vpternlogq	$210, %xmm7, %xmm18, %xmm12
	vpternlogq	$210, %xmm5, %xmm7, %xmm18
	vpternlogq	$210, %xmm14, %xmm5, %xmm7
	vmovdqa	%xmm1, %xmm14
	vmovdqa	%xmm12, -8(%rsp)
	vmovdqa	%xmm8, %xmm5
	vpternlogq	$150, %xmm6, %xmm22, %xmm14
	vmovdqa	%xmm3, %xmm6
	vpternlogq	$150, %xmm11, %xmm15, %xmm5
	vprolq	$1, %xmm5, %xmm5
	vpternlogq	$150, %xmm19, %xmm21, %xmm6
	vprolq	$25, %xmm6, %xmm12
	vmovdqa	%xmm2, %xmm6
	vprolq	$6, %xmm14, %xmm14
	vpternlogq	$150, %xmm24, %xmm20, %xmm6
	vmovdqa64	%xmm2, %xmm24
	vpternlogq	$150, -24(%rsp), %xmm20, %xmm2
	vprolq	$8, %xmm6, %xmm6
	vpternlogq	$150, %xmm27, %xmm20, %xmm24
	vprolq	$27, %xmm24, %xmm24
	vprolq	$39, %xmm2, %xmm27
	vpternlogq	$210, %xmm14, %xmm5, %xmm26
	vmovdqa64	%xmm6, %xmm19
	vpternlogq	$210, %xmm5, %xmm25, %xmm19
	vpternlogq	$210, %xmm12, %xmm14, %xmm5
	vpternlogq	$210, %xmm6, %xmm12, %xmm14
	vpternlogq	$210, %xmm25, %xmm6, %xmm12
	vpxorq	%xmm30, %xmm4, %xmm6
	vmovdqa64	%xmm8, %xmm30
	vprolq	$36, %xmm6, %xmm6
	vpternlogq	$150, %xmm13, %xmm15, %xmm30
	vmovdqa64	%xmm3, %xmm25
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm9, %xmm22, %xmm13
	vpternlogq	$150, %xmm23, %xmm21, %xmm25
	vpternlogq	$150, -40(%rsp), %xmm22, %xmm1
	vprolq	$15, %xmm13, %xmm9
	vpternlogq	$150, -120(%rsp), %xmm21, %xmm3
	vpxorq	%xmm31, %xmm4, %xmm4
	vpternlogq	$150, -104(%rsp), %xmm15, %xmm8
	vprolq	$56, %xmm25, %xmm25
	vpxorq	-8(%rsp), %xmm5, %xmm2
	vprolq	$10, %xmm30, %xmm11
	vmovdqa64	%xmm24, %xmm30
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm8, %xmm8
	vprolq	$62, %xmm1, %xmm28
	vmovdqa	%xmm0, %xmm1
	vprolq	$55, %xmm3, %xmm3
	vmovdqa	%xmm9, %xmm13
	vmovdqa64	%xmm25, %xmm23
	vpternlogq	$210, %xmm24, %xmm25, %xmm13
	vpternlogq	$210, %xmm6, %xmm24, %xmm23
	vpternlogq	$210, %xmm11, %xmm6, %xmm30
	vpternlogq	$210, %xmm9, %xmm11, %xmm6
	vmovdqa64	%xmm4, %xmm24
	vpternlogq	$210, %xmm25, %xmm9, %xmm11
	vpbroadcastq	%rax, %xmm9
	vmovdqa64	%xmm8, %xmm25
	vpternlogq	$150, %xmm2, %xmm9, %xmm1
	vmovdqa64	%xmm6, %xmm22
	vmovdqa	-72(%rsp), %xmm2
	vpternlogq	$210, %xmm28, %xmm8, %xmm24
	vmovdqa64	%xmm11, %xmm21
	vmovdqa64	%xmm13, %xmm20
	vpternlogq	$210, %xmm3, %xmm28, %xmm25
	vpternlogq	$210, %xmm27, %xmm3, %xmm28
	vpternlogq	$210, %xmm4, %xmm27, %xmm3
	vmovdqa64	%xmm28, %xmm15
	vpternlogq	$210, %xmm8, %xmm4, %xmm27
	vmovdqa64	%xmm23, %xmm9
	vmovdqa	%xmm3, -120(%rsp)
	vpternlogq	$150, %xmm1, %xmm30, %xmm15
	vmovdqa	%xmm10, %xmm1
	vpbroadcastq	%rax, %xmm8
	addq	$32766, %rax
	vpternlogq	$150, %xmm3, %xmm18, %xmm1
	vpternlogq	$150, %xmm1, %xmm14, %xmm22
	vmovdqa	-88(%rsp), %xmm1
	vprolq	$1, %xmm22, %xmm4
	vpternlogq	$150, %xmm27, %xmm7, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm21
	vmovdqa64	%xmm17, %xmm1
	vpternlogq	$150, %xmm24, %xmm2, %xmm1
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm1, %xmm19, %xmm20
	vmovdqa64	%xmm29, %xmm1
	vpternlogq	$150, %xmm25, %xmm16, %xmm1
	vpternlogq	$150, %xmm1, %xmm26, %xmm9
	vprolq	$1, %xmm9, %xmm3
	vpxorq	%xmm9, %xmm4, %xmm4
	vprolq	$1, %xmm21, %xmm9
	vpternlogq	$150, %xmm4, %xmm8, %xmm0
	vpxorq	%xmm5, %xmm4, %xmm5
	vpxorq	%xmm28, %xmm4, %xmm28
	vprolq	$1, %xmm20, %xmm1
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm5, %xmm5
	vprolq	$18, %xmm28, %xmm28
	vmovdqa	%xmm9, %xmm8
	vpternlogq	$150, %xmm18, %xmm15, %xmm8
	vmovdqa64	%xmm1, %xmm18
	vprolq	$44, %xmm8, %xmm8
	vpternlogq	$150, %xmm12, %xmm22, %xmm18
	vprolq	$43, %xmm18, %xmm12
	vmovdqa64	%xmm3, %xmm18
	vpternlogq	$150, %xmm13, %xmm21, %xmm18
	vprolq	$21, %xmm18, %xmm13
	vmovdqa64	%xmm2, %xmm18
	vpternlogq	$150, %xmm25, %xmm20, %xmm18
	vprolq	$14, %xmm18, %xmm25
	vmovdqa64	%xmm13, %xmm18
	vmovdqa64	%xmm25, %xmm31
	vpternlogq	$210, %xmm0, %xmm25, %xmm18
	vpternlogq	$210, %xmm8, %xmm0, %xmm31
	vpternlogq	$210, %xmm12, %xmm8, %xmm0
	vpternlogq	$210, %xmm13, %xmm12, %xmm8
	vmovdqa64	%xmm31, -104(%rsp)
	vmovdqa64	%xmm8, %xmm31
	vmovdqa	%xmm12, %xmm8
	vpternlogq	$210, %xmm25, %xmm13, %xmm8
	vmovdqa	%xmm9, %xmm13
	vmovdqa64	%xmm2, %xmm25
	vpternlogq	$150, %xmm6, %xmm15, %xmm13
	vmovdqa	%xmm8, -40(%rsp)
	vmovdqa	%xmm3, %xmm8
	vpternlogq	$150, %xmm16, %xmm20, %xmm25
	vprolq	$45, %xmm13, %xmm6
	vmovdqa	%xmm1, %xmm13
	vpternlogq	$150, %xmm17, %xmm21, %xmm8
	vmovdqa64	%xmm28, %xmm16
	vprolq	$28, %xmm8, %xmm8
	vpternlogq	$150, %xmm27, %xmm22, %xmm13
	vprolq	$61, %xmm13, %xmm12
	vprolq	$20, %xmm25, %xmm25
	vmovdqa	%xmm6, %xmm13
	vmovdqa64	%xmm8, %xmm27
	vmovdqa64	%xmm12, %xmm17
	vpternlogq	$210, %xmm8, %xmm12, %xmm13
	vpternlogq	$210, %xmm25, %xmm8, %xmm17
	vpternlogq	$210, %xmm5, %xmm25, %xmm27
	vpternlogq	$210, %xmm6, %xmm5, %xmm25
	vmovdqa	%xmm13, -24(%rsp)
	vpternlogq	$210, %xmm12, %xmm6, %xmm5
	vmovdqa	%xmm9, %xmm6
	vmovdqa	%xmm9, %xmm12
	vpternlogq	$150, %xmm10, %xmm15, %xmm6
	vmovdqa	%xmm1, %xmm10
	vpternlogq	$150, %xmm14, %xmm15, %xmm12
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm7, %xmm22, %xmm10
	vmovdqa	%xmm2, %xmm7
	vpxorq	-8(%rsp), %xmm4, %xmm8
	vprolq	$6, %xmm10, %xmm13
	vpternlogq	$150, %xmm23, %xmm20, %xmm7
	vmovdqa	%xmm3, %xmm10
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm9
	vprolq	$8, %xmm7, %xmm7
	vpternlogq	$150, %xmm19, %xmm21, %xmm10
	vpxorq	%xmm30, %xmm4, %xmm4
	vpbroadcastq	%rax, %xmm30
	vprolq	$25, %xmm10, %xmm10
	vprolq	$41, %xmm4, %xmm4
	vprolq	$2, %xmm9, %xmm9
	vprolq	$36, %xmm8, %xmm8
	vprolq	$10, %xmm12, %xmm12
	vpternlogq	$210, %xmm13, %xmm6, %xmm16
	vmovdqa64	%xmm7, %xmm19
	vpternlogq	$210, %xmm6, %xmm28, %xmm19
	vpternlogq	$210, %xmm10, %xmm13, %xmm6
	vpternlogq	$210, %xmm7, %xmm10, %xmm13
	vpternlogq	$210, %xmm28, %xmm7, %xmm10
	vmovdqa	%xmm2, %xmm7
	vpternlogq	$150, %xmm26, %xmm20, %xmm2
	vpternlogq	$150, %xmm29, %xmm20, %xmm7
	vmovdqa64	%xmm1, %xmm29
	vpternlogq	$150, -88(%rsp), %xmm22, %xmm1
	vprolq	$27, %xmm7, %xmm7
	vpternlogq	$150, %xmm11, %xmm22, %xmm29
	vmovdqa64	%xmm4, %xmm26
	vmovdqa64	%xmm9, %xmm22
	vprolq	$15, %xmm29, %xmm14
	vmovdqa64	%xmm3, %xmm29
	vpternlogq	$150, -72(%rsp), %xmm21, %xmm3
	vmovdqa64	%xmm19, %xmm20
	vprolq	$62, %xmm1, %xmm28
	vpternlogq	$150, %xmm24, %xmm21, %xmm29
	vmovdqa	%xmm0, %xmm1
	vmovdqa64	%xmm10, %xmm21
	vprolq	$56, %xmm29, %xmm24
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm14, %xmm29
	vpternlogq	$210, %xmm28, %xmm9, %xmm26
	vpternlogq	$210, %xmm7, %xmm24, %xmm29
	vmovdqa64	%xmm24, %xmm23
	vmovdqa64	%xmm29, %xmm11
	vpternlogq	$210, %xmm8, %xmm7, %xmm23
	vpternlogq	$210, %xmm12, %xmm8, %xmm7
	vprolq	$39, %xmm2, %xmm29
	vpternlogq	$210, %xmm14, %xmm12, %xmm8
	vpxorq	%xmm6, %xmm27, %xmm2
	vpternlogq	$210, %xmm24, %xmm14, %xmm12
	vpbroadcastq	%rax, %xmm14
	vpternlogq	$210, %xmm3, %xmm28, %xmm22
	vmovdqa	%xmm7, %xmm15
	subq	$134, %rax
	vpternlogq	$150, %xmm2, %xmm14, %xmm1
	vmovdqa64	%xmm13, %xmm24
	vmovdqa	-104(%rsp), %xmm2
	vmovdqa64	%xmm17, %xmm14
	vpternlogq	$150, %xmm22, %xmm2, %xmm14
	vpternlogq	$210, %xmm29, %xmm3, %xmm28
	vpternlogq	$210, %xmm4, %xmm29, %xmm3
	vpternlogq	$210, %xmm9, %xmm4, %xmm29
	vmovdqa	-40(%rsp), %xmm4
	vpternlogq	$150, %xmm1, %xmm28, %xmm15
	vmovdqa64	%xmm25, %xmm1
	vmovdqa	%xmm3, -120(%rsp)
	vprolq	$1, %xmm15, %xmm2
	vpternlogq	$150, %xmm3, %xmm31, %xmm1
	vpternlogq	$150, %xmm1, %xmm8, %xmm24
	vmovdqa	%xmm5, %xmm1
	vpternlogq	$150, %xmm29, %xmm4, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm21
	vmovdqa	-24(%rsp), %xmm1
	vprolq	$1, %xmm21, %xmm9
	vpternlogq	$150, %xmm26, %xmm18, %xmm1
	vpternlogq	$150, %xmm1, %xmm11, %xmm20
	vmovdqa	%xmm14, %xmm1
	vmovdqa64	%xmm16, %xmm14
	vpternlogq	$150, %xmm1, %xmm23, %xmm14
	vprolq	$1, %xmm20, %xmm1
	vmovdqa	%xmm14, %xmm3
	vprolq	$1, %xmm24, %xmm14
	vmovdqa	%xmm9, %xmm4
	vpternlogq	$150, %xmm25, %xmm15, %xmm4
	vprolq	$44, %xmm4, %xmm4
	vmovdqa64	%xmm1, %xmm25
	vpxorq	%xmm3, %xmm14, %xmm14
	vpternlogq	$150, %xmm10, %xmm24, %xmm25
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm14, %xmm30, %xmm0
	vpxorq	%xmm14, %xmm6, %xmm6
	vpxorq	%xmm14, %xmm28, %xmm28
	vprolq	$43, %xmm25, %xmm10
	vpxorq	%xmm14, %xmm7, %xmm7
	vprolq	$0, %xmm0, %xmm0
	vprolq	$3, %xmm6, %xmm6
	vprolq	$18, %xmm28, %xmm28
	vprolq	$41, %xmm7, %xmm7
	vmovdqa64	%xmm3, %xmm25
	vpternlogq	$150, %xmm11, %xmm21, %xmm25
	vprolq	$21, %xmm25, %xmm11
	vmovdqa64	%xmm2, %xmm25
	vpternlogq	$150, %xmm22, %xmm20, %xmm25
	vprolq	$14, %xmm25, %xmm25
	vmovdqa64	%xmm11, %xmm22
	vmovdqa64	%xmm25, %xmm30
	vpternlogq	$210, %xmm0, %xmm25, %xmm22
	vpternlogq	$210, %xmm4, %xmm0, %xmm30
	vpternlogq	$210, %xmm10, %xmm4, %xmm0
	vpternlogq	$210, %xmm11, %xmm10, %xmm4
	vmovdqa64	%xmm30, -88(%rsp)
	vmovdqa64	%xmm4, %xmm30
	vmovdqa	%xmm9, %xmm4
	vpternlogq	$210, %xmm25, %xmm11, %xmm10
	vpternlogq	$150, %xmm8, %xmm15, %xmm4
	vmovdqa	%xmm1, %xmm8
	vmovdqa	%xmm10, -72(%rsp)
	vmovdqa64	%xmm2, %xmm25
	vprolq	$45, %xmm4, %xmm4
	vpternlogq	$150, %xmm29, %xmm24, %xmm8
	vmovdqa	%xmm3, %xmm10
	vpternlogq	$150, %xmm17, %xmm20, %xmm25
	vprolq	$61, %xmm8, %xmm8
	vpternlogq	$150, %xmm18, %xmm21, %xmm10
	vmovdqa64	%xmm28, %xmm17
	vprolq	$28, %xmm10, %xmm10
	vprolq	$20, %xmm25, %xmm25
	vmovdqa64	%xmm4, %xmm29
	vmovdqa64	%xmm8, %xmm18
	vpternlogq	$210, %xmm10, %xmm8, %xmm29
	vpternlogq	$210, %xmm25, %xmm10, %xmm18
	vpternlogq	$210, %xmm6, %xmm25, %xmm10
	vpternlogq	$210, %xmm4, %xmm6, %xmm25
	vpternlogq	$210, %xmm8, %xmm4, %xmm6
	vmovdqa	%xmm1, %xmm8
	vmovdqa	%xmm9, %xmm4
	vmovdqa	%xmm10, -8(%rsp)
	vpternlogq	$150, %xmm5, %xmm24, %xmm8
	vmovdqa	%xmm3, %xmm5
	vpternlogq	$150, %xmm31, %xmm15, %xmm4
	vprolq	$6, %xmm8, %xmm11
	vmovdqa	%xmm2, %xmm8
	vpternlogq	$150, %xmm19, %xmm21, %xmm5
	vpbroadcastq	%rax, %xmm31
	vprolq	$1, %xmm4, %xmm4
	vpternlogq	$150, %xmm23, %xmm20, %xmm8
	vprolq	$8, %xmm8, %xmm8
	vprolq	$25, %xmm5, %xmm5
	vpternlogq	$210, %xmm11, %xmm4, %xmm17
	vmovdqa64	%xmm8, %xmm19
	vpternlogq	$210, %xmm4, %xmm28, %xmm19
	vpternlogq	$210, %xmm5, %xmm11, %xmm4
	vpternlogq	$210, %xmm8, %xmm5, %xmm11
	vpternlogq	$210, %xmm28, %xmm8, %xmm5
	vmovdqa64	%xmm9, %xmm28
	vpxorq	%xmm14, %xmm27, %xmm8
	vprolq	$36, %xmm8, %xmm8
	vpternlogq	$150, %xmm13, %xmm15, %xmm28
	vmovdqa64	%xmm3, %xmm27
	vmovdqa	%xmm1, %xmm13
	vprolq	$10, %xmm28, %xmm10
	vmovdqa64	%xmm5, %xmm23
	vpternlogq	$150, %xmm12, %xmm24, %xmm13
	vpternlogq	$150, %xmm26, %xmm21, %xmm27
	vprolq	$15, %xmm13, %xmm13
	vmovdqa	%xmm2, %xmm5
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm9
	vpternlogq	$150, -40(%rsp), %xmm24, %xmm1
	vprolq	$56, %xmm27, %xmm27
	vpternlogq	$150, -104(%rsp), %xmm20, %xmm5
	vpternlogq	$150, -24(%rsp), %xmm21, %xmm3
	vpternlogq	$150, %xmm16, %xmm20, %xmm2
	vprolq	$27, %xmm5, %xmm5
	vpbroadcastq	%rax, %xmm14
	vmovdqa64	%xmm7, %xmm24
	vmovdqa64	%xmm11, %xmm20
	vprolq	$2, %xmm9, %xmm9
	vmovdqa64	%xmm23, %xmm16
	vmovdqa64	%xmm19, %xmm15
	subq	$1, %rax
	vprolq	$55, %xmm3, %xmm3
	vprolq	$39, %xmm2, %xmm28
	vpxorq	-8(%rsp), %xmm4, %xmm2
	vmovdqa64	%xmm13, %xmm26
	vmovdqa64	%xmm27, %xmm12
	vpternlogq	$210, %xmm5, %xmm27, %xmm26
	vpternlogq	$210, %xmm8, %xmm5, %xmm12
	vpternlogq	$210, %xmm10, %xmm8, %xmm5
	vpternlogq	$210, %xmm13, %xmm10, %xmm8
	vpternlogq	$210, %xmm27, %xmm13, %xmm10
	vmovdqa64	%xmm9, %xmm21
	vprolq	$62, %xmm1, %xmm27
	vmovdqa	%xmm0, %xmm1
	vmovdqa	%xmm3, %xmm13
	vpternlogq	$150, %xmm2, %xmm14, %xmm1
	vmovdqa	%xmm5, %xmm14
	vpternlogq	$210, %xmm7, %xmm28, %xmm13
	vmovdqa	-72(%rsp), %xmm2
	vmovdqa	%xmm13, -120(%rsp)
	vpternlogq	$210, %xmm27, %xmm9, %xmm24
	vpternlogq	$210, %xmm3, %xmm27, %xmm21
	vpternlogq	$210, %xmm28, %xmm3, %xmm27
	vpternlogq	$150, %xmm1, %xmm27, %xmm14
	vmovdqa64	%xmm25, %xmm1
	vpternlogq	$210, %xmm9, %xmm7, %xmm28
	vmovdqa	-88(%rsp), %xmm7
	vpternlogq	$150, %xmm13, %xmm30, %xmm1
	vmovdqa64	%xmm17, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm20
	vmovdqa	%xmm6, %xmm1
	vprolq	$1, %xmm20, %xmm13
	vpternlogq	$150, %xmm28, %xmm2, %xmm1
	vprolq	$1, %xmm14, %xmm2
	vpternlogq	$150, %xmm1, %xmm10, %xmm16
	vmovdqa64	%xmm29, %xmm1
	vprolq	$1, %xmm16, %xmm9
	vpternlogq	$150, %xmm24, %xmm22, %xmm1
	vpternlogq	$150, %xmm1, %xmm26, %xmm15
	vmovdqa64	%xmm18, %xmm1
	vpternlogq	$150, %xmm21, %xmm7, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm3
	vprolq	$1, %xmm15, %xmm1
	vpxorq	%xmm3, %xmm13, %xmm13
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm13, %xmm31, %xmm0
	vpxorq	%xmm13, %xmm4, %xmm4
	vpxorq	%xmm13, %xmm27, %xmm27
	vprolq	$0, %xmm0, %xmm0
	vmovdqa	%xmm9, %xmm7
	vpxorq	%xmm13, %xmm5, %xmm5
	vprolq	$3, %xmm4, %xmm4
	vpternlogq	$150, %xmm25, %xmm14, %xmm7
	vprolq	$44, %xmm7, %xmm7
	vprolq	$18, %xmm27, %xmm27
	vprolq	$41, %xmm5, %xmm5
	vmovdqa64	%xmm1, %xmm25
	vpternlogq	$150, %xmm23, %xmm20, %xmm25
	vprolq	$43, %xmm25, %xmm23
	vmovdqa64	%xmm3, %xmm25
	vpternlogq	$150, %xmm26, %xmm16, %xmm25
	vmovdqa64	%xmm2, %xmm26
	vprolq	$21, %xmm25, %xmm25
	vpternlogq	$150, %xmm21, %xmm15, %xmm26
	vprolq	$14, %xmm26, %xmm26
	vmovdqa64	%xmm25, %xmm21
	vmovdqa64	%xmm26, %xmm31
	vpternlogq	$210, %xmm0, %xmm26, %xmm21
	vpternlogq	$210, %xmm7, %xmm0, %xmm31
	vpternlogq	$210, %xmm23, %xmm7, %xmm0
	vpternlogq	$210, %xmm25, %xmm23, %xmm7
	vmovdqa64	%xmm31, -104(%rsp)
	vmovdqa64	%xmm7, %xmm31
	vmovdqa	%xmm9, %xmm7
	vpternlogq	$210, %xmm26, %xmm25, %xmm23
	vpternlogq	$150, %xmm8, %xmm14, %xmm7
	vmovdqa64	%xmm3, %xmm25
	vmovdqa	%xmm1, %xmm8
	vmovdqa64	%xmm23, -40(%rsp)
	vprolq	$45, %xmm7, %xmm7
	vpternlogq	$150, %xmm22, %xmm16, %xmm25
	vpternlogq	$150, %xmm28, %xmm20, %xmm8
	vmovdqa64	%xmm2, %xmm22
	vprolq	$61, %xmm8, %xmm8
	vpternlogq	$150, %xmm18, %xmm15, %xmm22
	vmovdqa64	%xmm3, %xmm26
	vmovdqa64	%xmm27, %xmm18
	vprolq	$20, %xmm22, %xmm23
	vpternlogq	$150, %xmm19, %xmm16, %xmm26
	vprolq	$28, %xmm25, %xmm25
	vprolq	$25, %xmm26, %xmm26
	vmovdqa64	%xmm7, %xmm28
	vmovdqa64	%xmm8, %xmm22
	vpternlogq	$210, %xmm25, %xmm8, %xmm28
	vpternlogq	$210, %xmm23, %xmm25, %xmm22
	vpternlogq	$210, %xmm4, %xmm23, %xmm25
	vpternlogq	$210, %xmm7, %xmm4, %xmm23
	vpternlogq	$210, %xmm8, %xmm7, %xmm4
	vmovdqa	%xmm1, %xmm8
	vmovdqa64	%xmm25, -24(%rsp)
	vpternlogq	$150, %xmm6, %xmm20, %xmm8
	vmovdqa	%xmm2, %xmm6
	vmovdqa	%xmm9, %xmm7
	vprolq	$6, %xmm8, %xmm8
	vpternlogq	$150, %xmm12, %xmm15, %xmm6
	vpternlogq	$150, %xmm30, %xmm14, %xmm7
	vpbroadcastq	%rax, %xmm30
	vprolq	$8, %xmm6, %xmm6
	vprolq	$1, %xmm7, %xmm7
	vmovdqa64	%xmm8, %xmm19
	vmovdqa	%xmm6, %xmm12
	vpternlogq	$210, %xmm6, %xmm26, %xmm19
	vpternlogq	$210, %xmm8, %xmm7, %xmm18
	vpternlogq	$210, %xmm7, %xmm27, %xmm12
	vpternlogq	$210, %xmm26, %xmm8, %xmm7
	vpternlogq	$210, %xmm27, %xmm6, %xmm26
	vmovdqa64	%xmm1, %xmm27
	vmovdqa	%xmm2, %xmm6
	vpternlogq	$150, %xmm10, %xmm20, %xmm27
	vmovdqa	%xmm3, %xmm10
	vpternlogq	$150, -88(%rsp), %xmm15, %xmm6
	vprolq	$15, %xmm27, %xmm27
	vpternlogq	$150, %xmm24, %xmm16, %xmm10
	vmovdqa64	%xmm12, %xmm25
	vpxorq	-8(%rsp), %xmm13, %xmm8
	vprolq	$56, %xmm10, %xmm24
	vmovdqa	%xmm9, %xmm12
	vpternlogq	$150, -72(%rsp), %xmm20, %xmm1
	vpternlogq	$150, -120(%rsp), %xmm14, %xmm9
	vprolq	$27, %xmm6, %xmm6
	vpternlogq	$150, %xmm11, %xmm14, %xmm12
	vpternlogq	$150, %xmm17, %xmm15, %xmm2
	vpternlogq	$150, %xmm29, %xmm16, %xmm3
	vprolq	$36, %xmm8, %xmm8
	vpbroadcastq	%rax, %xmm14
	vmovdqa64	%xmm19, %xmm20
	vmovdqa64	%xmm26, %xmm16
	vprolq	$10, %xmm12, %xmm12
	vmovdqa64	%xmm25, %xmm15
	subq	$32642, %rax
	vprolq	$2, %xmm9, %xmm9
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm27, %xmm10
	vprolq	$39, %xmm2, %xmm29
	vpxorq	-24(%rsp), %xmm7, %xmm2
	vpternlogq	$210, %xmm6, %xmm24, %xmm10
	vmovdqa	%xmm10, %xmm11
	vmovdqa64	%xmm24, %xmm10
	vpternlogq	$210, %xmm8, %xmm6, %xmm10
	vpternlogq	$210, %xmm12, %xmm8, %xmm6
	vpternlogq	$210, %xmm27, %xmm12, %xmm8
	vpternlogq	$210, %xmm24, %xmm27, %xmm12
	vmovdqa64	%xmm9, %xmm17
	vmovdqa64	%xmm5, %xmm24
	vprolq	$62, %xmm1, %xmm27
	vmovdqa	%xmm0, %xmm1
	vmovdqa	%xmm3, %xmm13
	vpternlogq	$150, %xmm2, %xmm14, %xmm1
	vmovdqa	%xmm6, %xmm14
	vpternlogq	$210, %xmm5, %xmm29, %xmm13
	vmovdqa	-104(%rsp), %xmm2
	vmovdqa	%xmm13, -120(%rsp)
	vpternlogq	$210, %xmm27, %xmm9, %xmm24
	vpternlogq	$210, %xmm3, %xmm27, %xmm17
	vpternlogq	$210, %xmm29, %xmm3, %xmm27
	vpternlogq	$150, %xmm1, %xmm27, %xmm14
	vmovdqa64	%xmm23, %xmm1
	vpternlogq	$210, %xmm9, %xmm5, %xmm29
	vmovdqa	-40(%rsp), %xmm5
	vpternlogq	$150, %xmm13, %xmm31, %xmm1
	vmovdqa64	%xmm18, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm20
	vmovdqa	%xmm4, %xmm1
	vprolq	$1, %xmm20, %xmm13
	vpternlogq	$150, %xmm29, %xmm5, %xmm1
	vpternlogq	$150, %xmm1, %xmm12, %xmm16
	vmovdqa64	%xmm28, %xmm1
	vprolq	$1, %xmm16, %xmm9
	vpternlogq	$150, %xmm24, %xmm21, %xmm1
	vpternlogq	$150, %xmm1, %xmm11, %xmm15
	vmovdqa64	%xmm22, %xmm1
	vpternlogq	$150, %xmm17, %xmm2, %xmm1
	vprolq	$1, %xmm14, %xmm2
	vpternlogq	$150, %xmm1, %xmm10, %xmm3
	vprolq	$1, %xmm15, %xmm1
	vpxorq	%xmm3, %xmm13, %xmm13
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm13, %xmm30, %xmm0
	vpxorq	%xmm13, %xmm7, %xmm7
	vpxorq	%xmm13, %xmm27, %xmm27
	vprolq	$0, %xmm0, %xmm0
	vmovdqa	%xmm9, %xmm5
	vpxorq	%xmm13, %xmm6, %xmm6
	vprolq	$3, %xmm7, %xmm7
	vpternlogq	$150, %xmm23, %xmm14, %xmm5
	vprolq	$44, %xmm5, %xmm5
	vprolq	$18, %xmm27, %xmm27
	vprolq	$41, %xmm6, %xmm6
	vmovdqa64	%xmm1, %xmm23
	vpternlogq	$150, %xmm26, %xmm20, %xmm23
	vmovdqa64	%xmm3, %xmm26
	vprolq	$43, %xmm23, %xmm23
	vpternlogq	$150, %xmm11, %xmm16, %xmm26
	vprolq	$21, %xmm26, %xmm11
	vmovdqa64	%xmm2, %xmm26
	vpternlogq	$150, %xmm17, %xmm15, %xmm26
	vprolq	$14, %xmm26, %xmm26
	vmovdqa64	%xmm11, %xmm17
	vmovdqa64	%xmm26, %xmm30
	vpternlogq	$210, %xmm0, %xmm26, %xmm17
	vpternlogq	$210, %xmm5, %xmm0, %xmm30
	vpternlogq	$210, %xmm23, %xmm5, %xmm0
	vpternlogq	$210, %xmm11, %xmm23, %xmm5
	vmovdqa64	%xmm30, -88(%rsp)
	vmovdqa64	%xmm5, %xmm30
	vmovdqa	%xmm9, %xmm5
	vpternlogq	$210, %xmm26, %xmm11, %xmm23
	vpternlogq	$150, %xmm8, %xmm14, %xmm5
	vmovdqa64	%xmm3, %xmm26
	vmovdqa	%xmm1, %xmm8
	vmovdqa64	%xmm23, -72(%rsp)
	vprolq	$45, %xmm5, %xmm5
	vpternlogq	$150, %xmm21, %xmm16, %xmm26
	vpternlogq	$150, %xmm29, %xmm20, %xmm8
	vmovdqa64	%xmm2, %xmm21
	vprolq	$28, %xmm26, %xmm11
	vpternlogq	$150, %xmm22, %xmm15, %xmm21
	vmovdqa64	%xmm3, %xmm26
	vprolq	$61, %xmm8, %xmm8
	vpternlogq	$150, %xmm25, %xmm16, %xmm26
	vprolq	$20, %xmm21, %xmm23
	vprolq	$25, %xmm26, %xmm26
	vmovdqa64	%xmm5, %xmm29
	vmovdqa64	%xmm11, %xmm21
	vmovdqa64	%xmm8, %xmm22
	vpternlogq	$210, %xmm11, %xmm8, %xmm29
	vpternlogq	$210, %xmm23, %xmm11, %xmm22
	vpternlogq	$210, %xmm7, %xmm23, %xmm21
	vpternlogq	$210, %xmm5, %xmm7, %xmm23
	vpternlogq	$210, %xmm8, %xmm5, %xmm7
	vmovdqa	%xmm1, %xmm8
	vmovdqa	%xmm9, %xmm5
	vmovdqa64	%xmm21, -8(%rsp)
	vpternlogq	$150, %xmm4, %xmm20, %xmm8
	vmovdqa	%xmm2, %xmm4
	vpternlogq	$150, %xmm31, %xmm14, %xmm5
	vprolq	$6, %xmm8, %xmm11
	vpternlogq	$150, %xmm10, %xmm15, %xmm4
	vmovdqa64	%xmm27, %xmm8
	vmovdqa	%xmm9, %xmm10
	vprolq	$8, %xmm4, %xmm4
	vpternlogq	$150, %xmm19, %xmm14, %xmm10
	vpternlogq	$150, -120(%rsp), %xmm14, %xmm9
	vpbroadcastq	%rax, %xmm14
	vprolq	$1, %xmm5, %xmm5
	vpbroadcastq	%rax, %xmm31
	vmovdqa64	%xmm29, -120(%rsp)
	movl	$32778, %eax
	vprolq	$10, %xmm10, %xmm10
	vprolq	$2, %xmm9, %xmm9
	vmovdqa64	%xmm4, %xmm25
	vpternlogq	$210, %xmm5, %xmm27, %xmm25
	vpternlogq	$210, %xmm11, %xmm5, %xmm8
	vpternlogq	$210, %xmm26, %xmm11, %xmm5
	vpternlogq	$210, %xmm4, %xmm26, %xmm11
	vpternlogq	$210, %xmm27, %xmm4, %xmm26
	vmovdqa64	%xmm1, %xmm27
	vpternlogq	$150, %xmm12, %xmm20, %xmm27
	vmovdqa	%xmm3, %xmm12
	vmovdqa64	%xmm8, %xmm21
	vprolq	$15, %xmm27, %xmm27
	vpxorq	-24(%rsp), %xmm13, %xmm8
	vpternlogq	$150, %xmm24, %xmm16, %xmm12
	vmovdqa	%xmm2, %xmm4
	vprolq	$56, %xmm12, %xmm24
	vpternlogq	$150, -104(%rsp), %xmm15, %xmm4
	vpternlogq	$150, -40(%rsp), %xmm20, %xmm1
	vpternlogq	$150, %xmm18, %xmm15, %xmm2
	vprolq	$27, %xmm4, %xmm4
	vpternlogq	$150, %xmm28, %xmm16, %xmm3
	vmovdqa64	%xmm9, %xmm28
	vmovdqa64	%xmm11, %xmm18
	vprolq	$36, %xmm8, %xmm8
	vmovdqa64	%xmm26, %xmm16
	vmovdqa64	%xmm25, %xmm15
	vprolq	$55, %xmm3, %xmm3
	vprolq	$39, %xmm2, %xmm20
	vpxorq	-8(%rsp), %xmm5, %xmm2
	vmovdqa64	%xmm27, %xmm19
	vmovdqa64	%xmm24, %xmm12
	vpternlogq	$210, %xmm4, %xmm24, %xmm19
	vpternlogq	$210, %xmm8, %xmm4, %xmm12
	vpternlogq	$210, %xmm10, %xmm8, %xmm4
	vpternlogq	$210, %xmm27, %xmm10, %xmm8
	vpternlogq	$210, %xmm24, %xmm27, %xmm10
	vmovdqa64	%xmm6, %xmm24
	vmovdqa	%xmm3, %xmm13
	vprolq	$62, %xmm1, %xmm27
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm6, %xmm20, %xmm13
	vpternlogq	$150, %xmm2, %xmm14, %xmm1
	vmovdqa	%xmm4, %xmm14
	vmovdqa	%xmm13, -104(%rsp)
	vmovdqa	-88(%rsp), %xmm2
	vpternlogq	$210, %xmm27, %xmm9, %xmm24
	vpternlogq	$210, %xmm3, %xmm27, %xmm28
	vpternlogq	$210, %xmm20, %xmm3, %xmm27
	vpternlogq	$150, %xmm1, %xmm27, %xmm14
	vmovdqa64	%xmm23, %xmm1
	vpternlogq	$210, %xmm9, %xmm6, %xmm20
	vmovdqa	-72(%rsp), %xmm6
	vpternlogq	$150, %xmm13, %xmm30, %xmm1
	vmovdqa64	%xmm22, %xmm9
	vmovdqa64	%xmm21, %xmm3
	vpternlogq	$150, %xmm1, %xmm8, %xmm18
	vmovdqa	%xmm7, %xmm1
	vpternlogq	$150, %xmm28, %xmm2, %xmm9
	vprolq	$1, %xmm18, %xmm13
	vpternlogq	$150, %xmm20, %xmm6, %xmm1
	vpternlogq	$150, %xmm9, %xmm12, %xmm3
	vprolq	$1, %xmm14, %xmm2
	vpternlogq	$150, %xmm1, %xmm10, %xmm16
	vmovdqa64	%xmm29, %xmm1
	vprolq	$1, %xmm16, %xmm9
	vpternlogq	$150, %xmm24, %xmm17, %xmm1
	vpternlogq	$150, %xmm1, %xmm19, %xmm15
	vprolq	$1, %xmm15, %xmm1
	vpxorq	%xmm3, %xmm13, %xmm13
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm13, %xmm31, %xmm0
	vpxorq	%xmm13, %xmm5, %xmm5
	vpxorq	%xmm13, %xmm27, %xmm27
	vprolq	$0, %xmm0, %xmm0
	vmovdqa	%xmm9, %xmm6
	vpxorq	%xmm13, %xmm4, %xmm4
	vprolq	$3, %xmm5, %xmm5
	vpternlogq	$150, %xmm23, %xmm14, %xmm6
	vprolq	$44, %xmm6, %xmm6
	vmovdqa64	%xmm1, %xmm23
	vprolq	$18, %xmm27, %xmm27
	vpternlogq	$150, %xmm26, %xmm18, %xmm23
	vprolq	$43, %xmm23, %xmm23
	vprolq	$41, %xmm4, %xmm4
	vmovdqa64	%xmm3, %xmm26
	vpternlogq	$150, %xmm19, %xmm16, %xmm26
	vmovdqa64	%xmm2, %xmm19
	vprolq	$21, %xmm26, %xmm26
	vpternlogq	$150, %xmm28, %xmm15, %xmm19
	vprolq	$14, %xmm19, %xmm28
	vmovdqa64	%xmm26, %xmm19
	vmovdqa64	%xmm28, %xmm31
	vpternlogq	$210, %xmm0, %xmm28, %xmm19
	vpternlogq	$210, %xmm6, %xmm0, %xmm31
	vpternlogq	$210, %xmm23, %xmm6, %xmm0
	vpternlogq	$210, %xmm26, %xmm23, %xmm6
	vmovdqa64	%xmm31, -40(%rsp)
	vmovdqa64	%xmm6, %xmm31
	vmovdqa	%xmm3, %xmm6
	vpternlogq	$210, %xmm28, %xmm26, %xmm23
	vpternlogq	$150, %xmm17, %xmm16, %xmm6
	vmovdqa64	%xmm1, %xmm28
	vmovdqa64	%xmm23, %xmm29
	vprolq	$28, %xmm6, %xmm17
	vmovdqa	%xmm9, %xmm6
	vpternlogq	$150, %xmm20, %xmm18, %xmm28
	vmovdqa64	%xmm2, %xmm23
	vpternlogq	$150, %xmm8, %xmm14, %xmm6
	vpternlogq	$150, %xmm22, %xmm15, %xmm23
	vmovdqa64	%xmm3, %xmm26
	vprolq	$61, %xmm28, %xmm8
	vpternlogq	$150, %xmm25, %xmm16, %xmm26
	vprolq	$45, %xmm6, %xmm6
	vprolq	$20, %xmm23, %xmm23
	vprolq	$25, %xmm26, %xmm26
	vmovdqa64	%xmm8, %xmm22
	vmovdqa64	%xmm6, %xmm20
	vpternlogq	$210, %xmm23, %xmm17, %xmm22
	vpternlogq	$210, %xmm17, %xmm8, %xmm20
	vpternlogq	$210, %xmm5, %xmm23, %xmm17
	vpternlogq	$210, %xmm6, %xmm5, %xmm23
	vpternlogq	$210, %xmm8, %xmm6, %xmm5
	vmovdqa	%xmm9, %xmm6
	vmovdqa64	%xmm20, -24(%rsp)
	vpternlogq	$150, %xmm30, %xmm14, %xmm6
	vmovdqa64	%xmm1, %xmm30
	vpxorq	-8(%rsp), %xmm13, %xmm8
	vprolq	$1, %xmm6, %xmm6
	vpternlogq	$150, %xmm7, %xmm18, %xmm30
	vmovdqa	%xmm2, %xmm7
	vprolq	$6, %xmm30, %xmm20
	vpternlogq	$150, %xmm12, %xmm15, %xmm7
	vmovdqa64	%xmm27, %xmm30
	vmovdqa	%xmm9, %xmm12
	vprolq	$8, %xmm7, %xmm7
	vpternlogq	$150, %xmm11, %xmm14, %xmm12
	vpternlogq	$150, -104(%rsp), %xmm14, %xmm9
	vprolq	$36, %xmm8, %xmm8
	vprolq	$10, %xmm12, %xmm12
	vprolq	$2, %xmm9, %xmm9
	vpternlogq	$210, %xmm20, %xmm6, %xmm30
	vmovdqa64	%xmm7, %xmm25
	vpternlogq	$210, %xmm6, %xmm27, %xmm25
	vpternlogq	$210, %xmm26, %xmm20, %xmm6
	vpternlogq	$210, %xmm7, %xmm26, %xmm20
	vpternlogq	$210, %xmm27, %xmm7, %xmm26
	vmovdqa64	%xmm1, %xmm27
	vmovdqa	%xmm2, %xmm7
	vpternlogq	$150, %xmm10, %xmm18, %xmm27
	vmovdqa	%xmm3, %xmm10
	vpternlogq	$150, -88(%rsp), %xmm15, %xmm7
	vprolq	$15, %xmm27, %xmm27
	vpternlogq	$150, %xmm24, %xmm16, %xmm10
	vpternlogq	$150, -72(%rsp), %xmm18, %xmm1
	vpternlogq	$150, -120(%rsp), %xmm16, %xmm3
	vprolq	$56, %xmm10, %xmm24
	vpternlogq	$150, %xmm21, %xmm15, %xmm2
	vmovdqa64	%xmm9, %xmm18
	vmovdqa64	%xmm20, %xmm21
	vprolq	$27, %xmm7, %xmm7
	vmovdqa64	%xmm26, %xmm16
	vmovdqa64	%xmm25, %xmm15
	vmovdqa64	%xmm30, -120(%rsp)
	vprolq	$39, %xmm2, %xmm28
	vpxorq	%xmm6, %xmm17, %xmm2
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm27, %xmm10
	vpternlogq	$210, %xmm7, %xmm24, %xmm10
	vmovdqa	%xmm10, %xmm11
	vmovdqa64	%xmm24, %xmm10
	vpternlogq	$210, %xmm8, %xmm7, %xmm10
	vpternlogq	$210, %xmm12, %xmm8, %xmm7
	vpternlogq	$210, %xmm27, %xmm12, %xmm8
	vpternlogq	$210, %xmm24, %xmm27, %xmm12
	vmovdqa64	%xmm4, %xmm24
	vmovdqa	%xmm7, %xmm14
	vprolq	$62, %xmm1, %xmm27
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm27, %xmm9, %xmm24
	vpternlogq	$210, %xmm3, %xmm27, %xmm18
	vpternlogq	$210, %xmm28, %xmm3, %xmm27
	vpternlogq	$210, %xmm4, %xmm28, %xmm3
	vpternlogq	$210, %xmm9, %xmm4, %xmm28
	vmovdqa64	%xmm23, %xmm9
	vpternlogq	$150, %xmm3, %xmm31, %xmm9
	vpbroadcastq	%rax, %xmm4
	vmovdqa	%xmm3, -104(%rsp)
	vmovdqa64	%xmm30, %xmm3
	vpternlogq	$150, %xmm9, %xmm8, %xmm21
	vmovdqa	%xmm5, %xmm9
	vpternlogq	$150, %xmm2, %xmm4, %xmm1
	vmovdqa	-40(%rsp), %xmm2
	vprolq	$1, %xmm21, %xmm13
	vpternlogq	$150, %xmm28, %xmm29, %xmm9
	vpternlogq	$150, %xmm1, %xmm27, %xmm14
	vmovdqa	-24(%rsp), %xmm1
	movabsq	$-9223372034707292150, %rax
	vpternlogq	$150, %xmm9, %xmm12, %xmm16
	vmovdqa64	%xmm22, %xmm9
	vpternlogq	$150, %xmm18, %xmm2, %xmm9
	vpternlogq	$150, %xmm24, %xmm19, %xmm1
	vprolq	$1, %xmm14, %xmm2
	vpternlogq	$150, %xmm9, %xmm10, %xmm3
	vpternlogq	$150, %xmm1, %xmm11, %xmm15
	vprolq	$1, %xmm16, %xmm9
	vprolq	$1, %xmm15, %xmm1
	vpxorq	%xmm3, %xmm13, %xmm13
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm13, %xmm4, %xmm0
	vpxorq	%xmm13, %xmm6, %xmm6
	vpxorq	%xmm13, %xmm27, %xmm27
	vprolq	$0, %xmm0, %xmm0
	vpxorq	%xmm13, %xmm7, %xmm7
	vprolq	$3, %xmm6, %xmm6
	vprolq	$18, %xmm27, %xmm27
	vmovdqa	%xmm9, %xmm4
	vprolq	$41, %xmm7, %xmm7
	vpternlogq	$150, %xmm23, %xmm14, %xmm4
	vprolq	$44, %xmm4, %xmm23
	vmovdqa	%xmm1, %xmm4
	vpternlogq	$150, %xmm26, %xmm21, %xmm4
	vmovdqa64	%xmm3, %xmm26
	vprolq	$43, %xmm4, %xmm4
	vpternlogq	$150, %xmm11, %xmm16, %xmm26
	vprolq	$21, %xmm26, %xmm11
	vmovdqa64	%xmm2, %xmm26
	vpternlogq	$150, %xmm18, %xmm15, %xmm26
	vprolq	$14, %xmm26, %xmm26
	vmovdqa64	%xmm11, %xmm18
	vmovdqa64	%xmm26, %xmm30
	vpternlogq	$210, %xmm0, %xmm26, %xmm18
	vpternlogq	$210, %xmm23, %xmm0, %xmm30
	vpternlogq	$210, %xmm4, %xmm23, %xmm0
	vpternlogq	$210, %xmm11, %xmm4, %xmm23
	vmovdqa64	%xmm18, -88(%rsp)
	vpternlogq	$210, %xmm26, %xmm11, %xmm4
	vmovdqa64	%xmm30, -72(%rsp)
	vmovdqa64	%xmm3, %xmm18
	vmovdqa64	%xmm3, %xmm26
	vmovdqa64	%xmm23, -8(%rsp)
	vpternlogq	$150, %xmm19, %xmm16, %xmm18
	vmovdqa64	%xmm2, %xmm19
	vpternlogq	$150, %xmm25, %xmm16, %xmm26
	vprolq	$28, %xmm18, %xmm11
	vmovdqa	%xmm4, 8(%rsp)
	vmovdqa	%xmm9, %xmm4
	vpternlogq	$150, %xmm22, %xmm15, %xmm19
	vprolq	$20, %xmm19, %xmm23
	vpternlogq	$150, %xmm8, %xmm14, %xmm4
	vmovdqa	%xmm1, %xmm8
	vprolq	$45, %xmm4, %xmm4
	vpternlogq	$150, %xmm28, %xmm21, %xmm8
	vprolq	$61, %xmm8, %xmm8
	vprolq	$25, %xmm26, %xmm26
	vmovdqa64	%xmm11, %xmm28
	vpternlogq	$210, %xmm6, %xmm23, %xmm28
	vmovdqa64	%xmm4, %xmm19
	vmovdqa64	%xmm8, %xmm22
	vpternlogq	$210, %xmm11, %xmm8, %xmm19
	vpternlogq	$210, %xmm23, %xmm11, %xmm22
	vpternlogq	$210, %xmm4, %xmm6, %xmm23
	vpternlogq	$210, %xmm8, %xmm4, %xmm6
	vmovdqa	%xmm1, %xmm8
	vmovdqa	%xmm9, %xmm4
	vmovdqa64	%xmm19, %xmm30
	vpternlogq	$150, %xmm5, %xmm21, %xmm8
	vmovdqa	%xmm2, %xmm5
	vpternlogq	$150, %xmm31, %xmm14, %xmm4
	vprolq	$6, %xmm8, %xmm11
	vpternlogq	$150, %xmm10, %xmm15, %xmm5
	vmovdqa64	%xmm27, %xmm19
	vmovdqa	%xmm9, %xmm10
	vprolq	$8, %xmm5, %xmm5
	vpternlogq	$150, %xmm20, %xmm14, %xmm10
	vmovdqa64	%xmm1, %xmm20
	vpternlogq	$150, -104(%rsp), %xmm14, %xmm9
	vprolq	$1, %xmm4, %xmm4
	vpternlogq	$150, %xmm12, %xmm21, %xmm20
	vpxorq	%xmm13, %xmm17, %xmm8
	vpternlogq	$150, %xmm29, %xmm21, %xmm1
	vprolq	$15, %xmm20, %xmm12
	vpbroadcastq	%rax, %xmm14
	vprolq	$2, %xmm9, %xmm9
	vprolq	$36, %xmm8, %xmm8
	vprolq	$10, %xmm10, %xmm10
	vprolq	$62, %xmm1, %xmm29
	vmovdqa64	%xmm5, %xmm25
	vmovdqa	%xmm0, %xmm1
	vpternlogq	$210, %xmm4, %xmm27, %xmm25
	vpternlogq	$210, %xmm11, %xmm4, %xmm19
	vpternlogq	$210, %xmm26, %xmm11, %xmm4
	vpternlogq	$210, %xmm5, %xmm26, %xmm11
	vpternlogq	$210, %xmm27, %xmm5, %xmm26
	vmovdqa64	%xmm3, %xmm27
	vpternlogq	$150, %xmm24, %xmm16, %xmm27
	vmovdqa	%xmm2, %xmm5
	vpternlogq	$150, -24(%rsp), %xmm16, %xmm3
	vprolq	$56, %xmm27, %xmm27
	vpternlogq	$150, -40(%rsp), %xmm15, %xmm5
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm2
	vmovdqa64	%xmm12, %xmm24
	vprolq	$55, %xmm3, %xmm3
	vmovdqa64	%xmm9, %xmm21
	vmovdqa64	%xmm11, %xmm17
	vmovdqa64	%xmm26, %xmm16
	vprolq	$27, %xmm5, %xmm5
	vmovdqa64	%xmm25, %xmm15
	vprolq	$39, %xmm2, %xmm2
	vmovdqa64	%xmm27, %xmm20
	vmovdqa64	%xmm3, %xmm31
	vpternlogq	$210, %xmm3, %xmm29, %xmm21
	vpternlogq	$210, %xmm5, %xmm27, %xmm24
	vpternlogq	$210, %xmm8, %xmm5, %xmm20
	vpternlogq	$210, %xmm10, %xmm8, %xmm5
	vpternlogq	$210, %xmm12, %xmm10, %xmm8
	vpternlogq	$210, %xmm27, %xmm12, %xmm10
	vmovdqa64	%xmm7, %xmm27
	vpternlogq	$210, %xmm29, %xmm9, %xmm27
	vpternlogq	$210, %xmm7, %xmm2, %xmm31
	vpternlogq	$210, %xmm2, %xmm3, %xmm29
	vmovdqa	8(%rsp), %xmm3
	vmovdqa	%xmm2, %xmm13
	vpxorq	%xmm4, %xmm28, %xmm2
	vpternlogq	$150, %xmm2, %xmm14, %xmm1
	vmovdqa	-8(%rsp), %xmm2
	vmovdqa	%xmm5, %xmm14
	vpternlogq	$210, %xmm9, %xmm7, %xmm13
	vpternlogq	$150, %xmm1, %xmm29, %xmm14
	vmovdqa64	%xmm23, %xmm1
	vmovdqa	-72(%rsp), %xmm7
	vpbroadcastq	%rax, %xmm9
	vpternlogq	$150, %xmm31, %xmm2, %xmm1
	vmovdqa	-88(%rsp), %xmm2
	vpternlogq	$150, %xmm1, %xmm8, %xmm17
	vmovdqa	%xmm6, %xmm1
	vprolq	$1, %xmm17, %xmm12
	vpternlogq	$150, %xmm13, %xmm3, %xmm1
	vmovdqa64	%xmm19, %xmm3
	vpternlogq	$150, %xmm1, %xmm10, %xmm16
	vmovdqa64	%xmm30, %xmm1
	vpternlogq	$150, %xmm27, %xmm2, %xmm1
	vprolq	$1, %xmm14, %xmm2
	vpternlogq	$150, %xmm1, %xmm24, %xmm15
	vmovdqa64	%xmm22, %xmm1
	vpternlogq	$150, %xmm21, %xmm7, %xmm1
	vprolq	$1, %xmm16, %xmm7
	vpternlogq	$150, %xmm1, %xmm20, %xmm3
	vprolq	$1, %xmm15, %xmm1
	vpxorq	%xmm3, %xmm12, %xmm12
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm12, %xmm9, %xmm0
	vpxorq	%xmm12, %xmm4, %xmm4
	vpxorq	%xmm12, %xmm29, %xmm29
	vprolq	$0, %xmm0, %xmm0
	vpxorq	%xmm12, %xmm5, %xmm5
	vprolq	$3, %xmm4, %xmm4
	vprolq	$18, %xmm29, %xmm29
	vprolq	$41, %xmm5, %xmm5
	vmovdqa	%xmm7, %xmm9
	vpternlogq	$150, %xmm23, %xmm14, %xmm9
	vmovdqa64	%xmm1, %xmm23
	vprolq	$44, %xmm9, %xmm9
	vpternlogq	$150, %xmm26, %xmm17, %xmm23
	vmovdqa64	%xmm3, %xmm26
	vprolq	$43, %xmm23, %xmm23
	vpternlogq	$150, %xmm24, %xmm16, %xmm26
	vprolq	$21, %xmm26, %xmm24
	vmovdqa64	%xmm2, %xmm26
	vpternlogq	$150, %xmm21, %xmm15, %xmm26
	vprolq	$14, %xmm26, %xmm26
	vmovdqa64	%xmm24, %xmm21
	vmovdqa64	%xmm26, %xmm18
	vpternlogq	$210, %xmm0, %xmm26, %xmm21
	vpternlogq	$210, %xmm9, %xmm0, %xmm18
	vpternlogq	$210, %xmm23, %xmm9, %xmm0
	vpternlogq	$210, %xmm24, %xmm23, %xmm9
	vpternlogq	$210, %xmm26, %xmm24, %xmm23
	vmovdqa64	%xmm2, %xmm24
	vmovdqa	%xmm9, -104(%rsp)
	vmovdqa	%xmm3, %xmm9
	vpternlogq	$150, %xmm22, %xmm15, %xmm24
	vpternlogq	$150, -88(%rsp), %xmm16, %xmm9
	vmovdqa64	%xmm18, -120(%rsp)
	vmovdqa64	%xmm1, %xmm26
	vprolq	$20, %xmm24, %xmm22
	vmovdqa64	%xmm7, %xmm24
	vmovdqa64	%xmm23, -40(%rsp)
	vpternlogq	$150, %xmm10, %xmm17, %xmm26
	vprolq	$28, %xmm9, %xmm9
	vpternlogq	$150, %xmm8, %xmm14, %xmm24
	vmovdqa	%xmm3, %xmm10
	vprolq	$45, %xmm24, %xmm8
	vmovdqa64	%xmm1, %xmm24
	vpternlogq	$150, %xmm27, %xmm16, %xmm10
	vprolq	$15, %xmm26, %xmm26
	vpternlogq	$150, %xmm13, %xmm17, %xmm24
	vprolq	$61, %xmm24, %xmm13
	vprolq	$56, %xmm10, %xmm27
	vmovdqa64	%xmm8, %xmm18
	vmovdqa64	%xmm26, %xmm10
	vmovdqa64	%xmm13, %xmm24
	vpternlogq	$210, %xmm9, %xmm13, %xmm18
	vpternlogq	$210, %xmm22, %xmm9, %xmm24
	vpternlogq	$210, %xmm4, %xmm22, %xmm9
	vpternlogq	$210, %xmm8, %xmm4, %xmm22
	vmovdqa64	%xmm18, -88(%rsp)
	vpternlogq	$210, %xmm13, %xmm8, %xmm4
	vmovdqa	%xmm1, %xmm13
	vmovdqa64	%xmm24, %xmm23
	vmovdqa	%xmm9, -24(%rsp)
	vpternlogq	$150, %xmm6, %xmm17, %xmm13
	vmovdqa	%xmm3, %xmm6
	vmovdqa64	%xmm7, %xmm24
	vprolq	$6, %xmm13, %xmm13
	vpternlogq	$150, %xmm25, %xmm16, %xmm6
	vpternlogq	$150, -8(%rsp), %xmm14, %xmm24
	vpxorq	%xmm12, %xmm28, %xmm8
	vprolq	$25, %xmm6, %xmm25
	vmovdqa	%xmm2, %xmm6
	vpternlogq	$150, 8(%rsp), %xmm17, %xmm1
	vpternlogq	$150, %xmm30, %xmm16, %xmm3
	vprolq	$1, %xmm24, %xmm9
	vpternlogq	$150, %xmm20, %xmm15, %xmm6
	vmovdqa64	%xmm29, %xmm24
	vpbroadcastq	%rcx, %xmm12
	vprolq	$8, %xmm6, %xmm6
	vprolq	$36, %xmm8, %xmm8
	vprolq	$62, %xmm1, %xmm28
	vmovdqa	%xmm0, %xmm1
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm13, %xmm9, %xmm24
	vmovdqa64	%xmm6, %xmm20
	vmovdqa64	%xmm24, %xmm18
	vmovdqa64	%xmm7, %xmm24
	vpternlogq	$210, %xmm9, %xmm29, %xmm20
	vpternlogq	$210, %xmm25, %xmm13, %xmm9
	vpternlogq	$210, %xmm6, %xmm25, %xmm13
	vpternlogq	$210, %xmm29, %xmm6, %xmm25
	vmovdqa	%xmm2, %xmm6
	vpternlogq	$150, %xmm11, %xmm14, %xmm24
	vprolq	$10, %xmm24, %xmm24
	vpternlogq	$150, -72(%rsp), %xmm15, %xmm6
	vpternlogq	$150, %xmm31, %xmm14, %xmm7
	vpternlogq	$150, %xmm19, %xmm15, %xmm2
	vprolq	$27, %xmm6, %xmm6
	vmovdqa64	%xmm3, %xmm29
	vmovdqa64	%xmm25, %xmm19
	vmovdqa64	%xmm20, %xmm17
	vprolq	$2, %xmm7, %xmm7
	vprolq	$39, %xmm2, %xmm2
	vpternlogq	$210, %xmm6, %xmm27, %xmm10
	vmovdqa	%xmm10, %xmm11
	vmovdqa64	%xmm27, %xmm10
	vmovdqa64	%xmm7, %xmm16
	vpternlogq	$210, %xmm8, %xmm6, %xmm10
	vpternlogq	$210, %xmm24, %xmm8, %xmm6
	vpternlogq	$210, %xmm26, %xmm24, %xmm8
	vpternlogq	$210, %xmm27, %xmm26, %xmm24
	vmovdqa64	%xmm5, %xmm27
	vpternlogq	$210, %xmm3, %xmm28, %xmm16
	vpternlogq	$210, %xmm28, %xmm7, %xmm27
	vpternlogq	$210, %xmm2, %xmm3, %xmm28
	vpxorq	-24(%rsp), %xmm9, %xmm3
	vpternlogq	$210, %xmm5, %xmm2, %xmm29
	vmovdqa	%xmm6, %xmm15
	vpternlogq	$210, %xmm7, %xmm5, %xmm2
	vmovdqa	-104(%rsp), %xmm5
	vpternlogq	$150, %xmm3, %xmm12, %xmm1
	vmovdqa64	%xmm13, %xmm26
	vmovdqa	-40(%rsp), %xmm3
	vmovdqa	-120(%rsp), %xmm7
	vpternlogq	$150, %xmm1, %xmm28, %xmm15
	vmovdqa64	%xmm22, %xmm1
	vpternlogq	$150, %xmm29, %xmm5, %xmm1
	vprolq	$1, %xmm15, %xmm5
	vpternlogq	$150, %xmm1, %xmm8, %xmm26
	vmovdqa	%xmm4, %xmm1
	vprolq	$1, %xmm26, %xmm14
	vpternlogq	$150, %xmm2, %xmm3, %xmm1
	vmovdqa64	%xmm18, %xmm3
	vpternlogq	$150, %xmm1, %xmm24, %xmm19
	vmovdqa	-88(%rsp), %xmm1
	vpternlogq	$150, %xmm27, %xmm21, %xmm1
	vpternlogq	$150, %xmm1, %xmm11, %xmm17
	vmovdqa64	%xmm23, %xmm1
	vpternlogq	$150, %xmm16, %xmm7, %xmm1
	vprolq	$1, %xmm19, %xmm7
	vpternlogq	$150, %xmm1, %xmm10, %xmm3
	vprolq	$1, %xmm17, %xmm1
	vpxorq	%xmm3, %xmm14, %xmm14
	vprolq	$1, %xmm3, %xmm3
	vpternlogq	$150, %xmm14, %xmm12, %xmm0
	vpxorq	%xmm14, %xmm9, %xmm9
	vpxorq	%xmm14, %xmm28, %xmm28
	vprolq	$0, %xmm0, %xmm0
	vpxorq	%xmm14, %xmm6, %xmm6
	vprolq	$3, %xmm9, %xmm9
	vprolq	$18, %xmm28, %xmm28
	vprolq	$41, %xmm6, %xmm6
	vmovdqa	%xmm7, %xmm12
	vmovdqa64	%xmm1, %xmm31
	vpternlogq	$150, %xmm22, %xmm15, %xmm12
	vprolq	$44, %xmm12, %xmm12
	vpternlogq	$150, %xmm25, %xmm26, %xmm31
	vmovdqa64	%xmm3, %xmm25
	vprolq	$43, %xmm31, %xmm22
	vpternlogq	$150, %xmm11, %xmm19, %xmm25
	vprolq	$21, %xmm25, %xmm11
	vmovdqa64	%xmm5, %xmm25
	vpternlogq	$150, %xmm16, %xmm17, %xmm25
	vprolq	$14, %xmm25, %xmm25
	vmovdqa64	%xmm11, %xmm16
	vmovdqa64	%xmm25, %xmm31
	vpternlogq	$210, %xmm0, %xmm25, %xmm16
	vpternlogq	$210, %xmm12, %xmm0, %xmm31
	vpternlogq	$210, %xmm22, %xmm12, %xmm0
	vpternlogq	$210, %xmm11, %xmm22, %xmm12
	vmovdqa64	%xmm12, %xmm30
	vmovdqa64	%xmm22, %xmm12
	vmovdqa64	%xmm1, %xmm22
	vpternlogq	$210, %xmm25, %xmm11, %xmm12
	vmovdqa64	%xmm3, %xmm25
	vpternlogq	$150, %xmm4, %xmm26, %xmm22
	vpternlogq	$150, %xmm21, %xmm19, %xmm25
	vmovdqa64	%xmm7, %xmm21
	vmovdqa	%xmm12, -72(%rsp)
	vmovdqa	%xmm5, %xmm12
	vprolq	$28, %xmm25, %xmm11
	vpternlogq	$150, %xmm8, %xmm15, %xmm21
	vpternlogq	$150, %xmm23, %xmm17, %xmm12
	vmovdqa	%xmm5, %xmm4
	vprolq	$45, %xmm21, %xmm8
	vmovdqa64	%xmm1, %xmm21
	vpternlogq	$150, %xmm10, %xmm17, %xmm4
	vmovdqa64	%xmm28, %xmm10
	vprolq	$20, %xmm12, %xmm12
	vpternlogq	$150, %xmm2, %xmm26, %xmm21
	vprolq	$61, %xmm21, %xmm2
	vprolq	$8, %xmm4, %xmm4
	vmovdqa64	%xmm11, %xmm25
	vmovdqa64	%xmm8, %xmm21
	vpternlogq	$210, %xmm9, %xmm12, %xmm25
	vpternlogq	$210, %xmm11, %xmm2, %xmm21
	vmovdqa64	%xmm25, 8(%rsp)
	vmovdqa64	%xmm21, -8(%rsp)
	vmovdqa64	%xmm2, %xmm21
	vpternlogq	$210, %xmm12, %xmm11, %xmm21
	vpternlogq	$210, %xmm8, %xmm9, %xmm12
	vpternlogq	$210, %xmm2, %xmm8, %xmm9
	vprolq	$6, %xmm22, %xmm11
	vmovdqa	%xmm7, %xmm2
	vmovdqa64	%xmm3, %xmm22
	vmovdqa	%xmm7, %xmm8
	vpternlogq	$150, -104(%rsp), %xmm15, %xmm2
	vpternlogq	$150, %xmm20, %xmm19, %xmm22
	vpternlogq	$150, %xmm13, %xmm15, %xmm8
	vprolq	$1, %xmm2, %xmm2
	vmovdqa64	%xmm4, %xmm20
	vpternlogq	$150, %xmm29, %xmm15, %xmm7
	vprolq	$25, %xmm22, %xmm22
	vprolq	$10, %xmm8, %xmm13
	vmovdqa	%xmm1, %xmm8
	vpternlogq	$150, -40(%rsp), %xmm26, %xmm1
	vprolq	$2, %xmm7, %xmm7
	vpternlogq	$150, %xmm24, %xmm26, %xmm8
	vmovdqa64	%xmm3, %xmm24
	vpternlogq	$150, -88(%rsp), %xmm19, %xmm3
	vprolq	$15, %xmm8, %xmm8
	vpternlogq	$150, %xmm27, %xmm19, %xmm24
	vmovdqa64	.LC26(%rip), %xmm27
	vprolq	$56, %xmm24, %xmm25
	vprolq	$62, %xmm1, %xmm1
	vpternlogq	$210, %xmm11, %xmm2, %xmm10
	vpternlogq	$210, %xmm2, %xmm28, %xmm20
	vprolq	$55, %xmm3, %xmm3
	vpternlogq	$210, %xmm22, %xmm11, %xmm2
	vmovdqa	%xmm10, -104(%rsp)
	vpternlogq	$210, %xmm4, %xmm22, %xmm11
	vpxorq	-24(%rsp), %xmm14, %xmm10
	vpternlogq	$210, %xmm28, %xmm4, %xmm22
	vmovdqa	%xmm5, %xmm4
	vpternlogq	$150, -120(%rsp), %xmm17, %xmm4
	vpternlogq	$150, %xmm18, %xmm17, %xmm5
	vmovdqa64	%xmm7, %xmm26
	vprolq	$27, %xmm4, %xmm4
	vmovdqa64	%xmm8, %xmm24
	vmovdqa64	%xmm11, %xmm19
	vmovdqa64	%xmm22, %xmm18
	vprolq	$36, %xmm10, %xmm10
	vmovdqa64	%xmm25, %xmm23
	vmovdqa64	%xmm20, %xmm17
	vprolq	$39, %xmm5, %xmm5
	vpternlogq	$210, %xmm3, %xmm1, %xmm26
	vpternlogq	$210, %xmm4, %xmm25, %xmm24
	vpternlogq	$210, %xmm10, %xmm4, %xmm23
	vpternlogq	$210, %xmm13, %xmm10, %xmm4
	vpternlogq	$210, %xmm8, %xmm13, %xmm10
	vpternlogq	$210, %xmm25, %xmm8, %xmm13
	vmovdqa	%xmm6, %xmm8
	vmovdqa	%xmm4, %xmm15
	vpternlogq	$210, %xmm1, %xmm7, %xmm8
	vpternlogq	$210, %xmm5, %xmm3, %xmm1
	vmovdqa64	%xmm8, %xmm25
	vmovdqa	%xmm3, %xmm8
	vmovdqa	%xmm0, %xmm3
	vpternlogq	$210, %xmm6, %xmm5, %xmm8
	vpternlogq	$210, %xmm7, %xmm6, %xmm5
	vpxorq	8(%rsp), %xmm2, %xmm6
	vmovdqa	-104(%rsp), %xmm7
	vmovdqa	%xmm8, -120(%rsp)
	vpternlogq	$150, %xmm6, %xmm27, %xmm3
	vmovdqa	-72(%rsp), %xmm6
	vpternlogq	$150, %xmm3, %xmm1, %xmm15
	vmovdqa	%xmm12, %xmm3
	vpternlogq	$150, %xmm8, %xmm30, %xmm3
	vpternlogq	$150, %xmm3, %xmm10, %xmm19
	vmovdqa	%xmm9, %xmm3
	vprolq	$1, %xmm19, %xmm14
	vpternlogq	$150, %xmm5, %xmm6, %xmm3
	vmovdqa64	%xmm21, %xmm6
	vpternlogq	$150, %xmm3, %xmm13, %xmm18
	vmovdqa	-8(%rsp), %xmm3
	vpternlogq	$150, %xmm26, %xmm31, %xmm6
	vprolq	$1, %xmm18, %xmm8
	vpternlogq	$150, %xmm6, %xmm23, %xmm7
	vprolq	$1, %xmm15, %xmm6
	vpternlogq	$150, %xmm25, %xmm16, %xmm3
	vpternlogq	$150, %xmm3, %xmm24, %xmm17
	vprolq	$1, %xmm7, %xmm3
	vpxorq	%xmm7, %xmm14, %xmm14
	vprolq	$1, %xmm17, %xmm7
	vpternlogq	$150, %xmm14, %xmm27, %xmm0
	vpxorq	%xmm14, %xmm2, %xmm2
	vpxorq	%xmm14, %xmm1, %xmm1
	vprolq	$0, %xmm0, %xmm0
	vmovdqa64	%xmm8, %xmm27
	vpxorq	%xmm14, %xmm4, %xmm4
	vprolq	$3, %xmm2, %xmm2
	vpternlogq	$150, %xmm12, %xmm15, %xmm27
	vmovdqa64	%xmm6, %xmm28
	vprolq	$44, %xmm27, %xmm12
	vpternlogq	$150, %xmm26, %xmm17, %xmm28
	vprolq	$14, %xmm28, %xmm28
	vmovdqa64	%xmm3, %xmm29
	vprolq	$18, %xmm1, %xmm1
	vpternlogq	$150, %xmm16, %xmm18, %xmm29
	vmovdqa64	%xmm6, %xmm16
	vprolq	$28, %xmm29, %xmm29
	vmovdqa64	%xmm7, %xmm27
	vpternlogq	$150, %xmm21, %xmm17, %xmm16
	vprolq	$20, %xmm16, %xmm16
	vpternlogq	$150, %xmm22, %xmm19, %xmm27
	vprolq	$43, %xmm27, %xmm22
	vmovdqa64	%xmm3, %xmm27
	vprolq	$41, %xmm4, %xmm4
	vpternlogq	$150, %xmm24, %xmm18, %xmm27
	vprolq	$21, %xmm27, %xmm27
	vmovdqa64	%xmm28, %xmm24
	vpternlogq	$210, %xmm12, %xmm0, %xmm24
	vmovdqa64	%xmm27, %xmm26
	vpternlogq	$210, %xmm0, %xmm28, %xmm26
	vpternlogq	$210, %xmm22, %xmm12, %xmm0
	vpternlogq	$210, %xmm27, %xmm22, %xmm12
	vpternlogq	$210, %xmm28, %xmm27, %xmm22
	vmovdqa64	%xmm8, %xmm28
	vpternlogq	$150, %xmm10, %xmm15, %xmm28
	vmovdqa	%xmm7, %xmm10
	vprolq	$45, %xmm28, %xmm28
	vpternlogq	$150, %xmm5, %xmm19, %xmm10
	vprolq	$61, %xmm10, %xmm5
	vmovdqa64	%xmm29, %xmm10
	vpternlogq	$210, %xmm2, %xmm16, %xmm10
	vmovdqa64	%xmm28, %xmm27
	vmovdqa64	%xmm5, %xmm21
	vpternlogq	$210, %xmm29, %xmm5, %xmm27
	vpternlogq	$210, %xmm16, %xmm29, %xmm21
	vpternlogq	$210, %xmm28, %xmm2, %xmm16
	vpternlogq	$210, %xmm5, %xmm28, %xmm2
	vmovdqa	%xmm7, %xmm5
	vmovdqa64	%xmm8, %xmm28
	vmovdqa64	%xmm1, %xmm29
	vpternlogq	$150, %xmm9, %xmm19, %xmm5
	vmovdqa	%xmm3, %xmm9
	vpternlogq	$150, %xmm30, %xmm15, %xmm28
	vprolq	$1, %xmm28, %xmm28
	vpternlogq	$150, %xmm20, %xmm18, %xmm9
	vmovdqa64	%xmm6, %xmm20
	vprolq	$6, %xmm5, %xmm5
	vpternlogq	$150, %xmm23, %xmm17, %xmm20
	vprolq	$8, %xmm20, %xmm20
	vprolq	$25, %xmm9, %xmm9
	vpternlogq	$210, %xmm5, %xmm28, %xmm29
	vmovdqa64	%xmm20, %xmm23
	vpternlogq	$210, %xmm28, %xmm1, %xmm23
	vpternlogq	$210, %xmm9, %xmm5, %xmm28
	vpternlogq	$210, %xmm20, %xmm9, %xmm5
	vpternlogq	$210, %xmm1, %xmm20, %xmm9
	vmovdqa	%xmm8, %xmm1
	vpxorq	8(%rsp), %xmm14, %xmm20
	vmovdqa64	%xmm9, %xmm30
	vmovdqa	%xmm6, %xmm9
	vpternlogq	$150, %xmm11, %xmm15, %xmm1
	vprolq	$36, %xmm20, %xmm20
	vpternlogq	$150, %xmm31, %xmm17, %xmm9
	vmovdqa64	%xmm7, %xmm31
	vpternlogq	$150, -120(%rsp), %xmm15, %xmm8
	vprolq	$27, %xmm9, %xmm9
	vpternlogq	$150, %xmm13, %xmm19, %xmm31
	vpxorq	%xmm28, %xmm10, %xmm10
	vpternlogq	$150, -72(%rsp), %xmm19, %xmm7
	vprolq	$15, %xmm31, %xmm11
	vmovdqa64	%xmm3, %xmm31
	vpternlogq	$150, -104(%rsp), %xmm17, %xmm6
	vpternlogq	$150, -8(%rsp), %xmm18, %xmm3
	vprolq	$10, %xmm1, %xmm1
	vpternlogq	$150, %xmm25, %xmm18, %xmm31
	vmovdqa	-56(%rsp), %xmm15
	vprolq	$56, %xmm31, %xmm13
	vprolq	$2, %xmm8, %xmm8
	vprolq	$62, %xmm7, %xmm7
	vprolq	$55, %xmm3, %xmm3
	vprolq	$39, %xmm6, %xmm6
	vmovdqa64	%xmm11, %xmm25
	vmovdqa64	%xmm13, %xmm31
	vpternlogq	$210, %xmm9, %xmm13, %xmm25
	vpternlogq	$210, %xmm20, %xmm9, %xmm31
	vmovdqa	%xmm8, %xmm14
	vpternlogq	$210, %xmm1, %xmm20, %xmm9
	vpternlogq	$210, %xmm11, %xmm1, %xmm20
	vpternlogq	$210, %xmm13, %xmm11, %xmm1
	vmovdqa	%xmm4, %xmm13
	vpternlogq	$210, %xmm3, %xmm7, %xmm14
	vpternlogq	$210, %xmm7, %xmm8, %xmm13
	vpternlogq	$210, %xmm6, %xmm3, %xmm7
	vpternlogq	$210, %xmm4, %xmm6, %xmm3
	vpternlogq	$150, %xmm14, %xmm24, %xmm21
	vpternlogq	$210, %xmm8, %xmm4, %xmm6
	vpternlogq	$150, %xmm3, %xmm16, %xmm12
	vmovdqa	%xmm0, %xmm4
	vpternlogq	$150, %xmm12, %xmm20, %xmm5
	vpternlogq	$150, %xmm6, %xmm22, %xmm2
	vpternlogq	$150, %xmm10, %xmm15, %xmm4
	vpternlogq	$150, %xmm21, %xmm31, %xmm29
	vpternlogq	$150, %xmm13, %xmm26, %xmm27
	vpternlogq	$150, %xmm4, %xmm7, %xmm9
	vprolq	$1, %xmm5, %xmm7
	vpternlogq	$150, %xmm2, %xmm30, %xmm1
	vpternlogq	$150, %xmm27, %xmm25, %xmm23
	vprolq	$1, %xmm29, %xmm4
	vprolq	$1, %xmm1, %xmm3
	vprolq	$1, %xmm23, %xmm2
	vprolq	$1, %xmm9, %xmm6
	vpternlogq	$150, %xmm7, %xmm15, %xmm0
	vpternlogq	$150, %xmm1, %xmm25, %xmm4
	vpxorq	%xmm29, %xmm0, %xmm0
	vprolq	$21, %xmm4, %xmm1
	vpternlogq	$150, %xmm9, %xmm16, %xmm3
	vprolq	$0, %xmm0, %xmm0
	vpternlogq	$150, %xmm5, %xmm30, %xmm2
	vprolq	$43, %xmm2, %xmm2
	vpternlogq	$150, %xmm23, %xmm14, %xmm6
	vprolq	$44, %xmm3, %xmm3
	vprolq	$14, %xmm6, %xmm4
	vmovdqa	%xmm1, %xmm5
	vpternlogq	$210, %xmm0, %xmm4, %xmm5
	vpternlogq	$210, %xmm2, %xmm3, %xmm0
	vpxorq	.LC27(%rip), %xmm0, %xmm0
	vpternlogq	$210, %xmm1, %xmm2, %xmm3
	vpternlogq	$210, %xmm4, %xmm1, %xmm2
	vmovq	%xmm5, %rsi
	vmovq	%xmm0, %rcx
	vmovq	%xmm3, %rax
	vmovq	%xmm2, %rdx
	subq	$1, %r9
	jnb	.L50
	vmovq	%xmm0, (%rdi)
	vmovq	%xmm3, 8(%rdi)
	vmovq	%xmm2, 16(%rdi)
	vmovq	%xmm5, 24(%rdi)
	addq	$48, %rsp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L57:
	ret
	.cfi_endproc
.LFE7363:
	.size	chain_words_vec, .-chain_words_vec
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC28:
	.string	"chainwalk: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB7367:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC28(%rip), %rdx
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
.LFE7367:
	.size	die, .-die
	.section	.rodata.str1.1
.LC29:
	.string	"out of memory"
	.text
	.p2align 4
	.type	app, @function
app:
.LFB7369:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %rcx
	movq	%rdx, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	movq	%rdi, %rbx
	subq	$24, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rdi), %rax
	movq	(%rdi), %rdi
	addq	%rax, %rdx
	cmpq	%rdx, 16(%rbx)
	jb	.L66
.L63:
	movq	%rbp, %rdx
	addq	%rax, %rdi
	movq	%rcx, %rsi
	call	memcpy@PLT
	addq	%rbp, 8(%rbx)
	addq	$24, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L66:
	.cfi_restore_state
	movq	%rsi, 8(%rsp)
	leaq	4096(%rdx,%rdx), %rsi
	movq	%rsi, 16(%rbx)
	call	realloc@PLT
	movq	%rax, (%rbx)
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.L64
	movq	8(%rbx), %rax
	movq	8(%rsp), %rcx
	jmp	.L63
.L64:
	leaq	.LC29(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7369:
	.size	app, .-app
	.p2align 4
	.type	app64, @function
app64:
.LFB7370:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdi, %r8
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	andq	$-32, %rsp
	subq	$32, %rsp
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdx
	.p2align 5
	.p2align 4
	.p2align 3
.L68:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L68
	movl	$8, %edx
	movq	%rsp, %rsi
	movq	%r8, %rdi
	call	app
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L73
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L73:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7370:
	.size	app64, .-app64
	.p2align 4
	.type	signed_file, @function
signed_file:
.LFB7380:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rsi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdx, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	movq	%rdi, %rbx
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rsi), %rsi
	movl	(%rdx), %r13d
	call	app64
	movq	8(%r12), %rdx
	movq	(%r12), %rsi
	movq	%rbx, %rdi
	call	app
	movq	%rbx, %rdi
	xorl	%esi, %esi
	call	app64
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	app64
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	leaq	4(%rbp), %rsi
	movq	%rbx, %rdi
	movl	$4768, %edx
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	jmp	app
	.cfi_endproc
.LFE7380:
	.size	signed_file, .-signed_file
	.p2align 4
	.type	readfile, @function
readfile:
.LFB7371:
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
	leaq	-65536(%rsp), %r11
	.cfi_def_cfa 11, 65592
.LPSRL0:
	subq	$4096, %rsp
	orq	$0, (%rsp)
	cmpq	%r11, %rsp
	jne	.LPSRL0
	.cfi_def_cfa_register 7
	subq	$88, %rsp
	.cfi_def_cfa_offset 65680
	movq	%fs:40, %rax
	movq	%rax, 65608(%rsp)
	xorl	%eax, %eax
	movq	%rsi, %r15
	movq	%rdi, %r14
	xorl	%esi, %esi
	movq	%r15, %rdi
	call	open@PLT
	testl	%eax, %eax
	js	.L79
	vpxor	%xmm2, %xmm2, %xmm2
	movl	%eax, %r12d
	leaq	64(%rsp), %rbp
	xorl	%ebx, %ebx
	vmovdqa	%xmm2, (%rsp)
	jmp	.L77
	.p2align 4,,10
	.p2align 3
.L78:
	vmovdqa	(%rsp), %xmm0
	movq	%rbp, %rsi
	leaq	32(%rsp), %rdi
	movq	%rbx, 32(%rsp)
	vmovdqu	%xmm0, 40(%rsp)
	call	app
	vmovdqu	40(%rsp), %xmm1
	movq	32(%rsp), %rbx
	vmovdqa	%xmm1, (%rsp)
.L77:
	movl	$65536, %edx
	movq	%rbp, %rsi
	movl	%r12d, %edi
	call	read@PLT
	movq	%rax, %rdx
	testq	%rax, %rax
	jg	.L78
	movl	%r12d, %edi
	movq	%rax, 24(%rsp)
	call	close@PLT
	cmpq	$0, 24(%rsp)
	jne	.L79
	vmovdqa	(%rsp), %xmm3
	movq	%rbx, (%r14)
	vmovdqu	%xmm3, 8(%r14)
	movq	65608(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L83
	addq	$65624, %rsp
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
.L79:
	.cfi_restore_state
	movq	%r15, %rdi
	call	die
.L83:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7371:
	.size	readfile, .-readfile
	.p2align 4
	.type	chain_words_c, @function
chain_words_c:
.LFB7359:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$224, %rsp
	.cfi_offset 14, -24
	.cfi_offset 13, -32
	.cfi_offset 12, -40
	.cfi_offset 3, -48
	movq	%fs:40, %rax
	movq	%rax, 216(%rsp)
	xorl	%eax, %eax
	testq	%rsi, %rsi
	je	.L84
	movq	%rdi, %rbx
	leaq	-1(%rsi), %r14
	vpxor	%xmm0, %xmm0, %xmm0
	movabsq	$-9223372036854775808, %r12
	.p2align 4
	.p2align 3
.L86:
	movq	24(%rbx), %rax
	movq	(%rbx), %rdi
	vmovdqu64	%zmm0, 104(%rsp)
	vpxor	%xmm2, %xmm2, %xmm2
	movq	8(%rbx), %rsi
	movq	16(%rbx), %rcx
	movq	%r12, 128(%rsp)
	movq	%rax, %rdx
	vmovdqu64	%zmm0, 40(%rsp)
	shrq	$56, %rdx
	shldq	$8, %rcx, %rax
	vmovdqu	%ymm2, 168(%rsp)
	xorb	$1, %dh
	movq	%rax, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	%rdi, %rdx
	salq	$8, %rdx
	xorq	$67, %rdx
	movq	%rdx, (%rsp)
	movq	%rsi, %rdx
	shldq	$8, %rdi, %rdx
	movq	%rsp, %rdi
	movq	%rdx, 8(%rsp)
	movq	%rcx, %rdx
	shldq	$8, %rsi, %rdx
	movq	%rdx, 16(%rsp)
	vzeroupper
	call	keccak_f
	subq	$1, %r14
	vmovdqa	(%rsp), %ymm1
	cmpq	$-1, %r14
	vpxor	%xmm0, %xmm0, %xmm0
	vmovdqu	%ymm1, (%rbx)
	jne	.L86
	vzeroupper
.L84:
	movq	216(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L94
	leaq	-32(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L94:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7359:
	.size	chain_words_c, .-chain_words_c
	.p2align 4
	.type	unhex.constprop.0, @function
unhex.constprop.0:
.LFB7387:
	.cfi_startproc
	movq	%rdi, %r8
	xorl	%ecx, %ecx
	jmp	.L101
	.p2align 4,,10
	.p2align 3
.L106:
	movsbl	1(%rsi,%rcx,2), %edx
	subl	$48, %eax
	leal	-48(%rdx), %edi
	cmpb	$9, %dil
	ja	.L99
.L107:
	subl	$48, %edx
.L100:
	sall	$4, %eax
	orl	%edx, %eax
	movb	%al, (%r8,%rcx)
	addq	$1, %rcx
	cmpq	$32, %rcx
	je	.L105
.L101:
	movsbl	(%rsi,%rcx,2), %eax
	leal	-48(%rax), %edx
	cmpb	$9, %dl
	jbe	.L106
	leal	-97(%rax), %edx
	cmpb	$5, %dl
	ja	.L103
	movsbl	1(%rsi,%rcx,2), %edx
	subl	$87, %eax
	leal	-48(%rdx), %edi
	cmpb	$9, %dil
	jbe	.L107
.L99:
	leal	-97(%rdx), %edi
	cmpb	$5, %dil
	ja	.L103
	subl	$87, %edx
	jmp	.L100
.L105:
	xorl	%eax, %eax
	ret
.L103:
	movl	$-1, %eax
	ret
	.cfi_endproc
.LFE7387:
	.size	unhex.constprop.0, .-unhex.constprop.0
	.section	.rodata.str1.1
.LC30:
	.string	"\"n\""
.LC31:
	.string	"\"start\""
	.text
	.p2align 4
	.type	parse_chain, @function
parse_chain:
.LFB7383:
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
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	movq	%r12, %rsi
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %r14
	movq	%r14, 24(%rsp)
	movq	%rdx, %r14
	movq	%rsp, %rdi
	call	readfile
	movq	(%rsp), %rbp
	leaq	.LC30(%rip), %rsi
	movq	%rbp, %rdi
	call	strstr@PLT
	leaq	.LC31(%rip), %rsi
	movq	%rbp, %rdi
	movq	%rax, %r15
	call	strstr@PLT
	testq	%r15, %r15
	je	.L111
	movq	%rax, %rbx
	testq	%rax, %rax
	je	.L111
	movl	$58, %esi
	movq	%r15, %rdi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L111
	xorl	%esi, %esi
	leaq	1(%rax), %rdi
	movl	$10, %edx
	call	__isoc23_strtoull@PLT
	leaq	7(%rbx), %rdi
	movl	$34, %esi
	movq	%rax, (%r14)
	call	strchr@PLT
	testq	%rax, %rax
	je	.L111
	leaq	1(%rax), %rsi
	movq	%r13, %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L111
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L120
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%rbp, %rdi
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
.L111:
	.cfi_restore_state
	movq	%r12, %rdi
	call	die
.L120:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7383:
	.size	parse_chain, .-parse_chain
	.p2align 4
	.type	leaf_stmt, @function
leaf_stmt:
.LFB7366:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %rax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%rbx
	.cfi_offset 3, -24
	movq	%rdi, %rbx
	andq	$-32, %rsp
	subq	$416, %rsp
	vmovdqu	(%rax), %ymm1
	xorl	%eax, %eax
	movq	%fs:40, %rsi
	movq	%rsi, 408(%rsp)
	movq	%rdx, %rsi
	leaq	257(%rsp), %rdx
	.p2align 5
	.p2align 4
	.p2align 3
.L122:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L122
	vpxor	%xmm0, %xmm0, %xmm0
	vmovdqu	%ymm1, 225(%rsp)
	leaq	272(%rsp), %r8
	leaq	273(%rsp), %rdx
	movb	$76, 224(%rsp)
	leaq	408(%rsp), %rdi
	vmovdqu64	%zmm0, 312(%rsp)
	vmovdqu	%ymm0, 376(%rsp)
	vmovdqu64	%zmm0, 24(%rsp)
	vmovdqu64	%zmm0, 88(%rsp)
	vmovdqu64	%zmm0, 152(%rsp)
	vmovdqa	224(%rsp), %ymm0
	movb	$1, 313(%rsp)
	vmovdqu	%ymm0, 272(%rsp)
	vmovdqu	249(%rsp), %xmm0
	movb	$-128, 407(%rsp)
	movq	$76, 16(%rsp)
	vmovdqu	%xmm0, 297(%rsp)
	.p2align 6
	.p2align 4
	.p2align 3
.L123:
	movl	%edx, %eax
	movzbl	(%rdx), %esi
	addq	$1, %rdx
	subl	%r8d, %eax
	movl	%eax, %ecx
	andl	$7, %eax
	sarl	$3, %ecx
	sall	$3, %eax
	movslq	%ecx, %rcx
	shlx	%rax, %rsi, %rax
	xorq	%rax, 16(%rsp,%rcx,8)
	cmpq	%rdx, %rdi
	jne	.L123
	leaq	16(%rsp), %rdi
	vzeroupper
	call	keccak_f
	xorl	%eax, %eax
	.p2align 6
	.p2align 4
	.p2align 3
.L124:
	movl	%eax, %edx
	movl	%eax, %ecx
	sarl	$3, %edx
	andl	$7, %ecx
	movslq	%edx, %rdx
	sall	$3, %ecx
	movq	16(%rsp,%rdx,8), %rdx
	shrx	%rcx, %rdx, %rdx
	movb	%dl, (%rbx,%rax)
	addq	$1, %rax
	cmpq	$32, %rax
	jne	.L124
	movq	408(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L131
	movq	-8(%rbp), %rbx
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L131:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7366:
	.size	leaf_stmt, .-leaf_stmt
	.section	.rodata.str1.1
.LC32:
	.string	"malformed child file"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC33:
	.string	"trailing bytes in a child file"
	.text
	.p2align 4
	.type	app_signed_words.constprop.0, @function
app_signed_words.constprop.0:
.LFB7389:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$64, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rsi
	movq	%rsi, 56(%rsp)
	movq	8(%rdi), %rsi
	cmpq	$7, %rsi
	jbe	.L135
	movq	(%rdi), %rbx
	movq	%rdi, %r13
	xorl	%r15d, %r15d
	leaq	7(%rbx), %rax
	leaq	-1(%rbx), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L134:
	movzbl	(%rax), %edx
	salq	$8, %r15
	subq	$1, %rax
	orq	%rdx, %r15
	cmpq	%rcx, %rax
	jne	.L134
	subq	$8, %rsi
	cmpq	%r15, %rsi
	jb	.L135
	leaq	32(%rsp), %rdx
	addq	$8, %rbx
	xorl	%eax, %eax
	movq	%rdx, 24(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L136:
	shrx	%rax, %r15, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L136
	movq	24(%rsp), %rsi
	movl	$8, %edx
	leaq	g_pi(%rip), %rdi
	call	app
	movq	%r15, %rdx
	movq	%rbx, %rsi
	leaq	g_pi(%rip), %rdi
	call	app
	movq	%r15, %rdx
	leaq	ZERO8(%rip), %rsi
	leaq	g_pi(%rip), %rdi
	negq	%rdx
	andl	$7, %edx
	call	app
	movq	8(%r13), %rax
	subq	$8, %rax
	subq	%r15, %rax
	cmpq	$7, %rax
	jbe	.L135
	movq	$0, 16(%rsp)
	movq	0(%r13), %rdx
	leaq	(%r15,%rdx), %rax
	leaq	-8(%r15,%rdx), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L137:
	movq	16(%rsp), %r14
	movzbl	15(%rax), %edx
	subq	$1, %rax
	salq	$8, %r14
	orq	%r14, %rdx
	movq	%rdx, 16(%rsp)
	cmpq	%rcx, %rax
	jne	.L137
	movq	%rdx, %rbx
	movq	%rdx, %rsi
	leaq	g_pi(%rip), %rdi
	addq	$16, %r15
	call	app64
	testq	%rbx, %rbx
	je	.L138
	xorl	%r12d, %r12d
	.p2align 4
	.p2align 3
.L141:
	movq	8(%r13), %rsi
	movq	%rsi, %rax
	subq	%r15, %rax
	cmpq	$7, %rax
	jbe	.L135
	movq	0(%r13), %rdi
	xorl	%ebx, %ebx
	leaq	(%rdi,%r15), %rax
	leaq	-8(%rdi,%r15), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L139:
	movzbl	7(%rax), %edx
	salq	$8, %rbx
	subq	$1, %rax
	orq	%rdx, %rbx
	cmpq	%rax, %rcx
	jne	.L139
	leaq	8(%r15), %r14
	subq	%r14, %rsi
	cmpq	%rbx, %rsi
	jb	.L135
	movq	24(%rsp), %rdx
	leaq	(%rdi,%r14), %r15
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L140:
	shrx	%rax, %rbx, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L140
	movq	24(%rsp), %rsi
	movl	$8, %edx
	leaq	g_pi(%rip), %rdi
	call	app
	movq	%rbx, %rdx
	movq	%r15, %rsi
	leaq	g_pi(%rip), %rdi
	call	app
	movq	%rbx, %rdx
	addq	%r14, %rbx
	leaq	ZERO8(%rip), %rsi
	negq	%rdx
	leaq	g_pi(%rip), %rdi
	andl	$7, %edx
	call	app
	movq	8(%r13), %rax
	subq	%rbx, %rax
	cmpq	$31, %rax
	jbe	.L135
	movq	0(%r13), %rsi
	movl	$32, %edx
	leaq	32(%rbx), %r15
	addq	$1, %r12
	leaq	g_pi(%rip), %rdi
	addq	%rbx, %rsi
	call	app
	cmpq	%r12, 16(%rsp)
	jne	.L141
.L138:
	movq	8(%r13), %rax
	subq	%r15, %rax
	cmpq	$4775, %rax
	jbe	.L135
	movq	0(%r13), %rsi
	movl	$4776, %edx
	leaq	g_pi(%rip), %rdi
	addq	%r15, %rsi
	addq	$4776, %r15
	call	app
	cmpq	8(%r13), %r15
	jne	.L155
	movq	56(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L156
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L135:
	.cfi_restore_state
	leaq	.LC32(%rip), %rdi
	call	die
.L156:
	call	__stack_chk_fail@PLT
.L155:
	leaq	.LC33(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7389:
	.size	app_signed_words.constprop.0, .-app_signed_words.constprop.0
	.section	.rodata.str1.8
	.align 8
.LC34:
	.string	"usage: prover setup|first|step DIR"
	.section	.rodata.str1.1
.LC35:
	.string	"cannot enter DIR"
.LC36:
	.string	"setup"
.LC37:
	.string	"first"
.LC38:
	.string	"step"
.LC39:
	.string	"unknown mode"
.LC42:
	.string	"ready"
.LC43:
	.string	"go"
.LC44:
	.string	"no go"
.LC45:
	.string	"prev.stmt"
.LC46:
	.string	"prev.bin"
.LC47:
	.string	"RF_ORACLE"
.LC48:
	.string	"RF_ORACLE unset"
	.section	.rodata.str1.8
	.align 8
.LC49:
	.string	"cannot connect to the oracle service"
	.section	.rodata.str1.1
.LC50:
	.string	"SIGN write"
.LC51:
	.string	"SIGN read"
.LC52:
	.string	"SIGN refused"
.LC53:
	.string	"thread"
.LC54:
	.string	"proof.bin"
.LC55:
	.string	"%s.tmp"
.LC56:
	.string	"done"
.LC57:
	.string	"chainA.json"
.LC58:
	.string	"chainB.json"
.LC59:
	.string	"chain.json"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB7385:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$4096, %rsp
	orq	$0, (%rsp)
	subq	$1440, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rax
	movq	%rax, 5528(%rsp)
	xorl	%eax, %eax
	cmpl	$3, %edi
	jne	.L228
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L229
	movq	8(%rbx), %rbx
	leaq	.LC36(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L160
	leaq	.LC37(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	movl	%eax, %r14d
	testl	%eax, %eax
	je	.L161
	leaq	.LC38(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L230
.L161:
	call	__cpu_indicator_init@PLT
	movq	__cpu_model@GOTPCREL(%rip), %rax
	movl	12(%rax), %eax
	movl	%eax, %edx
	notl	%edx
	andl	$1081344, %edx
	je	.L231
	testl	$131072, %eax
	jne	.L232
.L163:
	leaq	chain_words_c(%rip), %rax
.L165:
	leaq	.LC42(%rip), %rdi
	movq	%rax, kernel(%rip)
	leaq	752(%rsp), %r12
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movl	$64, %esi
	movq	%r12, %rdi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L168
	movl	$2, %edx
	leaq	.LC43(%rip), %rsi
	movq	%r12, %rdi
	call	strncmp@PLT
	testl	%eax, %eax
	jne	.L168
	xorl	%edx, %edx
	vpxor	%xmm0, %xmm0, %xmm0
	movq	%rdx, 80(%rsp)
	vmovdqu	%xmm0, 88(%rsp)
	testl	%r14d, %r14d
	jne	.L233
	leaq	152(%rsp), %rax
	leaq	144(%rsp), %rdx
	movq	%rax, %rsi
	leaq	.LC57(%rip), %rdi
	movq	%rax, 32(%rsp)
	call	parse_chain
	leaq	224(%rsp), %rdx
	leaq	232(%rsp), %rsi
	leaq	.LC58(%rip), %rdi
	call	parse_chain
.L193:
	cmpl	$0, svc(%rip)
	js	.L173
.L179:
	xorl	%eax, %eax
	leaq	496(%rsp), %rbx
	movl	$16, %edx
	movq	$2, 496(%rsp)
	movq	%rax, 504(%rsp)
	movl	svc(%rip), %edi
	movq	%rbx, %rsi
	call	write@PLT
	cmpq	$16, %rax
	jne	.L174
	xorl	%r15d, %r15d
	.p2align 4
	.p2align 3
.L175:
	movl	$16, %edx
	movl	svc(%rip), %edi
	leaq	(%rbx,%r15), %rsi
	subq	%r15, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L184
	addq	%rax, %r15
	cmpq	$15, %r15
	jbe	.L175
	movq	%rbx, %rdx
	leaq	488(%rsp), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L181:
	movzbl	15(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rsi, %rdx
	jne	.L181
	cmpb	$0, 496(%rsp)
	jne	.L199
	xorl	%r15d, %r15d
	cmpq	$4772, %rax
	jne	.L199
	.p2align 4
	.p2align 3
.L182:
	movl	$4772, %edx
	movl	svc(%rip), %edi
	leaq	(%r12,%r15), %rsi
	subq	%r15, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L184
	addq	%rax, %r15
	cmpq	$4771, %r15
	jbe	.L182
	testl	%r14d, %r14d
	jne	.L185
	xorl	%esi, %esi
	leaq	224(%rsp), %rcx
	leaq	112(%rsp), %rdi
	leaq	walk(%rip), %rdx
	call	pthread_create@PLT
	testl	%eax, %eax
	jne	.L234
	movq	144(%rsp), %rsi
	movq	32(%rsp), %rdi
	leaq	184(%rsp), %rdx
	leaq	432(%rsp), %r13
	leaq	464(%rsp), %r14
	call	chain_end
	movq	112(%rsp), %rdi
	xorl	%esi, %esi
	call	pthread_join@PLT
	movq	144(%rsp), %rdx
	leaq	184(%rsp), %rsi
	movq	%r13, %rdi
	call	leaf_stmt
	movq	224(%rsp), %rdx
	leaq	264(%rsp), %rsi
	movq	%r14, %rdi
	call	leaf_stmt
	xorl	%esi, %esi
	leaq	piA.3(%rip), %rdi
	movq	144(%rsp), %r15
	call	app64
	movq	32(%rsp), %rsi
	movl	$32, %edx
	leaq	piA.3(%rip), %rdi
	call	app
	movq	%r15, %rsi
	leaq	piA.3(%rip), %rdi
	call	app64
	movq	%r12, %rdx
	leaq	piA.3(%rip), %rsi
	leaq	fA.2(%rip), %rdi
	call	signed_file
	movq	224(%rsp), %r15
	xorl	%esi, %esi
	leaq	piB.1(%rip), %rdi
	call	app64
	movl	$32, %edx
	leaq	232(%rsp), %rsi
	leaq	piB.1(%rip), %rdi
	call	app
	movq	%r15, %rsi
	leaq	piB.1(%rip), %rdi
	leaq	fB.0(%rip), %r15
	call	app64
	movq	%r12, %rdx
	leaq	piB.1(%rip), %rsi
	leaq	fB.0(%rip), %rdi
	call	signed_file
	leaq	fA.2(%rip), %rax
	movq	%rax, 32(%rsp)
.L187:
	movl	$1, %esi
	leaq	g_pi(%rip), %rdi
	call	app64
	movq	%r13, %rsi
	movl	$32, %edx
	leaq	g_pi(%rip), %rdi
	call	app
	movl	$32, %edx
	movq	%r14, %rsi
	leaq	g_pi(%rip), %rdi
	call	app
	movq	32(%rsp), %rdi
	call	app_signed_words.constprop.0
	movq	%r15, %rdi
	call	app_signed_words.constprop.0
	movq	%r12, %rdx
	leaq	g_pi(%rip), %rsi
	leaq	g_file(%rip), %rdi
	call	signed_file
	movl	$256, %ecx
	movq	%rbx, %rdi
	xorl	%eax, %eax
	leaq	.LC54(%rip), %r9
	movl	$2, %edx
	movl	$256, %esi
	leaq	.LC55(%rip), %r8
	call	__snprintf_chk@PLT
	movl	$420, %edx
	movq	%rbx, %rdi
	xorl	%eax, %eax
	movl	$577, %esi
	call	open@PLT
	movl	%eax, %r13d
	testl	%eax, %eax
	js	.L188
	movq	8+g_file(%rip), %rdx
	xorl	%r12d, %r12d
	testq	%rdx, %rdx
	je	.L191
	.p2align 4
	.p2align 3
.L189:
	leaq	g_file(%rip), %r14
	subq	%r12, %rdx
	movl	%r13d, %edi
	movq	(%r14), %rsi
	addq	%r12, %rsi
	call	write@PLT
	testq	%rax, %rax
	jle	.L188
	movq	8(%r14), %rdx
	addq	%rax, %r12
	cmpq	%rdx, %r12
	jb	.L189
.L191:
	movl	%r13d, %edi
	call	close@PLT
	testl	%eax, %eax
	jne	.L188
	leaq	.LC54(%rip), %rsi
	movq	%rbx, %rdi
	call	rename@PLT
	testl	%eax, %eax
	jne	.L235
	leaq	.LC56(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
.L160:
	movq	5528(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L236
	leaq	-40(%rbp), %rsp
	xorl	%eax, %eax
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L233:
	.cfi_restore_state
	leaq	152(%rsp), %rax
	leaq	.LC59(%rip), %rdi
	movq	%rax, %rsi
	leaq	144(%rsp), %rdx
	movq	%rax, 32(%rsp)
	call	parse_chain
	leaq	112(%rsp), %rdi
	leaq	.LC45(%rip), %rsi
	call	readfile
	cmpq	$63, 120(%rsp)
	jbe	.L194
	movq	112(%rsp), %rsi
	leaq	432(%rsp), %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L194
	movq	%rsi, %rdi
	call	free@PLT
	leaq	80(%rsp), %rdi
	leaq	.LC46(%rip), %rsi
	call	readfile
	jmp	.L193
.L185:
	movq	144(%rsp), %rsi
	movq	32(%rsp), %rdi
	leaq	184(%rsp), %rdx
	leaq	464(%rsp), %r14
	leaq	fA.2(%rip), %r15
	call	chain_end
	movq	144(%rsp), %rdx
	leaq	184(%rsp), %rsi
	movq	%r14, %rdi
	call	leaf_stmt
	xorl	%esi, %esi
	leaq	piA.3(%rip), %rdi
	movq	144(%rsp), %r13
	call	app64
	movq	32(%rsp), %rsi
	movl	$32, %edx
	leaq	piA.3(%rip), %rdi
	call	app
	movq	%r13, %rsi
	leaq	piA.3(%rip), %rdi
	leaq	432(%rsp), %r13
	call	app64
	movq	%r12, %rdx
	leaq	piA.3(%rip), %rsi
	leaq	fA.2(%rip), %rdi
	call	signed_file
	leaq	80(%rsp), %rax
	movq	%rax, 32(%rsp)
	jmp	.L187
.L173:
	leaq	.LC47(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.L237
	xorl	%eax, %eax
	movl	$27, %ecx
	movl	$107, %edx
	leaq	322(%rsp), %rdi
	rep stosl
	leaq	322(%rsp), %rdi
	movw	$1, 320(%rsp)
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, svc(%rip)
	testl	%eax, %eax
	js	.L178
	movl	$110, %edx
	leaq	320(%rsp), %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	je	.L179
.L178:
	leaq	.LC49(%rip), %rdi
	call	die
.L231:
	testl	$131072, %eax
	je	.L163
	vmovdqa	.LC40(%rip), %ymm1
	leaq	224(%rsp), %rbx
	vmovdqa	.LC41(%rip), %ymm0
	movl	$97, %esi
	movq	%rbx, %rdi
	leaq	320(%rsp), %r12
	vmovdqa	%ymm1, 224(%rsp)
	vmovdqa	%ymm1, (%rsp)
	vmovdqa	%ymm0, 320(%rsp)
	vmovdqa	%ymm0, 32(%rsp)
	vzeroupper
	call	chain_words_c
	movl	$97, %esi
	movq	%r12, %rdi
	call	chain_words_vec
	movl	$32, %edx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	memcmp@PLT
	vmovdqa	32(%rsp), %ymm0
	vmovdqa	(%rsp), %ymm1
	testl	%eax, %eax
	je	.L238
.L166:
	vmovdqa	%ymm1, 224(%rsp)
	movl	$97, %esi
	movq	%rbx, %rdi
	vmovdqa	%ymm0, 320(%rsp)
	vzeroupper
	call	chain_words_c
	movl	$97, %esi
	movq	%r12, %rdi
	call	chain_words_gp
	movl	$32, %edx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	vzeroupper
	call	memcmp@PLT
	testl	%eax, %eax
	jne	.L163
	leaq	chain_words_gp(%rip), %rax
	jmp	.L165
.L232:
	leaq	224(%rsp), %rbx
	leaq	320(%rsp), %r12
	vmovdqa	.LC40(%rip), %ymm1
	vmovdqa	.LC41(%rip), %ymm0
	jmp	.L166
.L238:
	leaq	chain_words_vec(%rip), %rax
	vzeroupper
	jmp	.L165
.L184:
	leaq	.LC51(%rip), %rdi
	call	die
.L188:
	movq	%rbx, %rdi
	call	die
.L229:
	leaq	.LC35(%rip), %rdi
	call	die
.L228:
	leaq	.LC34(%rip), %rdi
	call	die
.L236:
	call	__stack_chk_fail@PLT
.L194:
	leaq	.LC45(%rip), %rdi
	call	die
.L237:
	leaq	.LC48(%rip), %rdi
	call	die
.L235:
	leaq	.LC54(%rip), %rdi
	call	die
.L174:
	leaq	.LC50(%rip), %rdi
	call	die
.L168:
	leaq	.LC44(%rip), %rdi
	call	die
.L230:
	leaq	.LC39(%rip), %rdi
	call	die
.L199:
	leaq	.LC52(%rip), %rdi
	call	die
.L234:
	leaq	.LC53(%rip), %rdi
	call	die
	.cfi_endproc
.LFE7385:
	.size	main, .-main
	.local	fB.0
	.comm	fB.0,24,16
	.local	piB.1
	.comm	piB.1,24,16
	.local	fA.2
	.comm	fA.2,24,16
	.local	piA.3
	.comm	piA.3,24,16
	.local	g_file
	.comm	g_file,24,16
	.local	g_pi
	.comm	g_pi,24,16
	.data
	.align 4
	.type	svc, @object
	.size	svc, 4
svc:
	.long	-1
	.section	.rodata
	.align 8
	.type	ZERO8, @object
	.size	ZERO8, 8
ZERO8:
	.zero	8
	.section	.data.rel.local,"aw"
	.align 8
	.type	kernel, @object
	.size	kernel, 8
kernel:
	.quad	chain_words_c
	.section	.rodata
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
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC0:
	.long	0
	.long	3
	.long	6
	.long	9
	.align 16
.LC2:
	.long	1
	.long	5
	.long	3
	.long	7
	.align 16
.LC3:
	.long	0
	.long	1
	.long	2
	.long	3
	.align 16
.LC5:
	.quad	-9223372036854775808
	.quad	0
	.align 16
.LC26:
	.quad	-9223372036854742912
	.quad	-9223372036854742912
	.align 16
.LC27:
	.quad	-9223372034707259384
	.quad	-9223372034707259384
	.section	.rodata.cst32,"aM",@progbits,32
	.align 32
.LC40:
	.quad	81985529216486895
	.quad	-81985529216486896
	.quad	1
	.quad	2
	.set	.LC41,.LC40
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
