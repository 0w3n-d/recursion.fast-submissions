	.file	"prover.c"
	.text
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC0:
	.string	"toy prover: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB85:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC0(%rip), %rdx
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
.LFE85:
	.size	die, .-die
	.section	.rodata.str1.1
.LC1:
	.string	"out of memory"
	.text
	.p2align 4
	.type	app, @function
app:
.LFB86:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rdx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rdi), %rax
	movq	(%rdi), %rdi
	leaq	1(%rax,%rdx), %rbx
	movq	%rbx, %rsi
	call	realloc@PLT
	movq	%rax, 0(%rbp)
	testq	%rax, %rax
	je	.L7
	movq	8(%rbp), %rdx
	movq	%r13, %rsi
	cmpq	%rdx, %rbx
	leaq	(%rax,%rdx), %rdi
	cmovb	%rdx, %rbx
	movq	%rbx, %rcx
	subq	%rdx, %rcx
	movq	%r12, %rdx
	call	__memcpy_chk@PLT
	addq	%r12, 8(%rbp)
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L7:
	.cfi_restore_state
	leaq	.LC1(%rip), %rdi
	call	die
	.cfi_endproc
.LFE86:
	.size	app, .-app
	.p2align 4
	.type	app64, @function
app64:
.LFB87:
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
.L9:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L9
	movl	$8, %edx
	movq	%rsp, %rsi
	movq	%r8, %rdi
	call	app
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L14
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L14:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE87:
	.size	app64, .-app64
	.section	.rodata.str1.1
.LC2:
	.string	"rb"
	.text
	.p2align 4
	.type	readfile, @function
readfile:
.LFB88:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	leaq	-65536(%rsp), %r11
	.cfi_def_cfa 11, 65584
.LPSRL0:
	subq	$4096, %rsp
	orq	$0, (%rsp)
	cmpq	%r11, %rsp
	jne	.LPSRL0
	.cfi_def_cfa_register 7
	subq	$32, %rsp
	.cfi_def_cfa_offset 65616
	leaq	.LC2(%rip), %rsi
	movq	%fs:40, %rbx
	movq	%rbx, 65560(%rsp)
	movq	%rdi, %rbx
	call	fopen@PLT
	testq	%rax, %rax
	je	.L21
	movq	%rax, %r13
	xorl	%ebx, %ebx
	xorl	%ebp, %ebp
	jmp	.L16
	.p2align 4,,10
	.p2align 3
.L17:
	movq	%rax, %rdx
	leaq	16(%rsp), %rsi
	movq	%rsp, %rdi
	movq	%rbp, (%rsp)
	movq	%rbx, 8(%rsp)
	call	app
	movq	(%rsp), %rbp
	movq	8(%rsp), %rbx
.L16:
	movq	%r13, %rcx
	movl	$65536, %edx
	movl	$1, %esi
	leaq	16(%rsp), %rdi
	call	fread@PLT
	testq	%rax, %rax
	jne	.L17
	movq	%r13, %rdi
	call	fclose@PLT
	movq	%rbp, %rax
	movq	%rbx, %rdx
	movq	65560(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L22
	addq	$65568, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L21:
	.cfi_restore_state
	movq	%rbx, %rdi
	call	die
.L22:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE88:
	.size	readfile, .-readfile
	.p2align 4
	.type	keccak256, @function
keccak256:
.LFB79:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdi, %r8
	movl	$24, %ecx
	vpxor	%xmm0, %xmm0, %xmm0
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$640, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rax
	movq	%rax, 632(%rsp)
	xorl	%eax, %eax
	leaq	72(%rsp), %rdi
	leaq	496(%rsp), %r9
	movq	$0, 624(%rsp)
	vmovdqu	%ymm0, 496(%rsp)
	vmovdqu	%ymm0, 528(%rsp)
	vmovdqu	%ymm0, 560(%rsp)
	vmovdqu	%ymm0, 592(%rsp)
	rep stosq
	movl	%edx, %ecx
	movq	%r9, %rdi
	shrl	$3, %ecx
	rep movsq
	testb	$4, %dl
	je	.L24
	movl	(%rsi), %eax
	movl	%eax, (%rdi)
	movl	$4, %eax
.L24:
	testb	$2, %dl
	je	.L25
	movzwl	(%rsi,%rax), %ecx
	movw	%cx, (%rdi,%rax)
	addq	$2, %rax
.L25:
	testb	$1, %dl
	je	.L26
	movzbl	(%rsi,%rax), %ecx
	movb	%cl, (%rdi,%rax)
.L26:
	movzbl	496(%rsp), %eax
	addb	$-128, 631(%rsp)
	leaq	632(%rsp), %rdi
	xorb	$1, 496(%rsp,%rdx)
	leaq	497(%rsp), %rdx
	movq	%rax, 64(%rsp)
	.p2align 6
	.p2align 4
	.p2align 3
.L27:
	movl	%edx, %eax
	movzbl	(%rdx), %esi
	addq	$1, %rdx
	subl	%r9d, %eax
	movl	%eax, %ecx
	andl	$7, %eax
	sarl	$3, %ecx
	sall	$3, %eax
	movslq	%ecx, %rcx
	shlx	%rax, %rsi, %rax
	xorq	%rax, 64(%rsp,%rcx,8)
	cmpq	%rdx, %rdi
	jne	.L27
	leaq	RC(%rip), %r11
	movl	$3435973837, %edi
	.p2align 4
	.p2align 3
.L36:
	vmovdqu	104(%rsp), %ymm0
	movq	96(%rsp), %rax
	xorl	%esi, %esi
	leaq	64(%rsp), %r10
	vpxor	64(%rsp), %ymm0, %ymm0
	xorq	136(%rsp), %rax
	leaq	264(%rsp), %rcx
	vpxor	224(%rsp), %ymm0, %ymm0
	xorq	176(%rsp), %rax
	vmovdqu	144(%rsp), %ymm1
	xorq	216(%rsp), %rax
	vpxor	184(%rsp), %ymm1, %ymm1
	xorq	256(%rsp), %rax
	movq	%rax, 32(%rsp)
	vpxor	%ymm1, %ymm0, %ymm0
	vmovdqa	%ymm0, (%rsp)
.L38:
	leal	4(%rsi), %eax
	movq	%rax, %rdx
	imulq	%rdi, %rax
	shrq	$34, %rax
	leal	(%rax,%rax,4), %eax
	subl	%eax, %edx
	leal	1(%rsi), %eax
	movq	%rax, %rsi
	imulq	%rdi, %rax
	movslq	%edx, %r9
	shrq	$34, %rax
	leal	(%rax,%rax,4), %edx
	movl	%esi, %eax
	subl	%edx, %eax
	cltq
	movq	(%rsp,%rax,8), %rdx
	leaq	-160(%rcx), %rax
	rorx	$63, %rdx, %rdx
	xorq	(%rsp,%r9,8), %rdx
	xorq	%rdx, -200(%rcx)
.L29:
	xorq	%rdx, (%rax)
	xorq	%rdx, 40(%rax)
	addq	$80, %rax
	cmpq	%rcx, %rax
	jne	.L29
	leaq	8(%rax), %rcx
	cmpl	$5, %esi
	jne	.L38
	leaq	RHO(%rip), %r15
	leaq	64(%rsp), %r14
	xorl	%r13d, %r13d
.L32:
	leal	(%r13,%r13), %esi
	movq	%r15, %r12
	movq	%r14, %r9
	xorl	%edx, %edx
.L31:
	movl	%esi, %eax
	movq	(%r9), %rbx
	addq	$20, %r12
	addq	$40, %r9
	imulq	%rdi, %rax
	shrq	$34, %rax
	leal	(%rax,%rax,4), %ecx
	movl	%esi, %eax
	addl	$3, %esi
	subl	%ecx, %eax
	movl	-20(%r12), %ecx
	leal	(%rax,%rax,4), %eax
	addl	%edx, %eax
	rolq	%cl, %rbx
	addl	$1, %edx
	cltq
	movq	%rbx, 288(%rsp,%rax,8)
	cmpl	$5, %edx
	jne	.L31
	addl	$1, %r13d
	addq	$8, %r14
	addq	$4, %r15
	cmpl	$5, %r13d
	jne	.L32
	leaq	288(%rsp), %r12
	xorl	%r9d, %r9d
.L33:
	movq	8(%r12), %rax
	xorl	%ecx, %ecx
.L34:
	leal	2(%rcx), %edx
	notq	%rax
	movq	%rax, %rsi
	movq	%rdx, %rax
	imulq	%rdi, %rdx
	shrq	$34, %rdx
	leal	(%rdx,%rdx,4), %edx
	subl	%edx, %eax
	addl	%r9d, %eax
	cltq
	movq	288(%rsp,%rax,8), %rax
	andq	%rax, %rsi
	xorq	(%r12,%rcx,8), %rsi
	movq	%rsi, (%r10,%rcx,8)
	addq	$1, %rcx
	cmpq	$5, %rcx
	jne	.L34
	addl	$5, %r9d
	addq	$40, %r12
	addq	$40, %r10
	cmpl	$25, %r9d
	jne	.L33
	movq	64(%rsp), %rax
	addq	$8, %r11
	xorq	-8(%r11), %rax
	leaq	192+RC(%rip), %rbx
	movq	%rax, 64(%rsp)
	cmpq	%r11, %rbx
	jne	.L36
	movb	%al, (%r8)
	movl	$1, %eax
	.p2align 6
	.p2align 4
	.p2align 3
.L37:
	movl	%eax, %edx
	movl	%eax, %ecx
	sarl	$3, %edx
	andl	$7, %ecx
	movslq	%edx, %rdx
	sall	$3, %ecx
	movq	64(%rsp,%rdx,8), %rdx
	shrx	%rcx, %rdx, %rdx
	movb	%dl, (%r8,%rax)
	addq	$1, %rax
	cmpq	$32, %rax
	jne	.L37
	movq	632(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L61
	vzeroupper
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
.L61:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE79:
	.size	keccak256, .-keccak256
	.section	.rodata.str1.1
.LC3:
	.string	"ready"
.LC4:
	.string	"go"
.LC5:
	.string	"no go"
	.text
	.p2align 4
	.type	handshake, @function
handshake:
.LFB99:
	.cfi_startproc
	subq	$88, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %rdi
	movq	%rdi, 72(%rsp)
	leaq	.LC3(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movq	%rsp, %rdi
	movl	$64, %esi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L63
	cmpw	$28519, (%rsp)
	je	.L74
.L63:
	leaq	.LC5(%rip), %rdi
	call	die
.L74:
	movq	72(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L75
	addq	$88, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L75:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE99:
	.size	handshake, .-handshake
	.section	.rodata.str1.1
.LC6:
	.string	"RF_ORACLE"
.LC7:
	.string	"RF_ORACLE unset"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC8:
	.string	"cannot connect to the oracle service"
	.section	.rodata.str1.1
.LC9:
	.string	"SIGN write"
.LC10:
	.string	"SIGN read"
.LC11:
	.string	"SIGN refused"
	.text
	.p2align 4
	.type	signed_file, @function
signed_file:
.LFB97:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4144
	orq	$0, (%rsp)
	subq	$832, %rsp
	.cfi_def_cfa_offset 4976
	movl	svc(%rip), %eax
	movq	%fs:40, %r12
	movq	%r12, 4920(%rsp)
	movq	%rsi, %r12
	movq	%rdi, %r13
	testl	%eax, %eax
	js	.L77
.L83:
	leaq	128(%rsp), %rbp
	movl	svc(%rip), %edi
	movl	$16, %edx
	movq	$2, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	%rbp, %rsi
	call	write@PLT
	cmpq	$16, %rax
	jne	.L78
	xorl	%ebx, %ebx
	.p2align 4
	.p2align 3
.L79:
	movl	$16, %edx
	movl	svc(%rip), %edi
	leaq	0(%rbp,%rbx), %rsi
	subq	%rbx, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L88
	addq	%rax, %rbx
	cmpq	$15, %rbx
	jbe	.L79
	cmpb	$0, 128(%rsp)
	jne	.L85
	movq	%rbp, %rax
	leaq	120(%rsp), %rsi
	xorl	%edx, %edx
	.p2align 5
	.p2align 4
	.p2align 3
.L86:
	movzbl	15(%rax), %ecx
	salq	$8, %rdx
	subq	$1, %rax
	orq	%rcx, %rdx
	cmpq	%rsi, %rax
	jne	.L86
	cmpq	$4772, %rdx
	jne	.L85
	xorl	%ebx, %ebx
	leaq	144(%rsp), %r14
	movl	$4772, %ebp
	.p2align 4
	.p2align 3
.L87:
	movq	%rbp, %rdx
	movl	svc(%rip), %edi
	leaq	(%r14,%rbx), %rsi
	subq	%rbx, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L88
	addq	%rax, %rbx
	cmpq	$4771, %rbx
	jbe	.L87
	movq	%r12, %rsi
	movq	%rsp, %rdi
	movq	$0, (%rsp)
	movq	$0, 8(%rsp)
	call	app64
	movq	%r12, %rdx
	movq	%r13, %rsi
	movq	%rsp, %rdi
	call	app
	xorl	%esi, %esi
	movq	%rsp, %rdi
	call	app64
	movl	144(%rsp), %esi
	movq	%rsp, %rdi
	call	app64
	movl	$4768, %edx
	leaq	148(%rsp), %rsi
	movq	%rsp, %rdi
	call	app
	movq	(%rsp), %rax
	movq	8(%rsp), %rdx
	movq	4920(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L95
	addq	$4928, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L77:
	.cfi_restore_state
	leaq	.LC6(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.L96
	xorl	%eax, %eax
	movl	$27, %ecx
	leaq	18(%rsp), %rdi
	movl	$107, %edx
	rep stosl
	leaq	18(%rsp), %rdi
	movw	$1, 16(%rsp)
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, svc(%rip)
	testl	%eax, %eax
	js	.L82
	movl	$110, %edx
	leaq	16(%rsp), %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	je	.L83
.L82:
	leaq	.LC8(%rip), %rdi
	call	die
.L88:
	leaq	.LC10(%rip), %rdi
	call	die
.L78:
	leaq	.LC9(%rip), %rdi
	call	die
.L95:
	call	__stack_chk_fail@PLT
.L85:
	leaq	.LC11(%rip), %rdi
	call	die
.L96:
	leaq	.LC7(%rip), %rdi
	call	die
	.cfi_endproc
.LFE97:
	.size	signed_file, .-signed_file
	.section	.rodata.str1.1
.LC12:
	.string	"%2x"
	.text
	.p2align 4
	.type	unhex.constprop.0, @function
unhex.constprop.0:
.LFB106:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$24, %rsp
	.cfi_def_cfa_offset 64
	movq	%fs:40, %rbx
	movq	%rbx, 8(%rsp)
	movq	%rsi, %rbx
	leaq	64(%rbx), %r13
	.p2align 4
	.p2align 3
.L100:
	xorl	%eax, %eax
	leaq	4(%rsp), %rdx
	leaq	.LC12(%rip), %rsi
	movq	%rbx, %rdi
	call	__isoc23_sscanf@PLT
	cmpl	$1, %eax
	jne	.L104
	movl	4(%rsp), %eax
	addq	$2, %rbx
	addq	$1, %rbp
	movb	%al, -1(%rbp)
	cmpq	%r13, %rbx
	jne	.L100
	xorl	%eax, %eax
.L97:
	movq	8(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L105
	addq	$24, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L104:
	.cfi_restore_state
	movl	$-1, %eax
	jmp	.L97
.L105:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE106:
	.size	unhex.constprop.0, .-unhex.constprop.0
	.section	.rodata.str1.1
.LC13:
	.string	""
.LC14:
	.string	"\"n\":"
.LC15:
	.string	"\"start\":"
	.text
	.p2align 4
	.type	prove_chain_file, @function
prove_chain_file:
.LFB100:
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
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	movq	%rdi, %r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$192, %rsp
	.cfi_offset 3, -56
	movq	%rsi, 16(%rsp)
	movq	%fs:40, %rax
	movq	%rax, 184(%rsp)
	xorl	%eax, %eax
	call	readfile
	leaq	32(%rsp), %rdi
	leaq	.LC13(%rip), %rsi
	movq	%rdx, 40(%rsp)
	movl	$1, %edx
	movq	%rax, 32(%rsp)
	call	app
	movq	32(%rsp), %r14
	leaq	.LC14(%rip), %rsi
	movq	%r14, %rdi
	call	strstr@PLT
	leaq	.LC15(%rip), %rsi
	movq	%r14, %rdi
	movq	%rax, %rbx
	call	strstr@PLT
	testq	%rbx, %rbx
	je	.L110
	testq	%rax, %rax
	je	.L110
	leaq	8(%rax), %rdi
	movl	$34, %esi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L110
	leaq	1(%rax), %rsi
	leaq	64(%rsp), %rax
	movq	%rax, %rdi
	movq	%rax, 24(%rsp)
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L110
	leaq	4(%rbx), %rdi
	movl	$10, %edx
	xorl	%esi, %esi
	call	__isoc23_strtoull@PLT
	leaq	128(%rsp), %r12
	vmovdqa	64(%rsp), %ymm0
	movq	%rax, %rbx
	testq	%rax, %rax
	je	.L112
	xorl	%r15d, %r15d
	leaq	128(%rsp), %r12
	.p2align 4
	.p2align 3
.L113:
	movb	$67, 128(%rsp)
	movl	$33, %edx
	movq	%r12, %rsi
	leaq	96(%rsp), %rdi
	vmovdqu	%ymm0, 129(%rsp)
	vmovdqa	%ymm0, 96(%rsp)
	vzeroupper
	call	keccak256
	addq	$1, %r15
	vmovdqa	96(%rsp), %ymm0
	cmpq	%r15, %rbx
	jne	.L113
.L112:
	movb	$76, 128(%rsp)
	leaq	161(%rsp), %rdx
	xorl	%eax, %eax
	vmovdqu	%ymm0, 129(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L114:
	shrx	%rax, %rbx, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L114
	movq	16(%rsp), %rdi
	movl	$41, %edx
	movq	%r12, %rsi
	vzeroupper
	call	keccak256
	xorl	%esi, %esi
	leaq	48(%rsp), %rdi
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	call	app64
	movq	24(%rsp), %rsi
	movl	$32, %edx
	leaq	48(%rsp), %rdi
	call	app
	movq	%rbx, %rsi
	leaq	48(%rsp), %rdi
	call	app64
	movq	48(%rsp), %r12
	movq	56(%rsp), %rdx
	movq	%r12, %rdi
	movq	%rdx, %rsi
	call	signed_file
	movq	%r12, %rdi
	movq	%rax, %r13
	movq	%rdx, %rbx
	call	free@PLT
	movq	%r14, %rdi
	call	free@PLT
	movq	%r13, %rax
	movq	%rbx, %rdx
	movq	184(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L122
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
.L110:
	.cfi_restore_state
	movq	%r12, %rdi
	call	die
.L122:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE100:
	.size	prove_chain_file, .-prove_chain_file
	.section	.rodata.str1.1
.LC16:
	.string	"proof.bin"
.LC17:
	.string	"%s.tmp"
.LC18:
	.string	"wb"
	.text
	.p2align 4
	.type	writefile.constprop.0, @function
writefile.constprop.0:
.LFB107:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	leaq	.LC16(%rip), %r9
	movq	%rdi, %r13
	leaq	.LC17(%rip), %r8
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movl	$512, %ecx
	movq	%rsi, %r12
	movl	$2, %edx
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movl	$512, %esi
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$536, %rsp
	.cfi_def_cfa_offset 576
	movq	%fs:40, %rax
	movq	%rax, 520(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdi
	call	__snprintf_chk@PLT
	leaq	.LC18(%rip), %rsi
	movq	%rsp, %rdi
	call	fopen@PLT
	testq	%rax, %rax
	je	.L125
	movq	%rax, %rcx
	movq	%r12, %rdx
	movl	$1, %esi
	movq	%r13, %rdi
	movq	%rax, %rbp
	call	fwrite@PLT
	cmpq	%rax, %r12
	jne	.L125
	movq	%rbp, %rdi
	call	fclose@PLT
	testl	%eax, %eax
	jne	.L125
	leaq	.LC16(%rip), %rsi
	movq	%rsp, %rdi
	call	rename@PLT
	testl	%eax, %eax
	jne	.L125
	movq	520(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L132
	addq	$536, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L125:
	.cfi_restore_state
	leaq	.LC16(%rip), %rdi
	call	die
.L132:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE107:
	.size	writefile.constprop.0, .-writefile.constprop.0
	.section	.rodata.str1.1
.LC19:
	.string	"malformed child file"
	.section	.rodata.str1.8
	.align 8
.LC20:
	.string	"trailing bytes in a child file"
	.text
	.p2align 4
	.type	app_signed_words, @function
app_signed_words:
.LFB95:
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
	subq	$96, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rax
	movq	%rax, 88(%rsp)
	xorl	%eax, %eax
	cmpq	$7, %rdx
	jbe	.L136
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %r13
	xorl	%r15d, %r15d
	leaq	7(%rsi), %rax
	leaq	-1(%rsi), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L135:
	movzbl	(%rax), %edx
	salq	$8, %r15
	subq	$1, %rax
	orq	%rdx, %r15
	cmpq	%rcx, %rax
	jne	.L135
	leaq	-8(%r13), %r8
	cmpq	%r15, %r8
	jb	.L136
	leaq	64(%rsp), %rdx
	xorl	%eax, %eax
	movq	%rdx, 56(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L137:
	shrx	%rax, %r15, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L137
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%r8, 48(%rsp)
	call	app
	movq	%r15, %rdx
	leaq	8(%r12), %rsi
	movq	%rbx, %rdi
	call	app
	movq	%r15, %rdx
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	negq	%rdx
	andl	$7, %edx
	call	app
	movq	48(%rsp), %r8
	subq	%r15, %r8
	cmpq	$7, %r8
	jbe	.L136
	leaq	-8(%r12), %rdi
	leaq	(%r15,%r12), %rax
	movq	$0, 32(%rsp)
	movq	%rdi, 24(%rsp)
	leaq	(%r15,%rdi), %rsi
	.p2align 5
	.p2align 4
	.p2align 3
.L138:
	movq	32(%rsp), %rdx
	movzbl	15(%rax), %ecx
	subq	$1, %rax
	salq	$8, %rdx
	orq	%rdx, %rcx
	movq	%rcx, 32(%rsp)
	cmpq	%rax, %rsi
	jne	.L138
	movq	%rcx, %r14
	movq	%rcx, %rsi
	movq	%rbx, %rdi
	addq	$16, %r15
	call	app64
	testq	%r14, %r14
	je	.L139
	xorl	%r14d, %r14d
	.p2align 4
	.p2align 3
.L142:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$7, %rax
	jbe	.L136
	movq	24(%rsp), %rax
	leaq	(%r15,%r12), %rdx
	leaq	(%r15,%rax), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L140:
	movzbl	7(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rsi
	jne	.L140
	addq	$8, %r15
	movq	%r13, %rdx
	subq	%r15, %rdx
	cmpq	%rax, %rdx
	jb	.L136
	leaq	(%r12,%r15), %rdi
	movq	56(%rsp), %rcx
	xorl	%edx, %edx
	movq	%rdi, 48(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L141:
	shrx	%rdx, %rax, %rsi
	addl	$8, %edx
	movb	%sil, (%rcx)
	addq	$1, %rcx
	cmpl	$64, %edx
	jne	.L141
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%rax, 40(%rsp)
	call	app
	movq	40(%rsp), %rdx
	movq	48(%rsp), %rsi
	movq	%rbx, %rdi
	call	app
	movq	40(%rsp), %rax
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	movq	%rax, %rdx
	movq	%rax, 48(%rsp)
	negq	%rdx
	andl	$7, %edx
	call	app
	addq	48(%rsp), %r15
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$31, %rax
	jbe	.L136
	leaq	(%r12,%r15), %rsi
	movl	$32, %edx
	movq	%rbx, %rdi
	addq	$32, %r15
	call	app
	addq	$1, %r14
	cmpq	32(%rsp), %r14
	jne	.L142
.L139:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$4775, %rax
	jbe	.L136
	leaq	(%r12,%r15), %rsi
	movl	$4776, %edx
	movq	%rbx, %rdi
	addq	$4776, %r15
	call	app
	cmpq	%r15, %r13
	jne	.L156
	movq	88(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L157
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
.L136:
	.cfi_restore_state
	leaq	.LC19(%rip), %rdi
	call	die
.L157:
	call	__stack_chk_fail@PLT
.L156:
	leaq	.LC20(%rip), %rdi
	call	die
	.cfi_endproc
.LFE95:
	.size	app_signed_words, .-app_signed_words
	.p2align 4
	.type	ws_node, @function
ws_node:
.LFB96:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movq	%rdi, %r15
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	movq	%rsi, %r14
	movl	$1, %esi
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	movq	%rdx, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movq	%rcx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	movq	%r8, 8(%rsp)
	leaq	16(%rsp), %rdi
	movq	%fs:40, %rbp
	movq	%rbp, 40(%rsp)
	movq	%r9, %rbp
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	call	app64
	movl	$32, %edx
	movq	%r15, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movl	$32, %edx
	movq	%r14, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movq	%r13, %rsi
	movq	%r12, %rdx
	leaq	16(%rsp), %rdi
	call	app_signed_words
	movq	8(%rsp), %rsi
	leaq	16(%rsp), %rdi
	movq	%rbp, %rdx
	call	app_signed_words
	movq	16(%rsp), %rax
	movq	24(%rsp), %rdx
	movq	40(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L161
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
.L161:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE96:
	.size	ws_node, .-ws_node
	.section	.rodata.str1.8
	.align 8
.LC21:
	.string	"usage: prover setup|first|step DIR"
	.section	.rodata.str1.1
.LC22:
	.string	"cannot enter DIR"
.LC23:
	.string	"setup"
.LC24:
	.string	"first"
.LC25:
	.string	"chainA.json"
.LC26:
	.string	"chainB.json"
.LC27:
	.string	"done"
.LC28:
	.string	"step"
.LC29:
	.string	"prev.stmt"
.LC30:
	.string	"prev.bin"
.LC31:
	.string	"chain.json"
.LC32:
	.string	"unknown mode"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB103:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$112, %rsp
	.cfi_def_cfa_offset 144
	movq	%fs:40, %rax
	movq	%rax, 104(%rsp)
	xorl	%eax, %eax
	cmpl	$3, %edi
	jne	.L176
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L177
	movq	8(%rbx), %rbx
	leaq	.LC23(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L165
	leaq	.LC24(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L178
	leaq	.LC28(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L167
	call	handshake
	leaq	.LC29(%rip), %rdi
	call	readfile
	leaq	16(%rsp), %rdi
	leaq	.LC13(%rip), %rsi
	movq	%rdx, 24(%rsp)
	movl	$1, %edx
	movq	%rax, 16(%rsp)
	call	app
	cmpq	$64, 24(%rsp)
	jbe	.L169
	movq	16(%rsp), %rdx
	leaq	32(%rsp), %rdi
	movq	%rdx, %rsi
	movq	%rdx, 8(%rsp)
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L169
	movq	8(%rsp), %rdi
	call	free@PLT
	leaq	.LC30(%rip), %rdi
	call	readfile
	leaq	64(%rsp), %rsi
	leaq	.LC31(%rip), %rdi
	movq	%rsi, 8(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
.L175:
	call	prove_chain_file
	movq	8(%rsp), %rsi
	movq	%r15, %rcx
	leaq	32(%rsp), %rdi
	movq	%rdx, %r9
	movq	%rax, %r8
	movq	%r14, %rdx
	call	ws_node
	movq	%rax, %rdi
	movq	%rdx, %rsi
	call	signed_file
	movq	%rax, %rdi
	movq	%rdx, %rsi
	call	writefile.constprop.0
	leaq	.LC27(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
.L165:
	movq	104(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L179
	addq	$112, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L178:
	.cfi_restore_state
	call	handshake
	leaq	32(%rsp), %rsi
	leaq	.LC25(%rip), %rdi
	call	prove_chain_file
	leaq	64(%rsp), %rsi
	leaq	.LC26(%rip), %rdi
	movq	%rsi, 8(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	jmp	.L175
.L169:
	leaq	.LC29(%rip), %rdi
	call	die
.L177:
	leaq	.LC22(%rip), %rdi
	call	die
.L176:
	leaq	.LC21(%rip), %rdi
	call	die
.L179:
	call	__stack_chk_fail@PLT
.L167:
	leaq	.LC32(%rip), %rdi
	call	die
	.cfi_endproc
.LFE103:
	.size	main, .-main
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
