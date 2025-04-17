	.att_syntax
	.text
	.p2align	5
	.globl	_thash_f_jazz
	.globl	thash_f_jazz
	.globl	_thash_h_jazz
	.globl	thash_h_jazz
	.globl	_hash_message_jazz
	.globl	hash_message_jazz
	.globl	_prf_keygen_jazz
	.globl	prf_keygen_jazz
	.globl	_prf_jazz
	.globl	prf_jazz
_thash_f_jazz:
thash_f_jazz:
	movq	%rsp, %rax
	leaq	-64(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	movl	$0, %eax
	movl	%eax, 28(%rsi)
	leaq	-320(%rsp), %rsp
	call	L_thash_f$1
Lthash_f_jazz$1:
	leaq	320(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	movq	%rsp, %rsi
	vpxor	%ymm2, %ymm2, %ymm2
	andq	$-32, %rsp
	subq	$992, %rsp
	vmovdqu	%ymm2, 960(%rsp)
	vmovdqu	%ymm2, 928(%rsp)
	vmovdqu	%ymm2, 896(%rsp)
	vmovdqu	%ymm2, 864(%rsp)
	vmovdqu	%ymm2, 832(%rsp)
	vmovdqu	%ymm2, 800(%rsp)
	vmovdqu	%ymm2, 768(%rsp)
	vmovdqu	%ymm2, 736(%rsp)
	vmovdqu	%ymm2, 704(%rsp)
	vmovdqu	%ymm2, 672(%rsp)
	vmovdqu	%ymm2, 640(%rsp)
	vmovdqu	%ymm2, 608(%rsp)
	vmovdqu	%ymm2, 576(%rsp)
	vmovdqu	%ymm2, 544(%rsp)
	vmovdqu	%ymm2, 512(%rsp)
	vmovdqu	%ymm2, 480(%rsp)
	vmovdqu	%ymm2, 448(%rsp)
	vmovdqu	%ymm2, 416(%rsp)
	vmovdqu	%ymm2, 384(%rsp)
	vmovdqu	%ymm2, 352(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm2, 288(%rsp)
	vmovdqu	%ymm2, 256(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	vmovdqu	%ymm2, 192(%rsp)
	vmovdqu	%ymm2, 160(%rsp)
	vmovdqu	%ymm2, 128(%rsp)
	vmovdqu	%ymm2, 96(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	%ymm2, (%rsp)
	movq	%rsi, %rsp
	ret
_thash_h_jazz:
thash_h_jazz:
	movq	%rsp, %rax
	leaq	-64(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
Lthash_h_jazz$1:
	leaq	384(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	movq	%rsp, %rsi
	vpxor	%ymm2, %ymm2, %ymm2
	andq	$-32, %rsp
	subq	$1056, %rsp
	vmovdqu	%ymm2, 1024(%rsp)
	vmovdqu	%ymm2, 992(%rsp)
	vmovdqu	%ymm2, 960(%rsp)
	vmovdqu	%ymm2, 928(%rsp)
	vmovdqu	%ymm2, 896(%rsp)
	vmovdqu	%ymm2, 864(%rsp)
	vmovdqu	%ymm2, 832(%rsp)
	vmovdqu	%ymm2, 800(%rsp)
	vmovdqu	%ymm2, 768(%rsp)
	vmovdqu	%ymm2, 736(%rsp)
	vmovdqu	%ymm2, 704(%rsp)
	vmovdqu	%ymm2, 672(%rsp)
	vmovdqu	%ymm2, 640(%rsp)
	vmovdqu	%ymm2, 608(%rsp)
	vmovdqu	%ymm2, 576(%rsp)
	vmovdqu	%ymm2, 544(%rsp)
	vmovdqu	%ymm2, 512(%rsp)
	vmovdqu	%ymm2, 480(%rsp)
	vmovdqu	%ymm2, 448(%rsp)
	vmovdqu	%ymm2, 416(%rsp)
	vmovdqu	%ymm2, 384(%rsp)
	vmovdqu	%ymm2, 352(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm2, 288(%rsp)
	vmovdqu	%ymm2, 256(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	vmovdqu	%ymm2, 192(%rsp)
	vmovdqu	%ymm2, 160(%rsp)
	vmovdqu	%ymm2, 128(%rsp)
	vmovdqu	%ymm2, 96(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	%ymm2, (%rsp)
	movq	%rsi, %rsp
	ret
_hash_message_jazz:
hash_message_jazz:
	movq	%rsp, %rax
	leaq	-224(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rbx, 176(%rsp)
	movq	%rbp, 184(%rsp)
	movq	%r12, 192(%rsp)
	movq	%r13, 200(%rsp)
	movq	%r14, 208(%rsp)
	movq	%rax, 216(%rsp)
	leaq	16(%rsp), %rax
	movq	$2, %r10
	movb	%r10b, 31(%rax)
	shrq	$8, %r10
	movb	%r10b, 30(%rax)
	shrq	$8, %r10
	movb	%r10b, 29(%rax)
	shrq	$8, %r10
	movb	%r10b, 28(%rax)
	shrq	$8, %r10
	movb	%r10b, 27(%rax)
	shrq	$8, %r10
	movb	%r10b, 26(%rax)
	shrq	$8, %r10
	movb	%r10b, 25(%rax)
	shrq	$8, %r10
	movb	%r10b, 24(%rax)
	shrq	$8, %r10
	movb	%r10b, 23(%rax)
	shrq	$8, %r10
	movb	%r10b, 22(%rax)
	shrq	$8, %r10
	movb	%r10b, 21(%rax)
	shrq	$8, %r10
	movb	%r10b, 20(%rax)
	shrq	$8, %r10
	movb	%r10b, 19(%rax)
	shrq	$8, %r10
	movb	%r10b, 18(%rax)
	shrq	$8, %r10
	movb	%r10b, 17(%rax)
	shrq	$8, %r10
	movb	%r10b, 16(%rax)
	shrq	$8, %r10
	movb	%r10b, 15(%rax)
	shrq	$8, %r10
	movb	%r10b, 14(%rax)
	shrq	$8, %r10
	movb	%r10b, 13(%rax)
	shrq	$8, %r10
	movb	%r10b, 12(%rax)
	shrq	$8, %r10
	movb	%r10b, 11(%rax)
	shrq	$8, %r10
	movb	%r10b, 10(%rax)
	shrq	$8, %r10
	movb	%r10b, 9(%rax)
	shrq	$8, %r10
	movb	%r10b, 8(%rax)
	shrq	$8, %r10
	movb	%r10b, 7(%rax)
	shrq	$8, %r10
	movb	%r10b, 6(%rax)
	shrq	$8, %r10
	movb	%r10b, 5(%rax)
	shrq	$8, %r10
	movb	%r10b, 4(%rax)
	shrq	$8, %r10
	movb	%r10b, 3(%rax)
	shrq	$8, %r10
	movb	%r10b, 2(%rax)
	shrq	$8, %r10
	movb	%r10b, 1(%rax)
	shrq	$8, %r10
	movb	%r10b, (%rax)
	leaq	16(%rsp), %rax
	movq	$0, %r11
	call	Lmemcpy_u8pu8_plen___memcpy_u8pu8$1
Lhash_message_jazz$10:
	movq	%r8, %rax
	movq	$32, %r8
	movq	(%rsi), %r10
	movq	%r10, (%rax,%r8)
	movq	8(%rsi), %r10
	movq	%r10, 8(%rax,%r8)
	movq	16(%rsi), %r10
	movq	%r10, 16(%rax,%r8)
	movq	24(%rsi), %rsi
	movq	%rsi, 24(%rax,%r8)
	movq	$64, %rsi
	movq	(%rdx), %r8
	movq	%r8, (%rax,%rsi)
	movq	8(%rdx), %r8
	movq	%r8, 8(%rax,%rsi)
	movq	16(%rdx), %r8
	movq	%r8, 16(%rax,%rsi)
	movq	24(%rdx), %rdx
	movq	%rdx, 24(%rax,%rsi)
	leaq	16(%rsp), %rdx
	movb	%cl, 31(%rdx)
	shrq	$8, %rcx
	movb	%cl, 30(%rdx)
	shrq	$8, %rcx
	movb	%cl, 29(%rdx)
	shrq	$8, %rcx
	movb	%cl, 28(%rdx)
	shrq	$8, %rcx
	movb	%cl, 27(%rdx)
	shrq	$8, %rcx
	movb	%cl, 26(%rdx)
	shrq	$8, %rcx
	movb	%cl, 25(%rdx)
	shrq	$8, %rcx
	movb	%cl, 24(%rdx)
	shrq	$8, %rcx
	movb	%cl, 23(%rdx)
	shrq	$8, %rcx
	movb	%cl, 22(%rdx)
	shrq	$8, %rcx
	movb	%cl, 21(%rdx)
	shrq	$8, %rcx
	movb	%cl, 20(%rdx)
	shrq	$8, %rcx
	movb	%cl, 19(%rdx)
	shrq	$8, %rcx
	movb	%cl, 18(%rdx)
	shrq	$8, %rcx
	movb	%cl, 17(%rdx)
	shrq	$8, %rcx
	movb	%cl, 16(%rdx)
	shrq	$8, %rcx
	movb	%cl, 15(%rdx)
	shrq	$8, %rcx
	movb	%cl, 14(%rdx)
	shrq	$8, %rcx
	movb	%cl, 13(%rdx)
	shrq	$8, %rcx
	movb	%cl, 12(%rdx)
	shrq	$8, %rcx
	movb	%cl, 11(%rdx)
	shrq	$8, %rcx
	movb	%cl, 10(%rdx)
	shrq	$8, %rcx
	movb	%cl, 9(%rdx)
	shrq	$8, %rcx
	movb	%cl, 8(%rdx)
	shrq	$8, %rcx
	movb	%cl, 7(%rdx)
	shrq	$8, %rcx
	movb	%cl, 6(%rdx)
	shrq	$8, %rcx
	movb	%cl, 5(%rdx)
	shrq	$8, %rcx
	movb	%cl, 4(%rdx)
	shrq	$8, %rcx
	movb	%cl, 3(%rdx)
	shrq	$8, %rcx
	movb	%cl, 2(%rdx)
	shrq	$8, %rcx
	movb	%cl, 1(%rdx)
	shrq	$8, %rcx
	movb	%cl, (%rdx)
	leaq	16(%rsp), %rcx
	movq	$96, %rsi
	call	Lmemcpy_u8pu8_n___memcpy_u8pu8$1
Lhash_message_jazz$9:
	movq	%rax, %rcx
	addq	$128, %r9
	movq	%rdi, (%rsp)
	movq	%r9, %rax
	shlq	$3, %rax
	movq	%rax, 8(%rsp)
	movl	$1779033703, 16(%rsp)
	movl	$-1150833019, 20(%rsp)
	movl	$1013904242, 24(%rsp)
	movl	$-1521486534, 28(%rsp)
	movl	$1359893119, 32(%rsp)
	movl	$-1694144372, 36(%rsp)
	movl	$528734635, 40(%rsp)
	movl	$1541459225, 44(%rsp)
	leaq	16(%rsp), %rdx
	leaq	-272(%rsp), %rsp
	call	L_blocks_0_ref$1
Lhash_message_jazz$8:
	leaq	272(%rsp), %rsp
	movq	8(%rsp), %rsi
	movq	$0, %rax
	movl	%eax, 48(%rsp)
	movl	%eax, 52(%rsp)
	movl	%eax, 56(%rsp)
	movl	%eax, 60(%rsp)
	movl	%eax, 64(%rsp)
	movl	%eax, 68(%rsp)
	movl	%eax, 72(%rsp)
	movl	%eax, 76(%rsp)
	movl	%eax, 80(%rsp)
	movl	%eax, 84(%rsp)
	movl	%eax, 88(%rsp)
	movl	%eax, 92(%rsp)
	movl	%eax, 96(%rsp)
	movl	%eax, 100(%rsp)
	movl	%eax, 104(%rsp)
	movl	%eax, 108(%rsp)
	movl	%eax, 112(%rsp)
	movl	%eax, 116(%rsp)
	movl	%eax, 120(%rsp)
	movl	%eax, 124(%rsp)
	movl	%eax, 128(%rsp)
	movl	%eax, 132(%rsp)
	movl	%eax, 136(%rsp)
	movl	%eax, 140(%rsp)
	movl	%eax, 144(%rsp)
	movl	%eax, 148(%rsp)
	movl	%eax, 152(%rsp)
	movl	%eax, 156(%rsp)
	movl	%eax, 160(%rsp)
	movl	%eax, 164(%rsp)
	movl	%eax, 168(%rsp)
	movl	%eax, 172(%rsp)
	jmp 	Lhash_message_jazz$6
Lhash_message_jazz$7:
	movb	(%rcx,%rax), %dil
	movb	%dil, 48(%rsp,%rax)
	incq	%rax
Lhash_message_jazz$6:
	cmpq	%r9, %rax
	jb  	Lhash_message_jazz$7
	movb	$128, 48(%rsp,%rax)
	cmpq	$56, %r9
	jb  	Lhash_message_jazz$4
	movq	$120, %rdi
	movq	$2, %rax
	movq	$127, %rcx
	jmp 	Lhash_message_jazz$2
Lhash_message_jazz$4:
	movq	$56, %rdi
	movq	$1, %rax
	movq	$63, %rcx
Lhash_message_jazz$5:
	jmp 	Lhash_message_jazz$2
Lhash_message_jazz$3:
	movb	%sil, 48(%rsp,%rcx)
	shrq	$8, %rsi
	addq	$-1, %rcx
Lhash_message_jazz$2:
	cmpq	%rdi, %rcx
	jnb 	Lhash_message_jazz$3
	leaq	48(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
Lhash_message_jazz$1:
	leaq	280(%rsp), %rsp
	movq	(%rsp), %rax
	movl	16(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	20(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	24(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	28(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	32(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	36(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	40(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	44(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	movq	176(%rsp), %rbx
	movq	184(%rsp), %rbp
	movq	192(%rsp), %r12
	movq	200(%rsp), %r13
	movq	208(%rsp), %r14
	movq	216(%rsp), %rsp
	movq	%rsp, %rsi
	vpxor	%ymm2, %ymm2, %ymm2
	andq	$-32, %rsp
	subq	$512, %rsp
	vmovdqu	%ymm2, 480(%rsp)
	vmovdqu	%ymm2, 448(%rsp)
	vmovdqu	%ymm2, 416(%rsp)
	vmovdqu	%ymm2, 384(%rsp)
	vmovdqu	%ymm2, 352(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm2, 288(%rsp)
	vmovdqu	%ymm2, 256(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	vmovdqu	%ymm2, 192(%rsp)
	vmovdqu	%ymm2, 160(%rsp)
	vmovdqu	%ymm2, 128(%rsp)
	vmovdqu	%ymm2, 96(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	%ymm2, (%rsp)
	movq	%rsi, %rsp
	ret
_prf_keygen_jazz:
prf_keygen_jazz:
	movq	%rsp, %rax
	leaq	-64(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	movq	%rdx, %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
Lprf_keygen_jazz$1:
	leaq	312(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	movq	%rsp, %rsi
	vpxor	%ymm2, %ymm2, %ymm2
	andq	$-32, %rsp
	subq	$672, %rsp
	vmovdqu	%ymm2, 640(%rsp)
	vmovdqu	%ymm2, 608(%rsp)
	vmovdqu	%ymm2, 576(%rsp)
	vmovdqu	%ymm2, 544(%rsp)
	vmovdqu	%ymm2, 512(%rsp)
	vmovdqu	%ymm2, 480(%rsp)
	vmovdqu	%ymm2, 448(%rsp)
	vmovdqu	%ymm2, 416(%rsp)
	vmovdqu	%ymm2, 384(%rsp)
	vmovdqu	%ymm2, 352(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm2, 288(%rsp)
	vmovdqu	%ymm2, 256(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	vmovdqu	%ymm2, 192(%rsp)
	vmovdqu	%ymm2, 160(%rsp)
	vmovdqu	%ymm2, 128(%rsp)
	vmovdqu	%ymm2, 96(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	%ymm2, (%rsp)
	movq	%rsi, %rsp
	ret
_prf_jazz:
prf_jazz:
	movq	%rsp, %rax
	leaq	-64(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	movq	%rdi, %rax
	movq	%rdx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
Lprf_jazz$1:
	leaq	280(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	movq	%rsp, %rsi
	vpxor	%ymm2, %ymm2, %ymm2
	andq	$-32, %rsp
	subq	$640, %rsp
	vmovdqu	%ymm2, 608(%rsp)
	vmovdqu	%ymm2, 576(%rsp)
	vmovdqu	%ymm2, 544(%rsp)
	vmovdqu	%ymm2, 512(%rsp)
	vmovdqu	%ymm2, 480(%rsp)
	vmovdqu	%ymm2, 448(%rsp)
	vmovdqu	%ymm2, 416(%rsp)
	vmovdqu	%ymm2, 384(%rsp)
	vmovdqu	%ymm2, 352(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm2, 288(%rsp)
	vmovdqu	%ymm2, 256(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	vmovdqu	%ymm2, 192(%rsp)
	vmovdqu	%ymm2, 160(%rsp)
	vmovdqu	%ymm2, 128(%rsp)
	vmovdqu	%ymm2, 96(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	%ymm2, (%rsp)
	movq	%rsi, %rsp
	ret
L_thash_f$1:
	leaq	40(%rsp), %rax
	movq	%rax, %rcx
	movl	(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	4(%rax), %rcx
	movl	4(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	8(%rax), %rcx
	movl	8(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	12(%rax), %rcx
	movl	12(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	16(%rax), %rcx
	movl	16(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	20(%rax), %rcx
	movl	20(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	24(%rax), %rcx
	movl	24(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rcx)
	leaq	28(%rax), %rax
	movl	28(%rsi), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	leaq	104(%rsp), %rax
	movq	$0, %rcx
	movb	%cl, 31(%rax)
	shrq	$8, %rcx
	movb	%cl, 30(%rax)
	shrq	$8, %rcx
	movb	%cl, 29(%rax)
	shrq	$8, %rcx
	movb	%cl, 28(%rax)
	shrq	$8, %rcx
	movb	%cl, 27(%rax)
	shrq	$8, %rcx
	movb	%cl, 26(%rax)
	shrq	$8, %rcx
	movb	%cl, 25(%rax)
	shrq	$8, %rcx
	movb	%cl, 24(%rax)
	shrq	$8, %rcx
	movb	%cl, 23(%rax)
	shrq	$8, %rcx
	movb	%cl, 22(%rax)
	shrq	$8, %rcx
	movb	%cl, 21(%rax)
	shrq	$8, %rcx
	movb	%cl, 20(%rax)
	shrq	$8, %rcx
	movb	%cl, 19(%rax)
	shrq	$8, %rcx
	movb	%cl, 18(%rax)
	shrq	$8, %rcx
	movb	%cl, 17(%rax)
	shrq	$8, %rcx
	movb	%cl, 16(%rax)
	shrq	$8, %rcx
	movb	%cl, 15(%rax)
	shrq	$8, %rcx
	movb	%cl, 14(%rax)
	shrq	$8, %rcx
	movb	%cl, 13(%rax)
	shrq	$8, %rcx
	movb	%cl, 12(%rax)
	shrq	$8, %rcx
	movb	%cl, 11(%rax)
	shrq	$8, %rcx
	movb	%cl, 10(%rax)
	shrq	$8, %rcx
	movb	%cl, 9(%rax)
	shrq	$8, %rcx
	movb	%cl, 8(%rax)
	shrq	$8, %rcx
	movb	%cl, 7(%rax)
	shrq	$8, %rcx
	movb	%cl, 6(%rax)
	shrq	$8, %rcx
	movb	%cl, 5(%rax)
	shrq	$8, %rcx
	movb	%cl, 4(%rax)
	shrq	$8, %rcx
	movb	%cl, 3(%rax)
	shrq	$8, %rcx
	movb	%cl, 2(%rax)
	shrq	$8, %rcx
	movb	%cl, 1(%rax)
	shrq	$8, %rcx
	movb	%cl, (%rax)
	movq	%rdi, 8(%rsp)
	movq	%rsi, 16(%rsp)
	movq	%rdx, 24(%rsp)
	leaq	136(%rsp), %rax
	leaq	40(%rsp), %rsi
	movq	%rdx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_f$13:
	leaq	280(%rsp), %rsp
	movq	16(%rsp), %rax
	movl	$1, %ecx
	movl	%ecx, 28(%rax)
	leaq	40(%rsp), %rcx
	movq	%rcx, %rdx
	movl	(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	4(%rcx), %rdx
	movl	4(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	8(%rcx), %rdx
	movl	8(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	12(%rcx), %rdx
	movl	12(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	16(%rcx), %rdx
	movl	16(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	20(%rcx), %rdx
	movl	20(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	24(%rcx), %rdx
	movl	24(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	28(%rcx), %rcx
	movl	28(%rax), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rcx
	leaq	72(%rsp), %rax
	leaq	40(%rsp), %rsi
	movq	%rcx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_f$12:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rax
	movq	$0, %rcx
	jmp 	L_thash_f$10
L_thash_f$11:
	movq	(%rax,%rcx,8), %rdx
	xorq	72(%rsp,%rcx,8), %rdx
	movq	%rdx, 168(%rsp,%rcx,8)
	incq	%rcx
L_thash_f$10:
	cmpq	$4, %rcx
	jb  	L_thash_f$11
	leaq	104(%rsp), %rcx
	movq	%rax, 8(%rsp)
	movq	$96, %rax
	shlq	$3, %rax
	movq	%rax, 24(%rsp)
	movl	$1779033703, 72(%rsp)
	movl	$-1150833019, 76(%rsp)
	movl	$1013904242, 80(%rsp)
	movl	$-1521486534, 84(%rsp)
	movl	$1359893119, 88(%rsp)
	movl	$-1694144372, 92(%rsp)
	movl	$528734635, 96(%rsp)
	movl	$1541459225, 100(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	72(%rsp), %rdx
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_thash_f$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rax
	movq	24(%rsp), %rcx
	movq	$32, %rdi
	movq	$0, %r8
	movl	%r8d, 200(%rsp)
	movl	%r8d, 204(%rsp)
	movl	%r8d, 208(%rsp)
	movl	%r8d, 212(%rsp)
	movl	%r8d, 216(%rsp)
	movl	%r8d, 220(%rsp)
	movl	%r8d, 224(%rsp)
	movl	%r8d, 228(%rsp)
	movl	%r8d, 232(%rsp)
	movl	%r8d, 236(%rsp)
	movl	%r8d, 240(%rsp)
	movl	%r8d, 244(%rsp)
	movl	%r8d, 248(%rsp)
	movl	%r8d, 252(%rsp)
	movl	%r8d, 256(%rsp)
	movl	%r8d, 260(%rsp)
	movl	%r8d, 264(%rsp)
	movl	%r8d, 268(%rsp)
	movl	%r8d, 272(%rsp)
	movl	%r8d, 276(%rsp)
	movl	%r8d, 280(%rsp)
	movl	%r8d, 284(%rsp)
	movl	%r8d, 288(%rsp)
	movl	%r8d, 292(%rsp)
	movl	%r8d, 296(%rsp)
	movl	%r8d, 300(%rsp)
	movl	%r8d, 304(%rsp)
	movl	%r8d, 308(%rsp)
	movl	%r8d, 312(%rsp)
	movl	%r8d, 316(%rsp)
	movl	%r8d, 320(%rsp)
	movl	%r8d, 324(%rsp)
	jmp 	L_thash_f$7
L_thash_f$8:
	movq	%rsi, %r9
	addq	%r8, %r9
	movb	(%rax,%r9), %r9b
	movb	%r9b, 200(%rsp,%r8)
	incq	%r8
L_thash_f$7:
	cmpq	%rdi, %r8
	jb  	L_thash_f$8
	movb	$128, 200(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_thash_f$5
	movq	$120, %rdi
	movq	$2, %rax
	movq	$127, %rsi
	jmp 	L_thash_f$3
L_thash_f$5:
	movq	$56, %rdi
	movq	$1, %rax
	movq	$63, %rsi
L_thash_f$6:
	jmp 	L_thash_f$3
L_thash_f$4:
	movb	%cl, 200(%rsp,%rsi)
	shrq	$8, %rcx
	addq	$-1, %rsi
L_thash_f$3:
	cmpq	%rdi, %rsi
	jnb 	L_thash_f$4
	leaq	200(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_thash_f$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rax
	movl	72(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	76(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	80(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	84(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	88(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	92(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	96(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	100(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	movq	16(%rsp), %rcx
	ret
L_thash_h$1:
	leaq	136(%rsp), %rax
	movq	$1, %r8
	movb	%r8b, 31(%rax)
	shrq	$8, %r8
	movb	%r8b, 30(%rax)
	shrq	$8, %r8
	movb	%r8b, 29(%rax)
	shrq	$8, %r8
	movb	%r8b, 28(%rax)
	shrq	$8, %r8
	movb	%r8b, 27(%rax)
	shrq	$8, %r8
	movb	%r8b, 26(%rax)
	shrq	$8, %r8
	movb	%r8b, 25(%rax)
	shrq	$8, %r8
	movb	%r8b, 24(%rax)
	shrq	$8, %r8
	movb	%r8b, 23(%rax)
	shrq	$8, %r8
	movb	%r8b, 22(%rax)
	shrq	$8, %r8
	movb	%r8b, 21(%rax)
	shrq	$8, %r8
	movb	%r8b, 20(%rax)
	shrq	$8, %r8
	movb	%r8b, 19(%rax)
	shrq	$8, %r8
	movb	%r8b, 18(%rax)
	shrq	$8, %r8
	movb	%r8b, 17(%rax)
	shrq	$8, %r8
	movb	%r8b, 16(%rax)
	shrq	$8, %r8
	movb	%r8b, 15(%rax)
	shrq	$8, %r8
	movb	%r8b, 14(%rax)
	shrq	$8, %r8
	movb	%r8b, 13(%rax)
	shrq	$8, %r8
	movb	%r8b, 12(%rax)
	shrq	$8, %r8
	movb	%r8b, 11(%rax)
	shrq	$8, %r8
	movb	%r8b, 10(%rax)
	shrq	$8, %r8
	movb	%r8b, 9(%rax)
	shrq	$8, %r8
	movb	%r8b, 8(%rax)
	shrq	$8, %r8
	movb	%r8b, 7(%rax)
	shrq	$8, %r8
	movb	%r8b, 6(%rax)
	shrq	$8, %r8
	movb	%r8b, 5(%rax)
	shrq	$8, %r8
	movb	%r8b, 4(%rax)
	shrq	$8, %r8
	movb	%r8b, 3(%rax)
	shrq	$8, %r8
	movb	%r8b, 2(%rax)
	shrq	$8, %r8
	movb	%r8b, 1(%rax)
	shrq	$8, %r8
	movb	%r8b, (%rax)
	movl	$0, %eax
	movl	%eax, 28(%rsi)
	leaq	40(%rsp), %rax
	movq	%rax, %r8
	movl	(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	4(%rax), %r8
	movl	4(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	8(%rax), %r8
	movl	8(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	12(%rax), %r8
	movl	12(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	16(%rax), %r8
	movl	16(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	20(%rax), %r8
	movl	20(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	24(%rax), %r8
	movl	24(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	28(%rax), %rax
	movl	28(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rax)
	movq	%rdx, 8(%rsp)
	movq	%rdi, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	168(%rsp), %rax
	leaq	40(%rsp), %rsi
	movq	%rcx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$14:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movl	$1, %ecx
	movl	%ecx, 28(%rax)
	leaq	40(%rsp), %rcx
	movq	%rcx, %rdx
	movl	(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	4(%rcx), %rdx
	movl	4(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	8(%rcx), %rdx
	movl	8(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	12(%rcx), %rdx
	movl	12(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	16(%rcx), %rdx
	movl	16(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	20(%rcx), %rdx
	movl	20(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	24(%rcx), %rdx
	movl	24(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	28(%rcx), %rcx
	movl	28(%rax), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movq	%rax, 24(%rsp)
	movq	32(%rsp), %rcx
	leaq	72(%rsp), %rax
	leaq	40(%rsp), %rsi
	movq	%rcx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$13:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movl	$2, %ecx
	movl	%ecx, 28(%rax)
	movq	%rax, 24(%rsp)
	leaq	40(%rsp), %rcx
	movq	%rcx, %rdx
	movl	(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	4(%rcx), %rdx
	movl	4(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	8(%rcx), %rdx
	movl	8(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	12(%rcx), %rdx
	movl	12(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	16(%rcx), %rdx
	movl	16(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	20(%rcx), %rdx
	movl	20(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	24(%rcx), %rdx
	movl	24(%rax), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	leaq	28(%rcx), %rcx
	movl	28(%rax), %eax
	bswapl	%eax
	movl	%eax, (%rcx)
	movq	32(%rsp), %rcx
	leaq	104(%rsp), %rax
	leaq	40(%rsp), %rsi
	movq	%rcx, %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$12:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rax
	movq	$0, %rcx
	jmp 	L_thash_h$10
L_thash_h$11:
	movq	(%rax,%rcx,8), %rdx
	xorq	72(%rsp,%rcx,8), %rdx
	movq	%rdx, 200(%rsp,%rcx,8)
	incq	%rcx
L_thash_h$10:
	cmpq	$8, %rcx
	jb  	L_thash_h$11
	movq	16(%rsp), %rcx
	leaq	136(%rsp), %rax
	movq	%rcx, 16(%rsp)
	movq	$128, %rcx
	shlq	$3, %rcx
	movq	%rcx, 8(%rsp)
	movl	$1779033703, 40(%rsp)
	movl	$-1150833019, 44(%rsp)
	movl	$1013904242, 48(%rsp)
	movl	$-1521486534, 52(%rsp)
	movl	$1359893119, 56(%rsp)
	movl	$-1694144372, 60(%rsp)
	movl	$528734635, 64(%rsp)
	movl	$1541459225, 68(%rsp)
	movq	%rax, 32(%rsp)
	leaq	40(%rsp), %rdx
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_thash_h$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	$0, %rdi
	movq	$0, %r8
	movl	%r8d, 264(%rsp)
	movl	%r8d, 268(%rsp)
	movl	%r8d, 272(%rsp)
	movl	%r8d, 276(%rsp)
	movl	%r8d, 280(%rsp)
	movl	%r8d, 284(%rsp)
	movl	%r8d, 288(%rsp)
	movl	%r8d, 292(%rsp)
	movl	%r8d, 296(%rsp)
	movl	%r8d, 300(%rsp)
	movl	%r8d, 304(%rsp)
	movl	%r8d, 308(%rsp)
	movl	%r8d, 312(%rsp)
	movl	%r8d, 316(%rsp)
	movl	%r8d, 320(%rsp)
	movl	%r8d, 324(%rsp)
	movl	%r8d, 328(%rsp)
	movl	%r8d, 332(%rsp)
	movl	%r8d, 336(%rsp)
	movl	%r8d, 340(%rsp)
	movl	%r8d, 344(%rsp)
	movl	%r8d, 348(%rsp)
	movl	%r8d, 352(%rsp)
	movl	%r8d, 356(%rsp)
	movl	%r8d, 360(%rsp)
	movl	%r8d, 364(%rsp)
	movl	%r8d, 368(%rsp)
	movl	%r8d, 372(%rsp)
	movl	%r8d, 376(%rsp)
	movl	%r8d, 380(%rsp)
	movl	%r8d, 384(%rsp)
	movl	%r8d, 388(%rsp)
	jmp 	L_thash_h$7
L_thash_h$8:
	movq	%rsi, %r9
	addq	%r8, %r9
	movb	(%rax,%r9), %r9b
	movb	%r9b, 264(%rsp,%r8)
	incq	%r8
L_thash_h$7:
	cmpq	%rdi, %r8
	jb  	L_thash_h$8
	movb	$128, 264(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_thash_h$5
	movq	$120, %rdi
	movq	$2, %rax
	movq	$127, %rsi
	jmp 	L_thash_h$3
L_thash_h$5:
	movq	$56, %rdi
	movq	$1, %rax
	movq	$63, %rsi
L_thash_h$6:
	jmp 	L_thash_h$3
L_thash_h$4:
	movb	%cl, 264(%rsp,%rsi)
	shrq	$8, %rcx
	addq	$-1, %rsi
L_thash_h$3:
	cmpq	%rdi, %rsi
	jnb 	L_thash_h$4
	leaq	264(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_thash_h$2:
	leaq	280(%rsp), %rsp
	movq	16(%rsp), %rax
	movl	40(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	44(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	48(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	52(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	56(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	60(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	64(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	68(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	movq	24(%rsp), %rcx
	ret
L_prf_keygen$1:
	leaq	32(%rsp), %rax
	movq	$4, %rcx
	movb	%cl, 31(%rax)
	shrq	$8, %rcx
	movb	%cl, 30(%rax)
	shrq	$8, %rcx
	movb	%cl, 29(%rax)
	shrq	$8, %rcx
	movb	%cl, 28(%rax)
	shrq	$8, %rcx
	movb	%cl, 27(%rax)
	shrq	$8, %rcx
	movb	%cl, 26(%rax)
	shrq	$8, %rcx
	movb	%cl, 25(%rax)
	shrq	$8, %rcx
	movb	%cl, 24(%rax)
	shrq	$8, %rcx
	movb	%cl, 23(%rax)
	shrq	$8, %rcx
	movb	%cl, 22(%rax)
	shrq	$8, %rcx
	movb	%cl, 21(%rax)
	shrq	$8, %rcx
	movb	%cl, 20(%rax)
	shrq	$8, %rcx
	movb	%cl, 19(%rax)
	shrq	$8, %rcx
	movb	%cl, 18(%rax)
	shrq	$8, %rcx
	movb	%cl, 17(%rax)
	shrq	$8, %rcx
	movb	%cl, 16(%rax)
	shrq	$8, %rcx
	movb	%cl, 15(%rax)
	shrq	$8, %rcx
	movb	%cl, 14(%rax)
	shrq	$8, %rcx
	movb	%cl, 13(%rax)
	shrq	$8, %rcx
	movb	%cl, 12(%rax)
	shrq	$8, %rcx
	movb	%cl, 11(%rax)
	shrq	$8, %rcx
	movb	%cl, 10(%rax)
	shrq	$8, %rcx
	movb	%cl, 9(%rax)
	shrq	$8, %rcx
	movb	%cl, 8(%rax)
	shrq	$8, %rcx
	movb	%cl, 7(%rax)
	shrq	$8, %rcx
	movb	%cl, 6(%rax)
	shrq	$8, %rcx
	movb	%cl, 5(%rax)
	shrq	$8, %rcx
	movb	%cl, 4(%rax)
	shrq	$8, %rcx
	movb	%cl, 3(%rax)
	shrq	$8, %rcx
	movb	%cl, 2(%rax)
	shrq	$8, %rcx
	movb	%cl, 1(%rax)
	shrq	$8, %rcx
	movb	%cl, (%rax)
	leaq	64(%rsp), %rcx
	call	Lcopy_nbytes$1
L_prf_keygen$10:
	movq	(%rsi), %rax
	movq	%rax, 96(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 104(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 112(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 120(%rsp)
	movq	32(%rsi), %rax
	movq	%rax, 128(%rsp)
	movq	40(%rsi), %rax
	movq	%rax, 136(%rsp)
	movq	48(%rsi), %rax
	movq	%rax, 144(%rsp)
	movq	56(%rsi), %rax
	movq	%rax, 152(%rsp)
	leaq	32(%rsp), %rax
	movq	%rdi, 8(%rsp)
	movq	$128, %rcx
	shlq	$3, %rcx
	movq	%rcx, 16(%rsp)
	movl	$1779033703, 160(%rsp)
	movl	$-1150833019, 164(%rsp)
	movl	$1013904242, 168(%rsp)
	movl	$-1521486534, 172(%rsp)
	movl	$1359893119, 176(%rsp)
	movl	$-1694144372, 180(%rsp)
	movl	$528734635, 184(%rsp)
	movl	$1541459225, 188(%rsp)
	movq	%rax, 24(%rsp)
	leaq	160(%rsp), %rdx
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_prf_keygen$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	$0, %rdi
	movq	$0, %r8
	movl	%r8d, 192(%rsp)
	movl	%r8d, 196(%rsp)
	movl	%r8d, 200(%rsp)
	movl	%r8d, 204(%rsp)
	movl	%r8d, 208(%rsp)
	movl	%r8d, 212(%rsp)
	movl	%r8d, 216(%rsp)
	movl	%r8d, 220(%rsp)
	movl	%r8d, 224(%rsp)
	movl	%r8d, 228(%rsp)
	movl	%r8d, 232(%rsp)
	movl	%r8d, 236(%rsp)
	movl	%r8d, 240(%rsp)
	movl	%r8d, 244(%rsp)
	movl	%r8d, 248(%rsp)
	movl	%r8d, 252(%rsp)
	movl	%r8d, 256(%rsp)
	movl	%r8d, 260(%rsp)
	movl	%r8d, 264(%rsp)
	movl	%r8d, 268(%rsp)
	movl	%r8d, 272(%rsp)
	movl	%r8d, 276(%rsp)
	movl	%r8d, 280(%rsp)
	movl	%r8d, 284(%rsp)
	movl	%r8d, 288(%rsp)
	movl	%r8d, 292(%rsp)
	movl	%r8d, 296(%rsp)
	movl	%r8d, 300(%rsp)
	movl	%r8d, 304(%rsp)
	movl	%r8d, 308(%rsp)
	movl	%r8d, 312(%rsp)
	movl	%r8d, 316(%rsp)
	jmp 	L_prf_keygen$7
L_prf_keygen$8:
	movq	%rsi, %r9
	addq	%r8, %r9
	movb	(%rax,%r9), %r9b
	movb	%r9b, 192(%rsp,%r8)
	incq	%r8
L_prf_keygen$7:
	cmpq	%rdi, %r8
	jb  	L_prf_keygen$8
	movb	$128, 192(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_prf_keygen$5
	movq	$120, %rdi
	movq	$2, %rax
	movq	$127, %rsi
	jmp 	L_prf_keygen$3
L_prf_keygen$5:
	movq	$56, %rdi
	movq	$1, %rax
	movq	$63, %rsi
L_prf_keygen$6:
	jmp 	L_prf_keygen$3
L_prf_keygen$4:
	movb	%cl, 192(%rsp,%rsi)
	shrq	$8, %rcx
	addq	$-1, %rsi
L_prf_keygen$3:
	cmpq	%rdi, %rsi
	jnb 	L_prf_keygen$4
	leaq	192(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_prf_keygen$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rax
	movl	160(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	164(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	168(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	172(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	176(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	180(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	184(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	188(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	ret
L_prf$1:
	leaq	32(%rsp), %rcx
	movq	$3, %rdx
	movb	%dl, 31(%rcx)
	shrq	$8, %rdx
	movb	%dl, 30(%rcx)
	shrq	$8, %rdx
	movb	%dl, 29(%rcx)
	shrq	$8, %rdx
	movb	%dl, 28(%rcx)
	shrq	$8, %rdx
	movb	%dl, 27(%rcx)
	shrq	$8, %rdx
	movb	%dl, 26(%rcx)
	shrq	$8, %rdx
	movb	%dl, 25(%rcx)
	shrq	$8, %rdx
	movb	%dl, 24(%rcx)
	shrq	$8, %rdx
	movb	%dl, 23(%rcx)
	shrq	$8, %rdx
	movb	%dl, 22(%rcx)
	shrq	$8, %rdx
	movb	%dl, 21(%rcx)
	shrq	$8, %rdx
	movb	%dl, 20(%rcx)
	shrq	$8, %rdx
	movb	%dl, 19(%rcx)
	shrq	$8, %rdx
	movb	%dl, 18(%rcx)
	shrq	$8, %rdx
	movb	%dl, 17(%rcx)
	shrq	$8, %rdx
	movb	%dl, 16(%rcx)
	shrq	$8, %rdx
	movb	%dl, 15(%rcx)
	shrq	$8, %rdx
	movb	%dl, 14(%rcx)
	shrq	$8, %rdx
	movb	%dl, 13(%rcx)
	shrq	$8, %rdx
	movb	%dl, 12(%rcx)
	shrq	$8, %rdx
	movb	%dl, 11(%rcx)
	shrq	$8, %rdx
	movb	%dl, 10(%rcx)
	shrq	$8, %rdx
	movb	%dl, 9(%rcx)
	shrq	$8, %rdx
	movb	%dl, 8(%rcx)
	shrq	$8, %rdx
	movb	%dl, 7(%rcx)
	shrq	$8, %rdx
	movb	%dl, 6(%rcx)
	shrq	$8, %rdx
	movb	%dl, 5(%rcx)
	shrq	$8, %rdx
	movb	%dl, 4(%rcx)
	shrq	$8, %rdx
	movb	%dl, 3(%rcx)
	shrq	$8, %rdx
	movb	%dl, 2(%rcx)
	shrq	$8, %rdx
	movb	%dl, 1(%rcx)
	shrq	$8, %rdx
	movb	%dl, (%rcx)
	leaq	64(%rsp), %rcx
	call	Lcopy_nbytes$1
L_prf$10:
	movq	(%rsi), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsi), %rcx
	movq	%rcx, 104(%rsp)
	movq	16(%rsi), %rcx
	movq	%rcx, 112(%rsp)
	movq	24(%rsi), %rcx
	movq	%rcx, 120(%rsp)
	leaq	32(%rsp), %rcx
	movq	%rax, 8(%rsp)
	movq	$96, %rax
	shlq	$3, %rax
	movq	%rax, 16(%rsp)
	movl	$1779033703, 128(%rsp)
	movl	$-1150833019, 132(%rsp)
	movl	$1013904242, 136(%rsp)
	movl	$-1521486534, 140(%rsp)
	movl	$1359893119, 144(%rsp)
	movl	$-1694144372, 148(%rsp)
	movl	$528734635, 152(%rsp)
	movl	$1541459225, 156(%rsp)
	movq	%rcx, 24(%rsp)
	leaq	128(%rsp), %rdx
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_prf$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	$32, %rdi
	movq	$0, %r8
	movl	%r8d, 160(%rsp)
	movl	%r8d, 164(%rsp)
	movl	%r8d, 168(%rsp)
	movl	%r8d, 172(%rsp)
	movl	%r8d, 176(%rsp)
	movl	%r8d, 180(%rsp)
	movl	%r8d, 184(%rsp)
	movl	%r8d, 188(%rsp)
	movl	%r8d, 192(%rsp)
	movl	%r8d, 196(%rsp)
	movl	%r8d, 200(%rsp)
	movl	%r8d, 204(%rsp)
	movl	%r8d, 208(%rsp)
	movl	%r8d, 212(%rsp)
	movl	%r8d, 216(%rsp)
	movl	%r8d, 220(%rsp)
	movl	%r8d, 224(%rsp)
	movl	%r8d, 228(%rsp)
	movl	%r8d, 232(%rsp)
	movl	%r8d, 236(%rsp)
	movl	%r8d, 240(%rsp)
	movl	%r8d, 244(%rsp)
	movl	%r8d, 248(%rsp)
	movl	%r8d, 252(%rsp)
	movl	%r8d, 256(%rsp)
	movl	%r8d, 260(%rsp)
	movl	%r8d, 264(%rsp)
	movl	%r8d, 268(%rsp)
	movl	%r8d, 272(%rsp)
	movl	%r8d, 276(%rsp)
	movl	%r8d, 280(%rsp)
	movl	%r8d, 284(%rsp)
	jmp 	L_prf$7
L_prf$8:
	movq	%rsi, %r9
	addq	%r8, %r9
	movb	(%rax,%r9), %r9b
	movb	%r9b, 160(%rsp,%r8)
	incq	%r8
L_prf$7:
	cmpq	%rdi, %r8
	jb  	L_prf$8
	movb	$128, 160(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_prf$5
	movq	$120, %rdi
	movq	$2, %rax
	movq	$127, %rsi
	jmp 	L_prf$3
L_prf$5:
	movq	$56, %rdi
	movq	$1, %rax
	movq	$63, %rsi
L_prf$6:
	jmp 	L_prf$3
L_prf$4:
	movb	%cl, 160(%rsp,%rsi)
	shrq	$8, %rcx
	addq	$-1, %rsi
L_prf$3:
	cmpq	%rdi, %rsi
	jnb 	L_prf$4
	leaq	160(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_prf$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rax
	movl	128(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	132(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	136(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	140(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	144(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	148(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	152(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	156(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	ret
Lhash_plen_3n___blocks_0_ref_array$1:
	movq	$0, %rsi
	movq	$128, %rdi
	leaq	glob_data + 0(%rip), %rcx
	movq	%rdx, 8(%rsp)
	movq	8(%rsp), %rdx
	jmp 	Lhash_plen_3n___blocks_0_ref_array$2
Lhash_plen_3n___blocks_0_ref_array$3:
	movq	%rdi, 8(%rsp)
	movl	(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 32(%rsp)
	movl	4(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 36(%rsp)
	movl	8(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 40(%rsp)
	movl	12(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 44(%rsp)
	movl	16(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 48(%rsp)
	movl	20(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 52(%rsp)
	movl	24(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 56(%rsp)
	movl	28(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 60(%rsp)
	movl	32(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 64(%rsp)
	movl	36(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 68(%rsp)
	movl	40(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 72(%rsp)
	movl	44(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 76(%rsp)
	movl	48(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 80(%rsp)
	movl	52(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 84(%rsp)
	movl	56(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 88(%rsp)
	movl	60(%rax,%rsi), %edi
	bswapl	%edi
	movl	%edi, 92(%rsp)
	movq	%rsi, 16(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	68(%rsp), %edi
	movl	36(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	32(%rsp), %edi
	movl	%edi, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	72(%rsp), %edi
	movl	40(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	36(%rsp), %edi
	movl	%edi, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	76(%rsp), %edi
	movl	44(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	40(%rsp), %edi
	movl	%edi, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	80(%rsp), %edi
	movl	48(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	44(%rsp), %edi
	movl	%edi, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	84(%rsp), %edi
	movl	52(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	48(%rsp), %edi
	movl	%edi, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	88(%rsp), %edi
	movl	56(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	52(%rsp), %edi
	movl	%edi, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	92(%rsp), %edi
	movl	60(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	56(%rsp), %edi
	movl	%edi, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	96(%rsp), %edi
	movl	64(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	60(%rsp), %edi
	movl	%edi, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	100(%rsp), %edi
	movl	68(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	64(%rsp), %edi
	movl	%edi, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	104(%rsp), %edi
	movl	72(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	68(%rsp), %edi
	movl	%edi, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	108(%rsp), %edi
	movl	76(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	72(%rsp), %edi
	movl	%edi, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	112(%rsp), %edi
	movl	80(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	76(%rsp), %edi
	movl	%edi, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	116(%rsp), %edi
	movl	84(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	80(%rsp), %edi
	movl	%edi, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	120(%rsp), %edi
	movl	88(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	84(%rsp), %edi
	movl	%edi, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	124(%rsp), %edi
	movl	92(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	88(%rsp), %edi
	movl	%edi, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	128(%rsp), %edi
	movl	96(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	92(%rsp), %edi
	movl	%edi, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	132(%rsp), %edi
	movl	100(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	96(%rsp), %edi
	movl	%edi, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	136(%rsp), %edi
	movl	104(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	100(%rsp), %edi
	movl	%edi, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	140(%rsp), %edi
	movl	108(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	104(%rsp), %edi
	movl	%edi, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	144(%rsp), %edi
	movl	112(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	108(%rsp), %edi
	movl	%edi, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	148(%rsp), %edi
	movl	116(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	112(%rsp), %edi
	movl	%edi, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	152(%rsp), %edi
	movl	120(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	116(%rsp), %edi
	movl	%edi, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	156(%rsp), %edi
	movl	124(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	120(%rsp), %edi
	movl	%edi, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	160(%rsp), %edi
	movl	128(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	124(%rsp), %edi
	movl	%edi, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	164(%rsp), %edi
	movl	132(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	128(%rsp), %edi
	movl	%edi, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	168(%rsp), %edi
	movl	136(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	132(%rsp), %edi
	movl	%edi, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	172(%rsp), %edi
	movl	140(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	136(%rsp), %edi
	movl	%edi, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	176(%rsp), %edi
	movl	144(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	140(%rsp), %edi
	movl	%edi, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	180(%rsp), %edi
	movl	148(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	144(%rsp), %edi
	movl	%edi, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	184(%rsp), %edi
	movl	152(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	148(%rsp), %edi
	movl	%edi, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	188(%rsp), %edi
	movl	156(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	152(%rsp), %edi
	movl	%edi, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	192(%rsp), %edi
	movl	160(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	156(%rsp), %edi
	movl	%edi, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	196(%rsp), %edi
	movl	164(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	160(%rsp), %edi
	movl	%edi, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	200(%rsp), %edi
	movl	168(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	164(%rsp), %edi
	movl	%edi, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	204(%rsp), %edi
	movl	172(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	168(%rsp), %edi
	movl	%edi, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	208(%rsp), %edi
	movl	176(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	172(%rsp), %edi
	movl	%edi, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	212(%rsp), %edi
	movl	180(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	176(%rsp), %edi
	movl	%edi, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	216(%rsp), %edi
	movl	184(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	180(%rsp), %edi
	movl	%edi, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	220(%rsp), %edi
	movl	188(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	184(%rsp), %edi
	movl	%edi, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	224(%rsp), %edi
	movl	192(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	188(%rsp), %edi
	movl	%edi, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	228(%rsp), %edi
	movl	196(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	192(%rsp), %edi
	movl	%edi, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	232(%rsp), %edi
	movl	200(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	196(%rsp), %edi
	movl	%edi, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	236(%rsp), %edi
	movl	204(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	200(%rsp), %edi
	movl	%edi, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	240(%rsp), %edi
	movl	208(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	204(%rsp), %edi
	movl	%edi, 268(%rsp)
	movl	264(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	244(%rsp), %edi
	movl	212(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	208(%rsp), %edi
	movl	%edi, 272(%rsp)
	movl	268(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	248(%rsp), %edi
	movl	216(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	212(%rsp), %edi
	movl	%edi, 276(%rsp)
	movl	272(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	252(%rsp), %edi
	movl	220(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	216(%rsp), %edi
	movl	%edi, 280(%rsp)
	movl	276(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	256(%rsp), %edi
	movl	224(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	220(%rsp), %edi
	movl	%edi, 284(%rsp)
	movl	(%rdx), %r12d
	movl	4(%rdx), %esi
	movl	8(%rdx), %edi
	movl	12(%rdx), %r8d
	movl	16(%rdx), %ebp
	movl	20(%rdx), %r9d
	movl	24(%rdx), %r10d
	movl	28(%rdx), %r13d
	movq	%rdx, 24(%rsp)
	movq	$0, %rdx
	jmp 	Lhash_plen_3n___blocks_0_ref_array$4
Lhash_plen_3n___blocks_0_ref_array$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r9d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rcx,%rdx,4), %r11d
	addl	32(%rsp,%rdx,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%esi, %r13d
	movl	%r12d, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	movl	%esi, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r9d, %r10d
	movl	%ebp, %r9d
	movl	%r8d, %ebp
	addl	%r11d, %ebp
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r12d, %esi
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rdx
Lhash_plen_3n___blocks_0_ref_array$4:
	cmpq	$64, %rdx
	jb  	Lhash_plen_3n___blocks_0_ref_array$5
	movq	24(%rsp), %rdx
	addl	(%rdx), %r12d
	addl	4(%rdx), %esi
	addl	8(%rdx), %edi
	addl	12(%rdx), %r8d
	addl	16(%rdx), %ebp
	addl	20(%rdx), %r9d
	addl	24(%rdx), %r10d
	addl	28(%rdx), %r13d
	movl	%r12d, (%rdx)
	movl	%esi, 4(%rdx)
	movl	%edi, 8(%rdx)
	movl	%r8d, 12(%rdx)
	movl	%ebp, 16(%rdx)
	movl	%r9d, 20(%rdx)
	movl	%r10d, 24(%rdx)
	movl	%r13d, 28(%rdx)
	movq	16(%rsp), %rsi
	movq	8(%rsp), %rdi
	addq	$64, %rsi
	addq	$-64, %rdi
Lhash_plen_3n___blocks_0_ref_array$2:
	cmpq	$64, %rdi
	jnb 	Lhash_plen_3n___blocks_0_ref_array$3
	ret
Lhash_plen_2n___blocks_0_ref_array$1:
	movq	$0, %rsi
	movq	$96, %rdi
	leaq	glob_data + 0(%rip), %rax
	movq	%rdx, 8(%rsp)
	movq	8(%rsp), %rdx
	jmp 	Lhash_plen_2n___blocks_0_ref_array$2
Lhash_plen_2n___blocks_0_ref_array$3:
	movq	%rdi, 8(%rsp)
	movl	(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 32(%rsp)
	movl	4(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 36(%rsp)
	movl	8(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 40(%rsp)
	movl	12(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 44(%rsp)
	movl	16(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 48(%rsp)
	movl	20(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 52(%rsp)
	movl	24(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 56(%rsp)
	movl	28(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 60(%rsp)
	movl	32(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 64(%rsp)
	movl	36(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 68(%rsp)
	movl	40(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 72(%rsp)
	movl	44(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 76(%rsp)
	movl	48(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 80(%rsp)
	movl	52(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 84(%rsp)
	movl	56(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 88(%rsp)
	movl	60(%rcx,%rsi), %edi
	bswapl	%edi
	movl	%edi, 92(%rsp)
	movq	%rsi, 16(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	68(%rsp), %edi
	movl	36(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	32(%rsp), %edi
	movl	%edi, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	72(%rsp), %edi
	movl	40(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	36(%rsp), %edi
	movl	%edi, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	76(%rsp), %edi
	movl	44(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	40(%rsp), %edi
	movl	%edi, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	80(%rsp), %edi
	movl	48(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	44(%rsp), %edi
	movl	%edi, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	84(%rsp), %edi
	movl	52(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	48(%rsp), %edi
	movl	%edi, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	88(%rsp), %edi
	movl	56(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	52(%rsp), %edi
	movl	%edi, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	92(%rsp), %edi
	movl	60(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	56(%rsp), %edi
	movl	%edi, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	96(%rsp), %edi
	movl	64(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	60(%rsp), %edi
	movl	%edi, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	100(%rsp), %edi
	movl	68(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	64(%rsp), %edi
	movl	%edi, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	104(%rsp), %edi
	movl	72(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	68(%rsp), %edi
	movl	%edi, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	108(%rsp), %edi
	movl	76(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	72(%rsp), %edi
	movl	%edi, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	112(%rsp), %edi
	movl	80(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	76(%rsp), %edi
	movl	%edi, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	116(%rsp), %edi
	movl	84(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	80(%rsp), %edi
	movl	%edi, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	120(%rsp), %edi
	movl	88(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	84(%rsp), %edi
	movl	%edi, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	124(%rsp), %edi
	movl	92(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	88(%rsp), %edi
	movl	%edi, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	128(%rsp), %edi
	movl	96(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	92(%rsp), %edi
	movl	%edi, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	132(%rsp), %edi
	movl	100(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	96(%rsp), %edi
	movl	%edi, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	136(%rsp), %edi
	movl	104(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	100(%rsp), %edi
	movl	%edi, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	140(%rsp), %edi
	movl	108(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	104(%rsp), %edi
	movl	%edi, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	144(%rsp), %edi
	movl	112(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	108(%rsp), %edi
	movl	%edi, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	148(%rsp), %edi
	movl	116(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	112(%rsp), %edi
	movl	%edi, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	152(%rsp), %edi
	movl	120(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	116(%rsp), %edi
	movl	%edi, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	156(%rsp), %edi
	movl	124(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	120(%rsp), %edi
	movl	%edi, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	160(%rsp), %edi
	movl	128(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	124(%rsp), %edi
	movl	%edi, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	164(%rsp), %edi
	movl	132(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	128(%rsp), %edi
	movl	%edi, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	168(%rsp), %edi
	movl	136(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	132(%rsp), %edi
	movl	%edi, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	172(%rsp), %edi
	movl	140(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	136(%rsp), %edi
	movl	%edi, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	176(%rsp), %edi
	movl	144(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	140(%rsp), %edi
	movl	%edi, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	180(%rsp), %edi
	movl	148(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	144(%rsp), %edi
	movl	%edi, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	184(%rsp), %edi
	movl	152(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	148(%rsp), %edi
	movl	%edi, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	188(%rsp), %edi
	movl	156(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	152(%rsp), %edi
	movl	%edi, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	192(%rsp), %edi
	movl	160(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	156(%rsp), %edi
	movl	%edi, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	196(%rsp), %edi
	movl	164(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	160(%rsp), %edi
	movl	%edi, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	200(%rsp), %edi
	movl	168(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	164(%rsp), %edi
	movl	%edi, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	204(%rsp), %edi
	movl	172(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	168(%rsp), %edi
	movl	%edi, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	208(%rsp), %edi
	movl	176(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	172(%rsp), %edi
	movl	%edi, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	212(%rsp), %edi
	movl	180(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	176(%rsp), %edi
	movl	%edi, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	216(%rsp), %edi
	movl	184(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	180(%rsp), %edi
	movl	%edi, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	220(%rsp), %edi
	movl	188(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	184(%rsp), %edi
	movl	%edi, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	224(%rsp), %edi
	movl	192(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	188(%rsp), %edi
	movl	%edi, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	228(%rsp), %edi
	movl	196(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	192(%rsp), %edi
	movl	%edi, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	232(%rsp), %edi
	movl	200(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	196(%rsp), %edi
	movl	%edi, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	236(%rsp), %edi
	movl	204(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	200(%rsp), %edi
	movl	%edi, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	240(%rsp), %edi
	movl	208(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	204(%rsp), %edi
	movl	%edi, 268(%rsp)
	movl	264(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	244(%rsp), %edi
	movl	212(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	208(%rsp), %edi
	movl	%edi, 272(%rsp)
	movl	268(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	248(%rsp), %edi
	movl	216(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	212(%rsp), %edi
	movl	%edi, 276(%rsp)
	movl	272(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	252(%rsp), %edi
	movl	220(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	216(%rsp), %edi
	movl	%edi, 280(%rsp)
	movl	276(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	256(%rsp), %edi
	movl	224(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	220(%rsp), %edi
	movl	%edi, 284(%rsp)
	movl	(%rdx), %r12d
	movl	4(%rdx), %esi
	movl	8(%rdx), %edi
	movl	12(%rdx), %r8d
	movl	16(%rdx), %ebp
	movl	20(%rdx), %r9d
	movl	24(%rdx), %r10d
	movl	28(%rdx), %r13d
	movq	%rdx, 24(%rsp)
	movq	$0, %rdx
	jmp 	Lhash_plen_2n___blocks_0_ref_array$4
Lhash_plen_2n___blocks_0_ref_array$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r9d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rax,%rdx,4), %r11d
	addl	32(%rsp,%rdx,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%esi, %r13d
	movl	%r12d, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	movl	%esi, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r9d, %r10d
	movl	%ebp, %r9d
	movl	%r8d, %ebp
	addl	%r11d, %ebp
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r12d, %esi
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rdx
Lhash_plen_2n___blocks_0_ref_array$4:
	cmpq	$64, %rdx
	jb  	Lhash_plen_2n___blocks_0_ref_array$5
	movq	24(%rsp), %rdx
	addl	(%rdx), %r12d
	addl	4(%rdx), %esi
	addl	8(%rdx), %edi
	addl	12(%rdx), %r8d
	addl	16(%rdx), %ebp
	addl	20(%rdx), %r9d
	addl	24(%rdx), %r10d
	addl	28(%rdx), %r13d
	movl	%r12d, (%rdx)
	movl	%esi, 4(%rdx)
	movl	%edi, 8(%rdx)
	movl	%r8d, 12(%rdx)
	movl	%ebp, 16(%rdx)
	movl	%r9d, 20(%rdx)
	movl	%r10d, 24(%rdx)
	movl	%r13d, 28(%rdx)
	movq	16(%rsp), %rsi
	movq	8(%rsp), %rdi
	addq	$64, %rsi
	addq	$-64, %rdi
Lhash_plen_2n___blocks_0_ref_array$2:
	cmpq	$64, %rdi
	jnb 	Lhash_plen_2n___blocks_0_ref_array$3
	ret
L_blocks_0_ref$1:
	leaq	glob_data + 0(%rip), %rax
	movq	%rdx, 8(%rsp)
	movq	8(%rsp), %rdx
	jmp 	L_blocks_0_ref$2
L_blocks_0_ref$3:
	movl	(%rcx), %esi
	bswapl	%esi
	movl	%esi, 24(%rsp)
	movl	4(%rcx), %esi
	bswapl	%esi
	movl	%esi, 28(%rsp)
	movl	8(%rcx), %esi
	bswapl	%esi
	movl	%esi, 32(%rsp)
	movl	12(%rcx), %esi
	bswapl	%esi
	movl	%esi, 36(%rsp)
	movl	16(%rcx), %esi
	bswapl	%esi
	movl	%esi, 40(%rsp)
	movl	20(%rcx), %esi
	bswapl	%esi
	movl	%esi, 44(%rsp)
	movl	24(%rcx), %esi
	bswapl	%esi
	movl	%esi, 48(%rsp)
	movl	28(%rcx), %esi
	bswapl	%esi
	movl	%esi, 52(%rsp)
	movl	32(%rcx), %esi
	bswapl	%esi
	movl	%esi, 56(%rsp)
	movl	36(%rcx), %esi
	bswapl	%esi
	movl	%esi, 60(%rsp)
	movl	40(%rcx), %esi
	bswapl	%esi
	movl	%esi, 64(%rsp)
	movl	44(%rcx), %esi
	bswapl	%esi
	movl	%esi, 68(%rsp)
	movl	48(%rcx), %esi
	bswapl	%esi
	movl	%esi, 72(%rsp)
	movl	52(%rcx), %esi
	bswapl	%esi
	movl	%esi, 76(%rsp)
	movl	56(%rcx), %esi
	bswapl	%esi
	movl	%esi, 80(%rsp)
	movl	60(%rcx), %esi
	bswapl	%esi
	movl	%esi, 84(%rsp)
	movq	%rcx, 8(%rsp)
	movl	80(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	60(%rsp), %esi
	movl	28(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	24(%rsp), %esi
	movl	%esi, 88(%rsp)
	movl	84(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	64(%rsp), %esi
	movl	32(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	28(%rsp), %esi
	movl	%esi, 92(%rsp)
	movl	88(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	68(%rsp), %esi
	movl	36(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	32(%rsp), %esi
	movl	%esi, 96(%rsp)
	movl	92(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	72(%rsp), %esi
	movl	40(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	36(%rsp), %esi
	movl	%esi, 100(%rsp)
	movl	96(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	76(%rsp), %esi
	movl	44(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	40(%rsp), %esi
	movl	%esi, 104(%rsp)
	movl	100(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	80(%rsp), %esi
	movl	48(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	44(%rsp), %esi
	movl	%esi, 108(%rsp)
	movl	104(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	84(%rsp), %esi
	movl	52(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	48(%rsp), %esi
	movl	%esi, 112(%rsp)
	movl	108(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	88(%rsp), %esi
	movl	56(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	52(%rsp), %esi
	movl	%esi, 116(%rsp)
	movl	112(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	92(%rsp), %esi
	movl	60(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	56(%rsp), %esi
	movl	%esi, 120(%rsp)
	movl	116(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	96(%rsp), %esi
	movl	64(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	60(%rsp), %esi
	movl	%esi, 124(%rsp)
	movl	120(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	100(%rsp), %esi
	movl	68(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	64(%rsp), %esi
	movl	%esi, 128(%rsp)
	movl	124(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	104(%rsp), %esi
	movl	72(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	68(%rsp), %esi
	movl	%esi, 132(%rsp)
	movl	128(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	108(%rsp), %esi
	movl	76(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	72(%rsp), %esi
	movl	%esi, 136(%rsp)
	movl	132(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	112(%rsp), %esi
	movl	80(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	76(%rsp), %esi
	movl	%esi, 140(%rsp)
	movl	136(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	116(%rsp), %esi
	movl	84(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	80(%rsp), %esi
	movl	%esi, 144(%rsp)
	movl	140(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	120(%rsp), %esi
	movl	88(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	84(%rsp), %esi
	movl	%esi, 148(%rsp)
	movl	144(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	124(%rsp), %esi
	movl	92(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	88(%rsp), %esi
	movl	%esi, 152(%rsp)
	movl	148(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	128(%rsp), %esi
	movl	96(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	92(%rsp), %esi
	movl	%esi, 156(%rsp)
	movl	152(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	132(%rsp), %esi
	movl	100(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	96(%rsp), %esi
	movl	%esi, 160(%rsp)
	movl	156(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	136(%rsp), %esi
	movl	104(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	100(%rsp), %esi
	movl	%esi, 164(%rsp)
	movl	160(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	140(%rsp), %esi
	movl	108(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	104(%rsp), %esi
	movl	%esi, 168(%rsp)
	movl	164(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	144(%rsp), %esi
	movl	112(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	108(%rsp), %esi
	movl	%esi, 172(%rsp)
	movl	168(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	148(%rsp), %esi
	movl	116(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	112(%rsp), %esi
	movl	%esi, 176(%rsp)
	movl	172(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	152(%rsp), %esi
	movl	120(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	116(%rsp), %esi
	movl	%esi, 180(%rsp)
	movl	176(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	156(%rsp), %esi
	movl	124(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	120(%rsp), %esi
	movl	%esi, 184(%rsp)
	movl	180(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	160(%rsp), %esi
	movl	128(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	124(%rsp), %esi
	movl	%esi, 188(%rsp)
	movl	184(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	164(%rsp), %esi
	movl	132(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	128(%rsp), %esi
	movl	%esi, 192(%rsp)
	movl	188(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	168(%rsp), %esi
	movl	136(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	132(%rsp), %esi
	movl	%esi, 196(%rsp)
	movl	192(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	172(%rsp), %esi
	movl	140(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	136(%rsp), %esi
	movl	%esi, 200(%rsp)
	movl	196(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	176(%rsp), %esi
	movl	144(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	140(%rsp), %esi
	movl	%esi, 204(%rsp)
	movl	200(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	180(%rsp), %esi
	movl	148(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	144(%rsp), %esi
	movl	%esi, 208(%rsp)
	movl	204(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	184(%rsp), %esi
	movl	152(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	148(%rsp), %esi
	movl	%esi, 212(%rsp)
	movl	208(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	188(%rsp), %esi
	movl	156(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	152(%rsp), %esi
	movl	%esi, 216(%rsp)
	movl	212(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	192(%rsp), %esi
	movl	160(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	156(%rsp), %esi
	movl	%esi, 220(%rsp)
	movl	216(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	196(%rsp), %esi
	movl	164(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	160(%rsp), %esi
	movl	%esi, 224(%rsp)
	movl	220(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	200(%rsp), %esi
	movl	168(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	164(%rsp), %esi
	movl	%esi, 228(%rsp)
	movl	224(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	204(%rsp), %esi
	movl	172(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	168(%rsp), %esi
	movl	%esi, 232(%rsp)
	movl	228(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	208(%rsp), %esi
	movl	176(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	172(%rsp), %esi
	movl	%esi, 236(%rsp)
	movl	232(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	212(%rsp), %esi
	movl	180(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	176(%rsp), %esi
	movl	%esi, 240(%rsp)
	movl	236(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	216(%rsp), %esi
	movl	184(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	180(%rsp), %esi
	movl	%esi, 244(%rsp)
	movl	240(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	220(%rsp), %esi
	movl	188(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	184(%rsp), %esi
	movl	%esi, 248(%rsp)
	movl	244(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	224(%rsp), %esi
	movl	192(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	188(%rsp), %esi
	movl	%esi, 252(%rsp)
	movl	248(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	228(%rsp), %esi
	movl	196(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	192(%rsp), %esi
	movl	%esi, 256(%rsp)
	movl	252(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	232(%rsp), %esi
	movl	200(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	196(%rsp), %esi
	movl	%esi, 260(%rsp)
	movl	256(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	236(%rsp), %esi
	movl	204(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	200(%rsp), %esi
	movl	%esi, 264(%rsp)
	movl	260(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	240(%rsp), %esi
	movl	208(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	204(%rsp), %esi
	movl	%esi, 268(%rsp)
	movl	264(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	244(%rsp), %esi
	movl	212(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	208(%rsp), %esi
	movl	%esi, 272(%rsp)
	movl	268(%rsp), %ecx
	movl	%ecx, %esi
	rorl	$17, %esi
	movl	%ecx, %edi
	rorl	$19, %edi
	xorl	%edi, %esi
	shrl	$10, %ecx
	xorl	%ecx, %esi
	addl	248(%rsp), %esi
	movl	216(%rsp), %ecx
	movl	%ecx, %edi
	rorl	$7, %edi
	movl	%ecx, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %ecx
	xorl	%ecx, %edi
	addl	%edi, %esi
	addl	212(%rsp), %esi
	movl	%esi, 276(%rsp)
	movl	(%rdx), %r12d
	movl	4(%rdx), %ecx
	movl	8(%rdx), %esi
	movl	12(%rdx), %edi
	movl	16(%rdx), %ebp
	movl	20(%rdx), %r8d
	movl	24(%rdx), %r10d
	movl	28(%rdx), %r13d
	movq	%rdx, 16(%rsp)
	movq	$0, %rdx
	jmp 	L_blocks_0_ref$4
L_blocks_0_ref$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r8d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rax,%rdx,4), %r11d
	addl	24(%rsp,%rdx,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%ecx, %r13d
	movl	%r12d, %r14d
	andl	%esi, %r14d
	xorl	%r14d, %r13d
	movl	%ecx, %r14d
	andl	%esi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r8d, %r10d
	movl	%ebp, %r8d
	movl	%edi, %ebp
	addl	%r11d, %ebp
	movl	%esi, %edi
	movl	%ecx, %esi
	movl	%r12d, %ecx
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rdx
L_blocks_0_ref$4:
	cmpq	$64, %rdx
	jb  	L_blocks_0_ref$5
	movq	16(%rsp), %rdx
	addl	(%rdx), %r12d
	addl	4(%rdx), %ecx
	addl	8(%rdx), %esi
	addl	12(%rdx), %edi
	addl	16(%rdx), %ebp
	addl	20(%rdx), %r8d
	addl	24(%rdx), %r10d
	addl	28(%rdx), %r13d
	movl	%r12d, (%rdx)
	movl	%ecx, 4(%rdx)
	movl	%esi, 8(%rdx)
	movl	%edi, 12(%rdx)
	movl	%ebp, 16(%rdx)
	movl	%r8d, 20(%rdx)
	movl	%r10d, 24(%rdx)
	movl	%r13d, 28(%rdx)
	movq	8(%rsp), %rcx
	addq	$64, %rcx
	addq	$-64, %r9
L_blocks_0_ref$2:
	cmpq	$64, %r9
	jnb 	L_blocks_0_ref$3
	ret
L_blocks_1_ref$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%rdx, 8(%rsp)
	movq	$0, %rdx
	movq	8(%rsp), %rsi
	jmp 	L_blocks_1_ref$2
L_blocks_1_ref$3:
	movq	%rdx, 8(%rsp)
	shlq	$4, %rdx
	movl	(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 32(%rsp)
	movl	4(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 36(%rsp)
	movl	8(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 40(%rsp)
	movl	12(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 44(%rsp)
	movl	16(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 48(%rsp)
	movl	20(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 52(%rsp)
	movl	24(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 56(%rsp)
	movl	28(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 60(%rsp)
	movl	32(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 64(%rsp)
	movl	36(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 68(%rsp)
	movl	40(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 72(%rsp)
	movl	44(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 76(%rsp)
	movl	48(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 80(%rsp)
	movl	52(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 84(%rsp)
	movl	56(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 88(%rsp)
	movl	60(%rdi,%rdx,4), %edx
	bswapl	%edx
	movl	%edx, 92(%rsp)
	movq	%rdi, 16(%rsp)
	movl	88(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	68(%rsp), %edi
	movl	36(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	32(%rsp), %edi
	movl	%edi, 96(%rsp)
	movl	92(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	72(%rsp), %edi
	movl	40(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	36(%rsp), %edi
	movl	%edi, 100(%rsp)
	movl	96(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	76(%rsp), %edi
	movl	44(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	40(%rsp), %edi
	movl	%edi, 104(%rsp)
	movl	100(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	80(%rsp), %edi
	movl	48(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	44(%rsp), %edi
	movl	%edi, 108(%rsp)
	movl	104(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	84(%rsp), %edi
	movl	52(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	48(%rsp), %edi
	movl	%edi, 112(%rsp)
	movl	108(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	88(%rsp), %edi
	movl	56(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	52(%rsp), %edi
	movl	%edi, 116(%rsp)
	movl	112(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	92(%rsp), %edi
	movl	60(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	56(%rsp), %edi
	movl	%edi, 120(%rsp)
	movl	116(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	96(%rsp), %edi
	movl	64(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	60(%rsp), %edi
	movl	%edi, 124(%rsp)
	movl	120(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	100(%rsp), %edi
	movl	68(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	64(%rsp), %edi
	movl	%edi, 128(%rsp)
	movl	124(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	104(%rsp), %edi
	movl	72(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	68(%rsp), %edi
	movl	%edi, 132(%rsp)
	movl	128(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	108(%rsp), %edi
	movl	76(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	72(%rsp), %edi
	movl	%edi, 136(%rsp)
	movl	132(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	112(%rsp), %edi
	movl	80(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	76(%rsp), %edi
	movl	%edi, 140(%rsp)
	movl	136(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	116(%rsp), %edi
	movl	84(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	80(%rsp), %edi
	movl	%edi, 144(%rsp)
	movl	140(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	120(%rsp), %edi
	movl	88(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	84(%rsp), %edi
	movl	%edi, 148(%rsp)
	movl	144(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	124(%rsp), %edi
	movl	92(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	88(%rsp), %edi
	movl	%edi, 152(%rsp)
	movl	148(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	128(%rsp), %edi
	movl	96(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	92(%rsp), %edi
	movl	%edi, 156(%rsp)
	movl	152(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	132(%rsp), %edi
	movl	100(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	96(%rsp), %edi
	movl	%edi, 160(%rsp)
	movl	156(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	136(%rsp), %edi
	movl	104(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	100(%rsp), %edi
	movl	%edi, 164(%rsp)
	movl	160(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	140(%rsp), %edi
	movl	108(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	104(%rsp), %edi
	movl	%edi, 168(%rsp)
	movl	164(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	144(%rsp), %edi
	movl	112(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	108(%rsp), %edi
	movl	%edi, 172(%rsp)
	movl	168(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	148(%rsp), %edi
	movl	116(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	112(%rsp), %edi
	movl	%edi, 176(%rsp)
	movl	172(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	152(%rsp), %edi
	movl	120(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	116(%rsp), %edi
	movl	%edi, 180(%rsp)
	movl	176(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	156(%rsp), %edi
	movl	124(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	120(%rsp), %edi
	movl	%edi, 184(%rsp)
	movl	180(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	160(%rsp), %edi
	movl	128(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	124(%rsp), %edi
	movl	%edi, 188(%rsp)
	movl	184(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	164(%rsp), %edi
	movl	132(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	128(%rsp), %edi
	movl	%edi, 192(%rsp)
	movl	188(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	168(%rsp), %edi
	movl	136(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	132(%rsp), %edi
	movl	%edi, 196(%rsp)
	movl	192(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	172(%rsp), %edi
	movl	140(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	136(%rsp), %edi
	movl	%edi, 200(%rsp)
	movl	196(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	176(%rsp), %edi
	movl	144(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	140(%rsp), %edi
	movl	%edi, 204(%rsp)
	movl	200(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	180(%rsp), %edi
	movl	148(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	144(%rsp), %edi
	movl	%edi, 208(%rsp)
	movl	204(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	184(%rsp), %edi
	movl	152(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	148(%rsp), %edi
	movl	%edi, 212(%rsp)
	movl	208(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	188(%rsp), %edi
	movl	156(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	152(%rsp), %edi
	movl	%edi, 216(%rsp)
	movl	212(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	192(%rsp), %edi
	movl	160(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	156(%rsp), %edi
	movl	%edi, 220(%rsp)
	movl	216(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	196(%rsp), %edi
	movl	164(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	160(%rsp), %edi
	movl	%edi, 224(%rsp)
	movl	220(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	200(%rsp), %edi
	movl	168(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	164(%rsp), %edi
	movl	%edi, 228(%rsp)
	movl	224(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	204(%rsp), %edi
	movl	172(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	168(%rsp), %edi
	movl	%edi, 232(%rsp)
	movl	228(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	208(%rsp), %edi
	movl	176(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	172(%rsp), %edi
	movl	%edi, 236(%rsp)
	movl	232(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	212(%rsp), %edi
	movl	180(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	176(%rsp), %edi
	movl	%edi, 240(%rsp)
	movl	236(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	216(%rsp), %edi
	movl	184(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	180(%rsp), %edi
	movl	%edi, 244(%rsp)
	movl	240(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	220(%rsp), %edi
	movl	188(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	184(%rsp), %edi
	movl	%edi, 248(%rsp)
	movl	244(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	224(%rsp), %edi
	movl	192(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	188(%rsp), %edi
	movl	%edi, 252(%rsp)
	movl	248(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	228(%rsp), %edi
	movl	196(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	192(%rsp), %edi
	movl	%edi, 256(%rsp)
	movl	252(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	232(%rsp), %edi
	movl	200(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	196(%rsp), %edi
	movl	%edi, 260(%rsp)
	movl	256(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	236(%rsp), %edi
	movl	204(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	200(%rsp), %edi
	movl	%edi, 264(%rsp)
	movl	260(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	240(%rsp), %edi
	movl	208(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	204(%rsp), %edi
	movl	%edi, 268(%rsp)
	movl	264(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	244(%rsp), %edi
	movl	212(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	208(%rsp), %edi
	movl	%edi, 272(%rsp)
	movl	268(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	248(%rsp), %edi
	movl	216(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	212(%rsp), %edi
	movl	%edi, 276(%rsp)
	movl	272(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	252(%rsp), %edi
	movl	220(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	216(%rsp), %edi
	movl	%edi, 280(%rsp)
	movl	276(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	256(%rsp), %edi
	movl	224(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	220(%rsp), %edi
	movl	%edi, 284(%rsp)
	movl	(%rsi), %r12d
	movl	4(%rsi), %edx
	movl	8(%rsi), %edi
	movl	12(%rsi), %r8d
	movl	16(%rsi), %ebp
	movl	20(%rsi), %r9d
	movl	24(%rsi), %r10d
	movl	28(%rsi), %r13d
	movq	%rsi, 24(%rsp)
	movq	$0, %rsi
	jmp 	L_blocks_1_ref$4
L_blocks_1_ref$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r9d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rcx,%rsi,4), %r11d
	addl	32(%rsp,%rsi,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%edx, %r13d
	movl	%r12d, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	movl	%edx, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r9d, %r10d
	movl	%ebp, %r9d
	movl	%r8d, %ebp
	addl	%r11d, %ebp
	movl	%edi, %r8d
	movl	%edx, %edi
	movl	%r12d, %edx
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rsi
L_blocks_1_ref$4:
	cmpq	$64, %rsi
	jb  	L_blocks_1_ref$5
	movq	24(%rsp), %rsi
	addl	(%rsi), %r12d
	addl	4(%rsi), %edx
	addl	8(%rsi), %edi
	addl	12(%rsi), %r8d
	addl	16(%rsi), %ebp
	addl	20(%rsi), %r9d
	addl	24(%rsi), %r10d
	addl	28(%rsi), %r13d
	movl	%r12d, (%rsi)
	movl	%edx, 4(%rsi)
	movl	%edi, 8(%rsi)
	movl	%r8d, 12(%rsi)
	movl	%ebp, 16(%rsi)
	movl	%r9d, 20(%rsi)
	movl	%r10d, 24(%rsi)
	movl	%r13d, 28(%rsi)
	movq	16(%rsp), %rdi
	movq	8(%rsp), %rdx
	incq	%rdx
L_blocks_1_ref$2:
	cmpq	%rax, %rdx
	jb  	L_blocks_1_ref$3
	ret
Lcopy_nbytes$1:
	movq	(%r8), %rdx
	movq	%rdx, (%rcx)
	movq	8(%r8), %rdx
	movq	%rdx, 8(%rcx)
	movq	16(%r8), %rdx
	movq	%rdx, 16(%rcx)
	movq	24(%r8), %rdx
	movq	%rdx, 24(%rcx)
	ret
Lmemcpy_u8pu8_plen___memcpy_u8pu8$1:
	movq	(%rax), %r10
	movq	%r10, (%r8,%r11)
	addq	$8, %r11
	movq	8(%rax), %r10
	movq	%r10, (%r8,%r11)
	addq	$8, %r11
	movq	16(%rax), %r10
	movq	%r10, (%r8,%r11)
	addq	$8, %r11
	movq	24(%rax), %rax
	movq	%rax, (%r8,%r11)
	ret
Lmemcpy_u8pu8_n___memcpy_u8pu8$1:
	movq	(%rcx), %rdx
	movq	%rdx, (%rax,%rsi)
	addq	$8, %rsi
	movq	8(%rcx), %rdx
	movq	%rdx, (%rax,%rsi)
	addq	$8, %rsi
	movq	16(%rcx), %rdx
	movq	%rdx, (%rax,%rsi)
	addq	$8, %rsi
	movq	24(%rcx), %rcx
	movq	%rcx, (%rax,%rsi)
	ret
	.data
	.p2align	5
_glob_data:
glob_data:
G$SHA256_K:
	.byte	-104
	.byte	47
	.byte	-118
	.byte	66
	.byte	-111
	.byte	68
	.byte	55
	.byte	113
	.byte	-49
	.byte	-5
	.byte	-64
	.byte	-75
	.byte	-91
	.byte	-37
	.byte	-75
	.byte	-23
	.byte	91
	.byte	-62
	.byte	86
	.byte	57
	.byte	-15
	.byte	17
	.byte	-15
	.byte	89
	.byte	-92
	.byte	-126
	.byte	63
	.byte	-110
	.byte	-43
	.byte	94
	.byte	28
	.byte	-85
	.byte	-104
	.byte	-86
	.byte	7
	.byte	-40
	.byte	1
	.byte	91
	.byte	-125
	.byte	18
	.byte	-66
	.byte	-123
	.byte	49
	.byte	36
	.byte	-61
	.byte	125
	.byte	12
	.byte	85
	.byte	116
	.byte	93
	.byte	-66
	.byte	114
	.byte	-2
	.byte	-79
	.byte	-34
	.byte	-128
	.byte	-89
	.byte	6
	.byte	-36
	.byte	-101
	.byte	116
	.byte	-15
	.byte	-101
	.byte	-63
	.byte	-63
	.byte	105
	.byte	-101
	.byte	-28
	.byte	-122
	.byte	71
	.byte	-66
	.byte	-17
	.byte	-58
	.byte	-99
	.byte	-63
	.byte	15
	.byte	-52
	.byte	-95
	.byte	12
	.byte	36
	.byte	111
	.byte	44
	.byte	-23
	.byte	45
	.byte	-86
	.byte	-124
	.byte	116
	.byte	74
	.byte	-36
	.byte	-87
	.byte	-80
	.byte	92
	.byte	-38
	.byte	-120
	.byte	-7
	.byte	118
	.byte	82
	.byte	81
	.byte	62
	.byte	-104
	.byte	109
	.byte	-58
	.byte	49
	.byte	-88
	.byte	-56
	.byte	39
	.byte	3
	.byte	-80
	.byte	-57
	.byte	127
	.byte	89
	.byte	-65
	.byte	-13
	.byte	11
	.byte	-32
	.byte	-58
	.byte	71
	.byte	-111
	.byte	-89
	.byte	-43
	.byte	81
	.byte	99
	.byte	-54
	.byte	6
	.byte	103
	.byte	41
	.byte	41
	.byte	20
	.byte	-123
	.byte	10
	.byte	-73
	.byte	39
	.byte	56
	.byte	33
	.byte	27
	.byte	46
	.byte	-4
	.byte	109
	.byte	44
	.byte	77
	.byte	19
	.byte	13
	.byte	56
	.byte	83
	.byte	84
	.byte	115
	.byte	10
	.byte	101
	.byte	-69
	.byte	10
	.byte	106
	.byte	118
	.byte	46
	.byte	-55
	.byte	-62
	.byte	-127
	.byte	-123
	.byte	44
	.byte	114
	.byte	-110
	.byte	-95
	.byte	-24
	.byte	-65
	.byte	-94
	.byte	75
	.byte	102
	.byte	26
	.byte	-88
	.byte	112
	.byte	-117
	.byte	75
	.byte	-62
	.byte	-93
	.byte	81
	.byte	108
	.byte	-57
	.byte	25
	.byte	-24
	.byte	-110
	.byte	-47
	.byte	36
	.byte	6
	.byte	-103
	.byte	-42
	.byte	-123
	.byte	53
	.byte	14
	.byte	-12
	.byte	112
	.byte	-96
	.byte	106
	.byte	16
	.byte	22
	.byte	-63
	.byte	-92
	.byte	25
	.byte	8
	.byte	108
	.byte	55
	.byte	30
	.byte	76
	.byte	119
	.byte	72
	.byte	39
	.byte	-75
	.byte	-68
	.byte	-80
	.byte	52
	.byte	-77
	.byte	12
	.byte	28
	.byte	57
	.byte	74
	.byte	-86
	.byte	-40
	.byte	78
	.byte	79
	.byte	-54
	.byte	-100
	.byte	91
	.byte	-13
	.byte	111
	.byte	46
	.byte	104
	.byte	-18
	.byte	-126
	.byte	-113
	.byte	116
	.byte	111
	.byte	99
	.byte	-91
	.byte	120
	.byte	20
	.byte	120
	.byte	-56
	.byte	-124
	.byte	8
	.byte	2
	.byte	-57
	.byte	-116
	.byte	-6
	.byte	-1
	.byte	-66
	.byte	-112
	.byte	-21
	.byte	108
	.byte	80
	.byte	-92
	.byte	-9
	.byte	-93
	.byte	-7
	.byte	-66
	.byte	-14
	.byte	120
	.byte	113
	.byte	-58
