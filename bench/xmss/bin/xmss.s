	.att_syntax
	.text
	.p2align	5
	.globl	_xmssmt_sign_open_jazz
	.globl	xmssmt_sign_open_jazz
	.globl	_xmssmt_keypair_jazz
	.globl	xmssmt_keypair_jazz
_xmssmt_sign_open_jazz:
xmssmt_sign_open_jazz:
	movq	%rsp, %rax
	leaq	-56(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r15, 40(%rsp)
	movq	%rax, 48(%rsp)
	leaq	4(%r8), %rax
	movq	%rdx, %r8
	movq	%rax, %rdx
	leaq	-2376(%rsp), %rsp
	call	L_xmssmt_core_sign_open$1
Lxmssmt_sign_open_jazz$1:
	leaq	2376(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret
_xmssmt_keypair_jazz:
xmssmt_keypair_jazz:
	movq	%rsp, %rax
	leaq	-56(%rsp), %rsp
	andq	$-16, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r15, 40(%rsp)
	movq	%rax, 48(%rsp)
	movl	$1, %eax
	bswapl	%eax
	movl	%eax, (%rdi)
	movl	%eax, (%rsi)
	leaq	4(%rdi), %rbx
	leaq	4(%rsi), %rbp
	leaq	-792(%rsp), %rsp
	call	L_xmssmt_core_keypair$1
Lxmssmt_keypair_jazz$1:
	leaq	792(%rsp), %rsp
	xorq	%rax, %rax
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret
L_xmssmt_core_keypair$1:
	leaq	696(%rsp), %rdi
	movq	$96, %rsi
	call	__jasmin_syscall_randombytes__
	leaq	64(%rsp), %rcx
	movq	%rcx, %r9
	call	L_zero_address$1
L_xmssmt_core_keypair$17:
	leaq	64(%rsp), %rcx
	movl	$1, %edx
	movl	%edx, (%rcx)
	movq	%rbp, %rcx
	movq	$0, %rdx
	jmp 	L_xmssmt_core_keypair$15
L_xmssmt_core_keypair$16:
	movb	$0, (%rcx,%rdx)
	incq	%rdx
L_xmssmt_core_keypair$15:
	cmpq	$3, %rdx
	jb  	L_xmssmt_core_keypair$16
	leaq	3(%rbp), %rcx
	movq	%rax, %rdx
	call	Lmemcpy_u8u8_2N___memcpy_u8u8$1
L_xmssmt_core_keypair$14:
	leaq	99(%rbp), %rcx
	leaq	64(%rax), %rax
	movq	%rcx, %rdi
	movq	%rax, %rsi
	call	Lmemcpy_u8u8_N___memcpy_u8u8$1
L_xmssmt_core_keypair$13:
	leaq	32(%rbx), %rax
	leaq	99(%rbp), %rcx
	movq	%rax, %rdi
	movq	%rcx, %rsi
	call	Lmemcpy_u8u8_N___memcpy_u8u8$1
L_xmssmt_core_keypair$12:
	leaq	3(%rbp), %rdx
	leaq	32(%rbx), %rsi
	movq	%rbx, 8(%rsp)
	movq	%rbp, 16(%rsp)
	leaq	96(%rsp), %rdi
	movl	$0, %r8d
	movl	$10, %ecx
	leaq	64(%rsp), %rax
	movq	$0, %r9
	movq	%rdi, 24(%rsp)
	movq	%r9, 32(%rsp)
	movl	%r8d, 640(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rsi, 48(%rsp)
	movq	(%rax), %rdx
	movq	%rdx, 128(%rsp)
	movq	8(%rax), %rdx
	movq	%rdx, 136(%rsp)
	movq	16(%rax), %rdx
	movq	%rdx, 144(%rsp)
	movq	24(%rax), %rdx
	movq	%rdx, 152(%rsp)
	movq	(%rax), %rdx
	movq	%rdx, 160(%rsp)
	movq	8(%rax), %rdx
	movq	%rdx, 168(%rsp)
	movq	16(%rax), %rdx
	movq	%rdx, 176(%rsp)
	movq	24(%rax), %rdx
	movq	%rdx, 184(%rsp)
	movq	(%rax), %rdx
	movq	%rdx, 192(%rsp)
	movq	8(%rax), %rdx
	movq	%rdx, 200(%rsp)
	movq	16(%rax), %rdx
	movq	%rdx, 208(%rsp)
	movq	24(%rax), %rax
	movq	%rax, 216(%rsp)
	leaq	128(%rsp), %rax
	movl	$0, %edx
	movl	%edx, 12(%rax)
	leaq	160(%rsp), %rax
	movl	$1, %edx
	movl	%edx, 12(%rax)
	leaq	192(%rsp), %rax
	movl	$2, %edx
	movl	%edx, 12(%rax)
	movl	$0, %edx
	movl	$1, %eax
	shll	%cl, %eax
	jmp 	L_xmssmt_core_keypair$2
L_xmssmt_core_keypair$3:
	movl	%edx, 644(%rsp)
	movl	%eax, 648(%rsp)
	movl	640(%rsp), %eax
	addl	%edx, %eax
	leaq	160(%rsp), %rcx
	movl	%eax, 16(%rcx)
	leaq	128(%rsp), %rcx
	movl	%eax, 16(%rcx)
	movq	40(%rsp), %rax
	movq	48(%rsp), %rcx
	leaq	64(%rsp), %rdx
	leaq	160(%rsp), %rsi
	leaq	128(%rsp), %rdi
	leaq	-2184(%rsp), %rsp
	call	L_gen_leaf_wots$1
L_xmssmt_core_keypair$11:
	leaq	2184(%rsp), %rsp
	movq	32(%rsp), %rax
	shlq	$5, %rax
	leaq	288(%rsp), %rcx
	leaq	64(%rsp), %rdx
	movb	(%rdx), %sil
	movb	%sil, (%rcx,%rax)
	movb	1(%rdx), %sil
	movb	%sil, 1(%rcx,%rax)
	movb	2(%rdx), %sil
	movb	%sil, 2(%rcx,%rax)
	movb	3(%rdx), %sil
	movb	%sil, 3(%rcx,%rax)
	movb	4(%rdx), %sil
	movb	%sil, 4(%rcx,%rax)
	movb	5(%rdx), %sil
	movb	%sil, 5(%rcx,%rax)
	movb	6(%rdx), %sil
	movb	%sil, 6(%rcx,%rax)
	movb	7(%rdx), %sil
	movb	%sil, 7(%rcx,%rax)
	movb	8(%rdx), %sil
	movb	%sil, 8(%rcx,%rax)
	movb	9(%rdx), %sil
	movb	%sil, 9(%rcx,%rax)
	movb	10(%rdx), %sil
	movb	%sil, 10(%rcx,%rax)
	movb	11(%rdx), %sil
	movb	%sil, 11(%rcx,%rax)
	movb	12(%rdx), %sil
	movb	%sil, 12(%rcx,%rax)
	movb	13(%rdx), %sil
	movb	%sil, 13(%rcx,%rax)
	movb	14(%rdx), %sil
	movb	%sil, 14(%rcx,%rax)
	movb	15(%rdx), %sil
	movb	%sil, 15(%rcx,%rax)
	movb	16(%rdx), %sil
	movb	%sil, 16(%rcx,%rax)
	movb	17(%rdx), %sil
	movb	%sil, 17(%rcx,%rax)
	movb	18(%rdx), %sil
	movb	%sil, 18(%rcx,%rax)
	movb	19(%rdx), %sil
	movb	%sil, 19(%rcx,%rax)
	movb	20(%rdx), %sil
	movb	%sil, 20(%rcx,%rax)
	movb	21(%rdx), %sil
	movb	%sil, 21(%rcx,%rax)
	movb	22(%rdx), %sil
	movb	%sil, 22(%rcx,%rax)
	movb	23(%rdx), %sil
	movb	%sil, 23(%rcx,%rax)
	movb	24(%rdx), %sil
	movb	%sil, 24(%rcx,%rax)
	movb	25(%rdx), %sil
	movb	%sil, 25(%rcx,%rax)
	movb	26(%rdx), %sil
	movb	%sil, 26(%rcx,%rax)
	movb	27(%rdx), %sil
	movb	%sil, 27(%rcx,%rax)
	movb	28(%rdx), %sil
	movb	%sil, 28(%rcx,%rax)
	movb	29(%rdx), %sil
	movb	%sil, 29(%rcx,%rax)
	movb	30(%rdx), %sil
	movb	%sil, 30(%rcx,%rax)
	movb	31(%rdx), %dl
	movb	%dl, 31(%rcx,%rax)
	movq	32(%rsp), %rax
	incq	%rax
	movl	$0, 648(%rsp,%rax,4)
	movq	%rax, 32(%rsp)
	jmp 	L_xmssmt_core_keypair$4
L_xmssmt_core_keypair$5:
	movl	640(%rsp), %ecx
	movl	644(%rsp), %edx
	movl	%ecx, %esi
	addl	%edx, %esi
	movl	648(%rsp,%rax,4), %ecx
	incl	%ecx
	shrl	%cl, %esi
	leaq	192(%rsp), %rcx
	movl	648(%rsp,%rax,4), %eax
	movl	%eax, 20(%rcx)
	leaq	192(%rsp), %rax
	movl	%esi, 24(%rax)
	movq	32(%rsp), %rax
	addq	$-2, %rax
	shlq	$5, %rax
	movq	%rax, 56(%rsp)
	leaq	224(%rsp), %rcx
	leaq	288(%rsp), %rdx
	movq	$64, %rsi
	movq	$0, %rdi
	jmp 	L_xmssmt_core_keypair$9
L_xmssmt_core_keypair$10:
	movb	(%rdx,%rax), %r8b
	movb	%r8b, (%rcx,%rdi)
	incq	%rdi
	incq	%rax
L_xmssmt_core_keypair$9:
	cmpq	%rsi, %rdi
	jb  	L_xmssmt_core_keypair$10
	movq	48(%rsp), %rsi
	leaq	64(%rsp), %rcx
	leaq	224(%rsp), %rdx
	leaq	192(%rsp), %rdi
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_xmssmt_core_keypair$8:
	leaq	384(%rsp), %rsp
	movq	56(%rsp), %rax
	leaq	288(%rsp), %rcx
	leaq	64(%rsp), %rdx
	movb	(%rdx), %sil
	movb	%sil, (%rcx,%rax)
	movb	1(%rdx), %sil
	movb	%sil, 1(%rcx,%rax)
	movb	2(%rdx), %sil
	movb	%sil, 2(%rcx,%rax)
	movb	3(%rdx), %sil
	movb	%sil, 3(%rcx,%rax)
	movb	4(%rdx), %sil
	movb	%sil, 4(%rcx,%rax)
	movb	5(%rdx), %sil
	movb	%sil, 5(%rcx,%rax)
	movb	6(%rdx), %sil
	movb	%sil, 6(%rcx,%rax)
	movb	7(%rdx), %sil
	movb	%sil, 7(%rcx,%rax)
	movb	8(%rdx), %sil
	movb	%sil, 8(%rcx,%rax)
	movb	9(%rdx), %sil
	movb	%sil, 9(%rcx,%rax)
	movb	10(%rdx), %sil
	movb	%sil, 10(%rcx,%rax)
	movb	11(%rdx), %sil
	movb	%sil, 11(%rcx,%rax)
	movb	12(%rdx), %sil
	movb	%sil, 12(%rcx,%rax)
	movb	13(%rdx), %sil
	movb	%sil, 13(%rcx,%rax)
	movb	14(%rdx), %sil
	movb	%sil, 14(%rcx,%rax)
	movb	15(%rdx), %sil
	movb	%sil, 15(%rcx,%rax)
	movb	16(%rdx), %sil
	movb	%sil, 16(%rcx,%rax)
	movb	17(%rdx), %sil
	movb	%sil, 17(%rcx,%rax)
	movb	18(%rdx), %sil
	movb	%sil, 18(%rcx,%rax)
	movb	19(%rdx), %sil
	movb	%sil, 19(%rcx,%rax)
	movb	20(%rdx), %sil
	movb	%sil, 20(%rcx,%rax)
	movb	21(%rdx), %sil
	movb	%sil, 21(%rcx,%rax)
	movb	22(%rdx), %sil
	movb	%sil, 22(%rcx,%rax)
	movb	23(%rdx), %sil
	movb	%sil, 23(%rcx,%rax)
	movb	24(%rdx), %sil
	movb	%sil, 24(%rcx,%rax)
	movb	25(%rdx), %sil
	movb	%sil, 25(%rcx,%rax)
	movb	26(%rdx), %sil
	movb	%sil, 26(%rcx,%rax)
	movb	27(%rdx), %sil
	movb	%sil, 27(%rcx,%rax)
	movb	28(%rdx), %sil
	movb	%sil, 28(%rcx,%rax)
	movb	29(%rdx), %sil
	movb	%sil, 29(%rcx,%rax)
	movb	30(%rdx), %sil
	movb	%sil, 30(%rcx,%rax)
	movb	31(%rdx), %dl
	movb	%dl, 31(%rcx,%rax)
	movq	32(%rsp), %rax
	addq	$-1, %rax
	incl	648(%rsp,%rax,4)
	movq	%rax, 32(%rsp)
L_xmssmt_core_keypair$4:
	leaq	652(%rsp), %rcx
	cmpq	$2, %rax
	setnb	%dl
	cmpb	$0, %dl
	je  	L_xmssmt_core_keypair$6
	movl	-4(%rcx,%rax,4), %edx
	movl	-8(%rcx,%rax,4), %ecx
	cmpl	%ecx, %edx
	sete	%cl
	jmp 	L_xmssmt_core_keypair$7
L_xmssmt_core_keypair$6:
	movb	%dl, %cl
L_xmssmt_core_keypair$7:
	cmpb	$1, %cl
	je  	L_xmssmt_core_keypair$5
	movl	644(%rsp), %edx
	movl	648(%rsp), %eax
	incl	%edx
L_xmssmt_core_keypair$2:
	cmpl	%eax, %edx
	jb  	L_xmssmt_core_keypair$3
	movq	24(%rsp), %rax
	movq	288(%rsp), %rcx
	movq	%rcx, (%rax)
	movq	296(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	304(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	312(%rsp), %rcx
	movq	%rcx, 24(%rax)
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	$0, %rdx
	leaq	96(%rsp), %rsi
	movq	$0, %rdi
	movb	(%rsi,%rdi), %r8b
	movb	%r8b, (%rax,%rdx)
	movb	1(%rsi,%rdi), %r8b
	movb	%r8b, 1(%rax,%rdx)
	movb	2(%rsi,%rdi), %r8b
	movb	%r8b, 2(%rax,%rdx)
	movb	3(%rsi,%rdi), %r8b
	movb	%r8b, 3(%rax,%rdx)
	movb	4(%rsi,%rdi), %r8b
	movb	%r8b, 4(%rax,%rdx)
	movb	5(%rsi,%rdi), %r8b
	movb	%r8b, 5(%rax,%rdx)
	movb	6(%rsi,%rdi), %r8b
	movb	%r8b, 6(%rax,%rdx)
	movb	7(%rsi,%rdi), %r8b
	movb	%r8b, 7(%rax,%rdx)
	movb	8(%rsi,%rdi), %r8b
	movb	%r8b, 8(%rax,%rdx)
	movb	9(%rsi,%rdi), %r8b
	movb	%r8b, 9(%rax,%rdx)
	movb	10(%rsi,%rdi), %r8b
	movb	%r8b, 10(%rax,%rdx)
	movb	11(%rsi,%rdi), %r8b
	movb	%r8b, 11(%rax,%rdx)
	movb	12(%rsi,%rdi), %r8b
	movb	%r8b, 12(%rax,%rdx)
	movb	13(%rsi,%rdi), %r8b
	movb	%r8b, 13(%rax,%rdx)
	movb	14(%rsi,%rdi), %r8b
	movb	%r8b, 14(%rax,%rdx)
	movb	15(%rsi,%rdi), %r8b
	movb	%r8b, 15(%rax,%rdx)
	movb	16(%rsi,%rdi), %r8b
	movb	%r8b, 16(%rax,%rdx)
	movb	17(%rsi,%rdi), %r8b
	movb	%r8b, 17(%rax,%rdx)
	movb	18(%rsi,%rdi), %r8b
	movb	%r8b, 18(%rax,%rdx)
	movb	19(%rsi,%rdi), %r8b
	movb	%r8b, 19(%rax,%rdx)
	movb	20(%rsi,%rdi), %r8b
	movb	%r8b, 20(%rax,%rdx)
	movb	21(%rsi,%rdi), %r8b
	movb	%r8b, 21(%rax,%rdx)
	movb	22(%rsi,%rdi), %r8b
	movb	%r8b, 22(%rax,%rdx)
	movb	23(%rsi,%rdi), %r8b
	movb	%r8b, 23(%rax,%rdx)
	movb	24(%rsi,%rdi), %r8b
	movb	%r8b, 24(%rax,%rdx)
	movb	25(%rsi,%rdi), %r8b
	movb	%r8b, 25(%rax,%rdx)
	movb	26(%rsi,%rdi), %r8b
	movb	%r8b, 26(%rax,%rdx)
	movb	27(%rsi,%rdi), %r8b
	movb	%r8b, 27(%rax,%rdx)
	movb	28(%rsi,%rdi), %r8b
	movb	%r8b, 28(%rax,%rdx)
	movb	29(%rsi,%rdi), %r8b
	movb	%r8b, 29(%rax,%rdx)
	movb	30(%rsi,%rdi), %r8b
	movb	%r8b, 30(%rax,%rdx)
	movb	31(%rsi,%rdi), %sil
	movb	%sil, 31(%rax,%rdx)
	movq	$67, %rdx
	leaq	96(%rsp), %rsi
	movq	$0, %rdi
	movb	(%rsi,%rdi), %r8b
	movb	%r8b, (%rcx,%rdx)
	movb	1(%rsi,%rdi), %r8b
	movb	%r8b, 1(%rcx,%rdx)
	movb	2(%rsi,%rdi), %r8b
	movb	%r8b, 2(%rcx,%rdx)
	movb	3(%rsi,%rdi), %r8b
	movb	%r8b, 3(%rcx,%rdx)
	movb	4(%rsi,%rdi), %r8b
	movb	%r8b, 4(%rcx,%rdx)
	movb	5(%rsi,%rdi), %r8b
	movb	%r8b, 5(%rcx,%rdx)
	movb	6(%rsi,%rdi), %r8b
	movb	%r8b, 6(%rcx,%rdx)
	movb	7(%rsi,%rdi), %r8b
	movb	%r8b, 7(%rcx,%rdx)
	movb	8(%rsi,%rdi), %r8b
	movb	%r8b, 8(%rcx,%rdx)
	movb	9(%rsi,%rdi), %r8b
	movb	%r8b, 9(%rcx,%rdx)
	movb	10(%rsi,%rdi), %r8b
	movb	%r8b, 10(%rcx,%rdx)
	movb	11(%rsi,%rdi), %r8b
	movb	%r8b, 11(%rcx,%rdx)
	movb	12(%rsi,%rdi), %r8b
	movb	%r8b, 12(%rcx,%rdx)
	movb	13(%rsi,%rdi), %r8b
	movb	%r8b, 13(%rcx,%rdx)
	movb	14(%rsi,%rdi), %r8b
	movb	%r8b, 14(%rcx,%rdx)
	movb	15(%rsi,%rdi), %r8b
	movb	%r8b, 15(%rcx,%rdx)
	movb	16(%rsi,%rdi), %r8b
	movb	%r8b, 16(%rcx,%rdx)
	movb	17(%rsi,%rdi), %r8b
	movb	%r8b, 17(%rcx,%rdx)
	movb	18(%rsi,%rdi), %r8b
	movb	%r8b, 18(%rcx,%rdx)
	movb	19(%rsi,%rdi), %r8b
	movb	%r8b, 19(%rcx,%rdx)
	movb	20(%rsi,%rdi), %r8b
	movb	%r8b, 20(%rcx,%rdx)
	movb	21(%rsi,%rdi), %r8b
	movb	%r8b, 21(%rcx,%rdx)
	movb	22(%rsi,%rdi), %r8b
	movb	%r8b, 22(%rcx,%rdx)
	movb	23(%rsi,%rdi), %r8b
	movb	%r8b, 23(%rcx,%rdx)
	movb	24(%rsi,%rdi), %r8b
	movb	%r8b, 24(%rcx,%rdx)
	movb	25(%rsi,%rdi), %r8b
	movb	%r8b, 25(%rcx,%rdx)
	movb	26(%rsi,%rdi), %r8b
	movb	%r8b, 26(%rcx,%rdx)
	movb	27(%rsi,%rdi), %r8b
	movb	%r8b, 27(%rcx,%rdx)
	movb	28(%rsi,%rdi), %r8b
	movb	%r8b, 28(%rcx,%rdx)
	movb	29(%rsi,%rdi), %r8b
	movb	%r8b, 29(%rcx,%rdx)
	movb	30(%rsi,%rdi), %r8b
	movb	%r8b, 30(%rcx,%rdx)
	movb	31(%rsi,%rdi), %sil
	movb	%sil, 31(%rcx,%rdx)
	ret
L_xmssmt_core_sign_open$1:
	movq	$0, 8(%rsp)
	leaq	32(%rdx), %rax
	movq	%rdi, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r8, 32(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rax, 48(%rsp)
	leaq	72(%rsp), %rax
	movq	%rax, %r9
	call	L_zero_address$1
L_xmssmt_core_sign_open$21:
	leaq	104(%rsp), %r9
	call	L_zero_address$1
L_xmssmt_core_sign_open$20:
	leaq	136(%rsp), %r9
	call	L_zero_address$1
L_xmssmt_core_sign_open$19:
	leaq	72(%rsp), %rax
	movl	$0, %r9d
	movl	%r9d, 12(%rax)
	leaq	104(%rsp), %rax
	movl	$1, %r9d
	movl	%r9d, 12(%rax)
	leaq	136(%rsp), %rax
	movl	$2, %r9d
	movl	%r9d, 12(%rax)
	movq	%rcx, %r11
	addq	$-4963, %r11
	movq	%r11, (%rsi)
	movq	$0, %rax
	movq	$0, %r9
	jmp 	L_xmssmt_core_sign_open$17
L_xmssmt_core_sign_open$18:
	movzbq	(%r8,%r9), %r10
	movq	$2, %rcx
	subq	%r9, %rcx
	shlq	$3, %rcx
	shlq	%cl, %r10
	orq 	%r10, %rax
	incq	%r9
L_xmssmt_core_sign_open$17:
	cmpq	$3, %r9
	jb  	L_xmssmt_core_sign_open$18
	movq	$4963, %r10
	movq	$4963, %rbx
	movq	%rdi, %rcx
	movq	%r8, %r9
	movq	%rbx, %r12
	call	L_memcpy_u8pu8p$1
L_xmssmt_core_sign_open$16:
	addq	$3, %r8
	leaq	168(%rsp), %rcx
	call	L_memcpy_u8u8p$1
L_xmssmt_core_sign_open$15:
	movq	%rdi, %r8
	addq	$4835, %r8
	movq	(%rsi), %r9
	leaq	2352(%rsp), %rcx
	leaq	168(%rsp), %rsi
	movq	%rdx, %rdi
	movq	%rcx, %rdx
	movq	%rsi, %rcx
	movq	%rdi, %rsi
	movq	%rax, %rdi
	movq	%r8, %r10
	movq	%r9, %r8
	leaq	-176(%rsp), %rsp
	call	L_hash_message$1
L_xmssmt_core_sign_open$14:
	leaq	176(%rsp), %rsp
	addq	$35, 8(%rsp)
	movl	$0, %esi
	jmp 	L_xmssmt_core_sign_open$9
L_xmssmt_core_sign_open$10:
	movl	%esi, 2344(%rsp)
	movl	$1023, %ecx
	andl	%eax, %ecx
	shrq	$10, %rax
	movq	%rax, 56(%rsp)
	movl	%ecx, 2348(%rsp)
	leaq	72(%rsp), %rdx
	movl	%esi, (%rdx)
	leaq	104(%rsp), %rdx
	movl	%esi, (%rdx)
	leaq	136(%rsp), %rdx
	movl	%esi, (%rdx)
	leaq	104(%rsp), %rdx
	movq	%rax, %rsi
	shrq	$32, %rsi
	movl	%esi, 4(%rdx)
	movl	%eax, 8(%rdx)
	leaq	72(%rsp), %rdx
	movq	%rax, %rsi
	shrq	$32, %rsi
	movl	%esi, 4(%rdx)
	movl	%eax, 8(%rdx)
	leaq	136(%rsp), %rdx
	movq	%rax, %rsi
	shrq	$32, %rsi
	movl	%esi, 4(%rdx)
	movl	%eax, 8(%rdx)
	leaq	72(%rsp), %rax
	movl	%ecx, 16(%rax)
	movq	32(%rsp), %rax
	movq	48(%rsp), %rcx
	movq	%rax, %rdx
	addq	8(%rsp), %rdx
	leaq	200(%rsp), %rax
	leaq	2352(%rsp), %rsi
	leaq	72(%rsp), %rdi
	leaq	-288(%rsp), %rsp
	call	L_wots_pk_from_sig$1
L_xmssmt_core_sign_open$13:
	leaq	288(%rsp), %rsp
	movq	8(%rsp), %rax
	addq	$2144, %rax
	movq	%rax, 64(%rsp)
	movl	2348(%rsp), %eax
	leaq	104(%rsp), %rcx
	movl	%eax, 16(%rcx)
	movq	48(%rsp), %rcx
	leaq	168(%rsp), %rax
	leaq	200(%rsp), %rdx
	leaq	104(%rsp), %rsi
	movq	%rax, %rdi
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	leaq	-152(%rsp), %rsp
	call	L_l_tree$1
L_xmssmt_core_sign_open$12:
	leaq	152(%rsp), %rsp
	movl	2348(%rsp), %eax
	movq	32(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	%rcx, %rsi
	addq	64(%rsp), %rsi
	leaq	2352(%rsp), %rcx
	leaq	168(%rsp), %rdi
	leaq	136(%rsp), %r8
	movq	%rcx, %r9
	movq	%rdi, %rcx
	movq	%r8, %rdi
	leaq	-128(%rsp), %rsp
	call	L_compute_root$1
L_xmssmt_core_sign_open$11:
	leaq	128(%rsp), %rsp
	movq	64(%rsp), %rax
	addq	$320, %rax
	movq	%rax, 8(%rsp)
	movl	2344(%rsp), %esi
	movq	56(%rsp), %rax
	incl	%esi
L_xmssmt_core_sign_open$9:
	cmpl	$2, %esi
	jb  	L_xmssmt_core_sign_open$10
	movq	40(%rsp), %rax
	leaq	2352(%rsp), %rcx
	movb	$0, %dl
	movq	$0, %rsi
	jmp 	L_xmssmt_core_sign_open$7
L_xmssmt_core_sign_open$8:
	movb	(%rcx,%rsi), %dil
	xorb	(%rax,%rsi), %dil
	orb 	%dil, %dl
	incq	%rsi
L_xmssmt_core_sign_open$7:
	cmpq	$32, %rsi
	jb  	L_xmssmt_core_sign_open$8
	movq	24(%rsp), %rcx
	movq	(%rcx), %r11
	cmpb	$0, %dl
	jne 	L_xmssmt_core_sign_open$2
	movq	$0, %rax
	movq	16(%rsp), %rcx
	movq	32(%rsp), %r9
	movq	$0, %r10
	movq	8(%rsp), %rdx
	movq	%rdx, %r12
	call	L_memcpy_u8pu8p$1
L_xmssmt_core_sign_open$6:
	jmp 	L_xmssmt_core_sign_open$3
L_xmssmt_core_sign_open$2:
	movq	$-1, %rax
	movq	16(%rsp), %rdx
	movq	$0, %rsi
	jmp 	L_xmssmt_core_sign_open$4
L_xmssmt_core_sign_open$5:
	movb	$0, (%rdx,%rsi)
	incq	%rsi
L_xmssmt_core_sign_open$4:
	cmpq	%r11, %rsi
	jb  	L_xmssmt_core_sign_open$5
	movq	$0, (%rcx)
L_xmssmt_core_sign_open$3:
	ret
L_gen_leaf_wots$1:
	movq	%rdx, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rsi, 24(%rsp)
	leaq	48(%rsp), %rdx
	movq	%rcx, 32(%rsp)
	movq	%rdx, %rsi
	movq	%rax, %r8
	movq	%rcx, %rdx
	movq	%rdi, %rax
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
L_gen_leaf_wots$70:
	leaq	88(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$0, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	movq	%rax, %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$69:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$1, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	32(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$68:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$2, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	64(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$67:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$3, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	96(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$66:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$4, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	128(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$65:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$5, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	160(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$64:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$6, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	192(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$63:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$7, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	224(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$62:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$8, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	256(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$61:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$9, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	288(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$60:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$10, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	320(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$59:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$11, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	352(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$58:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$12, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	384(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$57:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$13, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	416(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$56:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$14, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	448(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$55:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$15, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	480(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$54:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$16, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	512(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$53:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$17, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	544(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$52:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$18, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	576(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$51:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$19, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	608(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$50:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$20, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	640(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$49:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$21, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	672(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$48:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$22, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	704(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$47:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$23, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	736(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$46:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$24, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	768(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$45:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$25, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	800(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$44:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$26, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	832(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$43:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$27, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	864(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$42:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$28, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	896(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$41:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$29, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	928(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$40:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$30, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	960(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$39:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$31, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	992(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$38:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$32, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1024(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$37:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$33, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1056(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$36:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$34, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1088(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$35:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$35, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1120(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$34:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$36, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1152(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$33:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$37, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1184(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$32:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$38, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1216(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$31:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$39, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1248(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$30:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$40, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1280(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$29:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$41, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1312(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$28:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$42, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1344(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$27:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$43, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1376(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$26:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$44, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1408(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$25:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$45, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1440(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$24:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$46, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1472(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$23:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$47, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1504(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$22:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$48, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1536(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$21:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$49, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1568(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$20:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$50, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1600(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$19:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$51, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1632(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$18:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$52, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1664(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$17:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$53, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1696(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$16:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$54, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1728(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$15:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$55, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1760(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$14:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$56, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1792(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$13:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$57, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1824(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$12:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$58, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1856(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$11:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$59, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1888(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$10:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$60, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1920(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$9:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$61, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1952(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$8:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$62, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	1984(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$7:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$63, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	2016(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$6:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$64, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	2048(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$5:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$65, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	2080(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$4:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movq	%rax, 40(%rsp)
	movl	$66, %eax
	movl	%eax, 20(%rdi)
	movq	40(%rsp), %rax
	movq	32(%rsp), %rsi
	leaq	2112(%rax), %r8
	movl	$0, %ecx
	movl	$15, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$3:
	leaq	32(%rsp), %rsp
	movq	%rax, 32(%rsp)
	movq	%rcx, 32(%rsp)
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	24(%rsp), %rdx
	leaq	48(%rsp), %rsi
	movq	%rax, %rdi
	movq	%rdx, %rax
	movq	%rcx, %rdx
	leaq	-152(%rsp), %rsp
	call	L_l_tree$1
L_gen_leaf_wots$2:
	leaq	152(%rsp), %rsp
	movq	%rdi, %rcx
	movq	32(%rsp), %rdx
	ret
L_compute_root$1:
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdx, 24(%rsp)
	movl	$0, %edx
	movl	%edx, 20(%rdi)
	movl	%eax, %edx
	shrl	$1, %edx
	movl	%edx, 24(%rdi)
	movl	%eax, %edx
	shrl	$0, %edx
	andl	$1, %edx
	cmpl	$0, %edx
	je  	L_compute_root$48
	movq	(%rcx), %rdx
	movq	%rdx, 104(%rsp)
	movq	8(%rcx), %rdx
	movq	%rdx, 112(%rsp)
	movq	16(%rcx), %rdx
	movq	%rdx, 120(%rsp)
	movq	24(%rcx), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	movq	32(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$51:
	jmp 	L_compute_root$49
L_compute_root$48:
	movq	(%rcx), %rdx
	movq	%rdx, 72(%rsp)
	movq	8(%rcx), %rdx
	movq	%rdx, 80(%rsp)
	movq	16(%rcx), %rdx
	movq	%rdx, 88(%rsp)
	movq	24(%rcx), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	movq	32(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$50:
L_compute_root$49:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$47:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$1, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$2, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$1, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$43
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$32, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$46:
	jmp 	L_compute_root$44
L_compute_root$43:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$32, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$45:
L_compute_root$44:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$42:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$2, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$3, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$2, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$38
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$64, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$41:
	jmp 	L_compute_root$39
L_compute_root$38:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$64, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$40:
L_compute_root$39:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$37:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$3, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$4, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$3, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$33
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$96, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$36:
	jmp 	L_compute_root$34
L_compute_root$33:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$96, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$35:
L_compute_root$34:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$32:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$4, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$5, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$4, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$28
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$128, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$31:
	jmp 	L_compute_root$29
L_compute_root$28:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$128, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$30:
L_compute_root$29:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$27:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$5, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$6, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$5, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$23
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$160, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$26:
	jmp 	L_compute_root$24
L_compute_root$23:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$160, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$25:
L_compute_root$24:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$22:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$6, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$7, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$6, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$18
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$192, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$21:
	jmp 	L_compute_root$19
L_compute_root$18:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$192, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$20:
L_compute_root$19:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$17:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$7, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$8, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$7, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$13
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$224, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$16:
	jmp 	L_compute_root$14
L_compute_root$13:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$224, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$15:
L_compute_root$14:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$12:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$8, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$9, %ecx
	movl	%ecx, 24(%rdi)
	movl	%eax, %ecx
	shrl	$8, %ecx
	andl	$1, %ecx
	cmpl	$0, %ecx
	je  	L_compute_root$8
	movq	40(%rsp), %rcx
	movq	%rcx, 104(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 112(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 128(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$256, 32(%rsp)
	leaq	72(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$11:
	jmp 	L_compute_root$9
L_compute_root$8:
	movq	40(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsp), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	addq	$256, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$10:
L_compute_root$9:
	movq	24(%rsp), %rsi
	leaq	40(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$7:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rdi
	movl	$9, %ecx
	movl	%ecx, 20(%rdi)
	movl	%eax, %ecx
	shrl	$10, %ecx
	movl	%ecx, 24(%rdi)
	shrl	$9, %eax
	andl	$1, %eax
	cmpl	$0, %eax
	je  	L_compute_root$3
	movq	40(%rsp), %rax
	movq	%rax, 104(%rsp)
	movq	48(%rsp), %rax
	movq	%rax, 112(%rsp)
	movq	56(%rsp), %rax
	movq	%rax, 120(%rsp)
	movq	64(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	8(%rsp), %rax
	movq	%rax, 8(%rsp)
	addq	$288, 8(%rsp)
	leaq	72(%rsp), %rcx
	movq	8(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$6:
	jmp 	L_compute_root$4
L_compute_root$3:
	movq	40(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	48(%rsp), %rax
	movq	%rax, 80(%rsp)
	movq	56(%rsp), %rax
	movq	%rax, 88(%rsp)
	movq	64(%rsp), %rax
	movq	%rax, 96(%rsp)
	movq	8(%rsp), %rax
	movq	%rax, 32(%rsp)
	addq	$288, 32(%rsp)
	leaq	104(%rsp), %rcx
	movq	32(%rsp), %r8
	call	L_memcpy_u8u8p$1
L_compute_root$5:
L_compute_root$4:
	movq	24(%rsp), %rsi
	movq	16(%rsp), %rcx
	leaq	72(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_compute_root$2:
	leaq	384(%rsp), %rsp
	movq	%rcx, %rax
	movq	%rdx, %rcx
	movq	%rax, 16(%rsp)
	movq	16(%rsp), %rax
	ret
L_l_tree$1:
	movq	$67, %rcx
	movl	$0, %r8d
	movq	%rdi, 8(%rsp)
	movq	%rsi, 16(%rsp)
	movq	%rdx, 24(%rsp)
	movl	%r8d, 120(%rsp)
	movl	%r8d, 20(%rax)
	jmp 	L_l_tree$3
L_l_tree$4:
	movq	%rcx, %rdx
	shrq	$1, %rdx
	movq	%rcx, 32(%rsp)
	movq	$0, %rsi
	jmp 	L_l_tree$7
L_l_tree$8:
	movq	%rsi, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movl	%esi, %ecx
	movl	%ecx, 24(%rax)
	movq	%rsi, %rcx
	shlq	$6, %rcx
	movq	$64, %rdx
	movq	16(%rsp), %rsi
	leaq	56(%rsp), %rdi
	movq	$0, %r8
	jmp 	L_l_tree$12
L_l_tree$13:
	movb	(%rsi,%rcx), %r9b
	movb	%r9b, (%rdi,%r8)
	incq	%r8
	incq	%rcx
L_l_tree$12:
	cmpq	%rdx, %r8
	jb  	L_l_tree$13
	movq	24(%rsp), %rsi
	leaq	124(%rsp), %rcx
	leaq	56(%rsp), %rdx
	movq	%rax, %rdi
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_l_tree$11:
	leaq	384(%rsp), %rsp
	movq	%rdx, %rax
	movq	40(%rsp), %rsi
	movq	16(%rsp), %rcx
	movq	%rsi, %rdx
	shlq	$5, %rdx
	leaq	124(%rsp), %rdi
	movq	$0, %r8
	jmp 	L_l_tree$9
L_l_tree$10:
	movb	(%rdi,%r8), %r9b
	movb	%r9b, (%rcx,%rdx)
	incq	%r8
	incq	%rdx
L_l_tree$9:
	cmpq	$32, %r8
	jb  	L_l_tree$10
	movq	48(%rsp), %rdx
	incq	%rsi
L_l_tree$7:
	cmpq	%rdx, %rsi
	jb  	L_l_tree$8
	movq	32(%rsp), %rcx
	movq	%rcx, %rdx
	andq	$1, %rdx
	cmpq	$0, %rdx
	jne 	L_l_tree$5
	shrq	$1, %rcx
	jmp 	L_l_tree$6
L_l_tree$5:
	movq	16(%rsp), %rdx
	movq	%rcx, %rsi
	addq	$-1, %rsi
	shlq	$5, %rsi
	movq	%rcx, %rdi
	shrq	$1, %rdi
	shlq	$5, %rdi
	movb	(%rdx,%rsi), %r8b
	movb	%r8b, (%rdx,%rdi)
	movb	1(%rdx,%rsi), %r8b
	movb	%r8b, 1(%rdx,%rdi)
	movb	2(%rdx,%rsi), %r8b
	movb	%r8b, 2(%rdx,%rdi)
	movb	3(%rdx,%rsi), %r8b
	movb	%r8b, 3(%rdx,%rdi)
	movb	4(%rdx,%rsi), %r8b
	movb	%r8b, 4(%rdx,%rdi)
	movb	5(%rdx,%rsi), %r8b
	movb	%r8b, 5(%rdx,%rdi)
	movb	6(%rdx,%rsi), %r8b
	movb	%r8b, 6(%rdx,%rdi)
	movb	7(%rdx,%rsi), %r8b
	movb	%r8b, 7(%rdx,%rdi)
	movb	8(%rdx,%rsi), %r8b
	movb	%r8b, 8(%rdx,%rdi)
	movb	9(%rdx,%rsi), %r8b
	movb	%r8b, 9(%rdx,%rdi)
	movb	10(%rdx,%rsi), %r8b
	movb	%r8b, 10(%rdx,%rdi)
	movb	11(%rdx,%rsi), %r8b
	movb	%r8b, 11(%rdx,%rdi)
	movb	12(%rdx,%rsi), %r8b
	movb	%r8b, 12(%rdx,%rdi)
	movb	13(%rdx,%rsi), %r8b
	movb	%r8b, 13(%rdx,%rdi)
	movb	14(%rdx,%rsi), %r8b
	movb	%r8b, 14(%rdx,%rdi)
	movb	15(%rdx,%rsi), %r8b
	movb	%r8b, 15(%rdx,%rdi)
	movb	16(%rdx,%rsi), %r8b
	movb	%r8b, 16(%rdx,%rdi)
	movb	17(%rdx,%rsi), %r8b
	movb	%r8b, 17(%rdx,%rdi)
	movb	18(%rdx,%rsi), %r8b
	movb	%r8b, 18(%rdx,%rdi)
	movb	19(%rdx,%rsi), %r8b
	movb	%r8b, 19(%rdx,%rdi)
	movb	20(%rdx,%rsi), %r8b
	movb	%r8b, 20(%rdx,%rdi)
	movb	21(%rdx,%rsi), %r8b
	movb	%r8b, 21(%rdx,%rdi)
	movb	22(%rdx,%rsi), %r8b
	movb	%r8b, 22(%rdx,%rdi)
	movb	23(%rdx,%rsi), %r8b
	movb	%r8b, 23(%rdx,%rdi)
	movb	24(%rdx,%rsi), %r8b
	movb	%r8b, 24(%rdx,%rdi)
	movb	25(%rdx,%rsi), %r8b
	movb	%r8b, 25(%rdx,%rdi)
	movb	26(%rdx,%rsi), %r8b
	movb	%r8b, 26(%rdx,%rdi)
	movb	27(%rdx,%rsi), %r8b
	movb	%r8b, 27(%rdx,%rdi)
	movb	28(%rdx,%rsi), %r8b
	movb	%r8b, 28(%rdx,%rdi)
	movb	29(%rdx,%rsi), %r8b
	movb	%r8b, 29(%rdx,%rdi)
	movb	30(%rdx,%rsi), %r8b
	movb	%r8b, 30(%rdx,%rdi)
	movb	31(%rdx,%rsi), %sil
	movb	%sil, 31(%rdx,%rdi)
	shrq	$1, %rcx
	incq	%rcx
L_l_tree$6:
	movl	120(%rsp), %edx
	incl	%edx
	movl	%edx, 20(%rax)
	movl	%edx, 120(%rsp)
L_l_tree$3:
	cmpq	$1, %rcx
	jnbe	L_l_tree$4
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	%rdx, %rsi
	movq	%rcx, %rdi
	call	Lmemcpy_u8u8_N___memcpy_u8u8$1
L_l_tree$2:
	ret
L_wots_pk_from_sig$1:
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	leaq	24(%rsp), %rdx
	leaq	-8(%rsp), %rsp
	call	L_chain_lengths$1
L_wots_pk_from_sig$136:
	leaq	8(%rsp), %rsp
	movl	$0, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	24(%rsp), %edx
	movl	$15, %r10d
	subl	24(%rsp), %r10d
	movq	%rcx, %r8
	movq	%rax, %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$135:
	movq	%rax, %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$134:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$1, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	28(%rsp), %edx
	movl	$15, %r10d
	subl	28(%rsp), %r10d
	movq	%rcx, %r8
	addq	$32, %r8
	leaq	32(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$133:
	leaq	32(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$132:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$2, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	32(%rsp), %edx
	movl	$15, %r10d
	subl	32(%rsp), %r10d
	movq	%rcx, %r8
	addq	$64, %r8
	leaq	64(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$131:
	leaq	64(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$130:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$3, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	36(%rsp), %edx
	movl	$15, %r10d
	subl	36(%rsp), %r10d
	movq	%rcx, %r8
	addq	$96, %r8
	leaq	96(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$129:
	leaq	96(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$128:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$4, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	40(%rsp), %edx
	movl	$15, %r10d
	subl	40(%rsp), %r10d
	movq	%rcx, %r8
	addq	$128, %r8
	leaq	128(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$127:
	leaq	128(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$126:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$5, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	44(%rsp), %edx
	movl	$15, %r10d
	subl	44(%rsp), %r10d
	movq	%rcx, %r8
	addq	$160, %r8
	leaq	160(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$125:
	leaq	160(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$124:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$6, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	48(%rsp), %edx
	movl	$15, %r10d
	subl	48(%rsp), %r10d
	movq	%rcx, %r8
	addq	$192, %r8
	leaq	192(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$123:
	leaq	192(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$122:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$7, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	52(%rsp), %edx
	movl	$15, %r10d
	subl	52(%rsp), %r10d
	movq	%rcx, %r8
	addq	$224, %r8
	leaq	224(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$121:
	leaq	224(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$120:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$8, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	56(%rsp), %edx
	movl	$15, %r10d
	subl	56(%rsp), %r10d
	movq	%rcx, %r8
	addq	$256, %r8
	leaq	256(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$119:
	leaq	256(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$118:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$9, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	60(%rsp), %edx
	movl	$15, %r10d
	subl	60(%rsp), %r10d
	movq	%rcx, %r8
	addq	$288, %r8
	leaq	288(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$117:
	leaq	288(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$116:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$10, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	64(%rsp), %edx
	movl	$15, %r10d
	subl	64(%rsp), %r10d
	movq	%rcx, %r8
	addq	$320, %r8
	leaq	320(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$115:
	leaq	320(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$114:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$11, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	68(%rsp), %edx
	movl	$15, %r10d
	subl	68(%rsp), %r10d
	movq	%rcx, %r8
	addq	$352, %r8
	leaq	352(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$113:
	leaq	352(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$112:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$12, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	72(%rsp), %edx
	movl	$15, %r10d
	subl	72(%rsp), %r10d
	movq	%rcx, %r8
	addq	$384, %r8
	leaq	384(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$111:
	leaq	384(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$110:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$13, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	76(%rsp), %edx
	movl	$15, %r10d
	subl	76(%rsp), %r10d
	movq	%rcx, %r8
	addq	$416, %r8
	leaq	416(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$109:
	leaq	416(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$108:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$14, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	80(%rsp), %edx
	movl	$15, %r10d
	subl	80(%rsp), %r10d
	movq	%rcx, %r8
	addq	$448, %r8
	leaq	448(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$107:
	leaq	448(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$106:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$15, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	84(%rsp), %edx
	movl	$15, %r10d
	subl	84(%rsp), %r10d
	movq	%rcx, %r8
	addq	$480, %r8
	leaq	480(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$105:
	leaq	480(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$104:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$16, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	88(%rsp), %edx
	movl	$15, %r10d
	subl	88(%rsp), %r10d
	movq	%rcx, %r8
	addq	$512, %r8
	leaq	512(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$103:
	leaq	512(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$102:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$17, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	92(%rsp), %edx
	movl	$15, %r10d
	subl	92(%rsp), %r10d
	movq	%rcx, %r8
	addq	$544, %r8
	leaq	544(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$101:
	leaq	544(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$100:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$18, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	96(%rsp), %edx
	movl	$15, %r10d
	subl	96(%rsp), %r10d
	movq	%rcx, %r8
	addq	$576, %r8
	leaq	576(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$99:
	leaq	576(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$98:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$19, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	100(%rsp), %edx
	movl	$15, %r10d
	subl	100(%rsp), %r10d
	movq	%rcx, %r8
	addq	$608, %r8
	leaq	608(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$97:
	leaq	608(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$96:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$20, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	104(%rsp), %edx
	movl	$15, %r10d
	subl	104(%rsp), %r10d
	movq	%rcx, %r8
	addq	$640, %r8
	leaq	640(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$95:
	leaq	640(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$94:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$21, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	108(%rsp), %edx
	movl	$15, %r10d
	subl	108(%rsp), %r10d
	movq	%rcx, %r8
	addq	$672, %r8
	leaq	672(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$93:
	leaq	672(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$92:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$22, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	112(%rsp), %edx
	movl	$15, %r10d
	subl	112(%rsp), %r10d
	movq	%rcx, %r8
	addq	$704, %r8
	leaq	704(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$91:
	leaq	704(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$90:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$23, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	116(%rsp), %edx
	movl	$15, %r10d
	subl	116(%rsp), %r10d
	movq	%rcx, %r8
	addq	$736, %r8
	leaq	736(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$89:
	leaq	736(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$88:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$24, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	120(%rsp), %edx
	movl	$15, %r10d
	subl	120(%rsp), %r10d
	movq	%rcx, %r8
	addq	$768, %r8
	leaq	768(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$87:
	leaq	768(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$86:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$25, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	124(%rsp), %edx
	movl	$15, %r10d
	subl	124(%rsp), %r10d
	movq	%rcx, %r8
	addq	$800, %r8
	leaq	800(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$85:
	leaq	800(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$84:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$26, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	128(%rsp), %edx
	movl	$15, %r10d
	subl	128(%rsp), %r10d
	movq	%rcx, %r8
	addq	$832, %r8
	leaq	832(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$83:
	leaq	832(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$82:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$27, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	132(%rsp), %edx
	movl	$15, %r10d
	subl	132(%rsp), %r10d
	movq	%rcx, %r8
	addq	$864, %r8
	leaq	864(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$81:
	leaq	864(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$80:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$28, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	136(%rsp), %edx
	movl	$15, %r10d
	subl	136(%rsp), %r10d
	movq	%rcx, %r8
	addq	$896, %r8
	leaq	896(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$79:
	leaq	896(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$78:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$29, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	140(%rsp), %edx
	movl	$15, %r10d
	subl	140(%rsp), %r10d
	movq	%rcx, %r8
	addq	$928, %r8
	leaq	928(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$77:
	leaq	928(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$76:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$30, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	144(%rsp), %edx
	movl	$15, %r10d
	subl	144(%rsp), %r10d
	movq	%rcx, %r8
	addq	$960, %r8
	leaq	960(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$75:
	leaq	960(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$74:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$31, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	148(%rsp), %edx
	movl	$15, %r10d
	subl	148(%rsp), %r10d
	movq	%rcx, %r8
	addq	$992, %r8
	leaq	992(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$73:
	leaq	992(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$72:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$32, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	152(%rsp), %edx
	movl	$15, %r10d
	subl	152(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1024, %r8
	leaq	1024(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$71:
	leaq	1024(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$70:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$33, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	156(%rsp), %edx
	movl	$15, %r10d
	subl	156(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1056, %r8
	leaq	1056(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$69:
	leaq	1056(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$68:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$34, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	160(%rsp), %edx
	movl	$15, %r10d
	subl	160(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1088, %r8
	leaq	1088(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$67:
	leaq	1088(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$66:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$35, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	164(%rsp), %edx
	movl	$15, %r10d
	subl	164(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1120, %r8
	leaq	1120(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$65:
	leaq	1120(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$64:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$36, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	168(%rsp), %edx
	movl	$15, %r10d
	subl	168(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1152, %r8
	leaq	1152(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$63:
	leaq	1152(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$62:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$37, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	172(%rsp), %edx
	movl	$15, %r10d
	subl	172(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1184, %r8
	leaq	1184(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$61:
	leaq	1184(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$60:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$38, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	176(%rsp), %edx
	movl	$15, %r10d
	subl	176(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1216, %r8
	leaq	1216(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$59:
	leaq	1216(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$58:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$39, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	180(%rsp), %edx
	movl	$15, %r10d
	subl	180(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1248, %r8
	leaq	1248(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$57:
	leaq	1248(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$56:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$40, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	184(%rsp), %edx
	movl	$15, %r10d
	subl	184(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1280, %r8
	leaq	1280(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$55:
	leaq	1280(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$54:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$41, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	188(%rsp), %edx
	movl	$15, %r10d
	subl	188(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1312, %r8
	leaq	1312(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$53:
	leaq	1312(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$52:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$42, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	192(%rsp), %edx
	movl	$15, %r10d
	subl	192(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1344, %r8
	leaq	1344(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$51:
	leaq	1344(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$50:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$43, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	196(%rsp), %edx
	movl	$15, %r10d
	subl	196(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1376, %r8
	leaq	1376(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$49:
	leaq	1376(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$48:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$44, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	200(%rsp), %edx
	movl	$15, %r10d
	subl	200(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1408, %r8
	leaq	1408(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$47:
	leaq	1408(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$46:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$45, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	204(%rsp), %edx
	movl	$15, %r10d
	subl	204(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1440, %r8
	leaq	1440(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$45:
	leaq	1440(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$44:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$46, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	208(%rsp), %edx
	movl	$15, %r10d
	subl	208(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1472, %r8
	leaq	1472(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$43:
	leaq	1472(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$42:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$47, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	212(%rsp), %edx
	movl	$15, %r10d
	subl	212(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1504, %r8
	leaq	1504(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$41:
	leaq	1504(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$40:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$48, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	216(%rsp), %edx
	movl	$15, %r10d
	subl	216(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1536, %r8
	leaq	1536(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$39:
	leaq	1536(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$38:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$49, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	220(%rsp), %edx
	movl	$15, %r10d
	subl	220(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1568, %r8
	leaq	1568(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$37:
	leaq	1568(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$36:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$50, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	224(%rsp), %edx
	movl	$15, %r10d
	subl	224(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1600, %r8
	leaq	1600(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$35:
	leaq	1600(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$34:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$51, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	228(%rsp), %edx
	movl	$15, %r10d
	subl	228(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1632, %r8
	leaq	1632(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$33:
	leaq	1632(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$32:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$52, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	232(%rsp), %edx
	movl	$15, %r10d
	subl	232(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1664, %r8
	leaq	1664(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$31:
	leaq	1664(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$30:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$53, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	236(%rsp), %edx
	movl	$15, %r10d
	subl	236(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1696, %r8
	leaq	1696(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$29:
	leaq	1696(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$28:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$54, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	240(%rsp), %edx
	movl	$15, %r10d
	subl	240(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1728, %r8
	leaq	1728(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$27:
	leaq	1728(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$26:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$55, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	244(%rsp), %edx
	movl	$15, %r10d
	subl	244(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1760, %r8
	leaq	1760(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$25:
	leaq	1760(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$24:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$56, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	248(%rsp), %edx
	movl	$15, %r10d
	subl	248(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1792, %r8
	leaq	1792(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$23:
	leaq	1792(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$22:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$57, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	252(%rsp), %edx
	movl	$15, %r10d
	subl	252(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1824, %r8
	leaq	1824(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$21:
	leaq	1824(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$20:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$58, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	256(%rsp), %edx
	movl	$15, %r10d
	subl	256(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1856, %r8
	leaq	1856(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$19:
	leaq	1856(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$18:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$59, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	260(%rsp), %edx
	movl	$15, %r10d
	subl	260(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1888, %r8
	leaq	1888(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$17:
	leaq	1888(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$16:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$60, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	264(%rsp), %edx
	movl	$15, %r10d
	subl	264(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1920, %r8
	leaq	1920(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$15:
	leaq	1920(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$14:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$61, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	268(%rsp), %edx
	movl	$15, %r10d
	subl	268(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1952, %r8
	leaq	1952(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$13:
	leaq	1952(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$12:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$62, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	272(%rsp), %edx
	movl	$15, %r10d
	subl	272(%rsp), %r10d
	movq	%rcx, %r8
	addq	$1984, %r8
	leaq	1984(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$11:
	leaq	1984(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$10:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$63, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	276(%rsp), %edx
	movl	$15, %r10d
	subl	276(%rsp), %r10d
	movq	%rcx, %r8
	addq	$2016, %r8
	leaq	2016(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$9:
	leaq	2016(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$8:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$64, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	280(%rsp), %edx
	movl	$15, %r10d
	subl	280(%rsp), %r10d
	movq	%rcx, %r8
	addq	$2048, %r8
	leaq	2048(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$7:
	leaq	2048(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$6:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$65, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	284(%rsp), %edx
	movl	$15, %r10d
	subl	284(%rsp), %r10d
	movq	%rcx, %r8
	addq	$2080, %r8
	leaq	2080(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$5:
	leaq	2080(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$4:
	leaq	32(%rsp), %rsp
	movq	%rcx, %rdi
	movl	$66, %ecx
	movl	%ecx, 20(%rdi)
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rcx
	movl	288(%rsp), %edx
	movl	$15, %r10d
	subl	288(%rsp), %r10d
	movq	%rcx, %r8
	addq	$2112, %r8
	leaq	2112(%rax), %rcx
	call	L_memcpy_u8u8p$1
L_wots_pk_from_sig$3:
	leaq	2112(%rax), %r8
	movl	%edx, %ecx
	movl	%r10d, %edx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_wots_pk_from_sig$2:
	leaq	32(%rsp), %rsp
	ret
L_chain_lengths$1:
	movq	%rdx, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %rcx
	movb	$0, %r11b
	movb	$0, %bl
	jmp 	L_chain_lengths$7
L_chain_lengths$8:
	cmpq	$0, %rcx
	jne 	L_chain_lengths$9
	movb	(%rsi,%r9), %bl
	incq	%r9
	addq	$8, %rcx
L_chain_lengths$9:
	addq	$-4, %rcx
	movzbl	%bl, %ebp
	shrl	%cl, %ebp
	andl	$15, %ebp
	movl	%ebp, (%r8,%r10,4)
	incq	%r10
	incb	%r11b
L_chain_lengths$7:
	cmpb	$64, %r11b
	jb  	L_chain_lengths$8
	leaq	256(%rdx), %rsi
	movq	%rdx, %rcx
	movq	$0, %r8
	movq	$0, %r9
	jmp 	L_chain_lengths$5
L_chain_lengths$6:
	movq	$15, %r10
	movl	(%rcx,%r9,4), %r11d
	subq	%r11, %r10
	addq	%r10, %r8
	incq	%r9
L_chain_lengths$5:
	cmpq	$64, %r9
	jb  	L_chain_lengths$6
	movq	$8, %rcx
	addq	$-4, %rcx
	shlq	%cl, %r8
	leaq	8(%rsp), %r9
	movb	%r8b, 1(%r9)
	shrq	$8, %r8
	movb	%r8b, (%r9)
	movq	$0, %r8
	movq	$0, %r10
	movq	$0, %rcx
	movb	$0, %r11b
	movb	$0, %bl
	jmp 	L_chain_lengths$2
L_chain_lengths$3:
	cmpq	$0, %rcx
	jne 	L_chain_lengths$4
	movb	(%r9,%r8), %bl
	incq	%r8
	addq	$8, %rcx
L_chain_lengths$4:
	addq	$-4, %rcx
	movzbl	%bl, %ebp
	shrl	%cl, %ebp
	andl	$15, %ebp
	movl	%ebp, (%rsi,%r10,4)
	incq	%r10
	incb	%r11b
L_chain_lengths$2:
	cmpb	$3, %r11b
	jb  	L_chain_lengths$3
	ret
L_gen_chain_inplace$1:
	movq	%r8, 8(%rsp)
	movq	%rsi, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movl	%ecx, %esi
	addl	%edx, %ecx
	jmp 	L_gen_chain_inplace$2
L_gen_chain_inplace$3:
	movl	%esi, 32(%rsp)
	movl	%ecx, 36(%rsp)
	movq	24(%rsp), %rdi
	movl	%esi, 24(%rdi)
	movl	$0, %ecx
	movl	%ecx, 28(%rdi)
	movq	16(%rsp), %rdx
	movq	8(%rsp), %rcx
	movq	%rdi, %rsi
	leaq	-320(%rsp), %rsp
	call	L_thash_f$1
L_gen_chain_inplace$4:
	leaq	320(%rsp), %rsp
	movq	%rcx, %r8
	movl	32(%rsp), %esi
	movl	36(%rsp), %ecx
	incl	%esi
L_gen_chain_inplace$2:
	cmpl	%ecx, %esi
	jb  	L_gen_chain_inplace$3
	movq	24(%rsp), %rcx
	ret
L_expand_seed$1:
	movq	%rsi, 8(%rsp)
	movq	%r8, 16(%rsp)
	movl	$0, %ecx
	movl	%ecx, 24(%rax)
	movl	$0, %ecx
	movl	%ecx, 28(%rax)
	leaq	32(%rsp), %rcx
	call	Lcopy_nbytes$1
L_expand_seed$69:
	movl	$0, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	movq	%rax, %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$68:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$1, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	32(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$67:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$2, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	64(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$66:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$3, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	96(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$65:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$4, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	128(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$64:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$5, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	160(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$63:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$6, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	192(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$62:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$7, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	224(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$61:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$8, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	256(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$60:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$9, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	288(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$59:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$10, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	320(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$58:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$11, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	352(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$57:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$12, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	384(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$56:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$13, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	416(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$55:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$14, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	448(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$54:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$15, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	480(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$53:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$16, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	512(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$52:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$17, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	544(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$51:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$18, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	576(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$50:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$19, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	608(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$49:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$20, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	640(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$48:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$21, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	672(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$47:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$22, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	704(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$46:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$23, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	736(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$45:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$24, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	768(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$44:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$25, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	800(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$43:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$26, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	832(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$42:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$27, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	864(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$41:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$28, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	896(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$40:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$29, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	928(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$39:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$30, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	960(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$38:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$31, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	992(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$37:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$32, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1024(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$36:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$33, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1056(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$35:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$34, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1088(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$34:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$35, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1120(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$33:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$36, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1152(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$32:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$37, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1184(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$31:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$38, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1216(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$30:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$39, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1248(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$29:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$40, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1280(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$28:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$41, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1312(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$27:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$42, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1344(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$26:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$43, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1376(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$25:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$44, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1408(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$24:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$45, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1440(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$23:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$46, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1472(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$22:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$47, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1504(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$21:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$48, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1536(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$20:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$49, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1568(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$19:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$50, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1600(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$18:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$51, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1632(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$17:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$52, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1664(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$16:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$53, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1696(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$15:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$54, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1728(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$14:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$55, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1760(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$13:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$56, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1792(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$12:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$57, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1824(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$11:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$58, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1856(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$10:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$59, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1888(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$9:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$60, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1920(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$8:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$61, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1952(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$7:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$62, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	1984(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$6:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$63, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	2016(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$5:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$64, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	2048(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$4:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$65, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	2080(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$3:
	leaq	312(%rsp), %rsp
	movq	%rax, 8(%rsp)
	movq	24(%rsp), %rax
	movl	$66, %ecx
	movl	%ecx, 20(%rax)
	movq	%rax, 24(%rsp)
	leaq	64(%rsp), %rcx
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
	movq	8(%rsp), %rax
	movq	16(%rsp), %rdx
	leaq	2112(%rax), %rdi
	leaq	32(%rsp), %r8
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$2:
	leaq	312(%rsp), %rsp
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rcx
	movq	16(%rsp), %rax
	ret
L_thash_f$1:
	leaq	40(%rsp), %rdi
	movq	%rdi, %r8
	movl	(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	4(%rdi), %r8
	movl	4(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	8(%rdi), %r8
	movl	8(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	12(%rdi), %r8
	movl	12(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	16(%rdi), %r8
	movl	16(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	20(%rdi), %r8
	movl	20(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	24(%rdi), %r8
	movl	24(%rsi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	leaq	28(%rdi), %rdi
	movl	28(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	104(%rsp), %rdi
	movq	$0, %r8
	movb	%r8b, 31(%rdi)
	shrq	$8, %r8
	movb	%r8b, 30(%rdi)
	shrq	$8, %r8
	movb	%r8b, 29(%rdi)
	shrq	$8, %r8
	movb	%r8b, 28(%rdi)
	shrq	$8, %r8
	movb	%r8b, 27(%rdi)
	shrq	$8, %r8
	movb	%r8b, 26(%rdi)
	shrq	$8, %r8
	movb	%r8b, 25(%rdi)
	shrq	$8, %r8
	movb	%r8b, 24(%rdi)
	shrq	$8, %r8
	movb	%r8b, 23(%rdi)
	shrq	$8, %r8
	movb	%r8b, 22(%rdi)
	shrq	$8, %r8
	movb	%r8b, 21(%rdi)
	shrq	$8, %r8
	movb	%r8b, 20(%rdi)
	shrq	$8, %r8
	movb	%r8b, 19(%rdi)
	shrq	$8, %r8
	movb	%r8b, 18(%rdi)
	shrq	$8, %r8
	movb	%r8b, 17(%rdi)
	shrq	$8, %r8
	movb	%r8b, 16(%rdi)
	shrq	$8, %r8
	movb	%r8b, 15(%rdi)
	shrq	$8, %r8
	movb	%r8b, 14(%rdi)
	shrq	$8, %r8
	movb	%r8b, 13(%rdi)
	shrq	$8, %r8
	movb	%r8b, 12(%rdi)
	shrq	$8, %r8
	movb	%r8b, 11(%rdi)
	shrq	$8, %r8
	movb	%r8b, 10(%rdi)
	shrq	$8, %r8
	movb	%r8b, 9(%rdi)
	shrq	$8, %r8
	movb	%r8b, 8(%rdi)
	shrq	$8, %r8
	movb	%r8b, 7(%rdi)
	shrq	$8, %r8
	movb	%r8b, 6(%rdi)
	shrq	$8, %r8
	movb	%r8b, 5(%rdi)
	shrq	$8, %r8
	movb	%r8b, 4(%rdi)
	shrq	$8, %r8
	movb	%r8b, 3(%rdi)
	shrq	$8, %r8
	movb	%r8b, 2(%rdi)
	shrq	$8, %r8
	movb	%r8b, 1(%rdi)
	shrq	$8, %r8
	movb	%r8b, (%rdi)
	movq	%rcx, 8(%rsp)
	movq	%rsi, 16(%rsp)
	movq	%rdx, 24(%rsp)
	leaq	136(%rsp), %rdi
	leaq	40(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_f$13:
	leaq	280(%rsp), %rsp
	movq	16(%rsp), %rcx
	movl	$1, %edx
	movl	%edx, 28(%rcx)
	leaq	40(%rsp), %rdx
	movq	%rdx, %rsi
	movl	(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	4(%rdx), %rsi
	movl	4(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	8(%rdx), %rsi
	movl	8(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	12(%rdx), %rsi
	movl	12(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	16(%rdx), %rsi
	movl	16(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	20(%rdx), %rsi
	movl	20(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	24(%rdx), %rsi
	movl	24(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	28(%rdx), %rdx
	movl	28(%rcx), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	movq	%rcx, 16(%rsp)
	movq	24(%rsp), %rdx
	leaq	72(%rsp), %rdi
	leaq	40(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_f$12:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rdx
	movq	$0, %rcx
	jmp 	L_thash_f$10
L_thash_f$11:
	movq	(%rdx,%rcx,8), %rsi
	xorq	72(%rsp,%rcx,8), %rsi
	movq	%rsi, 168(%rsp,%rcx,8)
	incq	%rcx
L_thash_f$10:
	cmpq	$4, %rcx
	jb  	L_thash_f$11
	leaq	104(%rsp), %rcx
	movq	%rdx, 8(%rsp)
	movq	$96, %rdx
	shlq	$3, %rdx
	movq	%rdx, 24(%rsp)
	movl	$1779033703, 72(%rsp)
	movl	$-1150833019, 76(%rsp)
	movl	$1013904242, 80(%rsp)
	movl	$-1521486534, 84(%rsp)
	movl	$1359893119, 88(%rsp)
	movl	$-1694144372, 92(%rsp)
	movl	$528734635, 96(%rsp)
	movl	$1541459225, 100(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	72(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_thash_f$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rcx
	movq	24(%rsp), %rdx
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
	movb	(%rcx,%r9), %r9b
	movb	%r9b, 200(%rsp,%r8)
	incq	%r8
L_thash_f$7:
	cmpq	%rdi, %r8
	jb  	L_thash_f$8
	movb	$128, 200(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_thash_f$5
	movq	$120, %rsi
	movq	$2, %r15
	movq	$127, %rcx
	jmp 	L_thash_f$3
L_thash_f$5:
	movq	$56, %rsi
	movq	$1, %r15
	movq	$63, %rcx
L_thash_f$6:
	jmp 	L_thash_f$3
L_thash_f$4:
	movb	%dl, 200(%rsp,%rcx)
	shrq	$8, %rdx
	addq	$-1, %rcx
L_thash_f$3:
	cmpq	%rsi, %rcx
	jnb 	L_thash_f$4
	leaq	200(%rsp), %rsi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_thash_f$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movl	72(%rsp), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movl	76(%rsp), %edx
	bswapl	%edx
	movl	%edx, 4(%rcx)
	movl	80(%rsp), %edx
	bswapl	%edx
	movl	%edx, 8(%rcx)
	movl	84(%rsp), %edx
	bswapl	%edx
	movl	%edx, 12(%rcx)
	movl	88(%rsp), %edx
	bswapl	%edx
	movl	%edx, 16(%rcx)
	movl	92(%rsp), %edx
	bswapl	%edx
	movl	%edx, 20(%rcx)
	movl	96(%rsp), %edx
	bswapl	%edx
	movl	%edx, 24(%rcx)
	movl	100(%rsp), %edx
	bswapl	%edx
	movl	%edx, 28(%rcx)
	movq	16(%rsp), %rdx
	ret
L_thash_h$1:
	leaq	136(%rsp), %r8
	movq	$1, %r9
	movb	%r9b, 31(%r8)
	shrq	$8, %r9
	movb	%r9b, 30(%r8)
	shrq	$8, %r9
	movb	%r9b, 29(%r8)
	shrq	$8, %r9
	movb	%r9b, 28(%r8)
	shrq	$8, %r9
	movb	%r9b, 27(%r8)
	shrq	$8, %r9
	movb	%r9b, 26(%r8)
	shrq	$8, %r9
	movb	%r9b, 25(%r8)
	shrq	$8, %r9
	movb	%r9b, 24(%r8)
	shrq	$8, %r9
	movb	%r9b, 23(%r8)
	shrq	$8, %r9
	movb	%r9b, 22(%r8)
	shrq	$8, %r9
	movb	%r9b, 21(%r8)
	shrq	$8, %r9
	movb	%r9b, 20(%r8)
	shrq	$8, %r9
	movb	%r9b, 19(%r8)
	shrq	$8, %r9
	movb	%r9b, 18(%r8)
	shrq	$8, %r9
	movb	%r9b, 17(%r8)
	shrq	$8, %r9
	movb	%r9b, 16(%r8)
	shrq	$8, %r9
	movb	%r9b, 15(%r8)
	shrq	$8, %r9
	movb	%r9b, 14(%r8)
	shrq	$8, %r9
	movb	%r9b, 13(%r8)
	shrq	$8, %r9
	movb	%r9b, 12(%r8)
	shrq	$8, %r9
	movb	%r9b, 11(%r8)
	shrq	$8, %r9
	movb	%r9b, 10(%r8)
	shrq	$8, %r9
	movb	%r9b, 9(%r8)
	shrq	$8, %r9
	movb	%r9b, 8(%r8)
	shrq	$8, %r9
	movb	%r9b, 7(%r8)
	shrq	$8, %r9
	movb	%r9b, 6(%r8)
	shrq	$8, %r9
	movb	%r9b, 5(%r8)
	shrq	$8, %r9
	movb	%r9b, 4(%r8)
	shrq	$8, %r9
	movb	%r9b, 3(%r8)
	shrq	$8, %r9
	movb	%r9b, 2(%r8)
	shrq	$8, %r9
	movb	%r9b, 1(%r8)
	shrq	$8, %r9
	movb	%r9b, (%r8)
	movl	$0, %r8d
	movl	%r8d, 28(%rdi)
	leaq	40(%rsp), %r8
	movq	%r8, %r9
	movl	(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	4(%r8), %r9
	movl	4(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	8(%r8), %r9
	movl	8(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	12(%r8), %r9
	movl	12(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	16(%r8), %r9
	movl	16(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	20(%r8), %r9
	movl	20(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	24(%r8), %r9
	movl	24(%rdi), %r10d
	bswapl	%r10d
	movl	%r10d, (%r9)
	leaq	28(%r8), %r8
	movl	28(%rdi), %r9d
	bswapl	%r9d
	movl	%r9d, (%r8)
	movq	%rdx, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rsi, 32(%rsp)
	leaq	168(%rsp), %rdi
	leaq	40(%rsp), %r8
	movq	%rsi, %rdx
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$14:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rcx
	movl	$1, %edx
	movl	%edx, 28(%rcx)
	leaq	40(%rsp), %rdx
	movq	%rdx, %rsi
	movl	(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	4(%rdx), %rsi
	movl	4(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	8(%rdx), %rsi
	movl	8(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	12(%rdx), %rsi
	movl	12(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	16(%rdx), %rsi
	movl	16(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	20(%rdx), %rsi
	movl	20(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	24(%rdx), %rsi
	movl	24(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	28(%rdx), %rdx
	movl	28(%rcx), %esi
	bswapl	%esi
	movl	%esi, (%rdx)
	movq	%rcx, 24(%rsp)
	movq	32(%rsp), %rdx
	leaq	72(%rsp), %rdi
	leaq	40(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$13:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rcx
	movl	$2, %edx
	movl	%edx, 28(%rcx)
	movq	%rcx, 24(%rsp)
	leaq	40(%rsp), %rdx
	movq	%rdx, %rsi
	movl	(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	4(%rdx), %rsi
	movl	4(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	8(%rdx), %rsi
	movl	8(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	12(%rdx), %rsi
	movl	12(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	16(%rdx), %rsi
	movl	16(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	20(%rdx), %rsi
	movl	20(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	24(%rdx), %rsi
	movl	24(%rcx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	28(%rdx), %rdx
	movl	28(%rcx), %ecx
	bswapl	%ecx
	movl	%ecx, (%rdx)
	movq	32(%rsp), %rdx
	leaq	104(%rsp), %rdi
	leaq	40(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_h$12:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movq	$0, %rdx
	jmp 	L_thash_h$10
L_thash_h$11:
	movq	(%rcx,%rdx,8), %rsi
	xorq	72(%rsp,%rdx,8), %rsi
	movq	%rsi, 200(%rsp,%rdx,8)
	incq	%rdx
L_thash_h$10:
	cmpq	$8, %rdx
	jb  	L_thash_h$11
	movq	16(%rsp), %rdx
	leaq	136(%rsp), %rcx
	movq	%rdx, 16(%rsp)
	movq	$128, %rdx
	shlq	$3, %rdx
	movq	%rdx, 8(%rsp)
	movl	$1779033703, 40(%rsp)
	movl	$-1150833019, 44(%rsp)
	movl	$1013904242, 48(%rsp)
	movl	$-1521486534, 52(%rsp)
	movl	$1359893119, 56(%rsp)
	movl	$-1694144372, 60(%rsp)
	movl	$528734635, 64(%rsp)
	movl	$1541459225, 68(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	40(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_thash_h$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rcx
	movq	8(%rsp), %rdx
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
	movb	(%rcx,%r9), %r9b
	movb	%r9b, 264(%rsp,%r8)
	incq	%r8
L_thash_h$7:
	cmpq	%rdi, %r8
	jb  	L_thash_h$8
	movb	$128, 264(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_thash_h$5
	movq	$120, %rsi
	movq	$2, %r15
	movq	$127, %rcx
	jmp 	L_thash_h$3
L_thash_h$5:
	movq	$56, %rsi
	movq	$1, %r15
	movq	$63, %rcx
L_thash_h$6:
	jmp 	L_thash_h$3
L_thash_h$4:
	movb	%dl, 264(%rsp,%rcx)
	shrq	$8, %rdx
	addq	$-1, %rcx
L_thash_h$3:
	cmpq	%rsi, %rcx
	jnb 	L_thash_h$4
	leaq	264(%rsp), %rsi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_thash_h$2:
	leaq	280(%rsp), %rsp
	movq	16(%rsp), %rcx
	movl	40(%rsp), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movl	44(%rsp), %edx
	bswapl	%edx
	movl	%edx, 4(%rcx)
	movl	48(%rsp), %edx
	bswapl	%edx
	movl	%edx, 8(%rcx)
	movl	52(%rsp), %edx
	bswapl	%edx
	movl	%edx, 12(%rcx)
	movl	56(%rsp), %edx
	bswapl	%edx
	movl	%edx, 16(%rcx)
	movl	60(%rsp), %edx
	bswapl	%edx
	movl	%edx, 20(%rcx)
	movl	64(%rsp), %edx
	bswapl	%edx
	movl	%edx, 24(%rcx)
	movl	68(%rsp), %edx
	bswapl	%edx
	movl	%edx, 28(%rcx)
	movq	24(%rsp), %rdx
	ret
L_hash_message$1:
	leaq	24(%rsp), %r9
	movq	$2, %r11
	movb	%r11b, 31(%r9)
	shrq	$8, %r11
	movb	%r11b, 30(%r9)
	shrq	$8, %r11
	movb	%r11b, 29(%r9)
	shrq	$8, %r11
	movb	%r11b, 28(%r9)
	shrq	$8, %r11
	movb	%r11b, 27(%r9)
	shrq	$8, %r11
	movb	%r11b, 26(%r9)
	shrq	$8, %r11
	movb	%r11b, 25(%r9)
	shrq	$8, %r11
	movb	%r11b, 24(%r9)
	shrq	$8, %r11
	movb	%r11b, 23(%r9)
	shrq	$8, %r11
	movb	%r11b, 22(%r9)
	shrq	$8, %r11
	movb	%r11b, 21(%r9)
	shrq	$8, %r11
	movb	%r11b, 20(%r9)
	shrq	$8, %r11
	movb	%r11b, 19(%r9)
	shrq	$8, %r11
	movb	%r11b, 18(%r9)
	shrq	$8, %r11
	movb	%r11b, 17(%r9)
	shrq	$8, %r11
	movb	%r11b, 16(%r9)
	shrq	$8, %r11
	movb	%r11b, 15(%r9)
	shrq	$8, %r11
	movb	%r11b, 14(%r9)
	shrq	$8, %r11
	movb	%r11b, 13(%r9)
	shrq	$8, %r11
	movb	%r11b, 12(%r9)
	shrq	$8, %r11
	movb	%r11b, 11(%r9)
	shrq	$8, %r11
	movb	%r11b, 10(%r9)
	shrq	$8, %r11
	movb	%r11b, 9(%r9)
	shrq	$8, %r11
	movb	%r11b, 8(%r9)
	shrq	$8, %r11
	movb	%r11b, 7(%r9)
	shrq	$8, %r11
	movb	%r11b, 6(%r9)
	shrq	$8, %r11
	movb	%r11b, 5(%r9)
	shrq	$8, %r11
	movb	%r11b, 4(%r9)
	shrq	$8, %r11
	movb	%r11b, 3(%r9)
	shrq	$8, %r11
	movb	%r11b, 2(%r9)
	shrq	$8, %r11
	movb	%r11b, 1(%r9)
	shrq	$8, %r11
	movb	%r11b, (%r9)
	leaq	24(%rsp), %r9
	movq	$0, %rbx
	call	Lmemcpy_u8pu8_plen___memcpy_u8pu8$1
L_hash_message$11:
	movq	%r10, %r9
	movq	$32, %r10
	movq	(%rcx), %r11
	movq	%r11, (%r9,%r10)
	movq	8(%rcx), %r11
	movq	%r11, 8(%r9,%r10)
	movq	16(%rcx), %r11
	movq	%r11, 16(%r9,%r10)
	movq	24(%rcx), %rcx
	movq	%rcx, 24(%r9,%r10)
	movq	$64, %rcx
	movq	(%rsi), %r10
	movq	%r10, (%r9,%rcx)
	movq	8(%rsi), %r10
	movq	%r10, 8(%r9,%rcx)
	movq	16(%rsi), %r10
	movq	%r10, 16(%r9,%rcx)
	movq	24(%rsi), %rsi
	movq	%rsi, 24(%r9,%rcx)
	leaq	24(%rsp), %rcx
	movb	%dil, 31(%rcx)
	shrq	$8, %rdi
	movb	%dil, 30(%rcx)
	shrq	$8, %rdi
	movb	%dil, 29(%rcx)
	shrq	$8, %rdi
	movb	%dil, 28(%rcx)
	shrq	$8, %rdi
	movb	%dil, 27(%rcx)
	shrq	$8, %rdi
	movb	%dil, 26(%rcx)
	shrq	$8, %rdi
	movb	%dil, 25(%rcx)
	shrq	$8, %rdi
	movb	%dil, 24(%rcx)
	shrq	$8, %rdi
	movb	%dil, 23(%rcx)
	shrq	$8, %rdi
	movb	%dil, 22(%rcx)
	shrq	$8, %rdi
	movb	%dil, 21(%rcx)
	shrq	$8, %rdi
	movb	%dil, 20(%rcx)
	shrq	$8, %rdi
	movb	%dil, 19(%rcx)
	shrq	$8, %rdi
	movb	%dil, 18(%rcx)
	shrq	$8, %rdi
	movb	%dil, 17(%rcx)
	shrq	$8, %rdi
	movb	%dil, 16(%rcx)
	shrq	$8, %rdi
	movb	%dil, 15(%rcx)
	shrq	$8, %rdi
	movb	%dil, 14(%rcx)
	shrq	$8, %rdi
	movb	%dil, 13(%rcx)
	shrq	$8, %rdi
	movb	%dil, 12(%rcx)
	shrq	$8, %rdi
	movb	%dil, 11(%rcx)
	shrq	$8, %rdi
	movb	%dil, 10(%rcx)
	shrq	$8, %rdi
	movb	%dil, 9(%rcx)
	shrq	$8, %rdi
	movb	%dil, 8(%rcx)
	shrq	$8, %rdi
	movb	%dil, 7(%rcx)
	shrq	$8, %rdi
	movb	%dil, 6(%rcx)
	shrq	$8, %rdi
	movb	%dil, 5(%rcx)
	shrq	$8, %rdi
	movb	%dil, 4(%rcx)
	shrq	$8, %rdi
	movb	%dil, 3(%rcx)
	shrq	$8, %rdi
	movb	%dil, 2(%rcx)
	shrq	$8, %rdi
	movb	%dil, 1(%rcx)
	shrq	$8, %rdi
	movb	%dil, (%rcx)
	leaq	24(%rsp), %rcx
	movq	$96, %rdi
	call	Lmemcpy_u8pu8_n___memcpy_u8pu8$1
L_hash_message$10:
	movq	%r9, %rsi
	movq	%r8, %rcx
	addq	$128, %rcx
	movq	%rdx, 8(%rsp)
	movq	%rcx, %rdx
	shlq	$3, %rdx
	movq	%rdx, 16(%rsp)
	movl	$1779033703, 24(%rsp)
	movl	$-1150833019, 28(%rsp)
	movl	$1013904242, 32(%rsp)
	movl	$-1521486534, 36(%rsp)
	movl	$1359893119, 40(%rsp)
	movl	$-1694144372, 44(%rsp)
	movl	$528734635, 48(%rsp)
	movl	$1541459225, 52(%rsp)
	leaq	24(%rsp), %rdi
	leaq	-272(%rsp), %rsp
	call	L_blocks_0_ref$1
L_hash_message$9:
	leaq	272(%rsp), %rsp
	movq	16(%rsp), %rdx
	movq	$0, %rdi
	movl	%edi, 56(%rsp)
	movl	%edi, 60(%rsp)
	movl	%edi, 64(%rsp)
	movl	%edi, 68(%rsp)
	movl	%edi, 72(%rsp)
	movl	%edi, 76(%rsp)
	movl	%edi, 80(%rsp)
	movl	%edi, 84(%rsp)
	movl	%edi, 88(%rsp)
	movl	%edi, 92(%rsp)
	movl	%edi, 96(%rsp)
	movl	%edi, 100(%rsp)
	movl	%edi, 104(%rsp)
	movl	%edi, 108(%rsp)
	movl	%edi, 112(%rsp)
	movl	%edi, 116(%rsp)
	movl	%edi, 120(%rsp)
	movl	%edi, 124(%rsp)
	movl	%edi, 128(%rsp)
	movl	%edi, 132(%rsp)
	movl	%edi, 136(%rsp)
	movl	%edi, 140(%rsp)
	movl	%edi, 144(%rsp)
	movl	%edi, 148(%rsp)
	movl	%edi, 152(%rsp)
	movl	%edi, 156(%rsp)
	movl	%edi, 160(%rsp)
	movl	%edi, 164(%rsp)
	movl	%edi, 168(%rsp)
	movl	%edi, 172(%rsp)
	movl	%edi, 176(%rsp)
	movl	%edi, 180(%rsp)
	jmp 	L_hash_message$7
L_hash_message$8:
	movb	(%rsi,%rdi), %r8b
	movb	%r8b, 56(%rsp,%rdi)
	incq	%rdi
L_hash_message$7:
	cmpq	%rcx, %rdi
	jb  	L_hash_message$8
	movb	$128, 56(%rsp,%rdi)
	cmpq	$56, %rcx
	jb  	L_hash_message$5
	movq	$120, %rsi
	movq	$2, %r15
	movq	$127, %rcx
	jmp 	L_hash_message$3
L_hash_message$5:
	movq	$56, %rsi
	movq	$1, %r15
	movq	$63, %rcx
L_hash_message$6:
	jmp 	L_hash_message$3
L_hash_message$4:
	movb	%dl, 56(%rsp,%rcx)
	shrq	$8, %rdx
	addq	$-1, %rcx
L_hash_message$3:
	cmpq	%rsi, %rcx
	jnb 	L_hash_message$4
	leaq	56(%rsp), %rsi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_hash_message$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movl	24(%rsp), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movl	28(%rsp), %edx
	bswapl	%edx
	movl	%edx, 4(%rcx)
	movl	32(%rsp), %edx
	bswapl	%edx
	movl	%edx, 8(%rcx)
	movl	36(%rsp), %edx
	bswapl	%edx
	movl	%edx, 12(%rcx)
	movl	40(%rsp), %edx
	bswapl	%edx
	movl	%edx, 16(%rcx)
	movl	44(%rsp), %edx
	bswapl	%edx
	movl	%edx, 20(%rcx)
	movl	48(%rsp), %edx
	bswapl	%edx
	movl	%edx, 24(%rcx)
	movl	52(%rsp), %edx
	bswapl	%edx
	movl	%edx, 28(%rcx)
	ret
L_prf_keygen$1:
	leaq	32(%rsp), %rcx
	movq	$4, %rsi
	movb	%sil, 31(%rcx)
	shrq	$8, %rsi
	movb	%sil, 30(%rcx)
	shrq	$8, %rsi
	movb	%sil, 29(%rcx)
	shrq	$8, %rsi
	movb	%sil, 28(%rcx)
	shrq	$8, %rsi
	movb	%sil, 27(%rcx)
	shrq	$8, %rsi
	movb	%sil, 26(%rcx)
	shrq	$8, %rsi
	movb	%sil, 25(%rcx)
	shrq	$8, %rsi
	movb	%sil, 24(%rcx)
	shrq	$8, %rsi
	movb	%sil, 23(%rcx)
	shrq	$8, %rsi
	movb	%sil, 22(%rcx)
	shrq	$8, %rsi
	movb	%sil, 21(%rcx)
	shrq	$8, %rsi
	movb	%sil, 20(%rcx)
	shrq	$8, %rsi
	movb	%sil, 19(%rcx)
	shrq	$8, %rsi
	movb	%sil, 18(%rcx)
	shrq	$8, %rsi
	movb	%sil, 17(%rcx)
	shrq	$8, %rsi
	movb	%sil, 16(%rcx)
	shrq	$8, %rsi
	movb	%sil, 15(%rcx)
	shrq	$8, %rsi
	movb	%sil, 14(%rcx)
	shrq	$8, %rsi
	movb	%sil, 13(%rcx)
	shrq	$8, %rsi
	movb	%sil, 12(%rcx)
	shrq	$8, %rsi
	movb	%sil, 11(%rcx)
	shrq	$8, %rsi
	movb	%sil, 10(%rcx)
	shrq	$8, %rsi
	movb	%sil, 9(%rcx)
	shrq	$8, %rsi
	movb	%sil, 8(%rcx)
	shrq	$8, %rsi
	movb	%sil, 7(%rcx)
	shrq	$8, %rsi
	movb	%sil, 6(%rcx)
	shrq	$8, %rsi
	movb	%sil, 5(%rcx)
	shrq	$8, %rsi
	movb	%sil, 4(%rcx)
	shrq	$8, %rsi
	movb	%sil, 3(%rcx)
	shrq	$8, %rsi
	movb	%sil, 2(%rcx)
	shrq	$8, %rsi
	movb	%sil, 1(%rcx)
	shrq	$8, %rsi
	movb	%sil, (%rcx)
	leaq	64(%rsp), %rcx
	call	Lcopy_nbytes$1
L_prf_keygen$10:
	movq	(%r8), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%r8), %rcx
	movq	%rcx, 104(%rsp)
	movq	16(%r8), %rcx
	movq	%rcx, 112(%rsp)
	movq	24(%r8), %rcx
	movq	%rcx, 120(%rsp)
	movq	32(%r8), %rcx
	movq	%rcx, 128(%rsp)
	movq	40(%r8), %rcx
	movq	%rcx, 136(%rsp)
	movq	48(%r8), %rcx
	movq	%rcx, 144(%rsp)
	movq	56(%r8), %rcx
	movq	%rcx, 152(%rsp)
	leaq	32(%rsp), %rcx
	movq	%rdi, 8(%rsp)
	movq	$128, %rdx
	shlq	$3, %rdx
	movq	%rdx, 16(%rsp)
	movl	$1779033703, 160(%rsp)
	movl	$-1150833019, 164(%rsp)
	movl	$1013904242, 168(%rsp)
	movl	$-1521486534, 172(%rsp)
	movl	$1359893119, 176(%rsp)
	movl	$-1694144372, 180(%rsp)
	movl	$528734635, 184(%rsp)
	movl	$1541459225, 188(%rsp)
	movq	%rcx, 24(%rsp)
	leaq	160(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_prf_keygen$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rcx
	movq	16(%rsp), %rdx
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
	movb	(%rcx,%r9), %r9b
	movb	%r9b, 192(%rsp,%r8)
	incq	%r8
L_prf_keygen$7:
	cmpq	%rdi, %r8
	jb  	L_prf_keygen$8
	movb	$128, 192(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_prf_keygen$5
	movq	$120, %rsi
	movq	$2, %r15
	movq	$127, %rcx
	jmp 	L_prf_keygen$3
L_prf_keygen$5:
	movq	$56, %rsi
	movq	$1, %r15
	movq	$63, %rcx
L_prf_keygen$6:
	jmp 	L_prf_keygen$3
L_prf_keygen$4:
	movb	%dl, 192(%rsp,%rcx)
	shrq	$8, %rdx
	addq	$-1, %rcx
L_prf_keygen$3:
	cmpq	%rsi, %rcx
	jnb 	L_prf_keygen$4
	leaq	192(%rsp), %rsi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_prf_keygen$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movl	160(%rsp), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movl	164(%rsp), %edx
	bswapl	%edx
	movl	%edx, 4(%rcx)
	movl	168(%rsp), %edx
	bswapl	%edx
	movl	%edx, 8(%rcx)
	movl	172(%rsp), %edx
	bswapl	%edx
	movl	%edx, 12(%rcx)
	movl	176(%rsp), %edx
	bswapl	%edx
	movl	%edx, 16(%rcx)
	movl	180(%rsp), %edx
	bswapl	%edx
	movl	%edx, 20(%rcx)
	movl	184(%rsp), %edx
	bswapl	%edx
	movl	%edx, 24(%rcx)
	movl	188(%rsp), %edx
	bswapl	%edx
	movl	%edx, 28(%rcx)
	ret
L_prf$1:
	leaq	32(%rsp), %rcx
	movq	$3, %rsi
	movb	%sil, 31(%rcx)
	shrq	$8, %rsi
	movb	%sil, 30(%rcx)
	shrq	$8, %rsi
	movb	%sil, 29(%rcx)
	shrq	$8, %rsi
	movb	%sil, 28(%rcx)
	shrq	$8, %rsi
	movb	%sil, 27(%rcx)
	shrq	$8, %rsi
	movb	%sil, 26(%rcx)
	shrq	$8, %rsi
	movb	%sil, 25(%rcx)
	shrq	$8, %rsi
	movb	%sil, 24(%rcx)
	shrq	$8, %rsi
	movb	%sil, 23(%rcx)
	shrq	$8, %rsi
	movb	%sil, 22(%rcx)
	shrq	$8, %rsi
	movb	%sil, 21(%rcx)
	shrq	$8, %rsi
	movb	%sil, 20(%rcx)
	shrq	$8, %rsi
	movb	%sil, 19(%rcx)
	shrq	$8, %rsi
	movb	%sil, 18(%rcx)
	shrq	$8, %rsi
	movb	%sil, 17(%rcx)
	shrq	$8, %rsi
	movb	%sil, 16(%rcx)
	shrq	$8, %rsi
	movb	%sil, 15(%rcx)
	shrq	$8, %rsi
	movb	%sil, 14(%rcx)
	shrq	$8, %rsi
	movb	%sil, 13(%rcx)
	shrq	$8, %rsi
	movb	%sil, 12(%rcx)
	shrq	$8, %rsi
	movb	%sil, 11(%rcx)
	shrq	$8, %rsi
	movb	%sil, 10(%rcx)
	shrq	$8, %rsi
	movb	%sil, 9(%rcx)
	shrq	$8, %rsi
	movb	%sil, 8(%rcx)
	shrq	$8, %rsi
	movb	%sil, 7(%rcx)
	shrq	$8, %rsi
	movb	%sil, 6(%rcx)
	shrq	$8, %rsi
	movb	%sil, 5(%rcx)
	shrq	$8, %rsi
	movb	%sil, 4(%rcx)
	shrq	$8, %rsi
	movb	%sil, 3(%rcx)
	shrq	$8, %rsi
	movb	%sil, 2(%rcx)
	shrq	$8, %rsi
	movb	%sil, 1(%rcx)
	shrq	$8, %rsi
	movb	%sil, (%rcx)
	leaq	64(%rsp), %rcx
	call	Lcopy_nbytes$1
L_prf$10:
	movq	(%r8), %rcx
	movq	%rcx, 96(%rsp)
	movq	8(%r8), %rcx
	movq	%rcx, 104(%rsp)
	movq	16(%r8), %rcx
	movq	%rcx, 112(%rsp)
	movq	24(%r8), %rcx
	movq	%rcx, 120(%rsp)
	leaq	32(%rsp), %rcx
	movq	%rdi, 8(%rsp)
	movq	$96, %rdx
	shlq	$3, %rdx
	movq	%rdx, 16(%rsp)
	movl	$1779033703, 128(%rsp)
	movl	$-1150833019, 132(%rsp)
	movl	$1013904242, 136(%rsp)
	movl	$-1521486534, 140(%rsp)
	movl	$1359893119, 144(%rsp)
	movl	$-1694144372, 148(%rsp)
	movl	$528734635, 152(%rsp)
	movl	$1541459225, 156(%rsp)
	movq	%rcx, 24(%rsp)
	leaq	128(%rsp), %r8
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_prf$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rcx
	movq	16(%rsp), %rdx
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
	movb	(%rcx,%r9), %r9b
	movb	%r9b, 160(%rsp,%r8)
	incq	%r8
L_prf$7:
	cmpq	%rdi, %r8
	jb  	L_prf$8
	movb	$128, 160(%rsp,%r8)
	cmpq	$56, %rdi
	jb  	L_prf$5
	movq	$120, %rsi
	movq	$2, %r15
	movq	$127, %rcx
	jmp 	L_prf$3
L_prf$5:
	movq	$56, %rsi
	movq	$1, %r15
	movq	$63, %rcx
L_prf$6:
	jmp 	L_prf$3
L_prf$4:
	movb	%dl, 160(%rsp,%rcx)
	shrq	$8, %rdx
	addq	$-1, %rcx
L_prf$3:
	cmpq	%rsi, %rcx
	jnb 	L_prf$4
	leaq	160(%rsp), %rsi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
L_prf$2:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movl	128(%rsp), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	movl	132(%rsp), %edx
	bswapl	%edx
	movl	%edx, 4(%rcx)
	movl	136(%rsp), %edx
	bswapl	%edx
	movl	%edx, 8(%rcx)
	movl	140(%rsp), %edx
	bswapl	%edx
	movl	%edx, 12(%rcx)
	movl	144(%rsp), %edx
	bswapl	%edx
	movl	%edx, 16(%rcx)
	movl	148(%rsp), %edx
	bswapl	%edx
	movl	%edx, 20(%rcx)
	movl	152(%rsp), %edx
	bswapl	%edx
	movl	%edx, 24(%rcx)
	movl	156(%rsp), %edx
	bswapl	%edx
	movl	%edx, 28(%rcx)
	ret
Lhash_plen_3n___blocks_0_ref_array$1:
	movq	$0, %rsi
	movq	$128, %rdi
	leaq	glob_data + 0(%rip), %rdx
	movq	%r8, 8(%rsp)
	movq	8(%rsp), %r11
	jmp 	Lhash_plen_3n___blocks_0_ref_array$2
Lhash_plen_3n___blocks_0_ref_array$3:
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
	movl	88(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	68(%rsp), %esi
	movl	36(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	32(%rsp), %esi
	movl	%esi, 96(%rsp)
	movl	92(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	72(%rsp), %esi
	movl	40(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	36(%rsp), %esi
	movl	%esi, 100(%rsp)
	movl	96(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	76(%rsp), %esi
	movl	44(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	40(%rsp), %esi
	movl	%esi, 104(%rsp)
	movl	100(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	80(%rsp), %esi
	movl	48(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	44(%rsp), %esi
	movl	%esi, 108(%rsp)
	movl	104(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	84(%rsp), %esi
	movl	52(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	48(%rsp), %esi
	movl	%esi, 112(%rsp)
	movl	108(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	88(%rsp), %esi
	movl	56(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	52(%rsp), %esi
	movl	%esi, 116(%rsp)
	movl	112(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	92(%rsp), %esi
	movl	60(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	56(%rsp), %esi
	movl	%esi, 120(%rsp)
	movl	116(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	96(%rsp), %esi
	movl	64(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	60(%rsp), %esi
	movl	%esi, 124(%rsp)
	movl	120(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	100(%rsp), %esi
	movl	68(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	64(%rsp), %esi
	movl	%esi, 128(%rsp)
	movl	124(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	104(%rsp), %esi
	movl	72(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	68(%rsp), %esi
	movl	%esi, 132(%rsp)
	movl	128(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	108(%rsp), %esi
	movl	76(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	72(%rsp), %esi
	movl	%esi, 136(%rsp)
	movl	132(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	112(%rsp), %esi
	movl	80(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	76(%rsp), %esi
	movl	%esi, 140(%rsp)
	movl	136(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	116(%rsp), %esi
	movl	84(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	80(%rsp), %esi
	movl	%esi, 144(%rsp)
	movl	140(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	120(%rsp), %esi
	movl	88(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	84(%rsp), %esi
	movl	%esi, 148(%rsp)
	movl	144(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	124(%rsp), %esi
	movl	92(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	88(%rsp), %esi
	movl	%esi, 152(%rsp)
	movl	148(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	128(%rsp), %esi
	movl	96(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	92(%rsp), %esi
	movl	%esi, 156(%rsp)
	movl	152(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	132(%rsp), %esi
	movl	100(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	96(%rsp), %esi
	movl	%esi, 160(%rsp)
	movl	156(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	136(%rsp), %esi
	movl	104(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	100(%rsp), %esi
	movl	%esi, 164(%rsp)
	movl	160(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	140(%rsp), %esi
	movl	108(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	104(%rsp), %esi
	movl	%esi, 168(%rsp)
	movl	164(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	144(%rsp), %esi
	movl	112(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	108(%rsp), %esi
	movl	%esi, 172(%rsp)
	movl	168(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	148(%rsp), %esi
	movl	116(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	112(%rsp), %esi
	movl	%esi, 176(%rsp)
	movl	172(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	152(%rsp), %esi
	movl	120(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	116(%rsp), %esi
	movl	%esi, 180(%rsp)
	movl	176(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	156(%rsp), %esi
	movl	124(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	120(%rsp), %esi
	movl	%esi, 184(%rsp)
	movl	180(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	160(%rsp), %esi
	movl	128(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	124(%rsp), %esi
	movl	%esi, 188(%rsp)
	movl	184(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	164(%rsp), %esi
	movl	132(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	128(%rsp), %esi
	movl	%esi, 192(%rsp)
	movl	188(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	168(%rsp), %esi
	movl	136(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	132(%rsp), %esi
	movl	%esi, 196(%rsp)
	movl	192(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	172(%rsp), %esi
	movl	140(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	136(%rsp), %esi
	movl	%esi, 200(%rsp)
	movl	196(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	176(%rsp), %esi
	movl	144(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	140(%rsp), %esi
	movl	%esi, 204(%rsp)
	movl	200(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	180(%rsp), %esi
	movl	148(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	144(%rsp), %esi
	movl	%esi, 208(%rsp)
	movl	204(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	184(%rsp), %esi
	movl	152(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	148(%rsp), %esi
	movl	%esi, 212(%rsp)
	movl	208(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	188(%rsp), %esi
	movl	156(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	152(%rsp), %esi
	movl	%esi, 216(%rsp)
	movl	212(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	192(%rsp), %esi
	movl	160(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	156(%rsp), %esi
	movl	%esi, 220(%rsp)
	movl	216(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	196(%rsp), %esi
	movl	164(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	160(%rsp), %esi
	movl	%esi, 224(%rsp)
	movl	220(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	200(%rsp), %esi
	movl	168(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	164(%rsp), %esi
	movl	%esi, 228(%rsp)
	movl	224(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	204(%rsp), %esi
	movl	172(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	168(%rsp), %esi
	movl	%esi, 232(%rsp)
	movl	228(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	208(%rsp), %esi
	movl	176(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	172(%rsp), %esi
	movl	%esi, 236(%rsp)
	movl	232(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	212(%rsp), %esi
	movl	180(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	176(%rsp), %esi
	movl	%esi, 240(%rsp)
	movl	236(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	216(%rsp), %esi
	movl	184(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	180(%rsp), %esi
	movl	%esi, 244(%rsp)
	movl	240(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	220(%rsp), %esi
	movl	188(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	184(%rsp), %esi
	movl	%esi, 248(%rsp)
	movl	244(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	224(%rsp), %esi
	movl	192(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	188(%rsp), %esi
	movl	%esi, 252(%rsp)
	movl	248(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	228(%rsp), %esi
	movl	196(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	192(%rsp), %esi
	movl	%esi, 256(%rsp)
	movl	252(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	232(%rsp), %esi
	movl	200(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	196(%rsp), %esi
	movl	%esi, 260(%rsp)
	movl	256(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	236(%rsp), %esi
	movl	204(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	200(%rsp), %esi
	movl	%esi, 264(%rsp)
	movl	260(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	240(%rsp), %esi
	movl	208(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	204(%rsp), %esi
	movl	%esi, 268(%rsp)
	movl	264(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	244(%rsp), %esi
	movl	212(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	208(%rsp), %esi
	movl	%esi, 272(%rsp)
	movl	268(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	248(%rsp), %esi
	movl	216(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	212(%rsp), %esi
	movl	%esi, 276(%rsp)
	movl	272(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	252(%rsp), %esi
	movl	220(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	216(%rsp), %esi
	movl	%esi, 280(%rsp)
	movl	276(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	256(%rsp), %esi
	movl	224(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	220(%rsp), %esi
	movl	%esi, 284(%rsp)
	movl	(%r11), %r14d
	movl	4(%r11), %esi
	movl	8(%r11), %edi
	movl	12(%r11), %r8d
	movl	16(%r11), %r13d
	movl	20(%r11), %r9d
	movl	24(%r11), %r10d
	movl	28(%r11), %r12d
	movq	%r11, 24(%rsp)
	movq	$0, %r11
	jmp 	Lhash_plen_3n___blocks_0_ref_array$4
Lhash_plen_3n___blocks_0_ref_array$5:
	movl	%r12d, %ebx
	movl	%r13d, %ebp
	rorl	$6, %ebp
	movl	%r13d, %r12d
	rorl	$11, %r12d
	xorl	%r12d, %ebp
	movl	%r13d, %r12d
	rorl	$25, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r13d, %ebp
	andl	%r9d, %ebp
	movl	%r13d, %r12d
	notl	%r12d
	andl	%r10d, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	addl	(%rdx,%r11,4), %ebx
	addl	32(%rsp,%r11,4), %ebx
	movl	%r14d, %ebp
	rorl	$2, %ebp
	movl	%r14d, %r12d
	rorl	$13, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	rorl	$22, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	movl	%r14d, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	movl	%esi, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	addl	%r12d, %ebp
	movl	%r10d, %r12d
	movl	%r9d, %r10d
	movl	%r13d, %r9d
	movl	%r8d, %r13d
	addl	%ebx, %r13d
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r14d, %esi
	movl	%ebx, %r14d
	addl	%ebp, %r14d
	incq	%r11
Lhash_plen_3n___blocks_0_ref_array$4:
	cmpq	$64, %r11
	jb  	Lhash_plen_3n___blocks_0_ref_array$5
	movq	24(%rsp), %r11
	addl	(%r11), %r14d
	addl	4(%r11), %esi
	addl	8(%r11), %edi
	addl	12(%r11), %r8d
	addl	16(%r11), %r13d
	addl	20(%r11), %r9d
	addl	24(%r11), %r10d
	addl	28(%r11), %r12d
	movl	%r14d, (%r11)
	movl	%esi, 4(%r11)
	movl	%edi, 8(%r11)
	movl	%r8d, 12(%r11)
	movl	%r13d, 16(%r11)
	movl	%r9d, 20(%r11)
	movl	%r10d, 24(%r11)
	movl	%r12d, 28(%r11)
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
	leaq	glob_data + 0(%rip), %rdx
	movq	%r8, 8(%rsp)
	movq	8(%rsp), %r11
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
	movl	88(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	68(%rsp), %esi
	movl	36(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	32(%rsp), %esi
	movl	%esi, 96(%rsp)
	movl	92(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	72(%rsp), %esi
	movl	40(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	36(%rsp), %esi
	movl	%esi, 100(%rsp)
	movl	96(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	76(%rsp), %esi
	movl	44(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	40(%rsp), %esi
	movl	%esi, 104(%rsp)
	movl	100(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	80(%rsp), %esi
	movl	48(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	44(%rsp), %esi
	movl	%esi, 108(%rsp)
	movl	104(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	84(%rsp), %esi
	movl	52(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	48(%rsp), %esi
	movl	%esi, 112(%rsp)
	movl	108(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	88(%rsp), %esi
	movl	56(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	52(%rsp), %esi
	movl	%esi, 116(%rsp)
	movl	112(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	92(%rsp), %esi
	movl	60(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	56(%rsp), %esi
	movl	%esi, 120(%rsp)
	movl	116(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	96(%rsp), %esi
	movl	64(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	60(%rsp), %esi
	movl	%esi, 124(%rsp)
	movl	120(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	100(%rsp), %esi
	movl	68(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	64(%rsp), %esi
	movl	%esi, 128(%rsp)
	movl	124(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	104(%rsp), %esi
	movl	72(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	68(%rsp), %esi
	movl	%esi, 132(%rsp)
	movl	128(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	108(%rsp), %esi
	movl	76(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	72(%rsp), %esi
	movl	%esi, 136(%rsp)
	movl	132(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	112(%rsp), %esi
	movl	80(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	76(%rsp), %esi
	movl	%esi, 140(%rsp)
	movl	136(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	116(%rsp), %esi
	movl	84(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	80(%rsp), %esi
	movl	%esi, 144(%rsp)
	movl	140(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	120(%rsp), %esi
	movl	88(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	84(%rsp), %esi
	movl	%esi, 148(%rsp)
	movl	144(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	124(%rsp), %esi
	movl	92(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	88(%rsp), %esi
	movl	%esi, 152(%rsp)
	movl	148(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	128(%rsp), %esi
	movl	96(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	92(%rsp), %esi
	movl	%esi, 156(%rsp)
	movl	152(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	132(%rsp), %esi
	movl	100(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	96(%rsp), %esi
	movl	%esi, 160(%rsp)
	movl	156(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	136(%rsp), %esi
	movl	104(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	100(%rsp), %esi
	movl	%esi, 164(%rsp)
	movl	160(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	140(%rsp), %esi
	movl	108(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	104(%rsp), %esi
	movl	%esi, 168(%rsp)
	movl	164(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	144(%rsp), %esi
	movl	112(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	108(%rsp), %esi
	movl	%esi, 172(%rsp)
	movl	168(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	148(%rsp), %esi
	movl	116(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	112(%rsp), %esi
	movl	%esi, 176(%rsp)
	movl	172(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	152(%rsp), %esi
	movl	120(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	116(%rsp), %esi
	movl	%esi, 180(%rsp)
	movl	176(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	156(%rsp), %esi
	movl	124(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	120(%rsp), %esi
	movl	%esi, 184(%rsp)
	movl	180(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	160(%rsp), %esi
	movl	128(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	124(%rsp), %esi
	movl	%esi, 188(%rsp)
	movl	184(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	164(%rsp), %esi
	movl	132(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	128(%rsp), %esi
	movl	%esi, 192(%rsp)
	movl	188(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	168(%rsp), %esi
	movl	136(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	132(%rsp), %esi
	movl	%esi, 196(%rsp)
	movl	192(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	172(%rsp), %esi
	movl	140(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	136(%rsp), %esi
	movl	%esi, 200(%rsp)
	movl	196(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	176(%rsp), %esi
	movl	144(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	140(%rsp), %esi
	movl	%esi, 204(%rsp)
	movl	200(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	180(%rsp), %esi
	movl	148(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	144(%rsp), %esi
	movl	%esi, 208(%rsp)
	movl	204(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	184(%rsp), %esi
	movl	152(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	148(%rsp), %esi
	movl	%esi, 212(%rsp)
	movl	208(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	188(%rsp), %esi
	movl	156(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	152(%rsp), %esi
	movl	%esi, 216(%rsp)
	movl	212(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	192(%rsp), %esi
	movl	160(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	156(%rsp), %esi
	movl	%esi, 220(%rsp)
	movl	216(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	196(%rsp), %esi
	movl	164(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	160(%rsp), %esi
	movl	%esi, 224(%rsp)
	movl	220(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	200(%rsp), %esi
	movl	168(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	164(%rsp), %esi
	movl	%esi, 228(%rsp)
	movl	224(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	204(%rsp), %esi
	movl	172(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	168(%rsp), %esi
	movl	%esi, 232(%rsp)
	movl	228(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	208(%rsp), %esi
	movl	176(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	172(%rsp), %esi
	movl	%esi, 236(%rsp)
	movl	232(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	212(%rsp), %esi
	movl	180(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	176(%rsp), %esi
	movl	%esi, 240(%rsp)
	movl	236(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	216(%rsp), %esi
	movl	184(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	180(%rsp), %esi
	movl	%esi, 244(%rsp)
	movl	240(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	220(%rsp), %esi
	movl	188(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	184(%rsp), %esi
	movl	%esi, 248(%rsp)
	movl	244(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	224(%rsp), %esi
	movl	192(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	188(%rsp), %esi
	movl	%esi, 252(%rsp)
	movl	248(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	228(%rsp), %esi
	movl	196(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	192(%rsp), %esi
	movl	%esi, 256(%rsp)
	movl	252(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	232(%rsp), %esi
	movl	200(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	196(%rsp), %esi
	movl	%esi, 260(%rsp)
	movl	256(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	236(%rsp), %esi
	movl	204(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	200(%rsp), %esi
	movl	%esi, 264(%rsp)
	movl	260(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	240(%rsp), %esi
	movl	208(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	204(%rsp), %esi
	movl	%esi, 268(%rsp)
	movl	264(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	244(%rsp), %esi
	movl	212(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	208(%rsp), %esi
	movl	%esi, 272(%rsp)
	movl	268(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	248(%rsp), %esi
	movl	216(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	212(%rsp), %esi
	movl	%esi, 276(%rsp)
	movl	272(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	252(%rsp), %esi
	movl	220(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	216(%rsp), %esi
	movl	%esi, 280(%rsp)
	movl	276(%rsp), %edi
	movl	%edi, %esi
	rorl	$17, %esi
	movl	%edi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %esi
	shrl	$10, %edi
	xorl	%edi, %esi
	addl	256(%rsp), %esi
	movl	224(%rsp), %edi
	movl	%edi, %r8d
	rorl	$7, %r8d
	movl	%edi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edi
	xorl	%edi, %r8d
	addl	%r8d, %esi
	addl	220(%rsp), %esi
	movl	%esi, 284(%rsp)
	movl	(%r11), %r14d
	movl	4(%r11), %esi
	movl	8(%r11), %edi
	movl	12(%r11), %r8d
	movl	16(%r11), %r13d
	movl	20(%r11), %r9d
	movl	24(%r11), %r10d
	movl	28(%r11), %r12d
	movq	%r11, 24(%rsp)
	movq	$0, %r11
	jmp 	Lhash_plen_2n___blocks_0_ref_array$4
Lhash_plen_2n___blocks_0_ref_array$5:
	movl	%r12d, %ebx
	movl	%r13d, %ebp
	rorl	$6, %ebp
	movl	%r13d, %r12d
	rorl	$11, %r12d
	xorl	%r12d, %ebp
	movl	%r13d, %r12d
	rorl	$25, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r13d, %ebp
	andl	%r9d, %ebp
	movl	%r13d, %r12d
	notl	%r12d
	andl	%r10d, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	addl	(%rdx,%r11,4), %ebx
	addl	32(%rsp,%r11,4), %ebx
	movl	%r14d, %ebp
	rorl	$2, %ebp
	movl	%r14d, %r12d
	rorl	$13, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	rorl	$22, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	movl	%r14d, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	movl	%esi, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	addl	%r12d, %ebp
	movl	%r10d, %r12d
	movl	%r9d, %r10d
	movl	%r13d, %r9d
	movl	%r8d, %r13d
	addl	%ebx, %r13d
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r14d, %esi
	movl	%ebx, %r14d
	addl	%ebp, %r14d
	incq	%r11
Lhash_plen_2n___blocks_0_ref_array$4:
	cmpq	$64, %r11
	jb  	Lhash_plen_2n___blocks_0_ref_array$5
	movq	24(%rsp), %r11
	addl	(%r11), %r14d
	addl	4(%r11), %esi
	addl	8(%r11), %edi
	addl	12(%r11), %r8d
	addl	16(%r11), %r13d
	addl	20(%r11), %r9d
	addl	24(%r11), %r10d
	addl	28(%r11), %r12d
	movl	%r14d, (%r11)
	movl	%esi, 4(%r11)
	movl	%edi, 8(%r11)
	movl	%r8d, 12(%r11)
	movl	%r13d, 16(%r11)
	movl	%r9d, 20(%r11)
	movl	%r10d, 24(%r11)
	movl	%r12d, 28(%r11)
	movq	16(%rsp), %rsi
	movq	8(%rsp), %rdi
	addq	$64, %rsi
	addq	$-64, %rdi
Lhash_plen_2n___blocks_0_ref_array$2:
	cmpq	$64, %rdi
	jnb 	Lhash_plen_2n___blocks_0_ref_array$3
	ret
L_blocks_0_ref$1:
	leaq	glob_data + 0(%rip), %rdx
	movq	%rdi, 8(%rsp)
	movq	8(%rsp), %r11
	jmp 	L_blocks_0_ref$2
L_blocks_0_ref$3:
	movl	(%rsi), %edi
	bswapl	%edi
	movl	%edi, 24(%rsp)
	movl	4(%rsi), %edi
	bswapl	%edi
	movl	%edi, 28(%rsp)
	movl	8(%rsi), %edi
	bswapl	%edi
	movl	%edi, 32(%rsp)
	movl	12(%rsi), %edi
	bswapl	%edi
	movl	%edi, 36(%rsp)
	movl	16(%rsi), %edi
	bswapl	%edi
	movl	%edi, 40(%rsp)
	movl	20(%rsi), %edi
	bswapl	%edi
	movl	%edi, 44(%rsp)
	movl	24(%rsi), %edi
	bswapl	%edi
	movl	%edi, 48(%rsp)
	movl	28(%rsi), %edi
	bswapl	%edi
	movl	%edi, 52(%rsp)
	movl	32(%rsi), %edi
	bswapl	%edi
	movl	%edi, 56(%rsp)
	movl	36(%rsi), %edi
	bswapl	%edi
	movl	%edi, 60(%rsp)
	movl	40(%rsi), %edi
	bswapl	%edi
	movl	%edi, 64(%rsp)
	movl	44(%rsi), %edi
	bswapl	%edi
	movl	%edi, 68(%rsp)
	movl	48(%rsi), %edi
	bswapl	%edi
	movl	%edi, 72(%rsp)
	movl	52(%rsi), %edi
	bswapl	%edi
	movl	%edi, 76(%rsp)
	movl	56(%rsi), %edi
	bswapl	%edi
	movl	%edi, 80(%rsp)
	movl	60(%rsi), %edi
	bswapl	%edi
	movl	%edi, 84(%rsp)
	movq	%rsi, 8(%rsp)
	movl	80(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	60(%rsp), %edi
	movl	28(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	24(%rsp), %edi
	movl	%edi, 88(%rsp)
	movl	84(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	64(%rsp), %edi
	movl	32(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	28(%rsp), %edi
	movl	%edi, 92(%rsp)
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
	movl	(%r11), %r14d
	movl	4(%r11), %esi
	movl	8(%r11), %edi
	movl	12(%r11), %r8d
	movl	16(%r11), %r13d
	movl	20(%r11), %r9d
	movl	24(%r11), %r10d
	movl	28(%r11), %r12d
	movq	%r11, 16(%rsp)
	movq	$0, %r11
	jmp 	L_blocks_0_ref$4
L_blocks_0_ref$5:
	movl	%r12d, %ebx
	movl	%r13d, %ebp
	rorl	$6, %ebp
	movl	%r13d, %r12d
	rorl	$11, %r12d
	xorl	%r12d, %ebp
	movl	%r13d, %r12d
	rorl	$25, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r13d, %ebp
	andl	%r9d, %ebp
	movl	%r13d, %r12d
	notl	%r12d
	andl	%r10d, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	addl	(%rdx,%r11,4), %ebx
	addl	24(%rsp,%r11,4), %ebx
	movl	%r14d, %ebp
	rorl	$2, %ebp
	movl	%r14d, %r12d
	rorl	$13, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	rorl	$22, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	movl	%r14d, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	movl	%esi, %r15d
	andl	%edi, %r15d
	xorl	%r15d, %r12d
	addl	%r12d, %ebp
	movl	%r10d, %r12d
	movl	%r9d, %r10d
	movl	%r13d, %r9d
	movl	%r8d, %r13d
	addl	%ebx, %r13d
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r14d, %esi
	movl	%ebx, %r14d
	addl	%ebp, %r14d
	incq	%r11
L_blocks_0_ref$4:
	cmpq	$64, %r11
	jb  	L_blocks_0_ref$5
	movq	16(%rsp), %r11
	addl	(%r11), %r14d
	addl	4(%r11), %esi
	addl	8(%r11), %edi
	addl	12(%r11), %r8d
	addl	16(%r11), %r13d
	addl	20(%r11), %r9d
	addl	24(%r11), %r10d
	addl	28(%r11), %r12d
	movl	%r14d, (%r11)
	movl	%esi, 4(%r11)
	movl	%edi, 8(%r11)
	movl	%r8d, 12(%r11)
	movl	%r13d, 16(%r11)
	movl	%r9d, 20(%r11)
	movl	%r10d, 24(%r11)
	movl	%r12d, 28(%r11)
	movq	8(%rsp), %rsi
	addq	$64, %rsi
	addq	$-64, %rcx
L_blocks_0_ref$2:
	cmpq	$64, %rcx
	jnb 	L_blocks_0_ref$3
	ret
L_blocks_1_ref$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%r11, 8(%rsp)
	movq	$0, %rdx
	movq	8(%rsp), %r10
	jmp 	L_blocks_1_ref$2
L_blocks_1_ref$3:
	movq	%rdx, 8(%rsp)
	shlq	$4, %rdx
	movl	(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 32(%rsp)
	movl	4(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 36(%rsp)
	movl	8(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 40(%rsp)
	movl	12(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 44(%rsp)
	movl	16(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 48(%rsp)
	movl	20(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 52(%rsp)
	movl	24(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 56(%rsp)
	movl	28(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 60(%rsp)
	movl	32(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 64(%rsp)
	movl	36(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 68(%rsp)
	movl	40(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 72(%rsp)
	movl	44(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 76(%rsp)
	movl	48(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 80(%rsp)
	movl	52(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 84(%rsp)
	movl	56(%rsi,%rdx,4), %edi
	bswapl	%edi
	movl	%edi, 88(%rsp)
	movl	60(%rsi,%rdx,4), %edx
	bswapl	%edx
	movl	%edx, 92(%rsp)
	movq	%rsi, 16(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	68(%rsp), %edx
	movl	36(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	32(%rsp), %edx
	movl	%edx, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	72(%rsp), %edx
	movl	40(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	36(%rsp), %edx
	movl	%edx, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	76(%rsp), %edx
	movl	44(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	40(%rsp), %edx
	movl	%edx, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	80(%rsp), %edx
	movl	48(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	44(%rsp), %edx
	movl	%edx, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	84(%rsp), %edx
	movl	52(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	48(%rsp), %edx
	movl	%edx, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	88(%rsp), %edx
	movl	56(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	52(%rsp), %edx
	movl	%edx, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	92(%rsp), %edx
	movl	60(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	56(%rsp), %edx
	movl	%edx, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	96(%rsp), %edx
	movl	64(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	60(%rsp), %edx
	movl	%edx, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	100(%rsp), %edx
	movl	68(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	64(%rsp), %edx
	movl	%edx, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	104(%rsp), %edx
	movl	72(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	68(%rsp), %edx
	movl	%edx, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	108(%rsp), %edx
	movl	76(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	72(%rsp), %edx
	movl	%edx, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	112(%rsp), %edx
	movl	80(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	76(%rsp), %edx
	movl	%edx, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	116(%rsp), %edx
	movl	84(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	80(%rsp), %edx
	movl	%edx, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	120(%rsp), %edx
	movl	88(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	84(%rsp), %edx
	movl	%edx, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	124(%rsp), %edx
	movl	92(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	88(%rsp), %edx
	movl	%edx, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	128(%rsp), %edx
	movl	96(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	92(%rsp), %edx
	movl	%edx, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	132(%rsp), %edx
	movl	100(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	96(%rsp), %edx
	movl	%edx, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	136(%rsp), %edx
	movl	104(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	100(%rsp), %edx
	movl	%edx, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	140(%rsp), %edx
	movl	108(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	104(%rsp), %edx
	movl	%edx, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	144(%rsp), %edx
	movl	112(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	108(%rsp), %edx
	movl	%edx, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	148(%rsp), %edx
	movl	116(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	112(%rsp), %edx
	movl	%edx, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	152(%rsp), %edx
	movl	120(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	116(%rsp), %edx
	movl	%edx, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	156(%rsp), %edx
	movl	124(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	120(%rsp), %edx
	movl	%edx, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	160(%rsp), %edx
	movl	128(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	124(%rsp), %edx
	movl	%edx, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	164(%rsp), %edx
	movl	132(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	128(%rsp), %edx
	movl	%edx, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	168(%rsp), %edx
	movl	136(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	132(%rsp), %edx
	movl	%edx, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	172(%rsp), %edx
	movl	140(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	136(%rsp), %edx
	movl	%edx, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	176(%rsp), %edx
	movl	144(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	140(%rsp), %edx
	movl	%edx, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	180(%rsp), %edx
	movl	148(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	144(%rsp), %edx
	movl	%edx, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	184(%rsp), %edx
	movl	152(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	148(%rsp), %edx
	movl	%edx, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	188(%rsp), %edx
	movl	156(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	152(%rsp), %edx
	movl	%edx, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	192(%rsp), %edx
	movl	160(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	156(%rsp), %edx
	movl	%edx, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	196(%rsp), %edx
	movl	164(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	160(%rsp), %edx
	movl	%edx, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	200(%rsp), %edx
	movl	168(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	164(%rsp), %edx
	movl	%edx, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	204(%rsp), %edx
	movl	172(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	168(%rsp), %edx
	movl	%edx, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	208(%rsp), %edx
	movl	176(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	172(%rsp), %edx
	movl	%edx, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	212(%rsp), %edx
	movl	180(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	176(%rsp), %edx
	movl	%edx, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	216(%rsp), %edx
	movl	184(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	180(%rsp), %edx
	movl	%edx, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	220(%rsp), %edx
	movl	188(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	184(%rsp), %edx
	movl	%edx, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	224(%rsp), %edx
	movl	192(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	188(%rsp), %edx
	movl	%edx, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	228(%rsp), %edx
	movl	196(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	192(%rsp), %edx
	movl	%edx, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	232(%rsp), %edx
	movl	200(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	196(%rsp), %edx
	movl	%edx, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	236(%rsp), %edx
	movl	204(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	200(%rsp), %edx
	movl	%edx, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	240(%rsp), %edx
	movl	208(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	204(%rsp), %edx
	movl	%edx, 268(%rsp)
	movl	264(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	244(%rsp), %edx
	movl	212(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	208(%rsp), %edx
	movl	%edx, 272(%rsp)
	movl	268(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	248(%rsp), %edx
	movl	216(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	212(%rsp), %edx
	movl	%edx, 276(%rsp)
	movl	272(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	252(%rsp), %edx
	movl	220(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	216(%rsp), %edx
	movl	%edx, 280(%rsp)
	movl	276(%rsp), %esi
	movl	%esi, %edx
	rorl	$17, %edx
	movl	%esi, %edi
	rorl	$19, %edi
	xorl	%edi, %edx
	shrl	$10, %esi
	xorl	%esi, %edx
	addl	256(%rsp), %edx
	movl	224(%rsp), %esi
	movl	%esi, %edi
	rorl	$7, %edi
	movl	%esi, %r8d
	rorl	$18, %r8d
	xorl	%r8d, %edi
	shrl	$3, %esi
	xorl	%esi, %edi
	addl	%edi, %edx
	addl	220(%rsp), %edx
	movl	%edx, 284(%rsp)
	movl	(%r10), %r14d
	movl	4(%r10), %edx
	movl	8(%r10), %esi
	movl	12(%r10), %edi
	movl	16(%r10), %r13d
	movl	20(%r10), %r8d
	movl	24(%r10), %r9d
	movl	28(%r10), %ebp
	movq	%r10, 24(%rsp)
	movq	$0, %r10
	jmp 	L_blocks_1_ref$4
L_blocks_1_ref$5:
	movl	%ebp, %r11d
	movl	%r13d, %ebx
	rorl	$6, %ebx
	movl	%r13d, %ebp
	rorl	$11, %ebp
	xorl	%ebp, %ebx
	movl	%r13d, %ebp
	rorl	$25, %ebp
	xorl	%ebp, %ebx
	addl	%ebx, %r11d
	movl	%r13d, %ebx
	andl	%r8d, %ebx
	movl	%r13d, %ebp
	notl	%ebp
	andl	%r9d, %ebp
	xorl	%ebp, %ebx
	addl	%ebx, %r11d
	addl	(%rcx,%r10,4), %r11d
	addl	32(%rsp,%r10,4), %r11d
	movl	%r14d, %ebx
	rorl	$2, %ebx
	movl	%r14d, %ebp
	rorl	$13, %ebp
	xorl	%ebp, %ebx
	movl	%r14d, %ebp
	rorl	$22, %ebp
	xorl	%ebp, %ebx
	movl	%r14d, %ebp
	andl	%edx, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	xorl	%r12d, %ebp
	movl	%edx, %r12d
	andl	%esi, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r9d, %ebp
	movl	%r8d, %r9d
	movl	%r13d, %r8d
	movl	%edi, %r13d
	addl	%r11d, %r13d
	movl	%esi, %edi
	movl	%edx, %esi
	movl	%r14d, %edx
	movl	%r11d, %r14d
	addl	%ebx, %r14d
	incq	%r10
L_blocks_1_ref$4:
	cmpq	$64, %r10
	jb  	L_blocks_1_ref$5
	movq	24(%rsp), %r10
	addl	(%r10), %r14d
	addl	4(%r10), %edx
	addl	8(%r10), %esi
	addl	12(%r10), %edi
	addl	16(%r10), %r13d
	addl	20(%r10), %r8d
	addl	24(%r10), %r9d
	addl	28(%r10), %ebp
	movl	%r14d, (%r10)
	movl	%edx, 4(%r10)
	movl	%esi, 8(%r10)
	movl	%edi, 12(%r10)
	movl	%r13d, 16(%r10)
	movl	%r8d, 20(%r10)
	movl	%r9d, 24(%r10)
	movl	%ebp, 28(%r10)
	movq	16(%rsp), %rsi
	movq	8(%rsp), %rdx
	incq	%rdx
L_blocks_1_ref$2:
	cmpq	%r15, %rdx
	jb  	L_blocks_1_ref$3
	ret
L_zero_address$1:
	movq	$0, (%r9)
	movq	$0, 8(%r9)
	movq	$0, 16(%r9)
	movq	$0, 24(%r9)
	ret
Lcopy_nbytes$1:
	movq	(%rdx), %rsi
	movq	%rsi, (%rcx)
	movq	8(%rdx), %rsi
	movq	%rsi, 8(%rcx)
	movq	16(%rdx), %rsi
	movq	%rsi, 16(%rcx)
	movq	24(%rdx), %rdx
	movq	%rdx, 24(%rcx)
	ret
Lmemcpy_u8pu8_plen___memcpy_u8pu8$1:
	movq	(%r9), %r11
	movq	%r11, (%r10,%rbx)
	addq	$8, %rbx
	movq	8(%r9), %r11
	movq	%r11, (%r10,%rbx)
	addq	$8, %rbx
	movq	16(%r9), %r11
	movq	%r11, (%r10,%rbx)
	addq	$8, %rbx
	movq	24(%r9), %r9
	movq	%r9, (%r10,%rbx)
	ret
Lmemcpy_u8u8_2N___memcpy_u8u8$1:
	movq	$0, %rsi
	jmp 	Lmemcpy_u8u8_2N___memcpy_u8u8$2
Lmemcpy_u8u8_2N___memcpy_u8u8$3:
	movb	(%rdx,%rsi), %dil
	movb	%dil, (%rcx,%rsi)
	incq	%rsi
Lmemcpy_u8u8_2N___memcpy_u8u8$2:
	cmpq	$64, %rsi
	jb  	Lmemcpy_u8u8_2N___memcpy_u8u8$3
	ret
Lmemcpy_u8u8_N___memcpy_u8u8$1:
	movq	$0, %rcx
	jmp 	Lmemcpy_u8u8_N___memcpy_u8u8$2
Lmemcpy_u8u8_N___memcpy_u8u8$3:
	movb	(%rsi,%rcx), %r8b
	movb	%r8b, (%rdi,%rcx)
	incq	%rcx
Lmemcpy_u8u8_N___memcpy_u8u8$2:
	cmpq	$32, %rcx
	jb  	Lmemcpy_u8u8_N___memcpy_u8u8$3
	ret
Lmemcpy_u8pu8_n___memcpy_u8pu8$1:
	movq	(%rcx), %rsi
	movq	%rsi, (%r9,%rdi)
	addq	$8, %rdi
	movq	8(%rcx), %rsi
	movq	%rsi, (%r9,%rdi)
	addq	$8, %rdi
	movq	16(%rcx), %rsi
	movq	%rsi, (%r9,%rdi)
	addq	$8, %rdi
	movq	24(%rcx), %rcx
	movq	%rcx, (%r9,%rdi)
	ret
L_memcpy_u8pu8p$1:
	movq	$0, %rbx
	jmp 	L_memcpy_u8pu8p$2
L_memcpy_u8pu8p$3:
	movb	(%r9,%r12), %bpl
	movb	%bpl, (%rcx,%r10)
	incq	%rbx
	incq	%r12
	incq	%r10
L_memcpy_u8pu8p$2:
	cmpq	%r11, %rbx
	jb  	L_memcpy_u8pu8p$3
	ret
L_memcpy_u8u8p$1:
	movq	(%r8), %r9
	movq	%r9, (%rcx)
	movq	8(%r8), %r9
	movq	%r9, 8(%rcx)
	movq	16(%r8), %r9
	movq	%r9, 16(%rcx)
	movq	24(%r8), %r8
	movq	%r8, 24(%rcx)
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
