	.att_syntax
	.text
	.p2align	5
	.globl	_treesig_jazz
	.globl	treesig_jazz
	.globl	_build_auth_path_jazz
	.globl	build_auth_path_jazz
	.globl	_treehash_jazz
	.globl	treehash_jazz
	.globl	_treehash_cond_jazz
	.globl	treehash_cond_jazz
_treesig_jazz:
treesig_jazz:
	movq	%rsp, %rax
	leaq	-2872(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 2816(%rsp)
	movq	%rbp, 2824(%rsp)
	movq	%r12, 2832(%rsp)
	movq	%r13, 2840(%rsp)
	movq	%r14, 2848(%rsp)
	movq	%r15, 2856(%rsp)
	movq	%rax, 2864(%rsp)
	leaq	99(%rcx), %rax
	leaq	3(%rcx), %rcx
	movl	$0, 16(%rsi)
	movq	%rdi, (%rsp)
	movq	%rsi, 8(%rsp)
	movl	%r8d, 2536(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	72(%rsp), %rdx
	movl	%r8d, 2540(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	%rax, 56(%rsp)
	movq	%rsi, 64(%rsp)
	movl	2540(%rsp), %eax
	shrl	$0, %eax
	xorl	$1, %eax
	shll	$0, %eax
	movq	40(%rsp), %rcx
	movq	%rcx, %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$0, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$79:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$1, %eax
	xorl	$1, %eax
	shll	$1, %eax
	movq	40(%rsp), %rcx
	leaq	32(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$1, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$78:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$2, %eax
	xorl	$1, %eax
	shll	$2, %eax
	movq	40(%rsp), %rcx
	leaq	64(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$2, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$77:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$3, %eax
	xorl	$1, %eax
	shll	$3, %eax
	movq	40(%rsp), %rcx
	leaq	96(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$3, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$76:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$4, %eax
	xorl	$1, %eax
	shll	$4, %eax
	movq	40(%rsp), %rcx
	leaq	128(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$4, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$75:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$5, %eax
	xorl	$1, %eax
	shll	$5, %eax
	movq	40(%rsp), %rcx
	leaq	160(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$5, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$74:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$6, %eax
	xorl	$1, %eax
	shll	$6, %eax
	movq	40(%rsp), %rcx
	leaq	192(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$6, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$73:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$7, %eax
	xorl	$1, %eax
	shll	$7, %eax
	movq	40(%rsp), %rcx
	leaq	224(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$7, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$72:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$8, %eax
	xorl	$1, %eax
	shll	$8, %eax
	movq	40(%rsp), %rcx
	leaq	256(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$8, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$71:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rax
	movq	%rax, 40(%rsp)
	movl	2540(%rsp), %eax
	shrl	$9, %eax
	xorl	$1, %eax
	shll	$9, %eax
	movq	40(%rsp), %rcx
	leaq	288(%rcx), %rdi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movl	$9, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreesig_jazz$70:
	leaq	640(%rsp), %rsp
	movq	8(%rsp), %rax
	movl	2536(%rsp), %ecx
	movl	$0, %edx
	movl	%edx, 12(%rax)
	movl	%ecx, 16(%rax)
	movq	16(%rsp), %rcx
	movq	24(%rsp), %rdx
	movq	32(%rsp), %rsi
	leaq	392(%rsp), %rdi
	movq	%rdx, 32(%rsp)
	leaq	2544(%rsp), %r8
	movq	%rcx, %r9
	leaq	-8(%rsp), %rsp
	call	L_chain_lengths$1
Ltreesig_jazz$69:
	leaq	8(%rsp), %rsp
	movq	%rdi, %r8
	movq	%rsi, %r9
	movq	%rdx, %rcx
	movq	%rax, %rsi
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
Ltreesig_jazz$68:
	leaq	88(%rsp), %rsp
	movq	%rax, %r13
	movq	%rcx, %rsi
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	movq	%r13, %rdi
	movl	$0, %eax
	movl	2544(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$67:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$1, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	32(%r13), %rdi
	movl	$0, %eax
	movl	2548(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$66:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$2, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	64(%r13), %rdi
	movl	$0, %eax
	movl	2552(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$65:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$3, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	96(%r13), %rdi
	movl	$0, %eax
	movl	2556(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$64:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$4, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	128(%r13), %rdi
	movl	$0, %eax
	movl	2560(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$63:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$5, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	160(%r13), %rdi
	movl	$0, %eax
	movl	2564(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$62:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$6, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	192(%r13), %rdi
	movl	$0, %eax
	movl	2568(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$61:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$7, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	224(%r13), %rdi
	movl	$0, %eax
	movl	2572(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$60:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$8, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	256(%r13), %rdi
	movl	$0, %eax
	movl	2576(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$59:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$9, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	288(%r13), %rdi
	movl	$0, %eax
	movl	2580(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$58:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$10, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	320(%r13), %rdi
	movl	$0, %eax
	movl	2584(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$57:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$11, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	352(%r13), %rdi
	movl	$0, %eax
	movl	2588(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$56:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$12, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	384(%r13), %rdi
	movl	$0, %eax
	movl	2592(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$55:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$13, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	416(%r13), %rdi
	movl	$0, %eax
	movl	2596(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$54:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$14, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	448(%r13), %rdi
	movl	$0, %eax
	movl	2600(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$53:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$15, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	480(%r13), %rdi
	movl	$0, %eax
	movl	2604(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$52:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$16, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	512(%r13), %rdi
	movl	$0, %eax
	movl	2608(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$51:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$17, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	544(%r13), %rdi
	movl	$0, %eax
	movl	2612(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$50:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$18, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	576(%r13), %rdi
	movl	$0, %eax
	movl	2616(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$49:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$19, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	608(%r13), %rdi
	movl	$0, %eax
	movl	2620(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$48:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$20, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	640(%r13), %rdi
	movl	$0, %eax
	movl	2624(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$47:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$21, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	672(%r13), %rdi
	movl	$0, %eax
	movl	2628(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$46:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$22, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	704(%r13), %rdi
	movl	$0, %eax
	movl	2632(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$45:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$23, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	736(%r13), %rdi
	movl	$0, %eax
	movl	2636(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$44:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$24, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	768(%r13), %rdi
	movl	$0, %eax
	movl	2640(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$43:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$25, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	800(%r13), %rdi
	movl	$0, %eax
	movl	2644(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$42:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$26, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	832(%r13), %rdi
	movl	$0, %eax
	movl	2648(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$41:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$27, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	864(%r13), %rdi
	movl	$0, %eax
	movl	2652(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$40:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$28, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	896(%r13), %rdi
	movl	$0, %eax
	movl	2656(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$39:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$29, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	928(%r13), %rdi
	movl	$0, %eax
	movl	2660(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$38:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$30, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	960(%r13), %rdi
	movl	$0, %eax
	movl	2664(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$37:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$31, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	992(%r13), %rdi
	movl	$0, %eax
	movl	2668(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$36:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$32, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1024(%r13), %rdi
	movl	$0, %eax
	movl	2672(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$35:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$33, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1056(%r13), %rdi
	movl	$0, %eax
	movl	2676(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$34:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$34, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1088(%r13), %rdi
	movl	$0, %eax
	movl	2680(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$33:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$35, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1120(%r13), %rdi
	movl	$0, %eax
	movl	2684(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$32:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$36, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1152(%r13), %rdi
	movl	$0, %eax
	movl	2688(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$31:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$37, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1184(%r13), %rdi
	movl	$0, %eax
	movl	2692(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$30:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$38, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1216(%r13), %rdi
	movl	$0, %eax
	movl	2696(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$29:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$39, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1248(%r13), %rdi
	movl	$0, %eax
	movl	2700(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$28:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$40, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1280(%r13), %rdi
	movl	$0, %eax
	movl	2704(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$27:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$41, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1312(%r13), %rdi
	movl	$0, %eax
	movl	2708(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$26:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$42, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1344(%r13), %rdi
	movl	$0, %eax
	movl	2712(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$25:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$43, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1376(%r13), %rdi
	movl	$0, %eax
	movl	2716(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$24:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$44, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1408(%r13), %rdi
	movl	$0, %eax
	movl	2720(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$23:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$45, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1440(%r13), %rdi
	movl	$0, %eax
	movl	2724(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$22:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$46, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1472(%r13), %rdi
	movl	$0, %eax
	movl	2728(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$21:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$47, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1504(%r13), %rdi
	movl	$0, %eax
	movl	2732(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$20:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$48, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1536(%r13), %rdi
	movl	$0, %eax
	movl	2736(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$19:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$49, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1568(%r13), %rdi
	movl	$0, %eax
	movl	2740(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$18:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$50, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1600(%r13), %rdi
	movl	$0, %eax
	movl	2744(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$17:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$51, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1632(%r13), %rdi
	movl	$0, %eax
	movl	2748(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$16:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$52, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1664(%r13), %rdi
	movl	$0, %eax
	movl	2752(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$15:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$53, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1696(%r13), %rdi
	movl	$0, %eax
	movl	2756(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$14:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$54, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1728(%r13), %rdi
	movl	$0, %eax
	movl	2760(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$13:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$55, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1760(%r13), %rdi
	movl	$0, %eax
	movl	2764(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$12:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$56, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1792(%r13), %rdi
	movl	$0, %eax
	movl	2768(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$11:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$57, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1824(%r13), %rdi
	movl	$0, %eax
	movl	2772(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$10:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$58, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1856(%r13), %rdi
	movl	$0, %eax
	movl	2776(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$9:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$59, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1888(%r13), %rdi
	movl	$0, %eax
	movl	2780(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$8:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$60, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1920(%r13), %rdi
	movl	$0, %eax
	movl	2784(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$7:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$61, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1952(%r13), %rdi
	movl	$0, %eax
	movl	2788(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$6:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$62, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	1984(%r13), %rdi
	movl	$0, %eax
	movl	2792(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$5:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$63, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	2016(%r13), %rdi
	movl	$0, %eax
	movl	2796(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$4:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$64, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	2048(%r13), %rdi
	movl	$0, %eax
	movl	2800(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$3:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$65, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	2080(%r13), %rdi
	movl	$0, %eax
	movl	2804(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$2:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$66, %eax
	movl	%eax, 20(%rsi)
	movq	32(%rsp), %rdx
	leaq	2112(%r13), %rdi
	movl	$0, %eax
	movl	2808(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Ltreesig_jazz$1:
	leaq	32(%rsp), %rsp
	movq	(%rsp), %rax
	movb	392(%rsp), %cl
	movb	%cl, (%rax)
	movb	393(%rsp), %cl
	movb	%cl, 1(%rax)
	movb	394(%rsp), %cl
	movb	%cl, 2(%rax)
	movb	395(%rsp), %cl
	movb	%cl, 3(%rax)
	movb	396(%rsp), %cl
	movb	%cl, 4(%rax)
	movb	397(%rsp), %cl
	movb	%cl, 5(%rax)
	movb	398(%rsp), %cl
	movb	%cl, 6(%rax)
	movb	399(%rsp), %cl
	movb	%cl, 7(%rax)
	movb	400(%rsp), %cl
	movb	%cl, 8(%rax)
	movb	401(%rsp), %cl
	movb	%cl, 9(%rax)
	movb	402(%rsp), %cl
	movb	%cl, 10(%rax)
	movb	403(%rsp), %cl
	movb	%cl, 11(%rax)
	movb	404(%rsp), %cl
	movb	%cl, 12(%rax)
	movb	405(%rsp), %cl
	movb	%cl, 13(%rax)
	movb	406(%rsp), %cl
	movb	%cl, 14(%rax)
	movb	407(%rsp), %cl
	movb	%cl, 15(%rax)
	movb	408(%rsp), %cl
	movb	%cl, 16(%rax)
	movb	409(%rsp), %cl
	movb	%cl, 17(%rax)
	movb	410(%rsp), %cl
	movb	%cl, 18(%rax)
	movb	411(%rsp), %cl
	movb	%cl, 19(%rax)
	movb	412(%rsp), %cl
	movb	%cl, 20(%rax)
	movb	413(%rsp), %cl
	movb	%cl, 21(%rax)
	movb	414(%rsp), %cl
	movb	%cl, 22(%rax)
	movb	415(%rsp), %cl
	movb	%cl, 23(%rax)
	movb	416(%rsp), %cl
	movb	%cl, 24(%rax)
	movb	417(%rsp), %cl
	movb	%cl, 25(%rax)
	movb	418(%rsp), %cl
	movb	%cl, 26(%rax)
	movb	419(%rsp), %cl
	movb	%cl, 27(%rax)
	movb	420(%rsp), %cl
	movb	%cl, 28(%rax)
	movb	421(%rsp), %cl
	movb	%cl, 29(%rax)
	movb	422(%rsp), %cl
	movb	%cl, 30(%rax)
	movb	423(%rsp), %cl
	movb	%cl, 31(%rax)
	movb	424(%rsp), %cl
	movb	%cl, 32(%rax)
	movb	425(%rsp), %cl
	movb	%cl, 33(%rax)
	movb	426(%rsp), %cl
	movb	%cl, 34(%rax)
	movb	427(%rsp), %cl
	movb	%cl, 35(%rax)
	movb	428(%rsp), %cl
	movb	%cl, 36(%rax)
	movb	429(%rsp), %cl
	movb	%cl, 37(%rax)
	movb	430(%rsp), %cl
	movb	%cl, 38(%rax)
	movb	431(%rsp), %cl
	movb	%cl, 39(%rax)
	movb	432(%rsp), %cl
	movb	%cl, 40(%rax)
	movb	433(%rsp), %cl
	movb	%cl, 41(%rax)
	movb	434(%rsp), %cl
	movb	%cl, 42(%rax)
	movb	435(%rsp), %cl
	movb	%cl, 43(%rax)
	movb	436(%rsp), %cl
	movb	%cl, 44(%rax)
	movb	437(%rsp), %cl
	movb	%cl, 45(%rax)
	movb	438(%rsp), %cl
	movb	%cl, 46(%rax)
	movb	439(%rsp), %cl
	movb	%cl, 47(%rax)
	movb	440(%rsp), %cl
	movb	%cl, 48(%rax)
	movb	441(%rsp), %cl
	movb	%cl, 49(%rax)
	movb	442(%rsp), %cl
	movb	%cl, 50(%rax)
	movb	443(%rsp), %cl
	movb	%cl, 51(%rax)
	movb	444(%rsp), %cl
	movb	%cl, 52(%rax)
	movb	445(%rsp), %cl
	movb	%cl, 53(%rax)
	movb	446(%rsp), %cl
	movb	%cl, 54(%rax)
	movb	447(%rsp), %cl
	movb	%cl, 55(%rax)
	movb	448(%rsp), %cl
	movb	%cl, 56(%rax)
	movb	449(%rsp), %cl
	movb	%cl, 57(%rax)
	movb	450(%rsp), %cl
	movb	%cl, 58(%rax)
	movb	451(%rsp), %cl
	movb	%cl, 59(%rax)
	movb	452(%rsp), %cl
	movb	%cl, 60(%rax)
	movb	453(%rsp), %cl
	movb	%cl, 61(%rax)
	movb	454(%rsp), %cl
	movb	%cl, 62(%rax)
	movb	455(%rsp), %cl
	movb	%cl, 63(%rax)
	movb	456(%rsp), %cl
	movb	%cl, 64(%rax)
	movb	457(%rsp), %cl
	movb	%cl, 65(%rax)
	movb	458(%rsp), %cl
	movb	%cl, 66(%rax)
	movb	459(%rsp), %cl
	movb	%cl, 67(%rax)
	movb	460(%rsp), %cl
	movb	%cl, 68(%rax)
	movb	461(%rsp), %cl
	movb	%cl, 69(%rax)
	movb	462(%rsp), %cl
	movb	%cl, 70(%rax)
	movb	463(%rsp), %cl
	movb	%cl, 71(%rax)
	movb	464(%rsp), %cl
	movb	%cl, 72(%rax)
	movb	465(%rsp), %cl
	movb	%cl, 73(%rax)
	movb	466(%rsp), %cl
	movb	%cl, 74(%rax)
	movb	467(%rsp), %cl
	movb	%cl, 75(%rax)
	movb	468(%rsp), %cl
	movb	%cl, 76(%rax)
	movb	469(%rsp), %cl
	movb	%cl, 77(%rax)
	movb	470(%rsp), %cl
	movb	%cl, 78(%rax)
	movb	471(%rsp), %cl
	movb	%cl, 79(%rax)
	movb	472(%rsp), %cl
	movb	%cl, 80(%rax)
	movb	473(%rsp), %cl
	movb	%cl, 81(%rax)
	movb	474(%rsp), %cl
	movb	%cl, 82(%rax)
	movb	475(%rsp), %cl
	movb	%cl, 83(%rax)
	movb	476(%rsp), %cl
	movb	%cl, 84(%rax)
	movb	477(%rsp), %cl
	movb	%cl, 85(%rax)
	movb	478(%rsp), %cl
	movb	%cl, 86(%rax)
	movb	479(%rsp), %cl
	movb	%cl, 87(%rax)
	movb	480(%rsp), %cl
	movb	%cl, 88(%rax)
	movb	481(%rsp), %cl
	movb	%cl, 89(%rax)
	movb	482(%rsp), %cl
	movb	%cl, 90(%rax)
	movb	483(%rsp), %cl
	movb	%cl, 91(%rax)
	movb	484(%rsp), %cl
	movb	%cl, 92(%rax)
	movb	485(%rsp), %cl
	movb	%cl, 93(%rax)
	movb	486(%rsp), %cl
	movb	%cl, 94(%rax)
	movb	487(%rsp), %cl
	movb	%cl, 95(%rax)
	movb	488(%rsp), %cl
	movb	%cl, 96(%rax)
	movb	489(%rsp), %cl
	movb	%cl, 97(%rax)
	movb	490(%rsp), %cl
	movb	%cl, 98(%rax)
	movb	491(%rsp), %cl
	movb	%cl, 99(%rax)
	movb	492(%rsp), %cl
	movb	%cl, 100(%rax)
	movb	493(%rsp), %cl
	movb	%cl, 101(%rax)
	movb	494(%rsp), %cl
	movb	%cl, 102(%rax)
	movb	495(%rsp), %cl
	movb	%cl, 103(%rax)
	movb	496(%rsp), %cl
	movb	%cl, 104(%rax)
	movb	497(%rsp), %cl
	movb	%cl, 105(%rax)
	movb	498(%rsp), %cl
	movb	%cl, 106(%rax)
	movb	499(%rsp), %cl
	movb	%cl, 107(%rax)
	movb	500(%rsp), %cl
	movb	%cl, 108(%rax)
	movb	501(%rsp), %cl
	movb	%cl, 109(%rax)
	movb	502(%rsp), %cl
	movb	%cl, 110(%rax)
	movb	503(%rsp), %cl
	movb	%cl, 111(%rax)
	movb	504(%rsp), %cl
	movb	%cl, 112(%rax)
	movb	505(%rsp), %cl
	movb	%cl, 113(%rax)
	movb	506(%rsp), %cl
	movb	%cl, 114(%rax)
	movb	507(%rsp), %cl
	movb	%cl, 115(%rax)
	movb	508(%rsp), %cl
	movb	%cl, 116(%rax)
	movb	509(%rsp), %cl
	movb	%cl, 117(%rax)
	movb	510(%rsp), %cl
	movb	%cl, 118(%rax)
	movb	511(%rsp), %cl
	movb	%cl, 119(%rax)
	movb	512(%rsp), %cl
	movb	%cl, 120(%rax)
	movb	513(%rsp), %cl
	movb	%cl, 121(%rax)
	movb	514(%rsp), %cl
	movb	%cl, 122(%rax)
	movb	515(%rsp), %cl
	movb	%cl, 123(%rax)
	movb	516(%rsp), %cl
	movb	%cl, 124(%rax)
	movb	517(%rsp), %cl
	movb	%cl, 125(%rax)
	movb	518(%rsp), %cl
	movb	%cl, 126(%rax)
	movb	519(%rsp), %cl
	movb	%cl, 127(%rax)
	movb	520(%rsp), %cl
	movb	%cl, 128(%rax)
	movb	521(%rsp), %cl
	movb	%cl, 129(%rax)
	movb	522(%rsp), %cl
	movb	%cl, 130(%rax)
	movb	523(%rsp), %cl
	movb	%cl, 131(%rax)
	movb	524(%rsp), %cl
	movb	%cl, 132(%rax)
	movb	525(%rsp), %cl
	movb	%cl, 133(%rax)
	movb	526(%rsp), %cl
	movb	%cl, 134(%rax)
	movb	527(%rsp), %cl
	movb	%cl, 135(%rax)
	movb	528(%rsp), %cl
	movb	%cl, 136(%rax)
	movb	529(%rsp), %cl
	movb	%cl, 137(%rax)
	movb	530(%rsp), %cl
	movb	%cl, 138(%rax)
	movb	531(%rsp), %cl
	movb	%cl, 139(%rax)
	movb	532(%rsp), %cl
	movb	%cl, 140(%rax)
	movb	533(%rsp), %cl
	movb	%cl, 141(%rax)
	movb	534(%rsp), %cl
	movb	%cl, 142(%rax)
	movb	535(%rsp), %cl
	movb	%cl, 143(%rax)
	movb	536(%rsp), %cl
	movb	%cl, 144(%rax)
	movb	537(%rsp), %cl
	movb	%cl, 145(%rax)
	movb	538(%rsp), %cl
	movb	%cl, 146(%rax)
	movb	539(%rsp), %cl
	movb	%cl, 147(%rax)
	movb	540(%rsp), %cl
	movb	%cl, 148(%rax)
	movb	541(%rsp), %cl
	movb	%cl, 149(%rax)
	movb	542(%rsp), %cl
	movb	%cl, 150(%rax)
	movb	543(%rsp), %cl
	movb	%cl, 151(%rax)
	movb	544(%rsp), %cl
	movb	%cl, 152(%rax)
	movb	545(%rsp), %cl
	movb	%cl, 153(%rax)
	movb	546(%rsp), %cl
	movb	%cl, 154(%rax)
	movb	547(%rsp), %cl
	movb	%cl, 155(%rax)
	movb	548(%rsp), %cl
	movb	%cl, 156(%rax)
	movb	549(%rsp), %cl
	movb	%cl, 157(%rax)
	movb	550(%rsp), %cl
	movb	%cl, 158(%rax)
	movb	551(%rsp), %cl
	movb	%cl, 159(%rax)
	movb	552(%rsp), %cl
	movb	%cl, 160(%rax)
	movb	553(%rsp), %cl
	movb	%cl, 161(%rax)
	movb	554(%rsp), %cl
	movb	%cl, 162(%rax)
	movb	555(%rsp), %cl
	movb	%cl, 163(%rax)
	movb	556(%rsp), %cl
	movb	%cl, 164(%rax)
	movb	557(%rsp), %cl
	movb	%cl, 165(%rax)
	movb	558(%rsp), %cl
	movb	%cl, 166(%rax)
	movb	559(%rsp), %cl
	movb	%cl, 167(%rax)
	movb	560(%rsp), %cl
	movb	%cl, 168(%rax)
	movb	561(%rsp), %cl
	movb	%cl, 169(%rax)
	movb	562(%rsp), %cl
	movb	%cl, 170(%rax)
	movb	563(%rsp), %cl
	movb	%cl, 171(%rax)
	movb	564(%rsp), %cl
	movb	%cl, 172(%rax)
	movb	565(%rsp), %cl
	movb	%cl, 173(%rax)
	movb	566(%rsp), %cl
	movb	%cl, 174(%rax)
	movb	567(%rsp), %cl
	movb	%cl, 175(%rax)
	movb	568(%rsp), %cl
	movb	%cl, 176(%rax)
	movb	569(%rsp), %cl
	movb	%cl, 177(%rax)
	movb	570(%rsp), %cl
	movb	%cl, 178(%rax)
	movb	571(%rsp), %cl
	movb	%cl, 179(%rax)
	movb	572(%rsp), %cl
	movb	%cl, 180(%rax)
	movb	573(%rsp), %cl
	movb	%cl, 181(%rax)
	movb	574(%rsp), %cl
	movb	%cl, 182(%rax)
	movb	575(%rsp), %cl
	movb	%cl, 183(%rax)
	movb	576(%rsp), %cl
	movb	%cl, 184(%rax)
	movb	577(%rsp), %cl
	movb	%cl, 185(%rax)
	movb	578(%rsp), %cl
	movb	%cl, 186(%rax)
	movb	579(%rsp), %cl
	movb	%cl, 187(%rax)
	movb	580(%rsp), %cl
	movb	%cl, 188(%rax)
	movb	581(%rsp), %cl
	movb	%cl, 189(%rax)
	movb	582(%rsp), %cl
	movb	%cl, 190(%rax)
	movb	583(%rsp), %cl
	movb	%cl, 191(%rax)
	movb	584(%rsp), %cl
	movb	%cl, 192(%rax)
	movb	585(%rsp), %cl
	movb	%cl, 193(%rax)
	movb	586(%rsp), %cl
	movb	%cl, 194(%rax)
	movb	587(%rsp), %cl
	movb	%cl, 195(%rax)
	movb	588(%rsp), %cl
	movb	%cl, 196(%rax)
	movb	589(%rsp), %cl
	movb	%cl, 197(%rax)
	movb	590(%rsp), %cl
	movb	%cl, 198(%rax)
	movb	591(%rsp), %cl
	movb	%cl, 199(%rax)
	movb	592(%rsp), %cl
	movb	%cl, 200(%rax)
	movb	593(%rsp), %cl
	movb	%cl, 201(%rax)
	movb	594(%rsp), %cl
	movb	%cl, 202(%rax)
	movb	595(%rsp), %cl
	movb	%cl, 203(%rax)
	movb	596(%rsp), %cl
	movb	%cl, 204(%rax)
	movb	597(%rsp), %cl
	movb	%cl, 205(%rax)
	movb	598(%rsp), %cl
	movb	%cl, 206(%rax)
	movb	599(%rsp), %cl
	movb	%cl, 207(%rax)
	movb	600(%rsp), %cl
	movb	%cl, 208(%rax)
	movb	601(%rsp), %cl
	movb	%cl, 209(%rax)
	movb	602(%rsp), %cl
	movb	%cl, 210(%rax)
	movb	603(%rsp), %cl
	movb	%cl, 211(%rax)
	movb	604(%rsp), %cl
	movb	%cl, 212(%rax)
	movb	605(%rsp), %cl
	movb	%cl, 213(%rax)
	movb	606(%rsp), %cl
	movb	%cl, 214(%rax)
	movb	607(%rsp), %cl
	movb	%cl, 215(%rax)
	movb	608(%rsp), %cl
	movb	%cl, 216(%rax)
	movb	609(%rsp), %cl
	movb	%cl, 217(%rax)
	movb	610(%rsp), %cl
	movb	%cl, 218(%rax)
	movb	611(%rsp), %cl
	movb	%cl, 219(%rax)
	movb	612(%rsp), %cl
	movb	%cl, 220(%rax)
	movb	613(%rsp), %cl
	movb	%cl, 221(%rax)
	movb	614(%rsp), %cl
	movb	%cl, 222(%rax)
	movb	615(%rsp), %cl
	movb	%cl, 223(%rax)
	movb	616(%rsp), %cl
	movb	%cl, 224(%rax)
	movb	617(%rsp), %cl
	movb	%cl, 225(%rax)
	movb	618(%rsp), %cl
	movb	%cl, 226(%rax)
	movb	619(%rsp), %cl
	movb	%cl, 227(%rax)
	movb	620(%rsp), %cl
	movb	%cl, 228(%rax)
	movb	621(%rsp), %cl
	movb	%cl, 229(%rax)
	movb	622(%rsp), %cl
	movb	%cl, 230(%rax)
	movb	623(%rsp), %cl
	movb	%cl, 231(%rax)
	movb	624(%rsp), %cl
	movb	%cl, 232(%rax)
	movb	625(%rsp), %cl
	movb	%cl, 233(%rax)
	movb	626(%rsp), %cl
	movb	%cl, 234(%rax)
	movb	627(%rsp), %cl
	movb	%cl, 235(%rax)
	movb	628(%rsp), %cl
	movb	%cl, 236(%rax)
	movb	629(%rsp), %cl
	movb	%cl, 237(%rax)
	movb	630(%rsp), %cl
	movb	%cl, 238(%rax)
	movb	631(%rsp), %cl
	movb	%cl, 239(%rax)
	movb	632(%rsp), %cl
	movb	%cl, 240(%rax)
	movb	633(%rsp), %cl
	movb	%cl, 241(%rax)
	movb	634(%rsp), %cl
	movb	%cl, 242(%rax)
	movb	635(%rsp), %cl
	movb	%cl, 243(%rax)
	movb	636(%rsp), %cl
	movb	%cl, 244(%rax)
	movb	637(%rsp), %cl
	movb	%cl, 245(%rax)
	movb	638(%rsp), %cl
	movb	%cl, 246(%rax)
	movb	639(%rsp), %cl
	movb	%cl, 247(%rax)
	movb	640(%rsp), %cl
	movb	%cl, 248(%rax)
	movb	641(%rsp), %cl
	movb	%cl, 249(%rax)
	movb	642(%rsp), %cl
	movb	%cl, 250(%rax)
	movb	643(%rsp), %cl
	movb	%cl, 251(%rax)
	movb	644(%rsp), %cl
	movb	%cl, 252(%rax)
	movb	645(%rsp), %cl
	movb	%cl, 253(%rax)
	movb	646(%rsp), %cl
	movb	%cl, 254(%rax)
	movb	647(%rsp), %cl
	movb	%cl, 255(%rax)
	movb	648(%rsp), %cl
	movb	%cl, 256(%rax)
	movb	649(%rsp), %cl
	movb	%cl, 257(%rax)
	movb	650(%rsp), %cl
	movb	%cl, 258(%rax)
	movb	651(%rsp), %cl
	movb	%cl, 259(%rax)
	movb	652(%rsp), %cl
	movb	%cl, 260(%rax)
	movb	653(%rsp), %cl
	movb	%cl, 261(%rax)
	movb	654(%rsp), %cl
	movb	%cl, 262(%rax)
	movb	655(%rsp), %cl
	movb	%cl, 263(%rax)
	movb	656(%rsp), %cl
	movb	%cl, 264(%rax)
	movb	657(%rsp), %cl
	movb	%cl, 265(%rax)
	movb	658(%rsp), %cl
	movb	%cl, 266(%rax)
	movb	659(%rsp), %cl
	movb	%cl, 267(%rax)
	movb	660(%rsp), %cl
	movb	%cl, 268(%rax)
	movb	661(%rsp), %cl
	movb	%cl, 269(%rax)
	movb	662(%rsp), %cl
	movb	%cl, 270(%rax)
	movb	663(%rsp), %cl
	movb	%cl, 271(%rax)
	movb	664(%rsp), %cl
	movb	%cl, 272(%rax)
	movb	665(%rsp), %cl
	movb	%cl, 273(%rax)
	movb	666(%rsp), %cl
	movb	%cl, 274(%rax)
	movb	667(%rsp), %cl
	movb	%cl, 275(%rax)
	movb	668(%rsp), %cl
	movb	%cl, 276(%rax)
	movb	669(%rsp), %cl
	movb	%cl, 277(%rax)
	movb	670(%rsp), %cl
	movb	%cl, 278(%rax)
	movb	671(%rsp), %cl
	movb	%cl, 279(%rax)
	movb	672(%rsp), %cl
	movb	%cl, 280(%rax)
	movb	673(%rsp), %cl
	movb	%cl, 281(%rax)
	movb	674(%rsp), %cl
	movb	%cl, 282(%rax)
	movb	675(%rsp), %cl
	movb	%cl, 283(%rax)
	movb	676(%rsp), %cl
	movb	%cl, 284(%rax)
	movb	677(%rsp), %cl
	movb	%cl, 285(%rax)
	movb	678(%rsp), %cl
	movb	%cl, 286(%rax)
	movb	679(%rsp), %cl
	movb	%cl, 287(%rax)
	movb	680(%rsp), %cl
	movb	%cl, 288(%rax)
	movb	681(%rsp), %cl
	movb	%cl, 289(%rax)
	movb	682(%rsp), %cl
	movb	%cl, 290(%rax)
	movb	683(%rsp), %cl
	movb	%cl, 291(%rax)
	movb	684(%rsp), %cl
	movb	%cl, 292(%rax)
	movb	685(%rsp), %cl
	movb	%cl, 293(%rax)
	movb	686(%rsp), %cl
	movb	%cl, 294(%rax)
	movb	687(%rsp), %cl
	movb	%cl, 295(%rax)
	movb	688(%rsp), %cl
	movb	%cl, 296(%rax)
	movb	689(%rsp), %cl
	movb	%cl, 297(%rax)
	movb	690(%rsp), %cl
	movb	%cl, 298(%rax)
	movb	691(%rsp), %cl
	movb	%cl, 299(%rax)
	movb	692(%rsp), %cl
	movb	%cl, 300(%rax)
	movb	693(%rsp), %cl
	movb	%cl, 301(%rax)
	movb	694(%rsp), %cl
	movb	%cl, 302(%rax)
	movb	695(%rsp), %cl
	movb	%cl, 303(%rax)
	movb	696(%rsp), %cl
	movb	%cl, 304(%rax)
	movb	697(%rsp), %cl
	movb	%cl, 305(%rax)
	movb	698(%rsp), %cl
	movb	%cl, 306(%rax)
	movb	699(%rsp), %cl
	movb	%cl, 307(%rax)
	movb	700(%rsp), %cl
	movb	%cl, 308(%rax)
	movb	701(%rsp), %cl
	movb	%cl, 309(%rax)
	movb	702(%rsp), %cl
	movb	%cl, 310(%rax)
	movb	703(%rsp), %cl
	movb	%cl, 311(%rax)
	movb	704(%rsp), %cl
	movb	%cl, 312(%rax)
	movb	705(%rsp), %cl
	movb	%cl, 313(%rax)
	movb	706(%rsp), %cl
	movb	%cl, 314(%rax)
	movb	707(%rsp), %cl
	movb	%cl, 315(%rax)
	movb	708(%rsp), %cl
	movb	%cl, 316(%rax)
	movb	709(%rsp), %cl
	movb	%cl, 317(%rax)
	movb	710(%rsp), %cl
	movb	%cl, 318(%rax)
	movb	711(%rsp), %cl
	movb	%cl, 319(%rax)
	movb	712(%rsp), %cl
	movb	%cl, 320(%rax)
	movb	713(%rsp), %cl
	movb	%cl, 321(%rax)
	movb	714(%rsp), %cl
	movb	%cl, 322(%rax)
	movb	715(%rsp), %cl
	movb	%cl, 323(%rax)
	movb	716(%rsp), %cl
	movb	%cl, 324(%rax)
	movb	717(%rsp), %cl
	movb	%cl, 325(%rax)
	movb	718(%rsp), %cl
	movb	%cl, 326(%rax)
	movb	719(%rsp), %cl
	movb	%cl, 327(%rax)
	movb	720(%rsp), %cl
	movb	%cl, 328(%rax)
	movb	721(%rsp), %cl
	movb	%cl, 329(%rax)
	movb	722(%rsp), %cl
	movb	%cl, 330(%rax)
	movb	723(%rsp), %cl
	movb	%cl, 331(%rax)
	movb	724(%rsp), %cl
	movb	%cl, 332(%rax)
	movb	725(%rsp), %cl
	movb	%cl, 333(%rax)
	movb	726(%rsp), %cl
	movb	%cl, 334(%rax)
	movb	727(%rsp), %cl
	movb	%cl, 335(%rax)
	movb	728(%rsp), %cl
	movb	%cl, 336(%rax)
	movb	729(%rsp), %cl
	movb	%cl, 337(%rax)
	movb	730(%rsp), %cl
	movb	%cl, 338(%rax)
	movb	731(%rsp), %cl
	movb	%cl, 339(%rax)
	movb	732(%rsp), %cl
	movb	%cl, 340(%rax)
	movb	733(%rsp), %cl
	movb	%cl, 341(%rax)
	movb	734(%rsp), %cl
	movb	%cl, 342(%rax)
	movb	735(%rsp), %cl
	movb	%cl, 343(%rax)
	movb	736(%rsp), %cl
	movb	%cl, 344(%rax)
	movb	737(%rsp), %cl
	movb	%cl, 345(%rax)
	movb	738(%rsp), %cl
	movb	%cl, 346(%rax)
	movb	739(%rsp), %cl
	movb	%cl, 347(%rax)
	movb	740(%rsp), %cl
	movb	%cl, 348(%rax)
	movb	741(%rsp), %cl
	movb	%cl, 349(%rax)
	movb	742(%rsp), %cl
	movb	%cl, 350(%rax)
	movb	743(%rsp), %cl
	movb	%cl, 351(%rax)
	movb	744(%rsp), %cl
	movb	%cl, 352(%rax)
	movb	745(%rsp), %cl
	movb	%cl, 353(%rax)
	movb	746(%rsp), %cl
	movb	%cl, 354(%rax)
	movb	747(%rsp), %cl
	movb	%cl, 355(%rax)
	movb	748(%rsp), %cl
	movb	%cl, 356(%rax)
	movb	749(%rsp), %cl
	movb	%cl, 357(%rax)
	movb	750(%rsp), %cl
	movb	%cl, 358(%rax)
	movb	751(%rsp), %cl
	movb	%cl, 359(%rax)
	movb	752(%rsp), %cl
	movb	%cl, 360(%rax)
	movb	753(%rsp), %cl
	movb	%cl, 361(%rax)
	movb	754(%rsp), %cl
	movb	%cl, 362(%rax)
	movb	755(%rsp), %cl
	movb	%cl, 363(%rax)
	movb	756(%rsp), %cl
	movb	%cl, 364(%rax)
	movb	757(%rsp), %cl
	movb	%cl, 365(%rax)
	movb	758(%rsp), %cl
	movb	%cl, 366(%rax)
	movb	759(%rsp), %cl
	movb	%cl, 367(%rax)
	movb	760(%rsp), %cl
	movb	%cl, 368(%rax)
	movb	761(%rsp), %cl
	movb	%cl, 369(%rax)
	movb	762(%rsp), %cl
	movb	%cl, 370(%rax)
	movb	763(%rsp), %cl
	movb	%cl, 371(%rax)
	movb	764(%rsp), %cl
	movb	%cl, 372(%rax)
	movb	765(%rsp), %cl
	movb	%cl, 373(%rax)
	movb	766(%rsp), %cl
	movb	%cl, 374(%rax)
	movb	767(%rsp), %cl
	movb	%cl, 375(%rax)
	movb	768(%rsp), %cl
	movb	%cl, 376(%rax)
	movb	769(%rsp), %cl
	movb	%cl, 377(%rax)
	movb	770(%rsp), %cl
	movb	%cl, 378(%rax)
	movb	771(%rsp), %cl
	movb	%cl, 379(%rax)
	movb	772(%rsp), %cl
	movb	%cl, 380(%rax)
	movb	773(%rsp), %cl
	movb	%cl, 381(%rax)
	movb	774(%rsp), %cl
	movb	%cl, 382(%rax)
	movb	775(%rsp), %cl
	movb	%cl, 383(%rax)
	movb	776(%rsp), %cl
	movb	%cl, 384(%rax)
	movb	777(%rsp), %cl
	movb	%cl, 385(%rax)
	movb	778(%rsp), %cl
	movb	%cl, 386(%rax)
	movb	779(%rsp), %cl
	movb	%cl, 387(%rax)
	movb	780(%rsp), %cl
	movb	%cl, 388(%rax)
	movb	781(%rsp), %cl
	movb	%cl, 389(%rax)
	movb	782(%rsp), %cl
	movb	%cl, 390(%rax)
	movb	783(%rsp), %cl
	movb	%cl, 391(%rax)
	movb	784(%rsp), %cl
	movb	%cl, 392(%rax)
	movb	785(%rsp), %cl
	movb	%cl, 393(%rax)
	movb	786(%rsp), %cl
	movb	%cl, 394(%rax)
	movb	787(%rsp), %cl
	movb	%cl, 395(%rax)
	movb	788(%rsp), %cl
	movb	%cl, 396(%rax)
	movb	789(%rsp), %cl
	movb	%cl, 397(%rax)
	movb	790(%rsp), %cl
	movb	%cl, 398(%rax)
	movb	791(%rsp), %cl
	movb	%cl, 399(%rax)
	movb	792(%rsp), %cl
	movb	%cl, 400(%rax)
	movb	793(%rsp), %cl
	movb	%cl, 401(%rax)
	movb	794(%rsp), %cl
	movb	%cl, 402(%rax)
	movb	795(%rsp), %cl
	movb	%cl, 403(%rax)
	movb	796(%rsp), %cl
	movb	%cl, 404(%rax)
	movb	797(%rsp), %cl
	movb	%cl, 405(%rax)
	movb	798(%rsp), %cl
	movb	%cl, 406(%rax)
	movb	799(%rsp), %cl
	movb	%cl, 407(%rax)
	movb	800(%rsp), %cl
	movb	%cl, 408(%rax)
	movb	801(%rsp), %cl
	movb	%cl, 409(%rax)
	movb	802(%rsp), %cl
	movb	%cl, 410(%rax)
	movb	803(%rsp), %cl
	movb	%cl, 411(%rax)
	movb	804(%rsp), %cl
	movb	%cl, 412(%rax)
	movb	805(%rsp), %cl
	movb	%cl, 413(%rax)
	movb	806(%rsp), %cl
	movb	%cl, 414(%rax)
	movb	807(%rsp), %cl
	movb	%cl, 415(%rax)
	movb	808(%rsp), %cl
	movb	%cl, 416(%rax)
	movb	809(%rsp), %cl
	movb	%cl, 417(%rax)
	movb	810(%rsp), %cl
	movb	%cl, 418(%rax)
	movb	811(%rsp), %cl
	movb	%cl, 419(%rax)
	movb	812(%rsp), %cl
	movb	%cl, 420(%rax)
	movb	813(%rsp), %cl
	movb	%cl, 421(%rax)
	movb	814(%rsp), %cl
	movb	%cl, 422(%rax)
	movb	815(%rsp), %cl
	movb	%cl, 423(%rax)
	movb	816(%rsp), %cl
	movb	%cl, 424(%rax)
	movb	817(%rsp), %cl
	movb	%cl, 425(%rax)
	movb	818(%rsp), %cl
	movb	%cl, 426(%rax)
	movb	819(%rsp), %cl
	movb	%cl, 427(%rax)
	movb	820(%rsp), %cl
	movb	%cl, 428(%rax)
	movb	821(%rsp), %cl
	movb	%cl, 429(%rax)
	movb	822(%rsp), %cl
	movb	%cl, 430(%rax)
	movb	823(%rsp), %cl
	movb	%cl, 431(%rax)
	movb	824(%rsp), %cl
	movb	%cl, 432(%rax)
	movb	825(%rsp), %cl
	movb	%cl, 433(%rax)
	movb	826(%rsp), %cl
	movb	%cl, 434(%rax)
	movb	827(%rsp), %cl
	movb	%cl, 435(%rax)
	movb	828(%rsp), %cl
	movb	%cl, 436(%rax)
	movb	829(%rsp), %cl
	movb	%cl, 437(%rax)
	movb	830(%rsp), %cl
	movb	%cl, 438(%rax)
	movb	831(%rsp), %cl
	movb	%cl, 439(%rax)
	movb	832(%rsp), %cl
	movb	%cl, 440(%rax)
	movb	833(%rsp), %cl
	movb	%cl, 441(%rax)
	movb	834(%rsp), %cl
	movb	%cl, 442(%rax)
	movb	835(%rsp), %cl
	movb	%cl, 443(%rax)
	movb	836(%rsp), %cl
	movb	%cl, 444(%rax)
	movb	837(%rsp), %cl
	movb	%cl, 445(%rax)
	movb	838(%rsp), %cl
	movb	%cl, 446(%rax)
	movb	839(%rsp), %cl
	movb	%cl, 447(%rax)
	movb	840(%rsp), %cl
	movb	%cl, 448(%rax)
	movb	841(%rsp), %cl
	movb	%cl, 449(%rax)
	movb	842(%rsp), %cl
	movb	%cl, 450(%rax)
	movb	843(%rsp), %cl
	movb	%cl, 451(%rax)
	movb	844(%rsp), %cl
	movb	%cl, 452(%rax)
	movb	845(%rsp), %cl
	movb	%cl, 453(%rax)
	movb	846(%rsp), %cl
	movb	%cl, 454(%rax)
	movb	847(%rsp), %cl
	movb	%cl, 455(%rax)
	movb	848(%rsp), %cl
	movb	%cl, 456(%rax)
	movb	849(%rsp), %cl
	movb	%cl, 457(%rax)
	movb	850(%rsp), %cl
	movb	%cl, 458(%rax)
	movb	851(%rsp), %cl
	movb	%cl, 459(%rax)
	movb	852(%rsp), %cl
	movb	%cl, 460(%rax)
	movb	853(%rsp), %cl
	movb	%cl, 461(%rax)
	movb	854(%rsp), %cl
	movb	%cl, 462(%rax)
	movb	855(%rsp), %cl
	movb	%cl, 463(%rax)
	movb	856(%rsp), %cl
	movb	%cl, 464(%rax)
	movb	857(%rsp), %cl
	movb	%cl, 465(%rax)
	movb	858(%rsp), %cl
	movb	%cl, 466(%rax)
	movb	859(%rsp), %cl
	movb	%cl, 467(%rax)
	movb	860(%rsp), %cl
	movb	%cl, 468(%rax)
	movb	861(%rsp), %cl
	movb	%cl, 469(%rax)
	movb	862(%rsp), %cl
	movb	%cl, 470(%rax)
	movb	863(%rsp), %cl
	movb	%cl, 471(%rax)
	movb	864(%rsp), %cl
	movb	%cl, 472(%rax)
	movb	865(%rsp), %cl
	movb	%cl, 473(%rax)
	movb	866(%rsp), %cl
	movb	%cl, 474(%rax)
	movb	867(%rsp), %cl
	movb	%cl, 475(%rax)
	movb	868(%rsp), %cl
	movb	%cl, 476(%rax)
	movb	869(%rsp), %cl
	movb	%cl, 477(%rax)
	movb	870(%rsp), %cl
	movb	%cl, 478(%rax)
	movb	871(%rsp), %cl
	movb	%cl, 479(%rax)
	movb	872(%rsp), %cl
	movb	%cl, 480(%rax)
	movb	873(%rsp), %cl
	movb	%cl, 481(%rax)
	movb	874(%rsp), %cl
	movb	%cl, 482(%rax)
	movb	875(%rsp), %cl
	movb	%cl, 483(%rax)
	movb	876(%rsp), %cl
	movb	%cl, 484(%rax)
	movb	877(%rsp), %cl
	movb	%cl, 485(%rax)
	movb	878(%rsp), %cl
	movb	%cl, 486(%rax)
	movb	879(%rsp), %cl
	movb	%cl, 487(%rax)
	movb	880(%rsp), %cl
	movb	%cl, 488(%rax)
	movb	881(%rsp), %cl
	movb	%cl, 489(%rax)
	movb	882(%rsp), %cl
	movb	%cl, 490(%rax)
	movb	883(%rsp), %cl
	movb	%cl, 491(%rax)
	movb	884(%rsp), %cl
	movb	%cl, 492(%rax)
	movb	885(%rsp), %cl
	movb	%cl, 493(%rax)
	movb	886(%rsp), %cl
	movb	%cl, 494(%rax)
	movb	887(%rsp), %cl
	movb	%cl, 495(%rax)
	movb	888(%rsp), %cl
	movb	%cl, 496(%rax)
	movb	889(%rsp), %cl
	movb	%cl, 497(%rax)
	movb	890(%rsp), %cl
	movb	%cl, 498(%rax)
	movb	891(%rsp), %cl
	movb	%cl, 499(%rax)
	movb	892(%rsp), %cl
	movb	%cl, 500(%rax)
	movb	893(%rsp), %cl
	movb	%cl, 501(%rax)
	movb	894(%rsp), %cl
	movb	%cl, 502(%rax)
	movb	895(%rsp), %cl
	movb	%cl, 503(%rax)
	movb	896(%rsp), %cl
	movb	%cl, 504(%rax)
	movb	897(%rsp), %cl
	movb	%cl, 505(%rax)
	movb	898(%rsp), %cl
	movb	%cl, 506(%rax)
	movb	899(%rsp), %cl
	movb	%cl, 507(%rax)
	movb	900(%rsp), %cl
	movb	%cl, 508(%rax)
	movb	901(%rsp), %cl
	movb	%cl, 509(%rax)
	movb	902(%rsp), %cl
	movb	%cl, 510(%rax)
	movb	903(%rsp), %cl
	movb	%cl, 511(%rax)
	movb	904(%rsp), %cl
	movb	%cl, 512(%rax)
	movb	905(%rsp), %cl
	movb	%cl, 513(%rax)
	movb	906(%rsp), %cl
	movb	%cl, 514(%rax)
	movb	907(%rsp), %cl
	movb	%cl, 515(%rax)
	movb	908(%rsp), %cl
	movb	%cl, 516(%rax)
	movb	909(%rsp), %cl
	movb	%cl, 517(%rax)
	movb	910(%rsp), %cl
	movb	%cl, 518(%rax)
	movb	911(%rsp), %cl
	movb	%cl, 519(%rax)
	movb	912(%rsp), %cl
	movb	%cl, 520(%rax)
	movb	913(%rsp), %cl
	movb	%cl, 521(%rax)
	movb	914(%rsp), %cl
	movb	%cl, 522(%rax)
	movb	915(%rsp), %cl
	movb	%cl, 523(%rax)
	movb	916(%rsp), %cl
	movb	%cl, 524(%rax)
	movb	917(%rsp), %cl
	movb	%cl, 525(%rax)
	movb	918(%rsp), %cl
	movb	%cl, 526(%rax)
	movb	919(%rsp), %cl
	movb	%cl, 527(%rax)
	movb	920(%rsp), %cl
	movb	%cl, 528(%rax)
	movb	921(%rsp), %cl
	movb	%cl, 529(%rax)
	movb	922(%rsp), %cl
	movb	%cl, 530(%rax)
	movb	923(%rsp), %cl
	movb	%cl, 531(%rax)
	movb	924(%rsp), %cl
	movb	%cl, 532(%rax)
	movb	925(%rsp), %cl
	movb	%cl, 533(%rax)
	movb	926(%rsp), %cl
	movb	%cl, 534(%rax)
	movb	927(%rsp), %cl
	movb	%cl, 535(%rax)
	movb	928(%rsp), %cl
	movb	%cl, 536(%rax)
	movb	929(%rsp), %cl
	movb	%cl, 537(%rax)
	movb	930(%rsp), %cl
	movb	%cl, 538(%rax)
	movb	931(%rsp), %cl
	movb	%cl, 539(%rax)
	movb	932(%rsp), %cl
	movb	%cl, 540(%rax)
	movb	933(%rsp), %cl
	movb	%cl, 541(%rax)
	movb	934(%rsp), %cl
	movb	%cl, 542(%rax)
	movb	935(%rsp), %cl
	movb	%cl, 543(%rax)
	movb	936(%rsp), %cl
	movb	%cl, 544(%rax)
	movb	937(%rsp), %cl
	movb	%cl, 545(%rax)
	movb	938(%rsp), %cl
	movb	%cl, 546(%rax)
	movb	939(%rsp), %cl
	movb	%cl, 547(%rax)
	movb	940(%rsp), %cl
	movb	%cl, 548(%rax)
	movb	941(%rsp), %cl
	movb	%cl, 549(%rax)
	movb	942(%rsp), %cl
	movb	%cl, 550(%rax)
	movb	943(%rsp), %cl
	movb	%cl, 551(%rax)
	movb	944(%rsp), %cl
	movb	%cl, 552(%rax)
	movb	945(%rsp), %cl
	movb	%cl, 553(%rax)
	movb	946(%rsp), %cl
	movb	%cl, 554(%rax)
	movb	947(%rsp), %cl
	movb	%cl, 555(%rax)
	movb	948(%rsp), %cl
	movb	%cl, 556(%rax)
	movb	949(%rsp), %cl
	movb	%cl, 557(%rax)
	movb	950(%rsp), %cl
	movb	%cl, 558(%rax)
	movb	951(%rsp), %cl
	movb	%cl, 559(%rax)
	movb	952(%rsp), %cl
	movb	%cl, 560(%rax)
	movb	953(%rsp), %cl
	movb	%cl, 561(%rax)
	movb	954(%rsp), %cl
	movb	%cl, 562(%rax)
	movb	955(%rsp), %cl
	movb	%cl, 563(%rax)
	movb	956(%rsp), %cl
	movb	%cl, 564(%rax)
	movb	957(%rsp), %cl
	movb	%cl, 565(%rax)
	movb	958(%rsp), %cl
	movb	%cl, 566(%rax)
	movb	959(%rsp), %cl
	movb	%cl, 567(%rax)
	movb	960(%rsp), %cl
	movb	%cl, 568(%rax)
	movb	961(%rsp), %cl
	movb	%cl, 569(%rax)
	movb	962(%rsp), %cl
	movb	%cl, 570(%rax)
	movb	963(%rsp), %cl
	movb	%cl, 571(%rax)
	movb	964(%rsp), %cl
	movb	%cl, 572(%rax)
	movb	965(%rsp), %cl
	movb	%cl, 573(%rax)
	movb	966(%rsp), %cl
	movb	%cl, 574(%rax)
	movb	967(%rsp), %cl
	movb	%cl, 575(%rax)
	movb	968(%rsp), %cl
	movb	%cl, 576(%rax)
	movb	969(%rsp), %cl
	movb	%cl, 577(%rax)
	movb	970(%rsp), %cl
	movb	%cl, 578(%rax)
	movb	971(%rsp), %cl
	movb	%cl, 579(%rax)
	movb	972(%rsp), %cl
	movb	%cl, 580(%rax)
	movb	973(%rsp), %cl
	movb	%cl, 581(%rax)
	movb	974(%rsp), %cl
	movb	%cl, 582(%rax)
	movb	975(%rsp), %cl
	movb	%cl, 583(%rax)
	movb	976(%rsp), %cl
	movb	%cl, 584(%rax)
	movb	977(%rsp), %cl
	movb	%cl, 585(%rax)
	movb	978(%rsp), %cl
	movb	%cl, 586(%rax)
	movb	979(%rsp), %cl
	movb	%cl, 587(%rax)
	movb	980(%rsp), %cl
	movb	%cl, 588(%rax)
	movb	981(%rsp), %cl
	movb	%cl, 589(%rax)
	movb	982(%rsp), %cl
	movb	%cl, 590(%rax)
	movb	983(%rsp), %cl
	movb	%cl, 591(%rax)
	movb	984(%rsp), %cl
	movb	%cl, 592(%rax)
	movb	985(%rsp), %cl
	movb	%cl, 593(%rax)
	movb	986(%rsp), %cl
	movb	%cl, 594(%rax)
	movb	987(%rsp), %cl
	movb	%cl, 595(%rax)
	movb	988(%rsp), %cl
	movb	%cl, 596(%rax)
	movb	989(%rsp), %cl
	movb	%cl, 597(%rax)
	movb	990(%rsp), %cl
	movb	%cl, 598(%rax)
	movb	991(%rsp), %cl
	movb	%cl, 599(%rax)
	movb	992(%rsp), %cl
	movb	%cl, 600(%rax)
	movb	993(%rsp), %cl
	movb	%cl, 601(%rax)
	movb	994(%rsp), %cl
	movb	%cl, 602(%rax)
	movb	995(%rsp), %cl
	movb	%cl, 603(%rax)
	movb	996(%rsp), %cl
	movb	%cl, 604(%rax)
	movb	997(%rsp), %cl
	movb	%cl, 605(%rax)
	movb	998(%rsp), %cl
	movb	%cl, 606(%rax)
	movb	999(%rsp), %cl
	movb	%cl, 607(%rax)
	movb	1000(%rsp), %cl
	movb	%cl, 608(%rax)
	movb	1001(%rsp), %cl
	movb	%cl, 609(%rax)
	movb	1002(%rsp), %cl
	movb	%cl, 610(%rax)
	movb	1003(%rsp), %cl
	movb	%cl, 611(%rax)
	movb	1004(%rsp), %cl
	movb	%cl, 612(%rax)
	movb	1005(%rsp), %cl
	movb	%cl, 613(%rax)
	movb	1006(%rsp), %cl
	movb	%cl, 614(%rax)
	movb	1007(%rsp), %cl
	movb	%cl, 615(%rax)
	movb	1008(%rsp), %cl
	movb	%cl, 616(%rax)
	movb	1009(%rsp), %cl
	movb	%cl, 617(%rax)
	movb	1010(%rsp), %cl
	movb	%cl, 618(%rax)
	movb	1011(%rsp), %cl
	movb	%cl, 619(%rax)
	movb	1012(%rsp), %cl
	movb	%cl, 620(%rax)
	movb	1013(%rsp), %cl
	movb	%cl, 621(%rax)
	movb	1014(%rsp), %cl
	movb	%cl, 622(%rax)
	movb	1015(%rsp), %cl
	movb	%cl, 623(%rax)
	movb	1016(%rsp), %cl
	movb	%cl, 624(%rax)
	movb	1017(%rsp), %cl
	movb	%cl, 625(%rax)
	movb	1018(%rsp), %cl
	movb	%cl, 626(%rax)
	movb	1019(%rsp), %cl
	movb	%cl, 627(%rax)
	movb	1020(%rsp), %cl
	movb	%cl, 628(%rax)
	movb	1021(%rsp), %cl
	movb	%cl, 629(%rax)
	movb	1022(%rsp), %cl
	movb	%cl, 630(%rax)
	movb	1023(%rsp), %cl
	movb	%cl, 631(%rax)
	movb	1024(%rsp), %cl
	movb	%cl, 632(%rax)
	movb	1025(%rsp), %cl
	movb	%cl, 633(%rax)
	movb	1026(%rsp), %cl
	movb	%cl, 634(%rax)
	movb	1027(%rsp), %cl
	movb	%cl, 635(%rax)
	movb	1028(%rsp), %cl
	movb	%cl, 636(%rax)
	movb	1029(%rsp), %cl
	movb	%cl, 637(%rax)
	movb	1030(%rsp), %cl
	movb	%cl, 638(%rax)
	movb	1031(%rsp), %cl
	movb	%cl, 639(%rax)
	movb	1032(%rsp), %cl
	movb	%cl, 640(%rax)
	movb	1033(%rsp), %cl
	movb	%cl, 641(%rax)
	movb	1034(%rsp), %cl
	movb	%cl, 642(%rax)
	movb	1035(%rsp), %cl
	movb	%cl, 643(%rax)
	movb	1036(%rsp), %cl
	movb	%cl, 644(%rax)
	movb	1037(%rsp), %cl
	movb	%cl, 645(%rax)
	movb	1038(%rsp), %cl
	movb	%cl, 646(%rax)
	movb	1039(%rsp), %cl
	movb	%cl, 647(%rax)
	movb	1040(%rsp), %cl
	movb	%cl, 648(%rax)
	movb	1041(%rsp), %cl
	movb	%cl, 649(%rax)
	movb	1042(%rsp), %cl
	movb	%cl, 650(%rax)
	movb	1043(%rsp), %cl
	movb	%cl, 651(%rax)
	movb	1044(%rsp), %cl
	movb	%cl, 652(%rax)
	movb	1045(%rsp), %cl
	movb	%cl, 653(%rax)
	movb	1046(%rsp), %cl
	movb	%cl, 654(%rax)
	movb	1047(%rsp), %cl
	movb	%cl, 655(%rax)
	movb	1048(%rsp), %cl
	movb	%cl, 656(%rax)
	movb	1049(%rsp), %cl
	movb	%cl, 657(%rax)
	movb	1050(%rsp), %cl
	movb	%cl, 658(%rax)
	movb	1051(%rsp), %cl
	movb	%cl, 659(%rax)
	movb	1052(%rsp), %cl
	movb	%cl, 660(%rax)
	movb	1053(%rsp), %cl
	movb	%cl, 661(%rax)
	movb	1054(%rsp), %cl
	movb	%cl, 662(%rax)
	movb	1055(%rsp), %cl
	movb	%cl, 663(%rax)
	movb	1056(%rsp), %cl
	movb	%cl, 664(%rax)
	movb	1057(%rsp), %cl
	movb	%cl, 665(%rax)
	movb	1058(%rsp), %cl
	movb	%cl, 666(%rax)
	movb	1059(%rsp), %cl
	movb	%cl, 667(%rax)
	movb	1060(%rsp), %cl
	movb	%cl, 668(%rax)
	movb	1061(%rsp), %cl
	movb	%cl, 669(%rax)
	movb	1062(%rsp), %cl
	movb	%cl, 670(%rax)
	movb	1063(%rsp), %cl
	movb	%cl, 671(%rax)
	movb	1064(%rsp), %cl
	movb	%cl, 672(%rax)
	movb	1065(%rsp), %cl
	movb	%cl, 673(%rax)
	movb	1066(%rsp), %cl
	movb	%cl, 674(%rax)
	movb	1067(%rsp), %cl
	movb	%cl, 675(%rax)
	movb	1068(%rsp), %cl
	movb	%cl, 676(%rax)
	movb	1069(%rsp), %cl
	movb	%cl, 677(%rax)
	movb	1070(%rsp), %cl
	movb	%cl, 678(%rax)
	movb	1071(%rsp), %cl
	movb	%cl, 679(%rax)
	movb	1072(%rsp), %cl
	movb	%cl, 680(%rax)
	movb	1073(%rsp), %cl
	movb	%cl, 681(%rax)
	movb	1074(%rsp), %cl
	movb	%cl, 682(%rax)
	movb	1075(%rsp), %cl
	movb	%cl, 683(%rax)
	movb	1076(%rsp), %cl
	movb	%cl, 684(%rax)
	movb	1077(%rsp), %cl
	movb	%cl, 685(%rax)
	movb	1078(%rsp), %cl
	movb	%cl, 686(%rax)
	movb	1079(%rsp), %cl
	movb	%cl, 687(%rax)
	movb	1080(%rsp), %cl
	movb	%cl, 688(%rax)
	movb	1081(%rsp), %cl
	movb	%cl, 689(%rax)
	movb	1082(%rsp), %cl
	movb	%cl, 690(%rax)
	movb	1083(%rsp), %cl
	movb	%cl, 691(%rax)
	movb	1084(%rsp), %cl
	movb	%cl, 692(%rax)
	movb	1085(%rsp), %cl
	movb	%cl, 693(%rax)
	movb	1086(%rsp), %cl
	movb	%cl, 694(%rax)
	movb	1087(%rsp), %cl
	movb	%cl, 695(%rax)
	movb	1088(%rsp), %cl
	movb	%cl, 696(%rax)
	movb	1089(%rsp), %cl
	movb	%cl, 697(%rax)
	movb	1090(%rsp), %cl
	movb	%cl, 698(%rax)
	movb	1091(%rsp), %cl
	movb	%cl, 699(%rax)
	movb	1092(%rsp), %cl
	movb	%cl, 700(%rax)
	movb	1093(%rsp), %cl
	movb	%cl, 701(%rax)
	movb	1094(%rsp), %cl
	movb	%cl, 702(%rax)
	movb	1095(%rsp), %cl
	movb	%cl, 703(%rax)
	movb	1096(%rsp), %cl
	movb	%cl, 704(%rax)
	movb	1097(%rsp), %cl
	movb	%cl, 705(%rax)
	movb	1098(%rsp), %cl
	movb	%cl, 706(%rax)
	movb	1099(%rsp), %cl
	movb	%cl, 707(%rax)
	movb	1100(%rsp), %cl
	movb	%cl, 708(%rax)
	movb	1101(%rsp), %cl
	movb	%cl, 709(%rax)
	movb	1102(%rsp), %cl
	movb	%cl, 710(%rax)
	movb	1103(%rsp), %cl
	movb	%cl, 711(%rax)
	movb	1104(%rsp), %cl
	movb	%cl, 712(%rax)
	movb	1105(%rsp), %cl
	movb	%cl, 713(%rax)
	movb	1106(%rsp), %cl
	movb	%cl, 714(%rax)
	movb	1107(%rsp), %cl
	movb	%cl, 715(%rax)
	movb	1108(%rsp), %cl
	movb	%cl, 716(%rax)
	movb	1109(%rsp), %cl
	movb	%cl, 717(%rax)
	movb	1110(%rsp), %cl
	movb	%cl, 718(%rax)
	movb	1111(%rsp), %cl
	movb	%cl, 719(%rax)
	movb	1112(%rsp), %cl
	movb	%cl, 720(%rax)
	movb	1113(%rsp), %cl
	movb	%cl, 721(%rax)
	movb	1114(%rsp), %cl
	movb	%cl, 722(%rax)
	movb	1115(%rsp), %cl
	movb	%cl, 723(%rax)
	movb	1116(%rsp), %cl
	movb	%cl, 724(%rax)
	movb	1117(%rsp), %cl
	movb	%cl, 725(%rax)
	movb	1118(%rsp), %cl
	movb	%cl, 726(%rax)
	movb	1119(%rsp), %cl
	movb	%cl, 727(%rax)
	movb	1120(%rsp), %cl
	movb	%cl, 728(%rax)
	movb	1121(%rsp), %cl
	movb	%cl, 729(%rax)
	movb	1122(%rsp), %cl
	movb	%cl, 730(%rax)
	movb	1123(%rsp), %cl
	movb	%cl, 731(%rax)
	movb	1124(%rsp), %cl
	movb	%cl, 732(%rax)
	movb	1125(%rsp), %cl
	movb	%cl, 733(%rax)
	movb	1126(%rsp), %cl
	movb	%cl, 734(%rax)
	movb	1127(%rsp), %cl
	movb	%cl, 735(%rax)
	movb	1128(%rsp), %cl
	movb	%cl, 736(%rax)
	movb	1129(%rsp), %cl
	movb	%cl, 737(%rax)
	movb	1130(%rsp), %cl
	movb	%cl, 738(%rax)
	movb	1131(%rsp), %cl
	movb	%cl, 739(%rax)
	movb	1132(%rsp), %cl
	movb	%cl, 740(%rax)
	movb	1133(%rsp), %cl
	movb	%cl, 741(%rax)
	movb	1134(%rsp), %cl
	movb	%cl, 742(%rax)
	movb	1135(%rsp), %cl
	movb	%cl, 743(%rax)
	movb	1136(%rsp), %cl
	movb	%cl, 744(%rax)
	movb	1137(%rsp), %cl
	movb	%cl, 745(%rax)
	movb	1138(%rsp), %cl
	movb	%cl, 746(%rax)
	movb	1139(%rsp), %cl
	movb	%cl, 747(%rax)
	movb	1140(%rsp), %cl
	movb	%cl, 748(%rax)
	movb	1141(%rsp), %cl
	movb	%cl, 749(%rax)
	movb	1142(%rsp), %cl
	movb	%cl, 750(%rax)
	movb	1143(%rsp), %cl
	movb	%cl, 751(%rax)
	movb	1144(%rsp), %cl
	movb	%cl, 752(%rax)
	movb	1145(%rsp), %cl
	movb	%cl, 753(%rax)
	movb	1146(%rsp), %cl
	movb	%cl, 754(%rax)
	movb	1147(%rsp), %cl
	movb	%cl, 755(%rax)
	movb	1148(%rsp), %cl
	movb	%cl, 756(%rax)
	movb	1149(%rsp), %cl
	movb	%cl, 757(%rax)
	movb	1150(%rsp), %cl
	movb	%cl, 758(%rax)
	movb	1151(%rsp), %cl
	movb	%cl, 759(%rax)
	movb	1152(%rsp), %cl
	movb	%cl, 760(%rax)
	movb	1153(%rsp), %cl
	movb	%cl, 761(%rax)
	movb	1154(%rsp), %cl
	movb	%cl, 762(%rax)
	movb	1155(%rsp), %cl
	movb	%cl, 763(%rax)
	movb	1156(%rsp), %cl
	movb	%cl, 764(%rax)
	movb	1157(%rsp), %cl
	movb	%cl, 765(%rax)
	movb	1158(%rsp), %cl
	movb	%cl, 766(%rax)
	movb	1159(%rsp), %cl
	movb	%cl, 767(%rax)
	movb	1160(%rsp), %cl
	movb	%cl, 768(%rax)
	movb	1161(%rsp), %cl
	movb	%cl, 769(%rax)
	movb	1162(%rsp), %cl
	movb	%cl, 770(%rax)
	movb	1163(%rsp), %cl
	movb	%cl, 771(%rax)
	movb	1164(%rsp), %cl
	movb	%cl, 772(%rax)
	movb	1165(%rsp), %cl
	movb	%cl, 773(%rax)
	movb	1166(%rsp), %cl
	movb	%cl, 774(%rax)
	movb	1167(%rsp), %cl
	movb	%cl, 775(%rax)
	movb	1168(%rsp), %cl
	movb	%cl, 776(%rax)
	movb	1169(%rsp), %cl
	movb	%cl, 777(%rax)
	movb	1170(%rsp), %cl
	movb	%cl, 778(%rax)
	movb	1171(%rsp), %cl
	movb	%cl, 779(%rax)
	movb	1172(%rsp), %cl
	movb	%cl, 780(%rax)
	movb	1173(%rsp), %cl
	movb	%cl, 781(%rax)
	movb	1174(%rsp), %cl
	movb	%cl, 782(%rax)
	movb	1175(%rsp), %cl
	movb	%cl, 783(%rax)
	movb	1176(%rsp), %cl
	movb	%cl, 784(%rax)
	movb	1177(%rsp), %cl
	movb	%cl, 785(%rax)
	movb	1178(%rsp), %cl
	movb	%cl, 786(%rax)
	movb	1179(%rsp), %cl
	movb	%cl, 787(%rax)
	movb	1180(%rsp), %cl
	movb	%cl, 788(%rax)
	movb	1181(%rsp), %cl
	movb	%cl, 789(%rax)
	movb	1182(%rsp), %cl
	movb	%cl, 790(%rax)
	movb	1183(%rsp), %cl
	movb	%cl, 791(%rax)
	movb	1184(%rsp), %cl
	movb	%cl, 792(%rax)
	movb	1185(%rsp), %cl
	movb	%cl, 793(%rax)
	movb	1186(%rsp), %cl
	movb	%cl, 794(%rax)
	movb	1187(%rsp), %cl
	movb	%cl, 795(%rax)
	movb	1188(%rsp), %cl
	movb	%cl, 796(%rax)
	movb	1189(%rsp), %cl
	movb	%cl, 797(%rax)
	movb	1190(%rsp), %cl
	movb	%cl, 798(%rax)
	movb	1191(%rsp), %cl
	movb	%cl, 799(%rax)
	movb	1192(%rsp), %cl
	movb	%cl, 800(%rax)
	movb	1193(%rsp), %cl
	movb	%cl, 801(%rax)
	movb	1194(%rsp), %cl
	movb	%cl, 802(%rax)
	movb	1195(%rsp), %cl
	movb	%cl, 803(%rax)
	movb	1196(%rsp), %cl
	movb	%cl, 804(%rax)
	movb	1197(%rsp), %cl
	movb	%cl, 805(%rax)
	movb	1198(%rsp), %cl
	movb	%cl, 806(%rax)
	movb	1199(%rsp), %cl
	movb	%cl, 807(%rax)
	movb	1200(%rsp), %cl
	movb	%cl, 808(%rax)
	movb	1201(%rsp), %cl
	movb	%cl, 809(%rax)
	movb	1202(%rsp), %cl
	movb	%cl, 810(%rax)
	movb	1203(%rsp), %cl
	movb	%cl, 811(%rax)
	movb	1204(%rsp), %cl
	movb	%cl, 812(%rax)
	movb	1205(%rsp), %cl
	movb	%cl, 813(%rax)
	movb	1206(%rsp), %cl
	movb	%cl, 814(%rax)
	movb	1207(%rsp), %cl
	movb	%cl, 815(%rax)
	movb	1208(%rsp), %cl
	movb	%cl, 816(%rax)
	movb	1209(%rsp), %cl
	movb	%cl, 817(%rax)
	movb	1210(%rsp), %cl
	movb	%cl, 818(%rax)
	movb	1211(%rsp), %cl
	movb	%cl, 819(%rax)
	movb	1212(%rsp), %cl
	movb	%cl, 820(%rax)
	movb	1213(%rsp), %cl
	movb	%cl, 821(%rax)
	movb	1214(%rsp), %cl
	movb	%cl, 822(%rax)
	movb	1215(%rsp), %cl
	movb	%cl, 823(%rax)
	movb	1216(%rsp), %cl
	movb	%cl, 824(%rax)
	movb	1217(%rsp), %cl
	movb	%cl, 825(%rax)
	movb	1218(%rsp), %cl
	movb	%cl, 826(%rax)
	movb	1219(%rsp), %cl
	movb	%cl, 827(%rax)
	movb	1220(%rsp), %cl
	movb	%cl, 828(%rax)
	movb	1221(%rsp), %cl
	movb	%cl, 829(%rax)
	movb	1222(%rsp), %cl
	movb	%cl, 830(%rax)
	movb	1223(%rsp), %cl
	movb	%cl, 831(%rax)
	movb	1224(%rsp), %cl
	movb	%cl, 832(%rax)
	movb	1225(%rsp), %cl
	movb	%cl, 833(%rax)
	movb	1226(%rsp), %cl
	movb	%cl, 834(%rax)
	movb	1227(%rsp), %cl
	movb	%cl, 835(%rax)
	movb	1228(%rsp), %cl
	movb	%cl, 836(%rax)
	movb	1229(%rsp), %cl
	movb	%cl, 837(%rax)
	movb	1230(%rsp), %cl
	movb	%cl, 838(%rax)
	movb	1231(%rsp), %cl
	movb	%cl, 839(%rax)
	movb	1232(%rsp), %cl
	movb	%cl, 840(%rax)
	movb	1233(%rsp), %cl
	movb	%cl, 841(%rax)
	movb	1234(%rsp), %cl
	movb	%cl, 842(%rax)
	movb	1235(%rsp), %cl
	movb	%cl, 843(%rax)
	movb	1236(%rsp), %cl
	movb	%cl, 844(%rax)
	movb	1237(%rsp), %cl
	movb	%cl, 845(%rax)
	movb	1238(%rsp), %cl
	movb	%cl, 846(%rax)
	movb	1239(%rsp), %cl
	movb	%cl, 847(%rax)
	movb	1240(%rsp), %cl
	movb	%cl, 848(%rax)
	movb	1241(%rsp), %cl
	movb	%cl, 849(%rax)
	movb	1242(%rsp), %cl
	movb	%cl, 850(%rax)
	movb	1243(%rsp), %cl
	movb	%cl, 851(%rax)
	movb	1244(%rsp), %cl
	movb	%cl, 852(%rax)
	movb	1245(%rsp), %cl
	movb	%cl, 853(%rax)
	movb	1246(%rsp), %cl
	movb	%cl, 854(%rax)
	movb	1247(%rsp), %cl
	movb	%cl, 855(%rax)
	movb	1248(%rsp), %cl
	movb	%cl, 856(%rax)
	movb	1249(%rsp), %cl
	movb	%cl, 857(%rax)
	movb	1250(%rsp), %cl
	movb	%cl, 858(%rax)
	movb	1251(%rsp), %cl
	movb	%cl, 859(%rax)
	movb	1252(%rsp), %cl
	movb	%cl, 860(%rax)
	movb	1253(%rsp), %cl
	movb	%cl, 861(%rax)
	movb	1254(%rsp), %cl
	movb	%cl, 862(%rax)
	movb	1255(%rsp), %cl
	movb	%cl, 863(%rax)
	movb	1256(%rsp), %cl
	movb	%cl, 864(%rax)
	movb	1257(%rsp), %cl
	movb	%cl, 865(%rax)
	movb	1258(%rsp), %cl
	movb	%cl, 866(%rax)
	movb	1259(%rsp), %cl
	movb	%cl, 867(%rax)
	movb	1260(%rsp), %cl
	movb	%cl, 868(%rax)
	movb	1261(%rsp), %cl
	movb	%cl, 869(%rax)
	movb	1262(%rsp), %cl
	movb	%cl, 870(%rax)
	movb	1263(%rsp), %cl
	movb	%cl, 871(%rax)
	movb	1264(%rsp), %cl
	movb	%cl, 872(%rax)
	movb	1265(%rsp), %cl
	movb	%cl, 873(%rax)
	movb	1266(%rsp), %cl
	movb	%cl, 874(%rax)
	movb	1267(%rsp), %cl
	movb	%cl, 875(%rax)
	movb	1268(%rsp), %cl
	movb	%cl, 876(%rax)
	movb	1269(%rsp), %cl
	movb	%cl, 877(%rax)
	movb	1270(%rsp), %cl
	movb	%cl, 878(%rax)
	movb	1271(%rsp), %cl
	movb	%cl, 879(%rax)
	movb	1272(%rsp), %cl
	movb	%cl, 880(%rax)
	movb	1273(%rsp), %cl
	movb	%cl, 881(%rax)
	movb	1274(%rsp), %cl
	movb	%cl, 882(%rax)
	movb	1275(%rsp), %cl
	movb	%cl, 883(%rax)
	movb	1276(%rsp), %cl
	movb	%cl, 884(%rax)
	movb	1277(%rsp), %cl
	movb	%cl, 885(%rax)
	movb	1278(%rsp), %cl
	movb	%cl, 886(%rax)
	movb	1279(%rsp), %cl
	movb	%cl, 887(%rax)
	movb	1280(%rsp), %cl
	movb	%cl, 888(%rax)
	movb	1281(%rsp), %cl
	movb	%cl, 889(%rax)
	movb	1282(%rsp), %cl
	movb	%cl, 890(%rax)
	movb	1283(%rsp), %cl
	movb	%cl, 891(%rax)
	movb	1284(%rsp), %cl
	movb	%cl, 892(%rax)
	movb	1285(%rsp), %cl
	movb	%cl, 893(%rax)
	movb	1286(%rsp), %cl
	movb	%cl, 894(%rax)
	movb	1287(%rsp), %cl
	movb	%cl, 895(%rax)
	movb	1288(%rsp), %cl
	movb	%cl, 896(%rax)
	movb	1289(%rsp), %cl
	movb	%cl, 897(%rax)
	movb	1290(%rsp), %cl
	movb	%cl, 898(%rax)
	movb	1291(%rsp), %cl
	movb	%cl, 899(%rax)
	movb	1292(%rsp), %cl
	movb	%cl, 900(%rax)
	movb	1293(%rsp), %cl
	movb	%cl, 901(%rax)
	movb	1294(%rsp), %cl
	movb	%cl, 902(%rax)
	movb	1295(%rsp), %cl
	movb	%cl, 903(%rax)
	movb	1296(%rsp), %cl
	movb	%cl, 904(%rax)
	movb	1297(%rsp), %cl
	movb	%cl, 905(%rax)
	movb	1298(%rsp), %cl
	movb	%cl, 906(%rax)
	movb	1299(%rsp), %cl
	movb	%cl, 907(%rax)
	movb	1300(%rsp), %cl
	movb	%cl, 908(%rax)
	movb	1301(%rsp), %cl
	movb	%cl, 909(%rax)
	movb	1302(%rsp), %cl
	movb	%cl, 910(%rax)
	movb	1303(%rsp), %cl
	movb	%cl, 911(%rax)
	movb	1304(%rsp), %cl
	movb	%cl, 912(%rax)
	movb	1305(%rsp), %cl
	movb	%cl, 913(%rax)
	movb	1306(%rsp), %cl
	movb	%cl, 914(%rax)
	movb	1307(%rsp), %cl
	movb	%cl, 915(%rax)
	movb	1308(%rsp), %cl
	movb	%cl, 916(%rax)
	movb	1309(%rsp), %cl
	movb	%cl, 917(%rax)
	movb	1310(%rsp), %cl
	movb	%cl, 918(%rax)
	movb	1311(%rsp), %cl
	movb	%cl, 919(%rax)
	movb	1312(%rsp), %cl
	movb	%cl, 920(%rax)
	movb	1313(%rsp), %cl
	movb	%cl, 921(%rax)
	movb	1314(%rsp), %cl
	movb	%cl, 922(%rax)
	movb	1315(%rsp), %cl
	movb	%cl, 923(%rax)
	movb	1316(%rsp), %cl
	movb	%cl, 924(%rax)
	movb	1317(%rsp), %cl
	movb	%cl, 925(%rax)
	movb	1318(%rsp), %cl
	movb	%cl, 926(%rax)
	movb	1319(%rsp), %cl
	movb	%cl, 927(%rax)
	movb	1320(%rsp), %cl
	movb	%cl, 928(%rax)
	movb	1321(%rsp), %cl
	movb	%cl, 929(%rax)
	movb	1322(%rsp), %cl
	movb	%cl, 930(%rax)
	movb	1323(%rsp), %cl
	movb	%cl, 931(%rax)
	movb	1324(%rsp), %cl
	movb	%cl, 932(%rax)
	movb	1325(%rsp), %cl
	movb	%cl, 933(%rax)
	movb	1326(%rsp), %cl
	movb	%cl, 934(%rax)
	movb	1327(%rsp), %cl
	movb	%cl, 935(%rax)
	movb	1328(%rsp), %cl
	movb	%cl, 936(%rax)
	movb	1329(%rsp), %cl
	movb	%cl, 937(%rax)
	movb	1330(%rsp), %cl
	movb	%cl, 938(%rax)
	movb	1331(%rsp), %cl
	movb	%cl, 939(%rax)
	movb	1332(%rsp), %cl
	movb	%cl, 940(%rax)
	movb	1333(%rsp), %cl
	movb	%cl, 941(%rax)
	movb	1334(%rsp), %cl
	movb	%cl, 942(%rax)
	movb	1335(%rsp), %cl
	movb	%cl, 943(%rax)
	movb	1336(%rsp), %cl
	movb	%cl, 944(%rax)
	movb	1337(%rsp), %cl
	movb	%cl, 945(%rax)
	movb	1338(%rsp), %cl
	movb	%cl, 946(%rax)
	movb	1339(%rsp), %cl
	movb	%cl, 947(%rax)
	movb	1340(%rsp), %cl
	movb	%cl, 948(%rax)
	movb	1341(%rsp), %cl
	movb	%cl, 949(%rax)
	movb	1342(%rsp), %cl
	movb	%cl, 950(%rax)
	movb	1343(%rsp), %cl
	movb	%cl, 951(%rax)
	movb	1344(%rsp), %cl
	movb	%cl, 952(%rax)
	movb	1345(%rsp), %cl
	movb	%cl, 953(%rax)
	movb	1346(%rsp), %cl
	movb	%cl, 954(%rax)
	movb	1347(%rsp), %cl
	movb	%cl, 955(%rax)
	movb	1348(%rsp), %cl
	movb	%cl, 956(%rax)
	movb	1349(%rsp), %cl
	movb	%cl, 957(%rax)
	movb	1350(%rsp), %cl
	movb	%cl, 958(%rax)
	movb	1351(%rsp), %cl
	movb	%cl, 959(%rax)
	movb	1352(%rsp), %cl
	movb	%cl, 960(%rax)
	movb	1353(%rsp), %cl
	movb	%cl, 961(%rax)
	movb	1354(%rsp), %cl
	movb	%cl, 962(%rax)
	movb	1355(%rsp), %cl
	movb	%cl, 963(%rax)
	movb	1356(%rsp), %cl
	movb	%cl, 964(%rax)
	movb	1357(%rsp), %cl
	movb	%cl, 965(%rax)
	movb	1358(%rsp), %cl
	movb	%cl, 966(%rax)
	movb	1359(%rsp), %cl
	movb	%cl, 967(%rax)
	movb	1360(%rsp), %cl
	movb	%cl, 968(%rax)
	movb	1361(%rsp), %cl
	movb	%cl, 969(%rax)
	movb	1362(%rsp), %cl
	movb	%cl, 970(%rax)
	movb	1363(%rsp), %cl
	movb	%cl, 971(%rax)
	movb	1364(%rsp), %cl
	movb	%cl, 972(%rax)
	movb	1365(%rsp), %cl
	movb	%cl, 973(%rax)
	movb	1366(%rsp), %cl
	movb	%cl, 974(%rax)
	movb	1367(%rsp), %cl
	movb	%cl, 975(%rax)
	movb	1368(%rsp), %cl
	movb	%cl, 976(%rax)
	movb	1369(%rsp), %cl
	movb	%cl, 977(%rax)
	movb	1370(%rsp), %cl
	movb	%cl, 978(%rax)
	movb	1371(%rsp), %cl
	movb	%cl, 979(%rax)
	movb	1372(%rsp), %cl
	movb	%cl, 980(%rax)
	movb	1373(%rsp), %cl
	movb	%cl, 981(%rax)
	movb	1374(%rsp), %cl
	movb	%cl, 982(%rax)
	movb	1375(%rsp), %cl
	movb	%cl, 983(%rax)
	movb	1376(%rsp), %cl
	movb	%cl, 984(%rax)
	movb	1377(%rsp), %cl
	movb	%cl, 985(%rax)
	movb	1378(%rsp), %cl
	movb	%cl, 986(%rax)
	movb	1379(%rsp), %cl
	movb	%cl, 987(%rax)
	movb	1380(%rsp), %cl
	movb	%cl, 988(%rax)
	movb	1381(%rsp), %cl
	movb	%cl, 989(%rax)
	movb	1382(%rsp), %cl
	movb	%cl, 990(%rax)
	movb	1383(%rsp), %cl
	movb	%cl, 991(%rax)
	movb	1384(%rsp), %cl
	movb	%cl, 992(%rax)
	movb	1385(%rsp), %cl
	movb	%cl, 993(%rax)
	movb	1386(%rsp), %cl
	movb	%cl, 994(%rax)
	movb	1387(%rsp), %cl
	movb	%cl, 995(%rax)
	movb	1388(%rsp), %cl
	movb	%cl, 996(%rax)
	movb	1389(%rsp), %cl
	movb	%cl, 997(%rax)
	movb	1390(%rsp), %cl
	movb	%cl, 998(%rax)
	movb	1391(%rsp), %cl
	movb	%cl, 999(%rax)
	movb	1392(%rsp), %cl
	movb	%cl, 1000(%rax)
	movb	1393(%rsp), %cl
	movb	%cl, 1001(%rax)
	movb	1394(%rsp), %cl
	movb	%cl, 1002(%rax)
	movb	1395(%rsp), %cl
	movb	%cl, 1003(%rax)
	movb	1396(%rsp), %cl
	movb	%cl, 1004(%rax)
	movb	1397(%rsp), %cl
	movb	%cl, 1005(%rax)
	movb	1398(%rsp), %cl
	movb	%cl, 1006(%rax)
	movb	1399(%rsp), %cl
	movb	%cl, 1007(%rax)
	movb	1400(%rsp), %cl
	movb	%cl, 1008(%rax)
	movb	1401(%rsp), %cl
	movb	%cl, 1009(%rax)
	movb	1402(%rsp), %cl
	movb	%cl, 1010(%rax)
	movb	1403(%rsp), %cl
	movb	%cl, 1011(%rax)
	movb	1404(%rsp), %cl
	movb	%cl, 1012(%rax)
	movb	1405(%rsp), %cl
	movb	%cl, 1013(%rax)
	movb	1406(%rsp), %cl
	movb	%cl, 1014(%rax)
	movb	1407(%rsp), %cl
	movb	%cl, 1015(%rax)
	movb	1408(%rsp), %cl
	movb	%cl, 1016(%rax)
	movb	1409(%rsp), %cl
	movb	%cl, 1017(%rax)
	movb	1410(%rsp), %cl
	movb	%cl, 1018(%rax)
	movb	1411(%rsp), %cl
	movb	%cl, 1019(%rax)
	movb	1412(%rsp), %cl
	movb	%cl, 1020(%rax)
	movb	1413(%rsp), %cl
	movb	%cl, 1021(%rax)
	movb	1414(%rsp), %cl
	movb	%cl, 1022(%rax)
	movb	1415(%rsp), %cl
	movb	%cl, 1023(%rax)
	movb	1416(%rsp), %cl
	movb	%cl, 1024(%rax)
	movb	1417(%rsp), %cl
	movb	%cl, 1025(%rax)
	movb	1418(%rsp), %cl
	movb	%cl, 1026(%rax)
	movb	1419(%rsp), %cl
	movb	%cl, 1027(%rax)
	movb	1420(%rsp), %cl
	movb	%cl, 1028(%rax)
	movb	1421(%rsp), %cl
	movb	%cl, 1029(%rax)
	movb	1422(%rsp), %cl
	movb	%cl, 1030(%rax)
	movb	1423(%rsp), %cl
	movb	%cl, 1031(%rax)
	movb	1424(%rsp), %cl
	movb	%cl, 1032(%rax)
	movb	1425(%rsp), %cl
	movb	%cl, 1033(%rax)
	movb	1426(%rsp), %cl
	movb	%cl, 1034(%rax)
	movb	1427(%rsp), %cl
	movb	%cl, 1035(%rax)
	movb	1428(%rsp), %cl
	movb	%cl, 1036(%rax)
	movb	1429(%rsp), %cl
	movb	%cl, 1037(%rax)
	movb	1430(%rsp), %cl
	movb	%cl, 1038(%rax)
	movb	1431(%rsp), %cl
	movb	%cl, 1039(%rax)
	movb	1432(%rsp), %cl
	movb	%cl, 1040(%rax)
	movb	1433(%rsp), %cl
	movb	%cl, 1041(%rax)
	movb	1434(%rsp), %cl
	movb	%cl, 1042(%rax)
	movb	1435(%rsp), %cl
	movb	%cl, 1043(%rax)
	movb	1436(%rsp), %cl
	movb	%cl, 1044(%rax)
	movb	1437(%rsp), %cl
	movb	%cl, 1045(%rax)
	movb	1438(%rsp), %cl
	movb	%cl, 1046(%rax)
	movb	1439(%rsp), %cl
	movb	%cl, 1047(%rax)
	movb	1440(%rsp), %cl
	movb	%cl, 1048(%rax)
	movb	1441(%rsp), %cl
	movb	%cl, 1049(%rax)
	movb	1442(%rsp), %cl
	movb	%cl, 1050(%rax)
	movb	1443(%rsp), %cl
	movb	%cl, 1051(%rax)
	movb	1444(%rsp), %cl
	movb	%cl, 1052(%rax)
	movb	1445(%rsp), %cl
	movb	%cl, 1053(%rax)
	movb	1446(%rsp), %cl
	movb	%cl, 1054(%rax)
	movb	1447(%rsp), %cl
	movb	%cl, 1055(%rax)
	movb	1448(%rsp), %cl
	movb	%cl, 1056(%rax)
	movb	1449(%rsp), %cl
	movb	%cl, 1057(%rax)
	movb	1450(%rsp), %cl
	movb	%cl, 1058(%rax)
	movb	1451(%rsp), %cl
	movb	%cl, 1059(%rax)
	movb	1452(%rsp), %cl
	movb	%cl, 1060(%rax)
	movb	1453(%rsp), %cl
	movb	%cl, 1061(%rax)
	movb	1454(%rsp), %cl
	movb	%cl, 1062(%rax)
	movb	1455(%rsp), %cl
	movb	%cl, 1063(%rax)
	movb	1456(%rsp), %cl
	movb	%cl, 1064(%rax)
	movb	1457(%rsp), %cl
	movb	%cl, 1065(%rax)
	movb	1458(%rsp), %cl
	movb	%cl, 1066(%rax)
	movb	1459(%rsp), %cl
	movb	%cl, 1067(%rax)
	movb	1460(%rsp), %cl
	movb	%cl, 1068(%rax)
	movb	1461(%rsp), %cl
	movb	%cl, 1069(%rax)
	movb	1462(%rsp), %cl
	movb	%cl, 1070(%rax)
	movb	1463(%rsp), %cl
	movb	%cl, 1071(%rax)
	movb	1464(%rsp), %cl
	movb	%cl, 1072(%rax)
	movb	1465(%rsp), %cl
	movb	%cl, 1073(%rax)
	movb	1466(%rsp), %cl
	movb	%cl, 1074(%rax)
	movb	1467(%rsp), %cl
	movb	%cl, 1075(%rax)
	movb	1468(%rsp), %cl
	movb	%cl, 1076(%rax)
	movb	1469(%rsp), %cl
	movb	%cl, 1077(%rax)
	movb	1470(%rsp), %cl
	movb	%cl, 1078(%rax)
	movb	1471(%rsp), %cl
	movb	%cl, 1079(%rax)
	movb	1472(%rsp), %cl
	movb	%cl, 1080(%rax)
	movb	1473(%rsp), %cl
	movb	%cl, 1081(%rax)
	movb	1474(%rsp), %cl
	movb	%cl, 1082(%rax)
	movb	1475(%rsp), %cl
	movb	%cl, 1083(%rax)
	movb	1476(%rsp), %cl
	movb	%cl, 1084(%rax)
	movb	1477(%rsp), %cl
	movb	%cl, 1085(%rax)
	movb	1478(%rsp), %cl
	movb	%cl, 1086(%rax)
	movb	1479(%rsp), %cl
	movb	%cl, 1087(%rax)
	movb	1480(%rsp), %cl
	movb	%cl, 1088(%rax)
	movb	1481(%rsp), %cl
	movb	%cl, 1089(%rax)
	movb	1482(%rsp), %cl
	movb	%cl, 1090(%rax)
	movb	1483(%rsp), %cl
	movb	%cl, 1091(%rax)
	movb	1484(%rsp), %cl
	movb	%cl, 1092(%rax)
	movb	1485(%rsp), %cl
	movb	%cl, 1093(%rax)
	movb	1486(%rsp), %cl
	movb	%cl, 1094(%rax)
	movb	1487(%rsp), %cl
	movb	%cl, 1095(%rax)
	movb	1488(%rsp), %cl
	movb	%cl, 1096(%rax)
	movb	1489(%rsp), %cl
	movb	%cl, 1097(%rax)
	movb	1490(%rsp), %cl
	movb	%cl, 1098(%rax)
	movb	1491(%rsp), %cl
	movb	%cl, 1099(%rax)
	movb	1492(%rsp), %cl
	movb	%cl, 1100(%rax)
	movb	1493(%rsp), %cl
	movb	%cl, 1101(%rax)
	movb	1494(%rsp), %cl
	movb	%cl, 1102(%rax)
	movb	1495(%rsp), %cl
	movb	%cl, 1103(%rax)
	movb	1496(%rsp), %cl
	movb	%cl, 1104(%rax)
	movb	1497(%rsp), %cl
	movb	%cl, 1105(%rax)
	movb	1498(%rsp), %cl
	movb	%cl, 1106(%rax)
	movb	1499(%rsp), %cl
	movb	%cl, 1107(%rax)
	movb	1500(%rsp), %cl
	movb	%cl, 1108(%rax)
	movb	1501(%rsp), %cl
	movb	%cl, 1109(%rax)
	movb	1502(%rsp), %cl
	movb	%cl, 1110(%rax)
	movb	1503(%rsp), %cl
	movb	%cl, 1111(%rax)
	movb	1504(%rsp), %cl
	movb	%cl, 1112(%rax)
	movb	1505(%rsp), %cl
	movb	%cl, 1113(%rax)
	movb	1506(%rsp), %cl
	movb	%cl, 1114(%rax)
	movb	1507(%rsp), %cl
	movb	%cl, 1115(%rax)
	movb	1508(%rsp), %cl
	movb	%cl, 1116(%rax)
	movb	1509(%rsp), %cl
	movb	%cl, 1117(%rax)
	movb	1510(%rsp), %cl
	movb	%cl, 1118(%rax)
	movb	1511(%rsp), %cl
	movb	%cl, 1119(%rax)
	movb	1512(%rsp), %cl
	movb	%cl, 1120(%rax)
	movb	1513(%rsp), %cl
	movb	%cl, 1121(%rax)
	movb	1514(%rsp), %cl
	movb	%cl, 1122(%rax)
	movb	1515(%rsp), %cl
	movb	%cl, 1123(%rax)
	movb	1516(%rsp), %cl
	movb	%cl, 1124(%rax)
	movb	1517(%rsp), %cl
	movb	%cl, 1125(%rax)
	movb	1518(%rsp), %cl
	movb	%cl, 1126(%rax)
	movb	1519(%rsp), %cl
	movb	%cl, 1127(%rax)
	movb	1520(%rsp), %cl
	movb	%cl, 1128(%rax)
	movb	1521(%rsp), %cl
	movb	%cl, 1129(%rax)
	movb	1522(%rsp), %cl
	movb	%cl, 1130(%rax)
	movb	1523(%rsp), %cl
	movb	%cl, 1131(%rax)
	movb	1524(%rsp), %cl
	movb	%cl, 1132(%rax)
	movb	1525(%rsp), %cl
	movb	%cl, 1133(%rax)
	movb	1526(%rsp), %cl
	movb	%cl, 1134(%rax)
	movb	1527(%rsp), %cl
	movb	%cl, 1135(%rax)
	movb	1528(%rsp), %cl
	movb	%cl, 1136(%rax)
	movb	1529(%rsp), %cl
	movb	%cl, 1137(%rax)
	movb	1530(%rsp), %cl
	movb	%cl, 1138(%rax)
	movb	1531(%rsp), %cl
	movb	%cl, 1139(%rax)
	movb	1532(%rsp), %cl
	movb	%cl, 1140(%rax)
	movb	1533(%rsp), %cl
	movb	%cl, 1141(%rax)
	movb	1534(%rsp), %cl
	movb	%cl, 1142(%rax)
	movb	1535(%rsp), %cl
	movb	%cl, 1143(%rax)
	movb	1536(%rsp), %cl
	movb	%cl, 1144(%rax)
	movb	1537(%rsp), %cl
	movb	%cl, 1145(%rax)
	movb	1538(%rsp), %cl
	movb	%cl, 1146(%rax)
	movb	1539(%rsp), %cl
	movb	%cl, 1147(%rax)
	movb	1540(%rsp), %cl
	movb	%cl, 1148(%rax)
	movb	1541(%rsp), %cl
	movb	%cl, 1149(%rax)
	movb	1542(%rsp), %cl
	movb	%cl, 1150(%rax)
	movb	1543(%rsp), %cl
	movb	%cl, 1151(%rax)
	movb	1544(%rsp), %cl
	movb	%cl, 1152(%rax)
	movb	1545(%rsp), %cl
	movb	%cl, 1153(%rax)
	movb	1546(%rsp), %cl
	movb	%cl, 1154(%rax)
	movb	1547(%rsp), %cl
	movb	%cl, 1155(%rax)
	movb	1548(%rsp), %cl
	movb	%cl, 1156(%rax)
	movb	1549(%rsp), %cl
	movb	%cl, 1157(%rax)
	movb	1550(%rsp), %cl
	movb	%cl, 1158(%rax)
	movb	1551(%rsp), %cl
	movb	%cl, 1159(%rax)
	movb	1552(%rsp), %cl
	movb	%cl, 1160(%rax)
	movb	1553(%rsp), %cl
	movb	%cl, 1161(%rax)
	movb	1554(%rsp), %cl
	movb	%cl, 1162(%rax)
	movb	1555(%rsp), %cl
	movb	%cl, 1163(%rax)
	movb	1556(%rsp), %cl
	movb	%cl, 1164(%rax)
	movb	1557(%rsp), %cl
	movb	%cl, 1165(%rax)
	movb	1558(%rsp), %cl
	movb	%cl, 1166(%rax)
	movb	1559(%rsp), %cl
	movb	%cl, 1167(%rax)
	movb	1560(%rsp), %cl
	movb	%cl, 1168(%rax)
	movb	1561(%rsp), %cl
	movb	%cl, 1169(%rax)
	movb	1562(%rsp), %cl
	movb	%cl, 1170(%rax)
	movb	1563(%rsp), %cl
	movb	%cl, 1171(%rax)
	movb	1564(%rsp), %cl
	movb	%cl, 1172(%rax)
	movb	1565(%rsp), %cl
	movb	%cl, 1173(%rax)
	movb	1566(%rsp), %cl
	movb	%cl, 1174(%rax)
	movb	1567(%rsp), %cl
	movb	%cl, 1175(%rax)
	movb	1568(%rsp), %cl
	movb	%cl, 1176(%rax)
	movb	1569(%rsp), %cl
	movb	%cl, 1177(%rax)
	movb	1570(%rsp), %cl
	movb	%cl, 1178(%rax)
	movb	1571(%rsp), %cl
	movb	%cl, 1179(%rax)
	movb	1572(%rsp), %cl
	movb	%cl, 1180(%rax)
	movb	1573(%rsp), %cl
	movb	%cl, 1181(%rax)
	movb	1574(%rsp), %cl
	movb	%cl, 1182(%rax)
	movb	1575(%rsp), %cl
	movb	%cl, 1183(%rax)
	movb	1576(%rsp), %cl
	movb	%cl, 1184(%rax)
	movb	1577(%rsp), %cl
	movb	%cl, 1185(%rax)
	movb	1578(%rsp), %cl
	movb	%cl, 1186(%rax)
	movb	1579(%rsp), %cl
	movb	%cl, 1187(%rax)
	movb	1580(%rsp), %cl
	movb	%cl, 1188(%rax)
	movb	1581(%rsp), %cl
	movb	%cl, 1189(%rax)
	movb	1582(%rsp), %cl
	movb	%cl, 1190(%rax)
	movb	1583(%rsp), %cl
	movb	%cl, 1191(%rax)
	movb	1584(%rsp), %cl
	movb	%cl, 1192(%rax)
	movb	1585(%rsp), %cl
	movb	%cl, 1193(%rax)
	movb	1586(%rsp), %cl
	movb	%cl, 1194(%rax)
	movb	1587(%rsp), %cl
	movb	%cl, 1195(%rax)
	movb	1588(%rsp), %cl
	movb	%cl, 1196(%rax)
	movb	1589(%rsp), %cl
	movb	%cl, 1197(%rax)
	movb	1590(%rsp), %cl
	movb	%cl, 1198(%rax)
	movb	1591(%rsp), %cl
	movb	%cl, 1199(%rax)
	movb	1592(%rsp), %cl
	movb	%cl, 1200(%rax)
	movb	1593(%rsp), %cl
	movb	%cl, 1201(%rax)
	movb	1594(%rsp), %cl
	movb	%cl, 1202(%rax)
	movb	1595(%rsp), %cl
	movb	%cl, 1203(%rax)
	movb	1596(%rsp), %cl
	movb	%cl, 1204(%rax)
	movb	1597(%rsp), %cl
	movb	%cl, 1205(%rax)
	movb	1598(%rsp), %cl
	movb	%cl, 1206(%rax)
	movb	1599(%rsp), %cl
	movb	%cl, 1207(%rax)
	movb	1600(%rsp), %cl
	movb	%cl, 1208(%rax)
	movb	1601(%rsp), %cl
	movb	%cl, 1209(%rax)
	movb	1602(%rsp), %cl
	movb	%cl, 1210(%rax)
	movb	1603(%rsp), %cl
	movb	%cl, 1211(%rax)
	movb	1604(%rsp), %cl
	movb	%cl, 1212(%rax)
	movb	1605(%rsp), %cl
	movb	%cl, 1213(%rax)
	movb	1606(%rsp), %cl
	movb	%cl, 1214(%rax)
	movb	1607(%rsp), %cl
	movb	%cl, 1215(%rax)
	movb	1608(%rsp), %cl
	movb	%cl, 1216(%rax)
	movb	1609(%rsp), %cl
	movb	%cl, 1217(%rax)
	movb	1610(%rsp), %cl
	movb	%cl, 1218(%rax)
	movb	1611(%rsp), %cl
	movb	%cl, 1219(%rax)
	movb	1612(%rsp), %cl
	movb	%cl, 1220(%rax)
	movb	1613(%rsp), %cl
	movb	%cl, 1221(%rax)
	movb	1614(%rsp), %cl
	movb	%cl, 1222(%rax)
	movb	1615(%rsp), %cl
	movb	%cl, 1223(%rax)
	movb	1616(%rsp), %cl
	movb	%cl, 1224(%rax)
	movb	1617(%rsp), %cl
	movb	%cl, 1225(%rax)
	movb	1618(%rsp), %cl
	movb	%cl, 1226(%rax)
	movb	1619(%rsp), %cl
	movb	%cl, 1227(%rax)
	movb	1620(%rsp), %cl
	movb	%cl, 1228(%rax)
	movb	1621(%rsp), %cl
	movb	%cl, 1229(%rax)
	movb	1622(%rsp), %cl
	movb	%cl, 1230(%rax)
	movb	1623(%rsp), %cl
	movb	%cl, 1231(%rax)
	movb	1624(%rsp), %cl
	movb	%cl, 1232(%rax)
	movb	1625(%rsp), %cl
	movb	%cl, 1233(%rax)
	movb	1626(%rsp), %cl
	movb	%cl, 1234(%rax)
	movb	1627(%rsp), %cl
	movb	%cl, 1235(%rax)
	movb	1628(%rsp), %cl
	movb	%cl, 1236(%rax)
	movb	1629(%rsp), %cl
	movb	%cl, 1237(%rax)
	movb	1630(%rsp), %cl
	movb	%cl, 1238(%rax)
	movb	1631(%rsp), %cl
	movb	%cl, 1239(%rax)
	movb	1632(%rsp), %cl
	movb	%cl, 1240(%rax)
	movb	1633(%rsp), %cl
	movb	%cl, 1241(%rax)
	movb	1634(%rsp), %cl
	movb	%cl, 1242(%rax)
	movb	1635(%rsp), %cl
	movb	%cl, 1243(%rax)
	movb	1636(%rsp), %cl
	movb	%cl, 1244(%rax)
	movb	1637(%rsp), %cl
	movb	%cl, 1245(%rax)
	movb	1638(%rsp), %cl
	movb	%cl, 1246(%rax)
	movb	1639(%rsp), %cl
	movb	%cl, 1247(%rax)
	movb	1640(%rsp), %cl
	movb	%cl, 1248(%rax)
	movb	1641(%rsp), %cl
	movb	%cl, 1249(%rax)
	movb	1642(%rsp), %cl
	movb	%cl, 1250(%rax)
	movb	1643(%rsp), %cl
	movb	%cl, 1251(%rax)
	movb	1644(%rsp), %cl
	movb	%cl, 1252(%rax)
	movb	1645(%rsp), %cl
	movb	%cl, 1253(%rax)
	movb	1646(%rsp), %cl
	movb	%cl, 1254(%rax)
	movb	1647(%rsp), %cl
	movb	%cl, 1255(%rax)
	movb	1648(%rsp), %cl
	movb	%cl, 1256(%rax)
	movb	1649(%rsp), %cl
	movb	%cl, 1257(%rax)
	movb	1650(%rsp), %cl
	movb	%cl, 1258(%rax)
	movb	1651(%rsp), %cl
	movb	%cl, 1259(%rax)
	movb	1652(%rsp), %cl
	movb	%cl, 1260(%rax)
	movb	1653(%rsp), %cl
	movb	%cl, 1261(%rax)
	movb	1654(%rsp), %cl
	movb	%cl, 1262(%rax)
	movb	1655(%rsp), %cl
	movb	%cl, 1263(%rax)
	movb	1656(%rsp), %cl
	movb	%cl, 1264(%rax)
	movb	1657(%rsp), %cl
	movb	%cl, 1265(%rax)
	movb	1658(%rsp), %cl
	movb	%cl, 1266(%rax)
	movb	1659(%rsp), %cl
	movb	%cl, 1267(%rax)
	movb	1660(%rsp), %cl
	movb	%cl, 1268(%rax)
	movb	1661(%rsp), %cl
	movb	%cl, 1269(%rax)
	movb	1662(%rsp), %cl
	movb	%cl, 1270(%rax)
	movb	1663(%rsp), %cl
	movb	%cl, 1271(%rax)
	movb	1664(%rsp), %cl
	movb	%cl, 1272(%rax)
	movb	1665(%rsp), %cl
	movb	%cl, 1273(%rax)
	movb	1666(%rsp), %cl
	movb	%cl, 1274(%rax)
	movb	1667(%rsp), %cl
	movb	%cl, 1275(%rax)
	movb	1668(%rsp), %cl
	movb	%cl, 1276(%rax)
	movb	1669(%rsp), %cl
	movb	%cl, 1277(%rax)
	movb	1670(%rsp), %cl
	movb	%cl, 1278(%rax)
	movb	1671(%rsp), %cl
	movb	%cl, 1279(%rax)
	movb	1672(%rsp), %cl
	movb	%cl, 1280(%rax)
	movb	1673(%rsp), %cl
	movb	%cl, 1281(%rax)
	movb	1674(%rsp), %cl
	movb	%cl, 1282(%rax)
	movb	1675(%rsp), %cl
	movb	%cl, 1283(%rax)
	movb	1676(%rsp), %cl
	movb	%cl, 1284(%rax)
	movb	1677(%rsp), %cl
	movb	%cl, 1285(%rax)
	movb	1678(%rsp), %cl
	movb	%cl, 1286(%rax)
	movb	1679(%rsp), %cl
	movb	%cl, 1287(%rax)
	movb	1680(%rsp), %cl
	movb	%cl, 1288(%rax)
	movb	1681(%rsp), %cl
	movb	%cl, 1289(%rax)
	movb	1682(%rsp), %cl
	movb	%cl, 1290(%rax)
	movb	1683(%rsp), %cl
	movb	%cl, 1291(%rax)
	movb	1684(%rsp), %cl
	movb	%cl, 1292(%rax)
	movb	1685(%rsp), %cl
	movb	%cl, 1293(%rax)
	movb	1686(%rsp), %cl
	movb	%cl, 1294(%rax)
	movb	1687(%rsp), %cl
	movb	%cl, 1295(%rax)
	movb	1688(%rsp), %cl
	movb	%cl, 1296(%rax)
	movb	1689(%rsp), %cl
	movb	%cl, 1297(%rax)
	movb	1690(%rsp), %cl
	movb	%cl, 1298(%rax)
	movb	1691(%rsp), %cl
	movb	%cl, 1299(%rax)
	movb	1692(%rsp), %cl
	movb	%cl, 1300(%rax)
	movb	1693(%rsp), %cl
	movb	%cl, 1301(%rax)
	movb	1694(%rsp), %cl
	movb	%cl, 1302(%rax)
	movb	1695(%rsp), %cl
	movb	%cl, 1303(%rax)
	movb	1696(%rsp), %cl
	movb	%cl, 1304(%rax)
	movb	1697(%rsp), %cl
	movb	%cl, 1305(%rax)
	movb	1698(%rsp), %cl
	movb	%cl, 1306(%rax)
	movb	1699(%rsp), %cl
	movb	%cl, 1307(%rax)
	movb	1700(%rsp), %cl
	movb	%cl, 1308(%rax)
	movb	1701(%rsp), %cl
	movb	%cl, 1309(%rax)
	movb	1702(%rsp), %cl
	movb	%cl, 1310(%rax)
	movb	1703(%rsp), %cl
	movb	%cl, 1311(%rax)
	movb	1704(%rsp), %cl
	movb	%cl, 1312(%rax)
	movb	1705(%rsp), %cl
	movb	%cl, 1313(%rax)
	movb	1706(%rsp), %cl
	movb	%cl, 1314(%rax)
	movb	1707(%rsp), %cl
	movb	%cl, 1315(%rax)
	movb	1708(%rsp), %cl
	movb	%cl, 1316(%rax)
	movb	1709(%rsp), %cl
	movb	%cl, 1317(%rax)
	movb	1710(%rsp), %cl
	movb	%cl, 1318(%rax)
	movb	1711(%rsp), %cl
	movb	%cl, 1319(%rax)
	movb	1712(%rsp), %cl
	movb	%cl, 1320(%rax)
	movb	1713(%rsp), %cl
	movb	%cl, 1321(%rax)
	movb	1714(%rsp), %cl
	movb	%cl, 1322(%rax)
	movb	1715(%rsp), %cl
	movb	%cl, 1323(%rax)
	movb	1716(%rsp), %cl
	movb	%cl, 1324(%rax)
	movb	1717(%rsp), %cl
	movb	%cl, 1325(%rax)
	movb	1718(%rsp), %cl
	movb	%cl, 1326(%rax)
	movb	1719(%rsp), %cl
	movb	%cl, 1327(%rax)
	movb	1720(%rsp), %cl
	movb	%cl, 1328(%rax)
	movb	1721(%rsp), %cl
	movb	%cl, 1329(%rax)
	movb	1722(%rsp), %cl
	movb	%cl, 1330(%rax)
	movb	1723(%rsp), %cl
	movb	%cl, 1331(%rax)
	movb	1724(%rsp), %cl
	movb	%cl, 1332(%rax)
	movb	1725(%rsp), %cl
	movb	%cl, 1333(%rax)
	movb	1726(%rsp), %cl
	movb	%cl, 1334(%rax)
	movb	1727(%rsp), %cl
	movb	%cl, 1335(%rax)
	movb	1728(%rsp), %cl
	movb	%cl, 1336(%rax)
	movb	1729(%rsp), %cl
	movb	%cl, 1337(%rax)
	movb	1730(%rsp), %cl
	movb	%cl, 1338(%rax)
	movb	1731(%rsp), %cl
	movb	%cl, 1339(%rax)
	movb	1732(%rsp), %cl
	movb	%cl, 1340(%rax)
	movb	1733(%rsp), %cl
	movb	%cl, 1341(%rax)
	movb	1734(%rsp), %cl
	movb	%cl, 1342(%rax)
	movb	1735(%rsp), %cl
	movb	%cl, 1343(%rax)
	movb	1736(%rsp), %cl
	movb	%cl, 1344(%rax)
	movb	1737(%rsp), %cl
	movb	%cl, 1345(%rax)
	movb	1738(%rsp), %cl
	movb	%cl, 1346(%rax)
	movb	1739(%rsp), %cl
	movb	%cl, 1347(%rax)
	movb	1740(%rsp), %cl
	movb	%cl, 1348(%rax)
	movb	1741(%rsp), %cl
	movb	%cl, 1349(%rax)
	movb	1742(%rsp), %cl
	movb	%cl, 1350(%rax)
	movb	1743(%rsp), %cl
	movb	%cl, 1351(%rax)
	movb	1744(%rsp), %cl
	movb	%cl, 1352(%rax)
	movb	1745(%rsp), %cl
	movb	%cl, 1353(%rax)
	movb	1746(%rsp), %cl
	movb	%cl, 1354(%rax)
	movb	1747(%rsp), %cl
	movb	%cl, 1355(%rax)
	movb	1748(%rsp), %cl
	movb	%cl, 1356(%rax)
	movb	1749(%rsp), %cl
	movb	%cl, 1357(%rax)
	movb	1750(%rsp), %cl
	movb	%cl, 1358(%rax)
	movb	1751(%rsp), %cl
	movb	%cl, 1359(%rax)
	movb	1752(%rsp), %cl
	movb	%cl, 1360(%rax)
	movb	1753(%rsp), %cl
	movb	%cl, 1361(%rax)
	movb	1754(%rsp), %cl
	movb	%cl, 1362(%rax)
	movb	1755(%rsp), %cl
	movb	%cl, 1363(%rax)
	movb	1756(%rsp), %cl
	movb	%cl, 1364(%rax)
	movb	1757(%rsp), %cl
	movb	%cl, 1365(%rax)
	movb	1758(%rsp), %cl
	movb	%cl, 1366(%rax)
	movb	1759(%rsp), %cl
	movb	%cl, 1367(%rax)
	movb	1760(%rsp), %cl
	movb	%cl, 1368(%rax)
	movb	1761(%rsp), %cl
	movb	%cl, 1369(%rax)
	movb	1762(%rsp), %cl
	movb	%cl, 1370(%rax)
	movb	1763(%rsp), %cl
	movb	%cl, 1371(%rax)
	movb	1764(%rsp), %cl
	movb	%cl, 1372(%rax)
	movb	1765(%rsp), %cl
	movb	%cl, 1373(%rax)
	movb	1766(%rsp), %cl
	movb	%cl, 1374(%rax)
	movb	1767(%rsp), %cl
	movb	%cl, 1375(%rax)
	movb	1768(%rsp), %cl
	movb	%cl, 1376(%rax)
	movb	1769(%rsp), %cl
	movb	%cl, 1377(%rax)
	movb	1770(%rsp), %cl
	movb	%cl, 1378(%rax)
	movb	1771(%rsp), %cl
	movb	%cl, 1379(%rax)
	movb	1772(%rsp), %cl
	movb	%cl, 1380(%rax)
	movb	1773(%rsp), %cl
	movb	%cl, 1381(%rax)
	movb	1774(%rsp), %cl
	movb	%cl, 1382(%rax)
	movb	1775(%rsp), %cl
	movb	%cl, 1383(%rax)
	movb	1776(%rsp), %cl
	movb	%cl, 1384(%rax)
	movb	1777(%rsp), %cl
	movb	%cl, 1385(%rax)
	movb	1778(%rsp), %cl
	movb	%cl, 1386(%rax)
	movb	1779(%rsp), %cl
	movb	%cl, 1387(%rax)
	movb	1780(%rsp), %cl
	movb	%cl, 1388(%rax)
	movb	1781(%rsp), %cl
	movb	%cl, 1389(%rax)
	movb	1782(%rsp), %cl
	movb	%cl, 1390(%rax)
	movb	1783(%rsp), %cl
	movb	%cl, 1391(%rax)
	movb	1784(%rsp), %cl
	movb	%cl, 1392(%rax)
	movb	1785(%rsp), %cl
	movb	%cl, 1393(%rax)
	movb	1786(%rsp), %cl
	movb	%cl, 1394(%rax)
	movb	1787(%rsp), %cl
	movb	%cl, 1395(%rax)
	movb	1788(%rsp), %cl
	movb	%cl, 1396(%rax)
	movb	1789(%rsp), %cl
	movb	%cl, 1397(%rax)
	movb	1790(%rsp), %cl
	movb	%cl, 1398(%rax)
	movb	1791(%rsp), %cl
	movb	%cl, 1399(%rax)
	movb	1792(%rsp), %cl
	movb	%cl, 1400(%rax)
	movb	1793(%rsp), %cl
	movb	%cl, 1401(%rax)
	movb	1794(%rsp), %cl
	movb	%cl, 1402(%rax)
	movb	1795(%rsp), %cl
	movb	%cl, 1403(%rax)
	movb	1796(%rsp), %cl
	movb	%cl, 1404(%rax)
	movb	1797(%rsp), %cl
	movb	%cl, 1405(%rax)
	movb	1798(%rsp), %cl
	movb	%cl, 1406(%rax)
	movb	1799(%rsp), %cl
	movb	%cl, 1407(%rax)
	movb	1800(%rsp), %cl
	movb	%cl, 1408(%rax)
	movb	1801(%rsp), %cl
	movb	%cl, 1409(%rax)
	movb	1802(%rsp), %cl
	movb	%cl, 1410(%rax)
	movb	1803(%rsp), %cl
	movb	%cl, 1411(%rax)
	movb	1804(%rsp), %cl
	movb	%cl, 1412(%rax)
	movb	1805(%rsp), %cl
	movb	%cl, 1413(%rax)
	movb	1806(%rsp), %cl
	movb	%cl, 1414(%rax)
	movb	1807(%rsp), %cl
	movb	%cl, 1415(%rax)
	movb	1808(%rsp), %cl
	movb	%cl, 1416(%rax)
	movb	1809(%rsp), %cl
	movb	%cl, 1417(%rax)
	movb	1810(%rsp), %cl
	movb	%cl, 1418(%rax)
	movb	1811(%rsp), %cl
	movb	%cl, 1419(%rax)
	movb	1812(%rsp), %cl
	movb	%cl, 1420(%rax)
	movb	1813(%rsp), %cl
	movb	%cl, 1421(%rax)
	movb	1814(%rsp), %cl
	movb	%cl, 1422(%rax)
	movb	1815(%rsp), %cl
	movb	%cl, 1423(%rax)
	movb	1816(%rsp), %cl
	movb	%cl, 1424(%rax)
	movb	1817(%rsp), %cl
	movb	%cl, 1425(%rax)
	movb	1818(%rsp), %cl
	movb	%cl, 1426(%rax)
	movb	1819(%rsp), %cl
	movb	%cl, 1427(%rax)
	movb	1820(%rsp), %cl
	movb	%cl, 1428(%rax)
	movb	1821(%rsp), %cl
	movb	%cl, 1429(%rax)
	movb	1822(%rsp), %cl
	movb	%cl, 1430(%rax)
	movb	1823(%rsp), %cl
	movb	%cl, 1431(%rax)
	movb	1824(%rsp), %cl
	movb	%cl, 1432(%rax)
	movb	1825(%rsp), %cl
	movb	%cl, 1433(%rax)
	movb	1826(%rsp), %cl
	movb	%cl, 1434(%rax)
	movb	1827(%rsp), %cl
	movb	%cl, 1435(%rax)
	movb	1828(%rsp), %cl
	movb	%cl, 1436(%rax)
	movb	1829(%rsp), %cl
	movb	%cl, 1437(%rax)
	movb	1830(%rsp), %cl
	movb	%cl, 1438(%rax)
	movb	1831(%rsp), %cl
	movb	%cl, 1439(%rax)
	movb	1832(%rsp), %cl
	movb	%cl, 1440(%rax)
	movb	1833(%rsp), %cl
	movb	%cl, 1441(%rax)
	movb	1834(%rsp), %cl
	movb	%cl, 1442(%rax)
	movb	1835(%rsp), %cl
	movb	%cl, 1443(%rax)
	movb	1836(%rsp), %cl
	movb	%cl, 1444(%rax)
	movb	1837(%rsp), %cl
	movb	%cl, 1445(%rax)
	movb	1838(%rsp), %cl
	movb	%cl, 1446(%rax)
	movb	1839(%rsp), %cl
	movb	%cl, 1447(%rax)
	movb	1840(%rsp), %cl
	movb	%cl, 1448(%rax)
	movb	1841(%rsp), %cl
	movb	%cl, 1449(%rax)
	movb	1842(%rsp), %cl
	movb	%cl, 1450(%rax)
	movb	1843(%rsp), %cl
	movb	%cl, 1451(%rax)
	movb	1844(%rsp), %cl
	movb	%cl, 1452(%rax)
	movb	1845(%rsp), %cl
	movb	%cl, 1453(%rax)
	movb	1846(%rsp), %cl
	movb	%cl, 1454(%rax)
	movb	1847(%rsp), %cl
	movb	%cl, 1455(%rax)
	movb	1848(%rsp), %cl
	movb	%cl, 1456(%rax)
	movb	1849(%rsp), %cl
	movb	%cl, 1457(%rax)
	movb	1850(%rsp), %cl
	movb	%cl, 1458(%rax)
	movb	1851(%rsp), %cl
	movb	%cl, 1459(%rax)
	movb	1852(%rsp), %cl
	movb	%cl, 1460(%rax)
	movb	1853(%rsp), %cl
	movb	%cl, 1461(%rax)
	movb	1854(%rsp), %cl
	movb	%cl, 1462(%rax)
	movb	1855(%rsp), %cl
	movb	%cl, 1463(%rax)
	movb	1856(%rsp), %cl
	movb	%cl, 1464(%rax)
	movb	1857(%rsp), %cl
	movb	%cl, 1465(%rax)
	movb	1858(%rsp), %cl
	movb	%cl, 1466(%rax)
	movb	1859(%rsp), %cl
	movb	%cl, 1467(%rax)
	movb	1860(%rsp), %cl
	movb	%cl, 1468(%rax)
	movb	1861(%rsp), %cl
	movb	%cl, 1469(%rax)
	movb	1862(%rsp), %cl
	movb	%cl, 1470(%rax)
	movb	1863(%rsp), %cl
	movb	%cl, 1471(%rax)
	movb	1864(%rsp), %cl
	movb	%cl, 1472(%rax)
	movb	1865(%rsp), %cl
	movb	%cl, 1473(%rax)
	movb	1866(%rsp), %cl
	movb	%cl, 1474(%rax)
	movb	1867(%rsp), %cl
	movb	%cl, 1475(%rax)
	movb	1868(%rsp), %cl
	movb	%cl, 1476(%rax)
	movb	1869(%rsp), %cl
	movb	%cl, 1477(%rax)
	movb	1870(%rsp), %cl
	movb	%cl, 1478(%rax)
	movb	1871(%rsp), %cl
	movb	%cl, 1479(%rax)
	movb	1872(%rsp), %cl
	movb	%cl, 1480(%rax)
	movb	1873(%rsp), %cl
	movb	%cl, 1481(%rax)
	movb	1874(%rsp), %cl
	movb	%cl, 1482(%rax)
	movb	1875(%rsp), %cl
	movb	%cl, 1483(%rax)
	movb	1876(%rsp), %cl
	movb	%cl, 1484(%rax)
	movb	1877(%rsp), %cl
	movb	%cl, 1485(%rax)
	movb	1878(%rsp), %cl
	movb	%cl, 1486(%rax)
	movb	1879(%rsp), %cl
	movb	%cl, 1487(%rax)
	movb	1880(%rsp), %cl
	movb	%cl, 1488(%rax)
	movb	1881(%rsp), %cl
	movb	%cl, 1489(%rax)
	movb	1882(%rsp), %cl
	movb	%cl, 1490(%rax)
	movb	1883(%rsp), %cl
	movb	%cl, 1491(%rax)
	movb	1884(%rsp), %cl
	movb	%cl, 1492(%rax)
	movb	1885(%rsp), %cl
	movb	%cl, 1493(%rax)
	movb	1886(%rsp), %cl
	movb	%cl, 1494(%rax)
	movb	1887(%rsp), %cl
	movb	%cl, 1495(%rax)
	movb	1888(%rsp), %cl
	movb	%cl, 1496(%rax)
	movb	1889(%rsp), %cl
	movb	%cl, 1497(%rax)
	movb	1890(%rsp), %cl
	movb	%cl, 1498(%rax)
	movb	1891(%rsp), %cl
	movb	%cl, 1499(%rax)
	movb	1892(%rsp), %cl
	movb	%cl, 1500(%rax)
	movb	1893(%rsp), %cl
	movb	%cl, 1501(%rax)
	movb	1894(%rsp), %cl
	movb	%cl, 1502(%rax)
	movb	1895(%rsp), %cl
	movb	%cl, 1503(%rax)
	movb	1896(%rsp), %cl
	movb	%cl, 1504(%rax)
	movb	1897(%rsp), %cl
	movb	%cl, 1505(%rax)
	movb	1898(%rsp), %cl
	movb	%cl, 1506(%rax)
	movb	1899(%rsp), %cl
	movb	%cl, 1507(%rax)
	movb	1900(%rsp), %cl
	movb	%cl, 1508(%rax)
	movb	1901(%rsp), %cl
	movb	%cl, 1509(%rax)
	movb	1902(%rsp), %cl
	movb	%cl, 1510(%rax)
	movb	1903(%rsp), %cl
	movb	%cl, 1511(%rax)
	movb	1904(%rsp), %cl
	movb	%cl, 1512(%rax)
	movb	1905(%rsp), %cl
	movb	%cl, 1513(%rax)
	movb	1906(%rsp), %cl
	movb	%cl, 1514(%rax)
	movb	1907(%rsp), %cl
	movb	%cl, 1515(%rax)
	movb	1908(%rsp), %cl
	movb	%cl, 1516(%rax)
	movb	1909(%rsp), %cl
	movb	%cl, 1517(%rax)
	movb	1910(%rsp), %cl
	movb	%cl, 1518(%rax)
	movb	1911(%rsp), %cl
	movb	%cl, 1519(%rax)
	movb	1912(%rsp), %cl
	movb	%cl, 1520(%rax)
	movb	1913(%rsp), %cl
	movb	%cl, 1521(%rax)
	movb	1914(%rsp), %cl
	movb	%cl, 1522(%rax)
	movb	1915(%rsp), %cl
	movb	%cl, 1523(%rax)
	movb	1916(%rsp), %cl
	movb	%cl, 1524(%rax)
	movb	1917(%rsp), %cl
	movb	%cl, 1525(%rax)
	movb	1918(%rsp), %cl
	movb	%cl, 1526(%rax)
	movb	1919(%rsp), %cl
	movb	%cl, 1527(%rax)
	movb	1920(%rsp), %cl
	movb	%cl, 1528(%rax)
	movb	1921(%rsp), %cl
	movb	%cl, 1529(%rax)
	movb	1922(%rsp), %cl
	movb	%cl, 1530(%rax)
	movb	1923(%rsp), %cl
	movb	%cl, 1531(%rax)
	movb	1924(%rsp), %cl
	movb	%cl, 1532(%rax)
	movb	1925(%rsp), %cl
	movb	%cl, 1533(%rax)
	movb	1926(%rsp), %cl
	movb	%cl, 1534(%rax)
	movb	1927(%rsp), %cl
	movb	%cl, 1535(%rax)
	movb	1928(%rsp), %cl
	movb	%cl, 1536(%rax)
	movb	1929(%rsp), %cl
	movb	%cl, 1537(%rax)
	movb	1930(%rsp), %cl
	movb	%cl, 1538(%rax)
	movb	1931(%rsp), %cl
	movb	%cl, 1539(%rax)
	movb	1932(%rsp), %cl
	movb	%cl, 1540(%rax)
	movb	1933(%rsp), %cl
	movb	%cl, 1541(%rax)
	movb	1934(%rsp), %cl
	movb	%cl, 1542(%rax)
	movb	1935(%rsp), %cl
	movb	%cl, 1543(%rax)
	movb	1936(%rsp), %cl
	movb	%cl, 1544(%rax)
	movb	1937(%rsp), %cl
	movb	%cl, 1545(%rax)
	movb	1938(%rsp), %cl
	movb	%cl, 1546(%rax)
	movb	1939(%rsp), %cl
	movb	%cl, 1547(%rax)
	movb	1940(%rsp), %cl
	movb	%cl, 1548(%rax)
	movb	1941(%rsp), %cl
	movb	%cl, 1549(%rax)
	movb	1942(%rsp), %cl
	movb	%cl, 1550(%rax)
	movb	1943(%rsp), %cl
	movb	%cl, 1551(%rax)
	movb	1944(%rsp), %cl
	movb	%cl, 1552(%rax)
	movb	1945(%rsp), %cl
	movb	%cl, 1553(%rax)
	movb	1946(%rsp), %cl
	movb	%cl, 1554(%rax)
	movb	1947(%rsp), %cl
	movb	%cl, 1555(%rax)
	movb	1948(%rsp), %cl
	movb	%cl, 1556(%rax)
	movb	1949(%rsp), %cl
	movb	%cl, 1557(%rax)
	movb	1950(%rsp), %cl
	movb	%cl, 1558(%rax)
	movb	1951(%rsp), %cl
	movb	%cl, 1559(%rax)
	movb	1952(%rsp), %cl
	movb	%cl, 1560(%rax)
	movb	1953(%rsp), %cl
	movb	%cl, 1561(%rax)
	movb	1954(%rsp), %cl
	movb	%cl, 1562(%rax)
	movb	1955(%rsp), %cl
	movb	%cl, 1563(%rax)
	movb	1956(%rsp), %cl
	movb	%cl, 1564(%rax)
	movb	1957(%rsp), %cl
	movb	%cl, 1565(%rax)
	movb	1958(%rsp), %cl
	movb	%cl, 1566(%rax)
	movb	1959(%rsp), %cl
	movb	%cl, 1567(%rax)
	movb	1960(%rsp), %cl
	movb	%cl, 1568(%rax)
	movb	1961(%rsp), %cl
	movb	%cl, 1569(%rax)
	movb	1962(%rsp), %cl
	movb	%cl, 1570(%rax)
	movb	1963(%rsp), %cl
	movb	%cl, 1571(%rax)
	movb	1964(%rsp), %cl
	movb	%cl, 1572(%rax)
	movb	1965(%rsp), %cl
	movb	%cl, 1573(%rax)
	movb	1966(%rsp), %cl
	movb	%cl, 1574(%rax)
	movb	1967(%rsp), %cl
	movb	%cl, 1575(%rax)
	movb	1968(%rsp), %cl
	movb	%cl, 1576(%rax)
	movb	1969(%rsp), %cl
	movb	%cl, 1577(%rax)
	movb	1970(%rsp), %cl
	movb	%cl, 1578(%rax)
	movb	1971(%rsp), %cl
	movb	%cl, 1579(%rax)
	movb	1972(%rsp), %cl
	movb	%cl, 1580(%rax)
	movb	1973(%rsp), %cl
	movb	%cl, 1581(%rax)
	movb	1974(%rsp), %cl
	movb	%cl, 1582(%rax)
	movb	1975(%rsp), %cl
	movb	%cl, 1583(%rax)
	movb	1976(%rsp), %cl
	movb	%cl, 1584(%rax)
	movb	1977(%rsp), %cl
	movb	%cl, 1585(%rax)
	movb	1978(%rsp), %cl
	movb	%cl, 1586(%rax)
	movb	1979(%rsp), %cl
	movb	%cl, 1587(%rax)
	movb	1980(%rsp), %cl
	movb	%cl, 1588(%rax)
	movb	1981(%rsp), %cl
	movb	%cl, 1589(%rax)
	movb	1982(%rsp), %cl
	movb	%cl, 1590(%rax)
	movb	1983(%rsp), %cl
	movb	%cl, 1591(%rax)
	movb	1984(%rsp), %cl
	movb	%cl, 1592(%rax)
	movb	1985(%rsp), %cl
	movb	%cl, 1593(%rax)
	movb	1986(%rsp), %cl
	movb	%cl, 1594(%rax)
	movb	1987(%rsp), %cl
	movb	%cl, 1595(%rax)
	movb	1988(%rsp), %cl
	movb	%cl, 1596(%rax)
	movb	1989(%rsp), %cl
	movb	%cl, 1597(%rax)
	movb	1990(%rsp), %cl
	movb	%cl, 1598(%rax)
	movb	1991(%rsp), %cl
	movb	%cl, 1599(%rax)
	movb	1992(%rsp), %cl
	movb	%cl, 1600(%rax)
	movb	1993(%rsp), %cl
	movb	%cl, 1601(%rax)
	movb	1994(%rsp), %cl
	movb	%cl, 1602(%rax)
	movb	1995(%rsp), %cl
	movb	%cl, 1603(%rax)
	movb	1996(%rsp), %cl
	movb	%cl, 1604(%rax)
	movb	1997(%rsp), %cl
	movb	%cl, 1605(%rax)
	movb	1998(%rsp), %cl
	movb	%cl, 1606(%rax)
	movb	1999(%rsp), %cl
	movb	%cl, 1607(%rax)
	movb	2000(%rsp), %cl
	movb	%cl, 1608(%rax)
	movb	2001(%rsp), %cl
	movb	%cl, 1609(%rax)
	movb	2002(%rsp), %cl
	movb	%cl, 1610(%rax)
	movb	2003(%rsp), %cl
	movb	%cl, 1611(%rax)
	movb	2004(%rsp), %cl
	movb	%cl, 1612(%rax)
	movb	2005(%rsp), %cl
	movb	%cl, 1613(%rax)
	movb	2006(%rsp), %cl
	movb	%cl, 1614(%rax)
	movb	2007(%rsp), %cl
	movb	%cl, 1615(%rax)
	movb	2008(%rsp), %cl
	movb	%cl, 1616(%rax)
	movb	2009(%rsp), %cl
	movb	%cl, 1617(%rax)
	movb	2010(%rsp), %cl
	movb	%cl, 1618(%rax)
	movb	2011(%rsp), %cl
	movb	%cl, 1619(%rax)
	movb	2012(%rsp), %cl
	movb	%cl, 1620(%rax)
	movb	2013(%rsp), %cl
	movb	%cl, 1621(%rax)
	movb	2014(%rsp), %cl
	movb	%cl, 1622(%rax)
	movb	2015(%rsp), %cl
	movb	%cl, 1623(%rax)
	movb	2016(%rsp), %cl
	movb	%cl, 1624(%rax)
	movb	2017(%rsp), %cl
	movb	%cl, 1625(%rax)
	movb	2018(%rsp), %cl
	movb	%cl, 1626(%rax)
	movb	2019(%rsp), %cl
	movb	%cl, 1627(%rax)
	movb	2020(%rsp), %cl
	movb	%cl, 1628(%rax)
	movb	2021(%rsp), %cl
	movb	%cl, 1629(%rax)
	movb	2022(%rsp), %cl
	movb	%cl, 1630(%rax)
	movb	2023(%rsp), %cl
	movb	%cl, 1631(%rax)
	movb	2024(%rsp), %cl
	movb	%cl, 1632(%rax)
	movb	2025(%rsp), %cl
	movb	%cl, 1633(%rax)
	movb	2026(%rsp), %cl
	movb	%cl, 1634(%rax)
	movb	2027(%rsp), %cl
	movb	%cl, 1635(%rax)
	movb	2028(%rsp), %cl
	movb	%cl, 1636(%rax)
	movb	2029(%rsp), %cl
	movb	%cl, 1637(%rax)
	movb	2030(%rsp), %cl
	movb	%cl, 1638(%rax)
	movb	2031(%rsp), %cl
	movb	%cl, 1639(%rax)
	movb	2032(%rsp), %cl
	movb	%cl, 1640(%rax)
	movb	2033(%rsp), %cl
	movb	%cl, 1641(%rax)
	movb	2034(%rsp), %cl
	movb	%cl, 1642(%rax)
	movb	2035(%rsp), %cl
	movb	%cl, 1643(%rax)
	movb	2036(%rsp), %cl
	movb	%cl, 1644(%rax)
	movb	2037(%rsp), %cl
	movb	%cl, 1645(%rax)
	movb	2038(%rsp), %cl
	movb	%cl, 1646(%rax)
	movb	2039(%rsp), %cl
	movb	%cl, 1647(%rax)
	movb	2040(%rsp), %cl
	movb	%cl, 1648(%rax)
	movb	2041(%rsp), %cl
	movb	%cl, 1649(%rax)
	movb	2042(%rsp), %cl
	movb	%cl, 1650(%rax)
	movb	2043(%rsp), %cl
	movb	%cl, 1651(%rax)
	movb	2044(%rsp), %cl
	movb	%cl, 1652(%rax)
	movb	2045(%rsp), %cl
	movb	%cl, 1653(%rax)
	movb	2046(%rsp), %cl
	movb	%cl, 1654(%rax)
	movb	2047(%rsp), %cl
	movb	%cl, 1655(%rax)
	movb	2048(%rsp), %cl
	movb	%cl, 1656(%rax)
	movb	2049(%rsp), %cl
	movb	%cl, 1657(%rax)
	movb	2050(%rsp), %cl
	movb	%cl, 1658(%rax)
	movb	2051(%rsp), %cl
	movb	%cl, 1659(%rax)
	movb	2052(%rsp), %cl
	movb	%cl, 1660(%rax)
	movb	2053(%rsp), %cl
	movb	%cl, 1661(%rax)
	movb	2054(%rsp), %cl
	movb	%cl, 1662(%rax)
	movb	2055(%rsp), %cl
	movb	%cl, 1663(%rax)
	movb	2056(%rsp), %cl
	movb	%cl, 1664(%rax)
	movb	2057(%rsp), %cl
	movb	%cl, 1665(%rax)
	movb	2058(%rsp), %cl
	movb	%cl, 1666(%rax)
	movb	2059(%rsp), %cl
	movb	%cl, 1667(%rax)
	movb	2060(%rsp), %cl
	movb	%cl, 1668(%rax)
	movb	2061(%rsp), %cl
	movb	%cl, 1669(%rax)
	movb	2062(%rsp), %cl
	movb	%cl, 1670(%rax)
	movb	2063(%rsp), %cl
	movb	%cl, 1671(%rax)
	movb	2064(%rsp), %cl
	movb	%cl, 1672(%rax)
	movb	2065(%rsp), %cl
	movb	%cl, 1673(%rax)
	movb	2066(%rsp), %cl
	movb	%cl, 1674(%rax)
	movb	2067(%rsp), %cl
	movb	%cl, 1675(%rax)
	movb	2068(%rsp), %cl
	movb	%cl, 1676(%rax)
	movb	2069(%rsp), %cl
	movb	%cl, 1677(%rax)
	movb	2070(%rsp), %cl
	movb	%cl, 1678(%rax)
	movb	2071(%rsp), %cl
	movb	%cl, 1679(%rax)
	movb	2072(%rsp), %cl
	movb	%cl, 1680(%rax)
	movb	2073(%rsp), %cl
	movb	%cl, 1681(%rax)
	movb	2074(%rsp), %cl
	movb	%cl, 1682(%rax)
	movb	2075(%rsp), %cl
	movb	%cl, 1683(%rax)
	movb	2076(%rsp), %cl
	movb	%cl, 1684(%rax)
	movb	2077(%rsp), %cl
	movb	%cl, 1685(%rax)
	movb	2078(%rsp), %cl
	movb	%cl, 1686(%rax)
	movb	2079(%rsp), %cl
	movb	%cl, 1687(%rax)
	movb	2080(%rsp), %cl
	movb	%cl, 1688(%rax)
	movb	2081(%rsp), %cl
	movb	%cl, 1689(%rax)
	movb	2082(%rsp), %cl
	movb	%cl, 1690(%rax)
	movb	2083(%rsp), %cl
	movb	%cl, 1691(%rax)
	movb	2084(%rsp), %cl
	movb	%cl, 1692(%rax)
	movb	2085(%rsp), %cl
	movb	%cl, 1693(%rax)
	movb	2086(%rsp), %cl
	movb	%cl, 1694(%rax)
	movb	2087(%rsp), %cl
	movb	%cl, 1695(%rax)
	movb	2088(%rsp), %cl
	movb	%cl, 1696(%rax)
	movb	2089(%rsp), %cl
	movb	%cl, 1697(%rax)
	movb	2090(%rsp), %cl
	movb	%cl, 1698(%rax)
	movb	2091(%rsp), %cl
	movb	%cl, 1699(%rax)
	movb	2092(%rsp), %cl
	movb	%cl, 1700(%rax)
	movb	2093(%rsp), %cl
	movb	%cl, 1701(%rax)
	movb	2094(%rsp), %cl
	movb	%cl, 1702(%rax)
	movb	2095(%rsp), %cl
	movb	%cl, 1703(%rax)
	movb	2096(%rsp), %cl
	movb	%cl, 1704(%rax)
	movb	2097(%rsp), %cl
	movb	%cl, 1705(%rax)
	movb	2098(%rsp), %cl
	movb	%cl, 1706(%rax)
	movb	2099(%rsp), %cl
	movb	%cl, 1707(%rax)
	movb	2100(%rsp), %cl
	movb	%cl, 1708(%rax)
	movb	2101(%rsp), %cl
	movb	%cl, 1709(%rax)
	movb	2102(%rsp), %cl
	movb	%cl, 1710(%rax)
	movb	2103(%rsp), %cl
	movb	%cl, 1711(%rax)
	movb	2104(%rsp), %cl
	movb	%cl, 1712(%rax)
	movb	2105(%rsp), %cl
	movb	%cl, 1713(%rax)
	movb	2106(%rsp), %cl
	movb	%cl, 1714(%rax)
	movb	2107(%rsp), %cl
	movb	%cl, 1715(%rax)
	movb	2108(%rsp), %cl
	movb	%cl, 1716(%rax)
	movb	2109(%rsp), %cl
	movb	%cl, 1717(%rax)
	movb	2110(%rsp), %cl
	movb	%cl, 1718(%rax)
	movb	2111(%rsp), %cl
	movb	%cl, 1719(%rax)
	movb	2112(%rsp), %cl
	movb	%cl, 1720(%rax)
	movb	2113(%rsp), %cl
	movb	%cl, 1721(%rax)
	movb	2114(%rsp), %cl
	movb	%cl, 1722(%rax)
	movb	2115(%rsp), %cl
	movb	%cl, 1723(%rax)
	movb	2116(%rsp), %cl
	movb	%cl, 1724(%rax)
	movb	2117(%rsp), %cl
	movb	%cl, 1725(%rax)
	movb	2118(%rsp), %cl
	movb	%cl, 1726(%rax)
	movb	2119(%rsp), %cl
	movb	%cl, 1727(%rax)
	movb	2120(%rsp), %cl
	movb	%cl, 1728(%rax)
	movb	2121(%rsp), %cl
	movb	%cl, 1729(%rax)
	movb	2122(%rsp), %cl
	movb	%cl, 1730(%rax)
	movb	2123(%rsp), %cl
	movb	%cl, 1731(%rax)
	movb	2124(%rsp), %cl
	movb	%cl, 1732(%rax)
	movb	2125(%rsp), %cl
	movb	%cl, 1733(%rax)
	movb	2126(%rsp), %cl
	movb	%cl, 1734(%rax)
	movb	2127(%rsp), %cl
	movb	%cl, 1735(%rax)
	movb	2128(%rsp), %cl
	movb	%cl, 1736(%rax)
	movb	2129(%rsp), %cl
	movb	%cl, 1737(%rax)
	movb	2130(%rsp), %cl
	movb	%cl, 1738(%rax)
	movb	2131(%rsp), %cl
	movb	%cl, 1739(%rax)
	movb	2132(%rsp), %cl
	movb	%cl, 1740(%rax)
	movb	2133(%rsp), %cl
	movb	%cl, 1741(%rax)
	movb	2134(%rsp), %cl
	movb	%cl, 1742(%rax)
	movb	2135(%rsp), %cl
	movb	%cl, 1743(%rax)
	movb	2136(%rsp), %cl
	movb	%cl, 1744(%rax)
	movb	2137(%rsp), %cl
	movb	%cl, 1745(%rax)
	movb	2138(%rsp), %cl
	movb	%cl, 1746(%rax)
	movb	2139(%rsp), %cl
	movb	%cl, 1747(%rax)
	movb	2140(%rsp), %cl
	movb	%cl, 1748(%rax)
	movb	2141(%rsp), %cl
	movb	%cl, 1749(%rax)
	movb	2142(%rsp), %cl
	movb	%cl, 1750(%rax)
	movb	2143(%rsp), %cl
	movb	%cl, 1751(%rax)
	movb	2144(%rsp), %cl
	movb	%cl, 1752(%rax)
	movb	2145(%rsp), %cl
	movb	%cl, 1753(%rax)
	movb	2146(%rsp), %cl
	movb	%cl, 1754(%rax)
	movb	2147(%rsp), %cl
	movb	%cl, 1755(%rax)
	movb	2148(%rsp), %cl
	movb	%cl, 1756(%rax)
	movb	2149(%rsp), %cl
	movb	%cl, 1757(%rax)
	movb	2150(%rsp), %cl
	movb	%cl, 1758(%rax)
	movb	2151(%rsp), %cl
	movb	%cl, 1759(%rax)
	movb	2152(%rsp), %cl
	movb	%cl, 1760(%rax)
	movb	2153(%rsp), %cl
	movb	%cl, 1761(%rax)
	movb	2154(%rsp), %cl
	movb	%cl, 1762(%rax)
	movb	2155(%rsp), %cl
	movb	%cl, 1763(%rax)
	movb	2156(%rsp), %cl
	movb	%cl, 1764(%rax)
	movb	2157(%rsp), %cl
	movb	%cl, 1765(%rax)
	movb	2158(%rsp), %cl
	movb	%cl, 1766(%rax)
	movb	2159(%rsp), %cl
	movb	%cl, 1767(%rax)
	movb	2160(%rsp), %cl
	movb	%cl, 1768(%rax)
	movb	2161(%rsp), %cl
	movb	%cl, 1769(%rax)
	movb	2162(%rsp), %cl
	movb	%cl, 1770(%rax)
	movb	2163(%rsp), %cl
	movb	%cl, 1771(%rax)
	movb	2164(%rsp), %cl
	movb	%cl, 1772(%rax)
	movb	2165(%rsp), %cl
	movb	%cl, 1773(%rax)
	movb	2166(%rsp), %cl
	movb	%cl, 1774(%rax)
	movb	2167(%rsp), %cl
	movb	%cl, 1775(%rax)
	movb	2168(%rsp), %cl
	movb	%cl, 1776(%rax)
	movb	2169(%rsp), %cl
	movb	%cl, 1777(%rax)
	movb	2170(%rsp), %cl
	movb	%cl, 1778(%rax)
	movb	2171(%rsp), %cl
	movb	%cl, 1779(%rax)
	movb	2172(%rsp), %cl
	movb	%cl, 1780(%rax)
	movb	2173(%rsp), %cl
	movb	%cl, 1781(%rax)
	movb	2174(%rsp), %cl
	movb	%cl, 1782(%rax)
	movb	2175(%rsp), %cl
	movb	%cl, 1783(%rax)
	movb	2176(%rsp), %cl
	movb	%cl, 1784(%rax)
	movb	2177(%rsp), %cl
	movb	%cl, 1785(%rax)
	movb	2178(%rsp), %cl
	movb	%cl, 1786(%rax)
	movb	2179(%rsp), %cl
	movb	%cl, 1787(%rax)
	movb	2180(%rsp), %cl
	movb	%cl, 1788(%rax)
	movb	2181(%rsp), %cl
	movb	%cl, 1789(%rax)
	movb	2182(%rsp), %cl
	movb	%cl, 1790(%rax)
	movb	2183(%rsp), %cl
	movb	%cl, 1791(%rax)
	movb	2184(%rsp), %cl
	movb	%cl, 1792(%rax)
	movb	2185(%rsp), %cl
	movb	%cl, 1793(%rax)
	movb	2186(%rsp), %cl
	movb	%cl, 1794(%rax)
	movb	2187(%rsp), %cl
	movb	%cl, 1795(%rax)
	movb	2188(%rsp), %cl
	movb	%cl, 1796(%rax)
	movb	2189(%rsp), %cl
	movb	%cl, 1797(%rax)
	movb	2190(%rsp), %cl
	movb	%cl, 1798(%rax)
	movb	2191(%rsp), %cl
	movb	%cl, 1799(%rax)
	movb	2192(%rsp), %cl
	movb	%cl, 1800(%rax)
	movb	2193(%rsp), %cl
	movb	%cl, 1801(%rax)
	movb	2194(%rsp), %cl
	movb	%cl, 1802(%rax)
	movb	2195(%rsp), %cl
	movb	%cl, 1803(%rax)
	movb	2196(%rsp), %cl
	movb	%cl, 1804(%rax)
	movb	2197(%rsp), %cl
	movb	%cl, 1805(%rax)
	movb	2198(%rsp), %cl
	movb	%cl, 1806(%rax)
	movb	2199(%rsp), %cl
	movb	%cl, 1807(%rax)
	movb	2200(%rsp), %cl
	movb	%cl, 1808(%rax)
	movb	2201(%rsp), %cl
	movb	%cl, 1809(%rax)
	movb	2202(%rsp), %cl
	movb	%cl, 1810(%rax)
	movb	2203(%rsp), %cl
	movb	%cl, 1811(%rax)
	movb	2204(%rsp), %cl
	movb	%cl, 1812(%rax)
	movb	2205(%rsp), %cl
	movb	%cl, 1813(%rax)
	movb	2206(%rsp), %cl
	movb	%cl, 1814(%rax)
	movb	2207(%rsp), %cl
	movb	%cl, 1815(%rax)
	movb	2208(%rsp), %cl
	movb	%cl, 1816(%rax)
	movb	2209(%rsp), %cl
	movb	%cl, 1817(%rax)
	movb	2210(%rsp), %cl
	movb	%cl, 1818(%rax)
	movb	2211(%rsp), %cl
	movb	%cl, 1819(%rax)
	movb	2212(%rsp), %cl
	movb	%cl, 1820(%rax)
	movb	2213(%rsp), %cl
	movb	%cl, 1821(%rax)
	movb	2214(%rsp), %cl
	movb	%cl, 1822(%rax)
	movb	2215(%rsp), %cl
	movb	%cl, 1823(%rax)
	movb	2216(%rsp), %cl
	movb	%cl, 1824(%rax)
	movb	2217(%rsp), %cl
	movb	%cl, 1825(%rax)
	movb	2218(%rsp), %cl
	movb	%cl, 1826(%rax)
	movb	2219(%rsp), %cl
	movb	%cl, 1827(%rax)
	movb	2220(%rsp), %cl
	movb	%cl, 1828(%rax)
	movb	2221(%rsp), %cl
	movb	%cl, 1829(%rax)
	movb	2222(%rsp), %cl
	movb	%cl, 1830(%rax)
	movb	2223(%rsp), %cl
	movb	%cl, 1831(%rax)
	movb	2224(%rsp), %cl
	movb	%cl, 1832(%rax)
	movb	2225(%rsp), %cl
	movb	%cl, 1833(%rax)
	movb	2226(%rsp), %cl
	movb	%cl, 1834(%rax)
	movb	2227(%rsp), %cl
	movb	%cl, 1835(%rax)
	movb	2228(%rsp), %cl
	movb	%cl, 1836(%rax)
	movb	2229(%rsp), %cl
	movb	%cl, 1837(%rax)
	movb	2230(%rsp), %cl
	movb	%cl, 1838(%rax)
	movb	2231(%rsp), %cl
	movb	%cl, 1839(%rax)
	movb	2232(%rsp), %cl
	movb	%cl, 1840(%rax)
	movb	2233(%rsp), %cl
	movb	%cl, 1841(%rax)
	movb	2234(%rsp), %cl
	movb	%cl, 1842(%rax)
	movb	2235(%rsp), %cl
	movb	%cl, 1843(%rax)
	movb	2236(%rsp), %cl
	movb	%cl, 1844(%rax)
	movb	2237(%rsp), %cl
	movb	%cl, 1845(%rax)
	movb	2238(%rsp), %cl
	movb	%cl, 1846(%rax)
	movb	2239(%rsp), %cl
	movb	%cl, 1847(%rax)
	movb	2240(%rsp), %cl
	movb	%cl, 1848(%rax)
	movb	2241(%rsp), %cl
	movb	%cl, 1849(%rax)
	movb	2242(%rsp), %cl
	movb	%cl, 1850(%rax)
	movb	2243(%rsp), %cl
	movb	%cl, 1851(%rax)
	movb	2244(%rsp), %cl
	movb	%cl, 1852(%rax)
	movb	2245(%rsp), %cl
	movb	%cl, 1853(%rax)
	movb	2246(%rsp), %cl
	movb	%cl, 1854(%rax)
	movb	2247(%rsp), %cl
	movb	%cl, 1855(%rax)
	movb	2248(%rsp), %cl
	movb	%cl, 1856(%rax)
	movb	2249(%rsp), %cl
	movb	%cl, 1857(%rax)
	movb	2250(%rsp), %cl
	movb	%cl, 1858(%rax)
	movb	2251(%rsp), %cl
	movb	%cl, 1859(%rax)
	movb	2252(%rsp), %cl
	movb	%cl, 1860(%rax)
	movb	2253(%rsp), %cl
	movb	%cl, 1861(%rax)
	movb	2254(%rsp), %cl
	movb	%cl, 1862(%rax)
	movb	2255(%rsp), %cl
	movb	%cl, 1863(%rax)
	movb	2256(%rsp), %cl
	movb	%cl, 1864(%rax)
	movb	2257(%rsp), %cl
	movb	%cl, 1865(%rax)
	movb	2258(%rsp), %cl
	movb	%cl, 1866(%rax)
	movb	2259(%rsp), %cl
	movb	%cl, 1867(%rax)
	movb	2260(%rsp), %cl
	movb	%cl, 1868(%rax)
	movb	2261(%rsp), %cl
	movb	%cl, 1869(%rax)
	movb	2262(%rsp), %cl
	movb	%cl, 1870(%rax)
	movb	2263(%rsp), %cl
	movb	%cl, 1871(%rax)
	movb	2264(%rsp), %cl
	movb	%cl, 1872(%rax)
	movb	2265(%rsp), %cl
	movb	%cl, 1873(%rax)
	movb	2266(%rsp), %cl
	movb	%cl, 1874(%rax)
	movb	2267(%rsp), %cl
	movb	%cl, 1875(%rax)
	movb	2268(%rsp), %cl
	movb	%cl, 1876(%rax)
	movb	2269(%rsp), %cl
	movb	%cl, 1877(%rax)
	movb	2270(%rsp), %cl
	movb	%cl, 1878(%rax)
	movb	2271(%rsp), %cl
	movb	%cl, 1879(%rax)
	movb	2272(%rsp), %cl
	movb	%cl, 1880(%rax)
	movb	2273(%rsp), %cl
	movb	%cl, 1881(%rax)
	movb	2274(%rsp), %cl
	movb	%cl, 1882(%rax)
	movb	2275(%rsp), %cl
	movb	%cl, 1883(%rax)
	movb	2276(%rsp), %cl
	movb	%cl, 1884(%rax)
	movb	2277(%rsp), %cl
	movb	%cl, 1885(%rax)
	movb	2278(%rsp), %cl
	movb	%cl, 1886(%rax)
	movb	2279(%rsp), %cl
	movb	%cl, 1887(%rax)
	movb	2280(%rsp), %cl
	movb	%cl, 1888(%rax)
	movb	2281(%rsp), %cl
	movb	%cl, 1889(%rax)
	movb	2282(%rsp), %cl
	movb	%cl, 1890(%rax)
	movb	2283(%rsp), %cl
	movb	%cl, 1891(%rax)
	movb	2284(%rsp), %cl
	movb	%cl, 1892(%rax)
	movb	2285(%rsp), %cl
	movb	%cl, 1893(%rax)
	movb	2286(%rsp), %cl
	movb	%cl, 1894(%rax)
	movb	2287(%rsp), %cl
	movb	%cl, 1895(%rax)
	movb	2288(%rsp), %cl
	movb	%cl, 1896(%rax)
	movb	2289(%rsp), %cl
	movb	%cl, 1897(%rax)
	movb	2290(%rsp), %cl
	movb	%cl, 1898(%rax)
	movb	2291(%rsp), %cl
	movb	%cl, 1899(%rax)
	movb	2292(%rsp), %cl
	movb	%cl, 1900(%rax)
	movb	2293(%rsp), %cl
	movb	%cl, 1901(%rax)
	movb	2294(%rsp), %cl
	movb	%cl, 1902(%rax)
	movb	2295(%rsp), %cl
	movb	%cl, 1903(%rax)
	movb	2296(%rsp), %cl
	movb	%cl, 1904(%rax)
	movb	2297(%rsp), %cl
	movb	%cl, 1905(%rax)
	movb	2298(%rsp), %cl
	movb	%cl, 1906(%rax)
	movb	2299(%rsp), %cl
	movb	%cl, 1907(%rax)
	movb	2300(%rsp), %cl
	movb	%cl, 1908(%rax)
	movb	2301(%rsp), %cl
	movb	%cl, 1909(%rax)
	movb	2302(%rsp), %cl
	movb	%cl, 1910(%rax)
	movb	2303(%rsp), %cl
	movb	%cl, 1911(%rax)
	movb	2304(%rsp), %cl
	movb	%cl, 1912(%rax)
	movb	2305(%rsp), %cl
	movb	%cl, 1913(%rax)
	movb	2306(%rsp), %cl
	movb	%cl, 1914(%rax)
	movb	2307(%rsp), %cl
	movb	%cl, 1915(%rax)
	movb	2308(%rsp), %cl
	movb	%cl, 1916(%rax)
	movb	2309(%rsp), %cl
	movb	%cl, 1917(%rax)
	movb	2310(%rsp), %cl
	movb	%cl, 1918(%rax)
	movb	2311(%rsp), %cl
	movb	%cl, 1919(%rax)
	movb	2312(%rsp), %cl
	movb	%cl, 1920(%rax)
	movb	2313(%rsp), %cl
	movb	%cl, 1921(%rax)
	movb	2314(%rsp), %cl
	movb	%cl, 1922(%rax)
	movb	2315(%rsp), %cl
	movb	%cl, 1923(%rax)
	movb	2316(%rsp), %cl
	movb	%cl, 1924(%rax)
	movb	2317(%rsp), %cl
	movb	%cl, 1925(%rax)
	movb	2318(%rsp), %cl
	movb	%cl, 1926(%rax)
	movb	2319(%rsp), %cl
	movb	%cl, 1927(%rax)
	movb	2320(%rsp), %cl
	movb	%cl, 1928(%rax)
	movb	2321(%rsp), %cl
	movb	%cl, 1929(%rax)
	movb	2322(%rsp), %cl
	movb	%cl, 1930(%rax)
	movb	2323(%rsp), %cl
	movb	%cl, 1931(%rax)
	movb	2324(%rsp), %cl
	movb	%cl, 1932(%rax)
	movb	2325(%rsp), %cl
	movb	%cl, 1933(%rax)
	movb	2326(%rsp), %cl
	movb	%cl, 1934(%rax)
	movb	2327(%rsp), %cl
	movb	%cl, 1935(%rax)
	movb	2328(%rsp), %cl
	movb	%cl, 1936(%rax)
	movb	2329(%rsp), %cl
	movb	%cl, 1937(%rax)
	movb	2330(%rsp), %cl
	movb	%cl, 1938(%rax)
	movb	2331(%rsp), %cl
	movb	%cl, 1939(%rax)
	movb	2332(%rsp), %cl
	movb	%cl, 1940(%rax)
	movb	2333(%rsp), %cl
	movb	%cl, 1941(%rax)
	movb	2334(%rsp), %cl
	movb	%cl, 1942(%rax)
	movb	2335(%rsp), %cl
	movb	%cl, 1943(%rax)
	movb	2336(%rsp), %cl
	movb	%cl, 1944(%rax)
	movb	2337(%rsp), %cl
	movb	%cl, 1945(%rax)
	movb	2338(%rsp), %cl
	movb	%cl, 1946(%rax)
	movb	2339(%rsp), %cl
	movb	%cl, 1947(%rax)
	movb	2340(%rsp), %cl
	movb	%cl, 1948(%rax)
	movb	2341(%rsp), %cl
	movb	%cl, 1949(%rax)
	movb	2342(%rsp), %cl
	movb	%cl, 1950(%rax)
	movb	2343(%rsp), %cl
	movb	%cl, 1951(%rax)
	movb	2344(%rsp), %cl
	movb	%cl, 1952(%rax)
	movb	2345(%rsp), %cl
	movb	%cl, 1953(%rax)
	movb	2346(%rsp), %cl
	movb	%cl, 1954(%rax)
	movb	2347(%rsp), %cl
	movb	%cl, 1955(%rax)
	movb	2348(%rsp), %cl
	movb	%cl, 1956(%rax)
	movb	2349(%rsp), %cl
	movb	%cl, 1957(%rax)
	movb	2350(%rsp), %cl
	movb	%cl, 1958(%rax)
	movb	2351(%rsp), %cl
	movb	%cl, 1959(%rax)
	movb	2352(%rsp), %cl
	movb	%cl, 1960(%rax)
	movb	2353(%rsp), %cl
	movb	%cl, 1961(%rax)
	movb	2354(%rsp), %cl
	movb	%cl, 1962(%rax)
	movb	2355(%rsp), %cl
	movb	%cl, 1963(%rax)
	movb	2356(%rsp), %cl
	movb	%cl, 1964(%rax)
	movb	2357(%rsp), %cl
	movb	%cl, 1965(%rax)
	movb	2358(%rsp), %cl
	movb	%cl, 1966(%rax)
	movb	2359(%rsp), %cl
	movb	%cl, 1967(%rax)
	movb	2360(%rsp), %cl
	movb	%cl, 1968(%rax)
	movb	2361(%rsp), %cl
	movb	%cl, 1969(%rax)
	movb	2362(%rsp), %cl
	movb	%cl, 1970(%rax)
	movb	2363(%rsp), %cl
	movb	%cl, 1971(%rax)
	movb	2364(%rsp), %cl
	movb	%cl, 1972(%rax)
	movb	2365(%rsp), %cl
	movb	%cl, 1973(%rax)
	movb	2366(%rsp), %cl
	movb	%cl, 1974(%rax)
	movb	2367(%rsp), %cl
	movb	%cl, 1975(%rax)
	movb	2368(%rsp), %cl
	movb	%cl, 1976(%rax)
	movb	2369(%rsp), %cl
	movb	%cl, 1977(%rax)
	movb	2370(%rsp), %cl
	movb	%cl, 1978(%rax)
	movb	2371(%rsp), %cl
	movb	%cl, 1979(%rax)
	movb	2372(%rsp), %cl
	movb	%cl, 1980(%rax)
	movb	2373(%rsp), %cl
	movb	%cl, 1981(%rax)
	movb	2374(%rsp), %cl
	movb	%cl, 1982(%rax)
	movb	2375(%rsp), %cl
	movb	%cl, 1983(%rax)
	movb	2376(%rsp), %cl
	movb	%cl, 1984(%rax)
	movb	2377(%rsp), %cl
	movb	%cl, 1985(%rax)
	movb	2378(%rsp), %cl
	movb	%cl, 1986(%rax)
	movb	2379(%rsp), %cl
	movb	%cl, 1987(%rax)
	movb	2380(%rsp), %cl
	movb	%cl, 1988(%rax)
	movb	2381(%rsp), %cl
	movb	%cl, 1989(%rax)
	movb	2382(%rsp), %cl
	movb	%cl, 1990(%rax)
	movb	2383(%rsp), %cl
	movb	%cl, 1991(%rax)
	movb	2384(%rsp), %cl
	movb	%cl, 1992(%rax)
	movb	2385(%rsp), %cl
	movb	%cl, 1993(%rax)
	movb	2386(%rsp), %cl
	movb	%cl, 1994(%rax)
	movb	2387(%rsp), %cl
	movb	%cl, 1995(%rax)
	movb	2388(%rsp), %cl
	movb	%cl, 1996(%rax)
	movb	2389(%rsp), %cl
	movb	%cl, 1997(%rax)
	movb	2390(%rsp), %cl
	movb	%cl, 1998(%rax)
	movb	2391(%rsp), %cl
	movb	%cl, 1999(%rax)
	movb	2392(%rsp), %cl
	movb	%cl, 2000(%rax)
	movb	2393(%rsp), %cl
	movb	%cl, 2001(%rax)
	movb	2394(%rsp), %cl
	movb	%cl, 2002(%rax)
	movb	2395(%rsp), %cl
	movb	%cl, 2003(%rax)
	movb	2396(%rsp), %cl
	movb	%cl, 2004(%rax)
	movb	2397(%rsp), %cl
	movb	%cl, 2005(%rax)
	movb	2398(%rsp), %cl
	movb	%cl, 2006(%rax)
	movb	2399(%rsp), %cl
	movb	%cl, 2007(%rax)
	movb	2400(%rsp), %cl
	movb	%cl, 2008(%rax)
	movb	2401(%rsp), %cl
	movb	%cl, 2009(%rax)
	movb	2402(%rsp), %cl
	movb	%cl, 2010(%rax)
	movb	2403(%rsp), %cl
	movb	%cl, 2011(%rax)
	movb	2404(%rsp), %cl
	movb	%cl, 2012(%rax)
	movb	2405(%rsp), %cl
	movb	%cl, 2013(%rax)
	movb	2406(%rsp), %cl
	movb	%cl, 2014(%rax)
	movb	2407(%rsp), %cl
	movb	%cl, 2015(%rax)
	movb	2408(%rsp), %cl
	movb	%cl, 2016(%rax)
	movb	2409(%rsp), %cl
	movb	%cl, 2017(%rax)
	movb	2410(%rsp), %cl
	movb	%cl, 2018(%rax)
	movb	2411(%rsp), %cl
	movb	%cl, 2019(%rax)
	movb	2412(%rsp), %cl
	movb	%cl, 2020(%rax)
	movb	2413(%rsp), %cl
	movb	%cl, 2021(%rax)
	movb	2414(%rsp), %cl
	movb	%cl, 2022(%rax)
	movb	2415(%rsp), %cl
	movb	%cl, 2023(%rax)
	movb	2416(%rsp), %cl
	movb	%cl, 2024(%rax)
	movb	2417(%rsp), %cl
	movb	%cl, 2025(%rax)
	movb	2418(%rsp), %cl
	movb	%cl, 2026(%rax)
	movb	2419(%rsp), %cl
	movb	%cl, 2027(%rax)
	movb	2420(%rsp), %cl
	movb	%cl, 2028(%rax)
	movb	2421(%rsp), %cl
	movb	%cl, 2029(%rax)
	movb	2422(%rsp), %cl
	movb	%cl, 2030(%rax)
	movb	2423(%rsp), %cl
	movb	%cl, 2031(%rax)
	movb	2424(%rsp), %cl
	movb	%cl, 2032(%rax)
	movb	2425(%rsp), %cl
	movb	%cl, 2033(%rax)
	movb	2426(%rsp), %cl
	movb	%cl, 2034(%rax)
	movb	2427(%rsp), %cl
	movb	%cl, 2035(%rax)
	movb	2428(%rsp), %cl
	movb	%cl, 2036(%rax)
	movb	2429(%rsp), %cl
	movb	%cl, 2037(%rax)
	movb	2430(%rsp), %cl
	movb	%cl, 2038(%rax)
	movb	2431(%rsp), %cl
	movb	%cl, 2039(%rax)
	movb	2432(%rsp), %cl
	movb	%cl, 2040(%rax)
	movb	2433(%rsp), %cl
	movb	%cl, 2041(%rax)
	movb	2434(%rsp), %cl
	movb	%cl, 2042(%rax)
	movb	2435(%rsp), %cl
	movb	%cl, 2043(%rax)
	movb	2436(%rsp), %cl
	movb	%cl, 2044(%rax)
	movb	2437(%rsp), %cl
	movb	%cl, 2045(%rax)
	movb	2438(%rsp), %cl
	movb	%cl, 2046(%rax)
	movb	2439(%rsp), %cl
	movb	%cl, 2047(%rax)
	movb	2440(%rsp), %cl
	movb	%cl, 2048(%rax)
	movb	2441(%rsp), %cl
	movb	%cl, 2049(%rax)
	movb	2442(%rsp), %cl
	movb	%cl, 2050(%rax)
	movb	2443(%rsp), %cl
	movb	%cl, 2051(%rax)
	movb	2444(%rsp), %cl
	movb	%cl, 2052(%rax)
	movb	2445(%rsp), %cl
	movb	%cl, 2053(%rax)
	movb	2446(%rsp), %cl
	movb	%cl, 2054(%rax)
	movb	2447(%rsp), %cl
	movb	%cl, 2055(%rax)
	movb	2448(%rsp), %cl
	movb	%cl, 2056(%rax)
	movb	2449(%rsp), %cl
	movb	%cl, 2057(%rax)
	movb	2450(%rsp), %cl
	movb	%cl, 2058(%rax)
	movb	2451(%rsp), %cl
	movb	%cl, 2059(%rax)
	movb	2452(%rsp), %cl
	movb	%cl, 2060(%rax)
	movb	2453(%rsp), %cl
	movb	%cl, 2061(%rax)
	movb	2454(%rsp), %cl
	movb	%cl, 2062(%rax)
	movb	2455(%rsp), %cl
	movb	%cl, 2063(%rax)
	movb	2456(%rsp), %cl
	movb	%cl, 2064(%rax)
	movb	2457(%rsp), %cl
	movb	%cl, 2065(%rax)
	movb	2458(%rsp), %cl
	movb	%cl, 2066(%rax)
	movb	2459(%rsp), %cl
	movb	%cl, 2067(%rax)
	movb	2460(%rsp), %cl
	movb	%cl, 2068(%rax)
	movb	2461(%rsp), %cl
	movb	%cl, 2069(%rax)
	movb	2462(%rsp), %cl
	movb	%cl, 2070(%rax)
	movb	2463(%rsp), %cl
	movb	%cl, 2071(%rax)
	movb	2464(%rsp), %cl
	movb	%cl, 2072(%rax)
	movb	2465(%rsp), %cl
	movb	%cl, 2073(%rax)
	movb	2466(%rsp), %cl
	movb	%cl, 2074(%rax)
	movb	2467(%rsp), %cl
	movb	%cl, 2075(%rax)
	movb	2468(%rsp), %cl
	movb	%cl, 2076(%rax)
	movb	2469(%rsp), %cl
	movb	%cl, 2077(%rax)
	movb	2470(%rsp), %cl
	movb	%cl, 2078(%rax)
	movb	2471(%rsp), %cl
	movb	%cl, 2079(%rax)
	movb	2472(%rsp), %cl
	movb	%cl, 2080(%rax)
	movb	2473(%rsp), %cl
	movb	%cl, 2081(%rax)
	movb	2474(%rsp), %cl
	movb	%cl, 2082(%rax)
	movb	2475(%rsp), %cl
	movb	%cl, 2083(%rax)
	movb	2476(%rsp), %cl
	movb	%cl, 2084(%rax)
	movb	2477(%rsp), %cl
	movb	%cl, 2085(%rax)
	movb	2478(%rsp), %cl
	movb	%cl, 2086(%rax)
	movb	2479(%rsp), %cl
	movb	%cl, 2087(%rax)
	movb	2480(%rsp), %cl
	movb	%cl, 2088(%rax)
	movb	2481(%rsp), %cl
	movb	%cl, 2089(%rax)
	movb	2482(%rsp), %cl
	movb	%cl, 2090(%rax)
	movb	2483(%rsp), %cl
	movb	%cl, 2091(%rax)
	movb	2484(%rsp), %cl
	movb	%cl, 2092(%rax)
	movb	2485(%rsp), %cl
	movb	%cl, 2093(%rax)
	movb	2486(%rsp), %cl
	movb	%cl, 2094(%rax)
	movb	2487(%rsp), %cl
	movb	%cl, 2095(%rax)
	movb	2488(%rsp), %cl
	movb	%cl, 2096(%rax)
	movb	2489(%rsp), %cl
	movb	%cl, 2097(%rax)
	movb	2490(%rsp), %cl
	movb	%cl, 2098(%rax)
	movb	2491(%rsp), %cl
	movb	%cl, 2099(%rax)
	movb	2492(%rsp), %cl
	movb	%cl, 2100(%rax)
	movb	2493(%rsp), %cl
	movb	%cl, 2101(%rax)
	movb	2494(%rsp), %cl
	movb	%cl, 2102(%rax)
	movb	2495(%rsp), %cl
	movb	%cl, 2103(%rax)
	movb	2496(%rsp), %cl
	movb	%cl, 2104(%rax)
	movb	2497(%rsp), %cl
	movb	%cl, 2105(%rax)
	movb	2498(%rsp), %cl
	movb	%cl, 2106(%rax)
	movb	2499(%rsp), %cl
	movb	%cl, 2107(%rax)
	movb	2500(%rsp), %cl
	movb	%cl, 2108(%rax)
	movb	2501(%rsp), %cl
	movb	%cl, 2109(%rax)
	movb	2502(%rsp), %cl
	movb	%cl, 2110(%rax)
	movb	2503(%rsp), %cl
	movb	%cl, 2111(%rax)
	movb	2504(%rsp), %cl
	movb	%cl, 2112(%rax)
	movb	2505(%rsp), %cl
	movb	%cl, 2113(%rax)
	movb	2506(%rsp), %cl
	movb	%cl, 2114(%rax)
	movb	2507(%rsp), %cl
	movb	%cl, 2115(%rax)
	movb	2508(%rsp), %cl
	movb	%cl, 2116(%rax)
	movb	2509(%rsp), %cl
	movb	%cl, 2117(%rax)
	movb	2510(%rsp), %cl
	movb	%cl, 2118(%rax)
	movb	2511(%rsp), %cl
	movb	%cl, 2119(%rax)
	movb	2512(%rsp), %cl
	movb	%cl, 2120(%rax)
	movb	2513(%rsp), %cl
	movb	%cl, 2121(%rax)
	movb	2514(%rsp), %cl
	movb	%cl, 2122(%rax)
	movb	2515(%rsp), %cl
	movb	%cl, 2123(%rax)
	movb	2516(%rsp), %cl
	movb	%cl, 2124(%rax)
	movb	2517(%rsp), %cl
	movb	%cl, 2125(%rax)
	movb	2518(%rsp), %cl
	movb	%cl, 2126(%rax)
	movb	2519(%rsp), %cl
	movb	%cl, 2127(%rax)
	movb	2520(%rsp), %cl
	movb	%cl, 2128(%rax)
	movb	2521(%rsp), %cl
	movb	%cl, 2129(%rax)
	movb	2522(%rsp), %cl
	movb	%cl, 2130(%rax)
	movb	2523(%rsp), %cl
	movb	%cl, 2131(%rax)
	movb	2524(%rsp), %cl
	movb	%cl, 2132(%rax)
	movb	2525(%rsp), %cl
	movb	%cl, 2133(%rax)
	movb	2526(%rsp), %cl
	movb	%cl, 2134(%rax)
	movb	2527(%rsp), %cl
	movb	%cl, 2135(%rax)
	movb	2528(%rsp), %cl
	movb	%cl, 2136(%rax)
	movb	2529(%rsp), %cl
	movb	%cl, 2137(%rax)
	movb	2530(%rsp), %cl
	movb	%cl, 2138(%rax)
	movb	2531(%rsp), %cl
	movb	%cl, 2139(%rax)
	movb	2532(%rsp), %cl
	movb	%cl, 2140(%rax)
	movb	2533(%rsp), %cl
	movb	%cl, 2141(%rax)
	movb	2534(%rsp), %cl
	movb	%cl, 2142(%rax)
	movb	2535(%rsp), %cl
	movb	%cl, 2143(%rax)
	movb	72(%rsp), %cl
	movb	%cl, 2144(%rax)
	movb	73(%rsp), %cl
	movb	%cl, 2145(%rax)
	movb	74(%rsp), %cl
	movb	%cl, 2146(%rax)
	movb	75(%rsp), %cl
	movb	%cl, 2147(%rax)
	movb	76(%rsp), %cl
	movb	%cl, 2148(%rax)
	movb	77(%rsp), %cl
	movb	%cl, 2149(%rax)
	movb	78(%rsp), %cl
	movb	%cl, 2150(%rax)
	movb	79(%rsp), %cl
	movb	%cl, 2151(%rax)
	movb	80(%rsp), %cl
	movb	%cl, 2152(%rax)
	movb	81(%rsp), %cl
	movb	%cl, 2153(%rax)
	movb	82(%rsp), %cl
	movb	%cl, 2154(%rax)
	movb	83(%rsp), %cl
	movb	%cl, 2155(%rax)
	movb	84(%rsp), %cl
	movb	%cl, 2156(%rax)
	movb	85(%rsp), %cl
	movb	%cl, 2157(%rax)
	movb	86(%rsp), %cl
	movb	%cl, 2158(%rax)
	movb	87(%rsp), %cl
	movb	%cl, 2159(%rax)
	movb	88(%rsp), %cl
	movb	%cl, 2160(%rax)
	movb	89(%rsp), %cl
	movb	%cl, 2161(%rax)
	movb	90(%rsp), %cl
	movb	%cl, 2162(%rax)
	movb	91(%rsp), %cl
	movb	%cl, 2163(%rax)
	movb	92(%rsp), %cl
	movb	%cl, 2164(%rax)
	movb	93(%rsp), %cl
	movb	%cl, 2165(%rax)
	movb	94(%rsp), %cl
	movb	%cl, 2166(%rax)
	movb	95(%rsp), %cl
	movb	%cl, 2167(%rax)
	movb	96(%rsp), %cl
	movb	%cl, 2168(%rax)
	movb	97(%rsp), %cl
	movb	%cl, 2169(%rax)
	movb	98(%rsp), %cl
	movb	%cl, 2170(%rax)
	movb	99(%rsp), %cl
	movb	%cl, 2171(%rax)
	movb	100(%rsp), %cl
	movb	%cl, 2172(%rax)
	movb	101(%rsp), %cl
	movb	%cl, 2173(%rax)
	movb	102(%rsp), %cl
	movb	%cl, 2174(%rax)
	movb	103(%rsp), %cl
	movb	%cl, 2175(%rax)
	movb	104(%rsp), %cl
	movb	%cl, 2176(%rax)
	movb	105(%rsp), %cl
	movb	%cl, 2177(%rax)
	movb	106(%rsp), %cl
	movb	%cl, 2178(%rax)
	movb	107(%rsp), %cl
	movb	%cl, 2179(%rax)
	movb	108(%rsp), %cl
	movb	%cl, 2180(%rax)
	movb	109(%rsp), %cl
	movb	%cl, 2181(%rax)
	movb	110(%rsp), %cl
	movb	%cl, 2182(%rax)
	movb	111(%rsp), %cl
	movb	%cl, 2183(%rax)
	movb	112(%rsp), %cl
	movb	%cl, 2184(%rax)
	movb	113(%rsp), %cl
	movb	%cl, 2185(%rax)
	movb	114(%rsp), %cl
	movb	%cl, 2186(%rax)
	movb	115(%rsp), %cl
	movb	%cl, 2187(%rax)
	movb	116(%rsp), %cl
	movb	%cl, 2188(%rax)
	movb	117(%rsp), %cl
	movb	%cl, 2189(%rax)
	movb	118(%rsp), %cl
	movb	%cl, 2190(%rax)
	movb	119(%rsp), %cl
	movb	%cl, 2191(%rax)
	movb	120(%rsp), %cl
	movb	%cl, 2192(%rax)
	movb	121(%rsp), %cl
	movb	%cl, 2193(%rax)
	movb	122(%rsp), %cl
	movb	%cl, 2194(%rax)
	movb	123(%rsp), %cl
	movb	%cl, 2195(%rax)
	movb	124(%rsp), %cl
	movb	%cl, 2196(%rax)
	movb	125(%rsp), %cl
	movb	%cl, 2197(%rax)
	movb	126(%rsp), %cl
	movb	%cl, 2198(%rax)
	movb	127(%rsp), %cl
	movb	%cl, 2199(%rax)
	movb	128(%rsp), %cl
	movb	%cl, 2200(%rax)
	movb	129(%rsp), %cl
	movb	%cl, 2201(%rax)
	movb	130(%rsp), %cl
	movb	%cl, 2202(%rax)
	movb	131(%rsp), %cl
	movb	%cl, 2203(%rax)
	movb	132(%rsp), %cl
	movb	%cl, 2204(%rax)
	movb	133(%rsp), %cl
	movb	%cl, 2205(%rax)
	movb	134(%rsp), %cl
	movb	%cl, 2206(%rax)
	movb	135(%rsp), %cl
	movb	%cl, 2207(%rax)
	movb	136(%rsp), %cl
	movb	%cl, 2208(%rax)
	movb	137(%rsp), %cl
	movb	%cl, 2209(%rax)
	movb	138(%rsp), %cl
	movb	%cl, 2210(%rax)
	movb	139(%rsp), %cl
	movb	%cl, 2211(%rax)
	movb	140(%rsp), %cl
	movb	%cl, 2212(%rax)
	movb	141(%rsp), %cl
	movb	%cl, 2213(%rax)
	movb	142(%rsp), %cl
	movb	%cl, 2214(%rax)
	movb	143(%rsp), %cl
	movb	%cl, 2215(%rax)
	movb	144(%rsp), %cl
	movb	%cl, 2216(%rax)
	movb	145(%rsp), %cl
	movb	%cl, 2217(%rax)
	movb	146(%rsp), %cl
	movb	%cl, 2218(%rax)
	movb	147(%rsp), %cl
	movb	%cl, 2219(%rax)
	movb	148(%rsp), %cl
	movb	%cl, 2220(%rax)
	movb	149(%rsp), %cl
	movb	%cl, 2221(%rax)
	movb	150(%rsp), %cl
	movb	%cl, 2222(%rax)
	movb	151(%rsp), %cl
	movb	%cl, 2223(%rax)
	movb	152(%rsp), %cl
	movb	%cl, 2224(%rax)
	movb	153(%rsp), %cl
	movb	%cl, 2225(%rax)
	movb	154(%rsp), %cl
	movb	%cl, 2226(%rax)
	movb	155(%rsp), %cl
	movb	%cl, 2227(%rax)
	movb	156(%rsp), %cl
	movb	%cl, 2228(%rax)
	movb	157(%rsp), %cl
	movb	%cl, 2229(%rax)
	movb	158(%rsp), %cl
	movb	%cl, 2230(%rax)
	movb	159(%rsp), %cl
	movb	%cl, 2231(%rax)
	movb	160(%rsp), %cl
	movb	%cl, 2232(%rax)
	movb	161(%rsp), %cl
	movb	%cl, 2233(%rax)
	movb	162(%rsp), %cl
	movb	%cl, 2234(%rax)
	movb	163(%rsp), %cl
	movb	%cl, 2235(%rax)
	movb	164(%rsp), %cl
	movb	%cl, 2236(%rax)
	movb	165(%rsp), %cl
	movb	%cl, 2237(%rax)
	movb	166(%rsp), %cl
	movb	%cl, 2238(%rax)
	movb	167(%rsp), %cl
	movb	%cl, 2239(%rax)
	movb	168(%rsp), %cl
	movb	%cl, 2240(%rax)
	movb	169(%rsp), %cl
	movb	%cl, 2241(%rax)
	movb	170(%rsp), %cl
	movb	%cl, 2242(%rax)
	movb	171(%rsp), %cl
	movb	%cl, 2243(%rax)
	movb	172(%rsp), %cl
	movb	%cl, 2244(%rax)
	movb	173(%rsp), %cl
	movb	%cl, 2245(%rax)
	movb	174(%rsp), %cl
	movb	%cl, 2246(%rax)
	movb	175(%rsp), %cl
	movb	%cl, 2247(%rax)
	movb	176(%rsp), %cl
	movb	%cl, 2248(%rax)
	movb	177(%rsp), %cl
	movb	%cl, 2249(%rax)
	movb	178(%rsp), %cl
	movb	%cl, 2250(%rax)
	movb	179(%rsp), %cl
	movb	%cl, 2251(%rax)
	movb	180(%rsp), %cl
	movb	%cl, 2252(%rax)
	movb	181(%rsp), %cl
	movb	%cl, 2253(%rax)
	movb	182(%rsp), %cl
	movb	%cl, 2254(%rax)
	movb	183(%rsp), %cl
	movb	%cl, 2255(%rax)
	movb	184(%rsp), %cl
	movb	%cl, 2256(%rax)
	movb	185(%rsp), %cl
	movb	%cl, 2257(%rax)
	movb	186(%rsp), %cl
	movb	%cl, 2258(%rax)
	movb	187(%rsp), %cl
	movb	%cl, 2259(%rax)
	movb	188(%rsp), %cl
	movb	%cl, 2260(%rax)
	movb	189(%rsp), %cl
	movb	%cl, 2261(%rax)
	movb	190(%rsp), %cl
	movb	%cl, 2262(%rax)
	movb	191(%rsp), %cl
	movb	%cl, 2263(%rax)
	movb	192(%rsp), %cl
	movb	%cl, 2264(%rax)
	movb	193(%rsp), %cl
	movb	%cl, 2265(%rax)
	movb	194(%rsp), %cl
	movb	%cl, 2266(%rax)
	movb	195(%rsp), %cl
	movb	%cl, 2267(%rax)
	movb	196(%rsp), %cl
	movb	%cl, 2268(%rax)
	movb	197(%rsp), %cl
	movb	%cl, 2269(%rax)
	movb	198(%rsp), %cl
	movb	%cl, 2270(%rax)
	movb	199(%rsp), %cl
	movb	%cl, 2271(%rax)
	movb	200(%rsp), %cl
	movb	%cl, 2272(%rax)
	movb	201(%rsp), %cl
	movb	%cl, 2273(%rax)
	movb	202(%rsp), %cl
	movb	%cl, 2274(%rax)
	movb	203(%rsp), %cl
	movb	%cl, 2275(%rax)
	movb	204(%rsp), %cl
	movb	%cl, 2276(%rax)
	movb	205(%rsp), %cl
	movb	%cl, 2277(%rax)
	movb	206(%rsp), %cl
	movb	%cl, 2278(%rax)
	movb	207(%rsp), %cl
	movb	%cl, 2279(%rax)
	movb	208(%rsp), %cl
	movb	%cl, 2280(%rax)
	movb	209(%rsp), %cl
	movb	%cl, 2281(%rax)
	movb	210(%rsp), %cl
	movb	%cl, 2282(%rax)
	movb	211(%rsp), %cl
	movb	%cl, 2283(%rax)
	movb	212(%rsp), %cl
	movb	%cl, 2284(%rax)
	movb	213(%rsp), %cl
	movb	%cl, 2285(%rax)
	movb	214(%rsp), %cl
	movb	%cl, 2286(%rax)
	movb	215(%rsp), %cl
	movb	%cl, 2287(%rax)
	movb	216(%rsp), %cl
	movb	%cl, 2288(%rax)
	movb	217(%rsp), %cl
	movb	%cl, 2289(%rax)
	movb	218(%rsp), %cl
	movb	%cl, 2290(%rax)
	movb	219(%rsp), %cl
	movb	%cl, 2291(%rax)
	movb	220(%rsp), %cl
	movb	%cl, 2292(%rax)
	movb	221(%rsp), %cl
	movb	%cl, 2293(%rax)
	movb	222(%rsp), %cl
	movb	%cl, 2294(%rax)
	movb	223(%rsp), %cl
	movb	%cl, 2295(%rax)
	movb	224(%rsp), %cl
	movb	%cl, 2296(%rax)
	movb	225(%rsp), %cl
	movb	%cl, 2297(%rax)
	movb	226(%rsp), %cl
	movb	%cl, 2298(%rax)
	movb	227(%rsp), %cl
	movb	%cl, 2299(%rax)
	movb	228(%rsp), %cl
	movb	%cl, 2300(%rax)
	movb	229(%rsp), %cl
	movb	%cl, 2301(%rax)
	movb	230(%rsp), %cl
	movb	%cl, 2302(%rax)
	movb	231(%rsp), %cl
	movb	%cl, 2303(%rax)
	movb	232(%rsp), %cl
	movb	%cl, 2304(%rax)
	movb	233(%rsp), %cl
	movb	%cl, 2305(%rax)
	movb	234(%rsp), %cl
	movb	%cl, 2306(%rax)
	movb	235(%rsp), %cl
	movb	%cl, 2307(%rax)
	movb	236(%rsp), %cl
	movb	%cl, 2308(%rax)
	movb	237(%rsp), %cl
	movb	%cl, 2309(%rax)
	movb	238(%rsp), %cl
	movb	%cl, 2310(%rax)
	movb	239(%rsp), %cl
	movb	%cl, 2311(%rax)
	movb	240(%rsp), %cl
	movb	%cl, 2312(%rax)
	movb	241(%rsp), %cl
	movb	%cl, 2313(%rax)
	movb	242(%rsp), %cl
	movb	%cl, 2314(%rax)
	movb	243(%rsp), %cl
	movb	%cl, 2315(%rax)
	movb	244(%rsp), %cl
	movb	%cl, 2316(%rax)
	movb	245(%rsp), %cl
	movb	%cl, 2317(%rax)
	movb	246(%rsp), %cl
	movb	%cl, 2318(%rax)
	movb	247(%rsp), %cl
	movb	%cl, 2319(%rax)
	movb	248(%rsp), %cl
	movb	%cl, 2320(%rax)
	movb	249(%rsp), %cl
	movb	%cl, 2321(%rax)
	movb	250(%rsp), %cl
	movb	%cl, 2322(%rax)
	movb	251(%rsp), %cl
	movb	%cl, 2323(%rax)
	movb	252(%rsp), %cl
	movb	%cl, 2324(%rax)
	movb	253(%rsp), %cl
	movb	%cl, 2325(%rax)
	movb	254(%rsp), %cl
	movb	%cl, 2326(%rax)
	movb	255(%rsp), %cl
	movb	%cl, 2327(%rax)
	movb	256(%rsp), %cl
	movb	%cl, 2328(%rax)
	movb	257(%rsp), %cl
	movb	%cl, 2329(%rax)
	movb	258(%rsp), %cl
	movb	%cl, 2330(%rax)
	movb	259(%rsp), %cl
	movb	%cl, 2331(%rax)
	movb	260(%rsp), %cl
	movb	%cl, 2332(%rax)
	movb	261(%rsp), %cl
	movb	%cl, 2333(%rax)
	movb	262(%rsp), %cl
	movb	%cl, 2334(%rax)
	movb	263(%rsp), %cl
	movb	%cl, 2335(%rax)
	movb	264(%rsp), %cl
	movb	%cl, 2336(%rax)
	movb	265(%rsp), %cl
	movb	%cl, 2337(%rax)
	movb	266(%rsp), %cl
	movb	%cl, 2338(%rax)
	movb	267(%rsp), %cl
	movb	%cl, 2339(%rax)
	movb	268(%rsp), %cl
	movb	%cl, 2340(%rax)
	movb	269(%rsp), %cl
	movb	%cl, 2341(%rax)
	movb	270(%rsp), %cl
	movb	%cl, 2342(%rax)
	movb	271(%rsp), %cl
	movb	%cl, 2343(%rax)
	movb	272(%rsp), %cl
	movb	%cl, 2344(%rax)
	movb	273(%rsp), %cl
	movb	%cl, 2345(%rax)
	movb	274(%rsp), %cl
	movb	%cl, 2346(%rax)
	movb	275(%rsp), %cl
	movb	%cl, 2347(%rax)
	movb	276(%rsp), %cl
	movb	%cl, 2348(%rax)
	movb	277(%rsp), %cl
	movb	%cl, 2349(%rax)
	movb	278(%rsp), %cl
	movb	%cl, 2350(%rax)
	movb	279(%rsp), %cl
	movb	%cl, 2351(%rax)
	movb	280(%rsp), %cl
	movb	%cl, 2352(%rax)
	movb	281(%rsp), %cl
	movb	%cl, 2353(%rax)
	movb	282(%rsp), %cl
	movb	%cl, 2354(%rax)
	movb	283(%rsp), %cl
	movb	%cl, 2355(%rax)
	movb	284(%rsp), %cl
	movb	%cl, 2356(%rax)
	movb	285(%rsp), %cl
	movb	%cl, 2357(%rax)
	movb	286(%rsp), %cl
	movb	%cl, 2358(%rax)
	movb	287(%rsp), %cl
	movb	%cl, 2359(%rax)
	movb	288(%rsp), %cl
	movb	%cl, 2360(%rax)
	movb	289(%rsp), %cl
	movb	%cl, 2361(%rax)
	movb	290(%rsp), %cl
	movb	%cl, 2362(%rax)
	movb	291(%rsp), %cl
	movb	%cl, 2363(%rax)
	movb	292(%rsp), %cl
	movb	%cl, 2364(%rax)
	movb	293(%rsp), %cl
	movb	%cl, 2365(%rax)
	movb	294(%rsp), %cl
	movb	%cl, 2366(%rax)
	movb	295(%rsp), %cl
	movb	%cl, 2367(%rax)
	movb	296(%rsp), %cl
	movb	%cl, 2368(%rax)
	movb	297(%rsp), %cl
	movb	%cl, 2369(%rax)
	movb	298(%rsp), %cl
	movb	%cl, 2370(%rax)
	movb	299(%rsp), %cl
	movb	%cl, 2371(%rax)
	movb	300(%rsp), %cl
	movb	%cl, 2372(%rax)
	movb	301(%rsp), %cl
	movb	%cl, 2373(%rax)
	movb	302(%rsp), %cl
	movb	%cl, 2374(%rax)
	movb	303(%rsp), %cl
	movb	%cl, 2375(%rax)
	movb	304(%rsp), %cl
	movb	%cl, 2376(%rax)
	movb	305(%rsp), %cl
	movb	%cl, 2377(%rax)
	movb	306(%rsp), %cl
	movb	%cl, 2378(%rax)
	movb	307(%rsp), %cl
	movb	%cl, 2379(%rax)
	movb	308(%rsp), %cl
	movb	%cl, 2380(%rax)
	movb	309(%rsp), %cl
	movb	%cl, 2381(%rax)
	movb	310(%rsp), %cl
	movb	%cl, 2382(%rax)
	movb	311(%rsp), %cl
	movb	%cl, 2383(%rax)
	movb	312(%rsp), %cl
	movb	%cl, 2384(%rax)
	movb	313(%rsp), %cl
	movb	%cl, 2385(%rax)
	movb	314(%rsp), %cl
	movb	%cl, 2386(%rax)
	movb	315(%rsp), %cl
	movb	%cl, 2387(%rax)
	movb	316(%rsp), %cl
	movb	%cl, 2388(%rax)
	movb	317(%rsp), %cl
	movb	%cl, 2389(%rax)
	movb	318(%rsp), %cl
	movb	%cl, 2390(%rax)
	movb	319(%rsp), %cl
	movb	%cl, 2391(%rax)
	movb	320(%rsp), %cl
	movb	%cl, 2392(%rax)
	movb	321(%rsp), %cl
	movb	%cl, 2393(%rax)
	movb	322(%rsp), %cl
	movb	%cl, 2394(%rax)
	movb	323(%rsp), %cl
	movb	%cl, 2395(%rax)
	movb	324(%rsp), %cl
	movb	%cl, 2396(%rax)
	movb	325(%rsp), %cl
	movb	%cl, 2397(%rax)
	movb	326(%rsp), %cl
	movb	%cl, 2398(%rax)
	movb	327(%rsp), %cl
	movb	%cl, 2399(%rax)
	movb	328(%rsp), %cl
	movb	%cl, 2400(%rax)
	movb	329(%rsp), %cl
	movb	%cl, 2401(%rax)
	movb	330(%rsp), %cl
	movb	%cl, 2402(%rax)
	movb	331(%rsp), %cl
	movb	%cl, 2403(%rax)
	movb	332(%rsp), %cl
	movb	%cl, 2404(%rax)
	movb	333(%rsp), %cl
	movb	%cl, 2405(%rax)
	movb	334(%rsp), %cl
	movb	%cl, 2406(%rax)
	movb	335(%rsp), %cl
	movb	%cl, 2407(%rax)
	movb	336(%rsp), %cl
	movb	%cl, 2408(%rax)
	movb	337(%rsp), %cl
	movb	%cl, 2409(%rax)
	movb	338(%rsp), %cl
	movb	%cl, 2410(%rax)
	movb	339(%rsp), %cl
	movb	%cl, 2411(%rax)
	movb	340(%rsp), %cl
	movb	%cl, 2412(%rax)
	movb	341(%rsp), %cl
	movb	%cl, 2413(%rax)
	movb	342(%rsp), %cl
	movb	%cl, 2414(%rax)
	movb	343(%rsp), %cl
	movb	%cl, 2415(%rax)
	movb	344(%rsp), %cl
	movb	%cl, 2416(%rax)
	movb	345(%rsp), %cl
	movb	%cl, 2417(%rax)
	movb	346(%rsp), %cl
	movb	%cl, 2418(%rax)
	movb	347(%rsp), %cl
	movb	%cl, 2419(%rax)
	movb	348(%rsp), %cl
	movb	%cl, 2420(%rax)
	movb	349(%rsp), %cl
	movb	%cl, 2421(%rax)
	movb	350(%rsp), %cl
	movb	%cl, 2422(%rax)
	movb	351(%rsp), %cl
	movb	%cl, 2423(%rax)
	movb	352(%rsp), %cl
	movb	%cl, 2424(%rax)
	movb	353(%rsp), %cl
	movb	%cl, 2425(%rax)
	movb	354(%rsp), %cl
	movb	%cl, 2426(%rax)
	movb	355(%rsp), %cl
	movb	%cl, 2427(%rax)
	movb	356(%rsp), %cl
	movb	%cl, 2428(%rax)
	movb	357(%rsp), %cl
	movb	%cl, 2429(%rax)
	movb	358(%rsp), %cl
	movb	%cl, 2430(%rax)
	movb	359(%rsp), %cl
	movb	%cl, 2431(%rax)
	movb	360(%rsp), %cl
	movb	%cl, 2432(%rax)
	movb	361(%rsp), %cl
	movb	%cl, 2433(%rax)
	movb	362(%rsp), %cl
	movb	%cl, 2434(%rax)
	movb	363(%rsp), %cl
	movb	%cl, 2435(%rax)
	movb	364(%rsp), %cl
	movb	%cl, 2436(%rax)
	movb	365(%rsp), %cl
	movb	%cl, 2437(%rax)
	movb	366(%rsp), %cl
	movb	%cl, 2438(%rax)
	movb	367(%rsp), %cl
	movb	%cl, 2439(%rax)
	movb	368(%rsp), %cl
	movb	%cl, 2440(%rax)
	movb	369(%rsp), %cl
	movb	%cl, 2441(%rax)
	movb	370(%rsp), %cl
	movb	%cl, 2442(%rax)
	movb	371(%rsp), %cl
	movb	%cl, 2443(%rax)
	movb	372(%rsp), %cl
	movb	%cl, 2444(%rax)
	movb	373(%rsp), %cl
	movb	%cl, 2445(%rax)
	movb	374(%rsp), %cl
	movb	%cl, 2446(%rax)
	movb	375(%rsp), %cl
	movb	%cl, 2447(%rax)
	movb	376(%rsp), %cl
	movb	%cl, 2448(%rax)
	movb	377(%rsp), %cl
	movb	%cl, 2449(%rax)
	movb	378(%rsp), %cl
	movb	%cl, 2450(%rax)
	movb	379(%rsp), %cl
	movb	%cl, 2451(%rax)
	movb	380(%rsp), %cl
	movb	%cl, 2452(%rax)
	movb	381(%rsp), %cl
	movb	%cl, 2453(%rax)
	movb	382(%rsp), %cl
	movb	%cl, 2454(%rax)
	movb	383(%rsp), %cl
	movb	%cl, 2455(%rax)
	movb	384(%rsp), %cl
	movb	%cl, 2456(%rax)
	movb	385(%rsp), %cl
	movb	%cl, 2457(%rax)
	movb	386(%rsp), %cl
	movb	%cl, 2458(%rax)
	movb	387(%rsp), %cl
	movb	%cl, 2459(%rax)
	movb	388(%rsp), %cl
	movb	%cl, 2460(%rax)
	movb	389(%rsp), %cl
	movb	%cl, 2461(%rax)
	movb	390(%rsp), %cl
	movb	%cl, 2462(%rax)
	movb	391(%rsp), %cl
	movb	%cl, 2463(%rax)
	movq	2816(%rsp), %rbx
	movq	2824(%rsp), %rbp
	movq	2832(%rsp), %r12
	movq	2840(%rsp), %r13
	movq	2848(%rsp), %r14
	movq	2856(%rsp), %r15
	movq	2864(%rsp), %rsp
	ret
_build_auth_path_jazz:
build_auth_path_jazz:
	movq	%rsp, %rax
	leaq	-96(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 40(%rsp)
	movq	%rbp, 48(%rsp)
	movq	%r12, 56(%rsp)
	movq	%r13, 64(%rsp)
	movq	%r14, 72(%rsp)
	movq	%r15, 80(%rsp)
	movq	%rax, 88(%rsp)
	movl	%ecx, 32(%rsp)
	movq	%rdi, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%r8, 24(%rsp)
	movl	32(%rsp), %eax
	shrl	$0, %eax
	xorl	$1, %eax
	shll	$0, %eax
	movq	(%rsp), %rcx
	movq	%rcx, %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$0, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$10:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$1, %eax
	xorl	$1, %eax
	shll	$1, %eax
	movq	(%rsp), %rcx
	leaq	32(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$1, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$9:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$2, %eax
	xorl	$1, %eax
	shll	$2, %eax
	movq	(%rsp), %rcx
	leaq	64(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$2, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$8:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$3, %eax
	xorl	$1, %eax
	shll	$3, %eax
	movq	(%rsp), %rcx
	leaq	96(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$3, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$7:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$4, %eax
	xorl	$1, %eax
	shll	$4, %eax
	movq	(%rsp), %rcx
	leaq	128(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$4, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$6:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$5, %eax
	xorl	$1, %eax
	shll	$5, %eax
	movq	(%rsp), %rcx
	leaq	160(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$5, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$5:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$6, %eax
	xorl	$1, %eax
	shll	$6, %eax
	movq	(%rsp), %rcx
	leaq	192(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$6, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$4:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$7, %eax
	xorl	$1, %eax
	shll	$7, %eax
	movq	(%rsp), %rcx
	leaq	224(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$7, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$3:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$8, %eax
	xorl	$1, %eax
	shll	$8, %eax
	movq	(%rsp), %rcx
	leaq	256(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$8, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$2:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rax
	movq	%rax, (%rsp)
	movl	32(%rsp), %eax
	shrl	$9, %eax
	xorl	$1, %eax
	shll	$9, %eax
	movq	(%rsp), %rcx
	leaq	288(%rcx), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %r9
	movl	$9, %r8d
	movl	%eax, %ecx
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Lbuild_auth_path_jazz$1:
	leaq	640(%rsp), %rsp
	movq	40(%rsp), %rbx
	movq	48(%rsp), %rbp
	movq	56(%rsp), %r12
	movq	64(%rsp), %r13
	movq	72(%rsp), %r14
	movq	80(%rsp), %r15
	movq	88(%rsp), %rsp
	ret
_treehash_jazz:
treehash_jazz:
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
	leaq	-640(%rsp), %rsp
	call	L_treehash$1
Ltreehash_jazz$1:
	leaq	640(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret
_treehash_cond_jazz:
treehash_cond_jazz:
	cmpq	$2, %rsi
	setnb	%al
	cmpb	$0, %al
	je  	Ltreehash_cond_jazz$1
	movl	-4(%rdi,%rsi,4), %eax
	movl	-8(%rdi,%rsi,4), %ecx
	cmpl	%ecx, %eax
	sete	%al
Ltreehash_cond_jazz$1:
	ret
L_treehash$1:
	movq	$0, %rax
	movq	%rdi, 8(%rsp)
	movq	%rax, 16(%rsp)
	movl	%ecx, 560(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	(%r9), %rax
	movq	%rax, 48(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 56(%rsp)
	movq	16(%r9), %rax
	movq	%rax, 64(%rsp)
	movq	24(%r9), %rax
	movq	%rax, 72(%rsp)
	movq	(%r9), %rax
	movq	%rax, 80(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 88(%rsp)
	movq	16(%r9), %rax
	movq	%rax, 96(%rsp)
	movq	24(%r9), %rax
	movq	%rax, 104(%rsp)
	movq	(%r9), %rax
	movq	%rax, 112(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 120(%rsp)
	movq	16(%r9), %rax
	movq	%rax, 128(%rsp)
	movq	24(%r9), %rax
	movq	%rax, 136(%rsp)
	leaq	48(%rsp), %rax
	movl	$0, %ecx
	movl	%ecx, 12(%rax)
	leaq	80(%rsp), %rax
	movl	$1, %ecx
	movl	%ecx, 12(%rax)
	leaq	112(%rsp), %rax
	movl	$2, %ecx
	movl	%ecx, 12(%rax)
	movl	%r8d, %ecx
	movl	$0, %edx
	movl	$1, %eax
	shll	%cl, %eax
	jmp 	L_treehash$2
L_treehash$3:
	movl	%edx, 564(%rsp)
	movl	%eax, 568(%rsp)
	movl	560(%rsp), %eax
	addl	%edx, %eax
	leaq	80(%rsp), %rcx
	movl	%eax, 16(%rcx)
	leaq	48(%rsp), %rcx
	movl	%eax, 16(%rcx)
	movq	24(%rsp), %rax
	movq	32(%rsp), %rcx
	leaq	572(%rsp), %rdx
	leaq	80(%rsp), %rsi
	leaq	48(%rsp), %rdi
	leaq	-2184(%rsp), %rsp
	call	L_gen_leaf_wots$1
L_treehash$11:
	leaq	2184(%rsp), %rsp
	movq	16(%rsp), %rax
	shlq	$5, %rax
	leaq	208(%rsp), %rcx
	leaq	572(%rsp), %rdx
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
	movq	16(%rsp), %rax
	incq	%rax
	movl	$0, 600(%rsp,%rax,4)
	movq	%rax, 16(%rsp)
	jmp 	L_treehash$4
L_treehash$5:
	movl	560(%rsp), %ecx
	movl	564(%rsp), %edx
	movl	%ecx, %esi
	addl	%edx, %esi
	movl	600(%rsp,%rax,4), %ecx
	incl	%ecx
	shrl	%cl, %esi
	leaq	112(%rsp), %rcx
	movl	600(%rsp,%rax,4), %eax
	movl	%eax, 20(%rcx)
	leaq	112(%rsp), %rax
	movl	%esi, 24(%rax)
	movq	16(%rsp), %rax
	addq	$-2, %rax
	shlq	$5, %rax
	movq	%rax, 40(%rsp)
	leaq	144(%rsp), %rcx
	leaq	208(%rsp), %rdx
	movq	$64, %rsi
	movq	$0, %rdi
	jmp 	L_treehash$9
L_treehash$10:
	movb	(%rdx,%rax), %r8b
	movb	%r8b, (%rcx,%rdi)
	incq	%rdi
	incq	%rax
L_treehash$9:
	cmpq	%rsi, %rdi
	jb  	L_treehash$10
	movq	32(%rsp), %r8
	leaq	572(%rsp), %rcx
	leaq	144(%rsp), %rdx
	leaq	112(%rsp), %rax
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_treehash$8:
	leaq	384(%rsp), %rsp
	movq	40(%rsp), %rax
	leaq	208(%rsp), %rcx
	leaq	572(%rsp), %rdx
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
	movq	16(%rsp), %rax
	addq	$-1, %rax
	incl	600(%rsp,%rax,4)
	movq	%rax, 16(%rsp)
L_treehash$4:
	leaq	604(%rsp), %rcx
	cmpq	$2, %rax
	setnb	%dl
	cmpb	$0, %dl
	je  	L_treehash$6
	movl	-4(%rcx,%rax,4), %edx
	movl	-8(%rcx,%rax,4), %ecx
	cmpl	%ecx, %edx
	sete	%cl
	jmp 	L_treehash$7
L_treehash$6:
	movb	%dl, %cl
L_treehash$7:
	cmpb	$1, %cl
	je  	L_treehash$5
	movl	564(%rsp), %edx
	movl	568(%rsp), %eax
	incl	%edx
L_treehash$2:
	cmpl	%eax, %edx
	jb  	L_treehash$3
	movq	8(%rsp), %rax
	movq	208(%rsp), %rcx
	movq	%rcx, (%rax)
	movq	216(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	224(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	232(%rsp), %rcx
	movq	%rcx, 24(%rax)
	ret
L_gen_leaf_wots$1:
	movq	%rdx, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rsi, 24(%rsp)
	leaq	48(%rsp), %rdx
	movq	%rcx, 32(%rsp)
	movq	%rdx, %r8
	movq	%rax, %r9
	movq	%rdi, %rsi
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
L_gen_leaf_wots$70:
	leaq	88(%rsp), %rsp
	movq	%rcx, %rsi
	movq	%rax, 40(%rsp)
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	movq	%r13, %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$69:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$1, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	32(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$68:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$2, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	64(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$67:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$3, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	96(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$66:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$4, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	128(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$65:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$5, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	160(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$64:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$6, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	192(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$63:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$7, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	224(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$62:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$8, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	256(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$61:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$9, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	288(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$60:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$10, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	320(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$59:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$11, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	352(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$58:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$12, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	384(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$57:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$13, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	416(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$56:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$14, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	448(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$55:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$15, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	480(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$54:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$16, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	512(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$53:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$17, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	544(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$52:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$18, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	576(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$51:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$19, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	608(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$50:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$20, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	640(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$49:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$21, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	672(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$48:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$22, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	704(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$47:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$23, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	736(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$46:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$24, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	768(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$45:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$25, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	800(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$44:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$26, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	832(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$43:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$27, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	864(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$42:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$28, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	896(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$41:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$29, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	928(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$40:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$30, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	960(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$39:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$31, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	992(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$38:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$32, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1024(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$37:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$33, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1056(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$36:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$34, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1088(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$35:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$35, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1120(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$34:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$36, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1152(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$33:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$37, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1184(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$32:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$38, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1216(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$31:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$39, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1248(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$30:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$40, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1280(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$29:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$41, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1312(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$28:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$42, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1344(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$27:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$43, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1376(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$26:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$44, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1408(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$25:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$45, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1440(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$24:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$46, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1472(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$23:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$47, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1504(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$22:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$48, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1536(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$21:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$49, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1568(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$20:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$50, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1600(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$19:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$51, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1632(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$18:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$52, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1664(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$17:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$53, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1696(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$16:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$54, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1728(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$15:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$55, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1760(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$14:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$56, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1792(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$13:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$57, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1824(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$12:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$58, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1856(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$11:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$59, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1888(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$10:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$60, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1920(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$9:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$61, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1952(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$8:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$62, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	1984(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$7:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$63, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	2016(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$6:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$64, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	2048(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$5:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$65, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	2080(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$4:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 40(%rsp)
	movl	$66, %eax
	movl	%eax, 20(%rsi)
	movq	40(%rsp), %r13
	movq	32(%rsp), %rdx
	leaq	2112(%r13), %rdi
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
L_gen_leaf_wots$3:
	leaq	32(%rsp), %rsp
	movq	%r13, 32(%rsp)
	movq	%rax, 32(%rsp)
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
	movq	32(%rsp), %rdx
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
	movq	24(%rsp), %r8
	leaq	124(%rsp), %rcx
	leaq	56(%rsp), %rdx
	leaq	-384(%rsp), %rsp
	call	L_thash_h$1
L_l_tree$11:
	leaq	384(%rsp), %rsp
	movq	%rcx, %rax
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
	call	Lmemcpy_u8u8_N___memcpy_u8u8$1
L_l_tree$2:
	ret
L_chain_lengths$1:
	movq	%r8, %r10
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %rcx
	movb	$0, %bpl
	movb	$0, %r12b
	jmp 	L_chain_lengths$7
L_chain_lengths$8:
	cmpq	$0, %rcx
	jne 	L_chain_lengths$9
	movb	(%r9,%r11), %r12b
	incq	%r11
	addq	$8, %rcx
L_chain_lengths$9:
	addq	$-4, %rcx
	movzbl	%r12b, %r13d
	shrl	%cl, %r13d
	andl	$15, %r13d
	movl	%r13d, (%r10,%rbx,4)
	incq	%rbx
	incb	%bpl
L_chain_lengths$7:
	cmpb	$64, %bpl
	jb  	L_chain_lengths$8
	leaq	256(%r8), %r9
	movq	%r8, %rcx
	movq	$0, %r10
	movq	$0, %r11
	jmp 	L_chain_lengths$5
L_chain_lengths$6:
	movq	$15, %rbx
	movl	(%rcx,%r11,4), %ebp
	subq	%rbp, %rbx
	addq	%rbx, %r10
	incq	%r11
L_chain_lengths$5:
	cmpq	$64, %r11
	jb  	L_chain_lengths$6
	movq	$8, %rcx
	addq	$-4, %rcx
	shlq	%cl, %r10
	leaq	8(%rsp), %r11
	movb	%r10b, 1(%r11)
	shrq	$8, %r10
	movb	%r10b, (%r11)
	movq	$0, %r10
	movq	$0, %rbx
	movq	$0, %rcx
	movb	$0, %bpl
	movb	$0, %r12b
	jmp 	L_chain_lengths$2
L_chain_lengths$3:
	cmpq	$0, %rcx
	jne 	L_chain_lengths$4
	movb	(%r11,%r10), %r12b
	incq	%r10
	addq	$8, %rcx
L_chain_lengths$4:
	addq	$-4, %rcx
	movzbl	%r12b, %r13d
	shrl	%cl, %r13d
	andl	$15, %r13d
	movl	%r13d, (%r9,%rbx,4)
	incq	%rbx
	incb	%bpl
L_chain_lengths$2:
	cmpb	$3, %bpl
	jb  	L_chain_lengths$3
	ret
L_gen_chain_inplace$1:
	movq	%rdi, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movl	%eax, %edx
	addl	%ecx, %eax
	jmp 	L_gen_chain_inplace$2
L_gen_chain_inplace$3:
	movl	%edx, 32(%rsp)
	movl	%eax, 36(%rsp)
	movq	24(%rsp), %rsi
	movl	%edx, 24(%rsi)
	movl	$0, %eax
	movl	%eax, 28(%rsi)
	movq	16(%rsp), %rcx
	movq	8(%rsp), %rax
	movq	%rsi, %rdx
	leaq	-320(%rsp), %rsp
	call	L_thash_f$1
L_gen_chain_inplace$4:
	leaq	320(%rsp), %rsp
	movq	%rax, %rdi
	movl	32(%rsp), %edx
	movl	36(%rsp), %eax
	incl	%edx
L_gen_chain_inplace$2:
	cmpl	%eax, %edx
	jb  	L_gen_chain_inplace$3
	movq	24(%rsp), %rax
	ret
L_expand_seed$1:
	movq	%r8, 8(%rsp)
	movq	%r9, 16(%rsp)
	movl	$0, %eax
	movl	%eax, 24(%rsi)
	movl	$0, %eax
	movl	%eax, 28(%rsi)
	leaq	32(%rsp), %rax
	call	Lcopy_nbytes$1
L_expand_seed$69:
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	%rsi, 24(%rsp)
	leaq	64(%rsp), %rax
	movq	%rax, %rcx
	movl	(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	4(%rax), %rcx
	movl	4(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	8(%rax), %rcx
	movl	8(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	12(%rax), %rcx
	movl	12(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	16(%rax), %rcx
	movl	16(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	20(%rax), %rcx
	movl	20(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	24(%rax), %rcx
	movl	24(%rsi), %edx
	bswapl	%edx
	movl	%edx, (%rcx)
	leaq	28(%rax), %rax
	movl	28(%rsi), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	movq	%r13, %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$68:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	32(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$67:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	64(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$66:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	96(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$65:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	128(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$64:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	160(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$63:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	192(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$62:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	224(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$61:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	256(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$60:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	288(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$59:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	320(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$58:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	352(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$57:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	384(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$56:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	416(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$55:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	448(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$54:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	480(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$53:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	512(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$52:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	544(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$51:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	576(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$50:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	608(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$49:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	640(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$48:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	672(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$47:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	704(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$46:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	736(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$45:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	768(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$44:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	800(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$43:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	832(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$42:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	864(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$41:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	896(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$40:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	928(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$39:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	960(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$38:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	992(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$37:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1024(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$36:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1056(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$35:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1088(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$34:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1120(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$33:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1152(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$32:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1184(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$31:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1216(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$30:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1248(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$29:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1280(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$28:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1312(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$27:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1344(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$26:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1376(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$25:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1408(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$24:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1440(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$23:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1472(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$22:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1504(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$21:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1536(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$20:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1568(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$19:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1600(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$18:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1632(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$17:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1664(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$16:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1696(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$15:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1728(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$14:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1760(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$13:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1792(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$12:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1824(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$11:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1856(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$10:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1888(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$9:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1920(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$8:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1952(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$7:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	1984(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$6:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	2016(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$5:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	2048(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$4:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	2080(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$3:
	leaq	312(%rsp), %rsp
	movq	%r13, 8(%rsp)
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
	movq	8(%rsp), %r13
	movq	16(%rsp), %rcx
	leaq	2112(%r13), %rsi
	leaq	32(%rsp), %rdi
	leaq	-312(%rsp), %rsp
	call	L_prf_keygen$1
L_expand_seed$2:
	leaq	312(%rsp), %rsp
	movq	%r13, 16(%rsp)
	movq	24(%rsp), %rcx
	movq	16(%rsp), %rax
	ret
L_thash_f$1:
	leaq	40(%rsp), %rsi
	movq	%rsi, %rdi
	movl	(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	4(%rsi), %rdi
	movl	4(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	8(%rsi), %rdi
	movl	8(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	12(%rsi), %rdi
	movl	12(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	16(%rsi), %rdi
	movl	16(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	20(%rsi), %rdi
	movl	20(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	24(%rsi), %rdi
	movl	24(%rdx), %r8d
	bswapl	%r8d
	movl	%r8d, (%rdi)
	leaq	28(%rsi), %rsi
	movl	28(%rdx), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	leaq	104(%rsp), %rsi
	movq	$0, %rdi
	movb	%dil, 31(%rsi)
	shrq	$8, %rdi
	movb	%dil, 30(%rsi)
	shrq	$8, %rdi
	movb	%dil, 29(%rsi)
	shrq	$8, %rdi
	movb	%dil, 28(%rsi)
	shrq	$8, %rdi
	movb	%dil, 27(%rsi)
	shrq	$8, %rdi
	movb	%dil, 26(%rsi)
	shrq	$8, %rdi
	movb	%dil, 25(%rsi)
	shrq	$8, %rdi
	movb	%dil, 24(%rsi)
	shrq	$8, %rdi
	movb	%dil, 23(%rsi)
	shrq	$8, %rdi
	movb	%dil, 22(%rsi)
	shrq	$8, %rdi
	movb	%dil, 21(%rsi)
	shrq	$8, %rdi
	movb	%dil, 20(%rsi)
	shrq	$8, %rdi
	movb	%dil, 19(%rsi)
	shrq	$8, %rdi
	movb	%dil, 18(%rsi)
	shrq	$8, %rdi
	movb	%dil, 17(%rsi)
	shrq	$8, %rdi
	movb	%dil, 16(%rsi)
	shrq	$8, %rdi
	movb	%dil, 15(%rsi)
	shrq	$8, %rdi
	movb	%dil, 14(%rsi)
	shrq	$8, %rdi
	movb	%dil, 13(%rsi)
	shrq	$8, %rdi
	movb	%dil, 12(%rsi)
	shrq	$8, %rdi
	movb	%dil, 11(%rsi)
	shrq	$8, %rdi
	movb	%dil, 10(%rsi)
	shrq	$8, %rdi
	movb	%dil, 9(%rsi)
	shrq	$8, %rdi
	movb	%dil, 8(%rsi)
	shrq	$8, %rdi
	movb	%dil, 7(%rsi)
	shrq	$8, %rdi
	movb	%dil, 6(%rsi)
	shrq	$8, %rdi
	movb	%dil, 5(%rsi)
	shrq	$8, %rdi
	movb	%dil, 4(%rsi)
	shrq	$8, %rdi
	movb	%dil, 3(%rsi)
	shrq	$8, %rdi
	movb	%dil, 2(%rsi)
	shrq	$8, %rdi
	movb	%dil, 1(%rsi)
	shrq	$8, %rdi
	movb	%dil, (%rsi)
	movq	%rax, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rcx, 24(%rsp)
	leaq	136(%rsp), %rsi
	leaq	40(%rsp), %rdi
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
	leaq	72(%rsp), %rsi
	leaq	40(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_prf$1
L_thash_f$12:
	leaq	280(%rsp), %rsp
	movq	8(%rsp), %rcx
	movq	$0, %rax
	jmp 	L_thash_f$10
L_thash_f$11:
	movq	(%rcx,%rax,8), %rdx
	xorq	72(%rsp,%rax,8), %rdx
	movq	%rdx, 168(%rsp,%rax,8)
	incq	%rax
L_thash_f$10:
	cmpq	$4, %rax
	jb  	L_thash_f$11
	leaq	104(%rsp), %rax
	movq	%rcx, 8(%rsp)
	movq	$96, %rcx
	shlq	$3, %rcx
	movq	%rcx, 24(%rsp)
	movl	$1779033703, 72(%rsp)
	movl	$-1150833019, 76(%rsp)
	movl	$1013904242, 80(%rsp)
	movl	$-1521486534, 84(%rsp)
	movl	$1359893119, 88(%rsp)
	movl	$-1694144372, 92(%rsp)
	movl	$528734635, 96(%rsp)
	movl	$1541459225, 100(%rsp)
	movq	%rax, 32(%rsp)
	leaq	72(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_thash_f$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rax
	movq	24(%rsp), %rcx
	movq	$32, %rsi
	movq	$0, %rdi
	movl	%edi, 200(%rsp)
	movl	%edi, 204(%rsp)
	movl	%edi, 208(%rsp)
	movl	%edi, 212(%rsp)
	movl	%edi, 216(%rsp)
	movl	%edi, 220(%rsp)
	movl	%edi, 224(%rsp)
	movl	%edi, 228(%rsp)
	movl	%edi, 232(%rsp)
	movl	%edi, 236(%rsp)
	movl	%edi, 240(%rsp)
	movl	%edi, 244(%rsp)
	movl	%edi, 248(%rsp)
	movl	%edi, 252(%rsp)
	movl	%edi, 256(%rsp)
	movl	%edi, 260(%rsp)
	movl	%edi, 264(%rsp)
	movl	%edi, 268(%rsp)
	movl	%edi, 272(%rsp)
	movl	%edi, 276(%rsp)
	movl	%edi, 280(%rsp)
	movl	%edi, 284(%rsp)
	movl	%edi, 288(%rsp)
	movl	%edi, 292(%rsp)
	movl	%edi, 296(%rsp)
	movl	%edi, 300(%rsp)
	movl	%edi, 304(%rsp)
	movl	%edi, 308(%rsp)
	movl	%edi, 312(%rsp)
	movl	%edi, 316(%rsp)
	movl	%edi, 320(%rsp)
	movl	%edi, 324(%rsp)
	jmp 	L_thash_f$7
L_thash_f$8:
	movq	%rdx, %r8
	addq	%rdi, %r8
	movb	(%rax,%r8), %r8b
	movb	%r8b, 200(%rsp,%rdi)
	incq	%rdi
L_thash_f$7:
	cmpq	%rsi, %rdi
	jb  	L_thash_f$8
	movb	$128, 200(%rsp,%rdi)
	cmpq	$56, %rsi
	jb  	L_thash_f$5
	movq	$120, %rsi
	movq	$2, %rax
	movq	$127, %rdx
	jmp 	L_thash_f$3
L_thash_f$5:
	movq	$56, %rsi
	movq	$1, %rax
	movq	$63, %rdx
L_thash_f$6:
	jmp 	L_thash_f$3
L_thash_f$4:
	movb	%cl, 200(%rsp,%rdx)
	shrq	$8, %rcx
	addq	$-1, %rdx
L_thash_f$3:
	cmpq	%rsi, %rdx
	jnb 	L_thash_f$4
	leaq	200(%rsp), %rsi
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
	leaq	136(%rsp), %rsi
	movq	$1, %rdi
	movb	%dil, 31(%rsi)
	shrq	$8, %rdi
	movb	%dil, 30(%rsi)
	shrq	$8, %rdi
	movb	%dil, 29(%rsi)
	shrq	$8, %rdi
	movb	%dil, 28(%rsi)
	shrq	$8, %rdi
	movb	%dil, 27(%rsi)
	shrq	$8, %rdi
	movb	%dil, 26(%rsi)
	shrq	$8, %rdi
	movb	%dil, 25(%rsi)
	shrq	$8, %rdi
	movb	%dil, 24(%rsi)
	shrq	$8, %rdi
	movb	%dil, 23(%rsi)
	shrq	$8, %rdi
	movb	%dil, 22(%rsi)
	shrq	$8, %rdi
	movb	%dil, 21(%rsi)
	shrq	$8, %rdi
	movb	%dil, 20(%rsi)
	shrq	$8, %rdi
	movb	%dil, 19(%rsi)
	shrq	$8, %rdi
	movb	%dil, 18(%rsi)
	shrq	$8, %rdi
	movb	%dil, 17(%rsi)
	shrq	$8, %rdi
	movb	%dil, 16(%rsi)
	shrq	$8, %rdi
	movb	%dil, 15(%rsi)
	shrq	$8, %rdi
	movb	%dil, 14(%rsi)
	shrq	$8, %rdi
	movb	%dil, 13(%rsi)
	shrq	$8, %rdi
	movb	%dil, 12(%rsi)
	shrq	$8, %rdi
	movb	%dil, 11(%rsi)
	shrq	$8, %rdi
	movb	%dil, 10(%rsi)
	shrq	$8, %rdi
	movb	%dil, 9(%rsi)
	shrq	$8, %rdi
	movb	%dil, 8(%rsi)
	shrq	$8, %rdi
	movb	%dil, 7(%rsi)
	shrq	$8, %rdi
	movb	%dil, 6(%rsi)
	shrq	$8, %rdi
	movb	%dil, 5(%rsi)
	shrq	$8, %rdi
	movb	%dil, 4(%rsi)
	shrq	$8, %rdi
	movb	%dil, 3(%rsi)
	shrq	$8, %rdi
	movb	%dil, 2(%rsi)
	shrq	$8, %rdi
	movb	%dil, 1(%rsi)
	shrq	$8, %rdi
	movb	%dil, (%rsi)
	movl	$0, %esi
	movl	%esi, 28(%rax)
	leaq	40(%rsp), %rsi
	movq	%rsi, %rdi
	movl	(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	4(%rsi), %rdi
	movl	4(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	8(%rsi), %rdi
	movl	8(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	12(%rsi), %rdi
	movl	12(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	16(%rsi), %rdi
	movl	16(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	20(%rsi), %rdi
	movl	20(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	24(%rsi), %rdi
	movl	24(%rax), %r9d
	bswapl	%r9d
	movl	%r9d, (%rdi)
	leaq	28(%rsi), %rsi
	movl	28(%rax), %edi
	bswapl	%edi
	movl	%edi, (%rsi)
	movq	%rdx, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%r8, 32(%rsp)
	leaq	168(%rsp), %rsi
	leaq	40(%rsp), %rdi
	movq	%r8, %rcx
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
	leaq	72(%rsp), %rsi
	leaq	40(%rsp), %rdi
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
	leaq	104(%rsp), %rsi
	leaq	40(%rsp), %rdi
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
	leaq	40(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_thash_h$9:
	leaq	280(%rsp), %rsp
	movq	32(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	$0, %rsi
	movq	$0, %rdi
	movl	%edi, 264(%rsp)
	movl	%edi, 268(%rsp)
	movl	%edi, 272(%rsp)
	movl	%edi, 276(%rsp)
	movl	%edi, 280(%rsp)
	movl	%edi, 284(%rsp)
	movl	%edi, 288(%rsp)
	movl	%edi, 292(%rsp)
	movl	%edi, 296(%rsp)
	movl	%edi, 300(%rsp)
	movl	%edi, 304(%rsp)
	movl	%edi, 308(%rsp)
	movl	%edi, 312(%rsp)
	movl	%edi, 316(%rsp)
	movl	%edi, 320(%rsp)
	movl	%edi, 324(%rsp)
	movl	%edi, 328(%rsp)
	movl	%edi, 332(%rsp)
	movl	%edi, 336(%rsp)
	movl	%edi, 340(%rsp)
	movl	%edi, 344(%rsp)
	movl	%edi, 348(%rsp)
	movl	%edi, 352(%rsp)
	movl	%edi, 356(%rsp)
	movl	%edi, 360(%rsp)
	movl	%edi, 364(%rsp)
	movl	%edi, 368(%rsp)
	movl	%edi, 372(%rsp)
	movl	%edi, 376(%rsp)
	movl	%edi, 380(%rsp)
	movl	%edi, 384(%rsp)
	movl	%edi, 388(%rsp)
	jmp 	L_thash_h$7
L_thash_h$8:
	movq	%rdx, %r8
	addq	%rdi, %r8
	movb	(%rax,%r8), %r8b
	movb	%r8b, 264(%rsp,%rdi)
	incq	%rdi
L_thash_h$7:
	cmpq	%rsi, %rdi
	jb  	L_thash_h$8
	movb	$128, 264(%rsp,%rdi)
	cmpq	$56, %rsi
	jb  	L_thash_h$5
	movq	$120, %rsi
	movq	$2, %rax
	movq	$127, %rdx
	jmp 	L_thash_h$3
L_thash_h$5:
	movq	$56, %rsi
	movq	$1, %rax
	movq	$63, %rdx
L_thash_h$6:
	jmp 	L_thash_h$3
L_thash_h$4:
	movb	%cl, 264(%rsp,%rdx)
	shrq	$8, %rcx
	addq	$-1, %rdx
L_thash_h$3:
	cmpq	%rsi, %rdx
	jnb 	L_thash_h$4
	leaq	264(%rsp), %rsi
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
	movq	$4, %rdx
	movb	%dl, 31(%rax)
	shrq	$8, %rdx
	movb	%dl, 30(%rax)
	shrq	$8, %rdx
	movb	%dl, 29(%rax)
	shrq	$8, %rdx
	movb	%dl, 28(%rax)
	shrq	$8, %rdx
	movb	%dl, 27(%rax)
	shrq	$8, %rdx
	movb	%dl, 26(%rax)
	shrq	$8, %rdx
	movb	%dl, 25(%rax)
	shrq	$8, %rdx
	movb	%dl, 24(%rax)
	shrq	$8, %rdx
	movb	%dl, 23(%rax)
	shrq	$8, %rdx
	movb	%dl, 22(%rax)
	shrq	$8, %rdx
	movb	%dl, 21(%rax)
	shrq	$8, %rdx
	movb	%dl, 20(%rax)
	shrq	$8, %rdx
	movb	%dl, 19(%rax)
	shrq	$8, %rdx
	movb	%dl, 18(%rax)
	shrq	$8, %rdx
	movb	%dl, 17(%rax)
	shrq	$8, %rdx
	movb	%dl, 16(%rax)
	shrq	$8, %rdx
	movb	%dl, 15(%rax)
	shrq	$8, %rdx
	movb	%dl, 14(%rax)
	shrq	$8, %rdx
	movb	%dl, 13(%rax)
	shrq	$8, %rdx
	movb	%dl, 12(%rax)
	shrq	$8, %rdx
	movb	%dl, 11(%rax)
	shrq	$8, %rdx
	movb	%dl, 10(%rax)
	shrq	$8, %rdx
	movb	%dl, 9(%rax)
	shrq	$8, %rdx
	movb	%dl, 8(%rax)
	shrq	$8, %rdx
	movb	%dl, 7(%rax)
	shrq	$8, %rdx
	movb	%dl, 6(%rax)
	shrq	$8, %rdx
	movb	%dl, 5(%rax)
	shrq	$8, %rdx
	movb	%dl, 4(%rax)
	shrq	$8, %rdx
	movb	%dl, 3(%rax)
	shrq	$8, %rdx
	movb	%dl, 2(%rax)
	shrq	$8, %rdx
	movb	%dl, 1(%rax)
	shrq	$8, %rdx
	movb	%dl, (%rax)
	leaq	64(%rsp), %rax
	call	Lcopy_nbytes$1
L_prf_keygen$10:
	movq	(%rdi), %rax
	movq	%rax, 96(%rsp)
	movq	8(%rdi), %rax
	movq	%rax, 104(%rsp)
	movq	16(%rdi), %rax
	movq	%rax, 112(%rsp)
	movq	24(%rdi), %rax
	movq	%rax, 120(%rsp)
	movq	32(%rdi), %rax
	movq	%rax, 128(%rsp)
	movq	40(%rdi), %rax
	movq	%rax, 136(%rsp)
	movq	48(%rdi), %rax
	movq	%rax, 144(%rsp)
	movq	56(%rdi), %rax
	movq	%rax, 152(%rsp)
	leaq	32(%rsp), %rax
	movq	%rsi, 8(%rsp)
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
	leaq	160(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_3n___blocks_0_ref_array$1
L_prf_keygen$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	$0, %rsi
	movq	$0, %rdi
	movl	%edi, 192(%rsp)
	movl	%edi, 196(%rsp)
	movl	%edi, 200(%rsp)
	movl	%edi, 204(%rsp)
	movl	%edi, 208(%rsp)
	movl	%edi, 212(%rsp)
	movl	%edi, 216(%rsp)
	movl	%edi, 220(%rsp)
	movl	%edi, 224(%rsp)
	movl	%edi, 228(%rsp)
	movl	%edi, 232(%rsp)
	movl	%edi, 236(%rsp)
	movl	%edi, 240(%rsp)
	movl	%edi, 244(%rsp)
	movl	%edi, 248(%rsp)
	movl	%edi, 252(%rsp)
	movl	%edi, 256(%rsp)
	movl	%edi, 260(%rsp)
	movl	%edi, 264(%rsp)
	movl	%edi, 268(%rsp)
	movl	%edi, 272(%rsp)
	movl	%edi, 276(%rsp)
	movl	%edi, 280(%rsp)
	movl	%edi, 284(%rsp)
	movl	%edi, 288(%rsp)
	movl	%edi, 292(%rsp)
	movl	%edi, 296(%rsp)
	movl	%edi, 300(%rsp)
	movl	%edi, 304(%rsp)
	movl	%edi, 308(%rsp)
	movl	%edi, 312(%rsp)
	movl	%edi, 316(%rsp)
	jmp 	L_prf_keygen$7
L_prf_keygen$8:
	movq	%rdx, %r8
	addq	%rdi, %r8
	movb	(%rax,%r8), %r8b
	movb	%r8b, 192(%rsp,%rdi)
	incq	%rdi
L_prf_keygen$7:
	cmpq	%rsi, %rdi
	jb  	L_prf_keygen$8
	movb	$128, 192(%rsp,%rdi)
	cmpq	$56, %rsi
	jb  	L_prf_keygen$5
	movq	$120, %rsi
	movq	$2, %rax
	movq	$127, %rdx
	jmp 	L_prf_keygen$3
L_prf_keygen$5:
	movq	$56, %rsi
	movq	$1, %rax
	movq	$63, %rdx
L_prf_keygen$6:
	jmp 	L_prf_keygen$3
L_prf_keygen$4:
	movb	%cl, 192(%rsp,%rdx)
	shrq	$8, %rcx
	addq	$-1, %rdx
L_prf_keygen$3:
	cmpq	%rsi, %rdx
	jnb 	L_prf_keygen$4
	leaq	192(%rsp), %rsi
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
	leaq	32(%rsp), %rax
	movq	$3, %rdx
	movb	%dl, 31(%rax)
	shrq	$8, %rdx
	movb	%dl, 30(%rax)
	shrq	$8, %rdx
	movb	%dl, 29(%rax)
	shrq	$8, %rdx
	movb	%dl, 28(%rax)
	shrq	$8, %rdx
	movb	%dl, 27(%rax)
	shrq	$8, %rdx
	movb	%dl, 26(%rax)
	shrq	$8, %rdx
	movb	%dl, 25(%rax)
	shrq	$8, %rdx
	movb	%dl, 24(%rax)
	shrq	$8, %rdx
	movb	%dl, 23(%rax)
	shrq	$8, %rdx
	movb	%dl, 22(%rax)
	shrq	$8, %rdx
	movb	%dl, 21(%rax)
	shrq	$8, %rdx
	movb	%dl, 20(%rax)
	shrq	$8, %rdx
	movb	%dl, 19(%rax)
	shrq	$8, %rdx
	movb	%dl, 18(%rax)
	shrq	$8, %rdx
	movb	%dl, 17(%rax)
	shrq	$8, %rdx
	movb	%dl, 16(%rax)
	shrq	$8, %rdx
	movb	%dl, 15(%rax)
	shrq	$8, %rdx
	movb	%dl, 14(%rax)
	shrq	$8, %rdx
	movb	%dl, 13(%rax)
	shrq	$8, %rdx
	movb	%dl, 12(%rax)
	shrq	$8, %rdx
	movb	%dl, 11(%rax)
	shrq	$8, %rdx
	movb	%dl, 10(%rax)
	shrq	$8, %rdx
	movb	%dl, 9(%rax)
	shrq	$8, %rdx
	movb	%dl, 8(%rax)
	shrq	$8, %rdx
	movb	%dl, 7(%rax)
	shrq	$8, %rdx
	movb	%dl, 6(%rax)
	shrq	$8, %rdx
	movb	%dl, 5(%rax)
	shrq	$8, %rdx
	movb	%dl, 4(%rax)
	shrq	$8, %rdx
	movb	%dl, 3(%rax)
	shrq	$8, %rdx
	movb	%dl, 2(%rax)
	shrq	$8, %rdx
	movb	%dl, 1(%rax)
	shrq	$8, %rdx
	movb	%dl, (%rax)
	leaq	64(%rsp), %rax
	call	Lcopy_nbytes$1
L_prf$10:
	movq	(%rdi), %rax
	movq	%rax, 96(%rsp)
	movq	8(%rdi), %rax
	movq	%rax, 104(%rsp)
	movq	16(%rdi), %rax
	movq	%rax, 112(%rsp)
	movq	24(%rdi), %rax
	movq	%rax, 120(%rsp)
	leaq	32(%rsp), %rax
	movq	%rsi, 8(%rsp)
	movq	$96, %rcx
	shlq	$3, %rcx
	movq	%rcx, 16(%rsp)
	movl	$1779033703, 128(%rsp)
	movl	$-1150833019, 132(%rsp)
	movl	$1013904242, 136(%rsp)
	movl	$-1521486534, 140(%rsp)
	movl	$1359893119, 144(%rsp)
	movl	$-1694144372, 148(%rsp)
	movl	$528734635, 152(%rsp)
	movl	$1541459225, 156(%rsp)
	movq	%rax, 24(%rsp)
	leaq	128(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	Lhash_plen_2n___blocks_0_ref_array$1
L_prf$9:
	leaq	280(%rsp), %rsp
	movq	24(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	$32, %rsi
	movq	$0, %rdi
	movl	%edi, 160(%rsp)
	movl	%edi, 164(%rsp)
	movl	%edi, 168(%rsp)
	movl	%edi, 172(%rsp)
	movl	%edi, 176(%rsp)
	movl	%edi, 180(%rsp)
	movl	%edi, 184(%rsp)
	movl	%edi, 188(%rsp)
	movl	%edi, 192(%rsp)
	movl	%edi, 196(%rsp)
	movl	%edi, 200(%rsp)
	movl	%edi, 204(%rsp)
	movl	%edi, 208(%rsp)
	movl	%edi, 212(%rsp)
	movl	%edi, 216(%rsp)
	movl	%edi, 220(%rsp)
	movl	%edi, 224(%rsp)
	movl	%edi, 228(%rsp)
	movl	%edi, 232(%rsp)
	movl	%edi, 236(%rsp)
	movl	%edi, 240(%rsp)
	movl	%edi, 244(%rsp)
	movl	%edi, 248(%rsp)
	movl	%edi, 252(%rsp)
	movl	%edi, 256(%rsp)
	movl	%edi, 260(%rsp)
	movl	%edi, 264(%rsp)
	movl	%edi, 268(%rsp)
	movl	%edi, 272(%rsp)
	movl	%edi, 276(%rsp)
	movl	%edi, 280(%rsp)
	movl	%edi, 284(%rsp)
	jmp 	L_prf$7
L_prf$8:
	movq	%rdx, %r8
	addq	%rdi, %r8
	movb	(%rax,%r8), %r8b
	movb	%r8b, 160(%rsp,%rdi)
	incq	%rdi
L_prf$7:
	cmpq	%rsi, %rdi
	jb  	L_prf$8
	movb	$128, 160(%rsp,%rdi)
	cmpq	$56, %rsi
	jb  	L_prf$5
	movq	$120, %rsi
	movq	$2, %rax
	movq	$127, %rdx
	jmp 	L_prf$3
L_prf$5:
	movq	$56, %rsi
	movq	$1, %rax
	movq	$63, %rdx
L_prf$6:
	jmp 	L_prf$3
L_prf$4:
	movb	%cl, 160(%rsp,%rdx)
	shrq	$8, %rcx
	addq	$-1, %rdx
L_prf$3:
	cmpq	%rsi, %rdx
	jnb 	L_prf$4
	leaq	160(%rsp), %rsi
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
	movq	$0, %rdx
	movq	$128, %rsi
	leaq	glob_data + 0(%rip), %rcx
	movq	%rdi, 8(%rsp)
	movq	8(%rsp), %r10
	jmp 	Lhash_plen_3n___blocks_0_ref_array$2
Lhash_plen_3n___blocks_0_ref_array$3:
	movq	%rsi, 8(%rsp)
	movl	(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 32(%rsp)
	movl	4(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 36(%rsp)
	movl	8(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 40(%rsp)
	movl	12(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 44(%rsp)
	movl	16(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 48(%rsp)
	movl	20(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 52(%rsp)
	movl	24(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 56(%rsp)
	movl	28(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 60(%rsp)
	movl	32(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 64(%rsp)
	movl	36(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 68(%rsp)
	movl	40(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 72(%rsp)
	movl	44(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 76(%rsp)
	movl	48(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 80(%rsp)
	movl	52(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 84(%rsp)
	movl	56(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 88(%rsp)
	movl	60(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 92(%rsp)
	movq	%rdx, 16(%rsp)
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
	movl	16(%r10), %r12d
	movl	20(%r10), %r8d
	movl	24(%r10), %r9d
	movl	28(%r10), %ebp
	movq	%r10, 24(%rsp)
	movq	$0, %r10
	jmp 	Lhash_plen_3n___blocks_0_ref_array$4
Lhash_plen_3n___blocks_0_ref_array$5:
	movl	%ebp, %r11d
	movl	%r12d, %ebx
	rorl	$6, %ebx
	movl	%r12d, %ebp
	rorl	$11, %ebp
	xorl	%ebp, %ebx
	movl	%r12d, %ebp
	rorl	$25, %ebp
	xorl	%ebp, %ebx
	addl	%ebx, %r11d
	movl	%r12d, %ebx
	andl	%r8d, %ebx
	movl	%r12d, %ebp
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
	movl	%r14d, %r15d
	andl	%esi, %r15d
	xorl	%r15d, %ebp
	movl	%edx, %r15d
	andl	%esi, %r15d
	xorl	%r15d, %ebp
	addl	%ebp, %ebx
	movl	%r9d, %ebp
	movl	%r8d, %r9d
	movl	%r12d, %r8d
	movl	%edi, %r12d
	addl	%r11d, %r12d
	movl	%esi, %edi
	movl	%edx, %esi
	movl	%r14d, %edx
	movl	%r11d, %r14d
	addl	%ebx, %r14d
	incq	%r10
Lhash_plen_3n___blocks_0_ref_array$4:
	cmpq	$64, %r10
	jb  	Lhash_plen_3n___blocks_0_ref_array$5
	movq	24(%rsp), %r10
	addl	(%r10), %r14d
	addl	4(%r10), %edx
	addl	8(%r10), %esi
	addl	12(%r10), %edi
	addl	16(%r10), %r12d
	addl	20(%r10), %r8d
	addl	24(%r10), %r9d
	addl	28(%r10), %ebp
	movl	%r14d, (%r10)
	movl	%edx, 4(%r10)
	movl	%esi, 8(%r10)
	movl	%edi, 12(%r10)
	movl	%r12d, 16(%r10)
	movl	%r8d, 20(%r10)
	movl	%r9d, 24(%r10)
	movl	%ebp, 28(%r10)
	movq	16(%rsp), %rdx
	movq	8(%rsp), %rsi
	addq	$64, %rdx
	addq	$-64, %rsi
Lhash_plen_3n___blocks_0_ref_array$2:
	cmpq	$64, %rsi
	jnb 	Lhash_plen_3n___blocks_0_ref_array$3
	ret
Lhash_plen_2n___blocks_0_ref_array$1:
	movq	$0, %rdx
	movq	$96, %rsi
	leaq	glob_data + 0(%rip), %rcx
	movq	%rdi, 8(%rsp)
	movq	8(%rsp), %r10
	jmp 	Lhash_plen_2n___blocks_0_ref_array$2
Lhash_plen_2n___blocks_0_ref_array$3:
	movq	%rsi, 8(%rsp)
	movl	(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 32(%rsp)
	movl	4(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 36(%rsp)
	movl	8(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 40(%rsp)
	movl	12(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 44(%rsp)
	movl	16(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 48(%rsp)
	movl	20(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 52(%rsp)
	movl	24(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 56(%rsp)
	movl	28(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 60(%rsp)
	movl	32(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 64(%rsp)
	movl	36(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 68(%rsp)
	movl	40(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 72(%rsp)
	movl	44(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 76(%rsp)
	movl	48(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 80(%rsp)
	movl	52(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 84(%rsp)
	movl	56(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 88(%rsp)
	movl	60(%rax,%rdx), %esi
	bswapl	%esi
	movl	%esi, 92(%rsp)
	movq	%rdx, 16(%rsp)
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
	movl	16(%r10), %r12d
	movl	20(%r10), %r8d
	movl	24(%r10), %r9d
	movl	28(%r10), %ebp
	movq	%r10, 24(%rsp)
	movq	$0, %r10
	jmp 	Lhash_plen_2n___blocks_0_ref_array$4
Lhash_plen_2n___blocks_0_ref_array$5:
	movl	%ebp, %r11d
	movl	%r12d, %ebx
	rorl	$6, %ebx
	movl	%r12d, %ebp
	rorl	$11, %ebp
	xorl	%ebp, %ebx
	movl	%r12d, %ebp
	rorl	$25, %ebp
	xorl	%ebp, %ebx
	addl	%ebx, %r11d
	movl	%r12d, %ebx
	andl	%r8d, %ebx
	movl	%r12d, %ebp
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
	movl	%r14d, %r15d
	andl	%esi, %r15d
	xorl	%r15d, %ebp
	movl	%edx, %r15d
	andl	%esi, %r15d
	xorl	%r15d, %ebp
	addl	%ebp, %ebx
	movl	%r9d, %ebp
	movl	%r8d, %r9d
	movl	%r12d, %r8d
	movl	%edi, %r12d
	addl	%r11d, %r12d
	movl	%esi, %edi
	movl	%edx, %esi
	movl	%r14d, %edx
	movl	%r11d, %r14d
	addl	%ebx, %r14d
	incq	%r10
Lhash_plen_2n___blocks_0_ref_array$4:
	cmpq	$64, %r10
	jb  	Lhash_plen_2n___blocks_0_ref_array$5
	movq	24(%rsp), %r10
	addl	(%r10), %r14d
	addl	4(%r10), %edx
	addl	8(%r10), %esi
	addl	12(%r10), %edi
	addl	16(%r10), %r12d
	addl	20(%r10), %r8d
	addl	24(%r10), %r9d
	addl	28(%r10), %ebp
	movl	%r14d, (%r10)
	movl	%edx, 4(%r10)
	movl	%esi, 8(%r10)
	movl	%edi, 12(%r10)
	movl	%r12d, 16(%r10)
	movl	%r8d, 20(%r10)
	movl	%r9d, 24(%r10)
	movl	%ebp, 28(%r10)
	movq	16(%rsp), %rdx
	movq	8(%rsp), %rsi
	addq	$64, %rdx
	addq	$-64, %rsi
Lhash_plen_2n___blocks_0_ref_array$2:
	cmpq	$64, %rsi
	jnb 	Lhash_plen_2n___blocks_0_ref_array$3
	ret
L_blocks_1_ref$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%r10, 8(%rsp)
	movq	$0, %rdx
	movq	8(%rsp), %r9
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
	movl	(%r9), %r12d
	movl	4(%r9), %edx
	movl	8(%r9), %r15d
	movl	12(%r9), %esi
	movl	16(%r9), %ebp
	movl	20(%r9), %edi
	movl	24(%r9), %r8d
	movl	28(%r9), %ebx
	movq	%r9, 24(%rsp)
	movq	$0, %r9
	jmp 	L_blocks_1_ref$4
L_blocks_1_ref$5:
	movl	%ebx, %r10d
	movl	%ebp, %r11d
	rorl	$6, %r11d
	movl	%ebp, %ebx
	rorl	$11, %ebx
	xorl	%ebx, %r11d
	movl	%ebp, %ebx
	rorl	$25, %ebx
	xorl	%ebx, %r11d
	addl	%r11d, %r10d
	movl	%ebp, %r11d
	andl	%edi, %r11d
	movl	%ebp, %ebx
	notl	%ebx
	andl	%r8d, %ebx
	xorl	%ebx, %r11d
	addl	%r11d, %r10d
	addl	(%rcx,%r9,4), %r10d
	addl	32(%rsp,%r9,4), %r10d
	movl	%r12d, %r11d
	rorl	$2, %r11d
	movl	%r12d, %ebx
	rorl	$13, %ebx
	xorl	%ebx, %r11d
	movl	%r12d, %ebx
	rorl	$22, %ebx
	xorl	%ebx, %r11d
	movl	%r12d, %ebx
	andl	%edx, %ebx
	movl	%r12d, %r14d
	andl	%r15d, %r14d
	xorl	%r14d, %ebx
	movl	%edx, %r14d
	andl	%r15d, %r14d
	xorl	%r14d, %ebx
	addl	%ebx, %r11d
	movl	%r8d, %ebx
	movl	%edi, %r8d
	movl	%ebp, %edi
	movl	%esi, %ebp
	addl	%r10d, %ebp
	movl	%r15d, %esi
	movl	%edx, %r15d
	movl	%r12d, %edx
	movl	%r10d, %r12d
	addl	%r11d, %r12d
	incq	%r9
L_blocks_1_ref$4:
	cmpq	$64, %r9
	jb  	L_blocks_1_ref$5
	movq	24(%rsp), %r9
	addl	(%r9), %r12d
	addl	4(%r9), %edx
	addl	8(%r9), %r15d
	addl	12(%r9), %esi
	addl	16(%r9), %ebp
	addl	20(%r9), %edi
	addl	24(%r9), %r8d
	addl	28(%r9), %ebx
	movl	%r12d, (%r9)
	movl	%edx, 4(%r9)
	movl	%r15d, 8(%r9)
	movl	%esi, 12(%r9)
	movl	%ebp, 16(%r9)
	movl	%edi, 20(%r9)
	movl	%r8d, 24(%r9)
	movl	%ebx, 28(%r9)
	movq	16(%rsp), %rsi
	movq	8(%rsp), %rdx
	incq	%rdx
L_blocks_1_ref$2:
	cmpq	%rax, %rdx
	jb  	L_blocks_1_ref$3
	ret
Lcopy_nbytes$1:
	movq	(%rcx), %rdx
	movq	%rdx, (%rax)
	movq	8(%rcx), %rdx
	movq	%rdx, 8(%rax)
	movq	16(%rcx), %rdx
	movq	%rdx, 16(%rax)
	movq	24(%rcx), %rcx
	movq	%rcx, 24(%rax)
	ret
Lmemcpy_u8u8_N___memcpy_u8u8$1:
	movq	$0, %rsi
	jmp 	Lmemcpy_u8u8_N___memcpy_u8u8$2
Lmemcpy_u8u8_N___memcpy_u8u8$3:
	movb	(%rdx,%rsi), %dil
	movb	%dil, (%rcx,%rsi)
	incq	%rsi
Lmemcpy_u8u8_N___memcpy_u8u8$2:
	cmpq	$32, %rsi
	jb  	Lmemcpy_u8u8_N___memcpy_u8u8$3
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
