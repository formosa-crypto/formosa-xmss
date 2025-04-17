	.att_syntax
	.text
	.p2align	5
	.globl	_wots_pk_from_sig_jazz
	.globl	wots_pk_from_sig_jazz
	.globl	_wots_sign_jazz
	.globl	wots_sign_jazz
	.globl	_wots_pkgen_jazz
	.globl	wots_pkgen_jazz
	.globl	_gen_chain_inplace_jazz
	.globl	gen_chain_inplace_jazz
	.globl	_wots_checksum_jazz
	.globl	wots_checksum_jazz
	.globl	_expand_seed_jazz
	.globl	expand_seed_jazz
_wots_pk_from_sig_jazz:
wots_pk_from_sig_jazz:
	movq	%rsp, %rax
	leaq	-344(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r12, 304(%rsp)
	movq	%r13, 312(%rsp)
	movq	%r14, 320(%rsp)
	movq	%r15, 328(%rsp)
	movq	%rax, 336(%rsp)
	movq	%rdi, %r13
	movq	%r8, (%rsp)
	movq	%rdx, 8(%rsp)
	leaq	16(%rsp), %rdx
	movq	%rcx, %r9
	leaq	-8(%rsp), %rsp
	call	L_chain_lengths$1
Lwots_pk_from_sig_jazz$135:
	leaq	8(%rsp), %rsp
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	16(%rsp), %edi
	movl	$15, %r9d
	subl	16(%rsp), %r9d
	movq	%rax, %rcx
	movq	%r13, %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$134:
	movq	%r13, %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$133:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$1, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	20(%rsp), %edi
	movl	$15, %r9d
	subl	20(%rsp), %r9d
	movq	%rax, %rcx
	addq	$32, %rcx
	leaq	32(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$132:
	leaq	32(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$131:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$2, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	24(%rsp), %edi
	movl	$15, %r9d
	subl	24(%rsp), %r9d
	movq	%rax, %rcx
	addq	$64, %rcx
	leaq	64(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$130:
	leaq	64(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$129:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$3, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	28(%rsp), %edi
	movl	$15, %r9d
	subl	28(%rsp), %r9d
	movq	%rax, %rcx
	addq	$96, %rcx
	leaq	96(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$128:
	leaq	96(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$127:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$4, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	32(%rsp), %edi
	movl	$15, %r9d
	subl	32(%rsp), %r9d
	movq	%rax, %rcx
	addq	$128, %rcx
	leaq	128(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$126:
	leaq	128(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$125:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$5, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	36(%rsp), %edi
	movl	$15, %r9d
	subl	36(%rsp), %r9d
	movq	%rax, %rcx
	addq	$160, %rcx
	leaq	160(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$124:
	leaq	160(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$123:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$6, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	40(%rsp), %edi
	movl	$15, %r9d
	subl	40(%rsp), %r9d
	movq	%rax, %rcx
	addq	$192, %rcx
	leaq	192(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$122:
	leaq	192(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$121:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$7, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	44(%rsp), %edi
	movl	$15, %r9d
	subl	44(%rsp), %r9d
	movq	%rax, %rcx
	addq	$224, %rcx
	leaq	224(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$120:
	leaq	224(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$119:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$8, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	48(%rsp), %edi
	movl	$15, %r9d
	subl	48(%rsp), %r9d
	movq	%rax, %rcx
	addq	$256, %rcx
	leaq	256(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$118:
	leaq	256(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$117:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$9, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	52(%rsp), %edi
	movl	$15, %r9d
	subl	52(%rsp), %r9d
	movq	%rax, %rcx
	addq	$288, %rcx
	leaq	288(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$116:
	leaq	288(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$115:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$10, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	56(%rsp), %edi
	movl	$15, %r9d
	subl	56(%rsp), %r9d
	movq	%rax, %rcx
	addq	$320, %rcx
	leaq	320(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$114:
	leaq	320(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$113:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$11, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	60(%rsp), %edi
	movl	$15, %r9d
	subl	60(%rsp), %r9d
	movq	%rax, %rcx
	addq	$352, %rcx
	leaq	352(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$112:
	leaq	352(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$111:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$12, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	64(%rsp), %edi
	movl	$15, %r9d
	subl	64(%rsp), %r9d
	movq	%rax, %rcx
	addq	$384, %rcx
	leaq	384(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$110:
	leaq	384(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$109:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$13, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	68(%rsp), %edi
	movl	$15, %r9d
	subl	68(%rsp), %r9d
	movq	%rax, %rcx
	addq	$416, %rcx
	leaq	416(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$108:
	leaq	416(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$107:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$14, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	72(%rsp), %edi
	movl	$15, %r9d
	subl	72(%rsp), %r9d
	movq	%rax, %rcx
	addq	$448, %rcx
	leaq	448(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$106:
	leaq	448(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$105:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$15, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	76(%rsp), %edi
	movl	$15, %r9d
	subl	76(%rsp), %r9d
	movq	%rax, %rcx
	addq	$480, %rcx
	leaq	480(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$104:
	leaq	480(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$103:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$16, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	80(%rsp), %edi
	movl	$15, %r9d
	subl	80(%rsp), %r9d
	movq	%rax, %rcx
	addq	$512, %rcx
	leaq	512(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$102:
	leaq	512(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$101:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$17, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	84(%rsp), %edi
	movl	$15, %r9d
	subl	84(%rsp), %r9d
	movq	%rax, %rcx
	addq	$544, %rcx
	leaq	544(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$100:
	leaq	544(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$99:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$18, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	88(%rsp), %edi
	movl	$15, %r9d
	subl	88(%rsp), %r9d
	movq	%rax, %rcx
	addq	$576, %rcx
	leaq	576(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$98:
	leaq	576(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$97:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$19, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	92(%rsp), %edi
	movl	$15, %r9d
	subl	92(%rsp), %r9d
	movq	%rax, %rcx
	addq	$608, %rcx
	leaq	608(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$96:
	leaq	608(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$95:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$20, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	96(%rsp), %edi
	movl	$15, %r9d
	subl	96(%rsp), %r9d
	movq	%rax, %rcx
	addq	$640, %rcx
	leaq	640(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$94:
	leaq	640(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$93:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$21, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	100(%rsp), %edi
	movl	$15, %r9d
	subl	100(%rsp), %r9d
	movq	%rax, %rcx
	addq	$672, %rcx
	leaq	672(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$92:
	leaq	672(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$91:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$22, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	104(%rsp), %edi
	movl	$15, %r9d
	subl	104(%rsp), %r9d
	movq	%rax, %rcx
	addq	$704, %rcx
	leaq	704(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$90:
	leaq	704(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$89:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$23, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	108(%rsp), %edi
	movl	$15, %r9d
	subl	108(%rsp), %r9d
	movq	%rax, %rcx
	addq	$736, %rcx
	leaq	736(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$88:
	leaq	736(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$87:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$24, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	112(%rsp), %edi
	movl	$15, %r9d
	subl	112(%rsp), %r9d
	movq	%rax, %rcx
	addq	$768, %rcx
	leaq	768(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$86:
	leaq	768(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$85:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$25, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	116(%rsp), %edi
	movl	$15, %r9d
	subl	116(%rsp), %r9d
	movq	%rax, %rcx
	addq	$800, %rcx
	leaq	800(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$84:
	leaq	800(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$83:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$26, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	120(%rsp), %edi
	movl	$15, %r9d
	subl	120(%rsp), %r9d
	movq	%rax, %rcx
	addq	$832, %rcx
	leaq	832(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$82:
	leaq	832(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$81:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$27, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	124(%rsp), %edi
	movl	$15, %r9d
	subl	124(%rsp), %r9d
	movq	%rax, %rcx
	addq	$864, %rcx
	leaq	864(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$80:
	leaq	864(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$79:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$28, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	128(%rsp), %edi
	movl	$15, %r9d
	subl	128(%rsp), %r9d
	movq	%rax, %rcx
	addq	$896, %rcx
	leaq	896(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$78:
	leaq	896(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$77:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$29, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	132(%rsp), %edi
	movl	$15, %r9d
	subl	132(%rsp), %r9d
	movq	%rax, %rcx
	addq	$928, %rcx
	leaq	928(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$76:
	leaq	928(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$75:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$30, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	136(%rsp), %edi
	movl	$15, %r9d
	subl	136(%rsp), %r9d
	movq	%rax, %rcx
	addq	$960, %rcx
	leaq	960(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$74:
	leaq	960(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$73:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$31, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	140(%rsp), %edi
	movl	$15, %r9d
	subl	140(%rsp), %r9d
	movq	%rax, %rcx
	addq	$992, %rcx
	leaq	992(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$72:
	leaq	992(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$71:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$32, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	144(%rsp), %edi
	movl	$15, %r9d
	subl	144(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1024, %rcx
	leaq	1024(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$70:
	leaq	1024(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$69:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$33, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	148(%rsp), %edi
	movl	$15, %r9d
	subl	148(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1056, %rcx
	leaq	1056(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$68:
	leaq	1056(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$67:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$34, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	152(%rsp), %edi
	movl	$15, %r9d
	subl	152(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1088, %rcx
	leaq	1088(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$66:
	leaq	1088(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$65:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$35, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	156(%rsp), %edi
	movl	$15, %r9d
	subl	156(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1120, %rcx
	leaq	1120(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$64:
	leaq	1120(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$63:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$36, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	160(%rsp), %edi
	movl	$15, %r9d
	subl	160(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1152, %rcx
	leaq	1152(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$62:
	leaq	1152(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$61:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$37, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	164(%rsp), %edi
	movl	$15, %r9d
	subl	164(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1184, %rcx
	leaq	1184(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$60:
	leaq	1184(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$59:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$38, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	168(%rsp), %edi
	movl	$15, %r9d
	subl	168(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1216, %rcx
	leaq	1216(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$58:
	leaq	1216(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$57:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$39, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	172(%rsp), %edi
	movl	$15, %r9d
	subl	172(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1248, %rcx
	leaq	1248(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$56:
	leaq	1248(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$55:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$40, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	176(%rsp), %edi
	movl	$15, %r9d
	subl	176(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1280, %rcx
	leaq	1280(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$54:
	leaq	1280(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$53:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$41, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	180(%rsp), %edi
	movl	$15, %r9d
	subl	180(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1312, %rcx
	leaq	1312(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$52:
	leaq	1312(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$51:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$42, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	184(%rsp), %edi
	movl	$15, %r9d
	subl	184(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1344, %rcx
	leaq	1344(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$50:
	leaq	1344(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$49:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$43, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	188(%rsp), %edi
	movl	$15, %r9d
	subl	188(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1376, %rcx
	leaq	1376(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$48:
	leaq	1376(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$47:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$44, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	192(%rsp), %edi
	movl	$15, %r9d
	subl	192(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1408, %rcx
	leaq	1408(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$46:
	leaq	1408(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$45:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$45, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	196(%rsp), %edi
	movl	$15, %r9d
	subl	196(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1440, %rcx
	leaq	1440(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$44:
	leaq	1440(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$43:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$46, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	200(%rsp), %edi
	movl	$15, %r9d
	subl	200(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1472, %rcx
	leaq	1472(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$42:
	leaq	1472(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$41:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$47, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	204(%rsp), %edi
	movl	$15, %r9d
	subl	204(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1504, %rcx
	leaq	1504(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$40:
	leaq	1504(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$39:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$48, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	208(%rsp), %edi
	movl	$15, %r9d
	subl	208(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1536, %rcx
	leaq	1536(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$38:
	leaq	1536(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$37:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$49, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	212(%rsp), %edi
	movl	$15, %r9d
	subl	212(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1568, %rcx
	leaq	1568(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$36:
	leaq	1568(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$35:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$50, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	216(%rsp), %edi
	movl	$15, %r9d
	subl	216(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1600, %rcx
	leaq	1600(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$34:
	leaq	1600(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$33:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$51, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	220(%rsp), %edi
	movl	$15, %r9d
	subl	220(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1632, %rcx
	leaq	1632(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$32:
	leaq	1632(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$31:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$52, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	224(%rsp), %edi
	movl	$15, %r9d
	subl	224(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1664, %rcx
	leaq	1664(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$30:
	leaq	1664(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$29:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$53, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	228(%rsp), %edi
	movl	$15, %r9d
	subl	228(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1696, %rcx
	leaq	1696(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$28:
	leaq	1696(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$27:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$54, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	232(%rsp), %edi
	movl	$15, %r9d
	subl	232(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1728, %rcx
	leaq	1728(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$26:
	leaq	1728(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$25:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$55, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	236(%rsp), %edi
	movl	$15, %r9d
	subl	236(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1760, %rcx
	leaq	1760(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$24:
	leaq	1760(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$23:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$56, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	240(%rsp), %edi
	movl	$15, %r9d
	subl	240(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1792, %rcx
	leaq	1792(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$22:
	leaq	1792(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$21:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$57, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	244(%rsp), %edi
	movl	$15, %r9d
	subl	244(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1824, %rcx
	leaq	1824(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$20:
	leaq	1824(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$19:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$58, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	248(%rsp), %edi
	movl	$15, %r9d
	subl	248(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1856, %rcx
	leaq	1856(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$18:
	leaq	1856(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$17:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$59, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	252(%rsp), %edi
	movl	$15, %r9d
	subl	252(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1888, %rcx
	leaq	1888(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$16:
	leaq	1888(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$15:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$60, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	256(%rsp), %edi
	movl	$15, %r9d
	subl	256(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1920, %rcx
	leaq	1920(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$14:
	leaq	1920(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$13:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$61, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	260(%rsp), %edi
	movl	$15, %r9d
	subl	260(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1952, %rcx
	leaq	1952(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$12:
	leaq	1952(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$11:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$62, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	264(%rsp), %edi
	movl	$15, %r9d
	subl	264(%rsp), %r9d
	movq	%rax, %rcx
	addq	$1984, %rcx
	leaq	1984(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$10:
	leaq	1984(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$9:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$63, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	268(%rsp), %edi
	movl	$15, %r9d
	subl	268(%rsp), %r9d
	movq	%rax, %rcx
	addq	$2016, %rcx
	leaq	2016(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$8:
	leaq	2016(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$7:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$64, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	272(%rsp), %edi
	movl	$15, %r9d
	subl	272(%rsp), %r9d
	movq	%rax, %rcx
	addq	$2048, %rcx
	leaq	2048(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$6:
	leaq	2048(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$5:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$65, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	276(%rsp), %edi
	movl	$15, %r9d
	subl	276(%rsp), %r9d
	movq	%rax, %rcx
	addq	$2080, %rcx
	leaq	2080(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$4:
	leaq	2080(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$3:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$66, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	8(%rsp), %rax
	movl	280(%rsp), %edi
	movl	$15, %r9d
	subl	280(%rsp), %r9d
	movq	%rax, %rcx
	addq	$2112, %rcx
	leaq	2112(%r13), %rax
	call	L_memcpy_u8u8p$1
Lwots_pk_from_sig_jazz$2:
	leaq	2112(%r13), %rdx
	movl	%edi, %eax
	movl	%r9d, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pk_from_sig_jazz$1:
	leaq	32(%rsp), %rsp
	movq	288(%rsp), %rbx
	movq	296(%rsp), %rbp
	movq	304(%rsp), %r12
	movq	312(%rsp), %r13
	movq	320(%rsp), %r14
	movq	328(%rsp), %r15
	movq	336(%rsp), %rsp
	movq	%rsp, %rsi
	andq	$-8, %rsp
	subq	$1288, %rsp
	movb	$0, 1287(%rsp)
	movb	$0, 1286(%rsp)
	movb	$0, 1285(%rsp)
	movb	$0, 1284(%rsp)
	movb	$0, 1283(%rsp)
	movb	$0, 1282(%rsp)
	movb	$0, 1281(%rsp)
	movb	$0, 1280(%rsp)
	movb	$0, 1279(%rsp)
	movb	$0, 1278(%rsp)
	movb	$0, 1277(%rsp)
	movb	$0, 1276(%rsp)
	movb	$0, 1275(%rsp)
	movb	$0, 1274(%rsp)
	movb	$0, 1273(%rsp)
	movb	$0, 1272(%rsp)
	movb	$0, 1271(%rsp)
	movb	$0, 1270(%rsp)
	movb	$0, 1269(%rsp)
	movb	$0, 1268(%rsp)
	movb	$0, 1267(%rsp)
	movb	$0, 1266(%rsp)
	movb	$0, 1265(%rsp)
	movb	$0, 1264(%rsp)
	movb	$0, 1263(%rsp)
	movb	$0, 1262(%rsp)
	movb	$0, 1261(%rsp)
	movb	$0, 1260(%rsp)
	movb	$0, 1259(%rsp)
	movb	$0, 1258(%rsp)
	movb	$0, 1257(%rsp)
	movb	$0, 1256(%rsp)
	movb	$0, 1255(%rsp)
	movb	$0, 1254(%rsp)
	movb	$0, 1253(%rsp)
	movb	$0, 1252(%rsp)
	movb	$0, 1251(%rsp)
	movb	$0, 1250(%rsp)
	movb	$0, 1249(%rsp)
	movb	$0, 1248(%rsp)
	movb	$0, 1247(%rsp)
	movb	$0, 1246(%rsp)
	movb	$0, 1245(%rsp)
	movb	$0, 1244(%rsp)
	movb	$0, 1243(%rsp)
	movb	$0, 1242(%rsp)
	movb	$0, 1241(%rsp)
	movb	$0, 1240(%rsp)
	movb	$0, 1239(%rsp)
	movb	$0, 1238(%rsp)
	movb	$0, 1237(%rsp)
	movb	$0, 1236(%rsp)
	movb	$0, 1235(%rsp)
	movb	$0, 1234(%rsp)
	movb	$0, 1233(%rsp)
	movb	$0, 1232(%rsp)
	movb	$0, 1231(%rsp)
	movb	$0, 1230(%rsp)
	movb	$0, 1229(%rsp)
	movb	$0, 1228(%rsp)
	movb	$0, 1227(%rsp)
	movb	$0, 1226(%rsp)
	movb	$0, 1225(%rsp)
	movb	$0, 1224(%rsp)
	movb	$0, 1223(%rsp)
	movb	$0, 1222(%rsp)
	movb	$0, 1221(%rsp)
	movb	$0, 1220(%rsp)
	movb	$0, 1219(%rsp)
	movb	$0, 1218(%rsp)
	movb	$0, 1217(%rsp)
	movb	$0, 1216(%rsp)
	movb	$0, 1215(%rsp)
	movb	$0, 1214(%rsp)
	movb	$0, 1213(%rsp)
	movb	$0, 1212(%rsp)
	movb	$0, 1211(%rsp)
	movb	$0, 1210(%rsp)
	movb	$0, 1209(%rsp)
	movb	$0, 1208(%rsp)
	movb	$0, 1207(%rsp)
	movb	$0, 1206(%rsp)
	movb	$0, 1205(%rsp)
	movb	$0, 1204(%rsp)
	movb	$0, 1203(%rsp)
	movb	$0, 1202(%rsp)
	movb	$0, 1201(%rsp)
	movb	$0, 1200(%rsp)
	movb	$0, 1199(%rsp)
	movb	$0, 1198(%rsp)
	movb	$0, 1197(%rsp)
	movb	$0, 1196(%rsp)
	movb	$0, 1195(%rsp)
	movb	$0, 1194(%rsp)
	movb	$0, 1193(%rsp)
	movb	$0, 1192(%rsp)
	movb	$0, 1191(%rsp)
	movb	$0, 1190(%rsp)
	movb	$0, 1189(%rsp)
	movb	$0, 1188(%rsp)
	movb	$0, 1187(%rsp)
	movb	$0, 1186(%rsp)
	movb	$0, 1185(%rsp)
	movb	$0, 1184(%rsp)
	movb	$0, 1183(%rsp)
	movb	$0, 1182(%rsp)
	movb	$0, 1181(%rsp)
	movb	$0, 1180(%rsp)
	movb	$0, 1179(%rsp)
	movb	$0, 1178(%rsp)
	movb	$0, 1177(%rsp)
	movb	$0, 1176(%rsp)
	movb	$0, 1175(%rsp)
	movb	$0, 1174(%rsp)
	movb	$0, 1173(%rsp)
	movb	$0, 1172(%rsp)
	movb	$0, 1171(%rsp)
	movb	$0, 1170(%rsp)
	movb	$0, 1169(%rsp)
	movb	$0, 1168(%rsp)
	movb	$0, 1167(%rsp)
	movb	$0, 1166(%rsp)
	movb	$0, 1165(%rsp)
	movb	$0, 1164(%rsp)
	movb	$0, 1163(%rsp)
	movb	$0, 1162(%rsp)
	movb	$0, 1161(%rsp)
	movb	$0, 1160(%rsp)
	movb	$0, 1159(%rsp)
	movb	$0, 1158(%rsp)
	movb	$0, 1157(%rsp)
	movb	$0, 1156(%rsp)
	movb	$0, 1155(%rsp)
	movb	$0, 1154(%rsp)
	movb	$0, 1153(%rsp)
	movb	$0, 1152(%rsp)
	movb	$0, 1151(%rsp)
	movb	$0, 1150(%rsp)
	movb	$0, 1149(%rsp)
	movb	$0, 1148(%rsp)
	movb	$0, 1147(%rsp)
	movb	$0, 1146(%rsp)
	movb	$0, 1145(%rsp)
	movb	$0, 1144(%rsp)
	movb	$0, 1143(%rsp)
	movb	$0, 1142(%rsp)
	movb	$0, 1141(%rsp)
	movb	$0, 1140(%rsp)
	movb	$0, 1139(%rsp)
	movb	$0, 1138(%rsp)
	movb	$0, 1137(%rsp)
	movb	$0, 1136(%rsp)
	movb	$0, 1135(%rsp)
	movb	$0, 1134(%rsp)
	movb	$0, 1133(%rsp)
	movb	$0, 1132(%rsp)
	movb	$0, 1131(%rsp)
	movb	$0, 1130(%rsp)
	movb	$0, 1129(%rsp)
	movb	$0, 1128(%rsp)
	movb	$0, 1127(%rsp)
	movb	$0, 1126(%rsp)
	movb	$0, 1125(%rsp)
	movb	$0, 1124(%rsp)
	movb	$0, 1123(%rsp)
	movb	$0, 1122(%rsp)
	movb	$0, 1121(%rsp)
	movb	$0, 1120(%rsp)
	movb	$0, 1119(%rsp)
	movb	$0, 1118(%rsp)
	movb	$0, 1117(%rsp)
	movb	$0, 1116(%rsp)
	movb	$0, 1115(%rsp)
	movb	$0, 1114(%rsp)
	movb	$0, 1113(%rsp)
	movb	$0, 1112(%rsp)
	movb	$0, 1111(%rsp)
	movb	$0, 1110(%rsp)
	movb	$0, 1109(%rsp)
	movb	$0, 1108(%rsp)
	movb	$0, 1107(%rsp)
	movb	$0, 1106(%rsp)
	movb	$0, 1105(%rsp)
	movb	$0, 1104(%rsp)
	movb	$0, 1103(%rsp)
	movb	$0, 1102(%rsp)
	movb	$0, 1101(%rsp)
	movb	$0, 1100(%rsp)
	movb	$0, 1099(%rsp)
	movb	$0, 1098(%rsp)
	movb	$0, 1097(%rsp)
	movb	$0, 1096(%rsp)
	movb	$0, 1095(%rsp)
	movb	$0, 1094(%rsp)
	movb	$0, 1093(%rsp)
	movb	$0, 1092(%rsp)
	movb	$0, 1091(%rsp)
	movb	$0, 1090(%rsp)
	movb	$0, 1089(%rsp)
	movb	$0, 1088(%rsp)
	movb	$0, 1087(%rsp)
	movb	$0, 1086(%rsp)
	movb	$0, 1085(%rsp)
	movb	$0, 1084(%rsp)
	movb	$0, 1083(%rsp)
	movb	$0, 1082(%rsp)
	movb	$0, 1081(%rsp)
	movb	$0, 1080(%rsp)
	movb	$0, 1079(%rsp)
	movb	$0, 1078(%rsp)
	movb	$0, 1077(%rsp)
	movb	$0, 1076(%rsp)
	movb	$0, 1075(%rsp)
	movb	$0, 1074(%rsp)
	movb	$0, 1073(%rsp)
	movb	$0, 1072(%rsp)
	movb	$0, 1071(%rsp)
	movb	$0, 1070(%rsp)
	movb	$0, 1069(%rsp)
	movb	$0, 1068(%rsp)
	movb	$0, 1067(%rsp)
	movb	$0, 1066(%rsp)
	movb	$0, 1065(%rsp)
	movb	$0, 1064(%rsp)
	movb	$0, 1063(%rsp)
	movb	$0, 1062(%rsp)
	movb	$0, 1061(%rsp)
	movb	$0, 1060(%rsp)
	movb	$0, 1059(%rsp)
	movb	$0, 1058(%rsp)
	movb	$0, 1057(%rsp)
	movb	$0, 1056(%rsp)
	movb	$0, 1055(%rsp)
	movb	$0, 1054(%rsp)
	movb	$0, 1053(%rsp)
	movb	$0, 1052(%rsp)
	movb	$0, 1051(%rsp)
	movb	$0, 1050(%rsp)
	movb	$0, 1049(%rsp)
	movb	$0, 1048(%rsp)
	movb	$0, 1047(%rsp)
	movb	$0, 1046(%rsp)
	movb	$0, 1045(%rsp)
	movb	$0, 1044(%rsp)
	movb	$0, 1043(%rsp)
	movb	$0, 1042(%rsp)
	movb	$0, 1041(%rsp)
	movb	$0, 1040(%rsp)
	movb	$0, 1039(%rsp)
	movb	$0, 1038(%rsp)
	movb	$0, 1037(%rsp)
	movb	$0, 1036(%rsp)
	movb	$0, 1035(%rsp)
	movb	$0, 1034(%rsp)
	movb	$0, 1033(%rsp)
	movb	$0, 1032(%rsp)
	movb	$0, 1031(%rsp)
	movb	$0, 1030(%rsp)
	movb	$0, 1029(%rsp)
	movb	$0, 1028(%rsp)
	movb	$0, 1027(%rsp)
	movb	$0, 1026(%rsp)
	movb	$0, 1025(%rsp)
	movb	$0, 1024(%rsp)
	movb	$0, 1023(%rsp)
	movb	$0, 1022(%rsp)
	movb	$0, 1021(%rsp)
	movb	$0, 1020(%rsp)
	movb	$0, 1019(%rsp)
	movb	$0, 1018(%rsp)
	movb	$0, 1017(%rsp)
	movb	$0, 1016(%rsp)
	movb	$0, 1015(%rsp)
	movb	$0, 1014(%rsp)
	movb	$0, 1013(%rsp)
	movb	$0, 1012(%rsp)
	movb	$0, 1011(%rsp)
	movb	$0, 1010(%rsp)
	movb	$0, 1009(%rsp)
	movb	$0, 1008(%rsp)
	movb	$0, 1007(%rsp)
	movb	$0, 1006(%rsp)
	movb	$0, 1005(%rsp)
	movb	$0, 1004(%rsp)
	movb	$0, 1003(%rsp)
	movb	$0, 1002(%rsp)
	movb	$0, 1001(%rsp)
	movb	$0, 1000(%rsp)
	movb	$0, 999(%rsp)
	movb	$0, 998(%rsp)
	movb	$0, 997(%rsp)
	movb	$0, 996(%rsp)
	movb	$0, 995(%rsp)
	movb	$0, 994(%rsp)
	movb	$0, 993(%rsp)
	movb	$0, 992(%rsp)
	movb	$0, 991(%rsp)
	movb	$0, 990(%rsp)
	movb	$0, 989(%rsp)
	movb	$0, 988(%rsp)
	movb	$0, 987(%rsp)
	movb	$0, 986(%rsp)
	movb	$0, 985(%rsp)
	movb	$0, 984(%rsp)
	movb	$0, 983(%rsp)
	movb	$0, 982(%rsp)
	movb	$0, 981(%rsp)
	movb	$0, 980(%rsp)
	movb	$0, 979(%rsp)
	movb	$0, 978(%rsp)
	movb	$0, 977(%rsp)
	movb	$0, 976(%rsp)
	movb	$0, 975(%rsp)
	movb	$0, 974(%rsp)
	movb	$0, 973(%rsp)
	movb	$0, 972(%rsp)
	movb	$0, 971(%rsp)
	movb	$0, 970(%rsp)
	movb	$0, 969(%rsp)
	movb	$0, 968(%rsp)
	movb	$0, 967(%rsp)
	movb	$0, 966(%rsp)
	movb	$0, 965(%rsp)
	movb	$0, 964(%rsp)
	movb	$0, 963(%rsp)
	movb	$0, 962(%rsp)
	movb	$0, 961(%rsp)
	movb	$0, 960(%rsp)
	movb	$0, 959(%rsp)
	movb	$0, 958(%rsp)
	movb	$0, 957(%rsp)
	movb	$0, 956(%rsp)
	movb	$0, 955(%rsp)
	movb	$0, 954(%rsp)
	movb	$0, 953(%rsp)
	movb	$0, 952(%rsp)
	movb	$0, 951(%rsp)
	movb	$0, 950(%rsp)
	movb	$0, 949(%rsp)
	movb	$0, 948(%rsp)
	movb	$0, 947(%rsp)
	movb	$0, 946(%rsp)
	movb	$0, 945(%rsp)
	movb	$0, 944(%rsp)
	movb	$0, 943(%rsp)
	movb	$0, 942(%rsp)
	movb	$0, 941(%rsp)
	movb	$0, 940(%rsp)
	movb	$0, 939(%rsp)
	movb	$0, 938(%rsp)
	movb	$0, 937(%rsp)
	movb	$0, 936(%rsp)
	movb	$0, 935(%rsp)
	movb	$0, 934(%rsp)
	movb	$0, 933(%rsp)
	movb	$0, 932(%rsp)
	movb	$0, 931(%rsp)
	movb	$0, 930(%rsp)
	movb	$0, 929(%rsp)
	movb	$0, 928(%rsp)
	movb	$0, 927(%rsp)
	movb	$0, 926(%rsp)
	movb	$0, 925(%rsp)
	movb	$0, 924(%rsp)
	movb	$0, 923(%rsp)
	movb	$0, 922(%rsp)
	movb	$0, 921(%rsp)
	movb	$0, 920(%rsp)
	movb	$0, 919(%rsp)
	movb	$0, 918(%rsp)
	movb	$0, 917(%rsp)
	movb	$0, 916(%rsp)
	movb	$0, 915(%rsp)
	movb	$0, 914(%rsp)
	movb	$0, 913(%rsp)
	movb	$0, 912(%rsp)
	movb	$0, 911(%rsp)
	movb	$0, 910(%rsp)
	movb	$0, 909(%rsp)
	movb	$0, 908(%rsp)
	movb	$0, 907(%rsp)
	movb	$0, 906(%rsp)
	movb	$0, 905(%rsp)
	movb	$0, 904(%rsp)
	movb	$0, 903(%rsp)
	movb	$0, 902(%rsp)
	movb	$0, 901(%rsp)
	movb	$0, 900(%rsp)
	movb	$0, 899(%rsp)
	movb	$0, 898(%rsp)
	movb	$0, 897(%rsp)
	movb	$0, 896(%rsp)
	movb	$0, 895(%rsp)
	movb	$0, 894(%rsp)
	movb	$0, 893(%rsp)
	movb	$0, 892(%rsp)
	movb	$0, 891(%rsp)
	movb	$0, 890(%rsp)
	movb	$0, 889(%rsp)
	movb	$0, 888(%rsp)
	movb	$0, 887(%rsp)
	movb	$0, 886(%rsp)
	movb	$0, 885(%rsp)
	movb	$0, 884(%rsp)
	movb	$0, 883(%rsp)
	movb	$0, 882(%rsp)
	movb	$0, 881(%rsp)
	movb	$0, 880(%rsp)
	movb	$0, 879(%rsp)
	movb	$0, 878(%rsp)
	movb	$0, 877(%rsp)
	movb	$0, 876(%rsp)
	movb	$0, 875(%rsp)
	movb	$0, 874(%rsp)
	movb	$0, 873(%rsp)
	movb	$0, 872(%rsp)
	movb	$0, 871(%rsp)
	movb	$0, 870(%rsp)
	movb	$0, 869(%rsp)
	movb	$0, 868(%rsp)
	movb	$0, 867(%rsp)
	movb	$0, 866(%rsp)
	movb	$0, 865(%rsp)
	movb	$0, 864(%rsp)
	movb	$0, 863(%rsp)
	movb	$0, 862(%rsp)
	movb	$0, 861(%rsp)
	movb	$0, 860(%rsp)
	movb	$0, 859(%rsp)
	movb	$0, 858(%rsp)
	movb	$0, 857(%rsp)
	movb	$0, 856(%rsp)
	movb	$0, 855(%rsp)
	movb	$0, 854(%rsp)
	movb	$0, 853(%rsp)
	movb	$0, 852(%rsp)
	movb	$0, 851(%rsp)
	movb	$0, 850(%rsp)
	movb	$0, 849(%rsp)
	movb	$0, 848(%rsp)
	movb	$0, 847(%rsp)
	movb	$0, 846(%rsp)
	movb	$0, 845(%rsp)
	movb	$0, 844(%rsp)
	movb	$0, 843(%rsp)
	movb	$0, 842(%rsp)
	movb	$0, 841(%rsp)
	movb	$0, 840(%rsp)
	movb	$0, 839(%rsp)
	movb	$0, 838(%rsp)
	movb	$0, 837(%rsp)
	movb	$0, 836(%rsp)
	movb	$0, 835(%rsp)
	movb	$0, 834(%rsp)
	movb	$0, 833(%rsp)
	movb	$0, 832(%rsp)
	movb	$0, 831(%rsp)
	movb	$0, 830(%rsp)
	movb	$0, 829(%rsp)
	movb	$0, 828(%rsp)
	movb	$0, 827(%rsp)
	movb	$0, 826(%rsp)
	movb	$0, 825(%rsp)
	movb	$0, 824(%rsp)
	movb	$0, 823(%rsp)
	movb	$0, 822(%rsp)
	movb	$0, 821(%rsp)
	movb	$0, 820(%rsp)
	movb	$0, 819(%rsp)
	movb	$0, 818(%rsp)
	movb	$0, 817(%rsp)
	movb	$0, 816(%rsp)
	movb	$0, 815(%rsp)
	movb	$0, 814(%rsp)
	movb	$0, 813(%rsp)
	movb	$0, 812(%rsp)
	movb	$0, 811(%rsp)
	movb	$0, 810(%rsp)
	movb	$0, 809(%rsp)
	movb	$0, 808(%rsp)
	movb	$0, 807(%rsp)
	movb	$0, 806(%rsp)
	movb	$0, 805(%rsp)
	movb	$0, 804(%rsp)
	movb	$0, 803(%rsp)
	movb	$0, 802(%rsp)
	movb	$0, 801(%rsp)
	movb	$0, 800(%rsp)
	movb	$0, 799(%rsp)
	movb	$0, 798(%rsp)
	movb	$0, 797(%rsp)
	movb	$0, 796(%rsp)
	movb	$0, 795(%rsp)
	movb	$0, 794(%rsp)
	movb	$0, 793(%rsp)
	movb	$0, 792(%rsp)
	movb	$0, 791(%rsp)
	movb	$0, 790(%rsp)
	movb	$0, 789(%rsp)
	movb	$0, 788(%rsp)
	movb	$0, 787(%rsp)
	movb	$0, 786(%rsp)
	movb	$0, 785(%rsp)
	movb	$0, 784(%rsp)
	movb	$0, 783(%rsp)
	movb	$0, 782(%rsp)
	movb	$0, 781(%rsp)
	movb	$0, 780(%rsp)
	movb	$0, 779(%rsp)
	movb	$0, 778(%rsp)
	movb	$0, 777(%rsp)
	movb	$0, 776(%rsp)
	movb	$0, 775(%rsp)
	movb	$0, 774(%rsp)
	movb	$0, 773(%rsp)
	movb	$0, 772(%rsp)
	movb	$0, 771(%rsp)
	movb	$0, 770(%rsp)
	movb	$0, 769(%rsp)
	movb	$0, 768(%rsp)
	movb	$0, 767(%rsp)
	movb	$0, 766(%rsp)
	movb	$0, 765(%rsp)
	movb	$0, 764(%rsp)
	movb	$0, 763(%rsp)
	movb	$0, 762(%rsp)
	movb	$0, 761(%rsp)
	movb	$0, 760(%rsp)
	movb	$0, 759(%rsp)
	movb	$0, 758(%rsp)
	movb	$0, 757(%rsp)
	movb	$0, 756(%rsp)
	movb	$0, 755(%rsp)
	movb	$0, 754(%rsp)
	movb	$0, 753(%rsp)
	movb	$0, 752(%rsp)
	movb	$0, 751(%rsp)
	movb	$0, 750(%rsp)
	movb	$0, 749(%rsp)
	movb	$0, 748(%rsp)
	movb	$0, 747(%rsp)
	movb	$0, 746(%rsp)
	movb	$0, 745(%rsp)
	movb	$0, 744(%rsp)
	movb	$0, 743(%rsp)
	movb	$0, 742(%rsp)
	movb	$0, 741(%rsp)
	movb	$0, 740(%rsp)
	movb	$0, 739(%rsp)
	movb	$0, 738(%rsp)
	movb	$0, 737(%rsp)
	movb	$0, 736(%rsp)
	movb	$0, 735(%rsp)
	movb	$0, 734(%rsp)
	movb	$0, 733(%rsp)
	movb	$0, 732(%rsp)
	movb	$0, 731(%rsp)
	movb	$0, 730(%rsp)
	movb	$0, 729(%rsp)
	movb	$0, 728(%rsp)
	movb	$0, 727(%rsp)
	movb	$0, 726(%rsp)
	movb	$0, 725(%rsp)
	movb	$0, 724(%rsp)
	movb	$0, 723(%rsp)
	movb	$0, 722(%rsp)
	movb	$0, 721(%rsp)
	movb	$0, 720(%rsp)
	movb	$0, 719(%rsp)
	movb	$0, 718(%rsp)
	movb	$0, 717(%rsp)
	movb	$0, 716(%rsp)
	movb	$0, 715(%rsp)
	movb	$0, 714(%rsp)
	movb	$0, 713(%rsp)
	movb	$0, 712(%rsp)
	movb	$0, 711(%rsp)
	movb	$0, 710(%rsp)
	movb	$0, 709(%rsp)
	movb	$0, 708(%rsp)
	movb	$0, 707(%rsp)
	movb	$0, 706(%rsp)
	movb	$0, 705(%rsp)
	movb	$0, 704(%rsp)
	movb	$0, 703(%rsp)
	movb	$0, 702(%rsp)
	movb	$0, 701(%rsp)
	movb	$0, 700(%rsp)
	movb	$0, 699(%rsp)
	movb	$0, 698(%rsp)
	movb	$0, 697(%rsp)
	movb	$0, 696(%rsp)
	movb	$0, 695(%rsp)
	movb	$0, 694(%rsp)
	movb	$0, 693(%rsp)
	movb	$0, 692(%rsp)
	movb	$0, 691(%rsp)
	movb	$0, 690(%rsp)
	movb	$0, 689(%rsp)
	movb	$0, 688(%rsp)
	movb	$0, 687(%rsp)
	movb	$0, 686(%rsp)
	movb	$0, 685(%rsp)
	movb	$0, 684(%rsp)
	movb	$0, 683(%rsp)
	movb	$0, 682(%rsp)
	movb	$0, 681(%rsp)
	movb	$0, 680(%rsp)
	movb	$0, 679(%rsp)
	movb	$0, 678(%rsp)
	movb	$0, 677(%rsp)
	movb	$0, 676(%rsp)
	movb	$0, 675(%rsp)
	movb	$0, 674(%rsp)
	movb	$0, 673(%rsp)
	movb	$0, 672(%rsp)
	movb	$0, 671(%rsp)
	movb	$0, 670(%rsp)
	movb	$0, 669(%rsp)
	movb	$0, 668(%rsp)
	movb	$0, 667(%rsp)
	movb	$0, 666(%rsp)
	movb	$0, 665(%rsp)
	movb	$0, 664(%rsp)
	movb	$0, 663(%rsp)
	movb	$0, 662(%rsp)
	movb	$0, 661(%rsp)
	movb	$0, 660(%rsp)
	movb	$0, 659(%rsp)
	movb	$0, 658(%rsp)
	movb	$0, 657(%rsp)
	movb	$0, 656(%rsp)
	movb	$0, 655(%rsp)
	movb	$0, 654(%rsp)
	movb	$0, 653(%rsp)
	movb	$0, 652(%rsp)
	movb	$0, 651(%rsp)
	movb	$0, 650(%rsp)
	movb	$0, 649(%rsp)
	movb	$0, 648(%rsp)
	movb	$0, 647(%rsp)
	movb	$0, 646(%rsp)
	movb	$0, 645(%rsp)
	movb	$0, 644(%rsp)
	movb	$0, 643(%rsp)
	movb	$0, 642(%rsp)
	movb	$0, 641(%rsp)
	movb	$0, 640(%rsp)
	movb	$0, 639(%rsp)
	movb	$0, 638(%rsp)
	movb	$0, 637(%rsp)
	movb	$0, 636(%rsp)
	movb	$0, 635(%rsp)
	movb	$0, 634(%rsp)
	movb	$0, 633(%rsp)
	movb	$0, 632(%rsp)
	movb	$0, 631(%rsp)
	movb	$0, 630(%rsp)
	movb	$0, 629(%rsp)
	movb	$0, 628(%rsp)
	movb	$0, 627(%rsp)
	movb	$0, 626(%rsp)
	movb	$0, 625(%rsp)
	movb	$0, 624(%rsp)
	movb	$0, 623(%rsp)
	movb	$0, 622(%rsp)
	movb	$0, 621(%rsp)
	movb	$0, 620(%rsp)
	movb	$0, 619(%rsp)
	movb	$0, 618(%rsp)
	movb	$0, 617(%rsp)
	movb	$0, 616(%rsp)
	movb	$0, 615(%rsp)
	movb	$0, 614(%rsp)
	movb	$0, 613(%rsp)
	movb	$0, 612(%rsp)
	movb	$0, 611(%rsp)
	movb	$0, 610(%rsp)
	movb	$0, 609(%rsp)
	movb	$0, 608(%rsp)
	movb	$0, 607(%rsp)
	movb	$0, 606(%rsp)
	movb	$0, 605(%rsp)
	movb	$0, 604(%rsp)
	movb	$0, 603(%rsp)
	movb	$0, 602(%rsp)
	movb	$0, 601(%rsp)
	movb	$0, 600(%rsp)
	movb	$0, 599(%rsp)
	movb	$0, 598(%rsp)
	movb	$0, 597(%rsp)
	movb	$0, 596(%rsp)
	movb	$0, 595(%rsp)
	movb	$0, 594(%rsp)
	movb	$0, 593(%rsp)
	movb	$0, 592(%rsp)
	movb	$0, 591(%rsp)
	movb	$0, 590(%rsp)
	movb	$0, 589(%rsp)
	movb	$0, 588(%rsp)
	movb	$0, 587(%rsp)
	movb	$0, 586(%rsp)
	movb	$0, 585(%rsp)
	movb	$0, 584(%rsp)
	movb	$0, 583(%rsp)
	movb	$0, 582(%rsp)
	movb	$0, 581(%rsp)
	movb	$0, 580(%rsp)
	movb	$0, 579(%rsp)
	movb	$0, 578(%rsp)
	movb	$0, 577(%rsp)
	movb	$0, 576(%rsp)
	movb	$0, 575(%rsp)
	movb	$0, 574(%rsp)
	movb	$0, 573(%rsp)
	movb	$0, 572(%rsp)
	movb	$0, 571(%rsp)
	movb	$0, 570(%rsp)
	movb	$0, 569(%rsp)
	movb	$0, 568(%rsp)
	movb	$0, 567(%rsp)
	movb	$0, 566(%rsp)
	movb	$0, 565(%rsp)
	movb	$0, 564(%rsp)
	movb	$0, 563(%rsp)
	movb	$0, 562(%rsp)
	movb	$0, 561(%rsp)
	movb	$0, 560(%rsp)
	movb	$0, 559(%rsp)
	movb	$0, 558(%rsp)
	movb	$0, 557(%rsp)
	movb	$0, 556(%rsp)
	movb	$0, 555(%rsp)
	movb	$0, 554(%rsp)
	movb	$0, 553(%rsp)
	movb	$0, 552(%rsp)
	movb	$0, 551(%rsp)
	movb	$0, 550(%rsp)
	movb	$0, 549(%rsp)
	movb	$0, 548(%rsp)
	movb	$0, 547(%rsp)
	movb	$0, 546(%rsp)
	movb	$0, 545(%rsp)
	movb	$0, 544(%rsp)
	movb	$0, 543(%rsp)
	movb	$0, 542(%rsp)
	movb	$0, 541(%rsp)
	movb	$0, 540(%rsp)
	movb	$0, 539(%rsp)
	movb	$0, 538(%rsp)
	movb	$0, 537(%rsp)
	movb	$0, 536(%rsp)
	movb	$0, 535(%rsp)
	movb	$0, 534(%rsp)
	movb	$0, 533(%rsp)
	movb	$0, 532(%rsp)
	movb	$0, 531(%rsp)
	movb	$0, 530(%rsp)
	movb	$0, 529(%rsp)
	movb	$0, 528(%rsp)
	movb	$0, 527(%rsp)
	movb	$0, 526(%rsp)
	movb	$0, 525(%rsp)
	movb	$0, 524(%rsp)
	movb	$0, 523(%rsp)
	movb	$0, 522(%rsp)
	movb	$0, 521(%rsp)
	movb	$0, 520(%rsp)
	movb	$0, 519(%rsp)
	movb	$0, 518(%rsp)
	movb	$0, 517(%rsp)
	movb	$0, 516(%rsp)
	movb	$0, 515(%rsp)
	movb	$0, 514(%rsp)
	movb	$0, 513(%rsp)
	movb	$0, 512(%rsp)
	movb	$0, 511(%rsp)
	movb	$0, 510(%rsp)
	movb	$0, 509(%rsp)
	movb	$0, 508(%rsp)
	movb	$0, 507(%rsp)
	movb	$0, 506(%rsp)
	movb	$0, 505(%rsp)
	movb	$0, 504(%rsp)
	movb	$0, 503(%rsp)
	movb	$0, 502(%rsp)
	movb	$0, 501(%rsp)
	movb	$0, 500(%rsp)
	movb	$0, 499(%rsp)
	movb	$0, 498(%rsp)
	movb	$0, 497(%rsp)
	movb	$0, 496(%rsp)
	movb	$0, 495(%rsp)
	movb	$0, 494(%rsp)
	movb	$0, 493(%rsp)
	movb	$0, 492(%rsp)
	movb	$0, 491(%rsp)
	movb	$0, 490(%rsp)
	movb	$0, 489(%rsp)
	movb	$0, 488(%rsp)
	movb	$0, 487(%rsp)
	movb	$0, 486(%rsp)
	movb	$0, 485(%rsp)
	movb	$0, 484(%rsp)
	movb	$0, 483(%rsp)
	movb	$0, 482(%rsp)
	movb	$0, 481(%rsp)
	movb	$0, 480(%rsp)
	movb	$0, 479(%rsp)
	movb	$0, 478(%rsp)
	movb	$0, 477(%rsp)
	movb	$0, 476(%rsp)
	movb	$0, 475(%rsp)
	movb	$0, 474(%rsp)
	movb	$0, 473(%rsp)
	movb	$0, 472(%rsp)
	movb	$0, 471(%rsp)
	movb	$0, 470(%rsp)
	movb	$0, 469(%rsp)
	movb	$0, 468(%rsp)
	movb	$0, 467(%rsp)
	movb	$0, 466(%rsp)
	movb	$0, 465(%rsp)
	movb	$0, 464(%rsp)
	movb	$0, 463(%rsp)
	movb	$0, 462(%rsp)
	movb	$0, 461(%rsp)
	movb	$0, 460(%rsp)
	movb	$0, 459(%rsp)
	movb	$0, 458(%rsp)
	movb	$0, 457(%rsp)
	movb	$0, 456(%rsp)
	movb	$0, 455(%rsp)
	movb	$0, 454(%rsp)
	movb	$0, 453(%rsp)
	movb	$0, 452(%rsp)
	movb	$0, 451(%rsp)
	movb	$0, 450(%rsp)
	movb	$0, 449(%rsp)
	movb	$0, 448(%rsp)
	movb	$0, 447(%rsp)
	movb	$0, 446(%rsp)
	movb	$0, 445(%rsp)
	movb	$0, 444(%rsp)
	movb	$0, 443(%rsp)
	movb	$0, 442(%rsp)
	movb	$0, 441(%rsp)
	movb	$0, 440(%rsp)
	movb	$0, 439(%rsp)
	movb	$0, 438(%rsp)
	movb	$0, 437(%rsp)
	movb	$0, 436(%rsp)
	movb	$0, 435(%rsp)
	movb	$0, 434(%rsp)
	movb	$0, 433(%rsp)
	movb	$0, 432(%rsp)
	movb	$0, 431(%rsp)
	movb	$0, 430(%rsp)
	movb	$0, 429(%rsp)
	movb	$0, 428(%rsp)
	movb	$0, 427(%rsp)
	movb	$0, 426(%rsp)
	movb	$0, 425(%rsp)
	movb	$0, 424(%rsp)
	movb	$0, 423(%rsp)
	movb	$0, 422(%rsp)
	movb	$0, 421(%rsp)
	movb	$0, 420(%rsp)
	movb	$0, 419(%rsp)
	movb	$0, 418(%rsp)
	movb	$0, 417(%rsp)
	movb	$0, 416(%rsp)
	movb	$0, 415(%rsp)
	movb	$0, 414(%rsp)
	movb	$0, 413(%rsp)
	movb	$0, 412(%rsp)
	movb	$0, 411(%rsp)
	movb	$0, 410(%rsp)
	movb	$0, 409(%rsp)
	movb	$0, 408(%rsp)
	movb	$0, 407(%rsp)
	movb	$0, 406(%rsp)
	movb	$0, 405(%rsp)
	movb	$0, 404(%rsp)
	movb	$0, 403(%rsp)
	movb	$0, 402(%rsp)
	movb	$0, 401(%rsp)
	movb	$0, 400(%rsp)
	movb	$0, 399(%rsp)
	movb	$0, 398(%rsp)
	movb	$0, 397(%rsp)
	movb	$0, 396(%rsp)
	movb	$0, 395(%rsp)
	movb	$0, 394(%rsp)
	movb	$0, 393(%rsp)
	movb	$0, 392(%rsp)
	movb	$0, 391(%rsp)
	movb	$0, 390(%rsp)
	movb	$0, 389(%rsp)
	movb	$0, 388(%rsp)
	movb	$0, 387(%rsp)
	movb	$0, 386(%rsp)
	movb	$0, 385(%rsp)
	movb	$0, 384(%rsp)
	movb	$0, 383(%rsp)
	movb	$0, 382(%rsp)
	movb	$0, 381(%rsp)
	movb	$0, 380(%rsp)
	movb	$0, 379(%rsp)
	movb	$0, 378(%rsp)
	movb	$0, 377(%rsp)
	movb	$0, 376(%rsp)
	movb	$0, 375(%rsp)
	movb	$0, 374(%rsp)
	movb	$0, 373(%rsp)
	movb	$0, 372(%rsp)
	movb	$0, 371(%rsp)
	movb	$0, 370(%rsp)
	movb	$0, 369(%rsp)
	movb	$0, 368(%rsp)
	movb	$0, 367(%rsp)
	movb	$0, 366(%rsp)
	movb	$0, 365(%rsp)
	movb	$0, 364(%rsp)
	movb	$0, 363(%rsp)
	movb	$0, 362(%rsp)
	movb	$0, 361(%rsp)
	movb	$0, 360(%rsp)
	movb	$0, 359(%rsp)
	movb	$0, 358(%rsp)
	movb	$0, 357(%rsp)
	movb	$0, 356(%rsp)
	movb	$0, 355(%rsp)
	movb	$0, 354(%rsp)
	movb	$0, 353(%rsp)
	movb	$0, 352(%rsp)
	movb	$0, 351(%rsp)
	movb	$0, 350(%rsp)
	movb	$0, 349(%rsp)
	movb	$0, 348(%rsp)
	movb	$0, 347(%rsp)
	movb	$0, 346(%rsp)
	movb	$0, 345(%rsp)
	movb	$0, 344(%rsp)
	movb	$0, 343(%rsp)
	movb	$0, 342(%rsp)
	movb	$0, 341(%rsp)
	movb	$0, 340(%rsp)
	movb	$0, 339(%rsp)
	movb	$0, 338(%rsp)
	movb	$0, 337(%rsp)
	movb	$0, 336(%rsp)
	movb	$0, 335(%rsp)
	movb	$0, 334(%rsp)
	movb	$0, 333(%rsp)
	movb	$0, 332(%rsp)
	movb	$0, 331(%rsp)
	movb	$0, 330(%rsp)
	movb	$0, 329(%rsp)
	movb	$0, 328(%rsp)
	movb	$0, 327(%rsp)
	movb	$0, 326(%rsp)
	movb	$0, 325(%rsp)
	movb	$0, 324(%rsp)
	movb	$0, 323(%rsp)
	movb	$0, 322(%rsp)
	movb	$0, 321(%rsp)
	movb	$0, 320(%rsp)
	movb	$0, 319(%rsp)
	movb	$0, 318(%rsp)
	movb	$0, 317(%rsp)
	movb	$0, 316(%rsp)
	movb	$0, 315(%rsp)
	movb	$0, 314(%rsp)
	movb	$0, 313(%rsp)
	movb	$0, 312(%rsp)
	movb	$0, 311(%rsp)
	movb	$0, 310(%rsp)
	movb	$0, 309(%rsp)
	movb	$0, 308(%rsp)
	movb	$0, 307(%rsp)
	movb	$0, 306(%rsp)
	movb	$0, 305(%rsp)
	movb	$0, 304(%rsp)
	movb	$0, 303(%rsp)
	movb	$0, 302(%rsp)
	movb	$0, 301(%rsp)
	movb	$0, 300(%rsp)
	movb	$0, 299(%rsp)
	movb	$0, 298(%rsp)
	movb	$0, 297(%rsp)
	movb	$0, 296(%rsp)
	movb	$0, 295(%rsp)
	movb	$0, 294(%rsp)
	movb	$0, 293(%rsp)
	movb	$0, 292(%rsp)
	movb	$0, 291(%rsp)
	movb	$0, 290(%rsp)
	movb	$0, 289(%rsp)
	movb	$0, 288(%rsp)
	movb	$0, 287(%rsp)
	movb	$0, 286(%rsp)
	movb	$0, 285(%rsp)
	movb	$0, 284(%rsp)
	movb	$0, 283(%rsp)
	movb	$0, 282(%rsp)
	movb	$0, 281(%rsp)
	movb	$0, 280(%rsp)
	movb	$0, 279(%rsp)
	movb	$0, 278(%rsp)
	movb	$0, 277(%rsp)
	movb	$0, 276(%rsp)
	movb	$0, 275(%rsp)
	movb	$0, 274(%rsp)
	movb	$0, 273(%rsp)
	movb	$0, 272(%rsp)
	movb	$0, 271(%rsp)
	movb	$0, 270(%rsp)
	movb	$0, 269(%rsp)
	movb	$0, 268(%rsp)
	movb	$0, 267(%rsp)
	movb	$0, 266(%rsp)
	movb	$0, 265(%rsp)
	movb	$0, 264(%rsp)
	movb	$0, 263(%rsp)
	movb	$0, 262(%rsp)
	movb	$0, 261(%rsp)
	movb	$0, 260(%rsp)
	movb	$0, 259(%rsp)
	movb	$0, 258(%rsp)
	movb	$0, 257(%rsp)
	movb	$0, 256(%rsp)
	movb	$0, 255(%rsp)
	movb	$0, 254(%rsp)
	movb	$0, 253(%rsp)
	movb	$0, 252(%rsp)
	movb	$0, 251(%rsp)
	movb	$0, 250(%rsp)
	movb	$0, 249(%rsp)
	movb	$0, 248(%rsp)
	movb	$0, 247(%rsp)
	movb	$0, 246(%rsp)
	movb	$0, 245(%rsp)
	movb	$0, 244(%rsp)
	movb	$0, 243(%rsp)
	movb	$0, 242(%rsp)
	movb	$0, 241(%rsp)
	movb	$0, 240(%rsp)
	movb	$0, 239(%rsp)
	movb	$0, 238(%rsp)
	movb	$0, 237(%rsp)
	movb	$0, 236(%rsp)
	movb	$0, 235(%rsp)
	movb	$0, 234(%rsp)
	movb	$0, 233(%rsp)
	movb	$0, 232(%rsp)
	movb	$0, 231(%rsp)
	movb	$0, 230(%rsp)
	movb	$0, 229(%rsp)
	movb	$0, 228(%rsp)
	movb	$0, 227(%rsp)
	movb	$0, 226(%rsp)
	movb	$0, 225(%rsp)
	movb	$0, 224(%rsp)
	movb	$0, 223(%rsp)
	movb	$0, 222(%rsp)
	movb	$0, 221(%rsp)
	movb	$0, 220(%rsp)
	movb	$0, 219(%rsp)
	movb	$0, 218(%rsp)
	movb	$0, 217(%rsp)
	movb	$0, 216(%rsp)
	movb	$0, 215(%rsp)
	movb	$0, 214(%rsp)
	movb	$0, 213(%rsp)
	movb	$0, 212(%rsp)
	movb	$0, 211(%rsp)
	movb	$0, 210(%rsp)
	movb	$0, 209(%rsp)
	movb	$0, 208(%rsp)
	movb	$0, 207(%rsp)
	movb	$0, 206(%rsp)
	movb	$0, 205(%rsp)
	movb	$0, 204(%rsp)
	movb	$0, 203(%rsp)
	movb	$0, 202(%rsp)
	movb	$0, 201(%rsp)
	movb	$0, 200(%rsp)
	movb	$0, 199(%rsp)
	movb	$0, 198(%rsp)
	movb	$0, 197(%rsp)
	movb	$0, 196(%rsp)
	movb	$0, 195(%rsp)
	movb	$0, 194(%rsp)
	movb	$0, 193(%rsp)
	movb	$0, 192(%rsp)
	movb	$0, 191(%rsp)
	movb	$0, 190(%rsp)
	movb	$0, 189(%rsp)
	movb	$0, 188(%rsp)
	movb	$0, 187(%rsp)
	movb	$0, 186(%rsp)
	movb	$0, 185(%rsp)
	movb	$0, 184(%rsp)
	movb	$0, 183(%rsp)
	movb	$0, 182(%rsp)
	movb	$0, 181(%rsp)
	movb	$0, 180(%rsp)
	movb	$0, 179(%rsp)
	movb	$0, 178(%rsp)
	movb	$0, 177(%rsp)
	movb	$0, 176(%rsp)
	movb	$0, 175(%rsp)
	movb	$0, 174(%rsp)
	movb	$0, 173(%rsp)
	movb	$0, 172(%rsp)
	movb	$0, 171(%rsp)
	movb	$0, 170(%rsp)
	movb	$0, 169(%rsp)
	movb	$0, 168(%rsp)
	movb	$0, 167(%rsp)
	movb	$0, 166(%rsp)
	movb	$0, 165(%rsp)
	movb	$0, 164(%rsp)
	movb	$0, 163(%rsp)
	movb	$0, 162(%rsp)
	movb	$0, 161(%rsp)
	movb	$0, 160(%rsp)
	movb	$0, 159(%rsp)
	movb	$0, 158(%rsp)
	movb	$0, 157(%rsp)
	movb	$0, 156(%rsp)
	movb	$0, 155(%rsp)
	movb	$0, 154(%rsp)
	movb	$0, 153(%rsp)
	movb	$0, 152(%rsp)
	movb	$0, 151(%rsp)
	movb	$0, 150(%rsp)
	movb	$0, 149(%rsp)
	movb	$0, 148(%rsp)
	movb	$0, 147(%rsp)
	movb	$0, 146(%rsp)
	movb	$0, 145(%rsp)
	movb	$0, 144(%rsp)
	movb	$0, 143(%rsp)
	movb	$0, 142(%rsp)
	movb	$0, 141(%rsp)
	movb	$0, 140(%rsp)
	movb	$0, 139(%rsp)
	movb	$0, 138(%rsp)
	movb	$0, 137(%rsp)
	movb	$0, 136(%rsp)
	movb	$0, 135(%rsp)
	movb	$0, 134(%rsp)
	movb	$0, 133(%rsp)
	movb	$0, 132(%rsp)
	movb	$0, 131(%rsp)
	movb	$0, 130(%rsp)
	movb	$0, 129(%rsp)
	movb	$0, 128(%rsp)
	movb	$0, 127(%rsp)
	movb	$0, 126(%rsp)
	movb	$0, 125(%rsp)
	movb	$0, 124(%rsp)
	movb	$0, 123(%rsp)
	movb	$0, 122(%rsp)
	movb	$0, 121(%rsp)
	movb	$0, 120(%rsp)
	movb	$0, 119(%rsp)
	movb	$0, 118(%rsp)
	movb	$0, 117(%rsp)
	movb	$0, 116(%rsp)
	movb	$0, 115(%rsp)
	movb	$0, 114(%rsp)
	movb	$0, 113(%rsp)
	movb	$0, 112(%rsp)
	movb	$0, 111(%rsp)
	movb	$0, 110(%rsp)
	movb	$0, 109(%rsp)
	movb	$0, 108(%rsp)
	movb	$0, 107(%rsp)
	movb	$0, 106(%rsp)
	movb	$0, 105(%rsp)
	movb	$0, 104(%rsp)
	movb	$0, 103(%rsp)
	movb	$0, 102(%rsp)
	movb	$0, 101(%rsp)
	movb	$0, 100(%rsp)
	movb	$0, 99(%rsp)
	movb	$0, 98(%rsp)
	movb	$0, 97(%rsp)
	movb	$0, 96(%rsp)
	movb	$0, 95(%rsp)
	movb	$0, 94(%rsp)
	movb	$0, 93(%rsp)
	movb	$0, 92(%rsp)
	movb	$0, 91(%rsp)
	movb	$0, 90(%rsp)
	movb	$0, 89(%rsp)
	movb	$0, 88(%rsp)
	movb	$0, 87(%rsp)
	movb	$0, 86(%rsp)
	movb	$0, 85(%rsp)
	movb	$0, 84(%rsp)
	movb	$0, 83(%rsp)
	movb	$0, 82(%rsp)
	movb	$0, 81(%rsp)
	movb	$0, 80(%rsp)
	movb	$0, 79(%rsp)
	movb	$0, 78(%rsp)
	movb	$0, 77(%rsp)
	movb	$0, 76(%rsp)
	movb	$0, 75(%rsp)
	movb	$0, 74(%rsp)
	movb	$0, 73(%rsp)
	movb	$0, 72(%rsp)
	movb	$0, 71(%rsp)
	movb	$0, 70(%rsp)
	movb	$0, 69(%rsp)
	movb	$0, 68(%rsp)
	movb	$0, 67(%rsp)
	movb	$0, 66(%rsp)
	movb	$0, 65(%rsp)
	movb	$0, 64(%rsp)
	movb	$0, 63(%rsp)
	movb	$0, 62(%rsp)
	movb	$0, 61(%rsp)
	movb	$0, 60(%rsp)
	movb	$0, 59(%rsp)
	movb	$0, 58(%rsp)
	movb	$0, 57(%rsp)
	movb	$0, 56(%rsp)
	movb	$0, 55(%rsp)
	movb	$0, 54(%rsp)
	movb	$0, 53(%rsp)
	movb	$0, 52(%rsp)
	movb	$0, 51(%rsp)
	movb	$0, 50(%rsp)
	movb	$0, 49(%rsp)
	movb	$0, 48(%rsp)
	movb	$0, 47(%rsp)
	movb	$0, 46(%rsp)
	movb	$0, 45(%rsp)
	movb	$0, 44(%rsp)
	movb	$0, 43(%rsp)
	movb	$0, 42(%rsp)
	movb	$0, 41(%rsp)
	movb	$0, 40(%rsp)
	movb	$0, 39(%rsp)
	movb	$0, 38(%rsp)
	movb	$0, 37(%rsp)
	movb	$0, 36(%rsp)
	movb	$0, 35(%rsp)
	movb	$0, 34(%rsp)
	movb	$0, 33(%rsp)
	movb	$0, 32(%rsp)
	movb	$0, 31(%rsp)
	movb	$0, 30(%rsp)
	movb	$0, 29(%rsp)
	movb	$0, 28(%rsp)
	movb	$0, 27(%rsp)
	movb	$0, 26(%rsp)
	movb	$0, 25(%rsp)
	movb	$0, 24(%rsp)
	movb	$0, 23(%rsp)
	movb	$0, 22(%rsp)
	movb	$0, 21(%rsp)
	movb	$0, 20(%rsp)
	movb	$0, 19(%rsp)
	movb	$0, 18(%rsp)
	movb	$0, 17(%rsp)
	movb	$0, 16(%rsp)
	movb	$0, 15(%rsp)
	movb	$0, 14(%rsp)
	movb	$0, 13(%rsp)
	movb	$0, 12(%rsp)
	movb	$0, 11(%rsp)
	movb	$0, 10(%rsp)
	movb	$0, 9(%rsp)
	movb	$0, 8(%rsp)
	movb	$0, 7(%rsp)
	movb	$0, 6(%rsp)
	movb	$0, 5(%rsp)
	movb	$0, 4(%rsp)
	movb	$0, 3(%rsp)
	movb	$0, 2(%rsp)
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
_wots_sign_jazz:
wots_sign_jazz:
	movq	%rsp, %rax
	leaq	-336(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 280(%rsp)
	movq	%rbp, 288(%rsp)
	movq	%r12, 296(%rsp)
	movq	%r13, 304(%rsp)
	movq	%r14, 312(%rsp)
	movq	%r15, 320(%rsp)
	movq	%rax, 328(%rsp)
	movq	%rdx, %r9
	movq	%rcx, %rax
	movq	%r8, (%rsp)
	leaq	8(%rsp), %rdx
	leaq	-8(%rsp), %rsp
	call	L_chain_lengths$1
Lwots_sign_jazz$69:
	leaq	8(%rsp), %rsp
	movq	%rax, %rdx
	movq	%r8, %rax
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
Lwots_sign_jazz$68:
	leaq	88(%rsp), %rsp
	movq	%rax, %r13
	movq	%rcx, %rsi
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	movq	%r13, %rdx
	movl	$0, %eax
	movl	8(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$67:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$1, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	32(%r13), %rdx
	movl	$0, %eax
	movl	12(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$66:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$2, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	64(%r13), %rdx
	movl	$0, %eax
	movl	16(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$65:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$3, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	96(%r13), %rdx
	movl	$0, %eax
	movl	20(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$64:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$4, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	128(%r13), %rdx
	movl	$0, %eax
	movl	24(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$63:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$5, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	160(%r13), %rdx
	movl	$0, %eax
	movl	28(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$62:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$6, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	192(%r13), %rdx
	movl	$0, %eax
	movl	32(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$61:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$7, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	224(%r13), %rdx
	movl	$0, %eax
	movl	36(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$60:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$8, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	256(%r13), %rdx
	movl	$0, %eax
	movl	40(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$59:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$9, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	288(%r13), %rdx
	movl	$0, %eax
	movl	44(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$58:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$10, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	320(%r13), %rdx
	movl	$0, %eax
	movl	48(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$57:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$11, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	352(%r13), %rdx
	movl	$0, %eax
	movl	52(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$56:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$12, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	384(%r13), %rdx
	movl	$0, %eax
	movl	56(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$55:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$13, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	416(%r13), %rdx
	movl	$0, %eax
	movl	60(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$54:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$14, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	448(%r13), %rdx
	movl	$0, %eax
	movl	64(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$53:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$15, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	480(%r13), %rdx
	movl	$0, %eax
	movl	68(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$52:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$16, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	512(%r13), %rdx
	movl	$0, %eax
	movl	72(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$51:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$17, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	544(%r13), %rdx
	movl	$0, %eax
	movl	76(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$50:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$18, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	576(%r13), %rdx
	movl	$0, %eax
	movl	80(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$49:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$19, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	608(%r13), %rdx
	movl	$0, %eax
	movl	84(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$48:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$20, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	640(%r13), %rdx
	movl	$0, %eax
	movl	88(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$47:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$21, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	672(%r13), %rdx
	movl	$0, %eax
	movl	92(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$46:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$22, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	704(%r13), %rdx
	movl	$0, %eax
	movl	96(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$45:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$23, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	736(%r13), %rdx
	movl	$0, %eax
	movl	100(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$44:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$24, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	768(%r13), %rdx
	movl	$0, %eax
	movl	104(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$43:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$25, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	800(%r13), %rdx
	movl	$0, %eax
	movl	108(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$42:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$26, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	832(%r13), %rdx
	movl	$0, %eax
	movl	112(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$41:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$27, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	864(%r13), %rdx
	movl	$0, %eax
	movl	116(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$40:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$28, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	896(%r13), %rdx
	movl	$0, %eax
	movl	120(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$39:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$29, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	928(%r13), %rdx
	movl	$0, %eax
	movl	124(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$38:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$30, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	960(%r13), %rdx
	movl	$0, %eax
	movl	128(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$37:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$31, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	992(%r13), %rdx
	movl	$0, %eax
	movl	132(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$36:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$32, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1024(%r13), %rdx
	movl	$0, %eax
	movl	136(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$35:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$33, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1056(%r13), %rdx
	movl	$0, %eax
	movl	140(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$34:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$34, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1088(%r13), %rdx
	movl	$0, %eax
	movl	144(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$33:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$35, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1120(%r13), %rdx
	movl	$0, %eax
	movl	148(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$32:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$36, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1152(%r13), %rdx
	movl	$0, %eax
	movl	152(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$31:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$37, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1184(%r13), %rdx
	movl	$0, %eax
	movl	156(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$30:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$38, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1216(%r13), %rdx
	movl	$0, %eax
	movl	160(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$29:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$39, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1248(%r13), %rdx
	movl	$0, %eax
	movl	164(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$28:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$40, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1280(%r13), %rdx
	movl	$0, %eax
	movl	168(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$27:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$41, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1312(%r13), %rdx
	movl	$0, %eax
	movl	172(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$26:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$42, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1344(%r13), %rdx
	movl	$0, %eax
	movl	176(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$25:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$43, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1376(%r13), %rdx
	movl	$0, %eax
	movl	180(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$24:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$44, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1408(%r13), %rdx
	movl	$0, %eax
	movl	184(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$23:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$45, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1440(%r13), %rdx
	movl	$0, %eax
	movl	188(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$22:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$46, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1472(%r13), %rdx
	movl	$0, %eax
	movl	192(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$21:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$47, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1504(%r13), %rdx
	movl	$0, %eax
	movl	196(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$20:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$48, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1536(%r13), %rdx
	movl	$0, %eax
	movl	200(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$19:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$49, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1568(%r13), %rdx
	movl	$0, %eax
	movl	204(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$18:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$50, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1600(%r13), %rdx
	movl	$0, %eax
	movl	208(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$17:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$51, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1632(%r13), %rdx
	movl	$0, %eax
	movl	212(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$16:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$52, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1664(%r13), %rdx
	movl	$0, %eax
	movl	216(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$15:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$53, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1696(%r13), %rdx
	movl	$0, %eax
	movl	220(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$14:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$54, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1728(%r13), %rdx
	movl	$0, %eax
	movl	224(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$13:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$55, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1760(%r13), %rdx
	movl	$0, %eax
	movl	228(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$12:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$56, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1792(%r13), %rdx
	movl	$0, %eax
	movl	232(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$11:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$57, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1824(%r13), %rdx
	movl	$0, %eax
	movl	236(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$10:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$58, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1856(%r13), %rdx
	movl	$0, %eax
	movl	240(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$9:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$59, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1888(%r13), %rdx
	movl	$0, %eax
	movl	244(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$8:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$60, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1920(%r13), %rdx
	movl	$0, %eax
	movl	248(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$7:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$61, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1952(%r13), %rdx
	movl	$0, %eax
	movl	252(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$6:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$62, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	1984(%r13), %rdx
	movl	$0, %eax
	movl	256(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$5:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$63, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	2016(%r13), %rdx
	movl	$0, %eax
	movl	260(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$4:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$64, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	2048(%r13), %rdx
	movl	$0, %eax
	movl	264(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$3:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$65, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	2080(%r13), %rdx
	movl	$0, %eax
	movl	268(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$2:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movl	$66, %eax
	movl	%eax, 20(%rsi)
	movq	(%rsp), %r8
	leaq	2112(%r13), %rdx
	movl	$0, %eax
	movl	272(%rsp), %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_sign_jazz$1:
	leaq	32(%rsp), %rsp
	movq	280(%rsp), %rbx
	movq	288(%rsp), %rbp
	movq	296(%rsp), %r12
	movq	304(%rsp), %r13
	movq	312(%rsp), %r14
	movq	320(%rsp), %r15
	movq	328(%rsp), %rsp
	movq	%rsp, %rsi
	andq	$-8, %rsp
	subq	$1280, %rsp
	movb	$0, 1279(%rsp)
	movb	$0, 1278(%rsp)
	movb	$0, 1277(%rsp)
	movb	$0, 1276(%rsp)
	movb	$0, 1275(%rsp)
	movb	$0, 1274(%rsp)
	movb	$0, 1273(%rsp)
	movb	$0, 1272(%rsp)
	movb	$0, 1271(%rsp)
	movb	$0, 1270(%rsp)
	movb	$0, 1269(%rsp)
	movb	$0, 1268(%rsp)
	movb	$0, 1267(%rsp)
	movb	$0, 1266(%rsp)
	movb	$0, 1265(%rsp)
	movb	$0, 1264(%rsp)
	movb	$0, 1263(%rsp)
	movb	$0, 1262(%rsp)
	movb	$0, 1261(%rsp)
	movb	$0, 1260(%rsp)
	movb	$0, 1259(%rsp)
	movb	$0, 1258(%rsp)
	movb	$0, 1257(%rsp)
	movb	$0, 1256(%rsp)
	movb	$0, 1255(%rsp)
	movb	$0, 1254(%rsp)
	movb	$0, 1253(%rsp)
	movb	$0, 1252(%rsp)
	movb	$0, 1251(%rsp)
	movb	$0, 1250(%rsp)
	movb	$0, 1249(%rsp)
	movb	$0, 1248(%rsp)
	movb	$0, 1247(%rsp)
	movb	$0, 1246(%rsp)
	movb	$0, 1245(%rsp)
	movb	$0, 1244(%rsp)
	movb	$0, 1243(%rsp)
	movb	$0, 1242(%rsp)
	movb	$0, 1241(%rsp)
	movb	$0, 1240(%rsp)
	movb	$0, 1239(%rsp)
	movb	$0, 1238(%rsp)
	movb	$0, 1237(%rsp)
	movb	$0, 1236(%rsp)
	movb	$0, 1235(%rsp)
	movb	$0, 1234(%rsp)
	movb	$0, 1233(%rsp)
	movb	$0, 1232(%rsp)
	movb	$0, 1231(%rsp)
	movb	$0, 1230(%rsp)
	movb	$0, 1229(%rsp)
	movb	$0, 1228(%rsp)
	movb	$0, 1227(%rsp)
	movb	$0, 1226(%rsp)
	movb	$0, 1225(%rsp)
	movb	$0, 1224(%rsp)
	movb	$0, 1223(%rsp)
	movb	$0, 1222(%rsp)
	movb	$0, 1221(%rsp)
	movb	$0, 1220(%rsp)
	movb	$0, 1219(%rsp)
	movb	$0, 1218(%rsp)
	movb	$0, 1217(%rsp)
	movb	$0, 1216(%rsp)
	movb	$0, 1215(%rsp)
	movb	$0, 1214(%rsp)
	movb	$0, 1213(%rsp)
	movb	$0, 1212(%rsp)
	movb	$0, 1211(%rsp)
	movb	$0, 1210(%rsp)
	movb	$0, 1209(%rsp)
	movb	$0, 1208(%rsp)
	movb	$0, 1207(%rsp)
	movb	$0, 1206(%rsp)
	movb	$0, 1205(%rsp)
	movb	$0, 1204(%rsp)
	movb	$0, 1203(%rsp)
	movb	$0, 1202(%rsp)
	movb	$0, 1201(%rsp)
	movb	$0, 1200(%rsp)
	movb	$0, 1199(%rsp)
	movb	$0, 1198(%rsp)
	movb	$0, 1197(%rsp)
	movb	$0, 1196(%rsp)
	movb	$0, 1195(%rsp)
	movb	$0, 1194(%rsp)
	movb	$0, 1193(%rsp)
	movb	$0, 1192(%rsp)
	movb	$0, 1191(%rsp)
	movb	$0, 1190(%rsp)
	movb	$0, 1189(%rsp)
	movb	$0, 1188(%rsp)
	movb	$0, 1187(%rsp)
	movb	$0, 1186(%rsp)
	movb	$0, 1185(%rsp)
	movb	$0, 1184(%rsp)
	movb	$0, 1183(%rsp)
	movb	$0, 1182(%rsp)
	movb	$0, 1181(%rsp)
	movb	$0, 1180(%rsp)
	movb	$0, 1179(%rsp)
	movb	$0, 1178(%rsp)
	movb	$0, 1177(%rsp)
	movb	$0, 1176(%rsp)
	movb	$0, 1175(%rsp)
	movb	$0, 1174(%rsp)
	movb	$0, 1173(%rsp)
	movb	$0, 1172(%rsp)
	movb	$0, 1171(%rsp)
	movb	$0, 1170(%rsp)
	movb	$0, 1169(%rsp)
	movb	$0, 1168(%rsp)
	movb	$0, 1167(%rsp)
	movb	$0, 1166(%rsp)
	movb	$0, 1165(%rsp)
	movb	$0, 1164(%rsp)
	movb	$0, 1163(%rsp)
	movb	$0, 1162(%rsp)
	movb	$0, 1161(%rsp)
	movb	$0, 1160(%rsp)
	movb	$0, 1159(%rsp)
	movb	$0, 1158(%rsp)
	movb	$0, 1157(%rsp)
	movb	$0, 1156(%rsp)
	movb	$0, 1155(%rsp)
	movb	$0, 1154(%rsp)
	movb	$0, 1153(%rsp)
	movb	$0, 1152(%rsp)
	movb	$0, 1151(%rsp)
	movb	$0, 1150(%rsp)
	movb	$0, 1149(%rsp)
	movb	$0, 1148(%rsp)
	movb	$0, 1147(%rsp)
	movb	$0, 1146(%rsp)
	movb	$0, 1145(%rsp)
	movb	$0, 1144(%rsp)
	movb	$0, 1143(%rsp)
	movb	$0, 1142(%rsp)
	movb	$0, 1141(%rsp)
	movb	$0, 1140(%rsp)
	movb	$0, 1139(%rsp)
	movb	$0, 1138(%rsp)
	movb	$0, 1137(%rsp)
	movb	$0, 1136(%rsp)
	movb	$0, 1135(%rsp)
	movb	$0, 1134(%rsp)
	movb	$0, 1133(%rsp)
	movb	$0, 1132(%rsp)
	movb	$0, 1131(%rsp)
	movb	$0, 1130(%rsp)
	movb	$0, 1129(%rsp)
	movb	$0, 1128(%rsp)
	movb	$0, 1127(%rsp)
	movb	$0, 1126(%rsp)
	movb	$0, 1125(%rsp)
	movb	$0, 1124(%rsp)
	movb	$0, 1123(%rsp)
	movb	$0, 1122(%rsp)
	movb	$0, 1121(%rsp)
	movb	$0, 1120(%rsp)
	movb	$0, 1119(%rsp)
	movb	$0, 1118(%rsp)
	movb	$0, 1117(%rsp)
	movb	$0, 1116(%rsp)
	movb	$0, 1115(%rsp)
	movb	$0, 1114(%rsp)
	movb	$0, 1113(%rsp)
	movb	$0, 1112(%rsp)
	movb	$0, 1111(%rsp)
	movb	$0, 1110(%rsp)
	movb	$0, 1109(%rsp)
	movb	$0, 1108(%rsp)
	movb	$0, 1107(%rsp)
	movb	$0, 1106(%rsp)
	movb	$0, 1105(%rsp)
	movb	$0, 1104(%rsp)
	movb	$0, 1103(%rsp)
	movb	$0, 1102(%rsp)
	movb	$0, 1101(%rsp)
	movb	$0, 1100(%rsp)
	movb	$0, 1099(%rsp)
	movb	$0, 1098(%rsp)
	movb	$0, 1097(%rsp)
	movb	$0, 1096(%rsp)
	movb	$0, 1095(%rsp)
	movb	$0, 1094(%rsp)
	movb	$0, 1093(%rsp)
	movb	$0, 1092(%rsp)
	movb	$0, 1091(%rsp)
	movb	$0, 1090(%rsp)
	movb	$0, 1089(%rsp)
	movb	$0, 1088(%rsp)
	movb	$0, 1087(%rsp)
	movb	$0, 1086(%rsp)
	movb	$0, 1085(%rsp)
	movb	$0, 1084(%rsp)
	movb	$0, 1083(%rsp)
	movb	$0, 1082(%rsp)
	movb	$0, 1081(%rsp)
	movb	$0, 1080(%rsp)
	movb	$0, 1079(%rsp)
	movb	$0, 1078(%rsp)
	movb	$0, 1077(%rsp)
	movb	$0, 1076(%rsp)
	movb	$0, 1075(%rsp)
	movb	$0, 1074(%rsp)
	movb	$0, 1073(%rsp)
	movb	$0, 1072(%rsp)
	movb	$0, 1071(%rsp)
	movb	$0, 1070(%rsp)
	movb	$0, 1069(%rsp)
	movb	$0, 1068(%rsp)
	movb	$0, 1067(%rsp)
	movb	$0, 1066(%rsp)
	movb	$0, 1065(%rsp)
	movb	$0, 1064(%rsp)
	movb	$0, 1063(%rsp)
	movb	$0, 1062(%rsp)
	movb	$0, 1061(%rsp)
	movb	$0, 1060(%rsp)
	movb	$0, 1059(%rsp)
	movb	$0, 1058(%rsp)
	movb	$0, 1057(%rsp)
	movb	$0, 1056(%rsp)
	movb	$0, 1055(%rsp)
	movb	$0, 1054(%rsp)
	movb	$0, 1053(%rsp)
	movb	$0, 1052(%rsp)
	movb	$0, 1051(%rsp)
	movb	$0, 1050(%rsp)
	movb	$0, 1049(%rsp)
	movb	$0, 1048(%rsp)
	movb	$0, 1047(%rsp)
	movb	$0, 1046(%rsp)
	movb	$0, 1045(%rsp)
	movb	$0, 1044(%rsp)
	movb	$0, 1043(%rsp)
	movb	$0, 1042(%rsp)
	movb	$0, 1041(%rsp)
	movb	$0, 1040(%rsp)
	movb	$0, 1039(%rsp)
	movb	$0, 1038(%rsp)
	movb	$0, 1037(%rsp)
	movb	$0, 1036(%rsp)
	movb	$0, 1035(%rsp)
	movb	$0, 1034(%rsp)
	movb	$0, 1033(%rsp)
	movb	$0, 1032(%rsp)
	movb	$0, 1031(%rsp)
	movb	$0, 1030(%rsp)
	movb	$0, 1029(%rsp)
	movb	$0, 1028(%rsp)
	movb	$0, 1027(%rsp)
	movb	$0, 1026(%rsp)
	movb	$0, 1025(%rsp)
	movb	$0, 1024(%rsp)
	movb	$0, 1023(%rsp)
	movb	$0, 1022(%rsp)
	movb	$0, 1021(%rsp)
	movb	$0, 1020(%rsp)
	movb	$0, 1019(%rsp)
	movb	$0, 1018(%rsp)
	movb	$0, 1017(%rsp)
	movb	$0, 1016(%rsp)
	movb	$0, 1015(%rsp)
	movb	$0, 1014(%rsp)
	movb	$0, 1013(%rsp)
	movb	$0, 1012(%rsp)
	movb	$0, 1011(%rsp)
	movb	$0, 1010(%rsp)
	movb	$0, 1009(%rsp)
	movb	$0, 1008(%rsp)
	movb	$0, 1007(%rsp)
	movb	$0, 1006(%rsp)
	movb	$0, 1005(%rsp)
	movb	$0, 1004(%rsp)
	movb	$0, 1003(%rsp)
	movb	$0, 1002(%rsp)
	movb	$0, 1001(%rsp)
	movb	$0, 1000(%rsp)
	movb	$0, 999(%rsp)
	movb	$0, 998(%rsp)
	movb	$0, 997(%rsp)
	movb	$0, 996(%rsp)
	movb	$0, 995(%rsp)
	movb	$0, 994(%rsp)
	movb	$0, 993(%rsp)
	movb	$0, 992(%rsp)
	movb	$0, 991(%rsp)
	movb	$0, 990(%rsp)
	movb	$0, 989(%rsp)
	movb	$0, 988(%rsp)
	movb	$0, 987(%rsp)
	movb	$0, 986(%rsp)
	movb	$0, 985(%rsp)
	movb	$0, 984(%rsp)
	movb	$0, 983(%rsp)
	movb	$0, 982(%rsp)
	movb	$0, 981(%rsp)
	movb	$0, 980(%rsp)
	movb	$0, 979(%rsp)
	movb	$0, 978(%rsp)
	movb	$0, 977(%rsp)
	movb	$0, 976(%rsp)
	movb	$0, 975(%rsp)
	movb	$0, 974(%rsp)
	movb	$0, 973(%rsp)
	movb	$0, 972(%rsp)
	movb	$0, 971(%rsp)
	movb	$0, 970(%rsp)
	movb	$0, 969(%rsp)
	movb	$0, 968(%rsp)
	movb	$0, 967(%rsp)
	movb	$0, 966(%rsp)
	movb	$0, 965(%rsp)
	movb	$0, 964(%rsp)
	movb	$0, 963(%rsp)
	movb	$0, 962(%rsp)
	movb	$0, 961(%rsp)
	movb	$0, 960(%rsp)
	movb	$0, 959(%rsp)
	movb	$0, 958(%rsp)
	movb	$0, 957(%rsp)
	movb	$0, 956(%rsp)
	movb	$0, 955(%rsp)
	movb	$0, 954(%rsp)
	movb	$0, 953(%rsp)
	movb	$0, 952(%rsp)
	movb	$0, 951(%rsp)
	movb	$0, 950(%rsp)
	movb	$0, 949(%rsp)
	movb	$0, 948(%rsp)
	movb	$0, 947(%rsp)
	movb	$0, 946(%rsp)
	movb	$0, 945(%rsp)
	movb	$0, 944(%rsp)
	movb	$0, 943(%rsp)
	movb	$0, 942(%rsp)
	movb	$0, 941(%rsp)
	movb	$0, 940(%rsp)
	movb	$0, 939(%rsp)
	movb	$0, 938(%rsp)
	movb	$0, 937(%rsp)
	movb	$0, 936(%rsp)
	movb	$0, 935(%rsp)
	movb	$0, 934(%rsp)
	movb	$0, 933(%rsp)
	movb	$0, 932(%rsp)
	movb	$0, 931(%rsp)
	movb	$0, 930(%rsp)
	movb	$0, 929(%rsp)
	movb	$0, 928(%rsp)
	movb	$0, 927(%rsp)
	movb	$0, 926(%rsp)
	movb	$0, 925(%rsp)
	movb	$0, 924(%rsp)
	movb	$0, 923(%rsp)
	movb	$0, 922(%rsp)
	movb	$0, 921(%rsp)
	movb	$0, 920(%rsp)
	movb	$0, 919(%rsp)
	movb	$0, 918(%rsp)
	movb	$0, 917(%rsp)
	movb	$0, 916(%rsp)
	movb	$0, 915(%rsp)
	movb	$0, 914(%rsp)
	movb	$0, 913(%rsp)
	movb	$0, 912(%rsp)
	movb	$0, 911(%rsp)
	movb	$0, 910(%rsp)
	movb	$0, 909(%rsp)
	movb	$0, 908(%rsp)
	movb	$0, 907(%rsp)
	movb	$0, 906(%rsp)
	movb	$0, 905(%rsp)
	movb	$0, 904(%rsp)
	movb	$0, 903(%rsp)
	movb	$0, 902(%rsp)
	movb	$0, 901(%rsp)
	movb	$0, 900(%rsp)
	movb	$0, 899(%rsp)
	movb	$0, 898(%rsp)
	movb	$0, 897(%rsp)
	movb	$0, 896(%rsp)
	movb	$0, 895(%rsp)
	movb	$0, 894(%rsp)
	movb	$0, 893(%rsp)
	movb	$0, 892(%rsp)
	movb	$0, 891(%rsp)
	movb	$0, 890(%rsp)
	movb	$0, 889(%rsp)
	movb	$0, 888(%rsp)
	movb	$0, 887(%rsp)
	movb	$0, 886(%rsp)
	movb	$0, 885(%rsp)
	movb	$0, 884(%rsp)
	movb	$0, 883(%rsp)
	movb	$0, 882(%rsp)
	movb	$0, 881(%rsp)
	movb	$0, 880(%rsp)
	movb	$0, 879(%rsp)
	movb	$0, 878(%rsp)
	movb	$0, 877(%rsp)
	movb	$0, 876(%rsp)
	movb	$0, 875(%rsp)
	movb	$0, 874(%rsp)
	movb	$0, 873(%rsp)
	movb	$0, 872(%rsp)
	movb	$0, 871(%rsp)
	movb	$0, 870(%rsp)
	movb	$0, 869(%rsp)
	movb	$0, 868(%rsp)
	movb	$0, 867(%rsp)
	movb	$0, 866(%rsp)
	movb	$0, 865(%rsp)
	movb	$0, 864(%rsp)
	movb	$0, 863(%rsp)
	movb	$0, 862(%rsp)
	movb	$0, 861(%rsp)
	movb	$0, 860(%rsp)
	movb	$0, 859(%rsp)
	movb	$0, 858(%rsp)
	movb	$0, 857(%rsp)
	movb	$0, 856(%rsp)
	movb	$0, 855(%rsp)
	movb	$0, 854(%rsp)
	movb	$0, 853(%rsp)
	movb	$0, 852(%rsp)
	movb	$0, 851(%rsp)
	movb	$0, 850(%rsp)
	movb	$0, 849(%rsp)
	movb	$0, 848(%rsp)
	movb	$0, 847(%rsp)
	movb	$0, 846(%rsp)
	movb	$0, 845(%rsp)
	movb	$0, 844(%rsp)
	movb	$0, 843(%rsp)
	movb	$0, 842(%rsp)
	movb	$0, 841(%rsp)
	movb	$0, 840(%rsp)
	movb	$0, 839(%rsp)
	movb	$0, 838(%rsp)
	movb	$0, 837(%rsp)
	movb	$0, 836(%rsp)
	movb	$0, 835(%rsp)
	movb	$0, 834(%rsp)
	movb	$0, 833(%rsp)
	movb	$0, 832(%rsp)
	movb	$0, 831(%rsp)
	movb	$0, 830(%rsp)
	movb	$0, 829(%rsp)
	movb	$0, 828(%rsp)
	movb	$0, 827(%rsp)
	movb	$0, 826(%rsp)
	movb	$0, 825(%rsp)
	movb	$0, 824(%rsp)
	movb	$0, 823(%rsp)
	movb	$0, 822(%rsp)
	movb	$0, 821(%rsp)
	movb	$0, 820(%rsp)
	movb	$0, 819(%rsp)
	movb	$0, 818(%rsp)
	movb	$0, 817(%rsp)
	movb	$0, 816(%rsp)
	movb	$0, 815(%rsp)
	movb	$0, 814(%rsp)
	movb	$0, 813(%rsp)
	movb	$0, 812(%rsp)
	movb	$0, 811(%rsp)
	movb	$0, 810(%rsp)
	movb	$0, 809(%rsp)
	movb	$0, 808(%rsp)
	movb	$0, 807(%rsp)
	movb	$0, 806(%rsp)
	movb	$0, 805(%rsp)
	movb	$0, 804(%rsp)
	movb	$0, 803(%rsp)
	movb	$0, 802(%rsp)
	movb	$0, 801(%rsp)
	movb	$0, 800(%rsp)
	movb	$0, 799(%rsp)
	movb	$0, 798(%rsp)
	movb	$0, 797(%rsp)
	movb	$0, 796(%rsp)
	movb	$0, 795(%rsp)
	movb	$0, 794(%rsp)
	movb	$0, 793(%rsp)
	movb	$0, 792(%rsp)
	movb	$0, 791(%rsp)
	movb	$0, 790(%rsp)
	movb	$0, 789(%rsp)
	movb	$0, 788(%rsp)
	movb	$0, 787(%rsp)
	movb	$0, 786(%rsp)
	movb	$0, 785(%rsp)
	movb	$0, 784(%rsp)
	movb	$0, 783(%rsp)
	movb	$0, 782(%rsp)
	movb	$0, 781(%rsp)
	movb	$0, 780(%rsp)
	movb	$0, 779(%rsp)
	movb	$0, 778(%rsp)
	movb	$0, 777(%rsp)
	movb	$0, 776(%rsp)
	movb	$0, 775(%rsp)
	movb	$0, 774(%rsp)
	movb	$0, 773(%rsp)
	movb	$0, 772(%rsp)
	movb	$0, 771(%rsp)
	movb	$0, 770(%rsp)
	movb	$0, 769(%rsp)
	movb	$0, 768(%rsp)
	movb	$0, 767(%rsp)
	movb	$0, 766(%rsp)
	movb	$0, 765(%rsp)
	movb	$0, 764(%rsp)
	movb	$0, 763(%rsp)
	movb	$0, 762(%rsp)
	movb	$0, 761(%rsp)
	movb	$0, 760(%rsp)
	movb	$0, 759(%rsp)
	movb	$0, 758(%rsp)
	movb	$0, 757(%rsp)
	movb	$0, 756(%rsp)
	movb	$0, 755(%rsp)
	movb	$0, 754(%rsp)
	movb	$0, 753(%rsp)
	movb	$0, 752(%rsp)
	movb	$0, 751(%rsp)
	movb	$0, 750(%rsp)
	movb	$0, 749(%rsp)
	movb	$0, 748(%rsp)
	movb	$0, 747(%rsp)
	movb	$0, 746(%rsp)
	movb	$0, 745(%rsp)
	movb	$0, 744(%rsp)
	movb	$0, 743(%rsp)
	movb	$0, 742(%rsp)
	movb	$0, 741(%rsp)
	movb	$0, 740(%rsp)
	movb	$0, 739(%rsp)
	movb	$0, 738(%rsp)
	movb	$0, 737(%rsp)
	movb	$0, 736(%rsp)
	movb	$0, 735(%rsp)
	movb	$0, 734(%rsp)
	movb	$0, 733(%rsp)
	movb	$0, 732(%rsp)
	movb	$0, 731(%rsp)
	movb	$0, 730(%rsp)
	movb	$0, 729(%rsp)
	movb	$0, 728(%rsp)
	movb	$0, 727(%rsp)
	movb	$0, 726(%rsp)
	movb	$0, 725(%rsp)
	movb	$0, 724(%rsp)
	movb	$0, 723(%rsp)
	movb	$0, 722(%rsp)
	movb	$0, 721(%rsp)
	movb	$0, 720(%rsp)
	movb	$0, 719(%rsp)
	movb	$0, 718(%rsp)
	movb	$0, 717(%rsp)
	movb	$0, 716(%rsp)
	movb	$0, 715(%rsp)
	movb	$0, 714(%rsp)
	movb	$0, 713(%rsp)
	movb	$0, 712(%rsp)
	movb	$0, 711(%rsp)
	movb	$0, 710(%rsp)
	movb	$0, 709(%rsp)
	movb	$0, 708(%rsp)
	movb	$0, 707(%rsp)
	movb	$0, 706(%rsp)
	movb	$0, 705(%rsp)
	movb	$0, 704(%rsp)
	movb	$0, 703(%rsp)
	movb	$0, 702(%rsp)
	movb	$0, 701(%rsp)
	movb	$0, 700(%rsp)
	movb	$0, 699(%rsp)
	movb	$0, 698(%rsp)
	movb	$0, 697(%rsp)
	movb	$0, 696(%rsp)
	movb	$0, 695(%rsp)
	movb	$0, 694(%rsp)
	movb	$0, 693(%rsp)
	movb	$0, 692(%rsp)
	movb	$0, 691(%rsp)
	movb	$0, 690(%rsp)
	movb	$0, 689(%rsp)
	movb	$0, 688(%rsp)
	movb	$0, 687(%rsp)
	movb	$0, 686(%rsp)
	movb	$0, 685(%rsp)
	movb	$0, 684(%rsp)
	movb	$0, 683(%rsp)
	movb	$0, 682(%rsp)
	movb	$0, 681(%rsp)
	movb	$0, 680(%rsp)
	movb	$0, 679(%rsp)
	movb	$0, 678(%rsp)
	movb	$0, 677(%rsp)
	movb	$0, 676(%rsp)
	movb	$0, 675(%rsp)
	movb	$0, 674(%rsp)
	movb	$0, 673(%rsp)
	movb	$0, 672(%rsp)
	movb	$0, 671(%rsp)
	movb	$0, 670(%rsp)
	movb	$0, 669(%rsp)
	movb	$0, 668(%rsp)
	movb	$0, 667(%rsp)
	movb	$0, 666(%rsp)
	movb	$0, 665(%rsp)
	movb	$0, 664(%rsp)
	movb	$0, 663(%rsp)
	movb	$0, 662(%rsp)
	movb	$0, 661(%rsp)
	movb	$0, 660(%rsp)
	movb	$0, 659(%rsp)
	movb	$0, 658(%rsp)
	movb	$0, 657(%rsp)
	movb	$0, 656(%rsp)
	movb	$0, 655(%rsp)
	movb	$0, 654(%rsp)
	movb	$0, 653(%rsp)
	movb	$0, 652(%rsp)
	movb	$0, 651(%rsp)
	movb	$0, 650(%rsp)
	movb	$0, 649(%rsp)
	movb	$0, 648(%rsp)
	movb	$0, 647(%rsp)
	movb	$0, 646(%rsp)
	movb	$0, 645(%rsp)
	movb	$0, 644(%rsp)
	movb	$0, 643(%rsp)
	movb	$0, 642(%rsp)
	movb	$0, 641(%rsp)
	movb	$0, 640(%rsp)
	movb	$0, 639(%rsp)
	movb	$0, 638(%rsp)
	movb	$0, 637(%rsp)
	movb	$0, 636(%rsp)
	movb	$0, 635(%rsp)
	movb	$0, 634(%rsp)
	movb	$0, 633(%rsp)
	movb	$0, 632(%rsp)
	movb	$0, 631(%rsp)
	movb	$0, 630(%rsp)
	movb	$0, 629(%rsp)
	movb	$0, 628(%rsp)
	movb	$0, 627(%rsp)
	movb	$0, 626(%rsp)
	movb	$0, 625(%rsp)
	movb	$0, 624(%rsp)
	movb	$0, 623(%rsp)
	movb	$0, 622(%rsp)
	movb	$0, 621(%rsp)
	movb	$0, 620(%rsp)
	movb	$0, 619(%rsp)
	movb	$0, 618(%rsp)
	movb	$0, 617(%rsp)
	movb	$0, 616(%rsp)
	movb	$0, 615(%rsp)
	movb	$0, 614(%rsp)
	movb	$0, 613(%rsp)
	movb	$0, 612(%rsp)
	movb	$0, 611(%rsp)
	movb	$0, 610(%rsp)
	movb	$0, 609(%rsp)
	movb	$0, 608(%rsp)
	movb	$0, 607(%rsp)
	movb	$0, 606(%rsp)
	movb	$0, 605(%rsp)
	movb	$0, 604(%rsp)
	movb	$0, 603(%rsp)
	movb	$0, 602(%rsp)
	movb	$0, 601(%rsp)
	movb	$0, 600(%rsp)
	movb	$0, 599(%rsp)
	movb	$0, 598(%rsp)
	movb	$0, 597(%rsp)
	movb	$0, 596(%rsp)
	movb	$0, 595(%rsp)
	movb	$0, 594(%rsp)
	movb	$0, 593(%rsp)
	movb	$0, 592(%rsp)
	movb	$0, 591(%rsp)
	movb	$0, 590(%rsp)
	movb	$0, 589(%rsp)
	movb	$0, 588(%rsp)
	movb	$0, 587(%rsp)
	movb	$0, 586(%rsp)
	movb	$0, 585(%rsp)
	movb	$0, 584(%rsp)
	movb	$0, 583(%rsp)
	movb	$0, 582(%rsp)
	movb	$0, 581(%rsp)
	movb	$0, 580(%rsp)
	movb	$0, 579(%rsp)
	movb	$0, 578(%rsp)
	movb	$0, 577(%rsp)
	movb	$0, 576(%rsp)
	movb	$0, 575(%rsp)
	movb	$0, 574(%rsp)
	movb	$0, 573(%rsp)
	movb	$0, 572(%rsp)
	movb	$0, 571(%rsp)
	movb	$0, 570(%rsp)
	movb	$0, 569(%rsp)
	movb	$0, 568(%rsp)
	movb	$0, 567(%rsp)
	movb	$0, 566(%rsp)
	movb	$0, 565(%rsp)
	movb	$0, 564(%rsp)
	movb	$0, 563(%rsp)
	movb	$0, 562(%rsp)
	movb	$0, 561(%rsp)
	movb	$0, 560(%rsp)
	movb	$0, 559(%rsp)
	movb	$0, 558(%rsp)
	movb	$0, 557(%rsp)
	movb	$0, 556(%rsp)
	movb	$0, 555(%rsp)
	movb	$0, 554(%rsp)
	movb	$0, 553(%rsp)
	movb	$0, 552(%rsp)
	movb	$0, 551(%rsp)
	movb	$0, 550(%rsp)
	movb	$0, 549(%rsp)
	movb	$0, 548(%rsp)
	movb	$0, 547(%rsp)
	movb	$0, 546(%rsp)
	movb	$0, 545(%rsp)
	movb	$0, 544(%rsp)
	movb	$0, 543(%rsp)
	movb	$0, 542(%rsp)
	movb	$0, 541(%rsp)
	movb	$0, 540(%rsp)
	movb	$0, 539(%rsp)
	movb	$0, 538(%rsp)
	movb	$0, 537(%rsp)
	movb	$0, 536(%rsp)
	movb	$0, 535(%rsp)
	movb	$0, 534(%rsp)
	movb	$0, 533(%rsp)
	movb	$0, 532(%rsp)
	movb	$0, 531(%rsp)
	movb	$0, 530(%rsp)
	movb	$0, 529(%rsp)
	movb	$0, 528(%rsp)
	movb	$0, 527(%rsp)
	movb	$0, 526(%rsp)
	movb	$0, 525(%rsp)
	movb	$0, 524(%rsp)
	movb	$0, 523(%rsp)
	movb	$0, 522(%rsp)
	movb	$0, 521(%rsp)
	movb	$0, 520(%rsp)
	movb	$0, 519(%rsp)
	movb	$0, 518(%rsp)
	movb	$0, 517(%rsp)
	movb	$0, 516(%rsp)
	movb	$0, 515(%rsp)
	movb	$0, 514(%rsp)
	movb	$0, 513(%rsp)
	movb	$0, 512(%rsp)
	movb	$0, 511(%rsp)
	movb	$0, 510(%rsp)
	movb	$0, 509(%rsp)
	movb	$0, 508(%rsp)
	movb	$0, 507(%rsp)
	movb	$0, 506(%rsp)
	movb	$0, 505(%rsp)
	movb	$0, 504(%rsp)
	movb	$0, 503(%rsp)
	movb	$0, 502(%rsp)
	movb	$0, 501(%rsp)
	movb	$0, 500(%rsp)
	movb	$0, 499(%rsp)
	movb	$0, 498(%rsp)
	movb	$0, 497(%rsp)
	movb	$0, 496(%rsp)
	movb	$0, 495(%rsp)
	movb	$0, 494(%rsp)
	movb	$0, 493(%rsp)
	movb	$0, 492(%rsp)
	movb	$0, 491(%rsp)
	movb	$0, 490(%rsp)
	movb	$0, 489(%rsp)
	movb	$0, 488(%rsp)
	movb	$0, 487(%rsp)
	movb	$0, 486(%rsp)
	movb	$0, 485(%rsp)
	movb	$0, 484(%rsp)
	movb	$0, 483(%rsp)
	movb	$0, 482(%rsp)
	movb	$0, 481(%rsp)
	movb	$0, 480(%rsp)
	movb	$0, 479(%rsp)
	movb	$0, 478(%rsp)
	movb	$0, 477(%rsp)
	movb	$0, 476(%rsp)
	movb	$0, 475(%rsp)
	movb	$0, 474(%rsp)
	movb	$0, 473(%rsp)
	movb	$0, 472(%rsp)
	movb	$0, 471(%rsp)
	movb	$0, 470(%rsp)
	movb	$0, 469(%rsp)
	movb	$0, 468(%rsp)
	movb	$0, 467(%rsp)
	movb	$0, 466(%rsp)
	movb	$0, 465(%rsp)
	movb	$0, 464(%rsp)
	movb	$0, 463(%rsp)
	movb	$0, 462(%rsp)
	movb	$0, 461(%rsp)
	movb	$0, 460(%rsp)
	movb	$0, 459(%rsp)
	movb	$0, 458(%rsp)
	movb	$0, 457(%rsp)
	movb	$0, 456(%rsp)
	movb	$0, 455(%rsp)
	movb	$0, 454(%rsp)
	movb	$0, 453(%rsp)
	movb	$0, 452(%rsp)
	movb	$0, 451(%rsp)
	movb	$0, 450(%rsp)
	movb	$0, 449(%rsp)
	movb	$0, 448(%rsp)
	movb	$0, 447(%rsp)
	movb	$0, 446(%rsp)
	movb	$0, 445(%rsp)
	movb	$0, 444(%rsp)
	movb	$0, 443(%rsp)
	movb	$0, 442(%rsp)
	movb	$0, 441(%rsp)
	movb	$0, 440(%rsp)
	movb	$0, 439(%rsp)
	movb	$0, 438(%rsp)
	movb	$0, 437(%rsp)
	movb	$0, 436(%rsp)
	movb	$0, 435(%rsp)
	movb	$0, 434(%rsp)
	movb	$0, 433(%rsp)
	movb	$0, 432(%rsp)
	movb	$0, 431(%rsp)
	movb	$0, 430(%rsp)
	movb	$0, 429(%rsp)
	movb	$0, 428(%rsp)
	movb	$0, 427(%rsp)
	movb	$0, 426(%rsp)
	movb	$0, 425(%rsp)
	movb	$0, 424(%rsp)
	movb	$0, 423(%rsp)
	movb	$0, 422(%rsp)
	movb	$0, 421(%rsp)
	movb	$0, 420(%rsp)
	movb	$0, 419(%rsp)
	movb	$0, 418(%rsp)
	movb	$0, 417(%rsp)
	movb	$0, 416(%rsp)
	movb	$0, 415(%rsp)
	movb	$0, 414(%rsp)
	movb	$0, 413(%rsp)
	movb	$0, 412(%rsp)
	movb	$0, 411(%rsp)
	movb	$0, 410(%rsp)
	movb	$0, 409(%rsp)
	movb	$0, 408(%rsp)
	movb	$0, 407(%rsp)
	movb	$0, 406(%rsp)
	movb	$0, 405(%rsp)
	movb	$0, 404(%rsp)
	movb	$0, 403(%rsp)
	movb	$0, 402(%rsp)
	movb	$0, 401(%rsp)
	movb	$0, 400(%rsp)
	movb	$0, 399(%rsp)
	movb	$0, 398(%rsp)
	movb	$0, 397(%rsp)
	movb	$0, 396(%rsp)
	movb	$0, 395(%rsp)
	movb	$0, 394(%rsp)
	movb	$0, 393(%rsp)
	movb	$0, 392(%rsp)
	movb	$0, 391(%rsp)
	movb	$0, 390(%rsp)
	movb	$0, 389(%rsp)
	movb	$0, 388(%rsp)
	movb	$0, 387(%rsp)
	movb	$0, 386(%rsp)
	movb	$0, 385(%rsp)
	movb	$0, 384(%rsp)
	movb	$0, 383(%rsp)
	movb	$0, 382(%rsp)
	movb	$0, 381(%rsp)
	movb	$0, 380(%rsp)
	movb	$0, 379(%rsp)
	movb	$0, 378(%rsp)
	movb	$0, 377(%rsp)
	movb	$0, 376(%rsp)
	movb	$0, 375(%rsp)
	movb	$0, 374(%rsp)
	movb	$0, 373(%rsp)
	movb	$0, 372(%rsp)
	movb	$0, 371(%rsp)
	movb	$0, 370(%rsp)
	movb	$0, 369(%rsp)
	movb	$0, 368(%rsp)
	movb	$0, 367(%rsp)
	movb	$0, 366(%rsp)
	movb	$0, 365(%rsp)
	movb	$0, 364(%rsp)
	movb	$0, 363(%rsp)
	movb	$0, 362(%rsp)
	movb	$0, 361(%rsp)
	movb	$0, 360(%rsp)
	movb	$0, 359(%rsp)
	movb	$0, 358(%rsp)
	movb	$0, 357(%rsp)
	movb	$0, 356(%rsp)
	movb	$0, 355(%rsp)
	movb	$0, 354(%rsp)
	movb	$0, 353(%rsp)
	movb	$0, 352(%rsp)
	movb	$0, 351(%rsp)
	movb	$0, 350(%rsp)
	movb	$0, 349(%rsp)
	movb	$0, 348(%rsp)
	movb	$0, 347(%rsp)
	movb	$0, 346(%rsp)
	movb	$0, 345(%rsp)
	movb	$0, 344(%rsp)
	movb	$0, 343(%rsp)
	movb	$0, 342(%rsp)
	movb	$0, 341(%rsp)
	movb	$0, 340(%rsp)
	movb	$0, 339(%rsp)
	movb	$0, 338(%rsp)
	movb	$0, 337(%rsp)
	movb	$0, 336(%rsp)
	movb	$0, 335(%rsp)
	movb	$0, 334(%rsp)
	movb	$0, 333(%rsp)
	movb	$0, 332(%rsp)
	movb	$0, 331(%rsp)
	movb	$0, 330(%rsp)
	movb	$0, 329(%rsp)
	movb	$0, 328(%rsp)
	movb	$0, 327(%rsp)
	movb	$0, 326(%rsp)
	movb	$0, 325(%rsp)
	movb	$0, 324(%rsp)
	movb	$0, 323(%rsp)
	movb	$0, 322(%rsp)
	movb	$0, 321(%rsp)
	movb	$0, 320(%rsp)
	movb	$0, 319(%rsp)
	movb	$0, 318(%rsp)
	movb	$0, 317(%rsp)
	movb	$0, 316(%rsp)
	movb	$0, 315(%rsp)
	movb	$0, 314(%rsp)
	movb	$0, 313(%rsp)
	movb	$0, 312(%rsp)
	movb	$0, 311(%rsp)
	movb	$0, 310(%rsp)
	movb	$0, 309(%rsp)
	movb	$0, 308(%rsp)
	movb	$0, 307(%rsp)
	movb	$0, 306(%rsp)
	movb	$0, 305(%rsp)
	movb	$0, 304(%rsp)
	movb	$0, 303(%rsp)
	movb	$0, 302(%rsp)
	movb	$0, 301(%rsp)
	movb	$0, 300(%rsp)
	movb	$0, 299(%rsp)
	movb	$0, 298(%rsp)
	movb	$0, 297(%rsp)
	movb	$0, 296(%rsp)
	movb	$0, 295(%rsp)
	movb	$0, 294(%rsp)
	movb	$0, 293(%rsp)
	movb	$0, 292(%rsp)
	movb	$0, 291(%rsp)
	movb	$0, 290(%rsp)
	movb	$0, 289(%rsp)
	movb	$0, 288(%rsp)
	movb	$0, 287(%rsp)
	movb	$0, 286(%rsp)
	movb	$0, 285(%rsp)
	movb	$0, 284(%rsp)
	movb	$0, 283(%rsp)
	movb	$0, 282(%rsp)
	movb	$0, 281(%rsp)
	movb	$0, 280(%rsp)
	movb	$0, 279(%rsp)
	movb	$0, 278(%rsp)
	movb	$0, 277(%rsp)
	movb	$0, 276(%rsp)
	movb	$0, 275(%rsp)
	movb	$0, 274(%rsp)
	movb	$0, 273(%rsp)
	movb	$0, 272(%rsp)
	movb	$0, 271(%rsp)
	movb	$0, 270(%rsp)
	movb	$0, 269(%rsp)
	movb	$0, 268(%rsp)
	movb	$0, 267(%rsp)
	movb	$0, 266(%rsp)
	movb	$0, 265(%rsp)
	movb	$0, 264(%rsp)
	movb	$0, 263(%rsp)
	movb	$0, 262(%rsp)
	movb	$0, 261(%rsp)
	movb	$0, 260(%rsp)
	movb	$0, 259(%rsp)
	movb	$0, 258(%rsp)
	movb	$0, 257(%rsp)
	movb	$0, 256(%rsp)
	movb	$0, 255(%rsp)
	movb	$0, 254(%rsp)
	movb	$0, 253(%rsp)
	movb	$0, 252(%rsp)
	movb	$0, 251(%rsp)
	movb	$0, 250(%rsp)
	movb	$0, 249(%rsp)
	movb	$0, 248(%rsp)
	movb	$0, 247(%rsp)
	movb	$0, 246(%rsp)
	movb	$0, 245(%rsp)
	movb	$0, 244(%rsp)
	movb	$0, 243(%rsp)
	movb	$0, 242(%rsp)
	movb	$0, 241(%rsp)
	movb	$0, 240(%rsp)
	movb	$0, 239(%rsp)
	movb	$0, 238(%rsp)
	movb	$0, 237(%rsp)
	movb	$0, 236(%rsp)
	movb	$0, 235(%rsp)
	movb	$0, 234(%rsp)
	movb	$0, 233(%rsp)
	movb	$0, 232(%rsp)
	movb	$0, 231(%rsp)
	movb	$0, 230(%rsp)
	movb	$0, 229(%rsp)
	movb	$0, 228(%rsp)
	movb	$0, 227(%rsp)
	movb	$0, 226(%rsp)
	movb	$0, 225(%rsp)
	movb	$0, 224(%rsp)
	movb	$0, 223(%rsp)
	movb	$0, 222(%rsp)
	movb	$0, 221(%rsp)
	movb	$0, 220(%rsp)
	movb	$0, 219(%rsp)
	movb	$0, 218(%rsp)
	movb	$0, 217(%rsp)
	movb	$0, 216(%rsp)
	movb	$0, 215(%rsp)
	movb	$0, 214(%rsp)
	movb	$0, 213(%rsp)
	movb	$0, 212(%rsp)
	movb	$0, 211(%rsp)
	movb	$0, 210(%rsp)
	movb	$0, 209(%rsp)
	movb	$0, 208(%rsp)
	movb	$0, 207(%rsp)
	movb	$0, 206(%rsp)
	movb	$0, 205(%rsp)
	movb	$0, 204(%rsp)
	movb	$0, 203(%rsp)
	movb	$0, 202(%rsp)
	movb	$0, 201(%rsp)
	movb	$0, 200(%rsp)
	movb	$0, 199(%rsp)
	movb	$0, 198(%rsp)
	movb	$0, 197(%rsp)
	movb	$0, 196(%rsp)
	movb	$0, 195(%rsp)
	movb	$0, 194(%rsp)
	movb	$0, 193(%rsp)
	movb	$0, 192(%rsp)
	movb	$0, 191(%rsp)
	movb	$0, 190(%rsp)
	movb	$0, 189(%rsp)
	movb	$0, 188(%rsp)
	movb	$0, 187(%rsp)
	movb	$0, 186(%rsp)
	movb	$0, 185(%rsp)
	movb	$0, 184(%rsp)
	movb	$0, 183(%rsp)
	movb	$0, 182(%rsp)
	movb	$0, 181(%rsp)
	movb	$0, 180(%rsp)
	movb	$0, 179(%rsp)
	movb	$0, 178(%rsp)
	movb	$0, 177(%rsp)
	movb	$0, 176(%rsp)
	movb	$0, 175(%rsp)
	movb	$0, 174(%rsp)
	movb	$0, 173(%rsp)
	movb	$0, 172(%rsp)
	movb	$0, 171(%rsp)
	movb	$0, 170(%rsp)
	movb	$0, 169(%rsp)
	movb	$0, 168(%rsp)
	movb	$0, 167(%rsp)
	movb	$0, 166(%rsp)
	movb	$0, 165(%rsp)
	movb	$0, 164(%rsp)
	movb	$0, 163(%rsp)
	movb	$0, 162(%rsp)
	movb	$0, 161(%rsp)
	movb	$0, 160(%rsp)
	movb	$0, 159(%rsp)
	movb	$0, 158(%rsp)
	movb	$0, 157(%rsp)
	movb	$0, 156(%rsp)
	movb	$0, 155(%rsp)
	movb	$0, 154(%rsp)
	movb	$0, 153(%rsp)
	movb	$0, 152(%rsp)
	movb	$0, 151(%rsp)
	movb	$0, 150(%rsp)
	movb	$0, 149(%rsp)
	movb	$0, 148(%rsp)
	movb	$0, 147(%rsp)
	movb	$0, 146(%rsp)
	movb	$0, 145(%rsp)
	movb	$0, 144(%rsp)
	movb	$0, 143(%rsp)
	movb	$0, 142(%rsp)
	movb	$0, 141(%rsp)
	movb	$0, 140(%rsp)
	movb	$0, 139(%rsp)
	movb	$0, 138(%rsp)
	movb	$0, 137(%rsp)
	movb	$0, 136(%rsp)
	movb	$0, 135(%rsp)
	movb	$0, 134(%rsp)
	movb	$0, 133(%rsp)
	movb	$0, 132(%rsp)
	movb	$0, 131(%rsp)
	movb	$0, 130(%rsp)
	movb	$0, 129(%rsp)
	movb	$0, 128(%rsp)
	movb	$0, 127(%rsp)
	movb	$0, 126(%rsp)
	movb	$0, 125(%rsp)
	movb	$0, 124(%rsp)
	movb	$0, 123(%rsp)
	movb	$0, 122(%rsp)
	movb	$0, 121(%rsp)
	movb	$0, 120(%rsp)
	movb	$0, 119(%rsp)
	movb	$0, 118(%rsp)
	movb	$0, 117(%rsp)
	movb	$0, 116(%rsp)
	movb	$0, 115(%rsp)
	movb	$0, 114(%rsp)
	movb	$0, 113(%rsp)
	movb	$0, 112(%rsp)
	movb	$0, 111(%rsp)
	movb	$0, 110(%rsp)
	movb	$0, 109(%rsp)
	movb	$0, 108(%rsp)
	movb	$0, 107(%rsp)
	movb	$0, 106(%rsp)
	movb	$0, 105(%rsp)
	movb	$0, 104(%rsp)
	movb	$0, 103(%rsp)
	movb	$0, 102(%rsp)
	movb	$0, 101(%rsp)
	movb	$0, 100(%rsp)
	movb	$0, 99(%rsp)
	movb	$0, 98(%rsp)
	movb	$0, 97(%rsp)
	movb	$0, 96(%rsp)
	movb	$0, 95(%rsp)
	movb	$0, 94(%rsp)
	movb	$0, 93(%rsp)
	movb	$0, 92(%rsp)
	movb	$0, 91(%rsp)
	movb	$0, 90(%rsp)
	movb	$0, 89(%rsp)
	movb	$0, 88(%rsp)
	movb	$0, 87(%rsp)
	movb	$0, 86(%rsp)
	movb	$0, 85(%rsp)
	movb	$0, 84(%rsp)
	movb	$0, 83(%rsp)
	movb	$0, 82(%rsp)
	movb	$0, 81(%rsp)
	movb	$0, 80(%rsp)
	movb	$0, 79(%rsp)
	movb	$0, 78(%rsp)
	movb	$0, 77(%rsp)
	movb	$0, 76(%rsp)
	movb	$0, 75(%rsp)
	movb	$0, 74(%rsp)
	movb	$0, 73(%rsp)
	movb	$0, 72(%rsp)
	movb	$0, 71(%rsp)
	movb	$0, 70(%rsp)
	movb	$0, 69(%rsp)
	movb	$0, 68(%rsp)
	movb	$0, 67(%rsp)
	movb	$0, 66(%rsp)
	movb	$0, 65(%rsp)
	movb	$0, 64(%rsp)
	movb	$0, 63(%rsp)
	movb	$0, 62(%rsp)
	movb	$0, 61(%rsp)
	movb	$0, 60(%rsp)
	movb	$0, 59(%rsp)
	movb	$0, 58(%rsp)
	movb	$0, 57(%rsp)
	movb	$0, 56(%rsp)
	movb	$0, 55(%rsp)
	movb	$0, 54(%rsp)
	movb	$0, 53(%rsp)
	movb	$0, 52(%rsp)
	movb	$0, 51(%rsp)
	movb	$0, 50(%rsp)
	movb	$0, 49(%rsp)
	movb	$0, 48(%rsp)
	movb	$0, 47(%rsp)
	movb	$0, 46(%rsp)
	movb	$0, 45(%rsp)
	movb	$0, 44(%rsp)
	movb	$0, 43(%rsp)
	movb	$0, 42(%rsp)
	movb	$0, 41(%rsp)
	movb	$0, 40(%rsp)
	movb	$0, 39(%rsp)
	movb	$0, 38(%rsp)
	movb	$0, 37(%rsp)
	movb	$0, 36(%rsp)
	movb	$0, 35(%rsp)
	movb	$0, 34(%rsp)
	movb	$0, 33(%rsp)
	movb	$0, 32(%rsp)
	movb	$0, 31(%rsp)
	movb	$0, 30(%rsp)
	movb	$0, 29(%rsp)
	movb	$0, 28(%rsp)
	movb	$0, 27(%rsp)
	movb	$0, 26(%rsp)
	movb	$0, 25(%rsp)
	movb	$0, 24(%rsp)
	movb	$0, 23(%rsp)
	movb	$0, 22(%rsp)
	movb	$0, 21(%rsp)
	movb	$0, 20(%rsp)
	movb	$0, 19(%rsp)
	movb	$0, 18(%rsp)
	movb	$0, 17(%rsp)
	movb	$0, 16(%rsp)
	movb	$0, 15(%rsp)
	movb	$0, 14(%rsp)
	movb	$0, 13(%rsp)
	movb	$0, 12(%rsp)
	movb	$0, 11(%rsp)
	movb	$0, 10(%rsp)
	movb	$0, 9(%rsp)
	movb	$0, 8(%rsp)
	movb	$0, 7(%rsp)
	movb	$0, 6(%rsp)
	movb	$0, 5(%rsp)
	movb	$0, 4(%rsp)
	movb	$0, 3(%rsp)
	movb	$0, 2(%rsp)
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
_wots_pkgen_jazz:
wots_pkgen_jazz:
	movq	%rsp, %rax
	leaq	-72(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 16(%rsp)
	movq	%rbp, 24(%rsp)
	movq	%r12, 32(%rsp)
	movq	%r13, 40(%rsp)
	movq	%r14, 48(%rsp)
	movq	%r15, 56(%rsp)
	movq	%rax, 64(%rsp)
	movq	%rcx, (%rsp)
	movq	%rcx, %rax
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
Lwots_pkgen_jazz$68:
	leaq	88(%rsp), %rsp
	movq	%rcx, %rsi
	movq	%rax, 8(%rsp)
	movl	$0, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	movq	%r13, %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$67:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$1, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	32(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$66:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$2, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	64(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$65:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$3, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	96(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$64:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$4, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	128(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$63:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$5, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	160(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$62:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$6, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	192(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$61:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$7, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	224(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$60:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$8, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	256(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$59:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$9, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	288(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$58:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$10, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	320(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$57:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$11, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	352(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$56:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$12, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	384(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$55:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$13, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	416(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$54:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$14, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	448(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$53:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$15, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	480(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$52:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$16, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	512(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$51:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$17, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	544(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$50:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$18, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	576(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$49:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$19, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	608(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$48:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$20, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	640(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$47:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$21, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	672(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$46:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$22, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	704(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$45:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$23, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	736(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$44:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$24, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	768(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$43:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$25, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	800(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$42:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$26, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	832(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$41:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$27, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	864(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$40:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$28, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	896(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$39:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$29, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	928(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$38:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$30, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	960(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$37:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$31, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	992(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$36:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$32, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1024(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$35:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$33, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1056(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$34:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$34, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1088(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$33:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$35, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1120(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$32:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$36, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1152(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$31:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$37, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1184(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$30:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$38, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1216(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$29:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$39, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1248(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$28:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$40, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1280(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$27:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$41, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1312(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$26:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$42, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1344(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$25:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$43, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1376(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$24:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$44, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1408(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$23:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$45, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1440(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$22:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$46, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1472(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$21:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$47, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1504(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$20:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$48, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1536(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$19:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$49, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1568(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$18:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$50, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1600(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$17:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$51, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1632(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$16:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$52, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1664(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$15:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$53, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1696(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$14:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$54, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1728(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$13:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$55, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1760(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$12:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$56, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1792(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$11:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$57, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1824(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$10:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$58, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1856(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$9:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$59, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1888(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$8:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$60, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1920(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$7:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$61, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1952(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$6:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$62, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	1984(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$5:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$63, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	2016(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$4:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$64, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	2048(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$3:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$65, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	2080(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$2:
	leaq	32(%rsp), %rsp
	movq	%rax, %rsi
	movq	%r13, 8(%rsp)
	movl	$66, %eax
	movl	%eax, 20(%rsi)
	movq	8(%rsp), %r13
	movq	(%rsp), %r8
	leaq	2112(%r13), %rdx
	movl	$0, %eax
	movl	$15, %ecx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lwots_pkgen_jazz$1:
	leaq	32(%rsp), %rsp
	movq	%r13, (%rsp)
	movq	16(%rsp), %rbx
	movq	24(%rsp), %rbp
	movq	32(%rsp), %r12
	movq	40(%rsp), %r13
	movq	48(%rsp), %r14
	movq	56(%rsp), %r15
	movq	64(%rsp), %rsp
	movq	%rsp, %rsi
	andq	$-8, %rsp
	subq	$1016, %rsp
	movb	$0, 1015(%rsp)
	movb	$0, 1014(%rsp)
	movb	$0, 1013(%rsp)
	movb	$0, 1012(%rsp)
	movb	$0, 1011(%rsp)
	movb	$0, 1010(%rsp)
	movb	$0, 1009(%rsp)
	movb	$0, 1008(%rsp)
	movb	$0, 1007(%rsp)
	movb	$0, 1006(%rsp)
	movb	$0, 1005(%rsp)
	movb	$0, 1004(%rsp)
	movb	$0, 1003(%rsp)
	movb	$0, 1002(%rsp)
	movb	$0, 1001(%rsp)
	movb	$0, 1000(%rsp)
	movb	$0, 999(%rsp)
	movb	$0, 998(%rsp)
	movb	$0, 997(%rsp)
	movb	$0, 996(%rsp)
	movb	$0, 995(%rsp)
	movb	$0, 994(%rsp)
	movb	$0, 993(%rsp)
	movb	$0, 992(%rsp)
	movb	$0, 991(%rsp)
	movb	$0, 990(%rsp)
	movb	$0, 989(%rsp)
	movb	$0, 988(%rsp)
	movb	$0, 987(%rsp)
	movb	$0, 986(%rsp)
	movb	$0, 985(%rsp)
	movb	$0, 984(%rsp)
	movb	$0, 983(%rsp)
	movb	$0, 982(%rsp)
	movb	$0, 981(%rsp)
	movb	$0, 980(%rsp)
	movb	$0, 979(%rsp)
	movb	$0, 978(%rsp)
	movb	$0, 977(%rsp)
	movb	$0, 976(%rsp)
	movb	$0, 975(%rsp)
	movb	$0, 974(%rsp)
	movb	$0, 973(%rsp)
	movb	$0, 972(%rsp)
	movb	$0, 971(%rsp)
	movb	$0, 970(%rsp)
	movb	$0, 969(%rsp)
	movb	$0, 968(%rsp)
	movb	$0, 967(%rsp)
	movb	$0, 966(%rsp)
	movb	$0, 965(%rsp)
	movb	$0, 964(%rsp)
	movb	$0, 963(%rsp)
	movb	$0, 962(%rsp)
	movb	$0, 961(%rsp)
	movb	$0, 960(%rsp)
	movb	$0, 959(%rsp)
	movb	$0, 958(%rsp)
	movb	$0, 957(%rsp)
	movb	$0, 956(%rsp)
	movb	$0, 955(%rsp)
	movb	$0, 954(%rsp)
	movb	$0, 953(%rsp)
	movb	$0, 952(%rsp)
	movb	$0, 951(%rsp)
	movb	$0, 950(%rsp)
	movb	$0, 949(%rsp)
	movb	$0, 948(%rsp)
	movb	$0, 947(%rsp)
	movb	$0, 946(%rsp)
	movb	$0, 945(%rsp)
	movb	$0, 944(%rsp)
	movb	$0, 943(%rsp)
	movb	$0, 942(%rsp)
	movb	$0, 941(%rsp)
	movb	$0, 940(%rsp)
	movb	$0, 939(%rsp)
	movb	$0, 938(%rsp)
	movb	$0, 937(%rsp)
	movb	$0, 936(%rsp)
	movb	$0, 935(%rsp)
	movb	$0, 934(%rsp)
	movb	$0, 933(%rsp)
	movb	$0, 932(%rsp)
	movb	$0, 931(%rsp)
	movb	$0, 930(%rsp)
	movb	$0, 929(%rsp)
	movb	$0, 928(%rsp)
	movb	$0, 927(%rsp)
	movb	$0, 926(%rsp)
	movb	$0, 925(%rsp)
	movb	$0, 924(%rsp)
	movb	$0, 923(%rsp)
	movb	$0, 922(%rsp)
	movb	$0, 921(%rsp)
	movb	$0, 920(%rsp)
	movb	$0, 919(%rsp)
	movb	$0, 918(%rsp)
	movb	$0, 917(%rsp)
	movb	$0, 916(%rsp)
	movb	$0, 915(%rsp)
	movb	$0, 914(%rsp)
	movb	$0, 913(%rsp)
	movb	$0, 912(%rsp)
	movb	$0, 911(%rsp)
	movb	$0, 910(%rsp)
	movb	$0, 909(%rsp)
	movb	$0, 908(%rsp)
	movb	$0, 907(%rsp)
	movb	$0, 906(%rsp)
	movb	$0, 905(%rsp)
	movb	$0, 904(%rsp)
	movb	$0, 903(%rsp)
	movb	$0, 902(%rsp)
	movb	$0, 901(%rsp)
	movb	$0, 900(%rsp)
	movb	$0, 899(%rsp)
	movb	$0, 898(%rsp)
	movb	$0, 897(%rsp)
	movb	$0, 896(%rsp)
	movb	$0, 895(%rsp)
	movb	$0, 894(%rsp)
	movb	$0, 893(%rsp)
	movb	$0, 892(%rsp)
	movb	$0, 891(%rsp)
	movb	$0, 890(%rsp)
	movb	$0, 889(%rsp)
	movb	$0, 888(%rsp)
	movb	$0, 887(%rsp)
	movb	$0, 886(%rsp)
	movb	$0, 885(%rsp)
	movb	$0, 884(%rsp)
	movb	$0, 883(%rsp)
	movb	$0, 882(%rsp)
	movb	$0, 881(%rsp)
	movb	$0, 880(%rsp)
	movb	$0, 879(%rsp)
	movb	$0, 878(%rsp)
	movb	$0, 877(%rsp)
	movb	$0, 876(%rsp)
	movb	$0, 875(%rsp)
	movb	$0, 874(%rsp)
	movb	$0, 873(%rsp)
	movb	$0, 872(%rsp)
	movb	$0, 871(%rsp)
	movb	$0, 870(%rsp)
	movb	$0, 869(%rsp)
	movb	$0, 868(%rsp)
	movb	$0, 867(%rsp)
	movb	$0, 866(%rsp)
	movb	$0, 865(%rsp)
	movb	$0, 864(%rsp)
	movb	$0, 863(%rsp)
	movb	$0, 862(%rsp)
	movb	$0, 861(%rsp)
	movb	$0, 860(%rsp)
	movb	$0, 859(%rsp)
	movb	$0, 858(%rsp)
	movb	$0, 857(%rsp)
	movb	$0, 856(%rsp)
	movb	$0, 855(%rsp)
	movb	$0, 854(%rsp)
	movb	$0, 853(%rsp)
	movb	$0, 852(%rsp)
	movb	$0, 851(%rsp)
	movb	$0, 850(%rsp)
	movb	$0, 849(%rsp)
	movb	$0, 848(%rsp)
	movb	$0, 847(%rsp)
	movb	$0, 846(%rsp)
	movb	$0, 845(%rsp)
	movb	$0, 844(%rsp)
	movb	$0, 843(%rsp)
	movb	$0, 842(%rsp)
	movb	$0, 841(%rsp)
	movb	$0, 840(%rsp)
	movb	$0, 839(%rsp)
	movb	$0, 838(%rsp)
	movb	$0, 837(%rsp)
	movb	$0, 836(%rsp)
	movb	$0, 835(%rsp)
	movb	$0, 834(%rsp)
	movb	$0, 833(%rsp)
	movb	$0, 832(%rsp)
	movb	$0, 831(%rsp)
	movb	$0, 830(%rsp)
	movb	$0, 829(%rsp)
	movb	$0, 828(%rsp)
	movb	$0, 827(%rsp)
	movb	$0, 826(%rsp)
	movb	$0, 825(%rsp)
	movb	$0, 824(%rsp)
	movb	$0, 823(%rsp)
	movb	$0, 822(%rsp)
	movb	$0, 821(%rsp)
	movb	$0, 820(%rsp)
	movb	$0, 819(%rsp)
	movb	$0, 818(%rsp)
	movb	$0, 817(%rsp)
	movb	$0, 816(%rsp)
	movb	$0, 815(%rsp)
	movb	$0, 814(%rsp)
	movb	$0, 813(%rsp)
	movb	$0, 812(%rsp)
	movb	$0, 811(%rsp)
	movb	$0, 810(%rsp)
	movb	$0, 809(%rsp)
	movb	$0, 808(%rsp)
	movb	$0, 807(%rsp)
	movb	$0, 806(%rsp)
	movb	$0, 805(%rsp)
	movb	$0, 804(%rsp)
	movb	$0, 803(%rsp)
	movb	$0, 802(%rsp)
	movb	$0, 801(%rsp)
	movb	$0, 800(%rsp)
	movb	$0, 799(%rsp)
	movb	$0, 798(%rsp)
	movb	$0, 797(%rsp)
	movb	$0, 796(%rsp)
	movb	$0, 795(%rsp)
	movb	$0, 794(%rsp)
	movb	$0, 793(%rsp)
	movb	$0, 792(%rsp)
	movb	$0, 791(%rsp)
	movb	$0, 790(%rsp)
	movb	$0, 789(%rsp)
	movb	$0, 788(%rsp)
	movb	$0, 787(%rsp)
	movb	$0, 786(%rsp)
	movb	$0, 785(%rsp)
	movb	$0, 784(%rsp)
	movb	$0, 783(%rsp)
	movb	$0, 782(%rsp)
	movb	$0, 781(%rsp)
	movb	$0, 780(%rsp)
	movb	$0, 779(%rsp)
	movb	$0, 778(%rsp)
	movb	$0, 777(%rsp)
	movb	$0, 776(%rsp)
	movb	$0, 775(%rsp)
	movb	$0, 774(%rsp)
	movb	$0, 773(%rsp)
	movb	$0, 772(%rsp)
	movb	$0, 771(%rsp)
	movb	$0, 770(%rsp)
	movb	$0, 769(%rsp)
	movb	$0, 768(%rsp)
	movb	$0, 767(%rsp)
	movb	$0, 766(%rsp)
	movb	$0, 765(%rsp)
	movb	$0, 764(%rsp)
	movb	$0, 763(%rsp)
	movb	$0, 762(%rsp)
	movb	$0, 761(%rsp)
	movb	$0, 760(%rsp)
	movb	$0, 759(%rsp)
	movb	$0, 758(%rsp)
	movb	$0, 757(%rsp)
	movb	$0, 756(%rsp)
	movb	$0, 755(%rsp)
	movb	$0, 754(%rsp)
	movb	$0, 753(%rsp)
	movb	$0, 752(%rsp)
	movb	$0, 751(%rsp)
	movb	$0, 750(%rsp)
	movb	$0, 749(%rsp)
	movb	$0, 748(%rsp)
	movb	$0, 747(%rsp)
	movb	$0, 746(%rsp)
	movb	$0, 745(%rsp)
	movb	$0, 744(%rsp)
	movb	$0, 743(%rsp)
	movb	$0, 742(%rsp)
	movb	$0, 741(%rsp)
	movb	$0, 740(%rsp)
	movb	$0, 739(%rsp)
	movb	$0, 738(%rsp)
	movb	$0, 737(%rsp)
	movb	$0, 736(%rsp)
	movb	$0, 735(%rsp)
	movb	$0, 734(%rsp)
	movb	$0, 733(%rsp)
	movb	$0, 732(%rsp)
	movb	$0, 731(%rsp)
	movb	$0, 730(%rsp)
	movb	$0, 729(%rsp)
	movb	$0, 728(%rsp)
	movb	$0, 727(%rsp)
	movb	$0, 726(%rsp)
	movb	$0, 725(%rsp)
	movb	$0, 724(%rsp)
	movb	$0, 723(%rsp)
	movb	$0, 722(%rsp)
	movb	$0, 721(%rsp)
	movb	$0, 720(%rsp)
	movb	$0, 719(%rsp)
	movb	$0, 718(%rsp)
	movb	$0, 717(%rsp)
	movb	$0, 716(%rsp)
	movb	$0, 715(%rsp)
	movb	$0, 714(%rsp)
	movb	$0, 713(%rsp)
	movb	$0, 712(%rsp)
	movb	$0, 711(%rsp)
	movb	$0, 710(%rsp)
	movb	$0, 709(%rsp)
	movb	$0, 708(%rsp)
	movb	$0, 707(%rsp)
	movb	$0, 706(%rsp)
	movb	$0, 705(%rsp)
	movb	$0, 704(%rsp)
	movb	$0, 703(%rsp)
	movb	$0, 702(%rsp)
	movb	$0, 701(%rsp)
	movb	$0, 700(%rsp)
	movb	$0, 699(%rsp)
	movb	$0, 698(%rsp)
	movb	$0, 697(%rsp)
	movb	$0, 696(%rsp)
	movb	$0, 695(%rsp)
	movb	$0, 694(%rsp)
	movb	$0, 693(%rsp)
	movb	$0, 692(%rsp)
	movb	$0, 691(%rsp)
	movb	$0, 690(%rsp)
	movb	$0, 689(%rsp)
	movb	$0, 688(%rsp)
	movb	$0, 687(%rsp)
	movb	$0, 686(%rsp)
	movb	$0, 685(%rsp)
	movb	$0, 684(%rsp)
	movb	$0, 683(%rsp)
	movb	$0, 682(%rsp)
	movb	$0, 681(%rsp)
	movb	$0, 680(%rsp)
	movb	$0, 679(%rsp)
	movb	$0, 678(%rsp)
	movb	$0, 677(%rsp)
	movb	$0, 676(%rsp)
	movb	$0, 675(%rsp)
	movb	$0, 674(%rsp)
	movb	$0, 673(%rsp)
	movb	$0, 672(%rsp)
	movb	$0, 671(%rsp)
	movb	$0, 670(%rsp)
	movb	$0, 669(%rsp)
	movb	$0, 668(%rsp)
	movb	$0, 667(%rsp)
	movb	$0, 666(%rsp)
	movb	$0, 665(%rsp)
	movb	$0, 664(%rsp)
	movb	$0, 663(%rsp)
	movb	$0, 662(%rsp)
	movb	$0, 661(%rsp)
	movb	$0, 660(%rsp)
	movb	$0, 659(%rsp)
	movb	$0, 658(%rsp)
	movb	$0, 657(%rsp)
	movb	$0, 656(%rsp)
	movb	$0, 655(%rsp)
	movb	$0, 654(%rsp)
	movb	$0, 653(%rsp)
	movb	$0, 652(%rsp)
	movb	$0, 651(%rsp)
	movb	$0, 650(%rsp)
	movb	$0, 649(%rsp)
	movb	$0, 648(%rsp)
	movb	$0, 647(%rsp)
	movb	$0, 646(%rsp)
	movb	$0, 645(%rsp)
	movb	$0, 644(%rsp)
	movb	$0, 643(%rsp)
	movb	$0, 642(%rsp)
	movb	$0, 641(%rsp)
	movb	$0, 640(%rsp)
	movb	$0, 639(%rsp)
	movb	$0, 638(%rsp)
	movb	$0, 637(%rsp)
	movb	$0, 636(%rsp)
	movb	$0, 635(%rsp)
	movb	$0, 634(%rsp)
	movb	$0, 633(%rsp)
	movb	$0, 632(%rsp)
	movb	$0, 631(%rsp)
	movb	$0, 630(%rsp)
	movb	$0, 629(%rsp)
	movb	$0, 628(%rsp)
	movb	$0, 627(%rsp)
	movb	$0, 626(%rsp)
	movb	$0, 625(%rsp)
	movb	$0, 624(%rsp)
	movb	$0, 623(%rsp)
	movb	$0, 622(%rsp)
	movb	$0, 621(%rsp)
	movb	$0, 620(%rsp)
	movb	$0, 619(%rsp)
	movb	$0, 618(%rsp)
	movb	$0, 617(%rsp)
	movb	$0, 616(%rsp)
	movb	$0, 615(%rsp)
	movb	$0, 614(%rsp)
	movb	$0, 613(%rsp)
	movb	$0, 612(%rsp)
	movb	$0, 611(%rsp)
	movb	$0, 610(%rsp)
	movb	$0, 609(%rsp)
	movb	$0, 608(%rsp)
	movb	$0, 607(%rsp)
	movb	$0, 606(%rsp)
	movb	$0, 605(%rsp)
	movb	$0, 604(%rsp)
	movb	$0, 603(%rsp)
	movb	$0, 602(%rsp)
	movb	$0, 601(%rsp)
	movb	$0, 600(%rsp)
	movb	$0, 599(%rsp)
	movb	$0, 598(%rsp)
	movb	$0, 597(%rsp)
	movb	$0, 596(%rsp)
	movb	$0, 595(%rsp)
	movb	$0, 594(%rsp)
	movb	$0, 593(%rsp)
	movb	$0, 592(%rsp)
	movb	$0, 591(%rsp)
	movb	$0, 590(%rsp)
	movb	$0, 589(%rsp)
	movb	$0, 588(%rsp)
	movb	$0, 587(%rsp)
	movb	$0, 586(%rsp)
	movb	$0, 585(%rsp)
	movb	$0, 584(%rsp)
	movb	$0, 583(%rsp)
	movb	$0, 582(%rsp)
	movb	$0, 581(%rsp)
	movb	$0, 580(%rsp)
	movb	$0, 579(%rsp)
	movb	$0, 578(%rsp)
	movb	$0, 577(%rsp)
	movb	$0, 576(%rsp)
	movb	$0, 575(%rsp)
	movb	$0, 574(%rsp)
	movb	$0, 573(%rsp)
	movb	$0, 572(%rsp)
	movb	$0, 571(%rsp)
	movb	$0, 570(%rsp)
	movb	$0, 569(%rsp)
	movb	$0, 568(%rsp)
	movb	$0, 567(%rsp)
	movb	$0, 566(%rsp)
	movb	$0, 565(%rsp)
	movb	$0, 564(%rsp)
	movb	$0, 563(%rsp)
	movb	$0, 562(%rsp)
	movb	$0, 561(%rsp)
	movb	$0, 560(%rsp)
	movb	$0, 559(%rsp)
	movb	$0, 558(%rsp)
	movb	$0, 557(%rsp)
	movb	$0, 556(%rsp)
	movb	$0, 555(%rsp)
	movb	$0, 554(%rsp)
	movb	$0, 553(%rsp)
	movb	$0, 552(%rsp)
	movb	$0, 551(%rsp)
	movb	$0, 550(%rsp)
	movb	$0, 549(%rsp)
	movb	$0, 548(%rsp)
	movb	$0, 547(%rsp)
	movb	$0, 546(%rsp)
	movb	$0, 545(%rsp)
	movb	$0, 544(%rsp)
	movb	$0, 543(%rsp)
	movb	$0, 542(%rsp)
	movb	$0, 541(%rsp)
	movb	$0, 540(%rsp)
	movb	$0, 539(%rsp)
	movb	$0, 538(%rsp)
	movb	$0, 537(%rsp)
	movb	$0, 536(%rsp)
	movb	$0, 535(%rsp)
	movb	$0, 534(%rsp)
	movb	$0, 533(%rsp)
	movb	$0, 532(%rsp)
	movb	$0, 531(%rsp)
	movb	$0, 530(%rsp)
	movb	$0, 529(%rsp)
	movb	$0, 528(%rsp)
	movb	$0, 527(%rsp)
	movb	$0, 526(%rsp)
	movb	$0, 525(%rsp)
	movb	$0, 524(%rsp)
	movb	$0, 523(%rsp)
	movb	$0, 522(%rsp)
	movb	$0, 521(%rsp)
	movb	$0, 520(%rsp)
	movb	$0, 519(%rsp)
	movb	$0, 518(%rsp)
	movb	$0, 517(%rsp)
	movb	$0, 516(%rsp)
	movb	$0, 515(%rsp)
	movb	$0, 514(%rsp)
	movb	$0, 513(%rsp)
	movb	$0, 512(%rsp)
	movb	$0, 511(%rsp)
	movb	$0, 510(%rsp)
	movb	$0, 509(%rsp)
	movb	$0, 508(%rsp)
	movb	$0, 507(%rsp)
	movb	$0, 506(%rsp)
	movb	$0, 505(%rsp)
	movb	$0, 504(%rsp)
	movb	$0, 503(%rsp)
	movb	$0, 502(%rsp)
	movb	$0, 501(%rsp)
	movb	$0, 500(%rsp)
	movb	$0, 499(%rsp)
	movb	$0, 498(%rsp)
	movb	$0, 497(%rsp)
	movb	$0, 496(%rsp)
	movb	$0, 495(%rsp)
	movb	$0, 494(%rsp)
	movb	$0, 493(%rsp)
	movb	$0, 492(%rsp)
	movb	$0, 491(%rsp)
	movb	$0, 490(%rsp)
	movb	$0, 489(%rsp)
	movb	$0, 488(%rsp)
	movb	$0, 487(%rsp)
	movb	$0, 486(%rsp)
	movb	$0, 485(%rsp)
	movb	$0, 484(%rsp)
	movb	$0, 483(%rsp)
	movb	$0, 482(%rsp)
	movb	$0, 481(%rsp)
	movb	$0, 480(%rsp)
	movb	$0, 479(%rsp)
	movb	$0, 478(%rsp)
	movb	$0, 477(%rsp)
	movb	$0, 476(%rsp)
	movb	$0, 475(%rsp)
	movb	$0, 474(%rsp)
	movb	$0, 473(%rsp)
	movb	$0, 472(%rsp)
	movb	$0, 471(%rsp)
	movb	$0, 470(%rsp)
	movb	$0, 469(%rsp)
	movb	$0, 468(%rsp)
	movb	$0, 467(%rsp)
	movb	$0, 466(%rsp)
	movb	$0, 465(%rsp)
	movb	$0, 464(%rsp)
	movb	$0, 463(%rsp)
	movb	$0, 462(%rsp)
	movb	$0, 461(%rsp)
	movb	$0, 460(%rsp)
	movb	$0, 459(%rsp)
	movb	$0, 458(%rsp)
	movb	$0, 457(%rsp)
	movb	$0, 456(%rsp)
	movb	$0, 455(%rsp)
	movb	$0, 454(%rsp)
	movb	$0, 453(%rsp)
	movb	$0, 452(%rsp)
	movb	$0, 451(%rsp)
	movb	$0, 450(%rsp)
	movb	$0, 449(%rsp)
	movb	$0, 448(%rsp)
	movb	$0, 447(%rsp)
	movb	$0, 446(%rsp)
	movb	$0, 445(%rsp)
	movb	$0, 444(%rsp)
	movb	$0, 443(%rsp)
	movb	$0, 442(%rsp)
	movb	$0, 441(%rsp)
	movb	$0, 440(%rsp)
	movb	$0, 439(%rsp)
	movb	$0, 438(%rsp)
	movb	$0, 437(%rsp)
	movb	$0, 436(%rsp)
	movb	$0, 435(%rsp)
	movb	$0, 434(%rsp)
	movb	$0, 433(%rsp)
	movb	$0, 432(%rsp)
	movb	$0, 431(%rsp)
	movb	$0, 430(%rsp)
	movb	$0, 429(%rsp)
	movb	$0, 428(%rsp)
	movb	$0, 427(%rsp)
	movb	$0, 426(%rsp)
	movb	$0, 425(%rsp)
	movb	$0, 424(%rsp)
	movb	$0, 423(%rsp)
	movb	$0, 422(%rsp)
	movb	$0, 421(%rsp)
	movb	$0, 420(%rsp)
	movb	$0, 419(%rsp)
	movb	$0, 418(%rsp)
	movb	$0, 417(%rsp)
	movb	$0, 416(%rsp)
	movb	$0, 415(%rsp)
	movb	$0, 414(%rsp)
	movb	$0, 413(%rsp)
	movb	$0, 412(%rsp)
	movb	$0, 411(%rsp)
	movb	$0, 410(%rsp)
	movb	$0, 409(%rsp)
	movb	$0, 408(%rsp)
	movb	$0, 407(%rsp)
	movb	$0, 406(%rsp)
	movb	$0, 405(%rsp)
	movb	$0, 404(%rsp)
	movb	$0, 403(%rsp)
	movb	$0, 402(%rsp)
	movb	$0, 401(%rsp)
	movb	$0, 400(%rsp)
	movb	$0, 399(%rsp)
	movb	$0, 398(%rsp)
	movb	$0, 397(%rsp)
	movb	$0, 396(%rsp)
	movb	$0, 395(%rsp)
	movb	$0, 394(%rsp)
	movb	$0, 393(%rsp)
	movb	$0, 392(%rsp)
	movb	$0, 391(%rsp)
	movb	$0, 390(%rsp)
	movb	$0, 389(%rsp)
	movb	$0, 388(%rsp)
	movb	$0, 387(%rsp)
	movb	$0, 386(%rsp)
	movb	$0, 385(%rsp)
	movb	$0, 384(%rsp)
	movb	$0, 383(%rsp)
	movb	$0, 382(%rsp)
	movb	$0, 381(%rsp)
	movb	$0, 380(%rsp)
	movb	$0, 379(%rsp)
	movb	$0, 378(%rsp)
	movb	$0, 377(%rsp)
	movb	$0, 376(%rsp)
	movb	$0, 375(%rsp)
	movb	$0, 374(%rsp)
	movb	$0, 373(%rsp)
	movb	$0, 372(%rsp)
	movb	$0, 371(%rsp)
	movb	$0, 370(%rsp)
	movb	$0, 369(%rsp)
	movb	$0, 368(%rsp)
	movb	$0, 367(%rsp)
	movb	$0, 366(%rsp)
	movb	$0, 365(%rsp)
	movb	$0, 364(%rsp)
	movb	$0, 363(%rsp)
	movb	$0, 362(%rsp)
	movb	$0, 361(%rsp)
	movb	$0, 360(%rsp)
	movb	$0, 359(%rsp)
	movb	$0, 358(%rsp)
	movb	$0, 357(%rsp)
	movb	$0, 356(%rsp)
	movb	$0, 355(%rsp)
	movb	$0, 354(%rsp)
	movb	$0, 353(%rsp)
	movb	$0, 352(%rsp)
	movb	$0, 351(%rsp)
	movb	$0, 350(%rsp)
	movb	$0, 349(%rsp)
	movb	$0, 348(%rsp)
	movb	$0, 347(%rsp)
	movb	$0, 346(%rsp)
	movb	$0, 345(%rsp)
	movb	$0, 344(%rsp)
	movb	$0, 343(%rsp)
	movb	$0, 342(%rsp)
	movb	$0, 341(%rsp)
	movb	$0, 340(%rsp)
	movb	$0, 339(%rsp)
	movb	$0, 338(%rsp)
	movb	$0, 337(%rsp)
	movb	$0, 336(%rsp)
	movb	$0, 335(%rsp)
	movb	$0, 334(%rsp)
	movb	$0, 333(%rsp)
	movb	$0, 332(%rsp)
	movb	$0, 331(%rsp)
	movb	$0, 330(%rsp)
	movb	$0, 329(%rsp)
	movb	$0, 328(%rsp)
	movb	$0, 327(%rsp)
	movb	$0, 326(%rsp)
	movb	$0, 325(%rsp)
	movb	$0, 324(%rsp)
	movb	$0, 323(%rsp)
	movb	$0, 322(%rsp)
	movb	$0, 321(%rsp)
	movb	$0, 320(%rsp)
	movb	$0, 319(%rsp)
	movb	$0, 318(%rsp)
	movb	$0, 317(%rsp)
	movb	$0, 316(%rsp)
	movb	$0, 315(%rsp)
	movb	$0, 314(%rsp)
	movb	$0, 313(%rsp)
	movb	$0, 312(%rsp)
	movb	$0, 311(%rsp)
	movb	$0, 310(%rsp)
	movb	$0, 309(%rsp)
	movb	$0, 308(%rsp)
	movb	$0, 307(%rsp)
	movb	$0, 306(%rsp)
	movb	$0, 305(%rsp)
	movb	$0, 304(%rsp)
	movb	$0, 303(%rsp)
	movb	$0, 302(%rsp)
	movb	$0, 301(%rsp)
	movb	$0, 300(%rsp)
	movb	$0, 299(%rsp)
	movb	$0, 298(%rsp)
	movb	$0, 297(%rsp)
	movb	$0, 296(%rsp)
	movb	$0, 295(%rsp)
	movb	$0, 294(%rsp)
	movb	$0, 293(%rsp)
	movb	$0, 292(%rsp)
	movb	$0, 291(%rsp)
	movb	$0, 290(%rsp)
	movb	$0, 289(%rsp)
	movb	$0, 288(%rsp)
	movb	$0, 287(%rsp)
	movb	$0, 286(%rsp)
	movb	$0, 285(%rsp)
	movb	$0, 284(%rsp)
	movb	$0, 283(%rsp)
	movb	$0, 282(%rsp)
	movb	$0, 281(%rsp)
	movb	$0, 280(%rsp)
	movb	$0, 279(%rsp)
	movb	$0, 278(%rsp)
	movb	$0, 277(%rsp)
	movb	$0, 276(%rsp)
	movb	$0, 275(%rsp)
	movb	$0, 274(%rsp)
	movb	$0, 273(%rsp)
	movb	$0, 272(%rsp)
	movb	$0, 271(%rsp)
	movb	$0, 270(%rsp)
	movb	$0, 269(%rsp)
	movb	$0, 268(%rsp)
	movb	$0, 267(%rsp)
	movb	$0, 266(%rsp)
	movb	$0, 265(%rsp)
	movb	$0, 264(%rsp)
	movb	$0, 263(%rsp)
	movb	$0, 262(%rsp)
	movb	$0, 261(%rsp)
	movb	$0, 260(%rsp)
	movb	$0, 259(%rsp)
	movb	$0, 258(%rsp)
	movb	$0, 257(%rsp)
	movb	$0, 256(%rsp)
	movb	$0, 255(%rsp)
	movb	$0, 254(%rsp)
	movb	$0, 253(%rsp)
	movb	$0, 252(%rsp)
	movb	$0, 251(%rsp)
	movb	$0, 250(%rsp)
	movb	$0, 249(%rsp)
	movb	$0, 248(%rsp)
	movb	$0, 247(%rsp)
	movb	$0, 246(%rsp)
	movb	$0, 245(%rsp)
	movb	$0, 244(%rsp)
	movb	$0, 243(%rsp)
	movb	$0, 242(%rsp)
	movb	$0, 241(%rsp)
	movb	$0, 240(%rsp)
	movb	$0, 239(%rsp)
	movb	$0, 238(%rsp)
	movb	$0, 237(%rsp)
	movb	$0, 236(%rsp)
	movb	$0, 235(%rsp)
	movb	$0, 234(%rsp)
	movb	$0, 233(%rsp)
	movb	$0, 232(%rsp)
	movb	$0, 231(%rsp)
	movb	$0, 230(%rsp)
	movb	$0, 229(%rsp)
	movb	$0, 228(%rsp)
	movb	$0, 227(%rsp)
	movb	$0, 226(%rsp)
	movb	$0, 225(%rsp)
	movb	$0, 224(%rsp)
	movb	$0, 223(%rsp)
	movb	$0, 222(%rsp)
	movb	$0, 221(%rsp)
	movb	$0, 220(%rsp)
	movb	$0, 219(%rsp)
	movb	$0, 218(%rsp)
	movb	$0, 217(%rsp)
	movb	$0, 216(%rsp)
	movb	$0, 215(%rsp)
	movb	$0, 214(%rsp)
	movb	$0, 213(%rsp)
	movb	$0, 212(%rsp)
	movb	$0, 211(%rsp)
	movb	$0, 210(%rsp)
	movb	$0, 209(%rsp)
	movb	$0, 208(%rsp)
	movb	$0, 207(%rsp)
	movb	$0, 206(%rsp)
	movb	$0, 205(%rsp)
	movb	$0, 204(%rsp)
	movb	$0, 203(%rsp)
	movb	$0, 202(%rsp)
	movb	$0, 201(%rsp)
	movb	$0, 200(%rsp)
	movb	$0, 199(%rsp)
	movb	$0, 198(%rsp)
	movb	$0, 197(%rsp)
	movb	$0, 196(%rsp)
	movb	$0, 195(%rsp)
	movb	$0, 194(%rsp)
	movb	$0, 193(%rsp)
	movb	$0, 192(%rsp)
	movb	$0, 191(%rsp)
	movb	$0, 190(%rsp)
	movb	$0, 189(%rsp)
	movb	$0, 188(%rsp)
	movb	$0, 187(%rsp)
	movb	$0, 186(%rsp)
	movb	$0, 185(%rsp)
	movb	$0, 184(%rsp)
	movb	$0, 183(%rsp)
	movb	$0, 182(%rsp)
	movb	$0, 181(%rsp)
	movb	$0, 180(%rsp)
	movb	$0, 179(%rsp)
	movb	$0, 178(%rsp)
	movb	$0, 177(%rsp)
	movb	$0, 176(%rsp)
	movb	$0, 175(%rsp)
	movb	$0, 174(%rsp)
	movb	$0, 173(%rsp)
	movb	$0, 172(%rsp)
	movb	$0, 171(%rsp)
	movb	$0, 170(%rsp)
	movb	$0, 169(%rsp)
	movb	$0, 168(%rsp)
	movb	$0, 167(%rsp)
	movb	$0, 166(%rsp)
	movb	$0, 165(%rsp)
	movb	$0, 164(%rsp)
	movb	$0, 163(%rsp)
	movb	$0, 162(%rsp)
	movb	$0, 161(%rsp)
	movb	$0, 160(%rsp)
	movb	$0, 159(%rsp)
	movb	$0, 158(%rsp)
	movb	$0, 157(%rsp)
	movb	$0, 156(%rsp)
	movb	$0, 155(%rsp)
	movb	$0, 154(%rsp)
	movb	$0, 153(%rsp)
	movb	$0, 152(%rsp)
	movb	$0, 151(%rsp)
	movb	$0, 150(%rsp)
	movb	$0, 149(%rsp)
	movb	$0, 148(%rsp)
	movb	$0, 147(%rsp)
	movb	$0, 146(%rsp)
	movb	$0, 145(%rsp)
	movb	$0, 144(%rsp)
	movb	$0, 143(%rsp)
	movb	$0, 142(%rsp)
	movb	$0, 141(%rsp)
	movb	$0, 140(%rsp)
	movb	$0, 139(%rsp)
	movb	$0, 138(%rsp)
	movb	$0, 137(%rsp)
	movb	$0, 136(%rsp)
	movb	$0, 135(%rsp)
	movb	$0, 134(%rsp)
	movb	$0, 133(%rsp)
	movb	$0, 132(%rsp)
	movb	$0, 131(%rsp)
	movb	$0, 130(%rsp)
	movb	$0, 129(%rsp)
	movb	$0, 128(%rsp)
	movb	$0, 127(%rsp)
	movb	$0, 126(%rsp)
	movb	$0, 125(%rsp)
	movb	$0, 124(%rsp)
	movb	$0, 123(%rsp)
	movb	$0, 122(%rsp)
	movb	$0, 121(%rsp)
	movb	$0, 120(%rsp)
	movb	$0, 119(%rsp)
	movb	$0, 118(%rsp)
	movb	$0, 117(%rsp)
	movb	$0, 116(%rsp)
	movb	$0, 115(%rsp)
	movb	$0, 114(%rsp)
	movb	$0, 113(%rsp)
	movb	$0, 112(%rsp)
	movb	$0, 111(%rsp)
	movb	$0, 110(%rsp)
	movb	$0, 109(%rsp)
	movb	$0, 108(%rsp)
	movb	$0, 107(%rsp)
	movb	$0, 106(%rsp)
	movb	$0, 105(%rsp)
	movb	$0, 104(%rsp)
	movb	$0, 103(%rsp)
	movb	$0, 102(%rsp)
	movb	$0, 101(%rsp)
	movb	$0, 100(%rsp)
	movb	$0, 99(%rsp)
	movb	$0, 98(%rsp)
	movb	$0, 97(%rsp)
	movb	$0, 96(%rsp)
	movb	$0, 95(%rsp)
	movb	$0, 94(%rsp)
	movb	$0, 93(%rsp)
	movb	$0, 92(%rsp)
	movb	$0, 91(%rsp)
	movb	$0, 90(%rsp)
	movb	$0, 89(%rsp)
	movb	$0, 88(%rsp)
	movb	$0, 87(%rsp)
	movb	$0, 86(%rsp)
	movb	$0, 85(%rsp)
	movb	$0, 84(%rsp)
	movb	$0, 83(%rsp)
	movb	$0, 82(%rsp)
	movb	$0, 81(%rsp)
	movb	$0, 80(%rsp)
	movb	$0, 79(%rsp)
	movb	$0, 78(%rsp)
	movb	$0, 77(%rsp)
	movb	$0, 76(%rsp)
	movb	$0, 75(%rsp)
	movb	$0, 74(%rsp)
	movb	$0, 73(%rsp)
	movb	$0, 72(%rsp)
	movb	$0, 71(%rsp)
	movb	$0, 70(%rsp)
	movb	$0, 69(%rsp)
	movb	$0, 68(%rsp)
	movb	$0, 67(%rsp)
	movb	$0, 66(%rsp)
	movb	$0, 65(%rsp)
	movb	$0, 64(%rsp)
	movb	$0, 63(%rsp)
	movb	$0, 62(%rsp)
	movb	$0, 61(%rsp)
	movb	$0, 60(%rsp)
	movb	$0, 59(%rsp)
	movb	$0, 58(%rsp)
	movb	$0, 57(%rsp)
	movb	$0, 56(%rsp)
	movb	$0, 55(%rsp)
	movb	$0, 54(%rsp)
	movb	$0, 53(%rsp)
	movb	$0, 52(%rsp)
	movb	$0, 51(%rsp)
	movb	$0, 50(%rsp)
	movb	$0, 49(%rsp)
	movb	$0, 48(%rsp)
	movb	$0, 47(%rsp)
	movb	$0, 46(%rsp)
	movb	$0, 45(%rsp)
	movb	$0, 44(%rsp)
	movb	$0, 43(%rsp)
	movb	$0, 42(%rsp)
	movb	$0, 41(%rsp)
	movb	$0, 40(%rsp)
	movb	$0, 39(%rsp)
	movb	$0, 38(%rsp)
	movb	$0, 37(%rsp)
	movb	$0, 36(%rsp)
	movb	$0, 35(%rsp)
	movb	$0, 34(%rsp)
	movb	$0, 33(%rsp)
	movb	$0, 32(%rsp)
	movb	$0, 31(%rsp)
	movb	$0, 30(%rsp)
	movb	$0, 29(%rsp)
	movb	$0, 28(%rsp)
	movb	$0, 27(%rsp)
	movb	$0, 26(%rsp)
	movb	$0, 25(%rsp)
	movb	$0, 24(%rsp)
	movb	$0, 23(%rsp)
	movb	$0, 22(%rsp)
	movb	$0, 21(%rsp)
	movb	$0, 20(%rsp)
	movb	$0, 19(%rsp)
	movb	$0, 18(%rsp)
	movb	$0, 17(%rsp)
	movb	$0, 16(%rsp)
	movb	$0, 15(%rsp)
	movb	$0, 14(%rsp)
	movb	$0, 13(%rsp)
	movb	$0, 12(%rsp)
	movb	$0, 11(%rsp)
	movb	$0, 10(%rsp)
	movb	$0, 9(%rsp)
	movb	$0, 8(%rsp)
	movb	$0, 7(%rsp)
	movb	$0, 6(%rsp)
	movb	$0, 5(%rsp)
	movb	$0, 4(%rsp)
	movb	$0, 3(%rsp)
	movb	$0, 2(%rsp)
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
_gen_chain_inplace_jazz:
gen_chain_inplace_jazz:
	movq	%rsp, %rax
	leaq	-48(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r14, 24(%rsp)
	movq	%r15, 32(%rsp)
	movq	%rax, 40(%rsp)
	movl	$0, %eax
	movq	%rdi, %rdx
	leaq	-32(%rsp), %rsp
	call	L_gen_chain_inplace$1
Lgen_chain_inplace_jazz$1:
	leaq	32(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r14
	movq	32(%rsp), %r15
	movq	40(%rsp), %rsp
	movq	%rsp, %rsi
	andq	$-8, %rsp
	subq	$992, %rsp
	movb	$0, 991(%rsp)
	movb	$0, 990(%rsp)
	movb	$0, 989(%rsp)
	movb	$0, 988(%rsp)
	movb	$0, 987(%rsp)
	movb	$0, 986(%rsp)
	movb	$0, 985(%rsp)
	movb	$0, 984(%rsp)
	movb	$0, 983(%rsp)
	movb	$0, 982(%rsp)
	movb	$0, 981(%rsp)
	movb	$0, 980(%rsp)
	movb	$0, 979(%rsp)
	movb	$0, 978(%rsp)
	movb	$0, 977(%rsp)
	movb	$0, 976(%rsp)
	movb	$0, 975(%rsp)
	movb	$0, 974(%rsp)
	movb	$0, 973(%rsp)
	movb	$0, 972(%rsp)
	movb	$0, 971(%rsp)
	movb	$0, 970(%rsp)
	movb	$0, 969(%rsp)
	movb	$0, 968(%rsp)
	movb	$0, 967(%rsp)
	movb	$0, 966(%rsp)
	movb	$0, 965(%rsp)
	movb	$0, 964(%rsp)
	movb	$0, 963(%rsp)
	movb	$0, 962(%rsp)
	movb	$0, 961(%rsp)
	movb	$0, 960(%rsp)
	movb	$0, 959(%rsp)
	movb	$0, 958(%rsp)
	movb	$0, 957(%rsp)
	movb	$0, 956(%rsp)
	movb	$0, 955(%rsp)
	movb	$0, 954(%rsp)
	movb	$0, 953(%rsp)
	movb	$0, 952(%rsp)
	movb	$0, 951(%rsp)
	movb	$0, 950(%rsp)
	movb	$0, 949(%rsp)
	movb	$0, 948(%rsp)
	movb	$0, 947(%rsp)
	movb	$0, 946(%rsp)
	movb	$0, 945(%rsp)
	movb	$0, 944(%rsp)
	movb	$0, 943(%rsp)
	movb	$0, 942(%rsp)
	movb	$0, 941(%rsp)
	movb	$0, 940(%rsp)
	movb	$0, 939(%rsp)
	movb	$0, 938(%rsp)
	movb	$0, 937(%rsp)
	movb	$0, 936(%rsp)
	movb	$0, 935(%rsp)
	movb	$0, 934(%rsp)
	movb	$0, 933(%rsp)
	movb	$0, 932(%rsp)
	movb	$0, 931(%rsp)
	movb	$0, 930(%rsp)
	movb	$0, 929(%rsp)
	movb	$0, 928(%rsp)
	movb	$0, 927(%rsp)
	movb	$0, 926(%rsp)
	movb	$0, 925(%rsp)
	movb	$0, 924(%rsp)
	movb	$0, 923(%rsp)
	movb	$0, 922(%rsp)
	movb	$0, 921(%rsp)
	movb	$0, 920(%rsp)
	movb	$0, 919(%rsp)
	movb	$0, 918(%rsp)
	movb	$0, 917(%rsp)
	movb	$0, 916(%rsp)
	movb	$0, 915(%rsp)
	movb	$0, 914(%rsp)
	movb	$0, 913(%rsp)
	movb	$0, 912(%rsp)
	movb	$0, 911(%rsp)
	movb	$0, 910(%rsp)
	movb	$0, 909(%rsp)
	movb	$0, 908(%rsp)
	movb	$0, 907(%rsp)
	movb	$0, 906(%rsp)
	movb	$0, 905(%rsp)
	movb	$0, 904(%rsp)
	movb	$0, 903(%rsp)
	movb	$0, 902(%rsp)
	movb	$0, 901(%rsp)
	movb	$0, 900(%rsp)
	movb	$0, 899(%rsp)
	movb	$0, 898(%rsp)
	movb	$0, 897(%rsp)
	movb	$0, 896(%rsp)
	movb	$0, 895(%rsp)
	movb	$0, 894(%rsp)
	movb	$0, 893(%rsp)
	movb	$0, 892(%rsp)
	movb	$0, 891(%rsp)
	movb	$0, 890(%rsp)
	movb	$0, 889(%rsp)
	movb	$0, 888(%rsp)
	movb	$0, 887(%rsp)
	movb	$0, 886(%rsp)
	movb	$0, 885(%rsp)
	movb	$0, 884(%rsp)
	movb	$0, 883(%rsp)
	movb	$0, 882(%rsp)
	movb	$0, 881(%rsp)
	movb	$0, 880(%rsp)
	movb	$0, 879(%rsp)
	movb	$0, 878(%rsp)
	movb	$0, 877(%rsp)
	movb	$0, 876(%rsp)
	movb	$0, 875(%rsp)
	movb	$0, 874(%rsp)
	movb	$0, 873(%rsp)
	movb	$0, 872(%rsp)
	movb	$0, 871(%rsp)
	movb	$0, 870(%rsp)
	movb	$0, 869(%rsp)
	movb	$0, 868(%rsp)
	movb	$0, 867(%rsp)
	movb	$0, 866(%rsp)
	movb	$0, 865(%rsp)
	movb	$0, 864(%rsp)
	movb	$0, 863(%rsp)
	movb	$0, 862(%rsp)
	movb	$0, 861(%rsp)
	movb	$0, 860(%rsp)
	movb	$0, 859(%rsp)
	movb	$0, 858(%rsp)
	movb	$0, 857(%rsp)
	movb	$0, 856(%rsp)
	movb	$0, 855(%rsp)
	movb	$0, 854(%rsp)
	movb	$0, 853(%rsp)
	movb	$0, 852(%rsp)
	movb	$0, 851(%rsp)
	movb	$0, 850(%rsp)
	movb	$0, 849(%rsp)
	movb	$0, 848(%rsp)
	movb	$0, 847(%rsp)
	movb	$0, 846(%rsp)
	movb	$0, 845(%rsp)
	movb	$0, 844(%rsp)
	movb	$0, 843(%rsp)
	movb	$0, 842(%rsp)
	movb	$0, 841(%rsp)
	movb	$0, 840(%rsp)
	movb	$0, 839(%rsp)
	movb	$0, 838(%rsp)
	movb	$0, 837(%rsp)
	movb	$0, 836(%rsp)
	movb	$0, 835(%rsp)
	movb	$0, 834(%rsp)
	movb	$0, 833(%rsp)
	movb	$0, 832(%rsp)
	movb	$0, 831(%rsp)
	movb	$0, 830(%rsp)
	movb	$0, 829(%rsp)
	movb	$0, 828(%rsp)
	movb	$0, 827(%rsp)
	movb	$0, 826(%rsp)
	movb	$0, 825(%rsp)
	movb	$0, 824(%rsp)
	movb	$0, 823(%rsp)
	movb	$0, 822(%rsp)
	movb	$0, 821(%rsp)
	movb	$0, 820(%rsp)
	movb	$0, 819(%rsp)
	movb	$0, 818(%rsp)
	movb	$0, 817(%rsp)
	movb	$0, 816(%rsp)
	movb	$0, 815(%rsp)
	movb	$0, 814(%rsp)
	movb	$0, 813(%rsp)
	movb	$0, 812(%rsp)
	movb	$0, 811(%rsp)
	movb	$0, 810(%rsp)
	movb	$0, 809(%rsp)
	movb	$0, 808(%rsp)
	movb	$0, 807(%rsp)
	movb	$0, 806(%rsp)
	movb	$0, 805(%rsp)
	movb	$0, 804(%rsp)
	movb	$0, 803(%rsp)
	movb	$0, 802(%rsp)
	movb	$0, 801(%rsp)
	movb	$0, 800(%rsp)
	movb	$0, 799(%rsp)
	movb	$0, 798(%rsp)
	movb	$0, 797(%rsp)
	movb	$0, 796(%rsp)
	movb	$0, 795(%rsp)
	movb	$0, 794(%rsp)
	movb	$0, 793(%rsp)
	movb	$0, 792(%rsp)
	movb	$0, 791(%rsp)
	movb	$0, 790(%rsp)
	movb	$0, 789(%rsp)
	movb	$0, 788(%rsp)
	movb	$0, 787(%rsp)
	movb	$0, 786(%rsp)
	movb	$0, 785(%rsp)
	movb	$0, 784(%rsp)
	movb	$0, 783(%rsp)
	movb	$0, 782(%rsp)
	movb	$0, 781(%rsp)
	movb	$0, 780(%rsp)
	movb	$0, 779(%rsp)
	movb	$0, 778(%rsp)
	movb	$0, 777(%rsp)
	movb	$0, 776(%rsp)
	movb	$0, 775(%rsp)
	movb	$0, 774(%rsp)
	movb	$0, 773(%rsp)
	movb	$0, 772(%rsp)
	movb	$0, 771(%rsp)
	movb	$0, 770(%rsp)
	movb	$0, 769(%rsp)
	movb	$0, 768(%rsp)
	movb	$0, 767(%rsp)
	movb	$0, 766(%rsp)
	movb	$0, 765(%rsp)
	movb	$0, 764(%rsp)
	movb	$0, 763(%rsp)
	movb	$0, 762(%rsp)
	movb	$0, 761(%rsp)
	movb	$0, 760(%rsp)
	movb	$0, 759(%rsp)
	movb	$0, 758(%rsp)
	movb	$0, 757(%rsp)
	movb	$0, 756(%rsp)
	movb	$0, 755(%rsp)
	movb	$0, 754(%rsp)
	movb	$0, 753(%rsp)
	movb	$0, 752(%rsp)
	movb	$0, 751(%rsp)
	movb	$0, 750(%rsp)
	movb	$0, 749(%rsp)
	movb	$0, 748(%rsp)
	movb	$0, 747(%rsp)
	movb	$0, 746(%rsp)
	movb	$0, 745(%rsp)
	movb	$0, 744(%rsp)
	movb	$0, 743(%rsp)
	movb	$0, 742(%rsp)
	movb	$0, 741(%rsp)
	movb	$0, 740(%rsp)
	movb	$0, 739(%rsp)
	movb	$0, 738(%rsp)
	movb	$0, 737(%rsp)
	movb	$0, 736(%rsp)
	movb	$0, 735(%rsp)
	movb	$0, 734(%rsp)
	movb	$0, 733(%rsp)
	movb	$0, 732(%rsp)
	movb	$0, 731(%rsp)
	movb	$0, 730(%rsp)
	movb	$0, 729(%rsp)
	movb	$0, 728(%rsp)
	movb	$0, 727(%rsp)
	movb	$0, 726(%rsp)
	movb	$0, 725(%rsp)
	movb	$0, 724(%rsp)
	movb	$0, 723(%rsp)
	movb	$0, 722(%rsp)
	movb	$0, 721(%rsp)
	movb	$0, 720(%rsp)
	movb	$0, 719(%rsp)
	movb	$0, 718(%rsp)
	movb	$0, 717(%rsp)
	movb	$0, 716(%rsp)
	movb	$0, 715(%rsp)
	movb	$0, 714(%rsp)
	movb	$0, 713(%rsp)
	movb	$0, 712(%rsp)
	movb	$0, 711(%rsp)
	movb	$0, 710(%rsp)
	movb	$0, 709(%rsp)
	movb	$0, 708(%rsp)
	movb	$0, 707(%rsp)
	movb	$0, 706(%rsp)
	movb	$0, 705(%rsp)
	movb	$0, 704(%rsp)
	movb	$0, 703(%rsp)
	movb	$0, 702(%rsp)
	movb	$0, 701(%rsp)
	movb	$0, 700(%rsp)
	movb	$0, 699(%rsp)
	movb	$0, 698(%rsp)
	movb	$0, 697(%rsp)
	movb	$0, 696(%rsp)
	movb	$0, 695(%rsp)
	movb	$0, 694(%rsp)
	movb	$0, 693(%rsp)
	movb	$0, 692(%rsp)
	movb	$0, 691(%rsp)
	movb	$0, 690(%rsp)
	movb	$0, 689(%rsp)
	movb	$0, 688(%rsp)
	movb	$0, 687(%rsp)
	movb	$0, 686(%rsp)
	movb	$0, 685(%rsp)
	movb	$0, 684(%rsp)
	movb	$0, 683(%rsp)
	movb	$0, 682(%rsp)
	movb	$0, 681(%rsp)
	movb	$0, 680(%rsp)
	movb	$0, 679(%rsp)
	movb	$0, 678(%rsp)
	movb	$0, 677(%rsp)
	movb	$0, 676(%rsp)
	movb	$0, 675(%rsp)
	movb	$0, 674(%rsp)
	movb	$0, 673(%rsp)
	movb	$0, 672(%rsp)
	movb	$0, 671(%rsp)
	movb	$0, 670(%rsp)
	movb	$0, 669(%rsp)
	movb	$0, 668(%rsp)
	movb	$0, 667(%rsp)
	movb	$0, 666(%rsp)
	movb	$0, 665(%rsp)
	movb	$0, 664(%rsp)
	movb	$0, 663(%rsp)
	movb	$0, 662(%rsp)
	movb	$0, 661(%rsp)
	movb	$0, 660(%rsp)
	movb	$0, 659(%rsp)
	movb	$0, 658(%rsp)
	movb	$0, 657(%rsp)
	movb	$0, 656(%rsp)
	movb	$0, 655(%rsp)
	movb	$0, 654(%rsp)
	movb	$0, 653(%rsp)
	movb	$0, 652(%rsp)
	movb	$0, 651(%rsp)
	movb	$0, 650(%rsp)
	movb	$0, 649(%rsp)
	movb	$0, 648(%rsp)
	movb	$0, 647(%rsp)
	movb	$0, 646(%rsp)
	movb	$0, 645(%rsp)
	movb	$0, 644(%rsp)
	movb	$0, 643(%rsp)
	movb	$0, 642(%rsp)
	movb	$0, 641(%rsp)
	movb	$0, 640(%rsp)
	movb	$0, 639(%rsp)
	movb	$0, 638(%rsp)
	movb	$0, 637(%rsp)
	movb	$0, 636(%rsp)
	movb	$0, 635(%rsp)
	movb	$0, 634(%rsp)
	movb	$0, 633(%rsp)
	movb	$0, 632(%rsp)
	movb	$0, 631(%rsp)
	movb	$0, 630(%rsp)
	movb	$0, 629(%rsp)
	movb	$0, 628(%rsp)
	movb	$0, 627(%rsp)
	movb	$0, 626(%rsp)
	movb	$0, 625(%rsp)
	movb	$0, 624(%rsp)
	movb	$0, 623(%rsp)
	movb	$0, 622(%rsp)
	movb	$0, 621(%rsp)
	movb	$0, 620(%rsp)
	movb	$0, 619(%rsp)
	movb	$0, 618(%rsp)
	movb	$0, 617(%rsp)
	movb	$0, 616(%rsp)
	movb	$0, 615(%rsp)
	movb	$0, 614(%rsp)
	movb	$0, 613(%rsp)
	movb	$0, 612(%rsp)
	movb	$0, 611(%rsp)
	movb	$0, 610(%rsp)
	movb	$0, 609(%rsp)
	movb	$0, 608(%rsp)
	movb	$0, 607(%rsp)
	movb	$0, 606(%rsp)
	movb	$0, 605(%rsp)
	movb	$0, 604(%rsp)
	movb	$0, 603(%rsp)
	movb	$0, 602(%rsp)
	movb	$0, 601(%rsp)
	movb	$0, 600(%rsp)
	movb	$0, 599(%rsp)
	movb	$0, 598(%rsp)
	movb	$0, 597(%rsp)
	movb	$0, 596(%rsp)
	movb	$0, 595(%rsp)
	movb	$0, 594(%rsp)
	movb	$0, 593(%rsp)
	movb	$0, 592(%rsp)
	movb	$0, 591(%rsp)
	movb	$0, 590(%rsp)
	movb	$0, 589(%rsp)
	movb	$0, 588(%rsp)
	movb	$0, 587(%rsp)
	movb	$0, 586(%rsp)
	movb	$0, 585(%rsp)
	movb	$0, 584(%rsp)
	movb	$0, 583(%rsp)
	movb	$0, 582(%rsp)
	movb	$0, 581(%rsp)
	movb	$0, 580(%rsp)
	movb	$0, 579(%rsp)
	movb	$0, 578(%rsp)
	movb	$0, 577(%rsp)
	movb	$0, 576(%rsp)
	movb	$0, 575(%rsp)
	movb	$0, 574(%rsp)
	movb	$0, 573(%rsp)
	movb	$0, 572(%rsp)
	movb	$0, 571(%rsp)
	movb	$0, 570(%rsp)
	movb	$0, 569(%rsp)
	movb	$0, 568(%rsp)
	movb	$0, 567(%rsp)
	movb	$0, 566(%rsp)
	movb	$0, 565(%rsp)
	movb	$0, 564(%rsp)
	movb	$0, 563(%rsp)
	movb	$0, 562(%rsp)
	movb	$0, 561(%rsp)
	movb	$0, 560(%rsp)
	movb	$0, 559(%rsp)
	movb	$0, 558(%rsp)
	movb	$0, 557(%rsp)
	movb	$0, 556(%rsp)
	movb	$0, 555(%rsp)
	movb	$0, 554(%rsp)
	movb	$0, 553(%rsp)
	movb	$0, 552(%rsp)
	movb	$0, 551(%rsp)
	movb	$0, 550(%rsp)
	movb	$0, 549(%rsp)
	movb	$0, 548(%rsp)
	movb	$0, 547(%rsp)
	movb	$0, 546(%rsp)
	movb	$0, 545(%rsp)
	movb	$0, 544(%rsp)
	movb	$0, 543(%rsp)
	movb	$0, 542(%rsp)
	movb	$0, 541(%rsp)
	movb	$0, 540(%rsp)
	movb	$0, 539(%rsp)
	movb	$0, 538(%rsp)
	movb	$0, 537(%rsp)
	movb	$0, 536(%rsp)
	movb	$0, 535(%rsp)
	movb	$0, 534(%rsp)
	movb	$0, 533(%rsp)
	movb	$0, 532(%rsp)
	movb	$0, 531(%rsp)
	movb	$0, 530(%rsp)
	movb	$0, 529(%rsp)
	movb	$0, 528(%rsp)
	movb	$0, 527(%rsp)
	movb	$0, 526(%rsp)
	movb	$0, 525(%rsp)
	movb	$0, 524(%rsp)
	movb	$0, 523(%rsp)
	movb	$0, 522(%rsp)
	movb	$0, 521(%rsp)
	movb	$0, 520(%rsp)
	movb	$0, 519(%rsp)
	movb	$0, 518(%rsp)
	movb	$0, 517(%rsp)
	movb	$0, 516(%rsp)
	movb	$0, 515(%rsp)
	movb	$0, 514(%rsp)
	movb	$0, 513(%rsp)
	movb	$0, 512(%rsp)
	movb	$0, 511(%rsp)
	movb	$0, 510(%rsp)
	movb	$0, 509(%rsp)
	movb	$0, 508(%rsp)
	movb	$0, 507(%rsp)
	movb	$0, 506(%rsp)
	movb	$0, 505(%rsp)
	movb	$0, 504(%rsp)
	movb	$0, 503(%rsp)
	movb	$0, 502(%rsp)
	movb	$0, 501(%rsp)
	movb	$0, 500(%rsp)
	movb	$0, 499(%rsp)
	movb	$0, 498(%rsp)
	movb	$0, 497(%rsp)
	movb	$0, 496(%rsp)
	movb	$0, 495(%rsp)
	movb	$0, 494(%rsp)
	movb	$0, 493(%rsp)
	movb	$0, 492(%rsp)
	movb	$0, 491(%rsp)
	movb	$0, 490(%rsp)
	movb	$0, 489(%rsp)
	movb	$0, 488(%rsp)
	movb	$0, 487(%rsp)
	movb	$0, 486(%rsp)
	movb	$0, 485(%rsp)
	movb	$0, 484(%rsp)
	movb	$0, 483(%rsp)
	movb	$0, 482(%rsp)
	movb	$0, 481(%rsp)
	movb	$0, 480(%rsp)
	movb	$0, 479(%rsp)
	movb	$0, 478(%rsp)
	movb	$0, 477(%rsp)
	movb	$0, 476(%rsp)
	movb	$0, 475(%rsp)
	movb	$0, 474(%rsp)
	movb	$0, 473(%rsp)
	movb	$0, 472(%rsp)
	movb	$0, 471(%rsp)
	movb	$0, 470(%rsp)
	movb	$0, 469(%rsp)
	movb	$0, 468(%rsp)
	movb	$0, 467(%rsp)
	movb	$0, 466(%rsp)
	movb	$0, 465(%rsp)
	movb	$0, 464(%rsp)
	movb	$0, 463(%rsp)
	movb	$0, 462(%rsp)
	movb	$0, 461(%rsp)
	movb	$0, 460(%rsp)
	movb	$0, 459(%rsp)
	movb	$0, 458(%rsp)
	movb	$0, 457(%rsp)
	movb	$0, 456(%rsp)
	movb	$0, 455(%rsp)
	movb	$0, 454(%rsp)
	movb	$0, 453(%rsp)
	movb	$0, 452(%rsp)
	movb	$0, 451(%rsp)
	movb	$0, 450(%rsp)
	movb	$0, 449(%rsp)
	movb	$0, 448(%rsp)
	movb	$0, 447(%rsp)
	movb	$0, 446(%rsp)
	movb	$0, 445(%rsp)
	movb	$0, 444(%rsp)
	movb	$0, 443(%rsp)
	movb	$0, 442(%rsp)
	movb	$0, 441(%rsp)
	movb	$0, 440(%rsp)
	movb	$0, 439(%rsp)
	movb	$0, 438(%rsp)
	movb	$0, 437(%rsp)
	movb	$0, 436(%rsp)
	movb	$0, 435(%rsp)
	movb	$0, 434(%rsp)
	movb	$0, 433(%rsp)
	movb	$0, 432(%rsp)
	movb	$0, 431(%rsp)
	movb	$0, 430(%rsp)
	movb	$0, 429(%rsp)
	movb	$0, 428(%rsp)
	movb	$0, 427(%rsp)
	movb	$0, 426(%rsp)
	movb	$0, 425(%rsp)
	movb	$0, 424(%rsp)
	movb	$0, 423(%rsp)
	movb	$0, 422(%rsp)
	movb	$0, 421(%rsp)
	movb	$0, 420(%rsp)
	movb	$0, 419(%rsp)
	movb	$0, 418(%rsp)
	movb	$0, 417(%rsp)
	movb	$0, 416(%rsp)
	movb	$0, 415(%rsp)
	movb	$0, 414(%rsp)
	movb	$0, 413(%rsp)
	movb	$0, 412(%rsp)
	movb	$0, 411(%rsp)
	movb	$0, 410(%rsp)
	movb	$0, 409(%rsp)
	movb	$0, 408(%rsp)
	movb	$0, 407(%rsp)
	movb	$0, 406(%rsp)
	movb	$0, 405(%rsp)
	movb	$0, 404(%rsp)
	movb	$0, 403(%rsp)
	movb	$0, 402(%rsp)
	movb	$0, 401(%rsp)
	movb	$0, 400(%rsp)
	movb	$0, 399(%rsp)
	movb	$0, 398(%rsp)
	movb	$0, 397(%rsp)
	movb	$0, 396(%rsp)
	movb	$0, 395(%rsp)
	movb	$0, 394(%rsp)
	movb	$0, 393(%rsp)
	movb	$0, 392(%rsp)
	movb	$0, 391(%rsp)
	movb	$0, 390(%rsp)
	movb	$0, 389(%rsp)
	movb	$0, 388(%rsp)
	movb	$0, 387(%rsp)
	movb	$0, 386(%rsp)
	movb	$0, 385(%rsp)
	movb	$0, 384(%rsp)
	movb	$0, 383(%rsp)
	movb	$0, 382(%rsp)
	movb	$0, 381(%rsp)
	movb	$0, 380(%rsp)
	movb	$0, 379(%rsp)
	movb	$0, 378(%rsp)
	movb	$0, 377(%rsp)
	movb	$0, 376(%rsp)
	movb	$0, 375(%rsp)
	movb	$0, 374(%rsp)
	movb	$0, 373(%rsp)
	movb	$0, 372(%rsp)
	movb	$0, 371(%rsp)
	movb	$0, 370(%rsp)
	movb	$0, 369(%rsp)
	movb	$0, 368(%rsp)
	movb	$0, 367(%rsp)
	movb	$0, 366(%rsp)
	movb	$0, 365(%rsp)
	movb	$0, 364(%rsp)
	movb	$0, 363(%rsp)
	movb	$0, 362(%rsp)
	movb	$0, 361(%rsp)
	movb	$0, 360(%rsp)
	movb	$0, 359(%rsp)
	movb	$0, 358(%rsp)
	movb	$0, 357(%rsp)
	movb	$0, 356(%rsp)
	movb	$0, 355(%rsp)
	movb	$0, 354(%rsp)
	movb	$0, 353(%rsp)
	movb	$0, 352(%rsp)
	movb	$0, 351(%rsp)
	movb	$0, 350(%rsp)
	movb	$0, 349(%rsp)
	movb	$0, 348(%rsp)
	movb	$0, 347(%rsp)
	movb	$0, 346(%rsp)
	movb	$0, 345(%rsp)
	movb	$0, 344(%rsp)
	movb	$0, 343(%rsp)
	movb	$0, 342(%rsp)
	movb	$0, 341(%rsp)
	movb	$0, 340(%rsp)
	movb	$0, 339(%rsp)
	movb	$0, 338(%rsp)
	movb	$0, 337(%rsp)
	movb	$0, 336(%rsp)
	movb	$0, 335(%rsp)
	movb	$0, 334(%rsp)
	movb	$0, 333(%rsp)
	movb	$0, 332(%rsp)
	movb	$0, 331(%rsp)
	movb	$0, 330(%rsp)
	movb	$0, 329(%rsp)
	movb	$0, 328(%rsp)
	movb	$0, 327(%rsp)
	movb	$0, 326(%rsp)
	movb	$0, 325(%rsp)
	movb	$0, 324(%rsp)
	movb	$0, 323(%rsp)
	movb	$0, 322(%rsp)
	movb	$0, 321(%rsp)
	movb	$0, 320(%rsp)
	movb	$0, 319(%rsp)
	movb	$0, 318(%rsp)
	movb	$0, 317(%rsp)
	movb	$0, 316(%rsp)
	movb	$0, 315(%rsp)
	movb	$0, 314(%rsp)
	movb	$0, 313(%rsp)
	movb	$0, 312(%rsp)
	movb	$0, 311(%rsp)
	movb	$0, 310(%rsp)
	movb	$0, 309(%rsp)
	movb	$0, 308(%rsp)
	movb	$0, 307(%rsp)
	movb	$0, 306(%rsp)
	movb	$0, 305(%rsp)
	movb	$0, 304(%rsp)
	movb	$0, 303(%rsp)
	movb	$0, 302(%rsp)
	movb	$0, 301(%rsp)
	movb	$0, 300(%rsp)
	movb	$0, 299(%rsp)
	movb	$0, 298(%rsp)
	movb	$0, 297(%rsp)
	movb	$0, 296(%rsp)
	movb	$0, 295(%rsp)
	movb	$0, 294(%rsp)
	movb	$0, 293(%rsp)
	movb	$0, 292(%rsp)
	movb	$0, 291(%rsp)
	movb	$0, 290(%rsp)
	movb	$0, 289(%rsp)
	movb	$0, 288(%rsp)
	movb	$0, 287(%rsp)
	movb	$0, 286(%rsp)
	movb	$0, 285(%rsp)
	movb	$0, 284(%rsp)
	movb	$0, 283(%rsp)
	movb	$0, 282(%rsp)
	movb	$0, 281(%rsp)
	movb	$0, 280(%rsp)
	movb	$0, 279(%rsp)
	movb	$0, 278(%rsp)
	movb	$0, 277(%rsp)
	movb	$0, 276(%rsp)
	movb	$0, 275(%rsp)
	movb	$0, 274(%rsp)
	movb	$0, 273(%rsp)
	movb	$0, 272(%rsp)
	movb	$0, 271(%rsp)
	movb	$0, 270(%rsp)
	movb	$0, 269(%rsp)
	movb	$0, 268(%rsp)
	movb	$0, 267(%rsp)
	movb	$0, 266(%rsp)
	movb	$0, 265(%rsp)
	movb	$0, 264(%rsp)
	movb	$0, 263(%rsp)
	movb	$0, 262(%rsp)
	movb	$0, 261(%rsp)
	movb	$0, 260(%rsp)
	movb	$0, 259(%rsp)
	movb	$0, 258(%rsp)
	movb	$0, 257(%rsp)
	movb	$0, 256(%rsp)
	movb	$0, 255(%rsp)
	movb	$0, 254(%rsp)
	movb	$0, 253(%rsp)
	movb	$0, 252(%rsp)
	movb	$0, 251(%rsp)
	movb	$0, 250(%rsp)
	movb	$0, 249(%rsp)
	movb	$0, 248(%rsp)
	movb	$0, 247(%rsp)
	movb	$0, 246(%rsp)
	movb	$0, 245(%rsp)
	movb	$0, 244(%rsp)
	movb	$0, 243(%rsp)
	movb	$0, 242(%rsp)
	movb	$0, 241(%rsp)
	movb	$0, 240(%rsp)
	movb	$0, 239(%rsp)
	movb	$0, 238(%rsp)
	movb	$0, 237(%rsp)
	movb	$0, 236(%rsp)
	movb	$0, 235(%rsp)
	movb	$0, 234(%rsp)
	movb	$0, 233(%rsp)
	movb	$0, 232(%rsp)
	movb	$0, 231(%rsp)
	movb	$0, 230(%rsp)
	movb	$0, 229(%rsp)
	movb	$0, 228(%rsp)
	movb	$0, 227(%rsp)
	movb	$0, 226(%rsp)
	movb	$0, 225(%rsp)
	movb	$0, 224(%rsp)
	movb	$0, 223(%rsp)
	movb	$0, 222(%rsp)
	movb	$0, 221(%rsp)
	movb	$0, 220(%rsp)
	movb	$0, 219(%rsp)
	movb	$0, 218(%rsp)
	movb	$0, 217(%rsp)
	movb	$0, 216(%rsp)
	movb	$0, 215(%rsp)
	movb	$0, 214(%rsp)
	movb	$0, 213(%rsp)
	movb	$0, 212(%rsp)
	movb	$0, 211(%rsp)
	movb	$0, 210(%rsp)
	movb	$0, 209(%rsp)
	movb	$0, 208(%rsp)
	movb	$0, 207(%rsp)
	movb	$0, 206(%rsp)
	movb	$0, 205(%rsp)
	movb	$0, 204(%rsp)
	movb	$0, 203(%rsp)
	movb	$0, 202(%rsp)
	movb	$0, 201(%rsp)
	movb	$0, 200(%rsp)
	movb	$0, 199(%rsp)
	movb	$0, 198(%rsp)
	movb	$0, 197(%rsp)
	movb	$0, 196(%rsp)
	movb	$0, 195(%rsp)
	movb	$0, 194(%rsp)
	movb	$0, 193(%rsp)
	movb	$0, 192(%rsp)
	movb	$0, 191(%rsp)
	movb	$0, 190(%rsp)
	movb	$0, 189(%rsp)
	movb	$0, 188(%rsp)
	movb	$0, 187(%rsp)
	movb	$0, 186(%rsp)
	movb	$0, 185(%rsp)
	movb	$0, 184(%rsp)
	movb	$0, 183(%rsp)
	movb	$0, 182(%rsp)
	movb	$0, 181(%rsp)
	movb	$0, 180(%rsp)
	movb	$0, 179(%rsp)
	movb	$0, 178(%rsp)
	movb	$0, 177(%rsp)
	movb	$0, 176(%rsp)
	movb	$0, 175(%rsp)
	movb	$0, 174(%rsp)
	movb	$0, 173(%rsp)
	movb	$0, 172(%rsp)
	movb	$0, 171(%rsp)
	movb	$0, 170(%rsp)
	movb	$0, 169(%rsp)
	movb	$0, 168(%rsp)
	movb	$0, 167(%rsp)
	movb	$0, 166(%rsp)
	movb	$0, 165(%rsp)
	movb	$0, 164(%rsp)
	movb	$0, 163(%rsp)
	movb	$0, 162(%rsp)
	movb	$0, 161(%rsp)
	movb	$0, 160(%rsp)
	movb	$0, 159(%rsp)
	movb	$0, 158(%rsp)
	movb	$0, 157(%rsp)
	movb	$0, 156(%rsp)
	movb	$0, 155(%rsp)
	movb	$0, 154(%rsp)
	movb	$0, 153(%rsp)
	movb	$0, 152(%rsp)
	movb	$0, 151(%rsp)
	movb	$0, 150(%rsp)
	movb	$0, 149(%rsp)
	movb	$0, 148(%rsp)
	movb	$0, 147(%rsp)
	movb	$0, 146(%rsp)
	movb	$0, 145(%rsp)
	movb	$0, 144(%rsp)
	movb	$0, 143(%rsp)
	movb	$0, 142(%rsp)
	movb	$0, 141(%rsp)
	movb	$0, 140(%rsp)
	movb	$0, 139(%rsp)
	movb	$0, 138(%rsp)
	movb	$0, 137(%rsp)
	movb	$0, 136(%rsp)
	movb	$0, 135(%rsp)
	movb	$0, 134(%rsp)
	movb	$0, 133(%rsp)
	movb	$0, 132(%rsp)
	movb	$0, 131(%rsp)
	movb	$0, 130(%rsp)
	movb	$0, 129(%rsp)
	movb	$0, 128(%rsp)
	movb	$0, 127(%rsp)
	movb	$0, 126(%rsp)
	movb	$0, 125(%rsp)
	movb	$0, 124(%rsp)
	movb	$0, 123(%rsp)
	movb	$0, 122(%rsp)
	movb	$0, 121(%rsp)
	movb	$0, 120(%rsp)
	movb	$0, 119(%rsp)
	movb	$0, 118(%rsp)
	movb	$0, 117(%rsp)
	movb	$0, 116(%rsp)
	movb	$0, 115(%rsp)
	movb	$0, 114(%rsp)
	movb	$0, 113(%rsp)
	movb	$0, 112(%rsp)
	movb	$0, 111(%rsp)
	movb	$0, 110(%rsp)
	movb	$0, 109(%rsp)
	movb	$0, 108(%rsp)
	movb	$0, 107(%rsp)
	movb	$0, 106(%rsp)
	movb	$0, 105(%rsp)
	movb	$0, 104(%rsp)
	movb	$0, 103(%rsp)
	movb	$0, 102(%rsp)
	movb	$0, 101(%rsp)
	movb	$0, 100(%rsp)
	movb	$0, 99(%rsp)
	movb	$0, 98(%rsp)
	movb	$0, 97(%rsp)
	movb	$0, 96(%rsp)
	movb	$0, 95(%rsp)
	movb	$0, 94(%rsp)
	movb	$0, 93(%rsp)
	movb	$0, 92(%rsp)
	movb	$0, 91(%rsp)
	movb	$0, 90(%rsp)
	movb	$0, 89(%rsp)
	movb	$0, 88(%rsp)
	movb	$0, 87(%rsp)
	movb	$0, 86(%rsp)
	movb	$0, 85(%rsp)
	movb	$0, 84(%rsp)
	movb	$0, 83(%rsp)
	movb	$0, 82(%rsp)
	movb	$0, 81(%rsp)
	movb	$0, 80(%rsp)
	movb	$0, 79(%rsp)
	movb	$0, 78(%rsp)
	movb	$0, 77(%rsp)
	movb	$0, 76(%rsp)
	movb	$0, 75(%rsp)
	movb	$0, 74(%rsp)
	movb	$0, 73(%rsp)
	movb	$0, 72(%rsp)
	movb	$0, 71(%rsp)
	movb	$0, 70(%rsp)
	movb	$0, 69(%rsp)
	movb	$0, 68(%rsp)
	movb	$0, 67(%rsp)
	movb	$0, 66(%rsp)
	movb	$0, 65(%rsp)
	movb	$0, 64(%rsp)
	movb	$0, 63(%rsp)
	movb	$0, 62(%rsp)
	movb	$0, 61(%rsp)
	movb	$0, 60(%rsp)
	movb	$0, 59(%rsp)
	movb	$0, 58(%rsp)
	movb	$0, 57(%rsp)
	movb	$0, 56(%rsp)
	movb	$0, 55(%rsp)
	movb	$0, 54(%rsp)
	movb	$0, 53(%rsp)
	movb	$0, 52(%rsp)
	movb	$0, 51(%rsp)
	movb	$0, 50(%rsp)
	movb	$0, 49(%rsp)
	movb	$0, 48(%rsp)
	movb	$0, 47(%rsp)
	movb	$0, 46(%rsp)
	movb	$0, 45(%rsp)
	movb	$0, 44(%rsp)
	movb	$0, 43(%rsp)
	movb	$0, 42(%rsp)
	movb	$0, 41(%rsp)
	movb	$0, 40(%rsp)
	movb	$0, 39(%rsp)
	movb	$0, 38(%rsp)
	movb	$0, 37(%rsp)
	movb	$0, 36(%rsp)
	movb	$0, 35(%rsp)
	movb	$0, 34(%rsp)
	movb	$0, 33(%rsp)
	movb	$0, 32(%rsp)
	movb	$0, 31(%rsp)
	movb	$0, 30(%rsp)
	movb	$0, 29(%rsp)
	movb	$0, 28(%rsp)
	movb	$0, 27(%rsp)
	movb	$0, 26(%rsp)
	movb	$0, 25(%rsp)
	movb	$0, 24(%rsp)
	movb	$0, 23(%rsp)
	movb	$0, 22(%rsp)
	movb	$0, 21(%rsp)
	movb	$0, 20(%rsp)
	movb	$0, 19(%rsp)
	movb	$0, 18(%rsp)
	movb	$0, 17(%rsp)
	movb	$0, 16(%rsp)
	movb	$0, 15(%rsp)
	movb	$0, 14(%rsp)
	movb	$0, 13(%rsp)
	movb	$0, 12(%rsp)
	movb	$0, 11(%rsp)
	movb	$0, 10(%rsp)
	movb	$0, 9(%rsp)
	movb	$0, 8(%rsp)
	movb	$0, 7(%rsp)
	movb	$0, 6(%rsp)
	movb	$0, 5(%rsp)
	movb	$0, 4(%rsp)
	movb	$0, 3(%rsp)
	movb	$0, 2(%rsp)
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
_wots_checksum_jazz:
wots_checksum_jazz:
	movq	%rsp, %r11
	leaq	-2(%rsp), %rsp
	andq	$-1, %rsp
	movq	$0, %rax
	movq	$0, %rcx
	jmp 	Lwots_checksum_jazz$4
Lwots_checksum_jazz$5:
	movq	$15, %rdx
	movl	(%rsi,%rcx,4), %r8d
	subq	%r8, %rdx
	addq	%rdx, %rax
	incq	%rcx
Lwots_checksum_jazz$4:
	cmpq	$64, %rcx
	jb  	Lwots_checksum_jazz$5
	movq	$8, %rcx
	addq	$-4, %rcx
	shlq	%cl, %rax
	movq	%rsp, %rdx
	movb	%al, 1(%rdx)
	shrq	$8, %rax
	movb	%al, (%rdx)
	movq	$0, %rax
	movq	$0, %rsi
	movq	$0, %rcx
	movb	$0, %r8b
	movb	$0, %r9b
	jmp 	Lwots_checksum_jazz$1
Lwots_checksum_jazz$2:
	cmpq	$0, %rcx
	jne 	Lwots_checksum_jazz$3
	movb	(%rdx,%rax), %r9b
	incq	%rax
	addq	$8, %rcx
Lwots_checksum_jazz$3:
	addq	$-4, %rcx
	movzbl	%r9b, %r10d
	shrl	%cl, %r10d
	andl	$15, %r10d
	movl	%r10d, (%rdi,%rsi,4)
	incq	%rsi
	incb	%r8b
Lwots_checksum_jazz$1:
	cmpb	$3, %r8b
	jb  	Lwots_checksum_jazz$2
	movq	%r11, %rsp
	movq	%rsp, %rsi
	andq	$-1, %rsp
	subq	$2, %rsp
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
_expand_seed_jazz:
expand_seed_jazz:
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
	movq	%rcx, %rax
	leaq	-88(%rsp), %rsp
	call	L_expand_seed$1
Lexpand_seed_jazz$1:
	leaq	88(%rsp), %rsp
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	movq	%rsp, %rsi
	andq	$-8, %rsp
	subq	$760, %rsp
	movb	$0, 759(%rsp)
	movb	$0, 758(%rsp)
	movb	$0, 757(%rsp)
	movb	$0, 756(%rsp)
	movb	$0, 755(%rsp)
	movb	$0, 754(%rsp)
	movb	$0, 753(%rsp)
	movb	$0, 752(%rsp)
	movb	$0, 751(%rsp)
	movb	$0, 750(%rsp)
	movb	$0, 749(%rsp)
	movb	$0, 748(%rsp)
	movb	$0, 747(%rsp)
	movb	$0, 746(%rsp)
	movb	$0, 745(%rsp)
	movb	$0, 744(%rsp)
	movb	$0, 743(%rsp)
	movb	$0, 742(%rsp)
	movb	$0, 741(%rsp)
	movb	$0, 740(%rsp)
	movb	$0, 739(%rsp)
	movb	$0, 738(%rsp)
	movb	$0, 737(%rsp)
	movb	$0, 736(%rsp)
	movb	$0, 735(%rsp)
	movb	$0, 734(%rsp)
	movb	$0, 733(%rsp)
	movb	$0, 732(%rsp)
	movb	$0, 731(%rsp)
	movb	$0, 730(%rsp)
	movb	$0, 729(%rsp)
	movb	$0, 728(%rsp)
	movb	$0, 727(%rsp)
	movb	$0, 726(%rsp)
	movb	$0, 725(%rsp)
	movb	$0, 724(%rsp)
	movb	$0, 723(%rsp)
	movb	$0, 722(%rsp)
	movb	$0, 721(%rsp)
	movb	$0, 720(%rsp)
	movb	$0, 719(%rsp)
	movb	$0, 718(%rsp)
	movb	$0, 717(%rsp)
	movb	$0, 716(%rsp)
	movb	$0, 715(%rsp)
	movb	$0, 714(%rsp)
	movb	$0, 713(%rsp)
	movb	$0, 712(%rsp)
	movb	$0, 711(%rsp)
	movb	$0, 710(%rsp)
	movb	$0, 709(%rsp)
	movb	$0, 708(%rsp)
	movb	$0, 707(%rsp)
	movb	$0, 706(%rsp)
	movb	$0, 705(%rsp)
	movb	$0, 704(%rsp)
	movb	$0, 703(%rsp)
	movb	$0, 702(%rsp)
	movb	$0, 701(%rsp)
	movb	$0, 700(%rsp)
	movb	$0, 699(%rsp)
	movb	$0, 698(%rsp)
	movb	$0, 697(%rsp)
	movb	$0, 696(%rsp)
	movb	$0, 695(%rsp)
	movb	$0, 694(%rsp)
	movb	$0, 693(%rsp)
	movb	$0, 692(%rsp)
	movb	$0, 691(%rsp)
	movb	$0, 690(%rsp)
	movb	$0, 689(%rsp)
	movb	$0, 688(%rsp)
	movb	$0, 687(%rsp)
	movb	$0, 686(%rsp)
	movb	$0, 685(%rsp)
	movb	$0, 684(%rsp)
	movb	$0, 683(%rsp)
	movb	$0, 682(%rsp)
	movb	$0, 681(%rsp)
	movb	$0, 680(%rsp)
	movb	$0, 679(%rsp)
	movb	$0, 678(%rsp)
	movb	$0, 677(%rsp)
	movb	$0, 676(%rsp)
	movb	$0, 675(%rsp)
	movb	$0, 674(%rsp)
	movb	$0, 673(%rsp)
	movb	$0, 672(%rsp)
	movb	$0, 671(%rsp)
	movb	$0, 670(%rsp)
	movb	$0, 669(%rsp)
	movb	$0, 668(%rsp)
	movb	$0, 667(%rsp)
	movb	$0, 666(%rsp)
	movb	$0, 665(%rsp)
	movb	$0, 664(%rsp)
	movb	$0, 663(%rsp)
	movb	$0, 662(%rsp)
	movb	$0, 661(%rsp)
	movb	$0, 660(%rsp)
	movb	$0, 659(%rsp)
	movb	$0, 658(%rsp)
	movb	$0, 657(%rsp)
	movb	$0, 656(%rsp)
	movb	$0, 655(%rsp)
	movb	$0, 654(%rsp)
	movb	$0, 653(%rsp)
	movb	$0, 652(%rsp)
	movb	$0, 651(%rsp)
	movb	$0, 650(%rsp)
	movb	$0, 649(%rsp)
	movb	$0, 648(%rsp)
	movb	$0, 647(%rsp)
	movb	$0, 646(%rsp)
	movb	$0, 645(%rsp)
	movb	$0, 644(%rsp)
	movb	$0, 643(%rsp)
	movb	$0, 642(%rsp)
	movb	$0, 641(%rsp)
	movb	$0, 640(%rsp)
	movb	$0, 639(%rsp)
	movb	$0, 638(%rsp)
	movb	$0, 637(%rsp)
	movb	$0, 636(%rsp)
	movb	$0, 635(%rsp)
	movb	$0, 634(%rsp)
	movb	$0, 633(%rsp)
	movb	$0, 632(%rsp)
	movb	$0, 631(%rsp)
	movb	$0, 630(%rsp)
	movb	$0, 629(%rsp)
	movb	$0, 628(%rsp)
	movb	$0, 627(%rsp)
	movb	$0, 626(%rsp)
	movb	$0, 625(%rsp)
	movb	$0, 624(%rsp)
	movb	$0, 623(%rsp)
	movb	$0, 622(%rsp)
	movb	$0, 621(%rsp)
	movb	$0, 620(%rsp)
	movb	$0, 619(%rsp)
	movb	$0, 618(%rsp)
	movb	$0, 617(%rsp)
	movb	$0, 616(%rsp)
	movb	$0, 615(%rsp)
	movb	$0, 614(%rsp)
	movb	$0, 613(%rsp)
	movb	$0, 612(%rsp)
	movb	$0, 611(%rsp)
	movb	$0, 610(%rsp)
	movb	$0, 609(%rsp)
	movb	$0, 608(%rsp)
	movb	$0, 607(%rsp)
	movb	$0, 606(%rsp)
	movb	$0, 605(%rsp)
	movb	$0, 604(%rsp)
	movb	$0, 603(%rsp)
	movb	$0, 602(%rsp)
	movb	$0, 601(%rsp)
	movb	$0, 600(%rsp)
	movb	$0, 599(%rsp)
	movb	$0, 598(%rsp)
	movb	$0, 597(%rsp)
	movb	$0, 596(%rsp)
	movb	$0, 595(%rsp)
	movb	$0, 594(%rsp)
	movb	$0, 593(%rsp)
	movb	$0, 592(%rsp)
	movb	$0, 591(%rsp)
	movb	$0, 590(%rsp)
	movb	$0, 589(%rsp)
	movb	$0, 588(%rsp)
	movb	$0, 587(%rsp)
	movb	$0, 586(%rsp)
	movb	$0, 585(%rsp)
	movb	$0, 584(%rsp)
	movb	$0, 583(%rsp)
	movb	$0, 582(%rsp)
	movb	$0, 581(%rsp)
	movb	$0, 580(%rsp)
	movb	$0, 579(%rsp)
	movb	$0, 578(%rsp)
	movb	$0, 577(%rsp)
	movb	$0, 576(%rsp)
	movb	$0, 575(%rsp)
	movb	$0, 574(%rsp)
	movb	$0, 573(%rsp)
	movb	$0, 572(%rsp)
	movb	$0, 571(%rsp)
	movb	$0, 570(%rsp)
	movb	$0, 569(%rsp)
	movb	$0, 568(%rsp)
	movb	$0, 567(%rsp)
	movb	$0, 566(%rsp)
	movb	$0, 565(%rsp)
	movb	$0, 564(%rsp)
	movb	$0, 563(%rsp)
	movb	$0, 562(%rsp)
	movb	$0, 561(%rsp)
	movb	$0, 560(%rsp)
	movb	$0, 559(%rsp)
	movb	$0, 558(%rsp)
	movb	$0, 557(%rsp)
	movb	$0, 556(%rsp)
	movb	$0, 555(%rsp)
	movb	$0, 554(%rsp)
	movb	$0, 553(%rsp)
	movb	$0, 552(%rsp)
	movb	$0, 551(%rsp)
	movb	$0, 550(%rsp)
	movb	$0, 549(%rsp)
	movb	$0, 548(%rsp)
	movb	$0, 547(%rsp)
	movb	$0, 546(%rsp)
	movb	$0, 545(%rsp)
	movb	$0, 544(%rsp)
	movb	$0, 543(%rsp)
	movb	$0, 542(%rsp)
	movb	$0, 541(%rsp)
	movb	$0, 540(%rsp)
	movb	$0, 539(%rsp)
	movb	$0, 538(%rsp)
	movb	$0, 537(%rsp)
	movb	$0, 536(%rsp)
	movb	$0, 535(%rsp)
	movb	$0, 534(%rsp)
	movb	$0, 533(%rsp)
	movb	$0, 532(%rsp)
	movb	$0, 531(%rsp)
	movb	$0, 530(%rsp)
	movb	$0, 529(%rsp)
	movb	$0, 528(%rsp)
	movb	$0, 527(%rsp)
	movb	$0, 526(%rsp)
	movb	$0, 525(%rsp)
	movb	$0, 524(%rsp)
	movb	$0, 523(%rsp)
	movb	$0, 522(%rsp)
	movb	$0, 521(%rsp)
	movb	$0, 520(%rsp)
	movb	$0, 519(%rsp)
	movb	$0, 518(%rsp)
	movb	$0, 517(%rsp)
	movb	$0, 516(%rsp)
	movb	$0, 515(%rsp)
	movb	$0, 514(%rsp)
	movb	$0, 513(%rsp)
	movb	$0, 512(%rsp)
	movb	$0, 511(%rsp)
	movb	$0, 510(%rsp)
	movb	$0, 509(%rsp)
	movb	$0, 508(%rsp)
	movb	$0, 507(%rsp)
	movb	$0, 506(%rsp)
	movb	$0, 505(%rsp)
	movb	$0, 504(%rsp)
	movb	$0, 503(%rsp)
	movb	$0, 502(%rsp)
	movb	$0, 501(%rsp)
	movb	$0, 500(%rsp)
	movb	$0, 499(%rsp)
	movb	$0, 498(%rsp)
	movb	$0, 497(%rsp)
	movb	$0, 496(%rsp)
	movb	$0, 495(%rsp)
	movb	$0, 494(%rsp)
	movb	$0, 493(%rsp)
	movb	$0, 492(%rsp)
	movb	$0, 491(%rsp)
	movb	$0, 490(%rsp)
	movb	$0, 489(%rsp)
	movb	$0, 488(%rsp)
	movb	$0, 487(%rsp)
	movb	$0, 486(%rsp)
	movb	$0, 485(%rsp)
	movb	$0, 484(%rsp)
	movb	$0, 483(%rsp)
	movb	$0, 482(%rsp)
	movb	$0, 481(%rsp)
	movb	$0, 480(%rsp)
	movb	$0, 479(%rsp)
	movb	$0, 478(%rsp)
	movb	$0, 477(%rsp)
	movb	$0, 476(%rsp)
	movb	$0, 475(%rsp)
	movb	$0, 474(%rsp)
	movb	$0, 473(%rsp)
	movb	$0, 472(%rsp)
	movb	$0, 471(%rsp)
	movb	$0, 470(%rsp)
	movb	$0, 469(%rsp)
	movb	$0, 468(%rsp)
	movb	$0, 467(%rsp)
	movb	$0, 466(%rsp)
	movb	$0, 465(%rsp)
	movb	$0, 464(%rsp)
	movb	$0, 463(%rsp)
	movb	$0, 462(%rsp)
	movb	$0, 461(%rsp)
	movb	$0, 460(%rsp)
	movb	$0, 459(%rsp)
	movb	$0, 458(%rsp)
	movb	$0, 457(%rsp)
	movb	$0, 456(%rsp)
	movb	$0, 455(%rsp)
	movb	$0, 454(%rsp)
	movb	$0, 453(%rsp)
	movb	$0, 452(%rsp)
	movb	$0, 451(%rsp)
	movb	$0, 450(%rsp)
	movb	$0, 449(%rsp)
	movb	$0, 448(%rsp)
	movb	$0, 447(%rsp)
	movb	$0, 446(%rsp)
	movb	$0, 445(%rsp)
	movb	$0, 444(%rsp)
	movb	$0, 443(%rsp)
	movb	$0, 442(%rsp)
	movb	$0, 441(%rsp)
	movb	$0, 440(%rsp)
	movb	$0, 439(%rsp)
	movb	$0, 438(%rsp)
	movb	$0, 437(%rsp)
	movb	$0, 436(%rsp)
	movb	$0, 435(%rsp)
	movb	$0, 434(%rsp)
	movb	$0, 433(%rsp)
	movb	$0, 432(%rsp)
	movb	$0, 431(%rsp)
	movb	$0, 430(%rsp)
	movb	$0, 429(%rsp)
	movb	$0, 428(%rsp)
	movb	$0, 427(%rsp)
	movb	$0, 426(%rsp)
	movb	$0, 425(%rsp)
	movb	$0, 424(%rsp)
	movb	$0, 423(%rsp)
	movb	$0, 422(%rsp)
	movb	$0, 421(%rsp)
	movb	$0, 420(%rsp)
	movb	$0, 419(%rsp)
	movb	$0, 418(%rsp)
	movb	$0, 417(%rsp)
	movb	$0, 416(%rsp)
	movb	$0, 415(%rsp)
	movb	$0, 414(%rsp)
	movb	$0, 413(%rsp)
	movb	$0, 412(%rsp)
	movb	$0, 411(%rsp)
	movb	$0, 410(%rsp)
	movb	$0, 409(%rsp)
	movb	$0, 408(%rsp)
	movb	$0, 407(%rsp)
	movb	$0, 406(%rsp)
	movb	$0, 405(%rsp)
	movb	$0, 404(%rsp)
	movb	$0, 403(%rsp)
	movb	$0, 402(%rsp)
	movb	$0, 401(%rsp)
	movb	$0, 400(%rsp)
	movb	$0, 399(%rsp)
	movb	$0, 398(%rsp)
	movb	$0, 397(%rsp)
	movb	$0, 396(%rsp)
	movb	$0, 395(%rsp)
	movb	$0, 394(%rsp)
	movb	$0, 393(%rsp)
	movb	$0, 392(%rsp)
	movb	$0, 391(%rsp)
	movb	$0, 390(%rsp)
	movb	$0, 389(%rsp)
	movb	$0, 388(%rsp)
	movb	$0, 387(%rsp)
	movb	$0, 386(%rsp)
	movb	$0, 385(%rsp)
	movb	$0, 384(%rsp)
	movb	$0, 383(%rsp)
	movb	$0, 382(%rsp)
	movb	$0, 381(%rsp)
	movb	$0, 380(%rsp)
	movb	$0, 379(%rsp)
	movb	$0, 378(%rsp)
	movb	$0, 377(%rsp)
	movb	$0, 376(%rsp)
	movb	$0, 375(%rsp)
	movb	$0, 374(%rsp)
	movb	$0, 373(%rsp)
	movb	$0, 372(%rsp)
	movb	$0, 371(%rsp)
	movb	$0, 370(%rsp)
	movb	$0, 369(%rsp)
	movb	$0, 368(%rsp)
	movb	$0, 367(%rsp)
	movb	$0, 366(%rsp)
	movb	$0, 365(%rsp)
	movb	$0, 364(%rsp)
	movb	$0, 363(%rsp)
	movb	$0, 362(%rsp)
	movb	$0, 361(%rsp)
	movb	$0, 360(%rsp)
	movb	$0, 359(%rsp)
	movb	$0, 358(%rsp)
	movb	$0, 357(%rsp)
	movb	$0, 356(%rsp)
	movb	$0, 355(%rsp)
	movb	$0, 354(%rsp)
	movb	$0, 353(%rsp)
	movb	$0, 352(%rsp)
	movb	$0, 351(%rsp)
	movb	$0, 350(%rsp)
	movb	$0, 349(%rsp)
	movb	$0, 348(%rsp)
	movb	$0, 347(%rsp)
	movb	$0, 346(%rsp)
	movb	$0, 345(%rsp)
	movb	$0, 344(%rsp)
	movb	$0, 343(%rsp)
	movb	$0, 342(%rsp)
	movb	$0, 341(%rsp)
	movb	$0, 340(%rsp)
	movb	$0, 339(%rsp)
	movb	$0, 338(%rsp)
	movb	$0, 337(%rsp)
	movb	$0, 336(%rsp)
	movb	$0, 335(%rsp)
	movb	$0, 334(%rsp)
	movb	$0, 333(%rsp)
	movb	$0, 332(%rsp)
	movb	$0, 331(%rsp)
	movb	$0, 330(%rsp)
	movb	$0, 329(%rsp)
	movb	$0, 328(%rsp)
	movb	$0, 327(%rsp)
	movb	$0, 326(%rsp)
	movb	$0, 325(%rsp)
	movb	$0, 324(%rsp)
	movb	$0, 323(%rsp)
	movb	$0, 322(%rsp)
	movb	$0, 321(%rsp)
	movb	$0, 320(%rsp)
	movb	$0, 319(%rsp)
	movb	$0, 318(%rsp)
	movb	$0, 317(%rsp)
	movb	$0, 316(%rsp)
	movb	$0, 315(%rsp)
	movb	$0, 314(%rsp)
	movb	$0, 313(%rsp)
	movb	$0, 312(%rsp)
	movb	$0, 311(%rsp)
	movb	$0, 310(%rsp)
	movb	$0, 309(%rsp)
	movb	$0, 308(%rsp)
	movb	$0, 307(%rsp)
	movb	$0, 306(%rsp)
	movb	$0, 305(%rsp)
	movb	$0, 304(%rsp)
	movb	$0, 303(%rsp)
	movb	$0, 302(%rsp)
	movb	$0, 301(%rsp)
	movb	$0, 300(%rsp)
	movb	$0, 299(%rsp)
	movb	$0, 298(%rsp)
	movb	$0, 297(%rsp)
	movb	$0, 296(%rsp)
	movb	$0, 295(%rsp)
	movb	$0, 294(%rsp)
	movb	$0, 293(%rsp)
	movb	$0, 292(%rsp)
	movb	$0, 291(%rsp)
	movb	$0, 290(%rsp)
	movb	$0, 289(%rsp)
	movb	$0, 288(%rsp)
	movb	$0, 287(%rsp)
	movb	$0, 286(%rsp)
	movb	$0, 285(%rsp)
	movb	$0, 284(%rsp)
	movb	$0, 283(%rsp)
	movb	$0, 282(%rsp)
	movb	$0, 281(%rsp)
	movb	$0, 280(%rsp)
	movb	$0, 279(%rsp)
	movb	$0, 278(%rsp)
	movb	$0, 277(%rsp)
	movb	$0, 276(%rsp)
	movb	$0, 275(%rsp)
	movb	$0, 274(%rsp)
	movb	$0, 273(%rsp)
	movb	$0, 272(%rsp)
	movb	$0, 271(%rsp)
	movb	$0, 270(%rsp)
	movb	$0, 269(%rsp)
	movb	$0, 268(%rsp)
	movb	$0, 267(%rsp)
	movb	$0, 266(%rsp)
	movb	$0, 265(%rsp)
	movb	$0, 264(%rsp)
	movb	$0, 263(%rsp)
	movb	$0, 262(%rsp)
	movb	$0, 261(%rsp)
	movb	$0, 260(%rsp)
	movb	$0, 259(%rsp)
	movb	$0, 258(%rsp)
	movb	$0, 257(%rsp)
	movb	$0, 256(%rsp)
	movb	$0, 255(%rsp)
	movb	$0, 254(%rsp)
	movb	$0, 253(%rsp)
	movb	$0, 252(%rsp)
	movb	$0, 251(%rsp)
	movb	$0, 250(%rsp)
	movb	$0, 249(%rsp)
	movb	$0, 248(%rsp)
	movb	$0, 247(%rsp)
	movb	$0, 246(%rsp)
	movb	$0, 245(%rsp)
	movb	$0, 244(%rsp)
	movb	$0, 243(%rsp)
	movb	$0, 242(%rsp)
	movb	$0, 241(%rsp)
	movb	$0, 240(%rsp)
	movb	$0, 239(%rsp)
	movb	$0, 238(%rsp)
	movb	$0, 237(%rsp)
	movb	$0, 236(%rsp)
	movb	$0, 235(%rsp)
	movb	$0, 234(%rsp)
	movb	$0, 233(%rsp)
	movb	$0, 232(%rsp)
	movb	$0, 231(%rsp)
	movb	$0, 230(%rsp)
	movb	$0, 229(%rsp)
	movb	$0, 228(%rsp)
	movb	$0, 227(%rsp)
	movb	$0, 226(%rsp)
	movb	$0, 225(%rsp)
	movb	$0, 224(%rsp)
	movb	$0, 223(%rsp)
	movb	$0, 222(%rsp)
	movb	$0, 221(%rsp)
	movb	$0, 220(%rsp)
	movb	$0, 219(%rsp)
	movb	$0, 218(%rsp)
	movb	$0, 217(%rsp)
	movb	$0, 216(%rsp)
	movb	$0, 215(%rsp)
	movb	$0, 214(%rsp)
	movb	$0, 213(%rsp)
	movb	$0, 212(%rsp)
	movb	$0, 211(%rsp)
	movb	$0, 210(%rsp)
	movb	$0, 209(%rsp)
	movb	$0, 208(%rsp)
	movb	$0, 207(%rsp)
	movb	$0, 206(%rsp)
	movb	$0, 205(%rsp)
	movb	$0, 204(%rsp)
	movb	$0, 203(%rsp)
	movb	$0, 202(%rsp)
	movb	$0, 201(%rsp)
	movb	$0, 200(%rsp)
	movb	$0, 199(%rsp)
	movb	$0, 198(%rsp)
	movb	$0, 197(%rsp)
	movb	$0, 196(%rsp)
	movb	$0, 195(%rsp)
	movb	$0, 194(%rsp)
	movb	$0, 193(%rsp)
	movb	$0, 192(%rsp)
	movb	$0, 191(%rsp)
	movb	$0, 190(%rsp)
	movb	$0, 189(%rsp)
	movb	$0, 188(%rsp)
	movb	$0, 187(%rsp)
	movb	$0, 186(%rsp)
	movb	$0, 185(%rsp)
	movb	$0, 184(%rsp)
	movb	$0, 183(%rsp)
	movb	$0, 182(%rsp)
	movb	$0, 181(%rsp)
	movb	$0, 180(%rsp)
	movb	$0, 179(%rsp)
	movb	$0, 178(%rsp)
	movb	$0, 177(%rsp)
	movb	$0, 176(%rsp)
	movb	$0, 175(%rsp)
	movb	$0, 174(%rsp)
	movb	$0, 173(%rsp)
	movb	$0, 172(%rsp)
	movb	$0, 171(%rsp)
	movb	$0, 170(%rsp)
	movb	$0, 169(%rsp)
	movb	$0, 168(%rsp)
	movb	$0, 167(%rsp)
	movb	$0, 166(%rsp)
	movb	$0, 165(%rsp)
	movb	$0, 164(%rsp)
	movb	$0, 163(%rsp)
	movb	$0, 162(%rsp)
	movb	$0, 161(%rsp)
	movb	$0, 160(%rsp)
	movb	$0, 159(%rsp)
	movb	$0, 158(%rsp)
	movb	$0, 157(%rsp)
	movb	$0, 156(%rsp)
	movb	$0, 155(%rsp)
	movb	$0, 154(%rsp)
	movb	$0, 153(%rsp)
	movb	$0, 152(%rsp)
	movb	$0, 151(%rsp)
	movb	$0, 150(%rsp)
	movb	$0, 149(%rsp)
	movb	$0, 148(%rsp)
	movb	$0, 147(%rsp)
	movb	$0, 146(%rsp)
	movb	$0, 145(%rsp)
	movb	$0, 144(%rsp)
	movb	$0, 143(%rsp)
	movb	$0, 142(%rsp)
	movb	$0, 141(%rsp)
	movb	$0, 140(%rsp)
	movb	$0, 139(%rsp)
	movb	$0, 138(%rsp)
	movb	$0, 137(%rsp)
	movb	$0, 136(%rsp)
	movb	$0, 135(%rsp)
	movb	$0, 134(%rsp)
	movb	$0, 133(%rsp)
	movb	$0, 132(%rsp)
	movb	$0, 131(%rsp)
	movb	$0, 130(%rsp)
	movb	$0, 129(%rsp)
	movb	$0, 128(%rsp)
	movb	$0, 127(%rsp)
	movb	$0, 126(%rsp)
	movb	$0, 125(%rsp)
	movb	$0, 124(%rsp)
	movb	$0, 123(%rsp)
	movb	$0, 122(%rsp)
	movb	$0, 121(%rsp)
	movb	$0, 120(%rsp)
	movb	$0, 119(%rsp)
	movb	$0, 118(%rsp)
	movb	$0, 117(%rsp)
	movb	$0, 116(%rsp)
	movb	$0, 115(%rsp)
	movb	$0, 114(%rsp)
	movb	$0, 113(%rsp)
	movb	$0, 112(%rsp)
	movb	$0, 111(%rsp)
	movb	$0, 110(%rsp)
	movb	$0, 109(%rsp)
	movb	$0, 108(%rsp)
	movb	$0, 107(%rsp)
	movb	$0, 106(%rsp)
	movb	$0, 105(%rsp)
	movb	$0, 104(%rsp)
	movb	$0, 103(%rsp)
	movb	$0, 102(%rsp)
	movb	$0, 101(%rsp)
	movb	$0, 100(%rsp)
	movb	$0, 99(%rsp)
	movb	$0, 98(%rsp)
	movb	$0, 97(%rsp)
	movb	$0, 96(%rsp)
	movb	$0, 95(%rsp)
	movb	$0, 94(%rsp)
	movb	$0, 93(%rsp)
	movb	$0, 92(%rsp)
	movb	$0, 91(%rsp)
	movb	$0, 90(%rsp)
	movb	$0, 89(%rsp)
	movb	$0, 88(%rsp)
	movb	$0, 87(%rsp)
	movb	$0, 86(%rsp)
	movb	$0, 85(%rsp)
	movb	$0, 84(%rsp)
	movb	$0, 83(%rsp)
	movb	$0, 82(%rsp)
	movb	$0, 81(%rsp)
	movb	$0, 80(%rsp)
	movb	$0, 79(%rsp)
	movb	$0, 78(%rsp)
	movb	$0, 77(%rsp)
	movb	$0, 76(%rsp)
	movb	$0, 75(%rsp)
	movb	$0, 74(%rsp)
	movb	$0, 73(%rsp)
	movb	$0, 72(%rsp)
	movb	$0, 71(%rsp)
	movb	$0, 70(%rsp)
	movb	$0, 69(%rsp)
	movb	$0, 68(%rsp)
	movb	$0, 67(%rsp)
	movb	$0, 66(%rsp)
	movb	$0, 65(%rsp)
	movb	$0, 64(%rsp)
	movb	$0, 63(%rsp)
	movb	$0, 62(%rsp)
	movb	$0, 61(%rsp)
	movb	$0, 60(%rsp)
	movb	$0, 59(%rsp)
	movb	$0, 58(%rsp)
	movb	$0, 57(%rsp)
	movb	$0, 56(%rsp)
	movb	$0, 55(%rsp)
	movb	$0, 54(%rsp)
	movb	$0, 53(%rsp)
	movb	$0, 52(%rsp)
	movb	$0, 51(%rsp)
	movb	$0, 50(%rsp)
	movb	$0, 49(%rsp)
	movb	$0, 48(%rsp)
	movb	$0, 47(%rsp)
	movb	$0, 46(%rsp)
	movb	$0, 45(%rsp)
	movb	$0, 44(%rsp)
	movb	$0, 43(%rsp)
	movb	$0, 42(%rsp)
	movb	$0, 41(%rsp)
	movb	$0, 40(%rsp)
	movb	$0, 39(%rsp)
	movb	$0, 38(%rsp)
	movb	$0, 37(%rsp)
	movb	$0, 36(%rsp)
	movb	$0, 35(%rsp)
	movb	$0, 34(%rsp)
	movb	$0, 33(%rsp)
	movb	$0, 32(%rsp)
	movb	$0, 31(%rsp)
	movb	$0, 30(%rsp)
	movb	$0, 29(%rsp)
	movb	$0, 28(%rsp)
	movb	$0, 27(%rsp)
	movb	$0, 26(%rsp)
	movb	$0, 25(%rsp)
	movb	$0, 24(%rsp)
	movb	$0, 23(%rsp)
	movb	$0, 22(%rsp)
	movb	$0, 21(%rsp)
	movb	$0, 20(%rsp)
	movb	$0, 19(%rsp)
	movb	$0, 18(%rsp)
	movb	$0, 17(%rsp)
	movb	$0, 16(%rsp)
	movb	$0, 15(%rsp)
	movb	$0, 14(%rsp)
	movb	$0, 13(%rsp)
	movb	$0, 12(%rsp)
	movb	$0, 11(%rsp)
	movb	$0, 10(%rsp)
	movb	$0, 9(%rsp)
	movb	$0, 8(%rsp)
	movb	$0, 7(%rsp)
	movb	$0, 6(%rsp)
	movb	$0, 5(%rsp)
	movb	$0, 4(%rsp)
	movb	$0, 3(%rsp)
	movb	$0, 2(%rsp)
	movb	$0, 1(%rsp)
	movb	$0, (%rsp)
	movq	%rsi, %rsp
	ret
L_chain_lengths$1:
	movq	%rdx, %r10
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
	movzbl	%r12b, %r14d
	shrl	%cl, %r14d
	andl	$15, %r14d
	movl	%r14d, (%r10,%rbx,4)
	incq	%rbx
	incb	%bpl
L_chain_lengths$7:
	cmpb	$64, %bpl
	jb  	L_chain_lengths$8
	leaq	256(%rdx), %r9
	movq	%rdx, %rcx
	movq	$0, %r11
	movq	$0, %r10
	jmp 	L_chain_lengths$5
L_chain_lengths$6:
	movq	$15, %rbx
	movl	(%rcx,%r10,4), %ebp
	subq	%rbp, %rbx
	addq	%rbx, %r11
	incq	%r10
L_chain_lengths$5:
	cmpq	$64, %r10
	jb  	L_chain_lengths$6
	movq	$8, %rcx
	addq	$-4, %rcx
	shlq	%cl, %r11
	leaq	8(%rsp), %r10
	movb	%r11b, 1(%r10)
	shrq	$8, %r11
	movb	%r11b, (%r10)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %rcx
	movb	$0, %bpl
	movb	$0, %r12b
	jmp 	L_chain_lengths$2
L_chain_lengths$3:
	cmpq	$0, %rcx
	jne 	L_chain_lengths$4
	movb	(%r10,%r11), %r12b
	incq	%r11
	addq	$8, %rcx
L_chain_lengths$4:
	addq	$-4, %rcx
	movzbl	%r12b, %r14d
	shrl	%cl, %r14d
	andl	$15, %r14d
	movl	%r14d, (%r9,%rbx,4)
	incq	%rbx
	incb	%bpl
L_chain_lengths$2:
	cmpb	$3, %bpl
	jb  	L_chain_lengths$3
	ret
L_gen_chain_inplace$1:
	movq	%rdx, 8(%rsp)
	movq	%r8, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movl	%eax, %esi
	addl	%ecx, %eax
	jmp 	L_gen_chain_inplace$2
L_gen_chain_inplace$3:
	movl	%esi, 32(%rsp)
	movl	%eax, 36(%rsp)
	movq	24(%rsp), %rdx
	movl	%esi, 24(%rdx)
	movl	$0, %eax
	movl	%eax, 28(%rdx)
	movq	16(%rsp), %rcx
	movq	8(%rsp), %rax
	leaq	-320(%rsp), %rsp
	call	L_thash_f$1
L_gen_chain_inplace$4:
	leaq	320(%rsp), %rsp
	movq	%rax, %rdx
	movl	32(%rsp), %esi
	movl	36(%rsp), %eax
	incl	%esi
L_gen_chain_inplace$2:
	cmpl	%eax, %esi
	jb  	L_gen_chain_inplace$3
	movq	24(%rsp), %rax
	ret
L_expand_seed$1:
	movq	%rdi, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movl	$0, %ecx
	movl	%ecx, 24(%rsi)
	movl	$0, %ecx
	movl	%ecx, 28(%rsi)
	leaq	32(%rsp), %rcx
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	16(%rsp), %rax
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
	movq	%rcx, %rax
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
	movq	24(%rsp), %rax
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
L_prf_keygen$1:
	leaq	32(%rsp), %rcx
	movq	$4, %rdx
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
	movl	4(%r9), %r15d
	movl	8(%r9), %edx
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
	andl	%r15d, %ebx
	movl	%r12d, %r14d
	andl	%edx, %r14d
	xorl	%r14d, %ebx
	movl	%r15d, %r14d
	andl	%edx, %r14d
	xorl	%r14d, %ebx
	addl	%ebx, %r11d
	movl	%r8d, %ebx
	movl	%edi, %r8d
	movl	%ebp, %edi
	movl	%esi, %ebp
	addl	%r10d, %ebp
	movl	%edx, %esi
	movl	%r15d, %edx
	movl	%r12d, %r15d
	movl	%r10d, %r12d
	addl	%r11d, %r12d
	incq	%r9
L_blocks_1_ref$4:
	cmpq	$64, %r9
	jb  	L_blocks_1_ref$5
	movq	24(%rsp), %r9
	addl	(%r9), %r12d
	addl	4(%r9), %r15d
	addl	8(%r9), %edx
	addl	12(%r9), %esi
	addl	16(%r9), %ebp
	addl	20(%r9), %edi
	addl	24(%r9), %r8d
	addl	28(%r9), %ebx
	movl	%r12d, (%r9)
	movl	%r15d, 4(%r9)
	movl	%edx, 8(%r9)
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
	movq	(%rax), %rdx
	movq	%rdx, (%rcx)
	movq	8(%rax), %rdx
	movq	%rdx, 8(%rcx)
	movq	16(%rax), %rdx
	movq	%rdx, 16(%rcx)
	movq	24(%rax), %rax
	movq	%rax, 24(%rcx)
	ret
L_memcpy_u8u8p$1:
	movq	(%rcx), %rdx
	movq	%rdx, (%rax)
	movq	8(%rcx), %rdx
	movq	%rdx, 8(%rax)
	movq	16(%rcx), %rdx
	movq	%rdx, 16(%rax)
	movq	24(%rcx), %rcx
	movq	%rcx, 24(%rax)
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
