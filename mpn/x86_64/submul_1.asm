dnl  AMD64 mpn_submul_1 -- Multiply a limb vector with a limb and subtract the
dnl  result from a second limb vector.

dnl  Copyright 2003, 2005 Free Software Foundation, Inc.

dnl  This file is part of the GNU MP Library.

dnl  The GNU MP Library is free software; you can redistribute it and/or modify
dnl  it under the terms of the GNU Lesser General Public License as published
dnl  by the Free Software Foundation; either version 2.1 of the License, or (at
dnl  your option) any later version.

dnl  The GNU MP Library is distributed in the hope that it will be useful, but
dnl  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
dnl  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
dnl  License for more details.

dnl  You should have received a copy of the GNU Lesser General Public License
dnl  along with the GNU MP Library; see the file COPYING.LIB.  If not, write to
dnl  the Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
dnl  MA 02111-1307, USA.

include(`../config.m4')


C		    cycles/limb
C Hammer:		3.5
C Prescott/Nocona:	21-23 (fluctuating due to w/c problems)


C INPUT PARAMETERS
C rp	rdi
C up	rsi
C n	rdx
C vl	rcx

	TEXT
	ALIGN(16)
	.byte	0,0,0			C				      3
ASM_START()
PROLOGUE(mpn_submul_1)
	pushq	%rbx			C				      1
	movq	%rdx, %rbx		C				      3
	xorl	%r8d, %r8d		C clear carry limb		      3
	subq	$4, %rbx		C				      4
	jb	.Lend			C				      2
.Loop:
	movq	(%rsi), %rax		C				      3
	mulq	%rcx			C				      3
	xorl	%r9d, %r9d		C				      3
	addq	%rax, %r8		C				      3
	adcq	%rdx, %r9		C				      3

	movq	8(%rsi), %rax		C				      4
	mulq	%rcx			C				      3
	xorl	%r10d, %r10d		C				      3
	addq	%rax, %r9		C				      3
	adcq	%rdx, %r10		C				      3

	movq	16(%rsi), %rax		C				      4
	mulq	%rcx			C				      3
	xorl	%r11d, %r11d		C				      3
	addq	%rax, %r10		C				      3
	adcq	%rdx, %r11		C				      3

	movq	24(%rsi), %rax		C				      4
	addq	$32, %rsi		C				      4
	mulq	%rcx			C				      3
	addq	%rax, %r11		C				      3
	adcq	$0, %rdx		C				      4

	subq	%r8, (%rdi)		C				      3
	sbbq	%r9, 8(%rdi)		C				      4
	sbbq	%r10, 16(%rdi)		C				      4
	sbbq	%r11, 24(%rdi)		C				      4

	movq	%rdx, %r8		C				      3
	adcq	$0,%r8			C				      4

	addq	$32, %rdi		C				      4
	subq	$4, %rbx		C				      4
	jae	.Loop			C				      2

	cmpl	$-4, %ebx		C				      3
	jne	.Lend			C				      2

	movq	%r8, %rax		C				      3
	popq	%rbx			C				      1
	ret				C				      1

.Lend:	movq	(%rsi), %rax		C				      3
	mulq	%rcx			C				      3
	xorl	%r9d, %r9d		C				      3
	addq	%rax, %r8		C				      3
	adcq	%rdx, %r9		C				      3

	cmpl	$-3, %ebx		C				      3
	jne	.L1			C				      2

	subq	%r8, (%rdi)		C				      3
	adcq	$0, %r9			C				      4
	movq	%r9, %rax		C				      3
	popq	%rbx			C				      1
	ret				C				      1

.L1:	movq	8(%rsi), %rax		C				      4
	mulq	%rcx			C				      3
	xorl	%r10d, %r10d		C				      3
	addq	%rax, %r9		C				      3
	adcq	%rdx, %r10		C				      3

	cmpl	$-2, %ebx		C				      3
	jne	.L2			C				      2

	subq	%r8, (%rdi)		C				      3
	sbbq	%r9, 8(%rdi)		C				      4
	adcq	$0, %r10		C				      4
	movq	%r10, %rax		C				      3
	popq	%rbx			C				      1
	ret				C				      1

.L2:	movq	16(%rsi), %rax		C				      4
	mulq	%rcx			C				      3
	xorl	%r11d, %r11d		C				      3
	addq	%rax, %r10		C				      3
	adcq	%rdx, %r11		C				      3

	subq	%r8, (%rdi)		C				      3
	sbbq	%r9, 8(%rdi)		C				      4
	sbbq	%r10, 16(%rdi)		C				      4
	adcq	$0, %r11		C				      4
	movq	%r11, %rax		C				      3
	popq	%rbx			C				      1
	ret				C				      1
EPILOGUE()
