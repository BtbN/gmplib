dnl  AMD64 mpn_rsh1sub_n -- rp[] = (up[] - vp[]) >> 1

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
dnl  along with the GNU MP Library; see the file COPYING.LIB.  If not, write
dnl  to the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
dnl  Boston, MA 02110-1301, USA.

include(`../config.m4')


C	    cycles/limb
C K8:		2.14	(mpn_add_n + mpn_rshift need 4.125)
C P4:		13
C P6-15:	3.8

C TODO
C  * Rewrite to use indexed addressing, like addlsh1.asm and sublsh1.asm.
C  * Try to approach the cache bandwidth 1.5 c/l.  It should be possible.

C INPUT PARAMETERS
define(`rp',`%rdi')
define(`up',`%rsi')
define(`vp',`%rdx')
define(`n',`%rcx')
define(`n32',`%ecx')

ASM_START()
	TEXT
	ALIGN(16)
	.byte	0,0,0,0,0,0,0,0
PROLOGUE(mpn_rsh1sub_n)
	pushq	%rbx			C				1

	xorl	%eax, %eax
	movq	(up), %rbx
	subq	(vp), %rbx

	rcrq	%rbx			C rotate, save acy
	adcl	%eax, %eax		C return value

	movl	n32, %r11d
	andl	$3, %r11d

	cmpl	$1, %r11d
	je	.Ldo			C jump if n = 1 5 9 ...

.Ln1:	cmpl	$2, %r11d
	jne	.Ln2			C jump unless n = 2 6 10 ...
	addq	%rbx, %rbx		C rotate carry limb, restore acy
	movq	8(up), %r10
	sbbq	8(vp), %r10
	leaq	8(up), up
	leaq	8(vp), vp
	leaq	8(rp), rp
	rcrq	%r10
	rcrq	%rbx
	movq	%rbx, -8(rp)
	jmp	.Lcj1

.Ln2:	cmpl	$3, %r11d
	jne	.Ln3			C jump unless n = 3 7 11 ...
	addq	%rbx, %rbx		C rotate carry limb, restore acy
	movq	8(up), %r9
	movq	16(up), %r10
	sbbq	8(vp), %r9
	sbbq	16(vp), %r10
	leaq	16(up), up
	leaq	16(vp), vp
	leaq	16(rp), rp
	rcrq	%r10
	rcrq	%r9
	rcrq	%rbx
	movq	%rbx, -16(rp)
	jmp	.Lcj2

.Ln3:	decq	n			C come here for n = 4 8 12 ...
	addq	%rbx, %rbx		C rotate carry limb, restore acy
	movq	8(up), %r8
	movq	16(up), %r9
	sbbq	8(vp), %r8
	sbbq	16(vp), %r9
	movq	24(up), %r10
	sbbq	24(vp), %r10
	leaq	24(up), up
	leaq	24(vp), vp
	leaq	24(rp), rp
	rcrq	%r10
	rcrq	%r9
	rcrq	%r8
	rcrq	%rbx
	movq	%rbx, -24(rp)
	movq	%r8, -16(rp)
.Lcj2:	movq	%r9, -8(rp)
.Lcj1:	movq	%r10, %rbx

.Ldo:
	shrq	$2, n			C				4
	je	.Lend			C				2
	ALIGN(16)
.Loop:	addq	%rbx, %rbx		C rotate carry limb, restore acy

	movq	8(up), %r8
	movq	16(up), %r9
	sbbq	8(vp), %r8
	sbbq	16(vp), %r9
	movq	24(up), %r10
	movq	32(up), %r11
	sbbq	24(vp), %r10
	sbbq	32(vp), %r11

	leaq	32(up), up
	leaq	32(vp), vp

	rcrq	%r11			C rotate, save acy
	rcrq	%r10
	rcrq	%r9
	rcrq	%r8

	rcrq	%rbx
	movq	%rbx, (rp)
	movq	%r8, 8(rp)
	movq	%r9, 16(rp)
	movq	%r10, 24(rp)
	movq	%r11, %rbx

	leaq	32(rp), rp
	decq	n
	jne	.Loop

.Lend:	movq	%rbx, (rp)
	popq	%rbx
	ret
EPILOGUE()
