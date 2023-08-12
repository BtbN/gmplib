dnl  S/390-64 mpn_mul_1 and mpn_mul_1c.
dnl  Based on C code contributed by Marius Hillenbrand.

dnl  Copyright 2023 Free Software Foundation, Inc.

dnl  This file is part of the GNU MP Library.
dnl
dnl  The GNU MP Library is free software; you can redistribute it and/or modify
dnl  it under the terms of either:
dnl
dnl    * the GNU Lesser General Public License as published by the Free
dnl      Software Foundation; either version 3 of the License, or (at your
dnl      option) any later version.
dnl
dnl  or
dnl
dnl    * the GNU General Public License as published by the Free Software
dnl      Foundation; either version 2 of the License, or (at your option) any
dnl      later version.
dnl
dnl  or both in parallel, as here.
dnl
dnl  The GNU MP Library is distributed in the hope that it will be useful, but
dnl  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
dnl  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
dnl  for more details.
dnl
dnl  You should have received copies of the GNU General Public License and the
dnl  GNU Lesser General Public License along with the GNU MP Library.  If not,
dnl  see https://www.gnu.org/licenses/.

include(`../config.m4')

C            cycles/limb
C z900		 -
C z990		 -
C z9		 -
C z10		 -
C z196		 -
C z12		 -
C z13		 ?
C z14		 ?
C z15		 2.25


define(`rp',	`%r2')
define(`ap',	`%r3')
define(`an',	`%r4')
define(`b0',	`%r5')
define(`cy',	`%r6')

define(`idx',	`%r4')

ifdef(`HAVE_HOST_CPU_z15',`define(`HAVE_vler',1)')
ifdef(`HAVE_HOST_CPU_z16',`define(`HAVE_vler',1)')
ifdef(`HAVE_vler',`
define(`vpdi', `dnl')
',`
define(`vler', `vl')
define(`vster', `vst')
')

ASM_START()

PROLOGUE(mpn_mul_1c)
	stmg	%r6, %r10, 48(%r15)
	j	L(ent)
EPILOGUE()

PROLOGUE(mpn_mul_1)
	stmg	%r6, %r10, 48(%r15)
	lghi	%r6, 0
L(ent):	vzero	%v2
	srlg	%r10, an, 2

	tmll	an, 1
	je	L(bx0)
L(bx1):	tmll	an, 2
	jne	L(b11)

L(b01):	lghi	idx, -24
	lgr	%r0, %r6
	lg	%r7, 0(ap)
	mlgr	%r6, b0
	algr	%r7, %r0
	lghi	%r0, 0
	alcgr	%r6, %r0
	stg	%r7, 0(rp)
	cgije	%r10, 0, L(1)
	j	L(cj0)

L(b11):	lghi	idx, -8
	lg	%r9, 0(ap)
	mlgr	%r8, b0
	algr	%r9, %r6
	lghi	%r6, 0
	alcgr	%r8, %r6
	stg	%r9, 0(rp)
	j	L(cj1)

L(bx0):	tmll	an, 2
	jne	L(b10)

L(b00):	lghi	idx, -32
L(cj0):	lg	%r1, 32(idx, ap)
	lg	%r9, 40(idx, ap)
	mlgr	%r0, b0
	mlgr	%r8, b0
	vlvgp	%v6, %r0, %r1
	vlvgp	%v7, %r9, %r6
	j	L(mid)

L(b10):	lghi	idx, -16
	lgr	%r8, %r6
L(cj1):	lg	%r1, 16(idx, ap)
	lg	%r7, 24(idx, ap)
	mlgr	%r0, b0
	mlgr	%r6, b0
	vlvgp	%v6, %r0, %r1
	vlvgp	%v7, %r7, %r8
	cgije	%r10, 0, L(end)

L(top):	lg	%r1, 32(idx, ap)
	lg	%r9, 40(idx, ap)
	mlgr	%r0, b0
	mlgr	%r8, b0
	vacq	%v3, %v6, %v7, %v2
	vacccq	%v2, %v6, %v7, %v2
	vpdi	%v3, %v3, %v3, 4
	vster	%v3, 16(idx, rp), 3
	vlvgp	%v6, %r0, %r1
	vlvgp	%v7, %r9, %r6
L(mid):	lg	%r1, 48(idx, ap)
	lg	%r7, 56(idx, ap)
	mlgr	%r0, b0
	mlgr	%r6, b0
	vacq	%v3, %v6, %v7, %v2
	vacccq	%v2, %v6, %v7, %v2
	vpdi	%v3, %v3, %v3, 4
	vster	%v3, 32(idx, rp), 3
	vlvgp	%v6, %r0, %r1
	vlvgp	%v7, %r7, %r8
	la	idx, 32(idx)
	brctg	%r10, L(top)

L(end):	vacq	%v3, %v6, %v7, %v2
	vacccq	%v2, %v6, %v7, %v2
	vpdi	%v3, %v3, %v3, 4
	vster	%v3, 16(idx, rp), 3

L(1):	vlgvg	%r2, %v2, 1
	algr	%r2, %r6
	lmg	%r6, %r10, 48(%r15)
	br	%r14
EPILOGUE()
