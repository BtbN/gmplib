dnl  PowerPC-32 mpn_divexact_by3 -- mpn by 3 exact division

dnl  Copyright 2002, 2003 Free Software Foundation, Inc.
dnl
dnl  This file is part of the GNU MP Library.
dnl
dnl  The GNU MP Library is free software; you can redistribute it and/or modify
dnl  it under the terms of the GNU Lesser General Public License as published
dnl  by the Free Software Foundation; either version 2.1 of the License, or (at
dnl  your option) any later version.
dnl
dnl  The GNU MP Library is distributed in the hope that it will be useful, but
dnl  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
dnl  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
dnl  License for more details.
dnl
dnl  You should have received a copy of the GNU Lesser General Public License
dnl  along with the GNU MP Library; see the file COPYING.LIB.  If not, write to
dnl  the Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
dnl  MA 02111-1307, USA.

include(`../config.m4')

C                cycles/limb
C 603e:             ?
C 604e:             7.0
C 75x (G3):        10.0
C 7400,7410 (G4):  10.0
C 744x,745x (G4+): 10.0
C power4/ppc970:   16.0

C void mpn_divexact_by3 (mp_ptr dst, mp_srcptr src, mp_size_t size);
C
C Scheduling the load back a bit gets us down from 11 c/l to 10 c/l.
C
C The mullw has the inverse in the first operand, since 0xAA..AB won't allow
C any early-out.  The src[] data normally won't either, but there's at least
C a chance, whereas 0xAA..AB never will.  If, for instance, src[] is all
C zeros (not a sensible input of course) we run at 7.0 c/l on ppc750.
C
C The mulhwu has the "3" multiplier in the second operand, which lets 750
C and 7400 use an early-out.  The other way around costs an extra 3.5 c/l or
C so, on average.

ASM_START()
PROLOGUE(mpn_divexact_by3c)

	C r3	dst
	C r4	src
	C r5	size
	C r6	carry

	mtctr	r5		C size
	lwz	r7, 0(r4)	C src[0]

	lis	r5, 0xAAAA	C inverse high
	subi	r3, r3, 4	C adjust dst for first stwu

	li	r0, 3		C multiplier 3
	ori	r5, r5, 0xAAAB	C inverse low

	subfc	r7, r6, r7	C l = src[0] - carry
	bdz	L(one)

L(top):
	C r0	3
	C r3	dst, incrementing
	C r4	src, incrementing
	C r5	inverse
	C r6	carry
	C r7	l

	mullw	r8, r5, r7	C q = inverse * l
	lwzu	r7, 4(r4)	C src[i]

	C

	mulhwu	r6, r8, r0	C c = high(3*q)
	stwu	r8, 4(r3)	C dst[i-1] = q

	C serialize
	subfe	r7, r6, r7 	C l = s - carry
	bdnz	L(top)


L(one):
	subfe	r4, r4, r4	C ca 0 or -1

	mullw	r8, r7, r5	C q = l * inverse

	mulhwu	r6, r8, r0	C c = high(3*q)
	stwu	r8, 4(r3)	C dst[i] = q

	subf	r3, r4, r6	C carry + ca

	blr

EPILOGUE()
