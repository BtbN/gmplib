dnl  IA-64 mpn_popcount.

dnl  Copyright 2000, 2001, 2002, 2003, 2004 Free Software Foundation, Inc.

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

C INPUT PARAMETERS
C sp = r32
C n = r33

C         cycles/limb
C Itanium:    1
C Itanium 2:  1


C unsigned long mpn_popcount (mp_srcptr src, mp_size_t size);
C
C 1 c/l is optimal on both itanium and itanium2.  itanium can only sustain 1
C load and 1 store per cycle, and itanium2 has only one popcnt unit.

ASM_START()
PROLOGUE(mpn_popcount)
	.prologue
	.save	ar.lc, r2
		mov	r2 = ar.lc
	.body
ifdef(`HAVE_ABI_32',
`		addp4	r32 = 0, r32
		sxt4	r33 = r33
		;;
')
		and	r22 = 3, r33
		shr.u	r23 = r33, 2	;;
		mov	ar.lc = r22
		mov	r8 = 0		;;
		br.cloop.dpnt	.Loop0	;;
		br.sptk	.L0
.Loop0:		ld8	r16 = [r32], 8	;;
		popcnt	r20 = r16	;;
		add	r8 = r8, r20
		br.cloop.dptk	.Loop0	;;

.L0:		mov	ar.lc = r23	;;
		br.cloop.dptk	.L1	;;
		mov	ar.lc = r2
		br.ret.sptk.many b0	;;
.L1:		ld8	r16 = [r32], 8	;;
		ld8	r17 = [r32], 8	;;
		ld8	r18 = [r32], 8	;;
		ld8	r19 = [r32], 8	;;
		br.cloop.dptk	.L2    ;;
		br.sptk		.Ldone1	;;
.L2:
		popcnt	r20 = r16
		ld8	r16 = [r32], 8	;;
		popcnt	r21 = r17
		ld8	r17 = [r32], 8	;;
		popcnt	r22 = r18
		ld8	r18 = [r32], 8	;;
		popcnt	r23 = r19
		ld8	r19 = [r32], 8	;;
		br.cloop.dptk	.Loop  ;;
		br.sptk		.Ldone0

.Loop:		add	r8 = r8, r20
		popcnt	r20 = r16
		ld8	r16 = [r32], 8	;;
		add	r8 = r8, r21
		popcnt	r21 = r17
		ld8	r17 = [r32], 8	;;
		add	r8 = r8, r22
		popcnt	r22 = r18
		ld8	r18 = [r32], 8	;;
		add	r8 = r8, r23
		popcnt	r23 = r19
		ld8	r19 = [r32], 8
		br.cloop.dptk	.Loop	;;

.Ldone0:
		add	r8 = r8, r20
		popcnt	r20 = r16	;;
		add	r8 = r8, r21
		popcnt	r21 = r17	;;
		add	r8 = r8, r22
		popcnt	r22 = r18	;;
		add	r8 = r8, r23
		popcnt	r23 = r19	;;
		add	r21 = r21, r20
		add	r23 = r23, r22	;;
		add	r8 = r8, r21	;;
		add	r8 = r8, r23
		mov	ar.lc = r2
		br.ret.sptk.many b0

.Ldone1:
		popcnt	r20 = r16
		popcnt	r21 = r17
		popcnt	r22 = r18
		popcnt	r23 = r19	;;
		add	r21 = r21, r20
		add	r23 = r23, r22	;;
		add	r8 = r8, r21	;;
		add	r8 = r8, r23
		mov	ar.lc = r2
		br.ret.sptk.many b0
EPILOGUE(mpn_popcount)
ASM_END()
