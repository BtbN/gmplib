dnl  S/390-64 mpn_invert_limb

dnl  Contributed to the GNU project by Torbjorn Granlund.

dnl  Copyright 2011 Free Software Foundation, Inc.

dnl  This file is part of the GNU MP Library.

dnl  The GNU MP Library is free software; you can redistribute it and/or modify
dnl  it under the terms of the GNU Lesser General Public License as published
dnl  by the Free Software Foundation; either version 3 of the License, or (at
dnl  your option) any later version.

dnl  The GNU MP Library is distributed in the hope that it will be useful, but
dnl  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
dnl  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
dnl  License for more details.

dnl  You should have received a copy of the GNU Lesser General Public License
dnl  along with the GNU MP Library.  If not, see http://www.gnu.org/licenses/.

include(`../config.m4')

C            cycles/limb
C z900	       142
C z990          88
C z9		 ?
C z10		 ?
C z196		 ?

ASM_START()
	TEXT
	ALIGN(16)
PROLOGUE(mpn_invert_limb)
	stg	%r9, 72(%r15)
	srlg	%r9, %r2, 55
	aghi	%r9, -256
	agr	%r9, %r9
	larl	%r4, approx_tab
	srlg	%r3, %r2, 24
	aghi	%r3, 1
	lghi	%r5, 1
	llgh	%r4, 0(%r9, %r4)
	sllg	%r9, %r4, 11
	msgr	%r4, %r4
	msgr	%r4, %r3
	srlg	%r4, %r4, 40
	aghi	%r9, -1
	sgr	%r9, %r4
	sllg	%r0, %r9, 60
	sllg	%r1, %r9, 13
	msgr	%r9, %r9
	msgr	%r9, %r3
	sgr	%r0, %r9
	ngr	%r5, %r2
	srlg	%r4, %r2, 1
	srlg	%r3, %r0, 47
	agr	%r3, %r1
	agr	%r4, %r5
	msgr	%r4, %r3
	srlg	%r1, %r3, 1
	lcgr	%r5, %r5
	ngr	%r1, %r5
	sgr	%r1, %r4
	mlgr	%r0, %r3
	srlg	%r9, %r0, 1
	sllg	%r4, %r3, 31
	agr	%r4, %r9
	lgr	%r1, %r4
	mlgr	%r0, %r2
	algr	%r1, %r2
	alcgr	%r0, %r2
	lgr	%r2, %r4
	sgr	%r2, %r0
	lg	%r9, 72(%r15)
	br	%r14
EPILOGUE()
	RODATA
	ALIGN(2)
approx_tab:
	.word	0x7fd,0x7f5,0x7ed,0x7e5,0x7dd,0x7d5,0x7ce,0x7c6
	.word	0x7bf,0x7b7,0x7b0,0x7a8,0x7a1,0x79a,0x792,0x78b
	.word	0x784,0x77d,0x776,0x76f,0x768,0x761,0x75b,0x754
	.word	0x74d,0x747,0x740,0x739,0x733,0x72c,0x726,0x720
	.word	0x719,0x713,0x70d,0x707,0x700,0x6fa,0x6f4,0x6ee
	.word	0x6e8,0x6e2,0x6dc,0x6d6,0x6d1,0x6cb,0x6c5,0x6bf
	.word	0x6ba,0x6b4,0x6ae,0x6a9,0x6a3,0x69e,0x698,0x693
	.word	0x68d,0x688,0x683,0x67d,0x678,0x673,0x66e,0x669
	.word	0x664,0x65e,0x659,0x654,0x64f,0x64a,0x645,0x640
	.word	0x63c,0x637,0x632,0x62d,0x628,0x624,0x61f,0x61a
	.word	0x616,0x611,0x60c,0x608,0x603,0x5ff,0x5fa,0x5f6
	.word	0x5f1,0x5ed,0x5e9,0x5e4,0x5e0,0x5dc,0x5d7,0x5d3
	.word	0x5cf,0x5cb,0x5c6,0x5c2,0x5be,0x5ba,0x5b6,0x5b2
	.word	0x5ae,0x5aa,0x5a6,0x5a2,0x59e,0x59a,0x596,0x592
	.word	0x58e,0x58a,0x586,0x583,0x57f,0x57b,0x577,0x574
	.word	0x570,0x56c,0x568,0x565,0x561,0x55e,0x55a,0x556
	.word	0x553,0x54f,0x54c,0x548,0x545,0x541,0x53e,0x53a
	.word	0x537,0x534,0x530,0x52d,0x52a,0x526,0x523,0x520
	.word	0x51c,0x519,0x516,0x513,0x50f,0x50c,0x509,0x506
	.word	0x503,0x500,0x4fc,0x4f9,0x4f6,0x4f3,0x4f0,0x4ed
	.word	0x4ea,0x4e7,0x4e4,0x4e1,0x4de,0x4db,0x4d8,0x4d5
	.word	0x4d2,0x4cf,0x4cc,0x4ca,0x4c7,0x4c4,0x4c1,0x4be
	.word	0x4bb,0x4b9,0x4b6,0x4b3,0x4b0,0x4ad,0x4ab,0x4a8
	.word	0x4a5,0x4a3,0x4a0,0x49d,0x49b,0x498,0x495,0x493
	.word	0x490,0x48d,0x48b,0x488,0x486,0x483,0x481,0x47e
	.word	0x47c,0x479,0x477,0x474,0x472,0x46f,0x46d,0x46a
	.word	0x468,0x465,0x463,0x461,0x45e,0x45c,0x459,0x457
	.word	0x455,0x452,0x450,0x44e,0x44b,0x449,0x447,0x444
	.word	0x442,0x440,0x43e,0x43b,0x439,0x437,0x435,0x432
	.word	0x430,0x42e,0x42c,0x42a,0x428,0x425,0x423,0x421
	.word	0x41f,0x41d,0x41b,0x419,0x417,0x414,0x412,0x410
	.word	0x40e,0x40c,0x40a,0x408,0x406,0x404,0x402,0x400
ASM_END()
