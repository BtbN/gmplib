/* Intel P55 gmp-mparam.h -- Compiler/machine parameter header file.

Copyright (C) 1991, 1993, 1994, 1999, 2000 Free Software Foundation, Inc.

This file is part of the GNU MP Library.

The GNU MP Library is free software; you can redistribute it and/or modify
it under the terms of the GNU Library General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at your
option) any later version.

The GNU MP Library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Library General Public
License for more details.

You should have received a copy of the GNU Library General Public License
along with the GNU MP Library; see the file COPYING.LIB.  If not, write to
the Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
MA 02111-1307, USA. */


#define BITS_PER_MP_LIMB 32
#define BYTES_PER_MP_LIMB 4
#define BITS_PER_LONGINT 32
#define BITS_PER_INT 32
#define BITS_PER_SHORTINT 16
#define BITS_PER_CHAR 8


#ifndef UMUL_TIME
#define UMUL_TIME   9 /* cycles */
#endif
#ifndef UDIV_TIME
#define UDIV_TIME   41 /* cycles */
#endif

/* bsf takes 18-42 cycles, put an average for uniform random numbers */
#ifndef COUNT_TRAILING_ZEROS_TIME
#define COUNT_TRAILING_ZEROS_TIME   20  /* cycles */
#endif


/* Generated by tuneup.c, 2000-07-06. */

#ifndef KARATSUBA_MUL_THRESHOLD
#define KARATSUBA_MUL_THRESHOLD   14
#endif
#ifndef TOOM3_MUL_THRESHOLD
#define TOOM3_MUL_THRESHOLD       99
#endif

#ifndef KARATSUBA_SQR_THRESHOLD
#define KARATSUBA_SQR_THRESHOLD   22
#endif
#ifndef TOOM3_SQR_THRESHOLD
#define TOOM3_SQR_THRESHOLD       89
#endif

#ifndef BZ_THRESHOLD
#define BZ_THRESHOLD              40
#endif

#ifndef FIB_THRESHOLD
#define FIB_THRESHOLD             98
#endif

#ifndef POWM_THRESHOLD
#define POWM_THRESHOLD            13
#endif

#ifndef GCD_ACCEL_THRESHOLD
#define GCD_ACCEL_THRESHOLD        5
#endif
#ifndef GCDEXT_THRESHOLD
#define GCDEXT_THRESHOLD          25
#endif
