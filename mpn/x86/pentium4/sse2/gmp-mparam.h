/* Intel Pentium-4 gmp-mparam.h -- Compiler/machine parameter header file.

Copyright 1991, 1993, 1994, 2000, 2001, 2002, 2003, 2004, 2005, 2007
Free Software Foundation, Inc.

This file is part of the GNU MP Library.

The GNU MP Library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or (at your
option) any later version.

The GNU MP Library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the GNU MP Library; see the file COPYING.LIB.  If not, write to
the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
MA 02110-1301, USA. */

#define BITS_PER_MP_LIMB 32
#define BYTES_PER_MP_LIMB 4


/* 2600 MHz Pentium 4 model 2 */

/* Generated by tuneup.c, 2007-05-20, gcc 4.1.2, using -p1000000 -f10000000 */

#define MUL_KARATSUBA_THRESHOLD          34
#define MUL_TOOM3_THRESHOLD             109

#define SQR_BASECASE_THRESHOLD            0  /* always (native) */
#define SQR_KARATSUBA_THRESHOLD          49
#define SQR_TOOM3_THRESHOLD             173

#define MULLOW_BASECASE_THRESHOLD         9
#define MULLOW_DC_THRESHOLD              39
#define MULLOW_MUL_N_THRESHOLD          656

#define DIV_SB_PREINV_THRESHOLD           4
#define DIV_DC_THRESHOLD                 18
#define POWM_THRESHOLD                  104

#define DC_DIV_QR_THRESHOLD              32
#define DC_DIVAPPR_Q_THRESHOLD           62
#define DC_DIV_Q_THRESHOLD               85
#define DC_BDIV_QR_THRESHOLD             55
#define DC_BDIV_Q_THRESHOLD              10
#define DIVEXACT_JEB_THRESHOLD           80

#define HGCD_SCHOENHAGE_THRESHOLD       101
#define GCD_ACCEL_THRESHOLD               6
#define GCD_SCHOENHAGE_THRESHOLD        341
#define GCDEXT_SCHOENHAGE_THRESHOLD     375
#define JACOBI_BASE_METHOD                1

#define USE_PREINV_DIVREM_1               1  /* native */
#define USE_PREINV_MOD_1                  1  /* native */
#define DIVREM_2_THRESHOLD               31
#define DIVEXACT_1_THRESHOLD              0  /* always (native) */
#define MODEXACT_1_ODD_THRESHOLD          0  /* always (native) */

#define GET_STR_DC_THRESHOLD             17
#define GET_STR_PRECOMPUTE_THRESHOLD     31
#define SET_STR_DC_THRESHOLD            674
#define SET_STR_PRECOMPUTE_THRESHOLD   1323

#define MUL_FFT_TABLE  { 720, 928, 1920, 5632, 14336, 73728, 163840, 393216, 1572864, 6291456, 0 }
#define MUL_FFT_MODF_THRESHOLD          960
#define MUL_FFT_THRESHOLD              5888

#define SQR_FFT_TABLE  { 720, 928, 1920, 5632, 14336, 57344, 163840, 655360, 1572864, 6291456, 0 }
#define SQR_FFT_MODF_THRESHOLD          816
#define SQR_FFT_THRESHOLD              4864

#define INV_NEWTON_THRESHOLD            283
#define BINV_NEWTON_THRESHOLD            27
