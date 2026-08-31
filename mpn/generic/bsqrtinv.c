/* mpn_bsqrtinv, compute r such that r^2 * y = 1 (mod 2^{b+1}).

   Contributed to the GNU project by Martin Boij (as part of perfpow.c),
   optimized by Marco Bodrato.

Copyright 2009, 2010, 2012, 2015, 2026 Free Software Foundation, Inc.

This file is part of the GNU MP Library.

The GNU MP Library is free software; you can redistribute it and/or modify
it under the terms of either:

  * the GNU Lesser General Public License as published by the Free
    Software Foundation; either version 3 of the License, or (at your
    option) any later version.

or

  * the GNU General Public License as published by the Free Software
    Foundation; either version 2 of the License, or (at your option) any
    later version.

or both in parallel, as here.

The GNU MP Library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received copies of the GNU General Public License and the
GNU Lesser General Public License along with the GNU MP Library.  If not,
see https://www.gnu.org/licenses/.  */

#include "gmp-impl.h"
#include "longlong.h"

/* Compute r such that r^2 * y = 1 (mod 2^{b+1}).
   Return non-zero if such an integer r exists.

   Iterates
     t  <-- (r^2 y - 1) / 2
     r' <-- r - r t , (or its negation, sometimes)
   using Hensel lifting.  Since we divide by two, the Hensel lifting is
   somewhat degenerates.  Therefore, we lift from 2^b to 2^{b+1}-1.

   Somewhere, the Halley recursion is used, lifting from n to 3n-1.
     t  <-- (r^2 y - 1) / 2
     r' <-- r - r t + r 3t^2 / 2

   FIXME:
     (1) Simplify to do precision book-keeping in limbs rather than bits.

     (2) Take advantage of zero low part of r^2 y - 1.

     (3) Use wrap-around trick.
*/

#ifndef BSQRTINV_DONT_USE_TABLE
/* Generated with GP-Pari:
   b=7;v=Vecsmall(-binary(2^2^b-1));
   forstep(i=1,2^(b+1),2,v[lift(Mod(i,2^(b+3))^-2)>>3+1]=i);
   for(i=1,2^b,print1(v[i],",");if(i%16==0,print(),print1(" ")))
 */
static const unsigned char binvsqrttab[128] =
  {   1, 171, 167, 205, 143,   5,  73, 253,  31,  75,  57,  45, 175, 101, 215,  93,
     63,  21, 231, 115, 207, 197,   9,  67,  95, 117,   7, 237, 239, 219, 233, 227,
    127, 213, 217,  77, 241, 123,  55, 125, 159, 203,  71,  83, 209,  27, 169,  35,
    191, 107, 153, 243, 177,  69, 119, 195, 223,  11, 135, 109, 145, 165, 105, 157,
    255,  85,  89,  51, 113, 251, 183,   3, 225, 181, 199, 211,  81, 155,  41, 163,
    193, 235,  25, 141,  49,  59, 247, 189, 161, 139, 249,  19,  17,  37,  23,  29,
    129,  43,  39, 179,  15, 133, 201, 131,  97,  53, 185, 173,  47, 229,  87, 221,
     65, 149, 103,  13,  79, 187, 137,  61,  33, 245, 121, 147, 111,  91, 151,  99};
#endif

/* tp needs 2*(1 + bnb / GMP_NUMB_BITS) limbs of space */
int
mpn_bsqrtinv (mp_ptr rp, mp_srcptr yp, mp_bitcnt_t bnb, mp_ptr tp)
{
  mp_limb_t y0 = *yp;
  ASSERT (bnb > 0);

#ifndef BSQRTINV_RP_NOT_ZEROED
  ASSERT ((bnb <= GMP_NUMB_BITS) || mpn_zero_p (rp + 1, bnb / GMP_NUMB_BITS));
#endif
  if (UNLIKELY (bnb == 1))
    {
      *rp = y0;
      return (y0 & 3) == 1;
    }
  else
    {
      mp_ptr tp2 = tp + 1 + bnb / GMP_NUMB_BITS;
      mp_size_t bn, order[GMP_LIMB_BITS + 1];
      mp_limb_t r0;
      int i;

      if ((y0 & 7) != 1)
	return 0;

#ifdef BSQRTINV_DONT_USE_TABLE
      /* 16-bits computations are enough */
      unsigned ru = 1 + ((y0 & 8) >> 2) + ((y0 & 16) >> 1);

      unsigned tu = ru * ru * (unsigned) y0 >> 1;
      ASSERT ((tu & (GMP_NUMB_MAX >> (GMP_NUMB_BITS - 4))) == 0);
      ru += ru * tu * ((tu >> 1) + tu - 1); /* Halley -> 11 */
      //      ru += ru * (tu >> 1) * (3 * tu - 2); /* Halley -> 11 */
      /* Better sequences are possible from size 11, but this
	 code is currently not used. */
      r0 = ru;
#else /* ! defined(BSQRTINV_DONT_USE_TABLE) */
      r0 = binvsqrttab[(y0 >> 3) & 0x7f];
#endif

#if GMP_NUMB_BITS < 9 * 2 - 1
      const mp_bitcnt_t precomputed_bits = 9;
#else /* GMP_NUMB_BITS > 9 * 2 - 2 */
      r0 -= r0 * (y0 * r0 * r0 >> 1); /* 9 -> 17 */
#if GMP_NUMB_BITS < 17 * 2 - 1
      const mp_bitcnt_t precomputed_bits = 17;
#else /* GMP_NUMB_BITS > 17 * 2 - 2 */
      r0 -= r0 * (y0 * r0 * r0 >> 1); /* 17 -> 33 */
#if GMP_NUMB_BITS < 33 * 2 - 1
      const mp_bitcnt_t precomputed_bits = 33;
#else /* GMP_NUMB_BITS > 33 * 2 - 2 */
      mp_bitcnt_t precomputed_bits = 33;
      do {
	r0 -= r0 * (y0 * r0 * r0 >> 1); /* n -> 2*n-1 */
	precomputed_bits = precomputed_bits * 2 - 1;
      } while ((GMP_NUMB_BITS + 3) / 2 > precomputed_bits);
#endif
#endif
#endif

      i = 0;
      for (; bnb > GMP_NUMB_BITS + 1; bnb = (bnb >> 1) + 1)
	order[i++] = bnb;
      if (bnb > precomputed_bits) {
	if (bnb >= GMP_NUMB_BITS) {
	  mp_limb_t r0h = r0 >> 1;
	  /* We could gain the third bit with (r0h|1)*((r0h+1)>>1) */
	  mp_limb_t r0sqm1 = r0h * (r0h + 1); /* r0*r0 >> 2 */
	  mp_limb_t yh = (y0 >> 2) + (yp[1] << (GMP_NUMB_BITS - 2));
	  mp_limb_t yrrm1d4 = y0 * r0sqm1 + yh; /* (r0*r0*y0-1) >> 2 */
	  ASSERT ((yrrm1d4 & (GMP_NUMB_MAX >> (GMP_NUMB_BITS - precomputed_bits + 1))) == 0);
	  mp_limb_t rt = r0h - r0 * yrrm1d4;  /* (r - r*(r0*r0*y0-1)/2) >>1 */
	  /* mp_limb_t rt = r0h + r0 * yrrm1d4 * (yrrm1d4 * 3 - 1); /\* Halley, x3 - 1 *\/ */
	  r0 = (rt << 1) ^ ((rt & GMP_LIMB_HIGHBIT) ? GMP_NUMB_MAX : CNST_LIMB(1));
#ifdef BSQRTINV_RP_NOT_ZEROED
	  rp[1] = 0;
#endif
	} else {
	  r0 -= r0 * (y0 * r0 * r0 >> 1); /* -> GMP_NUMB_BITS - 1 */
	}
      }

      if (i) {
	mp_limb_t t4, t3, t2, t1, t0, r1;

	umul_ppmm (t1, t0, r0, r0); /* [t1,t0] <- r^2 */
	if (bnb <= GMP_NUMB_BITS) {
	  umul_ppmm (t3, t2, y0, t0);
	  t3 += y0 * t1 + yp[1] * t0;
	  t2 = ((t2 >> 1) | (t3 << (GMP_NUMB_BITS - 1))) & GMP_NUMB_MAX;
	  t3 = t3 >> 1 ; /* [t3,t2] <- (r^2 y - 1) / 2 */

	  /* [r1,t4] <- r (r^2 y - 1) / 2 */
	  umul_ppmm (r1, t4, r0, t2);
	  r1 += r0 * t3;

	  /* r (r^2 y - 1) / 2 - r */
	  sub_ddmmss(rp[1], rp[0], r1, t4, 0, r0);
	} else {
	  t0 = (t0 >> 2) | (t1 << (GMP_NUMB_BITS -2)) & GMP_NUMB_MAX;
	  t1 = (t1 >> 2); /* [t1,t0] = r0*r0 >> 2 */
	  umul_ppmm (t3, t2, y0, t0);
	  t3 += y0 * t1 + yp[1] * t0;
	  t3 += (yp[1] >> 2) + (yp[2] << (GMP_NUMB_BITS - 2)) + (t2 != 0);
	  ASSERT (t2 + (y0 >> 2) + (yp[1] << (GMP_NUMB_BITS - 2)) == 0);
	  /* [t3,0] <- (r0^2 y - 1) / 2 / 2 */

	  t4 = t3 * r0 - 1;
	  /* [2*t4+1,-r0] <- r0*(r0^2 y-1)/2 - r0 */
	  if (t4 & GMP_LIMB_HIGHBIT) {
	    rp[0] = r0 & GMP_NUMB_MAX;
	    rp[1] = ~t4 << 1;
	  } else {
	    rp[0] = -r0 & GMP_NUMB_MAX;
	    rp[1] = (t4 << 1) ^ 1;
	  }
#ifdef BSQRTINV_RP_NOT_ZEROED
	  rp[2] = 0;
#endif
	}
	--i;

	for (bn = 2 + (bnb > GMP_NUMB_BITS); --i >= 0;)
	  {
	    mp_size_t pbn = bn;
	    /* The portion of the result of sqr that overlaps with
	       tp2, is not relevant anyway. */

	    /* FIXME: Could maybe be updated:
	       - use wraparound, low quarter known from previous
	         iteration; or
	       - the current r = prev_r + 2^n*d,
	         r^2 = prev_r^2 + 2^{n+1}*prev_r*d + 2^{2n}*d^2 .
	    */
	    mpn_sqr (tp, rp, bn); /* tp <- r^2 */

	    bnb = order[i];
	    bn = 1 + bnb / GMP_LIMB_BITS;

#ifdef  BSQRTINV_USE_MULMID
	    if (pbn > 20) /* Should be tuned, if it makes sense */
	      {
		int offset = 2; /* The larger, the safer */
		mpn_mullo_n (tp2 + pbn - offset, yp, tp + pbn - offset, bn - pbn + offset);
		/* mulmid partially overwrites tp2, but that part is unused here */
		mpn_mulmid (tp + pbn - offset, yp, bn, tp, pbn - offset);
		ASSERT (tp [bn + 2] < GMP_NUMB_MAX); /* MPN_INCR will be stopped here */
		MPN_INCR_U (tp + pbn, bn - pbn + 3, ! mpn_zero_p (tp + pbn - offset, offset) |
			    ! mpn_zero_p (tp2 + pbn - offset, offset - 1));
		mpn_add_nc (tp2 + pbn - 1, tp2 + pbn - 1, tp + pbn,
			    bn - pbn + 1, (tp2[pbn - 1] ^ tp[pbn]) & 1);
	      }
	    else
#endif
	      {
		mpn_mullo_n (tp2, yp, tp, bn); /* tp2 <- rp^2 y */
		ASSERT (tp2[0] == CNST_LIMB (1));
		ASSERT (pbn == 2 || mpn_zero_p (tp2 + 1, pbn - 2));
		/* tp2 <- (rp^2 y - 1) / 2 (skip the lowest limbs) */
	      }
	    ASSERT_NOCARRY (mpn_rshift (tp2 + pbn - 1, tp2 + pbn - 1, bn - pbn + 1, 1));

	    /* tp <- r (r^2 y - 1) / 2 (only the relevant limbs) */
#ifdef BSQRTINV_RP_NOT_ZEROED
	    rp [pbn] = 0;
#endif
	    ASSERT (pbn >= bn - pbn + 1 || (pbn == bn - pbn && rp [pbn] == 0));
	    mpn_mullo_n (tp, rp, tp2 + pbn - 1, bn - pbn + 1);

	    /* mpn_rsub_1 (rp + pbn - 1, tp, bn - pbn + 1, rp[pbn - 1]) */
	    int borrow;
	    SUBC_LIMB (borrow, rp[pbn - 1], rp[pbn - 1], tp[0]);

	    if (borrow)
	      mpn_com (rp + pbn, tp + 1, bn - pbn);
	    else
	      mpn_neg (rp + pbn, tp + 1, bn - pbn);
	    /* rp <- r - r (r^2 y - 1) / 2 */
	  }
      } else {
	*rp = r0 & GMP_NUMB_MAX;
      }
    }
  return 1;
}
