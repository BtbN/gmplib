/* mpn_sb_divrem_mn -- Divide natural numbers, producing both remainder and
   quotient.

   THE FUNCTIONS IN THIS FILE ARE INTERNAL FUNCTIONS WITH MUTABLE
   INTERFACES.  IT IS ONLY SAFE TO REACH THEM THROUGH DOCUMENTED INTERFACES.
   IN FACT, IT IS ALMOST GUARANTEED THAT THEY'LL CHANGE OR DISAPPEAR IN A
   FUTURE GNU MP RELEASE.


Copyright 1993, 1994, 1995, 1996, 2000, 2001 Free Software Foundation, Inc.

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
the Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
MA 02111-1307, USA. */

#include "gmp.h"
#include "gmp-impl.h"
#include "longlong.h"


/* The size where udiv_qrnnd_preinv should be used rather than udiv_qrnnd,
   meaning the quotient size where that should happen, the quotient size
   being how many udiv divisions will be done.  */

#ifndef SB_PREINV_THRESHOLD
# if UDIV_PREINV_ALWAYS
#  define SB_PREINV_THRESHOLD     0
# else
#  ifdef DIVREM_1_NORM_THRESHOLD
#   define SB_PREINV_THRESHOLD    DIVREM_1_NORM_THRESHOLD
#  else
#   if UDIV_TIME <= UDIV_NORM_PREINV_TIME
#    define SB_PREINV_THRESHOLD   MP_LIMB_T_MAX
#   else
#    define SB_PREINV_THRESHOLD \
       (1 + UDIV_TIME / (UDIV_TIME - UDIV_NORM_PREINV_TIME))
#   endif
#  endif
# endif
#endif


/* Divide num (NP/NSIZE) by den (DP/DSIZE) and write
   the NSIZE-DSIZE least significant quotient limbs at QP
   and the DSIZE long remainder at NP.
   Return the most significant limb of the quotient, this is always 0 or 1.

   Preconditions:
   0. NSIZE >= DSIZE.
   1. The most significant bit of the divisor must be set.
   2. QP must either not overlap with the input operands at all, or
      QP + DSIZE >= NP must hold true.  (This means that it's
      possible to put the quotient in the high part of NUM, right after the
      remainder in NUM.
   3. NSIZE >= DSIZE.
   4. DSIZE >= 2.  */


mp_limb_t
mpn_sb_divrem_mn (mp_ptr qp,
                  mp_ptr np, mp_size_t nsize,
                  mp_srcptr dp, mp_size_t dsize)
{
  mp_limb_t most_significant_q_limb = 0;
  mp_size_t qsize = nsize - dsize;
  mp_size_t i;
  mp_limb_t dx, d1, n0;
  mp_limb_t dxinv;
  int use_preinv;

  ASSERT (dsize > 2);
  ASSERT (nsize >= dsize);
  ASSERT (dp[dsize-1] & MP_LIMB_T_HIGHBIT);
  ASSERT (! MPN_OVERLAP_P (np, nsize, dp, dsize));
  ASSERT (! MPN_OVERLAP_P (qp, nsize-dsize, dp, dsize));
  ASSERT (! MPN_OVERLAP_P (qp, nsize-dsize, np, nsize) || qp+dsize >= np);

  np += qsize;
  dx = dp[dsize - 1];
  d1 = dp[dsize - 2];
  n0 = np[dsize - 1];

  if (n0 >= dx)
    {
      if (n0 > dx || mpn_cmp (np, dp, dsize - 1) >= 0)
	{
	  mpn_sub_n (np, np, dp, dsize);
	  most_significant_q_limb = 1;
	}
    }

  /* use_preinv is possibly a constant, but it's left to the compiler to
     optimize away the unused code in that case.  */
  use_preinv = ABOVE_THRESHOLD (qsize, SB_PREINV_THRESHOLD);
  if (use_preinv)
    invert_limb (dxinv, dx);

  for (i = qsize-1; i >= 0; i--)
    {
      mp_limb_t q;
      mp_limb_t nx;
      mp_limb_t cy_limb;

      nx = np[dsize - 1];
      np--;

      if (nx == dx)
	{
	  /* This might over-estimate q, but it's probably not worth
	     the extra code here to find out.  */
	  q = ~(mp_limb_t) 0;

#if 1
	  cy_limb = mpn_submul_1 (np, dp, dsize, q);
#else
	  /* This should be faster on many machines */
	  cy_limb = mpn_sub_n (np + 1, np + 1, dp, dsize);
	  cy = mpn_add_n (np, np, dp, dsize);
	  np[dsize] += cy;
#endif

	  if (nx != cy_limb)
	    {
	      mpn_add_n (np, np, dp, dsize);
	      q--;
	    }

	  qp[i] = q;
	}
      else
	{
	  mp_limb_t rx, r1, r0, p1, p0;

          /* "workaround" avoids a problem with gcc 2.7.2.3 i386 register
             usage when np[dsize-1] is used in an asm statement like
             umul_ppmm in udiv_qrnnd_preinv.  The symptom is seg faults due
             to registers being clobbered.  gcc 2.95 i386 doesn't have the
             problem. */
          {
            mp_limb_t  workaround = np[dsize - 1];
            if (use_preinv)
              udiv_qrnnd_preinv (q, r1, nx, workaround, dx, dxinv);
            else
              udiv_qrnnd (q, r1, nx, workaround, dx);
          }
	  umul_ppmm (p1, p0, d1, q);

	  r0 = np[dsize - 2];
	  rx = 0;
	  if (r1 < p1 || (r1 == p1 && r0 < p0))
	    {
	      p1 -= p0 < d1;
	      p0 -= d1;
	      q--;
	      r1 += dx;
	      rx = r1 < dx;
	    }

	  p1 += r0 < p0;	/* cannot carry! */
	  rx -= r1 < p1;	/* may become 11..1 if q is still too large */
	  r1 -= p1;
	  r0 -= p0;

	  cy_limb = mpn_submul_1 (np, dp, dsize - 2, q);

	  {
	    mp_limb_t cy1, cy2;
	    cy1 = r0 < cy_limb;
	    r0 -= cy_limb;
	    cy2 = r1 < cy1;
	    r1 -= cy1;
	    np[dsize - 1] = r1;
	    np[dsize - 2] = r0;
	    if (cy2 != rx)
	      {
		mpn_add_n (np, np, dp, dsize);
		q--;
	      }
	  }
	  qp[i] = q;
	}
    }

  /* ______ ______ ______
    |__rx__|__r1__|__r0__|		partial remainder
	    ______ ______
	 - |__p1__|__p0__|		partial product to subtract
	    ______ ______
	 - |______|cylimb|		

     rx is -1, 0 or 1.  If rx=1, then q is correct (it should match
     carry out).  If rx=-1 then q is too large.  If rx=0, then q might
     be too large, but it is most likely correct.
  */

  return most_significant_q_limb;
}
