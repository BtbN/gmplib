/* mpn_sqr_basecase -- Internal routine to square a natural number
   of length n.

   THIS IS AN INTERNAL FUNCTION WITH A MUTABLE INTERFACE.  IT IS ONLY
   SAFE TO REACH THIS FUNCTION THROUGH DOCUMENTED INTERFACES.


Copyright 1991, 1992, 1993, 1994, 1996, 1997, 2000, 2001 Free Software
Foundation, Inc.

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

void
mpn_sqr_basecase (mp_ptr prodp, mp_srcptr up, mp_size_t n)
{
  mp_size_t i;

  ASSERT (n >= 1);
  ASSERT (! MPN_OVERLAP_P (prodp, 2*n, up, n));

  {
    /* N.B.!  We need the superfluous indirection through argh to work around
       a reloader bug in GCC 2.7.*.  */
    mp_limb_t x;
    mp_limb_t argh;
    x = up[0];
    umul_ppmm (argh, prodp[0], x, x);
    prodp[1] = argh;
  }
  if (n > 1)
    {
      mp_limb_t tarr[2 * KARATSUBA_SQR_THRESHOLD];
      mp_ptr tp = tarr;
      mp_limb_t cy;

      /* must fit 2*n limbs in tarr */
      ASSERT (n <= KARATSUBA_SQR_THRESHOLD);

      cy = mpn_mul_1 (tp, up + 1, n - 1, up[0]);
      tp[n - 1] = cy;
      for (i = 2; i < n; i++)
	{
	  mp_limb_t cy;
	  cy = mpn_addmul_1 (tp + 2 * i - 2, up + i, n - i, up[i - 1]);
	  tp[n + i - 2] = cy;
	}
#if HAVE_NATIVE_mpn_sqr_diagonal
      mpn_sqr_diagonal (prodp + 2, up + 1, n - 1);
#else
      for (i = 1; i < n; i++)
	{
	  mp_limb_t x;
	  x = up[i];
	  umul_ppmm (prodp[2 * i + 1], prodp[2 * i], x, x);
	}
#endif
      {
	mp_limb_t cy;
	cy = mpn_lshift (tp, tp, 2 * n - 2, 1);
	cy += mpn_add_n (prodp + 1, prodp + 1, tp, 2 * n - 2);
	prodp[2 * n - 1] += cy;
      }
    }
}
