/* mpn_bsqrt, a^{1/2} (mod 2^n), for odd a.

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

/* tp needs (1 + nb / GMP_NUMB_BITS) limbs of space + the scratch
   used by mpn_bsqrtinv, i.e 3*(1 + nb / GMP_NUMB_BITS)

   For large enough sizes, it calls mpn_bsqrtinv for just half the
   needed precision, the last half is computed here, using a
   Karp–Markstein step.

   If T is the result of mpn_bsqrtinv, and A the input,
   R = A * T;
   result = R + T * (A-R^2)/2.
   In the computation of A-R^2, the lowest half is zero.

   WARNING:
   it reads  1 + (nb - 1) / GMP_NUMB_BITS limbs, and
   it writes 1 + (nb - 2) / GMP_NUMB_BITS limbs.
*/
int
mpn_bsqrt (mp_ptr rp, mp_srcptr ap, mp_bitcnt_t nb, mp_ptr tp)
{
  ASSERT (nb > 1);

  --nb;
  if (nb <= GMP_NUMB_BITS)
    {
      if (! mpn_bsqrtinv (tp, ap, nb, NULL))
	return 0;
      *rp = *tp * *ap;
    }
  else
    {
      mp_size_t nn = 1 + nb / GMP_NUMB_BITS;
      if (nn <= 4) /* THINK: should we tune this? */
	{
	  mp_ptr sp = tp + nn;

	  MPN_FILL (tp + 1, nn - 1, CNST_LIMB(0));
	  if (! mpn_bsqrtinv (tp, ap, nb, sp))
	    return 0;

	  nn -= nb % GMP_NUMB_BITS == 0;
	  mpn_mullo_n (rp, tp, ap, nn);
	}
      else
	{
	  mp_ptr sp;
	  mp_size_t n;
	  mp_bitcnt_t bnb = nb + 2 >> 1;

	  n = 1 + bnb / GMP_NUMB_BITS;
	  sp = tp + n;

	  MPN_FILL (tp, n, CNST_LIMB(0));
	  if (! mpn_bsqrtinv (tp, ap, bnb, sp))
	    return 0;

	  /* S = A * T; This is the low part of the result. */
	  mpn_mullo_n (rp, tp, ap, n);

	  if (n < 64) /* THINK: should we tune this? */
	    {
	      /* R^2; */
	      mpn_sqr (sp, rp, n);
	      --n;

	      /* (A-R^2)/2 */
	      ASSERT (mpn_cmp (sp, ap, n) == 0);
	      sp += n;
#if HAVE_NATIVE_mpn_rsh1sub_n
	      mpn_rsh1sub_n (sp, ap + n, sp, nn - n);
#else
	      mpn_sub_n (sp, ap + n, sp, nn - n);
	      ASSERT_NOCARRY (mpn_rshift (sp, sp, nn - n, 1));
#endif
	    }
	  else
	    {
	      mp_size_t rn = mpn_sqrmod_bnm1_next_size (n + 1);
	      TMP_DECL;

	      TMP_MARK;
	      mp_ptr scratch = TMP_ALLOC_LIMBS (mpn_sqrmod_bnm1_itch (rn, n));
	      /* S^2; */
	      mpn_sqrmod_bnm1 (sp + rn, rn, rp, n, scratch);
	      TMP_FREE;

	      --n;
	      mp_limb_t bw = mpn_sub (sp + rn, sp + rn, rn, ap, n);
	      MPN_DECR_U (sp + rn, rn, bw);

	      /* (A-R^2)/2 */
	      bw = mpn_sub_n (sp, ap + n, sp + n + rn, rn - n);
	      mpn_sub_nc (sp + rn - n, ap + rn, sp + rn, nn - rn, bw);
	      ASSERT_NOCARRY (mpn_rshift (sp, sp, nn - n, 1));
	    }

	  nn -= nb % GMP_NUMB_BITS == 0;
	  /* result = R + T * (A-R^2)/2. */
	  mp_limb_t saved_limb = rp [n];
	  mpn_mullo_n (rp + n, sp, tp, nn - n);
	  mpn_add_1 (rp + n, rp + n, nn - n, saved_limb);
	}
    }
  return 1;
}
