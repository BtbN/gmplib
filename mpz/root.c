/* mpz_root(root, u, nth) --  Set ROOT to floor(U^(1/nth)).
   Return an indication if the result is exact.

Copyright (C) 2000 Free Software Foundation, Inc.

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

/* Naive implementation of nth root extraction.  It would probably be a
   better idea to use a division-free Newton iteration.  It is insane
   to use full precision from iteration 1.  The mpz_scan1 trick compensates
   to some extent.  It would be natural to avoid representing the low zero
   bits mpz_scan1 is counting, and at the same time call mpn directly.  */

#include "gmp.h"
#include "gmp-impl.h"
#include "longlong.h"

int
mpz_root (mpz_ptr r, mpz_srcptr c, unsigned long int nth)
{
  mpz_t x, t0, t1, t2;
  unsigned long int nbits;
  int bit;
  int exact;
  int i;
  unsigned long int lowz;
  unsigned long int rl;

  if (mpz_sgn (c) == 0)
    {
      mpz_set_ui (r, 0);
      return 1;			/* exact result */
    }

  mpz_init (x);
  mpz_init (t0);
  mpz_init (t1);
  mpz_init (t2);

  nbits = (mpz_sizeinbase (c, 2) - 1) / nth;
  if (nbits == 0)
    {
      mpz_set_ui (r, 1);
      return 0;			/* inexact result FIXME */
    }

  /* Create a one-bit approximation.  */
  mpz_set_ui (x, 0);
  mpz_setbit (x, nbits);

  /* Make the approximation better, one bit at a time.  This odd-looking
     termination criteria makes large nth get better initial approximation,
     which avoids slow convergence for such values.  */
  bit = nbits - 1;
  for (i = 1; (nth >> i) != 0; i++)
    {
      mpz_setbit (x, bit);
      mpz_tdiv_q_2exp (t0, x, bit);
      mpz_pow_ui (t1, t0, nth);
      mpz_mul_2exp (t1, t1, bit * nth);
      if (mpz_cmp (c, t1) < 0)
	mpz_clrbit (x, bit);

      bit--;			/* check/set next bit */
      if (bit < 0)
	{
	  /* We're done.  */
	  mpz_pow_ui (t1, x, nth);
	  goto done;
	}
    }
  mpz_setbit (x, bit);
  mpz_set_ui (t2, 0); mpz_setbit (t2, bit);  mpz_add (x, x, t2);

#if DEBUG
  /* Check that the starting approximation is >= than the root.  */
  mpz_pow_ui (t1, x, nth);
  if (mpz_cmp (c, t1) >= 0)
    abort ();
#endif

  mpz_add_ui (x, x, 1);

  /* Main loop */
  do
    {
      lowz = mpz_scan1 (x, 0);
      mpz_tdiv_q_2exp (t0, x, lowz);
      mpz_pow_ui (t1, t0, nth - 1);
      mpz_mul_2exp (t1, t1, lowz * (nth - 1));
      mpz_tdiv_q (t2, c, t1);
      mpz_sub (t2, x, t2);
      rl = mpz_tdiv_q_ui (t2, t2, nth);
      mpz_sub (x, x, t2);
    }
  while (mpz_sgn (t2) != 0);

  /* If we got a non-zero remainder in the last division, we know our root
     is too large.  */
  mpz_sub_ui (x, x, (mp_limb_t) (rl != 0));

  /* Adjustment loop.  If we spend more care on rounding in the loop above,
     we could probably get rid of this, or greatly simplify it.  */
  {
    int bad = 0;
    lowz = mpz_scan1 (x, 0);
    mpz_tdiv_q_2exp (t0, x, lowz);
    mpz_pow_ui (t1, t0, nth);
    mpz_mul_2exp (t1, t1, lowz * nth);
    while (mpz_cmp (c, t1) < 0)
      {
	bad++;
	if (bad > 2)
	  abort ();			/* abort if our root is far off */
	mpz_sub_ui (x, x, 1);
	lowz = mpz_scan1 (x, 0);
	mpz_tdiv_q_2exp (t0, x, lowz);
	mpz_pow_ui (t1, t0, nth);
	mpz_mul_2exp (t1, t1, lowz * nth);
      }
  }

 done:
  exact = mpz_cmp (t1, c) == 0;

  if (r != NULL)
    mpz_set (r, x);

  mpz_clear (t2);
  mpz_clear (t1);
  mpz_clear (t0);
  mpz_clear (x);

  return exact;
}
