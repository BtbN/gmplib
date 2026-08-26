/* mpz_millerrabin(n,reps) -- An implementation of the probabilistic primality
   test found in Knuth's Seminumerical Algorithms book.  If the function
   mpz_millerrabin() returns 0 then n is not prime.  If it returns 1, then n is
   'probably' prime.  The probability of a false positive is (1/4)**reps, where
   reps is the number of internal passes of the probabilistic algorithm.  Knuth
   indicates that 25 passes are reasonable.

   With the current implementation, the first 24 MR-tests are substituted by a
   Baillie-PSW probable prime test.

   This implementation of the Baillie-PSW test was checked up to 2890*10^12,
   for smaller values no MR-test is performed, regardless of reps, and
   2 ("surely prime") is returned if the number was not proved composite.

   If GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS is defined as non-zero,
   the code assumes that the Baillie-PSW test was checked up to 2^64.

   THE FUNCTIONS IN THIS FILE ARE FOR INTERNAL USE ONLY.  THEY'RE ALMOST
   CERTAIN TO BE SUBJECT TO INCOMPATIBLE CHANGES OR DISAPPEAR COMPLETELY IN
   FUTURE GNU MP RELEASES.

Copyright 1991, 1993, 1994, 1996-2002, 2005, 2014, 2018-2022, 2024,
2026 Free Software Foundation, Inc.

Contributed by John Amanatides.
Changed to "BPSW, then Miller Rabin if required" by Marco Bodrato.

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

#ifndef GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS
#define GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS 0
#endif

#ifndef GMP_ENABLE_PROTH_TEST
#define GMP_ENABLE_PROTH_TEST 1
#endif

static int
mod_eq_m1 (mpz_srcptr x, mpz_srcptr m)
{
  mp_size_t ms;
  mp_srcptr mp, xp;

  ms = SIZ (m);
  if (SIZ (x) != ms)
    return 0;
  ASSERT (ms > 0);

  mp = PTR (m);
  xp = PTR (x);
  ASSERT ((mp[0] - 1) == (mp[0] ^ 1)); /* n is odd */

  if ((*xp ^ CNST_LIMB(1) ^ *mp) != CNST_LIMB(0)) /* xp[0] != mp[0] - 1 */
    return 0;
  else
    {
      int cmp;

      --ms;
      ++xp;
      ++mp;

      MPN_CMP (cmp, xp, mp, ms);

      return cmp == 0;
    }
}

/* Performs a Miller-Rabin test, on the number n, with base x.
 * The value q is the odd number such that (q<<k) + 1 = n.
 *
 * The variable y is overwritten, its only role is to reuse the same
 * temp variable.
 */

static int
millerrabin (mpz_srcptr n, mpz_srcptr x, mpz_ptr y,
	     mpz_srcptr q, mp_bitcnt_t k)
{
  mpz_powm (y, x, q, n);

  if (((SIZ (y) == 1) & (*PTR (y) == 1)) || mod_eq_m1 (y, n))
    return 1;

  for (mp_bitcnt_t i = 1; i < k; ++i)
    {
      mpz_powm_ui (y, y, 2L, n);
      if (mod_eq_m1 (y, n))
	return 1;
    }
  return 0;
}

int
mpz_millerrabin (mpz_srcptr n, int reps)
{
  mpz_t nm, x, y, q;
  mp_bitcnt_t k;
  mp_limb_t h;
  int is_prime;
  TMP_DECL;

  ASSERT (SIZ (n) > 0);
  h = PTR (n) [SIZ (n) - 1];
  ASSERT ((SIZ (n) > 1) || (h > 9));

  /* Find q and k, where q is odd and n = 1 + 2**k * q.  */
  k = mpn_scan1 (PTR (n), 1);

  if (GMP_ENABLE_PROTH_TEST &&
      (SIZ (n) <= (k - 1) / (GMP_NUMB_BITS >> 1) + 1) &&
      ((SIZ (n) < (k - 1) / (GMP_NUMB_BITS >> 1) + 1) ||
       (k % (GMP_NUMB_BITS >> 1) == 0) ||
       !(h >> k % (GMP_NUMB_BITS >> 1) * 2))) {
  /* if (GMP_ENABLE_PROTH_TEST && ((l = mpz_sizeinbase (n, 2) - k) <= k)) { */
    ASSERT (k > 1);
    /* The number n is a Proth number: 2**k > q. */

    /* The next search with _kronecker_ would fail with a square n,
       we detect possible squares (of the given form, > 9) here. */
    if (((SIZ (n) == (k - 1) / (GMP_NUMB_BITS >> 1) + 1) && /* (2^(k-1)+1)^2 */
	 ((h >> (k - 1) % (GMP_NUMB_BITS >> 1) * 2) == CNST_LIMB (1)) &&
	 (mpn_scan1 (PTR (n), k + 1) == k - 1 << 1)) ||
	((SIZ (n) == (k - 2) / (GMP_NUMB_BITS >> 1) + 1) && /* (2^(k-1)-1)^2 */
	 ((h >> (k - 2) % (GMP_NUMB_BITS >> 1) * 2) == CNST_LIMB (3)) &&
	 (mpz_scan0 (n, k + 1) == k - 1 << 1)))
      return 0; /* n is a square => it is a composite */

    unsigned long b = 3;
    do {
      int knb = mpz_kronecker_ui (n, b);
      if (knb <= 0) {
	if (knb == 0) /* knb == 0, gcd(b,n) != 1. */
	  is_prime = 0; /* Composite. */
	else {
	  mp_limb_t const xp[1] = {b};
	  TMP_MARK;

	  MPZ_TMP_INIT (y, SIZ (n));
	  MPZ_TMP_INIT (q, SIZ (n));

	  mpz_tdiv_q_2exp (q, n, 1);

	  mpz_roinit_n (x, xp, 1);
	  mpz_powm (y, x, q, n);
	  /* n is prime if and only if x^{(n-1)/2} (mod n) = n - 1.
	     In case, n is surely prime, we can return 2. */
	  is_prime = mod_eq_m1 (y, n) << 1;

	  TMP_FREE;
	}

	return is_prime;
      }

      /* k == 1, continue */
      b += 2; /* FIXME: Loop on primes only. */
    } while (b < MIN (ULONG_MAX, GMP_NUMB_MAX));
    /* FIXME: We should impose a smaller limit. */
  }

  TMP_MARK;

  MPZ_TMP_INIT (x, SIZ (n) + 1);
  MPZ_TMP_INIT (y, 2 * SIZ (n)); /* mpz_powm_ui needs excessive memory!!! */
  MPZ_TMP_INIT (q, SIZ (n));

  mpz_tdiv_q_2exp (q, n, k);

  /* BPSW test */
  mpz_set_ui (x, 2);
  is_prime = millerrabin (n, x, y, q, k) && mpz_stronglucas (n, x, y);

  /* Consider numbers up to 41*2^46 that pass the BPSW test as primes.
     This implementation was tested up to 289*10^13 > 2^51+2^49+2^46 */
  /* 2^5 < 41 = 0b101001 < 2^6 */
#define GMP_BPSW_LIMB_CONST CNST_LIMB(41)
#define GMP_BPSW_BITS_CONST (LOG2C(41) - 1)
#define GMP_BPSW_BITS_LIMIT (46 + GMP_BPSW_BITS_CONST)

#define GMP_BPSW_LIMBS_LIMIT (GMP_BPSW_BITS_LIMIT / GMP_NUMB_BITS)
#define GMP_BPSW_BITS_MOD (GMP_BPSW_BITS_LIMIT % GMP_NUMB_BITS)

  if (is_prime)
    {
#if !GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS && GMP_BPSW_BITS_MOD == 0
      MPZ_TMP_INIT (nm, SIZ (n));
      mpz_tdiv_q_2exp (nm, n, 1);
#endif
      if (
#if GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS
	  /* Consider numbers up to 2^64 that pass the BPSW test as primes. */
#if GMP_NUMB_BITS <= 64
	  SIZ (n) <= 64 / GMP_NUMB_BITS
#else
	  0
#endif
#if 64 % GMP_NUMB_BITS != 0
	  || SIZ (n) - 64 / GMP_NUMB_BITS == (h < CNST_LIMB(1) << 64 % GMP_NUMB_BITS)
#endif
#else
	  /* Consider numbers that pass the BPSW test as primes, if
	     they are in the range where this implementation of the
	     test has been fully tested. */
#if GMP_NUMB_BITS <=  GMP_BPSW_BITS_LIMIT
	  SIZ (n) <= GMP_BPSW_LIMBS_LIMIT ||
#endif
#if GMP_BPSW_BITS_MOD != 0
	  SIZ (n) - GMP_BPSW_LIMBS_LIMIT == (h <
#if GMP_BPSW_BITS_MOD >=  GMP_BPSW_BITS_CONST
					     GMP_BPSW_LIMB_CONST << (GMP_BPSW_BITS_MOD - GMP_BPSW_BITS_CONST))
#else
					     GMP_BPSW_LIMB_CONST >> (GMP_BPSW_BITS_CONST -  GMP_BPSW_BITS_MOD))
#endif
#else /* GMP_BPSW_BITS_MOD == 0 */
	  SIZ (nm) - GMP_BPSW_LIMBS_LIMIT + 1 == (h <
#if GMP_NUMB_BITS > GMP_BPSW_BITS_CONST
						  GMP_BPSW_LIMB_CONST << (GMP_NUMB_BITS - 1 - GMP_BPSW_BITS_CONST))
#else
						  GMP_BPSW_LIMB_CONST >> (1 + GMP_BPSW_BITS_CONST - GMP_NUMB_BITS))
#endif
#endif
#endif
	  )
	is_prime = 2;
      else
	{
#if GMP_BPSW_NOFALSEPOSITIVES_UPTO_64BITS || GMP_BPSW_BITS_MOD != 0
	  MPZ_TMP_INIT (nm, SIZ (n));
	  mpz_tdiv_q_2exp (nm, n, 1);
#endif
	  reps -= 24;
	  if (reps > 0)
	    {
	      gmp_randstate_t rstate;
	      /* (n-5)/2 */
	      mpz_sub_ui (nm, nm, 2L);
	      ASSERT (mpz_cmp_ui (nm, 1L) >= 0);

	      gmp_randinit_default (rstate);

	      do
		{
		  /* 3 to (n-1)/2 inclusive, don't want 1, 0 or 2 */
		  mpz_urandomm (x, rstate, nm);
		  mpz_add_ui (x, x, 3L);

		  is_prime = millerrabin (n, x, y, q, k);
		} while (--reps > 0 && is_prime);

	      gmp_randclear (rstate);
	    }
	}
    }
  TMP_FREE;
  return is_prime;
}

#undef GMP_BPSW_BITS_LIMIT
#undef GMP_BPSW_LIMB_CONST
#undef GMP_BPSW_BITS_CONST
#undef GMP_BPSW_LIMBS_LIMIT
#undef GMP_BPSW_BITS_MOD
