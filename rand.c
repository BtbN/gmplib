/* gmp_rand_init (state, size, alg) -- Initialize a random state.

Copyright (C) 1999, 2000  Free Software Foundation, Inc.

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

#include "gmp.h"
#include "gmp-impl.h"

/* Array of CL-schemes, ordered in increasing order of the first
   member (the 'm2exp' value).  The end of the array is indicated with
   an entry containing all zeros.  */
static __gmp_rand_lc_scheme_struct __gmp_rand_scheme[] =
{
#if 0
  /* FIXME: Remove. */
  {8, "7", 0},			/* Test. */
  {31,				/* fbsd rand(3) */
   "1103515245",		/* a (multiplier) */
   12345},			/* c (adder) */
#endif

  /*  {31, "22298549", 	     1}, */
				/* merit >= 1; no merit > 3 up to 32845469 */

  /* The following multipliers are all between 0.01m and 0.99m, and
     are congruent to 5 (mod 8).  They all pass the spectral test with
     Vt >= 2^(30/t) and merit >= 1.  (Up to and including 196 bits,
     merit >= 3.)  */

  {32, "43840821", 	     1},
  {33, "85943917", 	     1},
  {34, "171799469", 	     1},
  {35, "343825285", 	     1},
  {36, "687285701", 	     1},
  {37, "1374564613", 	     1},
  {38, "2749193437", 	     1},
  {39, "5497652029", 	     1},
  {40, "10995212661", 	     1},
  {56, "47988680294711517",  1},
  {64, "13469374875402548381", 1},
  {100, "203786806069096950756900463357", 1},	
  {128, "96573135900076068624591706046897650309", 1},
  {156, "43051576988660538262511726153887323360449035333", 1},
  {196, "1611627857640767981443524165616850972435303571524033586421", 1},
  {200, "491824250216153841876046962368396460896019632211283945747141", 1},
  {256, "79336254595106925775099152154558630917988041692672147726148065355845551082677", 1},
  {0, NULL, 0}			/* End of array. */
};

void
#if __STDC__
gmp_rand_init (gmp_rand_state s,
	       unsigned long int size,
	       gmp_rand_algorithm alg)
#else
gmp_rand_init (s, size, alg)
     gmp_rand_state s;
     unsigned long int size;
     gmp_rand_algorithm alg;
#endif
{
  switch (alg)
    {
    case GMP_RAND_ALG_LC:	/* Linear congruential.  */
      {
	__gmp_rand_lc_scheme_struct *sp;
	mpz_t a;


	/* Pick a scheme.  */
	for (sp = __gmp_rand_scheme; sp->m2exp != 0; sp++)
	  if (sp->m2exp / 2 >= size)
	    break;

	if (sp->m2exp == 0)	/* Nothing big enough found.  */
	  {
	    gmp_errno |= GMP_ERROR_INVALID_ARGUMENT;
	    return;
	  }

	/* Install scheme.  */
	mpz_init_set_str (a, sp->astr, 0);
	gmp_rand_init_lc_2exp (s, a, sp->c, sp->m2exp);
	
	break;
      }

#if 0
    case GMP_RAND_ALG_BBS:	/* Blum, Blum, and Shub. */
      {				
	mpz_t p, q;
	mpz_t ztmp;

	/* FIXME: Generate p and q.  They must be ``large'' primes,
           congruent to 3 mod 4.  Should we ensure that they meet some
           of the criterias for being ``hard primes''?*/

	/* These are around 128 bits. */
	mpz_init_set_str (p, "148028650191182616877187862194899201391", 10); 
	mpz_init_set_str (q, "315270837425234199477225845240496832591", 10);
	
	/* Allocate algorithm specific data. */
	s->data.bbs = (__gmp_rand_data_bbs *)
	  (*_mp_allocate_func) (sizeof (__gmp_rand_data_bbs));

	mpz_init (s->data.bbs->bi); /* The Blum integer. */
	mpz_mul (s->data.bbs->bi, p, q);

	/* Find a seed, x, with gcd (x, bi) == 1. */
	mpz_init (ztmp);
	while (1)
	  {
	    mpz_gcd (ztmp, seed, s->data.bbs->bi);
	    if (!mpz_cmp_ui (ztmp, 1))
	      break;
	    mpz_add_ui (seed, seed, 1);
	  }

	s->alg = alg;
	s->size = size;		/* FIXME: Remove. */
	mpz_set (s->seed, seed);

	mpz_clear (p);
	mpz_clear (q);
	mpz_clear (ztmp);
	break;
      }
#endif /* 0 */

    default:			/* Bad choice. */
      gmp_errno |= GMP_ERROR_UNSUPPORTED_ARGUMENT;
    }
}
