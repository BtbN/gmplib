/* Exercise mpz_probab_prime_p.

Copyright 2002, 2018-2019, 2022 Free Software Foundation, Inc.

This file is part of the GNU MP Library test suite.

The GNU MP Library test suite is free software; you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 3 of the License,
or (at your option) any later version.

The GNU MP Library test suite is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General
Public License for more details.

You should have received a copy of the GNU General Public License along with
the GNU MP Library test suite.  If not, see https://www.gnu.org/licenses/.  */

#include <stdio.h>
#include <stdlib.h>
#include "gmp-impl.h"
#include "tests.h"

#ifndef GMP_ENABLE_PROTH_TEST
#define GMP_ENABLE_PROTH_TEST 1
#endif

/* Enhancements:

   - Test some big primes don't come back claimed to be composite.
   - Test some big composites don't come back claimed to be certainly prime.
   - Test some big composites with small factors are identified as certainly
     composite.  */


/* return 2 if prime, 0 if composite */
int
isprime (unsigned long n)
{
  if (n < 4)
    return (n & 2);
  if ((n & 1) == 0)
    return 0;

  for (unsigned long i = 3; i*i <= n; i+=2)
    if ((n % i) == 0)
      return 0;

  return 2;
}

void
check_one (mpz_srcptr n, int want, char a)
{
  int  got;

  got = mpz_probab_prime_p (n, 25);

  /* "definitely prime" (2) is fine if we only wanted "probably prime" (1) */
  if ((got != want) && (got != want * 2))
    {
      printf ("mpz_probab_prime_p (%c)\n", a);
      mpz_trace ("  n    ", n);
      printf    ("  got =%d", got);
      printf    ("  want=%d", want);
      abort ();
    }
}

void
check_pn (mpz_ptr n, int want)
{
  check_one (n, want, '+');
  mpz_neg (n, n);
  check_one (n, want, '-');
}

/* expect certainty for small n */
void
check_small (void)
{
  mpz_t  n;
  long   i;

  mpz_init (n);

  for (i = 0; i < 300; i++)
    {
      mpz_set_si (n, i);
      check_pn (n, isprime (i));
    }

  mpz_clear (n);
}

void
check_proth_fixed ()
{
  static const struct {
    char*        k;
    mp_bitcnt_t  n;
    int       want;
  } data [] = {
    {"18975", 16, 1}, /* prime, b=61 */
    {"642497427", 34, 1}, /* prime, b=107 */
    {"430341165", 32, 0}, /* composite, b=113 */
    {"3432101253", 32, 1}, /* prime, b=113 */
    {"67067655", 64, 1}, /* prime, b=103 */
    {"117377265", 64, 0}, /* composite, b=113 */
    {"4654135305", 63, 1}, /* prime, b=107 */
    {"3836987091", 63, 0}, /* composite, b=131 */
    {"11838137235", 63, 1}, /* prime, b=109 */
    {"6269603373", 64, 0}, /* composite, b=137 */
    {"1300166691", 67, 1}, /* prime, b=113 */
    {"11257223805", 65, 0}, /* composite, b=151 */
    {"71459624811", 63, 1}, /* prime, b=137 */
    {"59242853985", 64, 0}, /* composite, b=157 */
    {"25739539989", 65, 1}, /* prime, b=139 */
    {"59242853985", 65, 0}, /* composite, b=179 */
    {"6148401", 103, 0}, /* composite, b=101 */
    {"69646689", 101, 1}, /* prime, b=97 */
  };
  mpz_t n;
  mpz_init (n);

  for (int i = 0; i < numberof (data); ++i) {
    mpz_set_str (n, data[i].k, 10);
    mpz_mul_2exp (n, n, data[i].n);
    int want = data[i].want << GMP_ENABLE_PROTH_TEST;
    mpz_add_ui (n, n, 1);

    check_one (n, want, 'h');
  }

  mpz_clear (n);
}

void
check_proth (gmp_randstate_ptr rands, int count)
{
  /* Exponents such that k*2^n + 1 is prime, with
     odd 2 < k < 18, and k < 2^n < 2^(2^14 + 10).
     Sequences where recomputed, but checked with OEIS. */
#define DATA_END 32767
  /* 3 * 2^n + 1, OEIS A002253 */
  static const unsigned data3[] = {
    2, 5, 6, 8, 12, 18, 30, 36, 41, 66, 189, 201, 209, 276, 353,
    408, 438, 534, 2208, 2816, 3168, 3189, 3912, DATA_END};
  /* 5 * 2^n + 1, OEIS A002254 */
  static const unsigned data5[] = {
    3, 7, 13, 15, 25, 39, 55, 75, 85, 127, 1947,
    3313, 4687, 5947, 13165, DATA_END};
  /* 7 * 2^n + 1, OEIS A002255 */
  static const unsigned data7[] = {
    4, 6, 14, 20, 26, 50, 52, 92, 120, 174, 180, 190, 290, 320,
    390, 432, 616, 830, 1804, 2256, 6614, 13496, 15494, DATA_END};
  /* 9 * 2^n + 1, OEIS A002256 */
  static const unsigned data9[] = {
    6, 7, 11, 14, 17, 33, 42, 43, 63, 65, 67, 81, 134, 162, 206,
    211, 366, 663, 782, 1305, 1411, 1494, 2297, 2826, 3230, 3354,
    3417, 3690, 4842, 5802, 6937, 7967, 9431, 13903, DATA_END};
  /* 11 * 2^n + 1, OEIS A002261 */
  static const unsigned data11[] = {
    5, 7, 19, 21, 43, 81, 125, 127, 209, 211, 3225,
    4543, 10179, 15329, DATA_END};
  /* 13 * 2^n + 1, OEIS A002257 */
  static const unsigned data13[] = {
    8, 10, 20, 28, 82, 188, 308, 316, 1000, DATA_END};
  /* 15 * 2^n + 1, OEIS A002258 */
  static const unsigned data15[] = {
    4, 9, 10, 12, 27, 37, 38, 44, 48, 78, 112, 168, 229, 297,
    339, 517, 522, 654, 900, 1518, 2808, 2875, 3128, 3888,
    4410, 6804, 7050, 7392, DATA_END};
  /* 17 * 2^n + 1, OEIS A002259 */
  static const unsigned data17[] = {
    15, 27, 51, 147, 243, 267, 347, 471, 747, 2163,
    3087, 5355, 6539, 7311, DATA_END};
  static const unsigned *data[8] = {
    data3, data5, data7, data9, data11, data13, data15, data17
  };

  mpz_t n;
  mpz_init (n);

  unsigned bits = 10;
  while ((count >> bits) > 2)
    {
      count >>= 1;
      ++bits;
      if (bits > 13)
	break;
    }

  for (int i = count; i != 0; --i) {
    unsigned long k = gmp_urandomb_ui (rands, 3); /* 0..7 */
    const unsigned *exponents = data[k];
    mpz_set_ui (n, 2 * k + 3); /* 3..17, odd */

    unsigned shift = gmp_urandomb_ui (rands, bits) + mpz_sizeinbase (n, 2);
    mpz_mul_2exp (n, n, shift);
    mpz_add_ui (n, n, 1);

    int want;
    for (unsigned j = 0; ; ++j)
      if (shift <= exponents[j])
	{
	  want = (shift == exponents[j]) << GMP_ENABLE_PROTH_TEST;
	  break;
	}

    /* count -= shift >> (6 + GMP_ENABLE_PROTH_TEST); */
    check_one (n, want, 'H');
  }

  mpz_clear (n);
}

void
check_composites (gmp_randstate_ptr rands, int count)
{
  int i;
  mpz_t a, b, n, bs;
  unsigned long size_range, size;

  mpz_init (a);
  mpz_init (b);
  mpz_init (n);
  mpz_init (bs);

  static const char * const composites[] = {
    "225670644213750121",	/* n=61*C16, if D < 61, (n/D) = 1.	*/
    "2386342059899637841",	/* n=61*C17, if D < 61, (n/D) = 1.	*/
    "1194649",	/* A square, but strong base-2 pseudoprime,	*/
    "12327121",	/* another base-2 pseudoprime square.	*/
    "18446744066047760377",	/* Should trigger Fibonacci's test;	*/
    "10323769",			/* &3==1, Lucas' test with D=37;	*/
    "1397419",			/* &3==3, Lucas' test with D=43;	*/
    "11708069165918597341",	/* &3==1, Lucas' test with large D=107;	*/
    "395009109077493751",	/* &3==3, Lucas' test with large D=113.	*/
    NULL
  };

  for (i = 0; composites[i]; i++)
    {
      mpz_set_str_or_abort (n, composites[i], 0);
      check_one (n, 0, 'c');
    }

  for (i = 0; i < count; i++)
    {
      mpz_urandomb (bs, rands, 32);
      size_range = mpz_get_ui (bs) % 13 + 1; /* 0..8192 bit operands */

      mpz_urandomb (bs, rands, size_range);
      size = mpz_get_ui (bs);
      mpz_rrandomb (a, rands, size);

      mpz_urandomb (bs, rands, 32);
      size_range = mpz_get_ui (bs) % 13 + 1; /* 0..8192 bit operands */
      mpz_rrandomb (b, rands, size);

      /* Exclude trivial factors */
      if (mpz_cmp_ui (a, 1) == 0)
	mpz_set_ui (a, 2);
      if (mpz_cmp_ui (b, 1) == 0)
	mpz_set_ui (b, 2);

      mpz_mul (n, a, b);

      check_pn (n, 0);
    }
  mpz_clear (a);
  mpz_clear (b);
  mpz_clear (n);
  mpz_clear (bs);
}

static void
check_primes (void)
{
  static const char * const primes[] = {
    "2", "53", "1234567891",
    "2055693949", "1125899906842597", "16412292043871650369",
    "18446744075358702679",	/* Lucas' test with large D=107.	*/
    /* diffie-hellman-group1-sha1, also "Well known group 2" in RFC
       2412, 2^1024 - 2^960 - 1 + 2^64 * { [2^894 pi] + 129093 } */
    "0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD1"
    "29024E088A67CC74020BBEA63B139B22514A08798E3404DD"
    "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245"
    "E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED"
    "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE65381"
    "FFFFFFFFFFFFFFFF",
    NULL
  };

  mpz_t n;
  int i;

  mpz_init (n);

  for (i = 0; primes[i]; i++)
    {
      mpz_set_str_or_abort (n, primes[i], 0);
      check_one (n, 1, 'p');
    }
  mpz_clear (n);
}

static void
check_fermat_mersenne (int count)
{
  int fermat_exponents [] = {1, 2, 4, 8, 16};
  int mersenne_exponents [] = {2, 3, 5, 7, 13, 17, 19, 31, 61, 89,
			       107, 127, 521, 607, 1279, 2203, 2281,
			       3217, 4253, 4423, 9689, 9941, 11213,
			       19937, 21701, 23209, 44497, 86243};
  mpz_t pp, sq;
  int i, j, want;

  mpz_init (pp);
  mpz_init (sq);
  count = MIN (110000, count);

  for (i=1; i<count; ++i)
    {
      mpz_set_ui (pp, 1);
      mpz_setbit (pp, i); /* 2^i + 1 */
      want = 0;
      for (j = 0; j < numberof (fermat_exponents); j++)
	if (fermat_exponents[j] == i)
	  {
	    /* Fermat's primes are small enough for a definite answer. */
	    want = 2;
	    break;
	  }
      check_one (pp, want, 'f');

      mpz_mul (sq, pp, pp); /* The square is a */
      want = 0;      /* non-prime Proth number */
      check_one (sq, want, 's');

      mpz_sub_ui (pp, pp, 2); /* 2^i - 1 */
      want = 0;
      for (j = 0; j < numberof (mersenne_exponents); j++)
	if (mersenne_exponents[j] == i)
	  {
	    want = 1 << (i < 50);
	    break;
	  }
      check_one (pp, want, 'm');

      mpz_mul (sq, pp, pp); /* The square is a */
      want = 0;      /* non-prime Proth number */
      check_one (sq, want, 'S');
    }
  mpz_clear (pp);
  mpz_clear (sq);
}

int
main (int argc, char **argv)
{
  int count = 1000;
  gmp_randstate_ptr rands;

  TESTS_REPS (count, argv, argc);

  tests_start ();

  check_small ();
  check_fermat_mersenne (count >> 3);
  rands = RANDS;
  check_composites (rands, count);
  check_primes ();
  check_proth_fixed ();
  check_proth (rands, count);

  tests_end ();
  exit (0);
}
