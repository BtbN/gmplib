/* mpf_fits_s*_p -- test whether an mpf fits a C signed type.

Copyright 2001 Free Software Foundation, Inc.

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


/* Notice this is equivalent to mpz_set_f + mpz_fits_s*_p.  */

int
FUNCTION (mpf_srcptr f)
{
  int        size, abs_size, i;
  mp_exp_t   exp;
  mp_srcptr  ptr;

  size = SIZ(f);
  if (size == 0)
    return 1;  /* zero fits */

  exp = EXP(f);
  if (exp != 1)  /* only 1 limb above the radix point */
    return 0;

  /* any fraction limbs must be zero */
  abs_size = ABS(size);
  ptr = PTR(f);
  for (i = 0; i < abs_size-1; i++)
    if (ptr[i] != 0)
      return 0;

  return ptr[abs_size-1]
    <= (size > 0 ? (mp_limb_t) MAXIMUM : - (mp_limb_t) MINIMUM);
}
