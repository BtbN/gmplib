/* Test mpq_mul_2exp and mpq_div_2exp.

Copyright (C) 2000 Free Software Foundation, Inc.

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

#include <stdio.h>
#include <stdlib.h>
#include "gmp.h"
#include "gmp-impl.h"


struct pair_t {
  const char     *num;
  const char     *den;
};

int
main (void)
{
  struct {
    struct pair_t  left;
    unsigned long  n;
    struct pair_t  right;

  } data[] = {
    { {"0","1"}, 0, {"0","1"} },
    { {"0","1"}, 1, {"0","1"} },
    { {"0","1"}, 2, {"0","1"} },

    { {"1","1"}, 0, {"1","1"} },
    { {"1","1"}, 1, {"2","1"} },
    { {"1","1"}, 2, {"4","1"} },
    { {"1","1"}, 3, {"8","1"} },

    { {"1","1"}, 31, {"0x80000000","1"} },
    { {"1","1"}, 32, {"0x100000000","1"} },
    { {"1","1"}, 33, {"0x200000000","1"} },
    { {"1","1"}, 63, {"0x8000000000000000","1"} },
    { {"1","1"}, 64, {"0x10000000000000000","1"} },
    { {"1","1"}, 65, {"0x20000000000000000","1"} },
    { {"1","1"}, 95, {"0x800000000000000000000000","1"} },
    { {"1","1"}, 96, {"0x1000000000000000000000000","1"} },
    { {"1","1"}, 97, {"0x2000000000000000000000000","1"} },
    { {"1","1"}, 127, {"0x80000000000000000000000000000000","1"} },
    { {"1","1"}, 128, {"0x100000000000000000000000000000000","1"} },
    { {"1","1"}, 129, {"0x200000000000000000000000000000000","1"} },

    { {"1","2"}, 31, {"0x40000000","1"} },
    { {"1","2"}, 32, {"0x80000000","1"} },
    { {"1","2"}, 33, {"0x100000000","1"} },
    { {"1","2"}, 63, {"0x4000000000000000","1"} },
    { {"1","2"}, 64, {"0x8000000000000000","1"} },
    { {"1","2"}, 65, {"0x10000000000000000","1"} },
    { {"1","2"}, 95, {"0x400000000000000000000000","1"} },
    { {"1","2"}, 96, {"0x800000000000000000000000","1"} },
    { {"1","2"}, 97, {"0x1000000000000000000000000","1"} },
    { {"1","2"}, 127, {"0x40000000000000000000000000000000","1"} },
    { {"1","2"}, 128, {"0x80000000000000000000000000000000","1"} },
    { {"1","2"}, 129, {"0x100000000000000000000000000000000","1"} },

    { {"1","0x80000000"}, 30, {"1","2"} },
    { {"1","0x80000000"}, 31, {"1","1"} },
    { {"1","0x80000000"}, 32, {"2","1"} },
    { {"1","0x80000000"}, 33, {"4","1"} },
    { {"1","0x80000000"}, 62, {"0x80000000","1"} },
    { {"1","0x80000000"}, 63, {"0x100000000","1"} },
    { {"1","0x80000000"}, 64, {"0x200000000","1"} },
    { {"1","0x80000000"}, 94, {"0x8000000000000000","1"} },
    { {"1","0x80000000"}, 95, {"0x10000000000000000","1"} },
    { {"1","0x80000000"}, 96, {"0x20000000000000000","1"} },
    { {"1","0x80000000"}, 126, {"0x800000000000000000000000","1"} },
    { {"1","0x80000000"}, 127, {"0x1000000000000000000000000","1"} },
    { {"1","0x80000000"}, 128, {"0x2000000000000000000000000","1"} },

    { {"1","0x100000000"}, 1, {"1","0x80000000"} },
    { {"1","0x100000000"}, 2, {"1","0x40000000"} },
    { {"1","0x100000000"}, 3, {"1","0x20000000"} },

    { {"1","0x10000000000000000"}, 1, {"1","0x8000000000000000"} },
    { {"1","0x10000000000000000"}, 2, {"1","0x4000000000000000"} },
    { {"1","0x10000000000000000"}, 3, {"1","0x2000000000000000"} },
  };

  void (*fun) _PROTO ((mpq_ptr, mpq_srcptr, unsigned long));
  const struct pair_t  *p_start, *p_want;
  const char  *name;
  mpq_t    sep, got, want;
  mpq_ptr  q;
  int      i, muldiv, sign, overlap;

  mpq_init (sep);
  mpq_init (got);
  mpq_init (want);

  for (i = 0; i < numberof (data); i++)
    {
      for (muldiv = 0; muldiv < 2; muldiv++)
        {
          if (muldiv == 0)
            {
              fun = mpq_mul_2exp;
              name = "mpq_mul_2exp";
              p_start = &data[i].left;
              p_want = &data[i].right;
            }
          else
            {
              fun = mpq_div_2exp;
              name = "mpq_div_2exp";
              p_start = &data[i].right;
              p_want = &data[i].left;
            }

          for (sign = 0; sign <= 1; sign++)
            {
              MPZ_SET_STR_OR_ABORT (mpq_numref(want), p_want->num, 0);
              MPZ_SET_STR_OR_ABORT (mpq_denref(want), p_want->den, 0);
              if (sign)
                mpq_neg (want, want);

              for (overlap = 0; overlap <= 1; overlap++)
                {
                  q = overlap ? got : sep;

                  /* initial garbage in "got" */
                  mpq_set_ui (got, 123L, 456L);

                  MPZ_SET_STR_OR_ABORT (mpq_numref(q), p_start->num, 0);
                  MPZ_SET_STR_OR_ABORT (mpq_denref(q), p_start->den, 0);
                  if (sign)
                    mpq_neg (q, q);

                  (*fun) (got, q, data[i].n);
                  MPQ_CHECK_FORMAT (got);

                  if (! mpq_equal (got, want))
                    {
                      printf ("%s wrong at data[%d], sign %d, overlap %d\n",
                              name, i, sign, overlap);
                      printf ("   num \"%s\"\n", p_start->num);
                      printf ("   den \"%s\"\n", p_start->den);
                      printf ("   n   %lu\n", data[i].n);

                      printf ("   got  ");
                      mpq_out_str (stdout, 16, got);
                      printf (" (hex)\n");

                      printf ("   want ");
                      mpq_out_str (stdout, 16, want);
                      printf (" (hex)\n");

                      abort ();
                    }
                }
            }
        }
    }

  exit (0);
}
