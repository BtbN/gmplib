dnl  GMP specific autoconf macros


dnl  Copyright 2000, 2001 Free Software Foundation, Inc.
dnl
dnl  This file is part of the GNU MP Library.
dnl
dnl  The GNU MP Library is free software; you can redistribute it and/or modify
dnl  it under the terms of the GNU Lesser General Public License as published
dnl  by the Free Software Foundation; either version 2.1 of the License, or (at
dnl  your option) any later version.
dnl
dnl  The GNU MP Library is distributed in the hope that it will be useful, but
dnl  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
dnl  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
dnl  License for more details.
dnl
dnl  You should have received a copy of the GNU Lesser General Public License
dnl  along with the GNU MP Library; see the file COPYING.LIB.  If not, write to
dnl  the Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
dnl  MA 02111-1307, USA.


define(X86_PATTERN,
[[i?86*-*-* | k[5-8]*-*-* | pentium*-*-* | athlon-*-*]])


dnl  GMP_HEADER_GETVAL(NAME,FILE)
dnl  ----------------------------
dnl
dnl  Expand at autoconf time to the value of a "#define NAME" from the given
dnl  FILE.  The regexps here aren't very rugged, but are enough for gmp.
dnl  /dev/null as a parameter prevents a hang if $2 is accidentally omitted.

define(GMP_HEADER_GETVAL,
[patsubst(patsubst(
esyscmd([grep "^#define $1 " $2 /dev/null 2>/dev/null]),
[^.*$1[ 	]+],[]),
[[
 	]*$],[])])


dnl  GMP_VERSION
dnl  -----------
dnl
dnl  The gmp version number, extracted from the #defines in gmp-h.in at
dnl  autoconf time.  Two digits like 3.0 if patchlevel <= 0, or three digits
dnl  like 3.0.1 if patchlevel > 0.

define(GMP_VERSION,
[GMP_HEADER_GETVAL(__GNU_MP_VERSION,gmp-h.in)[]dnl
.GMP_HEADER_GETVAL(__GNU_MP_VERSION_MINOR,gmp-h.in)[]dnl
ifelse(m4_eval(GMP_HEADER_GETVAL(__GNU_MP_VERSION_PATCHLEVEL,gmp-h.in) > 0),1,
[.GMP_HEADER_GETVAL(__GNU_MP_VERSION_PATCHLEVEL,gmp-h.in)])])


dnl  GMP_COMPARE_GE(A1,B1, A2,B2, ...)
dnl  ---------------------------------
dnl
dnl  Compare two version numbers A1.A2.etc and B1.B2.etc.  Set
dnl  $gmp_compare_ge to yes or no accoring to the result.  The A parts
dnl  should be variables, the B parts fixed numbers.  As many parts as
dnl  desired can be included.  An empty string in an A part is taken to be
dnl  zero, the B parts should be non-empty and non-zero.
dnl
dnl  For example,
dnl
dnl      GMP_COMPARE($major,10, $minor,3, $subminor,1)
dnl
dnl  would test whether $major.$minor.$subminor is greater than or equal to
dnl  10.3.1.

AC_DEFUN(GMP_COMPARE_GE,
[gmp_compare_ge=no
GMP_COMPARE_GE_INTERNAL($@)
])

AC_DEFUN(GMP_COMPARE_GE_INTERNAL,
[ifelse(len([$3]),0,
[if test -n "$1" && test "$1" -ge $2; then
  gmp_compare_ge=yes
fi],
[if test -n "$1"; then
  if test "$1" -gt $2; then
    gmp_compare_ge=yes
  else
    if test "$1" -eq $2; then
      GMP_COMPARE_GE_INTERNAL(m4_shift(m4_shift($@)))
    fi
  fi
fi])
])
  

dnl  GMP_PROG_AR
dnl  -----------
dnl  GMP additions to $AR.
dnl
dnl  A cross-"ar" may be necessary when cross-compiling since the build
dnl  system "ar" might try to interpret the object files to build a symbol
dnl  table index, hence the use of AC_CHECK_TOOL.
dnl
dnl  A user-selected $AR is always left unchanged.  AC_CHECK_TOOL is still
dnl  run to get the "checking" message printed though.

AC_DEFUN(GMP_PROG_AR,
[dnl  Want to establish $AR before libtool initialization.
AC_BEFORE([$0],[AC_PROG_LIBTOOL])
gmp_user_AR=$AR
AC_CHECK_TOOL(AR, ar, ar)
if test -z "$gmp_user_AR"; then
                        eval arflags=\"\$ar${abi1}_flags\"
  test -n "$arflags" || eval arflags=\"\$ar${abi2}_flags\"
  if test -n "$arflags"; then
    AR="$AR $arflags"
  fi
fi
])


dnl  GMP_PROG_M4
dnl  -----------
dnl
dnl  Find a working m4, either in $PATH or likely locations, and setup $M4
dnl  and an AC_SUBST accordingly.  If $M4 is already set then it's a user
dnl  choice and is accepted with no checks.  GMP_PROG_M4 is like
dnl  AC_PATH_PROG or AC_CHECK_PROG, but tests each m4 found to see if it's
dnl  good enough.
dnl 
dnl  See mpn/asm-defs.m4 for details on the known bad m4s.

AC_DEFUN(GMP_PROG_M4,
[AC_ARG_VAR(M4,[m4 macro processor])
AC_CACHE_CHECK([for suitable m4],
                gmp_cv_prog_m4,
[if test -n "$M4"; then
  gmp_cv_prog_m4="$M4"
else
  cat >conftest.m4 <<\EOF
dnl  Must protect this against being expanded during autoconf m4!
dnl  Dont put "dnl"s in this as autoconf will flag an error for unexpanded
dnl  macros.
[define(dollarhash,``$][#'')ifelse(dollarhash(x),1,`define(t1,Y)',
``bad: $][# not supported (SunOS /usr/bin/m4)
'')ifelse(eval(89),89,`define(t2,Y)',
`bad: eval() doesnt support 8 or 9 in a constant (OpenBSD 2.6 m4)
')ifelse(t1`'t2,YY,`good
')]
EOF
dnl ' <- balance the quotes for emacs sh-mode
  echo "trying m4" >&AC_FD_CC
  gmp_tmp_val=`(m4 conftest.m4) 2>&AC_FD_CC`
  echo "$gmp_tmp_val" >&AC_FD_CC
  if test "$gmp_tmp_val" = good; then
    gmp_cv_prog_m4="m4"
  else
    IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS=":"
dnl $ac_dummy forces splitting on constant user-supplied paths.
dnl POSIX.2 word splitting is done only on the output of word expansions,
dnl not every word.  This closes a longstanding sh security hole.
    ac_dummy="$PATH:/usr/5bin"
    for ac_dir in $ac_dummy; do
      test -z "$ac_dir" && ac_dir=.
      echo "trying $ac_dir/m4" >&AC_FD_CC
      gmp_tmp_val=`($ac_dir/m4 conftest.m4) 2>&AC_FD_CC`
      echo "$gmp_tmp_val" >&AC_FD_CC
      if test "$gmp_tmp_val" = good; then
        gmp_cv_prog_m4="$ac_dir/m4"
        break
      fi
    done
    IFS="$ac_save_ifs"
    if test -z "$gmp_cv_prog_m4"; then
      AC_MSG_ERROR([No usable m4 in \$PATH or /usr/5bin (see config.log for reasons).])
    fi
  fi
  rm -f conftest.m4
fi])
M4="$gmp_cv_prog_m4"
AC_SUBST(M4)
])


dnl  GMP_M4_M4WRAP_SPURIOUS
dnl  ----------------------
dnl  Check for the spurious output from m4wrap(), noted in mpn/asm-defs.m4.
dnl
dnl  The following systems have been seen with the problem.
dnl
dnl  - Alpha Unicos, but its assembler doesn't seem to mind.
dnl  - MacOS X (darwin), its assembler fails.
dnl  - NetBSD 1.4.1 m68k, and gas 1.92.3 on that system gives a warning and
dnl    ignores the last line since it doesn't have a newline.
dnl
dnl  Enhancement: Maybe this could be in GMP_PROG_M4, and attempt to prefer
dnl  an m4 with a working m4wrap, if it can be found.

AC_DEFUN(GMP_M4_M4WRAP_SPURIOUS,
[AC_REQUIRE([GMP_PROG_M4])
AC_CACHE_CHECK([if m4wrap produces spurious output],
               gmp_cv_m4_m4wrap_spurious,
[# hide the d-n-l from autoconf's error checking
tmp_d_n_l=d""nl
cat >conftest.m4 <<EOF
[changequote({,})define(x,)m4wrap({x})$tmp_d_n_l]
EOF
echo test input is >&AC_FD_CC
cat conftest.m4 >&AC_FD_CC
tmp_chars=`$M4 conftest.m4 | wc -c`
echo produces $tmp_chars chars output >&AC_FD_CC
rm -f conftest.m4
if test $tmp_chars = 0; then
  gmp_cv_m4_m4wrap_spurious=no
else
  gmp_cv_m4_m4wrap_spurious=yes
fi
])
GMP_DEFINE_RAW(["define(<M4WRAP_SPURIOUS>,<$gmp_cv_m4_m4wrap_spurious>)"])
])


dnl  GMP_PROG_NM
dnl  -----------
dnl  GMP additions to libtool AC_PROG_NM.
dnl
dnl  Note that if AC_PROG_NM can't find a working nm it still leaves
dnl  $NM set to "nm", so $NM can't be assumed to actually work.
dnl
dnl  A user-selected $NM is always left unchanged.  AC_PROG_NM is still run
dnl  to get the "checking" message printed though.

AC_DEFUN(GMP_PROG_NM,
[dnl  Make sure we're the first to call AC_PROG_NM, so our extra flags are
 dnl  used by everyone.
AC_BEFORE([$0],[AC_PROG_NM])
gmp_user_NM=$NM
AC_PROG_NM
if test -z "$gmp_user_NM"; then
                        eval nmflags=\"\$nm${abi1}_flags\"
  test -n "$nmflags" || eval nmflags=\"\$nm${abi2}_flags\"
  if test -n "$nmflags"; then
    NM="$NM $nmflags"
  fi
fi
])


dnl  GMP_PROG_CC_WORKS(cc/cflags,[ACTION-IF-WORKS][,ACTION-IF-NOT-WORKS])
dnl  --------------------------------------------------------------------
dnl  Check if CC/CFLAGS can compile and link.
dnl
dnl  This test is designed to be run repeatedly with different cc/cflags
dnl  selections, so the result is not cached.

AC_DEFUN(GMP_PROG_CC_WORKS,
[AC_MSG_CHECKING([compiler $1])
cat >conftest.c <<EOF
/* The following provokes an internal error from gcc 2.95.2 -mpowerpc64
   (without -maix64), hence detecting an unusable compiler */
void *g() { return (void *) 0; }
void *f() { return g(); }

int main () { return 0; }
EOF
gmp_compile="$1 conftest.c >&AC_FD_CC"
if AC_TRY_EVAL(gmp_compile); then
  rm -f conftest* a.out
  AC_MSG_RESULT(yes)
  ifelse([$2],,:,[$2])
else
  rm -f conftest* a.out
  AC_MSG_RESULT(no)
  ifelse([$3],,:,[$3])
fi
])


dnl  GMP_PROG_CC_IS_GNU(CC,[ACTIONS-IF-YES][,ACTIONS-IF-NO])
dnl  -------------------------------------------------------
dnl  Determine whether the given compiler is GNU C.
dnl
dnl  This test is the same as autoconf _AC_LANG_COMPILER_GNU, but doesn't
dnl  cache the result.  The same "ifndef" style test is used, to avoid
dnl  problems with syntax checking cpp's used on NeXT and Apple systems.

AC_DEFUN(GMP_PROG_CC_IS_GNU,
[cat >conftest.c <<EOF
#ifndef __GNUC__
  choke me
#endif
EOF
gmp_compile="$1 -c conftest.c"
if AC_TRY_EVAL(gmp_compile); then
  rm -f conftest*
  ifelse([$2],,:,[$2])
else
  rm -f conftest*
  ifelse([$3],,:,[$3])
fi
])


dnl  GMP_HPC_HPPA_2_0(cc,[ACTION-IF-GOOD][,ACTION-IF-BAD])
dnl  ---------------------------------------------------------
dnl  Find out whether a HP compiler is good enough to generate hppa 2.0.
dnl
dnl  This test might be repeated for different compilers, so the result is
dnl  not cached.

AC_DEFUN(GMP_HPC_HPPA_2_0,
[AC_MSG_CHECKING([whether HP compiler $1 is good for 64-bits])
# Bad compiler output:
#   ccom: HP92453-01 G.10.32.05 HP C Compiler
# Good compiler output:
#   ccom: HP92453-01 A.10.32.30 HP C Compiler
# Let A.10.32.30 or higher be ok.
echo >conftest.c
gmp_tmp_vs=`$1 $2 -V -c -o conftest.o conftest.c 2>&1 | grep "^ccom:"`
rm conftest*
gmp_tmp_v1=`echo $gmp_tmp_vs | sed 's/.* .\.\(.*\)\..*\..* HP C.*/\1/'`
gmp_tmp_v2=`echo $gmp_tmp_vs | sed 's/.* .\..*\.\(.*\)\..* HP C.*/\1/'`
gmp_tmp_v3=`echo $gmp_tmp_vs | sed 's/.* .\..*\..*\.\(.*\) HP C.*/\1/'`
if test -z "$gmp_tmp_v1"; then
  gmp_hpc_64bit=not-applicable
else
  GMP_COMPARE_GE($gmp_tmp_v1, 10, $gmp_tmp_v2, 32, $gmp_tmp_v3, 30)
  gmp_hpc_64bit=$gmp_compare_ge
fi
AC_MSG_RESULT($gmp_hpc_64bit)
if test $gmp_hpc_64bit = yes; then
  ifelse([$2],,:,[$2])
else
  ifelse([$3],,:,[$3])
fi
])


dnl  GMP_GCC_VERSION_GE(CC,MAJOR[,MINOR[,SUBMINOR]])
dnl  -----------------------------------------------
dnl
dnl  Test whether the version of CC (which must be GNU C) is >=
dnl  MAJOR.MINOR.SUBMINOR.  Set $gmp_compare_ge to "yes" or "no"
dnl  accordingly, or to "error" if the version number string can't be
dnl  parsed.
dnl
dnl  gcc --version is normally just "2.7.2.3" or "2.95.3" or whatever, but
dnl  egcs gives something like "egcs-2.91".  sed doesn't support "?" so a
dnl  pattern "(egcs-)*" is used.
dnl
dnl  There's no caching here, so that different CC's can be tested.

AC_DEFUN(GMP_GCC_VERSION_GE,
[tmp_version=`($1 --version) 2>&AC_FD_CC`
echo "$1 --version '$tmp_version'" >&AC_FD_CC

major=`(echo "$tmp_version" | sed -n ['s/^\(egcs-\)*\([0-9][0-9]*\).*/\2/p']) 2>&AC_FD_CC`
echo "    major '$major'" >&AC_FD_CC

ifelse([$3],,,
[minor=`(echo "$tmp_version" | sed -n ['s/^\(egcs-\)*[0-9][0-9]*\.\([0-9][0-9]*\).*/\2/p']) 2>&AC_FD_CC`
echo "    minor '$minor'" >&AC_FD_CC])

ifelse([$4],,,
[subminor=`(echo "$tmp_version" | sed -n ['s/^\(egcs-\)*[0-9][0-9]*\.[0-9][0-9]*\.\([0-9][0-9]*\).*/\2/p']) 2>&AC_FD_CC`
echo "    subminor '$subminor'" >&AC_FD_CC])

if test -z "$major"; then
  AC_MSG_WARN([unrecognised gcc version string: $tmp_version])
  gmp_compare_ge=error
else
  ifelse([$3],, [GMP_COMPARE_GE($major, $2)],
  [ifelse([$4],,[GMP_COMPARE_GE($major, $2, $minor, $3)],
                [GMP_COMPARE_GE($major, $2, $minor, $3, $subminor, $4)])])
fi
])


dnl  GMP_GCC_ARM_UMODSI(CC,[ACTIONS-IF-GOOD][,ACTIONS-IF-BAD])
dnl  ---------------------------------------------------------
dnl
dnl  gcc 2.95.3 and earlier on arm has a bug in the libgcc __umodsi routine
dnl  making "%" give wrong results for some operands, eg. "0x90000000 % 3".
dnl  We're hoping it'll be fixed in 2.95.4, and we know it'll be fixed in
dnl  gcc 3.
dnl
dnl  There's only a couple of places gmp cares about this, one is the
dnl  size==1 case in mpn/generic/mode1o.c, and this shows up in
dnl  tests/mpz/t-jac.c as a wrong result from mpz_kronecker_ui.

AC_DEFUN(GMP_GCC_ARM_UMODSI,
[AC_MSG_CHECKING([whether gcc unsigned division works])
GMP_GCC_VERSION_GE([$1], 2,95,4)
case $gmp_compare_ge in
yes)
  ifelse([$2],,:,[$2])
  gmp_gcc_arm_umodsi_result=yes ;;
*)
  ifelse([$3],,:,[$3])
  gmp_gcc_arm_umodsi_result="no, gcc <= 2.95.3" ;;
esac
AC_MSG_RESULT([$gmp_gcc_arm_umodsi_result])
])


dnl  GMP_GCC_MARCH_PENTIUMPRO(CC,[ACTIONS-IF-GOOD][,ACTIONS-IF-BAD])
dnl  ---------------------------------------------------------------
dnl
dnl  mpz/powm.c swox cvs rev 1.4 tickled a bug in gcc 2.95.2 when
dnl  -march=pentiumpro was used.  The problem appears to be fixed in 2.96,
dnl  so that option is used only on 2.96 and up.
dnl
dnl  The bug was incorrect code generated for a simple ABSIZ(z) expression
dnl  in mpz_redc(), some registers being clobbered near a cmov.  There's no
dnl  obvious reason for this, and there's many similar or identical
dnl  expressions throughout the library, so it seems wisest to disable
dnl  -march=pentiumpro until 2.96.
dnl
dnl  This macro is used only once, after finalizing a choice of CC, so the
dnl  result is cached.

AC_DEFUN(GMP_GCC_MARCH_PENTIUMPRO,
[AC_CACHE_CHECK([whether gcc -march=pentiumpro is good],
                gmp_cv_gcc_march_pentiumpro,
[GMP_GCC_VERSION_GE([$1], 2,96)
case $gmp_compare_ge in
yes|no)  gmp_cv_gcc_march_pentiumpro=$gmp_compare_ge ;;
error|*) gmp_cv_gcc_march_pentiumpro=no ;;
esac])
if test $gmp_cv_gcc_march_pentiumpro = yes; then
  ifelse([$2],,:,[$2])
else
  ifelse([$3],,:,[$3])
fi
])


dnl  GMP_GCC_M68K_OPTIMIZE(CCBASE,CC,FLAG-VARIABLE)
dnl  ----------------------------------------------
dnl  m68k gcc 2.95.x gets an internal compiler error when compiling the
dnl  current mpn/generic/gcdext.c (swox cvs rev 1.20) under -O2 or higher,
dnl  so just use -O for the offending gcc versions.  Naturally if gcdext.c
dnl  gets rearranged or rewritten so the ICE doesn't happen then this can be
dnl  removed.

AC_DEFUN(GMP_GCC_M68K_OPTIMIZE,
[case $host in
m68*-*-*)
  if test $1 = gcc; then
    case `$2 --version` in
    2.95*) $3=-O ;;
    esac
  fi
  ;;
esac
])


dnl  GMP_INIT([M4-DEF-FILE])
dnl  -----------------------
dnl  Initializations for GMP config.m4 generation.
dnl
dnl  FIXME: The generated config.m4 doesn't get recreated by config.status.
dnl  Maybe the relevant "echo"s should go through AC_CONFIG_COMMANDS.

AC_DEFUN(GMP_INIT,
[ifelse([$1], , gmp_configm4=config.m4, gmp_configm4="[$1]")
gmp_tmpconfigm4=cnfm4.tmp
gmp_tmpconfigm4i=cnfm4i.tmp
gmp_tmpconfigm4p=cnfm4p.tmp
rm -f $gmp_tmpconfigm4 $gmp_tmpconfigm4i $gmp_tmpconfigm4p

# CONFIG_TOP_SRCDIR is a path from the mpn builddir to the top srcdir.
# The pattern here tests for an absolute path the same way as
# _AC_OUTPUT_FILES in autoconf acgeneral.m4.
case $srcdir in
[[\\/]]* | ?:[[\\/]]* )  tmp="$srcdir"    ;;
*)                       tmp="../$srcdir" ;;
esac
echo ["define(<CONFIG_TOP_SRCDIR>,<\`$tmp'>)"] >>$gmp_tmpconfigm4

# All CPUs use asm-defs.m4 
echo ["include(CONFIG_TOP_SRCDIR\`/mpn/asm-defs.m4')"] >>$gmp_tmpconfigm4i
])


dnl  GMP_FINISH
dnl  ----------
dnl  Create config.m4 from its accumulated parts.
dnl
dnl  __CONFIG_M4_INCLUDED__ is used so that a second or subsequent include
dnl  of config.m4 is harmless.
dnl
dnl  A separate ifdef on the angle bracket quoted part ensures the quoting
dnl  style there is respected.  The basic defines from gmp_tmpconfigm4 are
dnl  fully quoted but are still put under an ifdef in case any have been
dnl  redefined by one of the m4 include files.
dnl
dnl  Doing a big ifdef within asm-defs.m4 and/or other macro files wouldn't
dnl  work, since it'd interpret parentheses and quotes in dnl comments, and
dnl  having a whole file as a macro argument would overflow the string space
dnl  on BSD m4.

AC_DEFUN(GMP_FINISH,
[AC_REQUIRE([GMP_INIT])
echo "creating $gmp_configm4"
echo ["d""nl $gmp_configm4.  Generated automatically by configure."] > $gmp_configm4
if test -f $gmp_tmpconfigm4; then
  echo ["changequote(<,>)"] >> $gmp_configm4
  echo ["ifdef(<__CONFIG_M4_INCLUDED__>,,<"] >> $gmp_configm4
  cat $gmp_tmpconfigm4 >> $gmp_configm4
  echo [">)"] >> $gmp_configm4
  echo ["changequote(\`,')"] >> $gmp_configm4
  rm $gmp_tmpconfigm4
fi
echo ["ifdef(\`__CONFIG_M4_INCLUDED__',,\`"] >> $gmp_configm4
if test -f $gmp_tmpconfigm4i; then
  cat $gmp_tmpconfigm4i >> $gmp_configm4
  rm $gmp_tmpconfigm4i
fi
if test -f $gmp_tmpconfigm4p; then
  cat $gmp_tmpconfigm4p >> $gmp_configm4
  rm $gmp_tmpconfigm4p
fi
echo ["')"] >> $gmp_configm4
echo ["define(\`__CONFIG_M4_INCLUDED__')"] >> $gmp_configm4
])


dnl  GMP_INCLUDE_MPN(FILE)
dnl  ---------------------
dnl  Add an include_mpn(`FILE') to config.m4.  FILE should be a path
dnl  relative to the mpn source directory, for example
dnl
dnl      GMP_INCLUDE_MPN(`x86/x86-defs.m4')
dnl

AC_DEFUN(GMP_INCLUDE_MPN,
[AC_REQUIRE([GMP_INIT])
echo ["include_mpn(\`$1')"] >> $gmp_tmpconfigm4i
])


dnl  GMP_DEFINE(MACRO, DEFINITION [, LOCATION])
dnl  ------------------------------------------
dnl  Define M4 macro MACRO as DEFINITION in temporary file.
dnl
dnl  If LOCATION is `POST', the definition will appear after any include()
dnl  directives inserted by GMP_INCLUDE.  Mind the quoting!  No shell
dnl  variables will get expanded.  Don't forget to invoke GMP_FINISH to
dnl  create file config.m4.  config.m4 uses `<' and '>' as quote characters
dnl  for all defines.

AC_DEFUN(GMP_DEFINE, 
[AC_REQUIRE([GMP_INIT])
echo ['define(<$1>, <$2>)'] >>ifelse([$3], [POST],
                              $gmp_tmpconfigm4p, $gmp_tmpconfigm4)
])


dnl  GMP_DEFINE_RAW(STRING, [, LOCATION])
dnl  ------------------------------------
dnl  Put STRING into config.m4 file.
dnl
dnl  If LOCATION is `POST', the definition will appear after any include()
dnl  directives inserted by GMP_INCLUDE.  Don't forget to invoke GMP_FINISH
dnl  to create file config.m4.

AC_DEFUN(GMP_DEFINE_RAW,
[AC_REQUIRE([GMP_INIT])
echo [$1] >> ifelse([$2], [POST], $gmp_tmpconfigm4p, $gmp_tmpconfigm4)
])


dnl  GMP_TRY_ASSEMBLE(asm-code,[action-success][,action-fail])
dnl  ----------------------------------------------------------
dnl  Attempt to assemble the given code.
dnl  Do "action-success" if this succeeds, "action-fail" if not.
dnl
dnl  conftest.o and conftest.out are available for inspection in
dnl  "action-success".  If either action does a "break" out of a loop then
dnl  an explicit "rm -f conftest*" will be necessary.
dnl
dnl  This is not unlike AC_TRY_COMPILE, but there's no default includes or
dnl  anything in "asm-code", everything wanted must be given explicitly.

AC_DEFUN(GMP_TRY_ASSEMBLE,
[cat >conftest.s <<EOF
[$1]
EOF
gmp_assemble="$CCAS $CFLAGS conftest.s >conftest.out 2>&1"
if AC_TRY_EVAL(gmp_assemble); then
  cat conftest.out >&AC_FD_CC
  ifelse([$2],,:,[$2])
else
  cat conftest.out >&AC_FD_CC
  echo "configure: failed program was:" >&AC_FD_CC
  cat conftest.s >&AC_FD_CC
  ifelse([$3],,:,[$3])
fi
rm -f conftest*
])


dnl  GMP_ASM_LABEL_SUFFIX
dnl  --------------------
dnl  Should a label have a colon or not?

AC_DEFUN(GMP_ASM_LABEL_SUFFIX,
[AC_CACHE_CHECK([what assembly label suffix to use],
                gmp_cv_asm_label_suffix,
[case $host in 
  *-*-hpux*) gmp_cv_asm_label_suffix=  ;;
  *)         gmp_cv_asm_label_suffix=: ;;
esac
])
echo ["define(<LABEL_SUFFIX>, <\$][1$gmp_cv_asm_label_suffix>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_UNDERSCORE([ACTION-IF-FOUND [, ACTION-IF-NOT-FOUND]])
dnl  -------------------------------------------------------------
dnl
dnl  Determine whether global symbols need to be prefixed with an underscore.
dnl  A test program is linked to an assembler module with or without an
dnl  underscore to see which works.
dnl
dnl  This method should be more reliable than grepping a .o file or using
dnl  nm, since it corresponds to what a real program is going to do.  Note
dnl  in particular that grepping doesn't work with SunOS 4 native grep since
dnl  that grep seems to have trouble with '\0's in files.

AC_DEFUN(GMP_ASM_UNDERSCORE,
[AC_REQUIRE([GMP_ASM_TEXT])
AC_REQUIRE([GMP_ASM_GLOBL])
AC_REQUIRE([GMP_ASM_LABEL_SUFFIX])
AC_CACHE_CHECK([if globals are prefixed by underscore], 
               gmp_cv_asm_underscore,
[cat >conftes1.c <<EOF
#ifdef __cplusplus
extern "C" { void underscore_test(); }
#endif
main () { underscore_test(); }
EOF
for tmp_underscore in "" "_"; do
  cat >conftes2.s <<EOF
      	$gmp_cv_asm_text
	$gmp_cv_asm_globl ${tmp_underscore}underscore_test
${tmp_underscore}underscore_test$gmp_cv_asm_label_suffix
EOF
  case $host in
  *-*-aix*)
    cat >>conftes2.s <<EOF
	$gmp_cv_asm_globl .${tmp_underscore}underscore_test
.${tmp_underscore}underscore_test$gmp_cv_asm_label_suffix
EOF
    ;;
  esac
  gmp_compile="$CC $CFLAGS $CPPFLAGS conftes1.c conftes2.s 1>&AC_FD_CC"
  if AC_TRY_EVAL(gmp_compile); then
    eval tmp_result$tmp_underscore=yes
  else
    eval tmp_result$tmp_underscore=no
  fi
done

if test $tmp_result_ = yes; then
  if test $tmp_result = yes; then
    AC_MSG_ERROR([Test program unexpectedly links both with and without underscore.])
  else
    gmp_cv_asm_underscore=yes
  fi
else
  if test $tmp_result = yes; then
    gmp_cv_asm_underscore=no
  else
    AC_MSG_ERROR([Test program links neither with nor without underscore.])
  fi
fi
rm -f conftes1* conftes2* a.out
])
if test "$gmp_cv_asm_underscore" = "yes"; then
  GMP_DEFINE(GSYM_PREFIX, [_])
  ifelse([$1],,:,[$1])
else
  GMP_DEFINE(GSYM_PREFIX, [])
  ifelse([$2],,:,[$2])
fi    
])


dnl  GMP_ASM_ALIGN_LOG([ACTION-IF-FOUND [, ACTION-IF-NOT-FOUND]])
dnl  ------------------------------------------------------------
dnl  Is parameter to `.align' logarithmic?

AC_DEFUN(GMP_ASM_ALIGN_LOG,
[AC_REQUIRE([GMP_ASM_GLOBL])
AC_REQUIRE([GMP_ASM_DATA])
AC_REQUIRE([GMP_ASM_LABEL_SUFFIX])
AC_REQUIRE([GMP_PROG_NM])
AC_CACHE_CHECK([if .align assembly directive is logarithmic],
               gmp_cv_asm_align_log,
[GMP_TRY_ASSEMBLE(
[      	$gmp_cv_asm_data
      	.align  4
	$gmp_cv_asm_globl	foo
	.byte	1
	.align	4
foo$gmp_cv_asm_label_suffix
	.byte	2],
  [gmp_tmp_val=[`$NM conftest.o | grep foo | \
     sed -e 's;[[][0-9][]]\(.*\);\1;' -e 's;[^1-9]*\([0-9]*\).*;\1;'`]
  if test "$gmp_tmp_val" = "10" || test "$gmp_tmp_val" = "16"; then
    gmp_cv_asm_align_log=yes
  else
    gmp_cv_asm_align_log=no
  fi],
  [AC_MSG_ERROR([cannot assemble alignment test])])])

GMP_DEFINE_RAW(["define(<ALIGN_LOGARITHMIC>,<$gmp_cv_asm_align_log>)"])
if test "$gmp_cv_asm_align_log" = "yes"; then
  ifelse([$1],,:,[$1])
else
  ifelse([$2],,:,[$2])
fi  
])


dnl  GMP_ASM_ALIGN_FILL_0x90
dnl  -----------------------
dnl  Determine whether a ",0x90" suffix works on a .align directive.
dnl  This is only meant for use on x86, 0x90 being a "nop".
dnl
dnl  Old gas, eg. 1.92.3
dnl       Needs ",0x90" or else the fill is 0x00, which can't be executed
dnl       across.
dnl
dnl  New gas, eg. 2.91
dnl       Generates multi-byte nop fills even when ",0x90" is given.
dnl
dnl  Solaris 2.6 as
dnl       ",0x90" is not allowed, causes a fatal error.
dnl
dnl  Solaris 2.8 as
dnl       ",0x90" does nothing, generates a warning that it's being ignored.
dnl
dnl  SCO OpenServer 5 as
dnl       Second parameter is max bytes to fill, not a fill pattern.
dnl       ",0x90" is an error due to being bigger than the first parameter.
dnl       Multi-byte nop fills are generated in text segments.
dnl
dnl  Note that both solaris "as"s only care about ",0x90" if they actually
dnl  have to use it to fill something, hence the .byte in the test.  It's
dnl  the second .align which provokes the error or warning.
dnl
dnl  The warning from solaris 2.8 is supressed to stop anyone worrying that
dnl  something might be wrong.

AC_DEFUN(GMP_ASM_ALIGN_FILL_0x90,
[AC_REQUIRE([GMP_ASM_TEXT])
AC_CACHE_CHECK([if the .align directive accepts an 0x90 fill in .text],
               gmp_cv_asm_align_fill_0x90,
[GMP_TRY_ASSEMBLE(
[      	$gmp_cv_asm_text
      	.align  4, 0x90
	.byte   0
      	.align  4, 0x90],
[if grep "Warning: Fill parameter ignored for executable section" conftest.out >/dev/null; then
  echo "Supressing this warning by omitting 0x90" 1>&AC_FD_CC
  gmp_cv_asm_align_fill_0x90=no
else
  gmp_cv_asm_align_fill_0x90=yes
fi],
[gmp_cv_asm_align_fill_0x90=no])])

GMP_DEFINE_RAW(["define(<ALIGN_FILL_0x90>,<$gmp_cv_asm_align_fill_0x90>)"])
])


dnl  GMP_ASM_TEXT
dnl  ------------

AC_DEFUN(GMP_ASM_TEXT,
[AC_CACHE_CHECK([how to switch to text section],
                gmp_cv_asm_text,
[case $host in
  *-*-aix*)  gmp_cv_asm_text=[".csect .text[PR]"] ;;
  *-*-hpux*) gmp_cv_asm_text=".code" ;;
  *)         gmp_cv_asm_text=".text" ;;
esac
])
echo ["define(<TEXT>, <$gmp_cv_asm_text>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_DATA
dnl  ------------
dnl  Can we say `.data'?

AC_DEFUN(GMP_ASM_DATA,
[AC_CACHE_CHECK([how to switch to data section],
                gmp_cv_asm_data,
[case $host in
  *-*-aix*) gmp_cv_asm_data=[".csect .data[RW]"] ;;
  *)        gmp_cv_asm_data=".data" ;;
esac
])
echo ["define(<DATA>, <$gmp_cv_asm_data>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_RODATA
dnl  --------------
dnl
dnl  ELF uses .section .rodata, possibly with a ,"a" though in gas the flags
dnl  default from the section name.
dnl
dnl  COFF looks like it might use .section .rdata, possibly with ,"dr"
dnl  though again gas uses defaults based on the section name.
dnl
dnl  a.out has only text, data and bss.
dnl
dnl  FIXME: It's not quite clear how to tell the difference between ELF and
dnl  COFF, so for the moment RODATA is a synonym for DATA on CPUs with split
dnl  code and data caching, or TEXT elsewhere.
dnl
dnl  i386 and i486 don't have caching but are treated the same as newer x86s
dnl  since i386 in particular is used to mean generic x86.

AC_DEFUN(GMP_ASM_RODATA,
[AC_REQUIRE([GMP_ASM_TEXT])
AC_REQUIRE([GMP_ASM_DATA])
AC_CACHE_CHECK([how to switch to read-only data section],
               gmp_cv_asm_rodata,
[case $host in
X86_PATTERN) gmp_cv_asm_rodata="$gmp_cv_asm_data" ;;
*)           gmp_cv_asm_rodata="$gmp_cv_asm_text" ;;
esac
])
echo ["define(<RODATA>, <$gmp_cv_asm_rodata>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_GLOBL
dnl  -------------
dnl  Can we say `.global'?

AC_DEFUN(GMP_ASM_GLOBL,
[AC_CACHE_CHECK([how to export a symbol],
                gmp_cv_asm_globl,
[case $host in
  *-*-hpux*) gmp_cv_asm_globl=".export" ;;
  *)         gmp_cv_asm_globl=".globl" ;;
esac
])
echo ["define(<GLOBL>, <$gmp_cv_asm_globl>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_GLOBL_ATTR
dnl  -----------------------
dnl  Do we need something after `.global symbol'?

AC_DEFUN(GMP_ASM_GLOBL_ATTR,
[AC_CACHE_CHECK([if the export directive needs an attribute],
                gmp_cv_asm_globl_attr,
[case $host in
  *-*-hpux*) gmp_cv_asm_globl_attr=",entry" ;;
  *)         gmp_cv_asm_globl_attr="" ;;
esac
])
echo ["define(<GLOBL_ATTR>, <$gmp_cv_asm_globl_attr>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_TYPE
dnl  ------------
dnl  Can we say ".type", and how?
dnl
dnl  For ELF systems .type is important, and failing to have it can lead to
dnl  strange problems.  For instance on i386 GNU/Linux if a program refers
dnl  to a function in a shared library that doesn't have .type, then calls
dnl  to it either from the program or the library get immediate segvs,
dnl  apparently due to an uninitialized program PLT entry.  If the only
dnl  references are from within the library then calls from there work fine
dnl  (and that can hide the problem).

AC_DEFUN(GMP_ASM_TYPE,
[AC_CACHE_CHECK([how the .type assembly directive should be used],
                gmp_cv_asm_type,
[for gmp_tmp_prefix in @ \# %; do
  GMP_TRY_ASSEMBLE([	.type	sym,${gmp_tmp_prefix}function],
    [gmp_cv_asm_type=".type	\$][1,${gmp_tmp_prefix}\$][2"
    break])
done
rm -f conftest*
if test -z "$gmp_cv_asm_type"; then
  gmp_cv_asm_type=""
fi
])
echo ["define(<TYPE>, <$gmp_cv_asm_type>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_SIZE
dnl  ------------
dnl  Can we say `.size'?

AC_DEFUN(GMP_ASM_SIZE,
[AC_CACHE_CHECK([if the .size assembly directive works],
                gmp_cv_asm_size,
[GMP_TRY_ASSEMBLE([	.size	sym,1],
  [gmp_cv_asm_size=".size	\$][1,\$][2"],
  [gmp_cv_asm_size=""])
])
echo ["define(<SIZE>, <$gmp_cv_asm_size>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_LSYM_PREFIX
dnl  -------------------
dnl  What is the prefix for a local label?
dnl
dnl  FIXME: Consider validating $NM by first requiring that gurkmacka shows
dnl  up when unprefixed.

AC_DEFUN(GMP_ASM_LSYM_PREFIX,
[AC_REQUIRE([GMP_ASM_LABEL_SUFFIX])
AC_REQUIRE([GMP_PROG_NM])
AC_CACHE_CHECK([what prefix to use for a local label], 
               gmp_cv_asm_lsym_prefix,
[gmp_cv_asm_lsym_prefix="L"
gmp_found=no
for gmp_tmp_pre in L .L $ L$; do
  echo "Trying $gmp_tmp_pre" >&AC_FD_CC
  GMP_TRY_ASSEMBLE(
[dummy${gmp_cv_asm_label_suffix}
${gmp_tmp_pre}gurkmacka${gmp_cv_asm_label_suffix}
	.byte 0],
  [$NM conftest.o >&AC_FD_CC 2>&AC_FD_CC
  if test $? != 0; then
    AC_MSG_WARN([NM failure, using default local label $gmp_cv_asm_lsym_prefix])
    gmp_found=yes
    break
  fi
  if $NM conftest.o | grep gurkmacka >/dev/null; then : ; else
    gmp_cv_asm_lsym_prefix="$gmp_tmp_pre"
    gmp_found=yes
    break
  fi])
done
rm -f conftest*
if test $gmp_found = no; then
  AC_MSG_WARN([cannot determine local label, using default $gmp_cv_asm_lsym_prefix])
fi
])
echo ["define(<LSYM_PREFIX>, <${gmp_cv_asm_lsym_prefix}>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_W32
dnl  -----------
dnl  How to define a 32-bit word.

AC_DEFUN(GMP_ASM_W32,
[AC_REQUIRE([GMP_ASM_DATA])
AC_REQUIRE([GMP_ASM_GLOBL])
AC_REQUIRE([GMP_ASM_LABEL_SUFFIX])
AC_REQUIRE([GMP_PROG_NM])
AC_CACHE_CHECK([how to define a 32-bit word],
	       gmp_cv_asm_w32,
[case $host in 
  *-*-hpux*)
    # FIXME: HPUX puts first symbol at 0x40000000, breaking our assumption
    # that it's at 0x0.  We'll have to declare another symbol before the
    # .long/.word and look at the distance between the two symbols.  The
    # only problem is that the sed expression(s) barfs (on Solaris, for
    # example) for the symbol with value 0.  For now, HPUX uses .word.
    gmp_cv_asm_w32=".word"
    ;;
  *-*-*)
    gmp_tmp_val=
    for gmp_tmp_op in .long .word; do
      GMP_TRY_ASSEMBLE(
[	$gmp_cv_asm_data
	$gmp_cv_asm_globl	foo
	$gmp_tmp_op	0
foo$gmp_cv_asm_label_suffix
	.byte	0],
        [gmp_tmp_val=[`$NM conftest.o | grep foo | \
          sed -e 's;[[][0-9][]]\(.*\);\1;' -e 's;[^1-9]*\([0-9]*\).*;\1;'`]
        if test "$gmp_tmp_val" = 4; then
          gmp_cv_asm_w32="$gmp_tmp_op"
          break
        fi])
    done
    rm -f conftest*
    ;;
esac
if test -z "$gmp_cv_asm_w32"; then
  AC_MSG_ERROR([cannot determine how to define a 32-bit word])
fi
])
echo ["define(<W32>, <$gmp_cv_asm_w32>)"] >> $gmp_tmpconfigm4
])


dnl  GMP_ASM_X86_MMX([ACTION-IF-FOUND][,ACTION-IF-NOT-FOUND])
dnl  ---------------------------------------------------------
dnl  Determine whether the assembler supports MMX instructions.
dnl
dnl  This macro is wanted before GMP_ASM_TEXT, so ".text" is hard coded
dnl  here.  ".text" is believed to be correct on all x86 systems, certainly
dnl  it's all GMP_ASM_TEXT gives currently.  Actually ".text" probably isn't
dnl  needed at all, at least for just checking instruction syntax.
dnl
dnl  "movq %mm0, %mm1" should assemble as "0f 6f c8", but Solaris 2.6 and
dnl  2.7 wrongly assemble it as "0f 6f c1" (that being the reverse "movq
dnl  %mm1, %mm0").  It seems more trouble than it's worth to work around
dnl  this in the code, so just detect and reject.

AC_DEFUN(GMP_ASM_X86_MMX,
[AC_CACHE_CHECK([if the assembler knows about MMX instructions],
		gmp_cv_asm_x86_mmx,
[GMP_TRY_ASSEMBLE(
[	.text
	movq	%mm0, %mm1],
[gmp_cv_asm_x86_mmx=yes
case $host in
*-*-solaris*)
  if (dis conftest.o >conftest.out) 2>/dev/null; then
    if grep "0f 6f c1" conftest.out >/dev/null; then
      gmp_cv_asm_x86_mmx=movq-bug
    fi
  else
    AC_MSG_WARN(["dis" not available to check for "as" movq bug])
  fi
esac],
[gmp_cv_asm_x86_mmx=no])])

case $gmp_cv_asm_x86_mmx in
movq-bug)
  AC_MSG_WARN([+----------------------------------------------------------])
  AC_MSG_WARN([| WARNING WARNING WARNING])
  AC_MSG_WARN([| Host CPU has MMX code, but the assembler])
  AC_MSG_WARN([|     $CCAS $CFLAGS])
  AC_MSG_WARN([| has the Solaris 2.6 and 2.7 bug where register to register])
  AC_MSG_WARN([| movq operands are reversed.])
  AC_MSG_WARN([| Non-MMX replacements will be used.])
  AC_MSG_WARN([| This will be an inferior build.])
  AC_MSG_WARN([+----------------------------------------------------------])
  ;;
no)
  AC_MSG_WARN([+----------------------------------------------------------])
  AC_MSG_WARN([| WARNING WARNING WARNING])
  AC_MSG_WARN([| Host CPU has MMX code, but it can't be assembled by])
  AC_MSG_WARN([|     $CCAS $CFLAGS])
  AC_MSG_WARN([| Non-MMX replacements will be used.])
  AC_MSG_WARN([| This will be an inferior build.])
  AC_MSG_WARN([+----------------------------------------------------------])
  ;;
esac
if test "$gmp_cv_asm_x86_mmx" = yes; then
  ifelse([$1],,:,[$1])
else
  ifelse([$2],,:,[$2])
fi
])


dnl  GMP_ASM_X86_SHLDL_CL
dnl  --------------------

AC_DEFUN(GMP_ASM_X86_SHLDL_CL,
[AC_REQUIRE([GMP_ASM_TEXT])
AC_CACHE_CHECK([if the assembler takes cl with shldl],
		gmp_cv_asm_x86_shldl_cl,
[GMP_TRY_ASSEMBLE(
[	$gmp_cv_asm_text
	shldl	%cl, %eax, %ebx],
  gmp_cv_asm_x86_shldl_cl=yes,
  gmp_cv_asm_x86_shldl_cl=no)
])
if test "$gmp_cv_asm_x86_shldl_cl" = "yes"; then
  GMP_DEFINE(WANT_SHLDL_CL,1)
else
  GMP_DEFINE(WANT_SHLDL_CL,0)
fi
])


dnl  GMP_ASM_X86_MCOUNT
dnl  ------------------
dnl  Find out how to call mcount for profiling on an x86 system.
dnl
dnl  A dummy function is compiled and the ".s" output examined.  The pattern
dnl  matching might be a bit fragile, but should work at least with gcc on
dnl  sensible systems.  Certainly it's better than hard coding a table of
dnl  conventions.
dnl
dnl  For non-PIC, any ".data" is taken to mean a counter might be passed.
dnl  It's assumed a movl will set it up, and the right register is taken
dnl  from that movl.  Any movl involving %esp is ignored (a frame pointer
dnl  setup normally).
dnl
dnl  For PIC, any ".data" is similarly interpreted, but a GOTOFF identifies
dnl  the line setting up the right register.
dnl
dnl  In both cases a line with "mcount" identifies the call and that line is
dnl  used literally.
dnl
dnl  On some systems (eg. FreeBSD 3.5) gcc emits ".data" but doesn't use it,
dnl  so it's not an error to have .data but then not find a register.
dnl
dnl  Variations in mcount conventions on different x86 systems can be found
dnl  in gcc config/i386.  mcount can have a "_" prefix or be .mcount or
dnl  _mcount_ptr, and for PIC it can be called through a GOT entry, or via
dnl  the PLT.  If a pointer to a counter is required it's passed in %eax or
dnl  %edx.
dnl
dnl  Flags to specify PIC are taken from $ac_cv_prog_cc_pic set by
dnl  AC_PROG_LIBTOOL.
dnl
dnl  Enhancement: Cache the values determined here. But what's the right way
dnl  to get two variables (mcount_nonpic_reg and mcount_nonpic_call say) set
dnl  from one block of commands?

AC_DEFUN(GMP_ASM_X86_MCOUNT,
[AC_REQUIRE([AC_ENABLE_SHARED])
AC_REQUIRE([AC_PROG_LIBTOOL])
AC_MSG_CHECKING([how to call x86 mcount])
cat >conftest.c <<EOF
foo(){bar();}
EOF

if test "$enable_static" = yes; then
  gmp_asmout_compile="$CC $CFLAGS $CPPFLAGS -S conftest.c 1>&AC_FD_CC"
  if AC_TRY_EVAL(gmp_asmout_compile); then
    if grep '\.data' conftest.s >/dev/null; then
      mcount_nonpic_reg=`sed -n ['/esp/!s/.*movl.*,\(%[a-z]*\).*$/\1/p'] conftest.s`
    else
      mcount_nonpic_reg=
    fi
    mcount_nonpic_call=`grep 'call.*mcount' conftest.s`
    if test -z "$mcount_nonpic_call"; then
      AC_MSG_ERROR([Cannot find mcount call for non-PIC])
    fi
  else
    AC_MSG_ERROR([Cannot compile test program for non-PIC])
  fi
fi

if test "$enable_shared" = yes; then
  gmp_asmout_compile="$CC $CFLAGS $CPPFLAGS $ac_cv_prog_cc_pic -S conftest.c 1>&AC_FD_CC"
  if AC_TRY_EVAL(gmp_asmout_compile); then
    if grep '\.data' conftest.s >/dev/null; then
      mcount_pic_reg=`sed -n ['s/.*GOTOFF.*,\(%[a-z]*\).*$/\1/p'] conftest.s`
    else
      mcount_pic_reg=
    fi
    mcount_pic_call=`grep 'call.*mcount' conftest.s`
    if test -z "$mcount_pic_call"; then
      AC_MSG_ERROR([Cannot find mcount call for PIC])
    fi
  else
    AC_MSG_ERROR([Cannot compile test program for PIC])
  fi
fi

GMP_DEFINE_RAW(["define(<MCOUNT_NONPIC_REG>, <\`$mcount_nonpic_reg'>)"])
GMP_DEFINE_RAW(["define(<MCOUNT_NONPIC_CALL>,<\`$mcount_nonpic_call'>)"])
GMP_DEFINE_RAW(["define(<MCOUNT_PIC_REG>,    <\`$mcount_pic_reg'>)"])
GMP_DEFINE_RAW(["define(<MCOUNT_PIC_CALL>,   <\`$mcount_pic_call'>)"])

rm -f conftest.*
AC_MSG_RESULT([determined])
])


dnl  GMP_ASM_POWERPC_R_REGISTERS
dnl  ---------------------------
dnl
dnl  Determine whether the assembler takes powerpc registers with an "r" as
dnl  in "r6", or as plain "6".  The latter is standard, but NeXT, Rhapsody,
dnl  and MacOS-X require the "r" forms.
dnl
dnl  See also mpn/powerpc32/powerpc-defs.m4 which uses the result of this
dnl  test.

AC_DEFUN(GMP_ASM_POWERPC_R_REGISTERS,
[AC_REQUIRE([GMP_ASM_TEXT])
AC_CACHE_CHECK([if the assembler needs r on registers],
               gmp_cv_asm_powerpc_r_registers,
[GMP_TRY_ASSEMBLE(
[	$gmp_cv_asm_text
	mtctr	6],
[gmp_cv_asm_powerpc_r_registers=no],
[GMP_TRY_ASSEMBLE(
[	$gmp_cv_asm_text
	mtctr	r6],
[gmp_cv_asm_powerpc_r_registers=yes],
[AC_MSG_ERROR([neither "mtctr 6" nor "mtctr r6" works])])])])

GMP_DEFINE_RAW(["define(<WANT_R_REGISTERS>,<$gmp_cv_asm_powerpc_r_registers>)"])
])


dnl  GMP_C_ATTRIBUTE_CONST
dnl  ---------------------

AC_DEFUN(GMP_C_ATTRIBUTE_CONST,
[AC_CACHE_CHECK([whether gcc __attribute__ ((const)) works],
                gmp_cv_c_attribute_const,
[AC_TRY_COMPILE([int foo (int x) __attribute__ ((const));], ,
  gmp_cv_c_attribute_const=yes, gmp_cv_c_attribute_const=no)
])
if test $gmp_cv_c_attribute_const = yes; then
  AC_DEFINE(HAVE_ATTRIBUTE_CONST, 1,
  [Define if the compiler accepts gcc style __attribute__ ((const))])
fi
])


dnl  GMP_C_ATTRIBUTE_NORETURN
dnl  ------------------------

AC_DEFUN(GMP_C_ATTRIBUTE_NORETURN,
[AC_CACHE_CHECK([whether gcc __attribute__ ((noreturn)) works],
                gmp_cv_c_attribute_noreturn,
[AC_TRY_COMPILE([void foo (int x) __attribute__ ((noreturn));], ,
  gmp_cv_c_attribute_noreturn=yes, gmp_cv_c_attribute_noreturn=no)
])
if test $gmp_cv_c_attribute_noreturn = yes; then
  AC_DEFINE(HAVE_ATTRIBUTE_NORETURN, 1,
  [Define if the compiler accepts gcc style __attribute__ ((noreturn))])
fi
])


dnl  GMP_C_SIZES
dnl  -----------
dnl
dnl  Determine some sizes, if not alredy provided by gmp-mparam.h.  These
dnl  are needed by GMP at preprocessing time, for use in #if conditionals.
dnl  $gmp_mparam_source is the selected gmp-mparam.h.
dnl
dnl  If some assembler code depends on a particular limb size it's probably
dnl  best to put explicit #defines for these in gmp-mparam.h.  That way if
dnl  strange compiler options change the size then a mismatch will be
dnl  detected by t-constants.c rather than only by the code crashing or
dnl  giving wrong results.
dnl
dnl  None of the assembler code depends on BITS_PER_ULONG currently, so it's
dnl  just as easy to let configure find it's size as put in explicit values.
dnl
dnl  The tests here assume bits=8*sizeof, but that might not be universally
dnl  true.  It'd be better to probe for how many bits seem to work, like
dnl  t-constants does.  But all currently supported systems have limbs and
dnl  ulongs with bits=8*sizeof, so it's academic.  Strange systems can
dnl  always have the right values put in gmp-mparam.h explicitly.
dnl
dnl  Notice the use of gmp-h.in, since gmp.h isn't instantiated yet.
dnl  AC_CHECK_SIZEOF includes confdefs.h, which gives the right
dnl  _LONG_LONG_LIMB setting.  __GMP_WITHIN_CONFIGURE ensures the #undef
dnl  template in gmp-h.in doesn't undo it.

AC_DEFUN(GMP_C_SIZES,
[if   grep "^#define BITS_PER_MP_LIMB"  $gmp_mparam_source >/dev/null \
   && grep "^#define BYTES_PER_MP_LIMB" $gmp_mparam_source >/dev/null; then : ;
else
  AC_CHECK_SIZEOF(mp_limb_t,,
[#include <stdio.h>
#define __GMP_WITHIN_CONFIGURE 1
#include "$srcdir/gmp-h.in"
])
  if test "$ac_cv_sizeof_mp_limb_t" = 0; then
    AC_MSG_ERROR([some sort of compiler problem, mp_limb_t doesn't seem to work])
  fi

  if grep "^#define BITS_PER_MP_LIMB"  $gmp_mparam_source >/dev/null; then : ;
  else
    AC_DEFINE_UNQUOTED(BITS_PER_MP_LIMB,  (8 * $ac_cv_sizeof_mp_limb_t),
                       [bits per mp_limb_t, if not in gmp-mparam.h])  
  fi
  if grep "^#define BYTES_PER_MP_LIMB" $gmp_mparam_source >/dev/null; then : ;
  else
    AC_DEFINE_UNQUOTED(BYTES_PER_MP_LIMB, $ac_cv_sizeof_mp_limb_t,
                       [bytes per mp_limb_t, if not in gmp-mparam.h])
  fi
fi

if grep "^#define BITS_PER_ULONG" $gmp_mparam_source >/dev/null; then : ;
else
  case $limb_chosen in
  longlong)
    AC_CHECK_SIZEOF(unsigned long)
    AC_DEFINE_UNQUOTED(BITS_PER_ULONG, (8 * $ac_cv_sizeof_unsigned_long),
                       [bits per unsigned long, if not in gmp-mparam.h])
    ;;
  *)
    # Copy the limb size when a limb is a ulong
    AC_DEFINE(BITS_PER_ULONG, BITS_PER_MP_LIMB)
    ;;
  esac
fi
])


dnl  GMP_FUNC_ALLOCA
dnl  ---------------
dnl
dnl  Determine whether "alloca" is available.  This is AC_FUNC_ALLOCA from
dnl  autoconf, but changed so it doesn't use alloca.c if alloca() isn't
dnl  available, and also to use gmp-impl.h for the conditionals detecting
dnl  compiler builtin alloca's.

AC_DEFUN(GMP_FUNC_ALLOCA,
[AC_REQUIRE([GMP_HEADER_ALLOCA])
AC_CACHE_CHECK([for alloca (via gmp-impl.h)],
               gmp_cv_func_alloca,
[AC_TRY_LINK(
[#define __GMP_WITHIN_CONFIGURE 1
#include "$srcdir/gmp-h.in"
#include "$srcdir/gmp-impl.h"],
  [char *p = (char *) alloca (1);],
  gmp_cv_func_alloca=yes,
  gmp_cv_func_alloca=no)])
if test $gmp_cv_func_alloca = yes; then
  AC_DEFINE(HAVE_ALLOCA, 1,
    [Define if alloca() works (via gmp-impl.h).])
fi
])

AC_DEFUN(GMP_HEADER_ALLOCA,
[# The Ultrix 4.2 mips builtin alloca declared by alloca.h only works
# for constant arguments.  Useless!
AC_CACHE_CHECK([for working alloca.h],
               gmp_cv_header_alloca,
[AC_TRY_LINK([#include <alloca.h>],
  [char *p = (char *) alloca (2 * sizeof (int));],
  gmp_cv_header_alloca=yes,
  gmp_cv_header_alloca=no)])
if test $gmp_cv_header_alloca = yes; then
  AC_DEFINE(HAVE_ALLOCA_H, 1,
    [Define if you have <alloca.h> and it should be used (not on Ultrix).])
fi
])
