dnl aclocal.m4 generated automatically by aclocal 1.4a

dnl Copyright (C) 1994, 1995-8, 1999 Free Software Foundation, Inc.
dnl This file is free software; the Free Software Foundation
dnl gives unlimited permission to copy and/or distribute it,
dnl with or without modifications, as long as this notice is preserved.

dnl This program is distributed in the hope that it will be useful,
dnl but WITHOUT ANY WARRANTY, to the extent permitted by law; without
dnl even the implied warranty of MERCHANTABILITY or FITNESS FOR A
dnl PARTICULAR PURPOSE.

dnl  GMP_PROG_CC_FIND([CC_LIST], [REQ_64BIT_CC])
dnl  Find first working compiler in CC_LIST.
dnl  If REQ_64BIT_CC is "yes", the compiler is required to be able to 
dnl  produce 64-bit code.
dnl  NOTE: If a compiler needs any special flags for producing 64-bit code,
dnl  these have to be found in shell variable `gmp_cflags64_{cc}', where `{cc}'
dnl  is the name of the compiler.
dnl  Set CC to the name of the first working compiler.
dnl  If a 64-bit compiler is found, set CC64 to the name of the compiler and
dnl  CFLAGS64 to flags to use.
dnl  This macro does not test that any of the compilers found realy work, 
dnl  nor if it is a GNU compiler.  To do this, when you have finally made
dnl  up your mind on which one to use, invoke [GMP_PROG_CC_SELECT]
dnl
AC_DEFUN(GMP_PROG_CC_FIND,
[AC_BEFORE([$0], [CC_PROG_CPP])
ifelse([$1], , gmp_cc_list="gcc cc", gmp_cc_list="[$1]")
ifelse([$2], , gmp_req_64bit_cc="no", gmp_req_64bit_cc="[$2]")

[echo "***DEBUG*** GMP_PROG_CC_FIND: gmp_cc_list=>$gmp_cc_list<"]
[echo "***DEBUG*** GMP_PROG_CC_FIND: gmp_req_64bit_cc=$gmp_req_64bit_cc"]

for gmp_tmp_compiler in $gmp_cc_list; do
  AC_CHECK_PROG(CC_TEST, $gmp_tmp_compiler, $gmp_tmp_compiler, , , /usr/ucb/cc)
  if test -n "$CC_TEST"; then
    CC=$CC_TEST
    if test "$gmp_req_64bit_cc" = "yes"; then
      eval gmp_tmp_compiler_flags=\$gmp_cflags64_${gmp_tmp_compiler}
      GMP_CHECK_CC_64BIT($gmp_tmp_compiler, $gmp_tmp_compiler_flags)
      if test "$gmp_cv_cc_64bit" = "yes"; then
        if test -z "$CC64"; then CC64=$gmp_tmp_compiler; fi
        if test -z "$CFLAGS64"; then CFLAGS64=$gmp_tmp_compiler_flags; fi
        break
      fi
    else
      break
    fi
  fi
done
[echo "***DEBUG*** GMP_PROG_CC_FIND: CC=$CC, CC64=$CC64, CFLAGS64=$CFLAGS64"]
])dnl

dnl  GMP_PROG_CC_SELECT
dnl  Check that `CC' works with `CFLAGS'.
AC_DEFUN(GMP_PROG_CC_SELECT,
[AC_BEFORE([$0], [CC_PROG_CPP])
AC_PROG_CC_WORKS
AC_PROG_CC_GNU

if test "$ac_cv_prog_gcc" = "yes"; then
  GCC=yes
else
  GCC=
fi
dnl [Code for setting CFLAGS removed.]
AC_SUBST(CC)
AC_PROVIDE([AC_PROG_CC])
])dnl

dnl  GMP_CHECK_CC_64BIT(cc, cflags64)
dnl  Find out if `CC' can produce 64-bit code.
AC_DEFUN(GMP_CHECK_CC_64BIT,
[
  gmp_tmp_CC_save="$CC"
  CC="[$1]"
  AC_MSG_CHECKING([whether the C compiler ($CC) is 64-bit capable])
  gmp_tmp_CFLAGS_save="$CFLAGS"
  CFLAGS="[$2]"
  AC_TRY_RUN([
    int main() { return (sizeof (void *) != 8); }
  ], gmp_cv_cc_64bit=yes, gmp_cv_cc_64bit=no, gmp_cv_cc_64bit=no)
  CC="$gmp_tmp_CC_save"
  CFLAGS="$gmp_tmp_CFLAGS_save"
  AC_MSG_RESULT($gmp_cv_cc_64bit)
])dnl

dnl  GMP_PROG_CCAS
dnl  Find C compiler invoking an assembler.
dnl  Set CCAS and [AC_SUBST] it.
AC_DEFUN(GMP_PROG_CCAS,
[AC_REQUIRE([GMP_PROG_CC_SELECT])
AC_CACHE_CHECK([for CC ($CC) invoking assembler],
               gmp_cv_prog_ccas,
[ac_assemble="$CC -c $CFLAGS conftest.s 1>&AC_FD_CC"
rm -f conftest*
echo ".byte	1" > conftest.s
if AC_TRY_EVAL(ac_assemble); then
  if test -f conftest.o; then
    gmp_cv_prog_ccas="$CC -c $CFLAGS"
  else
    dnl  FIXME: Disable all assembly code instead of fatal exit.
    dnl  FIXME: Better fatal exit.
    echo "configure: can't find a C compiler able to assemble"
    exit 1
  fi
else
  echo "configure: failed program was:" >&AC_FD_CC
  cat conftest.s >&AC_FD_CC
  dnl  FIXME: Disable all assembly code instead of fatal exit.
  dnl  FIXME: Better fatal exit.
  echo "configure: can't find a C compiler able to assemble"
  exit 1
fi
rm -f conftest*
])
CCAS="$gmp_cv_prog_ccas"
AC_SUBST(CCAS)
])dnl

dnl  GMP_PROG_LIBTOOL
dnl  Wrap [AC_PROG_LIBTOOL] to avoid the [AC_PROG_CC] problems.
AC_DEFUN(GMP_PROG_LIBTOOL, [
dnl  Save any variable that [AC_PROG_CC] may possibly set, invoke [AC_PROG_CC], and
dnl  restore the variables.  Finally, invoke [AC_PROG_LIBTOOL].
dnl  This is highly dependant on Autoconf version and
dnl  generally a mess.
gmp_save_CC=$CC
gmp_save_CFLAGS=$CFLAGS
gmp_save_ac_cv_prog_gcc=$ac_cv_prog_gcc
gmp_save_GCC=$GCC
gmp_save_ac_cv_prog_cc_g=$ac_cv_prog_cc_g
gmp_save_ac_cv_prog_cc_works=$ac_cv_prog_cc_works
gmp_save_ac_cv_prog_cc_cross=$ac_cv_prog_cc_cross
AC_PROG_CC
CC=$gmp_save_CC
CFLAGS=$gmp_save_CFLAGS
ac_cv_prog_gcc=$gmp_save_ac_cv_prog_gcc
GCC=$gmp_save_GCC
ac_cv_prog_cc_g=$gmp_save_ac_cv_prog_cc_g
ac_cv_prog_cc_works=$gmp_save_ac_cv_prog_cc_works
ac_cv_prog_cc_cross=$gmp_save_ac_cv_prog_cc_cross
AC_PROG_LIBTOOL
])dnl

dnl  GMP_INIT([M4-DEF-FILE])
dnl  
AC_DEFUN(GMP_INIT,
[ifelse([$1], , gmp_configm4=config.m4, gmp_configm4="[$1]")
gmp_tmpconfigm4=cnfm4.tmp
gmp_tmpconfigm4i=cnfm4i.tmp
test -f $gmp_tmpconfigm4 && rm $gmp_tmpconfigm4
test -f $gmp_tmpconfigm4i && rm $gmp_tmpconfigm4i
])dnl

dnl  GMP_FINISH
dnl  Create 
AC_DEFUN(GMP_FINISH,
[AC_REQUIRE([GMP_INIT])
echo [dnl $gmp_configm4.  Generated automatically by configure.] > $gmp_configm4
if test -f $gmp_tmpconfigm4; then
  echo ["changequote(<,>)dnl"] >> $gmp_configm4
  cat $gmp_tmpconfigm4 >> $gmp_configm4
  echo ["changequote(\`,')dnl"] >> $gmp_configm4
  rm $gmp_tmpconfigm4
fi
if test -f $gmp_tmpconfigm4i; then
  cat $gmp_tmpconfigm4i >> $gmp_configm4
  rm $gmp_tmpconfigm4i
fi
])dnl

dnl  GMP_INCLUDE(FILE)
AC_DEFUN(GMP_INCLUDE,
[AC_REQUIRE([GMP_INIT])
echo ["include(\`$1')"] >> $gmp_tmpconfigm4i
])dnl

dnl  GMP_SINCLUDE(FILE)
AC_DEFUN(GMP_SINCLUDE,
[AC_REQUIRE([GMP_INIT])
echo ["sinclude(\`$1')"] >> $gmp_tmpconfigm4i
])dnl

dnl  GMP_DEFINE(MACRO, DEFINITION)
dnl  Define M4 macro MACRO to DEFINITION in temporary file.  Invoke 
dnl  [GMP_FINISH] to create file config.m4 containing all GMP_DEFINEd
dnl  macros.  config.m4 uses `<' and '>' as quote characters.
AC_DEFUN(GMP_DEFINE, 
[AC_REQUIRE([GMP_INIT])
echo ['define(<$1>, <$2>)'] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_LABEL_SUFFIX
dnl  FIXME: Actually check.
AC_DEFUN(GMP_CHECK_ASM_LABEL_SUFFIX,
[AC_CACHE_CHECK([if assembly label needs a suffix],
               gmp_cv_check_asm_label_suffix,
[gmp_cv_check_asm_label_suffix=:])
echo ["define(<LABEL_SUFFIX>, <\$][1$gmp_cv_check_asm_label_suffix>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_UNDERSCORE([ACTION-IF-FOUND [, ACTION-IF-NOT-FOUND]])
dnl  Shamelessly borrowed from glibc.
AC_DEFUN(GMP_CHECK_ASM_UNDERSCORE,
[AC_CACHE_CHECK([if symbols are prefixed by underscore], 
	        gmp_cv_check_asm_underscore,
[cat > conftest.$ac_ext <<EOF
dnl This sometimes fails to find confdefs.h, for some reason.
dnl [#]line __oline__ "[$]0"
[#]line __oline__ "configure"
#include "confdefs.h"
void underscore_test(void) {
return; }
EOF
if AC_TRY_EVAL(ac_compile); then
  if grep _underscore_test conftest* >/dev/null; then
    gmp_cv_check_asm_underscore=yes
    ifelse([$1], , :, [$1])
  else
    gmp_cv_check_asm_underscore=no
    ifelse([$2], , :, [$2])
  fi
else
  echo "configure: failed program was:" >&AC_FD_CC
  cat conftest.$ac_ext >&AC_FD_CC
  ifelse([$2], , :, [$2])
fi
rm -f conftest*
])dnl
])dnl

dnl  GMP_CHECK_ASM_ALIGN_LOG([ACTION-IF-FOUND [, ACTION-IF-NOT-FOUND]])
dnl  Is parameter to `.align' logarithmic?
dnl  Requires NM to be set to nm for target.
AC_DEFUN(GMP_CHECK_ASM_ALIGN_LOG,
[AC_REQUIRE([GMP_PROG_CCAS])
AC_REQUIRE([GMP_CHECK_ASM_GLOBL])
AC_REQUIRE([GMP_CHECK_ASM_DATA])
AC_REQUIRE([GMP_CHECK_ASM_LABEL_SUFFIX])
AC_CACHE_CHECK([if .align assembly directive is logarithmic],
		gmp_cv_check_asm_align_log,
[if test -z "$NM"; then
  echo; echo ["configure: $0: fatal: need nm"]
  exit 1
fi
cat > conftest.s <<EOF
      	$gmp_cv_check_asm_data
      	.align  4
	$gmp_cv_check_asm_globl	foo
	.byte	1
	.align	4
foo$gmp_cv_check_asm_label_suffix
	.byte	2
EOF
ac_assemble="$CCAS $CFLAGS conftest.s 1>&AC_FD_CC"
if AC_TRY_EVAL(ac_assemble); then
  changequote(<,>)
  gmp_tmp_val=`$NM conftest.o | grep foo | sed -e 's;[[][0-9][]]\(.*\);\1;' \
       -e 's;[^1-9]*\([0-9]*\).*;\1;'`
  changequote([, ])dnl
  if test "$gmp_tmp_val" = "10" || test "$gmp_tmp_val" = "16"; then
    gmp_cv_check_asm_align_log=yes
    ifelse([$1], , :, [$1])
  else
    gmp_cv_check_asm_align_log=no
    ifelse([$2], , :, [$2])
  fi
else 
  echo "configure: failed program was:" >&AC_FD_CC
  cat conftest.s >&AC_FD_CC
  ifelse([$2], , :, [$2])
fi
rm -f conftest*
])
])dnl

dnl  GMP_CHECK_ASM_TEXT
AC_DEFUN(GMP_CHECK_ASM_TEXT,
[AC_CACHE_CHECK([how to switch to text section], gmp_cv_check_asm_text,
[case "$target" in
  *-*-aix*)
    changequote({, })
    gmp_cv_check_asm_text={".csect .text[PR]"}
    changequote([, ])
    ;;
  *-*-hpux*) gmp_cv_check_asm_text=[".code"] ;;
  *) gmp_cv_check_asm_text=[".text"] ;;
esac
])
echo ["define(<TEXT>, <$gmp_cv_check_asm_text>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_DATA
dnl  Can we say `.data'?
AC_DEFUN(GMP_CHECK_ASM_DATA,
[AC_CACHE_CHECK([how to switch to data section], gmp_cv_check_asm_data,
[case "$target" in
  *-*-aix*)
    changequote({, })
    gmp_cv_check_asm_data={".csect .data[RW]"}
    changequote([, ])
    ;;
  *-*-hpux*) gmp_cv_check_asm_data=[".code"] ;;
  *) gmp_cv_check_asm_data=[".data"] ;;
esac
])
echo ["define(<DATA>, <$gmp_cv_check_asm_data>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_GLOBL
dnl  Can we say `.global'?
AC_DEFUN(GMP_CHECK_ASM_GLOBL,
[AC_CACHE_CHECK([how to export a symbol], gmp_cv_check_asm_globl,
[case "$target" in
  *-*-hpux*) gmp_cv_check_asm_globl=[".xport"] ;;
  *) gmp_cv_check_asm_globl=[".globl"] ;;
esac
])
echo ["define(<GLOBL>, <$gmp_cv_check_asm_globl>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_TYPE
dnl  Can we say `.type'?
AC_DEFUN(GMP_CHECK_ASM_TYPE,
[AC_REQUIRE([GMP_PROG_CCAS])
AC_CACHE_CHECK([how the .type assembly directive should be used],
gmp_cv_check_asm_type,
[ac_assemble="$CCAS $CFLAGS conftest.s 1>&AC_FD_CC"
for gmp_tmp_prefix in @ \# %; do
  echo ".type	sym,${gmp_tmp_prefix}function" > conftest.s
  if AC_TRY_EVAL(ac_assemble); then
    gmp_cv_check_asm_type="[.type	\$][1,${gmp_tmp_prefix}\$][2]"
    break
  fi
done
if test -z "$gmp_cv_check_asm_type"; then
  gmp_cv_check_asm_type="[dnl]"
fi
])
echo ["define(<TYPE>, <$gmp_cv_check_asm_type>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_SIZE
dnl  Can we say `.size'?
AC_DEFUN(GMP_CHECK_ASM_SIZE,
[AC_REQUIRE([GMP_PROG_CCAS])
AC_CACHE_CHECK([if the .size assembly directive works], gmp_cv_check_asm_size,
[ac_assemble="$CCAS $CFLAGS conftest.s 1>&AC_FD_CC"
echo '.size	sym,1' > conftest.s
if AC_TRY_EVAL(ac_assemble); then
  gmp_cv_check_asm_size="[.size	\$][1,\$][2]"
else
  gmp_cv_check_asm_size="[dnl]"
fi
])
echo ["define(<SIZE>, <$gmp_cv_check_asm_size>)"] >> $gmp_tmpconfigm4
])dnl

dnl  GMP_CHECK_ASM_LSYM_PREFIX
dnl  What is the prefix for a local label?
dnl  Requires NM to be set to nm for target.
AC_DEFUN(GMP_CHECK_ASM_LSYM_PREFIX,
[AC_REQUIRE([GMP_PROG_CCAS])
AC_REQUIRE([GMP_CHECK_ASM_LABEL_SUFFIX])
AC_CACHE_CHECK([what prefix to use for a local label], 
gmp_cv_check_asm_lsym_prefix,
[if test -z "$NM"; then
  echo; echo ["$0: fatal: need nm"]
  exit 1
fi
ac_assemble="$CCAS $CFLAGS conftest.s 1>&AC_FD_CC"
gmp_cv_check_asm_lsym_prefix="L"
for gmp_tmp_pre in .L $ L$; do
  echo "${gmp_tmp_pre}gurkmacka${gmp_cv_check_asm_label_suffix}	.byte 0" > conftest.s
  if AC_TRY_EVAL(ac_assemble); then
    if $NM conftest.o | grep gurkmacka >/dev/null; then true; else
      gmp_cv_check_asm_lsym_prefix="$gmp_tmp_pre"
      break
    fi
  fi
done
])
echo ["define(<LSYM_PREFIX>, <${gmp_cv_check_asm_lsym_prefix}>)"] >> $gmp_tmpconfigm4
])

dnl  GMP_CHECK_ASM_W32
dnl  How to [define] a 32-bit word.
dnl  Requires NM to be set to nm for target.
AC_DEFUN(GMP_CHECK_ASM_W32,
[AC_REQUIRE([GMP_PROG_CCAS])
AC_REQUIRE([GMP_CHECK_ASM_DATA])
AC_REQUIRE([GMP_CHECK_ASM_GLOBL])
AC_REQUIRE([GMP_CHECK_ASM_LABEL_SUFFIX])
AC_CACHE_CHECK([how to [define] a 32-bit word],
	       gmp_cv_check_asm_w32,
[if test -z "$NM"; then
  echo; echo ["configure: $0: fatal: need nm"]
  exit 1
fi
ac_assemble="$CCAS $CFLAGS conftest.s 1>&AC_FD_CC"
for gmp_tmp_op in .long .word; do
  cat > conftest.s <<EOF
      	$gmp_cv_check_asm_data
	$gmp_cv_check_asm_globl	foo
	$gmp_tmp_op	0
foo${gmp_cv_check_asm_label_suffix}
	.byte	0
EOF
  if AC_TRY_EVAL(ac_assemble); then
    changequote(<,>)
    gmp_tmp_val=`$NM conftest.o | grep foo | sed -e 's;[[][0-9][]]\(.*\);\1;' \
         -e 's;[^1-9]*\([0-9]*\).*;\1;'`
    changequote([, ])dnl
    if test "$gmp_tmp_val" = "4"; then
      gmp_cv_check_asm_w32="$gmp_tmp_op"
      break
    fi
  fi
done
if test -z "$gmp_cv_check_asm_w32"; then
  echo; echo ["configure: $0: fatal: do not know how to define a 32-bit word"]
  exit 1
fi
rm -f conftest*
])
echo ["define(<W32>, <$gmp_cv_check_asm_w32>)"] >> $gmp_tmpconfigm4
])


# serial 42 AC_PROG_LIBTOOL
AC_DEFUN(AC_PROG_LIBTOOL,
[AC_REQUIRE([AC_LIBTOOL_SETUP])dnl

# Save cache, so that ltconfig can load it
AC_CACHE_SAVE

# Actually configure libtool.  ac_aux_dir is where install-sh is found.
AR="$AR" CC="$CC" CFLAGS="$CFLAGS" CPPFLAGS="$CPPFLAGS" \
FILE="$FILE" LD="$LD" LDFLAGS="$LDFLAGS" LIBS="$LIBS" \
LN_S="$LN_S" NM="$NM" RANLIB="$RANLIB" STRIP="$STRIP" \
AS="$AS" DLLTOOL="$DLLTOOL" OBJDUMP="$OBJDUMP" \
objext="$OBJEXT" exeext="$EXEEXT" reload_flag="$reload_flag" \
deplibs_check_method="$deplibs_check_method" file_magic_cmd="$file_magic_cmd" \
${CONFIG_SHELL-/bin/sh} $ac_aux_dir/ltconfig --no-reexec \
$libtool_flags --no-verify --build="$build" $ac_aux_dir/ltmain.sh $lt_target \
|| AC_MSG_ERROR([libtool configure failed])

# Reload cache, that may have been modified by ltconfig
AC_CACHE_LOAD

# This can be used to rebuild libtool when needed
LIBTOOL_DEPS="$ac_aux_dir/ltconfig $ac_aux_dir/ltmain.sh"

# Always use our own libtool.
LIBTOOL='$(SHELL) $(top_builddir)/libtool'
AC_SUBST(LIBTOOL)dnl

# Redirect the config.log output again, so that the ltconfig log is not
# clobbered by the next message.
exec 5>>./config.log
])

AC_DEFUN(AC_LIBTOOL_SETUP,
[AC_PREREQ(2.13)dnl
AC_REQUIRE([AC_ENABLE_SHARED])dnl
AC_REQUIRE([AC_ENABLE_STATIC])dnl
AC_REQUIRE([AC_ENABLE_FAST_INSTALL])dnl
AC_REQUIRE([AC_CANONICAL_HOST])dnl
AC_REQUIRE([AC_CANONICAL_BUILD])dnl
AC_REQUIRE([AC_PROG_CC])dnl
AC_REQUIRE([AC_PROG_LD])dnl
AC_REQUIRE([AC_PROG_LD_RELOAD_FLAG])dnl
AC_REQUIRE([AC_PROG_NM])dnl
AC_REQUIRE([AC_PROG_LN_S])dnl
AC_REQUIRE([AC_DEPLIBS_CHECK_METHOD])dnl
AC_REQUIRE([AC_OBJEXT])dnl
AC_REQUIRE([AC_EXEEXT])dnl
dnl

# Only perform the check for file, if the check method requires it
case "$deplibs_check_method" in
file_magic*)
  if test "$file_magic_cmd" = '$FILE'; then
    AC_PATH_FILE
  fi
  ;;
esac

case "$target" in
NONE) lt_target="$host" ;;
*) lt_target="$target" ;;
esac

AC_CHECK_TOOL(RANLIB, ranlib, :)
AC_CHECK_TOOL(STRIP, strip, :)

# Check for any special flags to pass to ltconfig.
libtool_flags="--cache-file=$cache_file"
test "$enable_shared" = no && libtool_flags="$libtool_flags --disable-shared"
test "$enable_static" = no && libtool_flags="$libtool_flags --disable-static"
test "$enable_fast_install" = no && libtool_flags="$libtool_flags --disable-fast-install"
test "$ac_cv_prog_gcc" = yes && libtool_flags="$libtool_flags --with-gcc"
test "$ac_cv_prog_gnu_ld" = yes && libtool_flags="$libtool_flags --with-gnu-ld"
ifdef([AC_PROVIDE_AC_LIBTOOL_DLOPEN],
[libtool_flags="$libtool_flags --enable-dlopen"])
ifdef([AC_PROVIDE_AC_LIBTOOL_WIN32_DLL],
[libtool_flags="$libtool_flags --enable-win32-dll"])
AC_ARG_ENABLE(libtool-lock,
  [  --disable-libtool-lock  avoid locking (might break parallel builds)])
test "x$enable_libtool_lock" = xno && libtool_flags="$libtool_flags --disable-lock"
test x"$silent" = xyes && libtool_flags="$libtool_flags --silent"

AC_ARG_WITH(pic,
  [  --with-pic              try to use only PIC/non-PIC objects [default=use both]],
     pic_mode="$withval", pic_mode=default)
test x"$pic_mode" = xyes && libtool_flags="$libtool_flags --prefer-pic"
test x"$pic_mode" = xno && libtool_flags="$libtool_flags --prefer-non-pic"

# Some flags need to be propagated to the compiler or linker for good
# libtool support.
case "$lt_target" in
*-*-irix6*)
  # Find out which ABI we are using.
  echo '[#]line __oline__ "configure"' > conftest.$ac_ext
  if AC_TRY_EVAL(ac_compile); then
    case "`/usr/bin/file conftest.o`" in
    *32-bit*)
      LD="${LD-ld} -32"
      ;;
    *N32*)
      LD="${LD-ld} -n32"
      ;;
    *64-bit*)
      LD="${LD-ld} -64"
      ;;
    esac
  fi
  rm -rf conftest*
  ;;

*-*-sco3.2v5*)
  # On SCO OpenServer 5, we need -belf to get full-featured binaries.
  SAVE_CFLAGS="$CFLAGS"
  CFLAGS="$CFLAGS -belf"
  AC_CACHE_CHECK([whether the C compiler needs -belf], lt_cv_cc_needs_belf,
    [AC_TRY_LINK([],[],[lt_cv_cc_needs_belf=yes],[lt_cv_cc_needs_belf=no])])
  if test x"$lt_cv_cc_needs_belf" != x"yes"; then
    # this is probably gcc 2.8.0, egcs 1.0 or newer; no need for -belf
    CFLAGS="$SAVE_CFLAGS"
  fi
  ;;

ifdef([AC_PROVIDE_AC_LIBTOOL_WIN32_DLL],
[*-*-cygwin* | *-*-mingw*)
  AC_CHECK_TOOL(DLLTOOL, dlltool, false)
  AC_CHECK_TOOL(AS, as, false)
  AC_CHECK_TOOL(OBJDUMP, objdump, false)

  # recent cygwin and mingw systems supply a stub DllMain which the user
  # can override, but on older systems we have to supply one
  AC_CACHE_CHECK([if libtool should supply DllMain function], lt_cv_need_dllmain,
    [AC_TRY_LINK([],
      [extern int __attribute__((__stdcall__)) DllMain(void*, int, void*);
      DllMain (0, 0, 0);],
      [lt_cv_need_dllmain=no],[lt_cv_need_dllmain=yes])])

  case "$lt_target/$CC" in
  *-*-cygwin*/gcc*-mno-cygwin*|*-*-mingw*)
    # old mingw systems require "-dll" to link a DLL, while more recent ones
    # require "-mdll"
    SAVE_CFLAGS="$CFLAGS"
    CFLAGS="$CFLAGS -mdll"
    AC_CACHE_CHECK([how to link DLLs], lt_cv_cc_dll_switch,
      [AC_TRY_LINK([], [], [lt_cv_cc_dll_switch=-mdll],[lt_cv_cc_dll_switch=-dll])])
    CFLAGS="$SAVE_CFLAGS" ;;
  *-*-cygwin*)
    # cygwin systems need to pass --dll to the linker, and not link
    # crt.o which will require a WinMain@16 definition.
    lt_cv_cc_dll_switch="-Wl,--dll -nostartfiles" ;;
  esac
  ;;
  ])
esac
])

# AC_LIBTOOL_DLOPEN - enable checks for dlopen support
AC_DEFUN(AC_LIBTOOL_DLOPEN, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])])

# AC_LIBTOOL_WIN32_DLL - declare package support for building win32 dll's
AC_DEFUN(AC_LIBTOOL_WIN32_DLL, [AC_BEFORE([$0], [AC_LIBTOOL_SETUP])])

# AC_ENABLE_SHARED - implement the --enable-shared flag
# Usage: AC_ENABLE_SHARED[(DEFAULT)]
#   Where DEFAULT is either `yes' or `no'.  If omitted, it defaults to
#   `yes'.
AC_DEFUN(AC_ENABLE_SHARED, [dnl
define([AC_ENABLE_SHARED_DEFAULT], ifelse($1, no, no, yes))dnl
AC_ARG_ENABLE(shared,
changequote(<<, >>)dnl
<<  --enable-shared[=PKGS]  build shared libraries [default=>>AC_ENABLE_SHARED_DEFAULT],
changequote([, ])dnl
[p=${PACKAGE-default}
case "$enableval" in
yes) enable_shared=yes ;;
no) enable_shared=no ;;
*)
  enable_shared=no
  # Look at the argument we got.  We use all the common list separators.
  IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS="${IFS}:,"
  for pkg in $enableval; do
    if test "X$pkg" = "X$p"; then
      enable_shared=yes
    fi
  done
  IFS="$ac_save_ifs"
  ;;
esac],
enable_shared=AC_ENABLE_SHARED_DEFAULT)dnl
])

# AC_DISABLE_SHARED - set the default shared flag to --disable-shared
AC_DEFUN(AC_DISABLE_SHARED, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])dnl
AC_ENABLE_SHARED(no)])

# AC_ENABLE_STATIC - implement the --enable-static flag
# Usage: AC_ENABLE_STATIC[(DEFAULT)]
#   Where DEFAULT is either `yes' or `no'.  If omitted, it defaults to
#   `yes'.
AC_DEFUN(AC_ENABLE_STATIC, [dnl
define([AC_ENABLE_STATIC_DEFAULT], ifelse($1, no, no, yes))dnl
AC_ARG_ENABLE(static,
changequote(<<, >>)dnl
<<  --enable-static[=PKGS]  build static libraries [default=>>AC_ENABLE_STATIC_DEFAULT],
changequote([, ])dnl
[p=${PACKAGE-default}
case "$enableval" in
yes) enable_static=yes ;;
no) enable_static=no ;;
*)
  enable_static=no
  # Look at the argument we got.  We use all the common list separators.
  IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS="${IFS}:,"
  for pkg in $enableval; do
    if test "X$pkg" = "X$p"; then
      enable_static=yes
    fi
  done
  IFS="$ac_save_ifs"
  ;;
esac],
enable_static=AC_ENABLE_STATIC_DEFAULT)dnl
])

# AC_DISABLE_STATIC - set the default static flag to --disable-static
AC_DEFUN(AC_DISABLE_STATIC, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])dnl
AC_ENABLE_STATIC(no)])


# AC_ENABLE_FAST_INSTALL - implement the --enable-fast-install flag
# Usage: AC_ENABLE_FAST_INSTALL[(DEFAULT)]
#   Where DEFAULT is either `yes' or `no'.  If omitted, it defaults to
#   `yes'.
AC_DEFUN(AC_ENABLE_FAST_INSTALL, [dnl
define([AC_ENABLE_FAST_INSTALL_DEFAULT], ifelse($1, no, no, yes))dnl
AC_ARG_ENABLE(fast-install,
changequote(<<, >>)dnl
<<  --enable-fast-install[=PKGS]  optimize for fast installation [default=>>AC_ENABLE_FAST_INSTALL_DEFAULT],
changequote([, ])dnl
[p=${PACKAGE-default}
case "$enableval" in
yes) enable_fast_install=yes ;;
no) enable_fast_install=no ;;
*)
  enable_fast_install=no
  # Look at the argument we got.  We use all the common list separators.
  IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS="${IFS}:,"
  for pkg in $enableval; do
    if test "X$pkg" = "X$p"; then
      enable_fast_install=yes
    fi
  done
  IFS="$ac_save_ifs"
  ;;
esac],
enable_fast_install=AC_ENABLE_FAST_INSTALL_DEFAULT)dnl
])

# AC_ENABLE_FAST_INSTALL - set the default to --disable-fast-install
AC_DEFUN(AC_DISABLE_FAST_INSTALL, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])dnl
AC_ENABLE_FAST_INSTALL(no)])


# AC_PATH_TOOL_PREFIX - find a file program which can recognise shared library
AC_DEFUN(AC_PATH_TOOL_PREFIX,
[AC_MSG_CHECKING([for $1])
AC_CACHE_VAL(lt_cv_path_FILE,
[case "$FILE" in
  /*)
  lt_cv_path_FILE="$FILE" # Let the user override the test with a path.
  ;;
  ?:/*)
  ac_cv_path_FILE="$FILE" # Let the user override the test with a dos path.
  ;;
  *)
  ac_save_file="$FILE"
  IFS="${IFS=   }"; ac_save_ifs="$IFS"; IFS=":"
dnl $ac_dummy forces splitting on constant user-supplied paths.
dnl POSIX.2 word splitting is done only on the output of word expansions,
dnl not every word.  This closes a longstanding sh security hole.
  ac_dummy="ifelse([$2], , $PATH, [$2])"
  for ac_dir in $ac_dummy; do
    test -z "$ac_dir" && ac_dir=.
    if test -f $ac_dir/$1; then
      lt_cv_path_FILE="$ac_dir/$1"
      if test -n "$file_magic_test_file"; then
        case "$deplibs_check_method" in
        "file_magic "*)
          file_magic_regex="`expr \"$deplibs_check_method\" : \"file_magic \(.*\)\"`"
	  FILE="$lt_cv_path_FILE"
          if eval $file_magic_cmd \$file_magic_test_file 2> /dev/null |
            egrep "$file_magic_regex" > /dev/null; then
            :
          else
            cat <<EOF 1>&2

*** Warning: the command libtool uses to detect shared libraries,
*** $file_magic_cmd, produces output that libtool cannot recognize.
*** The result is that libtool may fail to recognize shared libraries
*** as such.  This will affect the creation of libtool libraries that
*** depend on shared libraries, but programs linked with such libtool
*** libraries will work regardless of this problem.  Nevertheless, you
*** may want to report the problem to your system manager and/or to
*** bug-libtool@gnu.org

EOF
          fi ;;
        esac
      fi
      break
    fi
  done
  IFS="$ac_save_ifs"
  FILE="$ac_save_file"
  ;;
esac])
FILE="$lt_cv_path_FILE"
if test -n "$FILE"; then
  AC_MSG_RESULT($FILE)
else
  AC_MSG_RESULT(no)
fi
])


# AC_PATH_FILE - find a file program which can recognise a shared library
AC_DEFUN(AC_PATH_FILE,
[AC_REQUIRE([AC_CHECK_TOOL_PREFIX])dnl
AC_PATH_TOOL_PREFIX(${ac_tool_prefix}file, /usr/bin:$PATH)
if test -z "$lt_cv_path_FILE"; then
  if test -n "$ac_tool_prefix"; then
    AC_PATH_TOOL_PREFIX(file, /usr/bin:$PATH)
  else
    FILE=:
  fi
fi
])


# AC_PROG_LD - find the path to the GNU or non-GNU linker
AC_DEFUN(AC_PROG_LD,
[AC_ARG_WITH(gnu-ld,
[  --with-gnu-ld           assume the C compiler uses GNU ld [default=no]],
test "$withval" = no || with_gnu_ld=yes, with_gnu_ld=no)
AC_REQUIRE([AC_PROG_CC])dnl
AC_REQUIRE([AC_CANONICAL_HOST])dnl
AC_REQUIRE([AC_CANONICAL_BUILD])dnl
ac_prog=ld
if test "$ac_cv_prog_gcc" = yes; then
  # Check if gcc -print-prog-name=ld gives a path.
  AC_MSG_CHECKING([for ld used by GCC])
  case $lt_target in
  *-*-mingw*)
    # gcc leaves a trailing carriage return which upsets mingw
    ac_prog=`($CC -print-prog-name=ld) 2>&5 | tr -d '\015'` ;;
  *)
    ac_prog=`($CC -print-prog-name=ld) 2>&5` ;;
  esac
  case "$ac_prog" in
    # Accept absolute paths.
changequote(,)dnl
    [\\/]* | [A-Za-z]:[\\/]*)
      re_direlt='/[^/][^/]*/\.\./'
changequote([,])dnl
      # Canonicalize the path of ld
      ac_prog=`echo $ac_prog| sed 's%\\\\%/%g'`
      while echo $ac_prog | grep "$re_direlt" > /dev/null 2>&1; do
	ac_prog=`echo $ac_prog| sed "s%$re_direlt%/%"`
      done
      test -z "$LD" && LD="$ac_prog"
      ;;
  "")
    # If it fails, then pretend we aren't using GCC.
    ac_prog=ld
    ;;
  *)
    # If it is relative, then search for the first ld in PATH.
    with_gnu_ld=unknown
    ;;
  esac
elif test "$with_gnu_ld" = yes; then
  AC_MSG_CHECKING([for GNU ld])
else
  AC_MSG_CHECKING([for non-GNU ld])
fi
AC_CACHE_VAL(ac_cv_path_LD,
[if test -z "$LD"; then
  IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS="${IFS}${PATH_SEPARATOR-:}"
  for ac_dir in $PATH; do
    test -z "$ac_dir" && ac_dir=.
    if test -f "$ac_dir/$ac_prog" || test -f "$ac_dir/$ac_prog$ac_exeext"; then
      ac_cv_path_LD="$ac_dir/$ac_prog"
      # Check to see if the program is GNU ld.  I'd rather use --version,
      # but apparently some GNU ld's only accept -v.
      # Break only if it was the GNU/non-GNU ld that we prefer.
      if "$ac_cv_path_LD" -v 2>&1 < /dev/null | egrep '(GNU|with BFD)' > /dev/null; then
	test "$with_gnu_ld" != no && break
      else
	test "$with_gnu_ld" != yes && break
      fi
    fi
  done
  IFS="$ac_save_ifs"
else
  ac_cv_path_LD="$LD" # Let the user override the test with a path.
fi])
LD="$ac_cv_path_LD"
if test -n "$LD"; then
  AC_MSG_RESULT($LD)
else
  AC_MSG_RESULT(no)
fi
test -z "$LD" && AC_MSG_ERROR([no acceptable ld found in \$PATH])
AC_PROG_LD_GNU
])

AC_DEFUN(AC_PROG_LD_GNU,
[AC_CACHE_CHECK([if the linker ($LD) is GNU ld], ac_cv_prog_gnu_ld,
[# I'd rather use --version here, but apparently some GNU ld's only accept -v.
if $LD -v 2>&1 </dev/null | egrep '(GNU|with BFD)' 1>&5; then
  ac_cv_prog_gnu_ld=yes
else
  ac_cv_prog_gnu_ld=no
fi])
with_gnu_ld=$ac_cv_prog_gnu_ld
])

# AC_PROG_LD_RELOAD_FLAG - find reload flag for linker
#   -- PORTME Some linkers may need a different reload flag.
AC_DEFUN(AC_PROG_LD_RELOAD_FLAG,
[AC_CACHE_CHECK([for $LD option to reload object files], lt_cv_ld_reload_flag,
[lt_cv_ld_reload_flag='-r'])
reload_flag=$lt_cv_ld_reload_flag
test -n "$reload_flag" && reload_flag=" $reload_flag"
])

# AC_DEPLIBS_CHECK_METHOD - how to check for library dependencies
#  -- PORTME fill in with the dynamic library characteristics
AC_DEFUN(AC_DEPLIBS_CHECK_METHOD,
[AC_CACHE_CHECK([how to recognise dependant libraries], 
lt_cv_deplibs_check_method,
[lt_cv_file_magic_cmd='$FILE'
lt_cv_file_magic_test_file=
lt_cv_deplibs_check_method='unknown'
# Need to set the preceding variable on all platforms that support
# interlibrary dependencies.
# 'none' -- dependencies not supported.
# `unknown' -- same as none, but documents that we really don't know.
# 'pass_all' -- all dependencies passed with no checks.
# 'test_compile' -- check by making test program.
# 'file_magic [regex]' -- check by looking for files in library path
# which responds to the $file_magic_cmd with a given egrep regex.
# If you have `file' or equivalent on your system and you're not sure
# whether `pass_all' will *always* work, you probably want this one.

case "$host_os" in
aix4* | beos*)
  lt_cv_deplibs_check_method=pass_all
  ;;
  
bsdi4*)
  lt_cv_deplibs_check_method='file_magic ELF [0-9][0-9]*-bit [ML]SB (shared object|dynamic lib)'
  lt_cv_file_magic_test_file=/shlib/libc.so
  ;;  

cygwin* | mingw*)
  lt_cv_deplibs_check_method='file_magic file format pei*-i386(.*architecture: i386)?'
  lt_cv_file_magic_cmd='${OBJDUMP} -f'
  ;;

freebsd*)
  case "$version_type" in
  freebsd-elf*)
    lt_cv_deplibs_check_method=pass_all
    ;;
  esac
  ;;
  
gnu*)
  lt_cv_deplibs_check_method=pass_all
  ;;
  
irix5* | irix6*)
  case "$host_os" in
  irix5*)
    # this will be overridden with pass_all, but let us keep it just in case
    lt_cv_deplibs_check_method="file_magic ELF 32-bit MSB dynamic lib MIPS - version 1"
    ;;
  *)
    case "$LD" in
    *-32|*"-32 ") libmagic=32-bit;;
    *-n32|*"-n32 ") libmagic=N32;;
    *-64|*"-64 ") libmagic=64-bit;;
    *) libmagic=never-match;;
    esac
    # this will be overridden with pass_all, but let us keep it just in case
    lt_cv_deplibs_check_method="file_magic ELF ${libmagic} MSB mips-[1234] dynamic lib MIPS - version 1"
    ;;
  esac
  lt_cv_file_magic_test_file=`echo /lib${libsuff}/libc.so*`
  lt_cv_deplibs_check_method=pass_all
  ;;

# This must be Linux ELF.
linux-gnu*)
  case "$host_cpu" in
  alpha* | i*86 | sparc* )
    lt_cv_deplibs_check_method=pass_all ;;
  *)
    # glibc up to 2.1.1 does not perform some relocations on ARM
    lt_cv_deplibs_check_method='file_magic ELF [0-9][0-9]*-bit [LM]SB (shared object|dynamic lib )' ;;
  esac
  lt_cv_file_magic_test_file=`echo /lib/libc.so* /lib/libc-*.so`
  ;;

osf3* | osf4* | osf5*)
  # this will be overridden with pass_all, but let us keep it just in case
  lt_cv_deplibs_check_method='file_magic COFF format alpha shared library'
  lt_cv_file_magic_test_file=/shlib/libc.so
  lt_cv_deplibs_check_method=pass_all
  ;;

sco3.2v5*)
  lt_cv_deplibs_check_method=pass_all
  ;;
  
solaris*)
  lt_cv_deplibs_check_method=pass_all
  lt_cv_file_magic_test_file=/lib/libc.so
  ;;

sysv4 | sysv4.2uw2* | sysv4.3* | sysv5*)
  case "$host_vendor" in
  ncr)
    lt_cv_deplibs_check_method=pass_all
    ;;
  motorola)
    lt_cv_deplibs_check_method='file_magic ELF [0-9][0-9]*-bit [ML]SB (shared object|dynamic lib) M[0-9][0-9]* Version [0-9]'
    lt_cv_file_magic_test_file=`echo /usr/lib/libc.so*`
    ;;
  esac
  ;;
esac
])
file_magic_cmd=$lt_cv_file_magic_cmd
deplibs_check_method=$lt_cv_deplibs_check_method
])


# AC_PROG_NM - find the path to a BSD-compatible name lister
AC_DEFUN(AC_PROG_NM,
[AC_MSG_CHECKING([for BSD-compatible nm])
AC_CACHE_VAL(ac_cv_path_NM,
[if test -n "$NM"; then
  # Let the user override the test.
  ac_cv_path_NM="$NM"
else
  IFS="${IFS= 	}"; ac_save_ifs="$IFS"; IFS="${IFS}${PATH_SEPARATOR-:}"
  for ac_dir in $PATH /usr/ccs/bin /usr/ucb /bin; do
    test -z "$ac_dir" && ac_dir=.
    if test -f $ac_dir/nm || test -f $ac_dir/nm$ac_exeext ; then
      # Check to see if the nm accepts a BSD-compat flag.
      # Adding the `sed 1q' prevents false positives on HP-UX, which says:
      #   nm: unknown option "B" ignored
      if ($ac_dir/nm -B /dev/null 2>&1 | sed '1q'; exit 0) | egrep /dev/null >/dev/null; then
	ac_cv_path_NM="$ac_dir/nm -B"
	break
      elif ($ac_dir/nm -p /dev/null 2>&1 | sed '1q'; exit 0) | egrep /dev/null >/dev/null; then
	ac_cv_path_NM="$ac_dir/nm -p"
	break
      else
	ac_cv_path_NM=${ac_cv_path_NM="$ac_dir/nm"} # keep the first match, but
	continue # so that we can try to find one that supports BSD flags
      fi
    fi
  done
  IFS="$ac_save_ifs"
  test -z "$ac_cv_path_NM" && ac_cv_path_NM=nm
fi])
NM="$ac_cv_path_NM"
AC_MSG_RESULT([$NM])
])

# AC_CHECK_LIBM - check for math library
AC_DEFUN(AC_CHECK_LIBM,
[AC_REQUIRE([AC_CANONICAL_HOST])dnl
LIBM=
case "$lt_target" in
*-*-beos* | *-*-cygwin*)
  # These system don't have libm
  ;;
*-ncr-sysv4.3*)
  AC_CHECK_LIB(mw, _mwvalidcheckl, LIBM="-lmw")
  AC_CHECK_LIB(m, main, LIBM="$LIBM -lm")
  ;;
*)
  AC_CHECK_LIB(m, main, LIBM="-lm")
  ;;
esac
])

# AC_LIBLTDL_CONVENIENCE[(dir)] - sets LIBLTDL to the link flags for
# the libltdl convenience library, adds --enable-ltdl-convenience to
# the configure arguments.  Note that LIBLTDL is not AC_SUBSTed, nor
# is AC_CONFIG_SUBDIRS called.  If DIR is not provided, it is assumed
# to be `${top_builddir}/libltdl'.  Make sure you start DIR with
# '${top_builddir}/' (note the single quotes!) if your package is not
# flat, and, if you're not using automake, define top_builddir as
# appropriate in the Makefiles.
AC_DEFUN(AC_LIBLTDL_CONVENIENCE, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])dnl
  case "$enable_ltdl_convenience" in
  no) AC_MSG_ERROR([this package needs a convenience libltdl]) ;;
  "") enable_ltdl_convenience=yes
      ac_configure_args="$ac_configure_args --enable-ltdl-convenience" ;;
  esac
  LIBLTDL=ifelse($#,1,$1,['${top_builddir}/libltdl'])/libltdlc.la
  INCLTDL=ifelse($#,1,-I$1,
  ['-I${top_builddir}/libltdl -I${top_srcdir}/libltdl'])
])

# AC_LIBLTDL_INSTALLABLE[(dir)] - sets LIBLTDL to the link flags for
# the libltdl installable library, and adds --enable-ltdl-install to
# the configure arguments.  Note that LIBLTDL is not AC_SUBSTed, nor
# is AC_CONFIG_SUBDIRS called.  If DIR is not provided, it is assumed
# to be `${top_builddir}/libltdl'.  Make sure you start DIR with
# '${top_builddir}/' (note the single quotes!) if your package is not
# flat, and, if you're not using automake, define top_builddir as
# appropriate in the Makefiles.
# In the future, this macro may have to be called after AC_PROG_LIBTOOL.
AC_DEFUN(AC_LIBLTDL_INSTALLABLE, [AC_BEFORE([$0],[AC_LIBTOOL_SETUP])dnl
  AC_CHECK_LIB(ltdl, main,
  [test x"$enable_ltdl_install" != xyes && enable_ltdl_install=no],
  [if test x"$enable_ltdl_install" = xno; then
     AC_MSG_WARN([libltdl not installed, but installation disabled])
   else
     enable_ltdl_install=yes
   fi
  ])
  if test x"$enable_ltdl_install" = x"yes"; then
    ac_configure_args="$ac_configure_args --enable-ltdl-install"
    LIBLTDL=ifelse($#,1,$1,['${top_builddir}/libltdl'])/libltdl.la
    INCLTDL=ifelse($#,1,-I$1,
    ['-I${top_builddir}/libltdl -I${top_srcdir}/libltdl'])
  else
    ac_configure_args="$ac_configure_args --enable-ltdl-install=no"
    LIBLTDL="-lltdl"
    INCLTDL=
  fi
])

dnl old names
AC_DEFUN(AM_PROG_LIBTOOL, [indir([AC_PROG_LIBTOOL])])dnl
AC_DEFUN(AM_ENABLE_SHARED, [indir([AC_ENABLE_SHARED], $@)])dnl
AC_DEFUN(AM_ENABLE_STATIC, [indir([AC_ENABLE_STATIC], $@)])dnl
AC_DEFUN(AM_DISABLE_SHARED, [indir([AC_DISABLE_SHARED], $@)])dnl
AC_DEFUN(AM_DISABLE_STATIC, [indir([AC_DISABLE_STATIC], $@)])dnl
AC_DEFUN(AM_PROG_LD, [indir([AC_PROG_LD])])dnl
AC_DEFUN(AM_PROG_NM, [indir([AC_PROG_NM])])dnl

dnl This is just to silence aclocal about the macro not being used
ifelse([AC_DISABLE_FAST_INSTALL])dnl

# Do all the work for Automake.  This macro actually does too much --
# some checks are only needed if your package does certain things.
# But this isn't really a big deal.

# serial 1

dnl Usage:
dnl AM_INIT_AUTOMAKE(package,version, [no-define])

AC_DEFUN(AM_INIT_AUTOMAKE,
[AC_REQUIRE([AC_PROG_INSTALL])
dnl We require 2.13 because we rely on SHELL being computed by configure.
AC_PREREQ([2.13])
PACKAGE=[$1]
AC_SUBST(PACKAGE)
VERSION=[$2]
AC_SUBST(VERSION)
dnl test to see if srcdir already configured
if test "`CDPATH=: && cd $srcdir && pwd`" != "`pwd`" &&
   test -f $srcdir/config.status; then
  AC_MSG_ERROR([source directory already configured; run "make distclean" there first])
fi
ifelse([$3],,
AC_DEFINE_UNQUOTED(PACKAGE, "$PACKAGE", [Name of package])
AC_DEFINE_UNQUOTED(VERSION, "$VERSION", [Version number of package]))
AC_REQUIRE([AM_SANITY_CHECK])
AC_REQUIRE([AC_ARG_PROGRAM])
AM_MISSING_PROG(ACLOCAL, aclocal)
AM_MISSING_PROG(AUTOCONF, autoconf)
AM_MISSING_PROG(AUTOMAKE, automake)
AM_MISSING_PROG(AUTOHEADER, autoheader)
AM_MISSING_PROG(MAKEINFO, makeinfo)
AM_MISSING_PROG(AMTAR, tar)
AM_MISSING_INSTALL_SH
dnl We need awk for the "check" target.  The system "awk" is bad on
dnl some platforms.
AC_REQUIRE([AC_PROG_AWK])
AC_REQUIRE([AC_PROG_MAKE_SET])
AC_REQUIRE([AM_DEP_TRACK])
AC_REQUIRE([AM_SET_DEPDIR])
ifdef([AC_PROVIDE_AC_PROG_CC], [AM_DEPENDENCIES(CC)], [
   define([AC_PROG_CC], defn([AC_PROG_CC])[AM_DEPENDENCIES(CC)])])
ifdef([AC_PROVIDE_AC_PROG_CXX], [AM_DEPENDENCIES(CXX)], [
   define([AC_PROG_CXX], defn([AC_PROG_CXX])[AM_DEPENDENCIES(CXX)])])
])

#
# Check to make sure that the build environment is sane.
#

AC_DEFUN(AM_SANITY_CHECK,
[AC_MSG_CHECKING([whether build environment is sane])
# Just in case
sleep 1
echo timestamp > conftestfile
# Do `set' in a subshell so we don't clobber the current shell's
# arguments.  Must try -L first in case configure is actually a
# symlink; some systems play weird games with the mod time of symlinks
# (eg FreeBSD returns the mod time of the symlink's containing
# directory).
if (
   set X `ls -Lt $srcdir/configure conftestfile 2> /dev/null`
   if test "[$]*" = "X"; then
      # -L didn't work.
      set X `ls -t $srcdir/configure conftestfile`
   fi
   if test "[$]*" != "X $srcdir/configure conftestfile" \
      && test "[$]*" != "X conftestfile $srcdir/configure"; then

      # If neither matched, then we have a broken ls.  This can happen
      # if, for instance, CONFIG_SHELL is bash and it inherits a
      # broken ls alias from the environment.  This has actually
      # happened.  Such a system could not be considered "sane".
      AC_MSG_ERROR([ls -t appears to fail.  Make sure there is not a broken
alias in your environment])
   fi

   test "[$]2" = conftestfile
   )
then
   # Ok.
   :
else
   AC_MSG_ERROR([newly created file is older than distributed files!
Check your system clock])
fi
rm -f conftest*
AC_MSG_RESULT(yes)])

dnl AM_MISSING_PROG(NAME, PROGRAM)
AC_DEFUN(AM_MISSING_PROG, [
AC_REQUIRE([AM_MISSING_HAS_RUN])
$1=${$1-"${am_missing_run}$2"}
AC_SUBST($1)])

dnl Like AM_MISSING_PROG, but only looks for install-sh.
dnl AM_MISSING_INSTALL_SH()
AC_DEFUN(AM_MISSING_INSTALL_SH, [
AC_REQUIRE([AM_MISSING_HAS_RUN])
if test -z "$install_sh"; then
   install_sh="$ac_aux_dir/install-sh"
   test -f "$install_sh" || install_sh="$ac_aux_dir/install.sh"
   test -f "$install_sh" || install_sh="${am_missing_run}${ac_auxdir}/install-sh"
   dnl FIXME: an evil hack: we remove the SHELL invocation from
   dnl install_sh because automake adds it back in.  Sigh.
   install_sh="`echo $install_sh | sed -e 's/\${SHELL}//'`"
fi
AC_SUBST(install_sh)])

dnl AM_MISSING_HAS_RUN.
dnl Define MISSING if not defined so far and test if it supports --run.
dnl If it does, set am_missing_run to use it, otherwise, to nothing.
AC_DEFUN([AM_MISSING_HAS_RUN], [
test x"${MISSING+set}" = xset || \
  MISSING="\${SHELL} `CDPATH=: && cd $ac_aux_dir && pwd`/missing"
dnl Use eval to expand $SHELL
if eval "$MISSING --run :"; then
  am_missing_run="$MISSING --run "
else
  am_missing_run=
  AC_MSG_WARN([`missing' script is too old or missing])
fi
])

dnl See how the compiler implements dependency checking.
dnl Usage:
dnl AM_DEPENDENCIES(NAME)
dnl NAME is "CC", "CXX" or "OBJC".

dnl We try a few techniques and use that to set a single cache variable.

AC_DEFUN(AM_DEPENDENCIES,[
AC_REQUIRE([AM_SET_DEPDIR])
AC_REQUIRE([AM_OUTPUT_DEPENDENCY_COMMANDS])
ifelse([$1],CC,[
AC_REQUIRE([AC_PROG_CC])
AC_REQUIRE([AC_PROG_CPP])
depcc="$CC"
depcpp="$CPP"],[$1],CXX,[
AC_REQUIRE([AC_PROG_CXX])
AC_REQUIRE([AC_PROG_CXXCPP])
depcc="$CXX"
depcpp="$CXXCPP"],[$1],OBJC,[
am_cv_OBJC_dependencies_compiler_type=gcc],[
AC_REQUIRE([AC_PROG_][$1])
depcc="$[$1]"
depcpp=""])
AC_MSG_CHECKING([dependency style of $depcc])
AC_CACHE_VAL(am_cv_[$1]_dependencies_compiler_type,[
if test -z "$AMDEP"; then
  echo '#include "conftest.h"' > conftest.c
  echo 'int i;' > conftest.h

  am_cv_[$1]_dependencies_compiler_type=none
  for depmode in `sed -n 's/^#*\([a-zA-Z0-9]*\))$/\1/p' < "$am_depcomp"`; do
    case "$depmode" in
    nosideeffect)
      # after this tag, mechanisms are not by side-effect, so they'll
      # only be used when explicitly requested
      if test "x$enable_dependency_tracking" = xyes; then
	continue
      else
	break
      fi
      ;;
    none) break ;;
    esac
    if depmode="$depmode" \
       source=conftest.c object=conftest.o \
       depfile=conftest.Po tmpdepfile=conftest.TPo \
       $SHELL $am_depcomp $depcc -c conftest.c 2>/dev/null &&
       grep conftest.h conftest.Po > /dev/null 2>&1; then
      am_cv_[$1]_dependencies_compiler_type="$depmode"
      break
    fi
  done

  rm -f conftest.*
else
  am_cv_[$1]_dependencies_compiler_type=none
fi
])
AC_MSG_RESULT($am_cv_[$1]_dependencies_compiler_type)
[$1]DEPMODE="depmode=$am_cv_[$1]_dependencies_compiler_type"
AC_SUBST([$1]DEPMODE)
])

dnl Choose a directory name for dependency files.
dnl This macro is AC_REQUIREd in AM_DEPENDENCIES

AC_DEFUN(AM_SET_DEPDIR,[
if test -d .deps || mkdir .deps 2> /dev/null || test -d .deps; then
  DEPDIR=.deps
else
  DEPDIR=_deps
fi
AC_SUBST(DEPDIR)
])

AC_DEFUN(AM_DEP_TRACK,[
AC_ARG_ENABLE(dependency-tracking,
[  --disable-dependency-tracking Speeds up one-time builds
  --enable-dependency-tracking  Do not reject slow dependency extractors])
if test "x$enable_dependency_tracking" = xno; then
  AMDEP="#"
else
  am_depcomp="$ac_aux_dir/depcomp"
  if test ! -f "$am_depcomp"; then
    AMDEP="#"
  else
    AMDEP=
  fi
fi
AC_SUBST(AMDEP)
if test -z "$AMDEP"; then
  AMDEPBACKSLASH='\'
else
  AMDEPBACKSLASH=
fi
pushdef([subst], defn([AC_SUBST]))
subst(AMDEPBACKSLASH)
popdef([subst])
])

dnl Generate code to set up dependency tracking.
dnl This macro should only be invoked once -- use via AC_REQUIRE.
dnl Usage:
dnl AM_OUTPUT_DEPENDENCY_COMMANDS

dnl
dnl This code is only required when automatic dependency tracking
dnl is enabled.  FIXME.  This creates each `.P' file that we will
dnl need in order to bootstrap the dependency handling code.
AC_DEFUN(AM_OUTPUT_DEPENDENCY_COMMANDS,[
AC_OUTPUT_COMMANDS([
test x"$AMDEP" != x"" ||
for mf in $CONFIG_FILES; do
  case "$mf" in
  Makefile) dirpart=.;;
  */Makefile) dirpart=`echo "$mf" | sed -e 's|/[^/]*$||'`;;
  *) continue;;
  esac
  grep '^DEP_FILES *= *[^ #]' < "$mf" > /dev/null || continue
  # Extract the definition of DEP_FILES from the Makefile without
  # running `make'.
  DEPDIR=`sed -n -e '/^DEPDIR = / s///p' < "$mf"`
  test -z "$DEPDIR" && continue
  # When using ansi2knr, U may be empty or an underscore; expand it
  U=`sed -n -e '/^U = / s///p' < "$mf"`
  test -d "$dirpart/$DEPDIR" || mkdir "$dirpart/$DEPDIR"
  # We invoke sed twice because it is the simplest approach to
  # changing $(DEPDIR) to its actual value in the expansion.
  for file in `sed -n -e '
    /^DEP_FILES = .*\\\\$/ {
      s/^DEP_FILES = //
      :loop
	s/\\\\$//
	p
	n
	/\\\\$/ b loop
      p
    }
    /^DEP_FILES = / s/^DEP_FILES = //p' < "$mf" | \
       sed -e 's/\$(DEPDIR)/'"$DEPDIR"'/g' -e 's/\$U/'"$U"'/g'`; do
    # Make sure the directory exists.
    test -f "$dirpart/$file" && continue
    fdir=`echo "$file" | sed -e 's|/[^/]*$||'`
    $ac_aux_dir/mkinstalldirs "$dirpart/$fdir" > /dev/null 2>&1
    # echo "creating $dirpart/$file"
    echo '# dummy' > "$dirpart/$file"
  done
done
], [AMDEP="$AMDEP"
ac_aux_dir="$ac_aux_dir"])])

# Like AC_CONFIG_HEADER, but automatically create stamp file.

AC_DEFUN(AM_CONFIG_HEADER,
[AC_PREREQ([2.12])
AC_CONFIG_HEADER([$1])
dnl When config.status generates a header, we must update the stamp-h file.
dnl This file resides in the same directory as the config header
dnl that is generated.  We must strip everything past the first ":",
dnl and everything past the last "/".
AC_OUTPUT_COMMANDS(changequote(<<,>>)dnl
ifelse(patsubst(<<$1>>, <<[^ ]>>, <<>>), <<>>,
<<test -z "<<$>>CONFIG_HEADERS" || echo timestamp > patsubst(<<$1>>, <<^\([^:]*/\)?.*>>, <<\1>>)stamp-h<<>>dnl>>,
<<am_indx=1
for am_file in <<$1>>; do
  case " <<$>>CONFIG_HEADERS " in
  *" <<$>>am_file "*<<)>>
    echo timestamp > `echo <<$>>am_file | sed -e 's%:.*%%' -e 's%[^/]*$%%'`stamp-h$am_indx
    ;;
  esac
  am_indx=`expr "<<$>>am_indx" + 1`
done<<>>dnl>>)
changequote([,]))])

# Add --enable-maintainer-mode option to configure.
# From Jim Meyering

# serial 1

AC_DEFUN(AM_MAINTAINER_MODE,
[AC_MSG_CHECKING([whether to enable maintainer-specific portions of Makefiles])
  dnl maintainer-mode is disabled by default
  AC_ARG_ENABLE(maintainer-mode,
[  --enable-maintainer-mode enable make rules and dependencies not useful
                          (and sometimes confusing) to the casual installer],
      USE_MAINTAINER_MODE=$enableval,
      USE_MAINTAINER_MODE=no)
  AC_MSG_RESULT($USE_MAINTAINER_MODE)
  AM_CONDITIONAL(MAINTAINER_MODE, test $USE_MAINTAINER_MODE = yes)
  MAINT=$MAINTAINER_MODE_TRUE
  AC_SUBST(MAINT)dnl
]
)

# Define a conditional.

AC_DEFUN(AM_CONDITIONAL,
[AC_SUBST($1_TRUE)
AC_SUBST($1_FALSE)
if $2; then
  $1_TRUE=
  $1_FALSE='#'
else
  $1_TRUE='#'
  $1_FALSE=
fi])

