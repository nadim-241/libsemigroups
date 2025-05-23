dnl Process this file with autoconf to produce a configure script.

dnl Autoconf and automake initialization.

AC_PREREQ([2.69])
AC_INIT([libsemigroups],m4_esyscmd([etc/version-number.sh | tr -d "\n"]),[jdm3@st-andrews.ac.uk])
AC_CONFIG_SRCDIR(include/libsemigroups/libsemigroups.hpp)
AC_CONFIG_HEADERS(config/config.h)
AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_AUX_DIR(config)
AC_CANONICAL_TARGET

dnl Set default CFLAGS/CXXFLAGS to nothing, to avoid passing -g -O2 as
dnl the default C/CXXFLAGS when compiling in, e.g. debug mode
: ${CFLAGS=""}
: ${CXXFLAGS=""}

AM_INIT_AUTOMAKE([1.11 -Wall foreign subdir-objects tar-pax])
AM_SILENT_RULES([yes])
AM_PROG_AR

AX_PREFIX_CONFIG_H([include/libsemigroups/config.hpp],[],[config/config.h])

AC_PROG_CXX
AC_LANG([C++])
AX_CXX_COMPILE_STDCXX_17(,[mandatory])

dnl ## Check for pthread, this seems to be required to compile with GCC
AC_LANG_PUSH([C])
AX_PTHREAD(,[AC_MSG_ERROR([pthread is required])])
AC_CHECK_LIB([pthread], [pthread_create])

AM_MAINTAINER_MODE

AC_SUBST(ac_aux_dir)

dnl Checks for programs.

AC_PROG_INSTALL
AC_PROG_LN_S
LT_INIT

# Checks for header files.
AC_CHECK_HEADERS([limits.h stdint.h stdlib.h sys/time.h unistd.h pthread.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_CHECK_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_INT64_T
AC_TYPE_SIZE_T
AC_TYPE_UINT64_T
AC_CHECK_TYPES([ptrdiff_t])
AC_CHECK_SIZEOF([void *])

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([gettimeofday memset pow sqrt])
AC_LANG_POP([C])

# To handle the configure option `feature` (specified using either
# --enable-feature or --disable-feature) use:
# AC_ARG_ENABLE(feature, help-str, [action-if-given], [action-if-not-given]).

# Note that action-if-given is performed if in --disable-feature is specified.

########################################
# debug
########################################

AC_MSG_CHECKING([whether to enable debug mode])

# Check if --enable-debug or --disable-debug was specified, and provide the help
# string for the flag. If a flag was specified, set the value of debug
# accordingly. Otherwise, if a flag was not specified, set debug to false.
AC_ARG_ENABLE([debug],
    [AS_HELP_STRING([--enable-debug], [enable debug mode])],
    [case "${enableval}" in
        yes) debug=yes ;;
        no)  debug=no ;;
        *) AC_MSG_ERROR([bad value ${enableval} for --enable-debug]) ;;
    esac],
    [debug=no])
AC_MSG_RESULT([$debug])

# Sets a conditional value that can be used in Makefile.am
AM_CONDITIONAL([LIBSEMIGROUPS_DEBUG], [test "x$debug" = "xyes"])

# Sets the C++ preprocessor macro that goes into config.hpp
AS_IF([test "x$debug" = "xyes"],
    AC_DEFINE([DEBUG], [1], [define if building in debug mode]))

########################################
# compile-warnings
########################################

AC_MSG_CHECKING([whether enable compiler warnings])

# Check if --enable-compile-warnings or --disable-compile-warnings was
# specified, and provide the help string for the flag. If a flag was specified,
# set the value of compile_warnings accordingly. Otherwise, if a flag was not
# specified, set compile_warnings to no.
AC_ARG_ENABLE([compile-warnings],
    [AS_HELP_STRING([--enable-compile-warnings], [enable compiler warnings])],
    [case "${enableval}" in
        yes) compile_warnings=yes ;;
        no)  compile_warnings=no ;;
        *) AC_MSG_ERROR([bad value ${enableval} for --enable-compile-warnings]) ;;
    esac],
    [compile_warnings=no])
AC_MSG_RESULT([$compile_warnings])

AS_IF([test "x$compile_warnings" = "xyes"],
  [ax_enable_compile_warnings=yes
   AX_COMPILER_FLAGS_CXXFLAGS([WARNING_CXXFLAGS], [], [ dnl
       -pedantic dnl
       -Wold-style-cast])
   AC_SUBST([WARNING_CXXFLAGS])])

########################################
# backward
########################################

AC_MSG_CHECKING([whether to enable backward mode])

# Check if --enable-backward or --disable-backward was specified, and provide
# the help string for the flag. If a flag was specified, set the value of
# backward accordingly. Otherwise, if a flag was not specified, set backward to
# yes.
AC_ARG_ENABLE([backward],
    [AS_HELP_STRING([--disable-backward], [disable backward])],
    [case "${enableval}" in
        yes) backward=yes ;;
        no)  backward=no ;;
        *) AC_MSG_ERROR([bad value ${enableval} for --enable-backward]) ;;
    esac],
    [backward=yes]
  )
AC_MSG_RESULT([$backward])

AS_IF([test "x$backward" = "xyes"], [
  AC_CHECK_HEADER(execinfo.h,
    [AC_DEFINE([BACKWARD_ENABLED], [1], [define if building with backward-cpp enabled])],
    [AC_MSG_WARN([backward enabled but execinfo.h not found, disabling backward!])])
])

# Check if code coverage mode is enabled
AX_CODE_COVERAGE()

# Check if HPCombi is enable, and available
AX_CHECK_HPCOMBI()

# Check if the vendored fmt should be used or not
AX_CHECK_FMT()

# Check if the vendored eigen should be used or not, or if eigen should be
# disabled altogether
AX_CHECK_EIGEN()

dnl Output configured files

dnl compiler builtins
AC_DEFUN([CHECK_COMPILER_BUILTIN],
[AC_MSG_CHECKING([for $1])
    AC_LINK_IFELSE(
        [AC_LANG_PROGRAM(
            [[]],
            [$1[($2)];
            ]
        )],
        [AS_VAR_SET([[have_]$1], [yes])],
        [AS_VAR_SET([[have_]$1], [no])]
        )
    AC_MSG_RESULT(AS_VAR_GET([[have_]$1]))
    AS_IF([test yes = AS_VAR_GET([[have_]$1])],
        [AC_DEFINE_UNQUOTED(AS_TR_CPP([HAVE_]$1), 1,
            [Define to 1 if the system has the `]$1[' built-in function])], []
        )])

CHECK_COMPILER_BUILTIN([__builtin_popcountl],[0]);
CHECK_COMPILER_BUILTIN([__builtin_clzll],[0]);

dnl
dnl User setting: Enable popcnt (on by default)
dnl
AC_MSG_CHECKING([whether to try and use __builtin_popcntl])
AC_ARG_ENABLE([popcnt],
    AS_HELP_STRING([--enable-popcnt], [use __builtin_popcntl if available]),
    [case "${enableval}" in
        yes) popcnt=yes ;;
        no)  popcnt=no ;;
        *) AC_MSG_ERROR([bad value ${enableval} for --enable-popcnt]) ;;
    esac],
    [popcnt=yes])
AC_MSG_RESULT([$popcnt])

AS_IF([test "x$popcnt" = "xyes"],
    [USE_POPCNT=1],
    [USE_POPCNT=0])

AC_DEFINE_UNQUOTED([USE_POPCNT],
    [$USE_POPCNT],
    [define as 1 if we should try and use the __builtin_popcntl function if available])

dnl
dnl User setting: Enable clz (on by default)
dnl
AC_MSG_CHECKING([whether to try and use __builtin_clzlll])
AC_ARG_ENABLE([clzll],
    AS_HELP_STRING([--enable-clzll], [use __builtin_clzll if available]),
    [case "${enableval}" in
        yes) clzll=yes ;;
        no)  clzll=no ;;
        *) AC_MSG_ERROR([bad value ${enableval} for --enable-clzll]) ;;
    esac],
    [clzll=yes])
AC_MSG_RESULT([$clzll])

AS_IF([test "x$clzll" = "xyes"],
    [USE_CLZLL=1],
    [USE_CLZLL=0])

AC_DEFINE_UNQUOTED([USE_CLZLL],
    [$USE_CLZLL],
    [define as 1 if we should try and use the __builtin_clzlll function if available])

AC_CONFIG_FILES([Makefile libsemigroups.pc])
AC_OUTPUT
