/* config.h - hand edited by Stefan Bellon to suit RISC OS needs
 *	Copyright (C) 2001 Free Software Foundation, Inc.
 *
 * This file is part of GNUPG.
 *
 * GNUPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * GNUPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301,
 * USA.
 */
#ifndef G10_CONFIG_H
#define G10_CONFIG_H

/* need this, because some autoconf tests rely on this (e.g. stpcpy)
 * and it should be used for new programs
 */
#define _GNU_SOURCE  1


/* Define if using alloca.c.  */
#undef C_ALLOCA

/* Define to empty if the keyword does not work.  */
/* #undef const */

/* Define to one of _getb67, GETB67, getb67 for Cray-2 and Cray-YMP systems.
   This function is required for alloca.c support on those systems.  */
#undef CRAY_STACKSEG_END

/* Define if you have alloca, as a function or macro.  */
/* #undef HAVE_ALLOCA */
#define HAVE_ALLOCA 1

/* Define if you have <alloca.h> and it should be used (not on Ultrix).  */
/* #undef HAVE_ALLOCA_H */
#define HAVE_ALLOCA_H 1

/* #undef _LIBC */

/* Define if you don't have vprintf but do have _doprnt.  */
#undef HAVE_DOPRNT

/* Define if you have the vprintf function.  */
#define HAVE_VPRINTF 1

/* Define to `long' if <sys/types.h> doesn't define.  */
#undef off_t

/* Define if you need to in order for stat and other things to work.  */
#undef _POSIX_SOURCE

/* Define as the return type of signal handlers (int or void).  */
#define RETSIGTYPE void

/* Define to `unsigned' if <sys/types.h> doesn't define.  */
#define size_t unsigned int

/* If using the C implementation of alloca, define if you know the
   direction of stack growth for your system; otherwise it will be
   automatically deduced at run-time.
 STACK_DIRECTION > 0 => grows toward higher addresses
 STACK_DIRECTION < 0 => grows toward lower addresses
 STACK_DIRECTION = 0 => direction of growth unknown
 */
#undef STACK_DIRECTION

/* Define if you have the ANSI C header files.  */
#define STDC_HEADERS 1

/* Define if `sys_siglist' is declared by <signal.h>.  */
#define SYS_SIGLIST_DECLARED 1

#undef M_DEBUG
#undef M_GUARD
#define PRINTABLE_OS_NAME "RISC OS"

/* Define if your locale.h file contains LC_MESSAGES.  */
#define HAVE_LC_MESSAGES 1

#define LOCALEDIR ""

/* Define to 1 if NLS is requested.  */
#define ENABLE_NLS 1

/* Define as 1 if you have catgets and don't want to use GNU gettext.  */
#undef HAVE_CATGETS

/* Define as 1 if you have gettext and don't want to use GNU gettext.  */
#undef HAVE_GETTEXT

#undef BIG_ENDIAN_HOST
#define LITTLE_ENDIAN_HOST 1

#undef HAVE_BYTE_TYPEDEF
#undef HAVE_USHORT_TYPEDEF
#undef HAVE_ULONG_TYPEDEF
#undef HAVE_U16_TYPEDEF
#undef HAVE_U32_TYPEDEF

#undef HAVE_BROKEN_MLOCK

/* defined if we have a /dev/random and /dev/urandom */
#undef HAVE_DEV_RANDOM
/* and the real names of the random devices */
#undef NAME_OF_DEV_RANDOM
#undef NAME_OF_DEV_URANDOM
/* Linux has an ioctl */
#undef HAVE_DEV_RANDOM_IOCTL

/* see cipher/rndegd.c */
#undef EGD_SOCKET_NAME

#undef USE_DYNAMIC_LINKING
#undef HAVE_DL_DLOPEN
#undef HAVE_DL_SHL_LOAD
#undef HAVE_DLD_DLD_LINK

#undef USE_SHM_COPROCESSING

#undef IPC_HAVE_SHM_LOCK
#undef IPC_RMID_DEFERRED_RELEASE

/* set this to limit filenames to the 8.3 format */
#undef USE_ONLY_8DOT3
/* defined if we must run on a stupid file system */
#undef HAVE_DRIVE_LETTERS
/* defined if we run on some of the PCDOS like systems (DOS, Windoze. OS/2)
 * with special properties like no file modes */
#undef HAVE_DOSISH_SYSTEM
/* because the Unix gettext has to much overhead on MingW32 systems
 * and these systems lack Posix functions, we use a simplified version
 * of gettext */
#undef USE_SIMPLE_GETTEXT
/* At some point in the system we need to know that we use the Windows
 * random module. */
#undef USE_STATIC_RNDW32

#undef USE_CAPABILITIES

/* Some systems have mkdir that takes a single argument. */
#undef MKDIR_TAKES_ONE_ARG

/* The number of bytes in a unsigned int.  */
#define SIZEOF_UNSIGNED_INT 4

/* The number of bytes in a unsigned long.  */
#define SIZEOF_UNSIGNED_LONG 4

/* The number of bytes in a unsigned long long.  */
/* Is defined later on */
/* #define SIZEOF_UNSIGNED_LONG_LONG 0 */

/* The number of bytes in a unsigned short.  */
#define SIZEOF_UNSIGNED_SHORT 2

/* Define if you have the __argz_count function.  */
#undef HAVE___ARGZ_COUNT

/* Define if you have the __argz_next function.  */
#undef HAVE___ARGZ_NEXT

/* Define if you have the __argz_stringify function.  */
#undef HAVE___ARGZ_STRINGIFY

/* Define if you have the atexit function.  */
#define HAVE_ATEXIT 1

/* Define if you have the clock_gettime function.  */
#undef HAVE_CLOCK_GETTIME

/* Define if you have the dcgettext function.  */
#undef HAVE_DCGETTEXT

/* Define if you have the dlopen function.  */
#undef HAVE_DLOPEN

/* Define if you have the fopen64 function.  */
#undef HAVE_FOPEN64

/* Define if you have the fstat64 function.  */
#undef HAVE_FSTAT64

/* Define if you have the getcwd function.  */
#define HAVE_GETCWD 1

/* Define if you have the gethrtime function.  */
#undef HAVE_GETHRTIME

/* Define if you have the getpagesize function.  */
#define HAVE_GETPAGESIZE 1

/* Define if you have the getrusage function.  */
#define HAVE_GETRUSAGE 1

/* Define if you have the gettimeofday function.  */
#define HAVE_GETTIMEOFDAY 1

/* Define if you have the memicmp function.  */
#undef HAVE_MEMICMP

/* Define if you have the memmove function.  */
#define HAVE_MEMMOVE 1

/* Define if you have the mlock function.  */
#undef HAVE_MLOCK

/* Define if you have the mmap function.  */
#undef HAVE_MMAP

/* Define if you have the munmap function.  */
#undef HAVE_MUNMAP

/* Define if you have the nl_langinfo function.  */
#undef HAVE_NL_LANGINFO

/* Define if you have the putenv function.  */
#define HAVE_PUTENV 1

/* Define if you have the raise function.  */
#define HAVE_RAISE 1

/* Define if you have the rand function.  */
#define HAVE_RAND 1

/* Define if you have the setenv function.  */
#define HAVE_SETENV 1

/* Define if you have the setlocale function.  */
#define HAVE_SETLOCALE 1

/* Define if you have the setrlimit function.  */
#define HAVE_SETRLIMIT 1

/* Define if you have the sigaction function.  */
#define HAVE_SIGACTION 1

/* Define if you have the sigprocmask function.  */
#define HAVE_SIGPROCMASK 1

/* Define if you have the stpcpy function.  */
#define HAVE_STPCPY 1

/* Define if you have the strcasecmp function.  */
#define HAVE_STRCASECMP 1

/* Define if you have the strchr function.  */
#define HAVE_STRCHR 1

/* Define if you have the strdup function.  */
#define HAVE_STRDUP 1

/* Define if you have the strerror function.  */
#define HAVE_STRERROR 1

/* Define if you have the strftime function.  */
#define HAVE_STRFTIME 1

/* Define if you have the stricmp function.  */
#define HAVE_STRICMP 1

/* Define if you have the strlwr function.  */
#undef HAVE_STRLWR

/* Define if you have the strtoul function.  */
#define HAVE_STRTOUL 1

/* Define if you have the strsep function.  */
#define HAVE_STRSEP 1

/* Define if you have the tcgetattr function.  */
#undef HAVE_TCGETATTR

/* Define if you have the wait4 function.  */
#define HAVE_WAIT4 1

/* Define if you have the waitpid function.  */
#define HAVE_WAITPID 1

/* Define if you have the <argz.h> header file.  */
#undef HAVE_ARGZ_H

/* Define if you have the <direct.h> header file.  */
#undef HAVE_DIRECT_H

/* Define if you have the <gdbm.h> header file.  */
#undef HAVE_GDBM_H

/* Define if you have the <langinfo.h> header file.  */
#undef HAVE_LANGINFO_H

/* Define if you have the <limits.h> header file.  */
#define HAVE_LIMITS_H 1

/* Define if you have the <linux/random.h> header file.  */
#undef HAVE_LINUX_RANDOM_H

/* Define if you have the <locale.h> header file.  */
#define HAVE_LOCALE_H 1

/* Define if you have the <malloc.h> header file.  */
#define HAVE_MALLOC_H 1

/* Define if you have the <nl_types.h> header file.  */
#undef HAVE_NL_TYPES_H

/* Define if you have the <string.h> header file.  */
#define HAVE_STRING_H 1

/* Define if you have the <sys/capability.h> header file.  */
#undef HAVE_SYS_CAPABILITY_H

/* Define if you have the <sys/ipc.h> header file.  */
#undef HAVE_SYS_IPC_H

/* Define if you have the <sys/mman.h> header file.  */
#define HAVE_SYS_MMAN_H 1

/* Define if you have the <sys/param.h> header file.  */
#define HAVE_SYS_PARAM_H 1

/* Define if you have the <sys/shm.h> header file.  */
#undef HAVE_SYS_SHM_H

/* Define if you have the <sys/stat.h> header file.  */
#define HAVE_SYS_STAT_H 1

/* Define if you have the <termio.h> header file.  */
#undef HAVE_TERMIO_H

/* Define if you have the <unistd.h> header file.  */
#define HAVE_UNISTD_H 1

/* Define if you have the <zlib.h> header file.  */
#define HAVE_ZLIB_H 1

/* Define if you have the dl library (-ldl).  */
#undef HAVE_LIBDL

/* Define if you have the dld library (-ldld).  */
#undef HAVE_LIBDLD

/* Define if you have the gdbm library (-lgdbm).  */
#undef HAVE_LIBGDBM

/* Define if you have the i library (-li).  */
#undef HAVE_LIBI

/* Define if you have the nsl library (-lnsl).  */
#undef HAVE_LIBNSL

/* Define if you have the rt library (-lrt).  */
#undef HAVE_LIBRT

/* Name of package */
#define PACKAGE "GnuPG"


/* define if compiled symbols have a leading underscore */
#define WITH_SYMBOL_UNDERSCORE 1

#define HAVE_BUILTIN_EXPECT 1
#define HAVE_ULONG_TYPEDEF 1
#define HAVE_USHORT_TYPEDEF 1
#define HAVE_TIMES 1
#define HAVE_INTTYPES_H?1
#define HAVE_FSEEKO 1
#define HAVE_GETOPT_H 1
#define HAVE_SIGSET_T 1
#define HAVE_STRUCT_SIGACTION 1
#define HAVE_ICONV 0

#ifndef __set_errno
#define __set_errno(val) (errno = (val), -1)
#endif

/* RISC OS specifica */
#if (__CC_NORCROFT == 1) /* Norcroft */
# undef __GNUC__
# define __GNUC_MINOR__ 0
# define __GLIBC__ 0

# if (__CC_NORCROFT_VERSION < 544) /* old version of Norcroft */
#  define inline __inline
#  define STR(a) #a
#  define __func__ "[" __FILE__ ":" STR(__LINE__) "]"
#  define SIZEOF_UNSIGNED_LONG_LONG 0
# else
#  define SIZEOF_UNSIGNED_LONG_LONG 8
# endif
#else /* gcc */
# define SIZEOF_UNSIGNED_LONG_LONG 8
#endif

#define HAVE_LDAP_GET_OPTION 1
#undef  USE_ZLIBRISCOS
#define USE_DNS_SRV 1
#define USE_RNDRISCOS 1
#define USE_RSA 1
#define USE_CAST5 1
#define USE_BLOWFISH 1
#define USE_AES 1
#define USE_TWOFISH 1
#define USE_SHA256 1
#if SIZEOF_UNSIGNED_LONG_LONG == 8
# define USE_SHA512
#endif

#ifdef IS_DEVELOPMENT_VERSION
# define DEBUG 1
/*# define M_DEBUG */
# define M_GUARD 1
# define USE_IDEA 1
#endif

#include "g10defs.h"

#endif /*G10_CONFIG_H*/
