#ifndef INT_LIB_H
#define INT_LIB_H

/* Assumption: Signed integral is 2's complement. */
/* Assumption: Right shift of signed negative is arithmetic shift. */
/* Assumption: Endianness is little or big (not mixed). */

#if defined(__ELF__)
#define FNALIAS(alias_name, original_name) void alias_name() __attribute__((alias(#original_name)))
#else
#define FNALIAS(alias, name) _Pragma("GCC error(\"alias unsupported on this file format\")")
#endif

#if __ARM_EABI__
# define ARM_EABI_FNALIAS(aeabi_name, name)         void __aeabi_##aeabi_name() __attribute__((alias("__" #name)));
# define COMPILER_RT_ABI __attribute__((pcs("aapcs")))
#else
# define ARM_EABI_FNALIAS(aeabi_name, name)
# if defined(__arm__) && defined(_WIN32) && (!defined(_MSC_VER) || defined(__clang__))
#   define COMPILER_RT_ABI __attribute__((pcs("aapcs")))
# else
#   define COMPILER_RT_ABI
# endif
#endif

#define ALWAYS_INLINE __attribute__((always_inline))
#define NOINLINE __attribute__((noinline))
#define NORETURN __attribute__((noreturn))
#define UNUSED __attribute__((unused))

#include <limits.h>
#include <stdint.h>
#include <stdbool.h>
#include <float.h>

#include "int_types.h"
#include "int_util.h"

COMPILER_RT_ABI si_int __paritysi2(si_int a);
COMPILER_RT_ABI si_int __paritydi2(di_int a);

COMPILER_RT_ABI di_int __divdi3(di_int a, di_int b);
COMPILER_RT_ABI si_int __divsi3(si_int a, si_int b);
COMPILER_RT_ABI su_int __udivsi3(su_int n, su_int d);

COMPILER_RT_ABI su_int __udivmodsi4(su_int a, su_int b, su_int* rem);
COMPILER_RT_ABI du_int __udivmoddi4(du_int a, du_int b, du_int* rem);
#ifdef CRT_HAS_128BIT
COMPILER_RT_ABI si_int __clzti2(ti_int a);
COMPILER_RT_ABI tu_int __udivmodti4(tu_int a, tu_int b, tu_int* rem);
#endif

#endif
