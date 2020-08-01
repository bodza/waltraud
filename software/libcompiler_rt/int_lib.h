#ifndef INT_LIB_H
#define INT_LIB_H

/* Assumption: Signed integral is 2's complement. */
/* Assumption: Right shift of signed negative is arithmetic shift. */
/* Assumption: Endianness is little or big (not mixed). */

#include <limits.h>
#include <stdint.h>
#include <stdbool.h>

typedef      int si_int;
typedef unsigned su_int;

typedef          long long di_int;
typedef unsigned long long du_int;

di_int __divdi3(di_int a, di_int b);
si_int __divsi3(si_int a, si_int b);
su_int __udivsi3(su_int n, su_int d);

#endif
