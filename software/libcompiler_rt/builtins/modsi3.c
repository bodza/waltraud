#include "int_lib.h"

/* Returns: a % b */

COMPILER_RT_ABI si_int
__modsi3(si_int a, si_int b)
{
    return a - __divsi3(a, b) * b;
}
