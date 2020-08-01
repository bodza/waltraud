#include "int_lib.h"

/* Returns: a % b */

su_int
__umodsi3(su_int a, su_int b)
{
    return a - __udivsi3(a, b) * b;
}
