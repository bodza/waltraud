#ifndef _ASM_GENERIC_DIV64_H
#define _ASM_GENERIC_DIV64_H

/*
 * The semantics of do_div() are:
 *
 * uint32_t do_div(uint64_t *n, uint32_t base)
 * {
 *     uint32_t remainder = *n % base;
 *     *n = *n / base;
 *     return remainder;
 * }
 *
 * NOTE: macro parameter n is evaluated multiple times, beware of side effects!
 */

#include <stdint.h>

extern uint32_t __div64_32(uint64_t *dividend, uint32_t divisor);

/* The unnecessary pointer compare is there to check for type safety (n must be 64bit)
 */
# define do_div(n,base) ({                          \
    uint32_t __base = (base);                       \
    uint32_t __rem;                                 \
    (void)(((typeof((n)) *)0) == ((uint64_t *)0));  \
    if (((n) >> 32) == 0) {                         \
        __rem = (uint32_t)(n) % __base;             \
        (n) = (uint32_t)(n) / __base;               \
    } else                                          \
        __rem = __div64_32(&(n), __base);           \
    __rem;                                          \
 })

#endif
