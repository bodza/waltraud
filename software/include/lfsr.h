#include <limits.h>

/*
 * Galois LFSR
 *
 * Polynomials verified with https://bitbucket.org/gallen/mlpolygen/
 */
static inline unsigned long lfsr(unsigned long bits, unsigned long prev)
{
    static const unsigned long lfsr_taps[] = {
        0x0,
        0x0,
        0x3,
        0x6,
        0xc,
        0x14,
        0x30,
        0x60,
        0xb8,
        0x110,
        0x240,
        0x500,
        0x829,
        0x100d,
        0x2015,
        0x6000,
        0xd008,
        0x12000,
        0x20400,
        0x40023,
        0x90000,
        0x140000,
        0x300000,
        0x420000,
        0xe10000,
        0x1200000,
        0x2000023,
        0x4000013,
        0x9000000,
        0x14000000,
        0x20000029,
        0x48000000,
        0x80200003,
#if __WORDSIZE == 64
        0x100080000,
        0x204000003,
        0x500000000,
        0x801000000,
        0x100000001f,
        0x2000000031,
        0x4400000000,
        0xa000140000,
        0x12000000000,
        0x300000c0000,
        0x63000000000,
        0xc0000030000,
        0x1b0000000000,
        0x300003000000,
        0x420000000000,
        0xc00000180000,
        0x1008000000000,
        0x3000000c00000,
        0x6000c00000000,
        0x9000000000000,
        0x18003000000000,
        0x30000000030000,
        0x40000040000000,
        0xc0000600000000,
        0x102000000000000,
        0x200004000000000,
        0x600003000000000,
        0xc00000000000000,
        0x1800300000000000,
        0x3000000000000030,
        0x6000000000000000,
        0x800000000000000d
#endif
    };
    unsigned long lsb = prev & 1;

    prev >>= 1;
    prev ^= (-lsb) & lfsr_taps[bits];

    return prev;
}
