.global _start
_start:

.org 0x00000000 # Reset
    j _crt0

_crt0:
    /* zero-initialize all registers */
    addi x1, zero, 0
    addi x2, zero, 0
    addi x3, zero, 0
    addi x4, zero, 0
    addi x5, zero, 0
    addi x6, zero, 0
    addi x7, zero, 0
    addi x8, zero, 0
    addi x9, zero, 0
    addi x10, zero, 0
    addi x11, zero, 0
    addi x12, zero, 0
    addi x13, zero, 0
    addi x14, zero, 0
    addi x15, zero, 0
    addi x16, zero, 0
    addi x17, zero, 0
    addi x18, zero, 0
    addi x19, zero, 0
    addi x20, zero, 0
    addi x21, zero, 0
    addi x22, zero, 0
    addi x23, zero, 0
    addi x24, zero, 0
    addi x25, zero, 0
    addi x26, zero, 0
    addi x27, zero, 0
    addi x28, zero, 0
    addi x29, zero, 0
    addi x30, zero, 0
    addi x31, zero, 0

    /* Load DATA */
    la t0, _fdata_rom
    la t1, _fdata
    la t2, _edata
3:
    lw t3, 0(t0)
    sw t3, 0(t1)
    /* _edata is aligned to 16 bytes. Use word-xfers. */
    addi t0, t0, 4
    addi t1, t1, 4
    bltu t1, t2, 3b

    /* Clear BSS */
    la t0, _fbss
    la t1, _ebss
2:
    sw zero, 0(t0)
    addi t0, t0, 4
    bltu t0, t1, 2b

    /* set main stack */
    la sp, _fstack

    /* jump to main */
    jal ra, main

1:
    /* loop forever */
    j 1b
