#include <stdio.h>
#include <console.h>
#include <uart.h>
#include <irq.h>

// #include <generated/csr.h>
#include <generated/soc.h>
#include <generated/mem.h>

#define CMD_LINE_BUFFER_SIZE 64

#define CLEAR  "\e[2J\e[;H"
#define PROMPT "\e[92;1mWaltraud\e[0m> "

static int readline(char *s, int size)
{
    static char skip = 0;

    char c[2];
    int ptr;

    c[1] = 0;
    ptr = 0;
    while (1) {
        c[0] = readchar();
        if (c[0] == skip) {
            continue;
        }
        skip = 0;
        switch (c[0]) {
            case 0x7f:
            case 0x08:
                if (ptr > 0) {
                    ptr--;
                    putsnonl("\x08 \x08");
                }
                break;
            case 0x07:
                break;
            case '\r':
                skip = '\n';
                s[ptr] = 0x00;
                putsnonl("\n");
                return 0;
            case '\n':
                skip = '\r';
                s[ptr] = 0x00;
                putsnonl("\n");
                return 0;
            default:
                putsnonl(c);
                s[ptr] = c[0];
                ptr++;
                break;
        }
    }

    return 0;
}

int main(int argc, char **argv)
{
    irq_setmask(0);
    irq_setie(1);
    uart_init();

    printf("\n");
    printf(" BIOS built on "__DATE__" "__TIME__"\n");
    printf("\n");
    printf("\e[1mCLK\e[0m:       %dMHz\n", CONFIG_CLOCK_FREQUENCY / 1000000);
    printf("\e[1mBUS\e[0m:       %s %d-bit @ %dGiB\n", CONFIG_BUS_STANDARD, CONFIG_BUS_DATA_WIDTH, (1 << (CONFIG_BUS_ADDRESS_WIDTH - 30)));
    printf("\e[1mCSR\e[0m:       %d-bit data\n", CONFIG_CSR_DATA_WIDTH);
    printf("\e[1mSRAM\e[0m:      %dKiB\n", SRAM_SIZE / 1024);
    printf("\n");

    char buffer[CMD_LINE_BUFFER_SIZE];

    while (1) {
        printf("\n%s", PROMPT);
        readline(buffer, CMD_LINE_BUFFER_SIZE);
        printf("\n%s", buffer);
    }

    return 0;
}
