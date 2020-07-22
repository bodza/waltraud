#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <console.h>
#include <ctype.h>
#include <string.h>
#include <uart.h>
#include <system.h>
#include <id.h>
#include <irq.h>
#include <crc.h>
#include <memtest.h>

#include <generated/csr.h>
#include <generated/soc.h>
#include <generated/mem.h>
#include <generated/git.h>

#include <liblitedram/sdram.h>

extern unsigned int _ftext, _edata_rom;

#define NUMBER_OF_BYTES_ON_A_LINE 16

static void dump_bytes(unsigned int *ptr, int count, unsigned long addr)
{
    char *data = (char *)ptr;
    int line_bytes = 0, i = 0;

    putsnonl("Memory dump:");
    while (count > 0) {
        line_bytes = (count > NUMBER_OF_BYTES_ON_A_LINE) ? NUMBER_OF_BYTES_ON_A_LINE : count;

        printf("\n0x%08x  ", addr);
        for (i = 0; i < line_bytes; i++)
            printf("%02x ", *(unsigned char *)(data+i));

        for (; i < NUMBER_OF_BYTES_ON_A_LINE; i++)
            printf("   ");

        printf(" ");

        for (i = 0; i < line_bytes; i++) {
            if ((*(data + i) < 0x20) || (*(data + i) > 0x7e))
                printf(".");
            else
                printf("%c", *(data + i));
        }

        for (; i < NUMBER_OF_BYTES_ON_A_LINE; i++)
            printf(" ");

        data += (char)line_bytes;
        count -= line_bytes;
        addr += line_bytes;
    }
    printf("\n");
}

static void crcbios(void)
{
    /* _edata_rom is located right after the end of the flat binary image.
     * The CRC tool writes the 32-bit CRC here.
     * We also use the address of _edata_rom to know the length of our code.
     */
    unsigned long offset_bios = (unsigned long)&_ftext;
    unsigned int expected_crc = _edata_rom;
    unsigned long length = (unsigned long)&_edata_rom - offset_bios;
    unsigned int actual_crc = crc32((unsigned char *)offset_bios, length);

    if (expected_crc == actual_crc)
        printf(" BIOS CRC passed (%08x)\n", actual_crc);
    else {
        printf(" BIOS CRC failed (expected %08x, got %08x)\n", expected_crc, actual_crc);
    }
}

#define MAX_PARAM       8

#define MISC_CMDS       0
#define SYSTEM_CMDS     1
#define CACHE_CMDS      2
#define MEM_CMDS        3
#define LITEDRAM_CMDS   4

#define NB_OF_GROUPS    8

typedef void (*cmd_handler)(int nb_params, char **params);

struct cmd_struct {
    void (*func)(int nb_params, char **params);
    const char *name;
    const char *help;
    int group;
};

extern struct cmd_struct *const __bios_cmd_start[];
extern struct cmd_struct *const __bios_cmd_end[];

#define CMD(cmd_name, handler, help_txt, group_id) \
    struct cmd_struct s_##cmd_name = {             \
        .func = (cmd_handler)handler,              \
        .name = #cmd_name,                         \
        .help = help_txt,                          \
        .group = group_id,                         \
    };                                             \
    const struct cmd_struct *__bios_cmd_##cmd_name __attribute__((__used__)) __attribute__((__section__(".bios_cmd"))) = &s_##cmd_name

/**
 * Command "help"
 *
 * Print a list of available commands with their help text
 */
static void help_handler(int nb_params, char **params)
{
    struct cmd_struct * const *cmd;

    puts("\nAvailable commands:\n");

    for (int i = 0; i < NB_OF_GROUPS; i++) {
        int not_empty = 0;
        for (cmd = __bios_cmd_start; cmd != __bios_cmd_end; cmd++) {
            if ((*cmd)->group == i) {
                printf("%-16s - %s\n", (*cmd)->name, (*cmd)->help ? (*cmd)->help : "-");
                not_empty = 1;
            }
        }
        if (not_empty) {
            printf("\n");
        }
    }
}
CMD(help, help_handler, "Print this help", MISC_CMDS);

/**
 * Command "ident"
 *
 * Identifier of the system
 */
static void ident_helper(int nb_params, char **params)
{
    char buffer[IDENT_SIZE];

    get_ident(buffer);
    printf("Ident: %s", (*buffer) ? buffer : "-");
}
CMD(ident, ident_helper, "Identifier of the system", SYSTEM_CMDS);

#ifdef CSR_CTRL_RESET_ADDR
/**
 * Command "reboot"
 *
 * Reboot the system
 */
static void reboot(int nb_params, char **params)
{
    ctrl_reset_write(1);
}
CMD(reboot, reboot, "Reboot the system", SYSTEM_CMDS);
#endif

#ifdef CSR_TIMER0_UPTIME_CYCLES_ADDR
/**
 * Command "uptime"
 *
 * Uptime of the system
 */
static void uptime(int nb_params, char **params)
{
    unsigned long uptime;

    timer0_uptime_latch_write(1);
    uptime = timer0_uptime_cycles_read();
    printf("Uptime: %ld sys_clk cycles / %ld seconds", uptime, uptime / CONFIG_CLOCK_FREQUENCY);
}
CMD(uptime, uptime, "Uptime of the system since power-up", SYSTEM_CMDS);
#endif

/**
 * Command "crc"
 *
 * Compute CRC32 over an address range
 */
static void crc(int nb_params, char **params)
{
    if (nb_params < 2) {
        printf("crc <address> <length>");
        return;
    }

    char *c;

    unsigned int addr = strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned int length = strtoul(params[1], &c, 0);
    if (*c != 0) {
        printf("Incorrect length");
        return;
    }

    printf("CRC32: %08x", crc32((unsigned char *)addr, length));
}
CMD(crc, crc, "Compute CRC32 of a part of the address space", MISC_CMDS);

/**
 * Command "flush_cpu_dcache"
 *
 * Flush CPU data cache
 */
CMD(flush_cpu_dcache, flush_cpu_dcache, "Flush CPU data cache", CACHE_CMDS);

#ifdef CONFIG_L2_SIZE
/**
 * Command "flush_l2_cache"
 *
 * Flush L2 cache
 */
CMD(flush_l2_cache, flush_l2_cache, "Flush L2 cache", CACHE_CMDS);
#endif

#ifdef CSR_SDRAM_BASE
/**
 * Command "sdrrow"
 *
 * Precharge/Activate row
 */
static void sdrrow_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        sdrrow(0);
        printf("Precharged");
    }

    char *c;

    unsigned int row = strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect row");
        return;
    }

    sdrrow(row);
    printf("Activated row %d", row);
}
CMD(sdrrow, sdrrow_handler, "Precharge/Activate row", LITEDRAM_CMDS);

/**
 * Command "sdrsw"
 *
 * Gives SDRAM control to SW
 */
CMD(sdrsw, sdrsw, "Gives SDRAM control to SW", LITEDRAM_CMDS);

/**
 * Command "sdrhw"
 *
 * Gives SDRAM control to HW
 */
CMD(sdrhw, sdrhw, "Gives SDRAM control to HW", LITEDRAM_CMDS);

/**
 * Command "sdrrdbuf"
 *
 * Dump SDRAM read buffer
 */
static void sdrrdbuf_handler(int nb_params, char **params)
{
    sdrrdbuf(-1);
}
CMD(sdrrdbuf, sdrrdbuf_handler, "Dump SDRAM read buffer", LITEDRAM_CMDS);

/**
 * Command "sdrrd"
 *
 * Read SDRAM data
 */
static void sdrrd_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("sdrrd <address>");
        return;
    }

    char *c;
    int dq;

    unsigned int addr = strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    if (nb_params < 2)
        dq = -1;
    else {
        dq = strtoul(params[1], &c, 0);
        if (*c != 0) {
            printf("Incorrect DQ");
            return;
        }
    }

    sdrrd(addr, dq);
}
CMD(sdrrd, sdrrd_handler, "Read SDRAM data", LITEDRAM_CMDS);

/**
 * Command "sdrrderr"
 *
 * Print SDRAM read errors
 */
static void sdrrderr_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("sdrrderr <count>");
        return;
    }

    char *c;

    int count = strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect count");
        return;
    }

    sdrrderr(count);
}
CMD(sdrrderr, sdrrderr_handler, "Print SDRAM read errors", LITEDRAM_CMDS);

/**
 * Command "sdrwr"
 *
 * Write SDRAM test data
 */
static void sdrwr_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("sdrwr <address>");
        return;
    }

    char *c;

    unsigned int addr = strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    sdrwr(addr);
}
CMD(sdrwr, sdrwr_handler, "Write SDRAM test data", LITEDRAM_CMDS);

#ifdef CSR_DDRPHY_BASE
/**
 * Command "sdrinit"
 *
 * Start SDRAM initialisation
 */
CMD(sdrinit, sdrinit, "Start SDRAM initialisation", LITEDRAM_CMDS);

/**
 * Command "sdrlevel"
 *
 * Perform read/write leveling
 */
CMD(sdrlevel, sdrlevel, "Perform read/write leveling", LITEDRAM_CMDS);

#ifdef SDRAM_PHY_WRITE_LEVELING_CAPABLE
/**
 * Command "sdrwlon"
 *
 * Write leveling ON
 */
CMD(sdrwlon, sdrwlon, "Enable write leveling", LITEDRAM_CMDS);

/**
 * Command "sdrwloff"
 *
 * Write leveling OFF
 */
CMD(sdrwloff, sdrwloff, "Disable write leveling", LITEDRAM_CMDS);
#endif
#endif
#endif

/**
 * Command "mr"
 *
 * Memory read
 */
static void mr(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("mr <address> [length]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned int length;
    if (nb_params == 1) {
        length = 4;
    } else {
        length = strtoul(params[1], &c, 0);
        if (*c != 0) {
            printf("\nIncorrect length");
            return;
        }
    }

    dump_bytes(addr, length, (unsigned long)addr);
}
CMD(mr, mr, "Read address space", MEM_CMDS);

/**
 * Command "mw"
 *
 * Memory write
 */
static void mw(int nb_params, char **params)
{
    if (nb_params < 2) {
        printf("mw <address> <value> [count]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned int value = strtoul(params[1], &c, 0);
    if(*c != 0) {
        printf("Incorrect value");
        return;
    }

    unsigned int count;
    if (nb_params == 2) {
        count = 1;
    } else {
        count = strtoul(params[2], &c, 0);
        if(*c != 0) {
            printf("Incorrect count");
            return;
        }
    }

    for (unsigned int i = 0; i < count; i++) {
        *addr++ = value;
    }
}
CMD(mw, mw, "Write address space", MEM_CMDS);

/**
 * Command "mc"
 *
 * Memory copy
 */
static void mc(int nb_params, char **params)
{
    if (nb_params < 2) {
        printf("mc <dst> <src> [count]");
        return;
    }

    char *c;

    unsigned int *dstaddr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect destination address");
        return;
    }

    unsigned int *srcaddr = (unsigned int *)strtoul(params[1], &c, 0);
    if (*c != 0) {
        printf("Incorrect source address");
        return;
    }

    unsigned int count;
    if (nb_params == 2) {
        count = 1;
    } else {
        count = strtoul(params[2], &c, 0);
        if (*c != 0) {
            printf("Incorrect count");
            return;
        }
    }

    for (unsigned int i = 0; i < count; i++) {
        *dstaddr++ = *srcaddr++;
    }
}
CMD(mc, mc, "Copy address space", MEM_CMDS);

/**
 * Command "memtest"
 *
 * Run a memory test
 */
static void memtest_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("memtest <addr> [<maxsize>]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned long maxsize = ~0uL;
    if (nb_params >= 2) {
        maxsize = strtoul(params[1], &c, 0);
        if (*c != 0) {
            printf("Incorrect max size");
            return;
        }
    }

    memtest(addr, maxsize);
}
CMD(memtest, memtest_handler, "Run a memory test", MEM_CMDS);

/**
 * Command "memspeed"
 *
 * Run a memory speed test
 */
static void memspeed_handler(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("memspeed <addr> <size> [<readonly>]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned long size = strtoul(params[1], &c, 0);
    if (*c != 0) {
        printf("Incorrect size");
        return;
    }

    bool read_only = false;
    if (nb_params >= 3) {
        read_only = (bool) strtoul(params[2], &c, 0);
        if (*c != 0) {
            printf("Incorrect readonly value");
            return;
        }
    }

    memspeed(addr, size, read_only);
}
CMD(memspeed, memspeed_handler, "Run a memory speed test", MEM_CMDS);

#ifdef CSR_DEBUG_PRINTER
/**
 * Command "csrprint"
 *
 * Print CSR values
 */
static void csrprint(int nb_params, char **params)
{
    print_csrs();
}
CMD(csrprint, csrprint, "Print CSR values", MEM_CMDS);
#endif

#ifdef CSR_WB_SOFTCONTROL_BASE
static void wbr(int nb_params, char **params)
{
    if (nb_params < 1) {
        printf("mr <address> [length]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned int length;
    if (nb_params == 1) {
        length = 4;
    } else {
        length = strtoul(params[1], &c, 0);
        if(*c != 0) {
            printf("\nIncorrect length");
            return;
        }
    }

    for (unsigned int i = 0; i < length; ++i) {
        wb_softcontrol_adr_write((unsigned long)(addr + i));
        wb_softcontrol_read_write(1);
        printf("0x%08x: 0x%08x\n", (unsigned long)(addr + i), wb_softcontrol_data_read());
    }
}
CMD(wbr, wbr, "Read using softcontrol wishbone controller", MEM_CMDS);

static void wbw(int nb_params, char **params)
{
    if (nb_params < 2) {
        printf("mw <address> <value> [count]");
        return;
    }

    char *c;

    unsigned int *addr = (unsigned int *)strtoul(params[0], &c, 0);
    if (*c != 0) {
        printf("Incorrect address");
        return;
    }

    unsigned int value = strtoul(params[1], &c, 0);
    if(*c != 0) {
        printf("Incorrect value");
        return;
    }

    unsigned int count;
    if (nb_params == 2) {
        count = 1;
    } else {
        count = strtoul(params[2], &c, 0);
        if(*c != 0) {
            printf("Incorrect count");
            return;
        }
    }

    wb_softcontrol_data_write(value);
    for (unsigned int i = 0; i < count; i++) {
        wb_softcontrol_adr_write((unsigned long)(addr + i));
        wb_softcontrol_write_write(1);
    }
}
CMD(wbw, wbw, "Write using softcontrol wishbone controller", MEM_CMDS);
#endif

static int get_param(char *buf, char **cmd, char **params)
{
    int nb_param = 0;

    for (int i = 0; i < MAX_PARAM; i++) {
        params[i] = NULL;
    }

    *cmd = buf;

    while ((*buf != ' ') && (*buf !=0))
        buf++;

    if (*buf == 0) {
        return nb_param;
    }

    *buf++ = 0;

    while (1) {
        while ((*buf == ' ') && (*buf !=0)) {
            buf++;
        }

        if (*buf == 0) {
            return nb_param;
        }

        params[nb_param++] = buf;

        while ((*buf != ' ') && (*buf !=0)) {
            buf++;
        }

        if (*buf == 0) {
            return nb_param;
        }
        *buf++ = 0;
    }
}

static struct cmd_struct *cmd_dispatch(char *command, int nb_params, char **params)
{
    for (struct cmd_struct * const *cmd = __bios_cmd_start; cmd != __bios_cmd_end; cmd++) {
        if (!strcmp(command, (*cmd)->name)) {
            (*cmd)->func(nb_params, params);
            return (*cmd);
        }
    }

    return NULL;
}

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
#ifdef CONFIG_CPU_HAS_INTERRUPT
    irq_setmask(0);
    irq_setie(1);
#endif
    uart_init();

    printf("\n");
    printf(" BIOS built on "__DATE__" "__TIME__"\n");
    crcbios();
    printf("\n");
    printf("--=============== \e[1mSoC\e[0m ==================--\n");
    printf("\e[1mCPU\e[0m:       %s @ %dMHz\n", CONFIG_CPU_HUMAN_NAME, CONFIG_CLOCK_FREQUENCY/1000000);
    printf("\e[1mBUS\e[0m:       %s %d-bit @ %dGiB\n", CONFIG_BUS_STANDARD, CONFIG_BUS_DATA_WIDTH, (1 << (CONFIG_BUS_ADDRESS_WIDTH - 30)));
    printf("\e[1mCSR\e[0m:       %d-bit data\n", CONFIG_CSR_DATA_WIDTH);
    printf("\e[1mROM\e[0m:       %dKiB\n", ROM_SIZE/1024);
    printf("\e[1mSRAM\e[0m:      %dKiB\n", SRAM_SIZE/1024);
#ifdef CONFIG_L2_SIZE
    printf("\e[1mL2\e[0m:        %dKiB\n", CONFIG_L2_SIZE/1024);
#endif
#ifdef MAIN_RAM_SIZE
    printf("\e[1mMAIN-RAM\e[0m:  %dKiB\n", MAIN_RAM_SIZE/1024);
#endif
    printf("\n");

#ifdef CSR_SDRAM_BASE
    printf("--========== \e[1mInitialization\e[0m ============--\n");
    if (sdrinit() != 1)
        printf("Memory initialization failed\n");
    printf("\n");
#endif

    char buffer[CMD_LINE_BUFFER_SIZE];
    char *params[MAX_PARAM];
    char *command;
    struct cmd_struct *cmd;
    int nb_params;

    printf("--============= \e[1mConsole\e[0m ================--\n");
    printf("\n%s", PROMPT);
    while (1) {
        readline(buffer, CMD_LINE_BUFFER_SIZE);
        if (buffer[0] != 0) {
            printf("\n");
            nb_params = get_param(buffer, &command, params);
            cmd = cmd_dispatch(command, nb_params, params);
            if (!cmd) {
                printf("Command not found");
            }
        }
        printf("\n%s", PROMPT);
    }
    return 0;
}
