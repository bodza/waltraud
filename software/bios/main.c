#include <uart.h>

int main(int argc, char **argv)
{
    uart_init();

    while (1) {
        uart_write(uart_read());
    }

    return 0;
}
