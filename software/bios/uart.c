#include <uart.h>

#include <generated/csr.h>

/*
 * Buffer sizes must be a power of 2 so that modulos can be computed with logical AND.
 */

void uart_isr(void)
{
}

char uart_read(void)
{
    while (uart_rxempty_read())
        ;
    char c = uart_rxtx_read();
    uart_ev_pending_write(UART_EV_RX);
    return c;
}

int uart_read_nonblock(void)
{
    return (uart_rxempty_read() == 0);
}

void uart_write(char c)
{
    while (uart_txfull_read())
        ;
    uart_rxtx_write(c);
    uart_ev_pending_write(UART_EV_TX);
}

void uart_init(void)
{
    uart_ev_pending_write(uart_ev_pending_read());
    uart_ev_enable_write(UART_EV_TX | UART_EV_RX);
}

void uart_sync(void)
{
    while (uart_txfull_read())
        ;
}
