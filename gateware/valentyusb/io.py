from eigen.fhdl.module import Module
from eigen.fhdl.specials import Instance, TSTriple
from eigen.fhdl.structure import ClockSignal, If, Signal

#from eigen.genlib.cdc import MultiReg

class Raw(Instance.PreformattedParam):
    def __init__(self, value):
        self.value = value

class IoBuf(Module):
    def __init__(self, usbp_pin, usbn_pin, usb_pullup_pin=None):
        # tx/rx io interface
        self.usb_tx_en = Signal()
        self.usb_p_tx = Signal()
        self.usb_n_tx = Signal()

        self.usb_p_rx = Signal()
        self.usb_n_rx = Signal()

        self.usb_p_rx_io = Signal()
        self.usb_n_rx_io = Signal()

        usb_p_t = TSTriple()
        usb_n_t = TSTriple()

        self.specials += usb_p_t.get_tristate(usbp_pin)
        self.specials += usb_n_t.get_tristate(usbn_pin)

        self.usb_pullup = Signal()
        if usb_pullup_pin is not None:
            self.comb += [
                usb_pullup_pin.eq(self.usb_pullup),
            ]

        usb_tx_en = Signal()
        usb_p_tx = Signal()
        usb_n_tx = Signal()

        self.sync.usb_48 += [
             usb_tx_en.eq(self.usb_tx_en),
        ]

        # Add IO buffers for outputs
        self.specials += Instance('OFS1P3BX',
            i_D=self.usb_p_tx,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_tx,
        )
        self.specials += Instance('OFS1P3BX',
            i_D=self.usb_n_tx,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_tx,
        )

        # Use IO buffers on input
        usb_p_rx_ = Signal()
        usb_n_rx_ = Signal()
        usb_p_t_i = Signal()
        usb_n_t_i = Signal()
        self.specials += Instance('IFS1P3BX',
            i_D=usb_p_t.i,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_rx_,
        )
        self.sync.usb_48 += usb_p_t_i.eq(usb_p_rx_)
        
        self.specials += Instance('IFS1P3BX',
            i_D=usb_n_t.i,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_rx_,
        )
        self.sync.usb_48 += usb_n_t_i.eq(usb_n_rx_)

        #######################################################################
        #######################################################################
        #### Mux the USB +/- pair with the TX and RX paths
        #######################################################################
        #######################################################################
        #self.specials += [
            #MultiReg(usb_p_t.i, usb_p_t_i),
            #MultiReg(usb_n_t.i, usb_n_t_i)
        #]

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p_rx.eq(0b1),
                self.usb_n_rx.eq(0b0),
            ).Else(
                self.usb_p_rx.eq(usb_p_t_i),
                self.usb_n_rx.eq(usb_n_t_i),
            ),
            usb_p_t.oe.eq(usb_tx_en),
            usb_n_t.oe.eq(usb_tx_en),
            usb_p_t.o.eq(usb_p_tx),
            usb_n_t.o.eq(usb_n_tx),
        ]

class FakeIoBuf(Module):
    def __init__(self):
        self.usb_pullup = Signal()

        self.usb_p = Signal()
        self.usb_n = Signal()

        self.usb_tx_en = Signal()
        self.usb_p_tx = Signal()
        self.usb_n_tx = Signal()

        self.usb_p_rx = Signal()
        self.usb_n_rx = Signal()

        self.usb_p_rx_io = Signal()
        self.usb_n_rx_io = Signal()

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p_rx.eq(0b1),
                self.usb_n_rx.eq(0b0)
            ).Else(
                self.usb_p_rx.eq(self.usb_p_rx_io),
                self.usb_n_rx.eq(self.usb_n_rx_io)
            ),
        ]

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p.eq(self.usb_p_tx),
                self.usb_n.eq(self.usb_n_tx),
            ).Else(
                self.usb_p.eq(self.usb_p_rx),
                self.usb_n.eq(self.usb_n_rx),
            ),
        ]

    def recv(self, v):
        tx_en = yield self.usb_tx_en
        assert not tx_en, "Currently transmitting!"

        if v == '0' or v == '_':
            # SE0 - both lines pulled low
            yield self.usb_p_rx_io.eq(0)
            yield self.usb_n_rx_io.eq(0)
        elif v == '1':
            # SE1 - illegal, should never occur
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(1)
        elif v == '-' or v == 'I':
            # Idle
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(0)
        elif v == 'J':
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(0)
        elif v == 'K':
            yield self.usb_p_rx_io.eq(0)
            yield self.usb_n_rx_io.eq(1)
        else:
            assert False, "Unknown value: %s" % v

    def current(self):
        usb_p = yield self.usb_p
        usb_n = yield self.usb_n
        values = (usb_p, usb_n)

        if values == (0, 0):
            return '_'
        elif values == (1, 1):
            return '1'
        elif values == (1, 0):
            return 'J'
        elif values == (0, 1):
            return 'K'
        else:
            assert False, values