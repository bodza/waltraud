from enum import IntEnum
import functools, operator

from .eigen import *
from .eigen import _AsyncFIFO, _SyncFIFOBuffered

class PID(IntEnum):
    # USB Packet IDs
    """
    >>> bin(PID.SETUP.value)
    '0b1101'
    >>> PID.SETUP.encode()
    'KKKKJJJJJJJJJJJJKKKKKKKKJJJJKKKK'
    >>> for p in PID:
    ...    print("%-10s" % p, "%x" % p.value, "%02x" % p.byte(), p.encode(1))
    PID.SETUP  d 2d KJJJKKJK
    PID.OUT    1 e1 KJKJKKKK
    PID.IN     9 69 KJKKJJJK
    PID.SOF    5 a5 KJJKJJKK
    PID.DATA0  3 c3 KKJKJKKK
    PID.DATA1  b 4b KKJJKJJK
    PID.DATA2  7 87 KKKJKJKK
    PID.MDATA  f 0f KKKKJKJK
    PID.ACK    2 d2 JJKJJKKK
    PID.NAK    a 5a JJKKKJJK
    PID.STALL  e 1e JJJJJKJK
    PID.NYET   6 96 JJJKKJKK
    PID.PRE    c 3c JKKKKKJK
    PID.SPLIT  8 78 JKJJJJJK
    PID.PING   4 b4 JKKJJJKK
    PID.RESERVED 0 f0 JKJKKKKK
    """

    # Token pids
    SETUP   = 0b1101 # D
    OUT     = 0b0001 # 1
    IN      = 0b1001 # 9
    SOF     = 0b0101 # 5

    # Data pid
    DATA0   = 0b0011 # 3
    DATA1   = 0b1011 # B
    # USB HS only
    DATA2   = 0b0111 # B
    MDATA   = 0b1111 # F

    # Handshake pids
    ACK     = 0b0010 # 2
    NAK     = 0b1010 # A
    STALL   = 0b1110 # E
    # USB HS only
    NYET    = 0b0110 # 6

    # USB HS only
    PRE      = 0b1100 # C
    ERR      = 0b1100 # C
    SPLIT    = 0b1000 # 8
    PING     = 0b0100 # 4
    RESERVED = 0b0000 # 0

    def byte(self):
        v = self.value
        return v | ((0b1111 ^ v) << 4)

    def encode(self, cycles=4):
        # Prevent cyclic imports by importing here...
        from .utils.packet import nrzi, sync, encode_pid
        return nrzi(sync() + encode_pid(self.value), cycles)[cycles * len(sync()):]

class PIDTypes(IntEnum):
    """
    >>> # Token PIDs
    >>> PIDTypes.token(PID.SETUP), PIDTypes.data(PID.SETUP), PIDTypes.handshake(PID.SETUP)
    (True, False, False)
    >>> PIDTypes.token(PID.OUT), PIDTypes.data(PID.OUT), PIDTypes.handshake(PID.OUT)
    (True, False, False)
    >>> PIDTypes.token(PID.IN), PIDTypes.data(PID.IN), PIDTypes.handshake(PID.IN)
    (True, False, False)
    >>> PIDTypes.token(PID.SOF), PIDTypes.data(PID.SOF), PIDTypes.handshake(PID.SOF)
    (True, False, False)

    >>> # Data PIDs
    >>> PIDTypes.token(PID.DATA0), PIDTypes.data(PID.DATA0), PIDTypes.handshake(PID.DATA0)
    (False, True, False)
    >>> PIDTypes.token(PID.DATA1), PIDTypes.data(PID.DATA1), PIDTypes.handshake(PID.DATA1)
    (False, True, False)
    >>> # USB2.0 Data PIDs
    >>> PIDTypes.token(PID.DATA2), PIDTypes.data(PID.DATA2), PIDTypes.handshake(PID.DATA2)
    (False, True, False)
    >>> PIDTypes.token(PID.MDATA), PIDTypes.data(PID.MDATA), PIDTypes.handshake(PID.MDATA)
    (False, True, False)

    >>> # Handshake PIDs
    >>> PIDTypes.token(PID.ACK), PIDTypes.data(PID.ACK), PIDTypes.handshake(PID.ACK)
    (False, False, True)
    >>> PIDTypes.token(PID.NAK), PIDTypes.data(PID.NAK), PIDTypes.handshake(PID.NAK)
    (False, False, True)
    >>> PIDTypes.token(PID.STALL), PIDTypes.data(PID.STALL), PIDTypes.handshake(PID.STALL)
    (False, False, True)
    >>> # USB2.0 Handshake PIDs
    >>> PIDTypes.token(PID.NYET), PIDTypes.data(PID.NYET), PIDTypes.handshake(PID.NYET)
    (False, False, True)

    >>> # Special PIDs
    >>> PIDTypes.token(PID.PRE), PIDTypes.data(PID.PRE), PIDTypes.handshake(PID.PRE)
    (False, False, False)
    """

    TOKEN     = 0b0001
    DATA      = 0b0011
    HANDSHAKE = 0b0010
    SPECIAL   = 0b0000

    TYPE_MASK = 0b0011

    @staticmethod
    def token(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.TOKEN

    @staticmethod
    def data(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.DATA

    @staticmethod
    def handshake(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.HANDSHAKE

    @staticmethod
    def special(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.SPECIAL

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

@ResetInserter()
class RxBitstuffRemover(Module):
    """RX Bitstuff Removal

    Long sequences of 1's would cause the receiver to lose it's lock on the
    transmitter's clock.  USB solves this with bitstuffing.  A '0' is stuffed
    after every 6 consecutive 1's.  This extra bit is required to recover the
    clock, but it should not be passed on to higher layers in the device.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.9
    https://en.wikipedia.org/wiki/Bit_stuffing

    Clock Domain
    ------------
    usb_12 : 12MHz

    Input Ports
    ------------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    Output Ports
    ------------
    o_data : Signal(1)
        Decoded data bit from USB bus.

    o_stall : Signal(1)
        Indicates the bit stuffer just removed an extra bit, so no data available.

    o_error : Signal(1)
        Indicates there has been a bitstuff error. A bitstuff error occurs
        when there should be a stuffed '0' after 6 consecutive 1's; but instead
        of a '0', there is an additional '1'.  This is normal during IDLE, but
        should never happen within a packet.
        Qualified by valid.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_data = Signal()

        # This state machine recognizes sequences of 6 bits and drops the 7th bit.
        # The fsm implements a counter in a series of several states.
        # This is intentional to help absolutely minimize the levels of logic used.
        self.submodules.stuff = stuff = FSM(reset_state="D0")

        drop_bit = Signal(1)

        for i in range(6):
            stuff.act("D%d" % i,
                If(self.i_valid,
                    If(self.i_data,
                        # Receiving '1' increments the bitstuff counter.
                        NextState("D%d" % (i + 1))
                    ).Else(
                        # Receiving '0' resets the bitstuff counter.
                        NextState("D0")
                    )
                ),
            )

        stuff.act("D6",
            If(self.i_valid,
                drop_bit.eq(1),
                # Reset the bitstuff counter, drop the data.
                NextState("D0")
            )
        )

        # pass all of the outputs through a pipe stage
        self.o_data = Signal()
        self.o_error = Signal()
        self.o_stall = Signal(reset=1)

        self.sync += [
            self.o_data.eq(self.i_data),
            self.o_stall.eq(drop_bit | ~self.i_valid),
            self.o_error.eq(drop_bit & self.i_data & self.i_valid),
        ]

class RxClockDataRecovery(Module):
    """RX Clock Data Recovery module.

    RxClockDataRecovery synchronizes the USB differential pair with the FPGAs
    clocks, de-glitches the differential pair, and recovers the incoming clock
    and data.

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    usbp_raw : Signal(1)
        Raw USB+ input from the FPGA IOs, no need to synchronize.

    usbn_raw : Signal(1)
        Raw USB- input from the FPGA IOs, no need to synchronize.

    Output Ports
    ------------
    Output ports are data members of the module. All output ports are flopped.
    The line_state_dj/dk/se0/se1 outputs are 1-hot encoded.

    line_state_valid : Signal(1)
        Asserted for one clock when the output line state is ready to be sampled.

    line_state_dj : Signal(1)
        Represents Full Speed J-state on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_dk : Signal(1)
        Represents Full Speed K-state on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_se0 : Signal(1)
        Represents SE0 on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_se1 : Signal(1)
        Represents SE1 on the incoming USB data pair.
        Qualify with line_state_valid.
    """

    def __init__(self, usbp_raw, usbn_raw):
        if False:
            #######################################################################
            # Synchronize raw USB signals
            #
            # We need to synchronize the raw USB signals with the usb_48 clock
            # domain.  MultiReg implements a multi-stage shift register that takes
            # care of this for us.  Without MultiReg we would have metastability
            # issues.
            #
            usbp = Signal(reset=1)
            usbn = Signal()

            self.specials += MultiReg(usbp_raw, usbp, n=1, reset=1)
            self.specials += MultiReg(usbn_raw, usbn, n=1)
        else:
            # Leave raw USB signals meta-stable.  The synchronizer should clean
            # them up.
            usbp = usbp_raw
            usbn = usbn_raw

        #######################################################################
        # Line State Recovery State Machine
        #
        # The receive path doesn't use a differential receiver.  Because of
        # this there is a chance that one of the differential pairs will appear
        # to have changed to the new state while the other is still in the old
        # state.  The following state machine detects transitions and waits an
        # extra sampling clock before decoding the state on the differential
        # pair.  This transition period # will only ever last for one clock as
        # long as there is no noise on the line.  If there is enough noise on
        # the line then the data may be corrupted and the packet will fail the
        # data integrity checks.
        #
        self.submodules.lsr = lsr = FSM()

        dpair = Signal(2)
        self.comb += dpair.eq(Cat(usbn, usbp))

        # output signals for use by the clock recovery stage
        line_state_dt = Signal()
        line_state_dj = Signal()
        line_state_dk = Signal()
        line_state_se0 = Signal()
        line_state_se1 = Signal()

        # If we are in a transition state, then we can sample the pair and
        # move to the next corresponding line state.
        lsr.act("DT",
            line_state_dt.eq(1),
            Case(dpair, {
                0b10 : NextState("DJ"),
                0b01 : NextState("DK"),
                0b00 : NextState("SE0"),
                0b11 : NextState("SE1")
            })
        )

        # If we are in a valid line state and the value of the pair changes,
        # then we need to move to the transition state.
        lsr.act("DJ",  line_state_dj.eq(1),  If(dpair != 0b10, NextState("DT")))
        lsr.act("DK",  line_state_dk.eq(1),  If(dpair != 0b01, NextState("DT")))
        lsr.act("SE0", line_state_se0.eq(1), If(dpair != 0b00, NextState("DT")))
        lsr.act("SE1", line_state_se1.eq(1), If(dpair != 0b11, NextState("DT")))

        #######################################################################
        # Clock and Data Recovery
        #
        # The DT state from the line state recovery state machine is used to align to
        # transmit clock.  The line state is sampled in the middle of the bit time.
        #
        # Example of signal relationships
        # -------------------------------
        # line_state        DT  DJ  DJ  DJ  DT  DK  DK  DK  DK  DK  DK  DT  DJ  DJ  DJ
        # line_state_valid  ________----____________----____________----________----____
        # bit_phase         0   0   1   2   3   0   1   2   3   0   1   2   0   1   2
        #

        # We 4x oversample, so make the line_state_phase have 4 possible values.
        line_state_phase = Signal(2)

        self.line_state_valid = Signal()
        self.line_state_dj = Signal()
        self.line_state_dk = Signal()
        self.line_state_se0 = Signal()
        self.line_state_se1 = Signal()

        self.sync += [
            self.line_state_valid.eq(line_state_phase == 1),

            If(line_state_dt,
                # re-align the phase with the incoming transition
                line_state_phase.eq(0),

                # make sure we never assert valid on a transition
                self.line_state_valid.eq(0),
            ).Else(
                # keep tracking the clock by incrementing the phase
                line_state_phase.eq(line_state_phase + 1)
            ),

            # flop all the outputs to help with timing
            self.line_state_dj.eq(line_state_dj),
            self.line_state_dk.eq(line_state_dk),
            self.line_state_se0.eq(line_state_se0),
            self.line_state_se1.eq(line_state_se1),
        ]

@ResetInserter()
class RxPacketDetect(Module):
    """Packet Detection

    Full Speed packets begin with the following sequence:

        KJKJKJKK

    This raw sequence corresponds to the following data:

        00000001

    The bus idle condition is signaled with the J state:

        JJJJJJJJ

    This translates to a series of '1's since there are no transitions.  Given
    this information, it is easy to detect the beginning of a packet by looking
    for 00000001.

    The end of a packet is even easier to detect.  The end of a packet is
    signaled with two SE0 and one J.  We can just look for the first SE0 to
    detect the end of the packet.

    Packet detection can occur in parallel with bitstuff removal.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.10

    Input Ports
    ------------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    i_se0 : Signal(1)
        Indicator for SE0 from USB bus.
        Qualified by valid.

    Output Ports
    ------------
    o_pkt_start : Signal(1)
        Asserted for one clock on the last bit of the sync.

    o_pkt_active : Signal(1)
        Asserted while in the middle of a packet.

    o_pkt_end : Signal(1)
        Asserted for one clock after the last data bit of a packet was received.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_data = Signal()
        self.i_se0 = Signal()

        self.submodules.pkt = pkt = FSM()

        pkt_start = Signal()
        pkt_active = Signal()
        pkt_end = Signal()

        for i in range(5):
            pkt.act("D%d" % i,
                If(self.i_valid,
                    If(self.i_data | self.i_se0,
                        # Receiving '1' or SE0 early resets the packet start counter.
                        NextState("D0")
                    ).Else(
                        # Receiving '0' increments the packet start counter.
                        NextState("D%d" % (i + 1))
                    )
                )
            )

        pkt.act("D5",
            If(self.i_valid,
                If(self.i_se0,
                    NextState("D0")
                # once we get a '1', the packet is active
                ).Elif(self.i_data,
                    pkt_start.eq(1),
                    NextState("PKT_ACTIVE")
                )
            )
        )

        pkt.act("PKT_ACTIVE",
            pkt_active.eq(1),
            If(self.i_valid & self.i_se0,
                NextState("D0"),
                pkt_active.eq(0),
                pkt_end.eq(1)
            )
        )

        # pass all of the outputs through a pipe stage
        self.o_pkt_start = Signal()
        self.o_pkt_active = Signal()
        self.o_pkt_end = Signal()
        self.comb += [
            self.o_pkt_start.eq(pkt_start),
            self.o_pkt_active.eq(pkt_active),
            self.o_pkt_end.eq(pkt_end),
        ]

class RxNRZIDecoder(Module):
    """RX NRZI decoder.

    In order to ensure there are enough bit transitions for a receiver to recover
    the clock usb uses NRZI encoding.  This module processes the incoming
    dj, dk, se0, and valid signals and decodes them to data values.  It
    also pipelines the se0 signal and passes it through unmodified.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.8
    https://en.wikipedia.org/wiki/Non-return-to-zero

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_dj : Signal(1)
        Indicates the bus is currently in a Full-Speed J-state.
        Qualified by valid.

    i_dk : Signal(1)
        Indicates the bus is currently in a Full-Speed K-state.
        Qualified by valid.

    i_se0 : Signal(1)
        Indicates the bus is currently in a SE0 state.
        Qualified by valid.

    Output Ports
    ------------
    Output ports are data members of the module. All output ports are flopped.

    o_valid : Signal(1)
        Qualifier for all of the output signals. Indicates one bit of valid
        data is present on the outputs.

    o_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    o_se0 : Signal(1)
        Indicates the bus is currently in a SE0 state.
        Qualified by valid.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_dj = Signal()
        self.i_dk = Signal()
        self.i_se0 = Signal()

        # pass all of the outputs through a pipe stage
        self.o_valid = Signal(1)
        self.o_data = Signal(1)
        self.o_se0 = Signal(1)

        if False:
            valid = Signal(1)
            data = Signal(1)

            # simple state machine decodes a JK transition as a '0' and no transition as a '1'.  se0 is ignored.
            self.submodules.nrzi = nrzi = FSM()

            nrzi.act("DJ",
                If(self.i_valid,
                    valid.eq(1),

                    If(self.i_dj,
                        data.eq(1)
                    ).Elif(self.i_dk,
                        data.eq(0),
                        NextState("DK")
                    )
                )
            )

            nrzi.act("DK",
                If(self.i_valid,
                    valid.eq(1),

                    If(self.i_dj,
                        data.eq(0),
                        NextState("DJ")
                    ).Elif(self.i_dk,
                        data.eq(1)
                    )
                )
            )

            self.sync += [
                self.o_valid.eq(valid),
                If(valid,
                    self.o_se0.eq(self.i_se0),
                    self.o_data.eq(data),
                ),
            ]
        else:
            last_data = Signal()
            self.sync += [
                If(self.i_valid,
                    last_data.eq(self.i_dk),
                    self.o_data.eq(~(self.i_dk ^ last_data)),
                    self.o_se0.eq((~self.i_dj) & (~self.i_dk)),
                ),
                self.o_valid.eq(self.i_valid),
            ]

@ResetInserter()
class RxShifter(Module):
    """RX Shifter

    A shifter is responsible for shifting in serial bits and presenting them
    as parallel data.  The shifter knows how many bits to shift and has
    controls for resetting the shifter.

    Clock Domain
    ------------
    usb_12 : 12MHz

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Number of bits to shift in.

    Input Ports
    -----------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Serial input data.
        Qualified by valid.

    Output Ports
    ------------
    o_data : Signal(width)
        Shifted in data.

    o_put : Signal(1)
        Asserted for one clock once the register is full.
    """

    def __init__(self, width):
        self.i_valid = Signal()
        self.i_data = Signal()

        self.o_data = Signal(width)
        self.o_put = Signal()

        # Instead of using a counter, we will use a sentinel bit in the shift register to indicate when it is full.
        shift_reg = Signal(width+1, reset=0b1)

        self.comb += self.o_data.eq(shift_reg[0:width])
        self.sync += [
            self.o_put.eq(shift_reg[width-1] & ~shift_reg[width] & self.i_valid),
            If(self.i_valid,
                If(shift_reg[width],
                    shift_reg.eq(Cat(self.i_data, shift_reg.reset[0:width])),
                ).Else(
                    shift_reg.eq(Cat(self.i_data, shift_reg[0:width])),
                ),
            ),
        ]

class RxPipeline(Module):
    def __init__(self):
        self.reset = Signal()

        # 12MHz USB alignment pulse in 48MHz clock domain
        self.o_bit_strobe = Signal()

        # Reset state is J
        self.i_usbp = Signal(reset=1)
        self.i_usbn = Signal(reset=0)

        self.o_data_strobe = Signal()
        self.o_data_payload = Signal(8)

        self.o_pkt_start = Signal()
        self.o_pkt_in_progress = Signal()
        self.o_pkt_end = Signal()

        # 48MHz domain
        # Clock recovery
        clock_data_recovery = RxClockDataRecovery(self.i_usbp, self.i_usbn)
        self.submodules.clock_data_recovery = ClockDomainsRenamer("usb_48")(clock_data_recovery)
        self.comb += [
            self.o_bit_strobe.eq(clock_data_recovery.line_state_valid),
        ]

        # A reset condition is one where the device is in SE0 for more than 2.5 uS, which is ~30 bit times.
        self.o_reset = Signal()
        reset_counter = Signal(7)
        self.comb += self.o_reset.eq(reset_counter[6])
        self.sync.usb_48 += [
            If(clock_data_recovery.line_state_valid,
                If(clock_data_recovery.line_state_se0,
                    If(~reset_counter[6],
                        reset_counter.eq(reset_counter + 1),
                    )
                ).Else(
                    reset_counter.eq(0),
                )
            )
        ]

        # NRZI decoding
        nrzi = RxNRZIDecoder()
        self.submodules.nrzi = nrzi = ClockDomainsRenamer("usb_48")(nrzi)
        self.comb += [
            nrzi.i_valid.eq(self.o_bit_strobe),
            nrzi.i_dj.eq(clock_data_recovery.line_state_dj),
            nrzi.i_dk.eq(clock_data_recovery.line_state_dk),
            nrzi.i_se0.eq(clock_data_recovery.line_state_se0),
        ]

        # The packet detector asserts the reset of the pipeline.
        reset = Signal()
        detect = RxPacketDetect()
        self.submodules.detect = detect = ClockDomainsRenamer("usb_48")(detect)
        self.comb += [
            detect.reset.eq(self.reset),
            detect.i_valid.eq(nrzi.o_valid),
            detect.i_se0.eq(nrzi.o_se0),
            detect.i_data.eq(nrzi.o_data),
            reset.eq(~detect.o_pkt_active),
        ]

        bitstuff = RxBitstuffRemover()
        self.submodules.bitstuff = ClockDomainsRenamer("usb_48")(bitstuff)
        self.comb += [
            bitstuff.reset.eq(~detect.o_pkt_active | self.reset),
            bitstuff.i_valid.eq(nrzi.o_valid),
            bitstuff.i_data.eq(nrzi.o_data),
        ]

        last_reset = Signal()
        self.sync.usb_48 += [
            last_reset.eq(reset),
        ]

        # 1bit->8bit (1byte) serial to parallel conversion
        shifter = RxShifter(width=8)
        self.submodules.shifter = shifter = ClockDomainsRenamer("usb_48")(shifter)
        self.comb += [
            shifter.reset.eq(last_reset),
            shifter.i_data.eq(bitstuff.o_data),
            shifter.i_valid.eq(~bitstuff.o_stall & detect.o_pkt_active),
        ]

        # Cross the data from the 48MHz domain to the 12MHz domain
        flag_start = Signal()
        flag_end = Signal()
        flag_valid = Signal()
        payloadFifo = _AsyncFIFO(8, 2)
        self.submodules.payloadFifo = payloadFifo = ClockDomainsRenamer({"write":"usb_48", "read":"usb_12"})(payloadFifo)

        self.comb += [
            payloadFifo.din.eq(shifter.o_data[::-1]),
            payloadFifo.we.eq(shifter.o_put),
            self.o_data_payload.eq(payloadFifo.dout),
            self.o_data_strobe.eq(payloadFifo.readable),
            payloadFifo.re.eq(1),
        ]

        flagsFifo = _AsyncFIFO(2, 2)
        self.submodules.flagsFifo = flagsFifo = ClockDomainsRenamer({"write":"usb_48", "read":"usb_12"})(flagsFifo)

        self.comb += [
            flagsFifo.din[1].eq(detect.o_pkt_start),
            flagsFifo.din[0].eq(detect.o_pkt_end),
            flagsFifo.we.eq(detect.o_pkt_start | detect.o_pkt_end),
            flag_start.eq(flagsFifo.dout[1]),
            flag_end.eq(flagsFifo.dout[0]),
            flag_valid.eq(flagsFifo.readable),
            flagsFifo.re.eq(1),
        ]

        # Packet flag signals (in 12MHz domain)
        self.comb += [
            self.o_pkt_start.eq(flag_start & flag_valid),
            self.o_pkt_end.eq(flag_end & flag_valid),
        ]

        self.sync.usb_12 += [
            If(self.o_pkt_start,
                self.o_pkt_in_progress.eq(1),
            ).Elif(self.o_pkt_end,
                self.o_pkt_in_progress.eq(0),
            ),
        ]

@ResetInserter()
class TxBitstuffer(Module):
    """
    Bitstuff Insertion

    Long sequences of 1's would cause the receiver to lose it's lock on the
    transmitter's clock.  USB solves this with bitstuffing.  A '0' is stuffed
    after every 6 consecutive 1's.

    The TxBitstuffer is the only component in the transmit pipeline that can
    delay transmission of serial data.  It is therefore responsible for
    generating the bit_strobe signal that keeps the pipe moving forward.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.9
    https://en.wikipedia.org/wiki/Bit_stuffing

    Clock Domain
    ------------
    usb_12 : 48MHz

    Input Ports
    ------------
    i_data : Signal(1)
        Data bit to be transmitted on USB.

    Output Ports
    ------------
    o_data : Signal(1)
        Data bit to be transmitted on USB.

    o_stall : Signal(1)
        Used to apply backpressure on the tx pipeline.
    """

    def __init__(self):
        self.i_data = Signal()

        self.o_stall = Signal(1)
        self.o_will_stall = Signal(1)
        self.o_data = Signal(1)

        self.submodules.stuff = stuff = FSM()

        stuff_bit = Signal(1)

        for i in range(5):
            stuff.act("D%d" % i,
                If(self.i_data,
                    # Receiving '1' increments the bitstuff counter.
                    NextState("D%d" % (i + 1))
                ).Else(
                    # Receiving '0' resets the bitstuff counter.
                    NextState("D0")
                )
            )

        stuff.act("D5",
            If(self.i_data,
                # There's a '1', so indicate we might stall on the next loop.
                self.o_will_stall.eq(1),

                # Receiving '1' increments the bitstuff counter.
                NextState("D6")
            ).Else(
                # Receiving '0' resets the bitstuff counter.
                NextState("D0")
            )
        )

        stuff.act("D6",
            # stuff a bit
            stuff_bit.eq(1),

            # Reset the bitstuff counter
            NextState("D0")
        )

        self.comb += [
            self.o_stall.eq(stuff_bit)
        ]

        # flop outputs
        self.sync += [
            If(stuff_bit,
                self.o_data.eq(0),
            ).Else(
                self.o_data.eq(self.i_data),
            ),
        ]

class TxNRZIEncoder(Module):
    """
    NRZI Encode

    In order to ensure there are enough bit transitions for a receiver to recover
    the clock usb uses NRZI encoding.  This module processes the incoming
    dj, dk, se0, and valid signals and decodes them to data values.  It
    also pipelines the se0 signal and passes it through unmodified.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.8
    https://en.wikipedia.org/wiki/Non-return-to-zero

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    i_valid : Signal(1)
        Qualifies oe, data, and se0.

    i_oe : Signal(1)
        Indicates that the transmit pipeline should be driving USB.

    i_data : Signal(1)
        Data bit to be transmitted on USB. Qualified by o_valid.

    i_se0 : Signal(1)
        Overrides value of o_data when asserted and indicates that SE0 state
        should be asserted on USB. Qualified by o_valid.

    Output Ports
    ------------
    o_usbp : Signal(1)
        Raw value of USB+ line.

    o_usbn : Signal(1)
        Raw value of USB- line.

    o_oe : Signal(1)
        When asserted it indicates that the tx pipeline should be driving USB.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_oe = Signal()
        self.i_data = Signal()

        # Simple state machine to perform NRZI encoding.
        self.submodules.nrzi = nrzi = FSM()

        usbp = Signal(1)
        usbn = Signal(1)
        oe = Signal(1)

        # wait for new packet to start
        nrzi.act("IDLE",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(0),

            If(self.i_valid,
                If(self.i_oe,
                    # first bit of sync always forces a transition, we idle in J so the first output bit is K.
                    NextState("DK")
                )
            )
        )

        # the output line is in state J
        nrzi.act("DJ",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                If(~self.i_oe,
                    NextState("SE0A")
                ).Elif(self.i_data,
                    NextState("DJ")
                ).Else(
                    NextState("DK")
                )
            )
        )

        # the output line is in state K
        nrzi.act("DK",
            usbp.eq(0),
            usbn.eq(1),
            oe.eq(1),

            If(self.i_valid,
                If(~self.i_oe,
                    NextState("SE0A")
                ).Elif(self.i_data,
                    NextState("DK")
                ).Else(
                    NextState("DJ")
                )
            )
        )

        # first bit of the SE0 state
        nrzi.act("SE0A",
            usbp.eq(0),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("SE0B")
            )
        )
        # second bit of the SE0 state
        nrzi.act("SE0B",
            usbp.eq(0),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("EOPJ")
            )
        )

        # drive the bus back to J before relinquishing control
        nrzi.act("EOPJ",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("IDLE")
            )
        )

        # flop all outputs
        self.o_usbp = Signal(1)
        self.o_usbn = Signal(1)
        self.o_oe = Signal(1)

        self.sync += [
            self.o_oe.eq(oe),
            self.o_usbp.eq(usbp),
            self.o_usbn.eq(usbn),
        ]

@ResetInserter()
@CEInserter()
class TxShifter(Module):
    """Transmit Shifter

    TxShifter accepts parallel data and shifts it out serially.

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the data to be shifted.

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    i_data : Signal(width)
        Data to be transmitted.

    Output Ports
    ------------
    Output ports are data members of the module. All outputs are flopped.

    o_data : Signal(1)
        Serial data output.

    o_empty : Signal(1)
        Asserted the cycle before the shifter loads in more i_data.

    o_get : Signal(1)
        Asserted the cycle after the shifter loads in i_data.

    """

    def __init__(self, width):
        self.i_data = Signal(width)
        self.o_get = Signal(1)
        self.o_empty = Signal(1)

        self.o_data = Signal(1)

        shifter = Signal(width)
        pos = Signal(width, reset=0b1)

        empty = Signal(1)
        self.sync += [
            pos.eq(pos >> 1),
            shifter.eq(shifter >> 1),
            If(empty,
                shifter.eq(self.i_data),
                pos.eq(1 << (width-1)),
            ),
            self.o_get.eq(empty),
        ]
        self.comb += [
            empty.eq(pos[0]),
            self.o_empty.eq(empty),
            self.o_data.eq(shifter[0]),
        ]

@CEInserter()
@ResetInserter()
class TxSerialCrcGenerator(Module):
    """
    Transmit CRC Generator

    TxSerialCrcGenerator generates a running CRC.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 8.3.5
    https://en.wikipedia.org/wiki/Cyclic_redundancy_check

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the CRC.

    polynomial : int
        CRC polynomial in integer form.

    initial : int
        Initial value of the CRC register before data starts shifting in.

    Input Ports
    ------------
    i_data : Signal(1)
        Serial data to generate CRC for.

    Output Ports
    ------------
    o_crc : Signal(width)
        Current CRC value.

    """

    def __init__(self, width, polynomial, initial):

        self.i_data = Signal()

        crc = Signal(width, reset=initial)
        crc_invert = Signal(1)

        self.comb += [
            crc_invert.eq(self.i_data ^ crc[width - 1])
        ]

        for i in range(width):
            rhs_data = None
            if i == 0:
                rhs_data = crc_invert
            else:
                if (polynomial >> i) & 1:
                    rhs_data = crc[i - 1] ^ crc_invert
                else:
                    rhs_data = crc[i - 1]

            self.sync += [
                crc[i].eq(rhs_data)
            ]

        self.o_crc = Signal(width)

        for i in range(width):
            self.comb += [
                self.o_crc[i].eq(1 ^ crc[width - i - 1]),
            ]

def bytes_to_int(d):
    """Convert a list of bytes to an int

    Bytes are in LSB first.

    >>> hex(bytes_to_int([0, 1]))
    '0x100'
    >>> hex(bytes_to_int([1, 2]))
    '0x201'
    """
    v = 0
    for i,d in enumerate(d):
        v |= d << (i*8)
    return v

def cols(rows):
    """
    >>> a = [
    ...  [1, 2],
    ...  ['a', 'b'],
    ...  [4, 5],
    ... ]
    >>> for c in cols(a):
    ...   print(c)
    [1, 'a', 4]
    [2, 'b', 5]
    >>> a = [
    ...  [1, 2, 3],
    ...  ['a', 'b', 'c'],
    ... ]
    >>> for c in cols(a):
    ...   print(c)
    [1, 'a']
    [2, 'b']
    [3, 'c']

    """
    all_c = []
    for ci in range(len(rows[0])):
        all_c.append([])
    for ci in range(len(rows[0])):
        for ri in range(len(rows)):
            assert len(rows[ri]) == len(all_c), "len(%r) != %i" % (rows[ri], len(all_c))
            all_c[ci].append(rows[ri][ci])
    return all_c

def lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data):
    """
    shift_by == num_data_bits
    len(data_cur) == num_data_bits
    >>> for i in range(5):
    ...   l = [0]*5; l[i] = 1
    ...   r = lfsr_serial_shift_crc(
    ...      lfsr_poly=[0,0,1,0,1], # (5, 2, 0)
    ...      lfsr_cur=l,
    ...      data=[0,0,0,0],
    ...   )
    ...   print("Min[%i] =" % i, r)
    Min[0] = [1, 0, 0, 0, 0]
    Min[1] = [0, 0, 1, 0, 1]
    Min[2] = [0, 1, 0, 1, 0]
    Min[3] = [1, 0, 1, 0, 0]
    Min[4] = [0, 1, 1, 0, 1]
    >>> for i in range(4):
    ...   d = [0]*4; d[i] = 1
    ...   r = lfsr_serial_shift_crc(
    ...      lfsr_poly=[0,0,1,0,1], # (5, 2, 0)
    ...      lfsr_cur=[0,0,0,0,0],
    ...      data=d,
    ...   )
    ...   print("Nin[%i] =" % i, r)
    Nin[0] = [0, 0, 1, 0, 1]
    Nin[1] = [0, 1, 0, 1, 0]
    Nin[2] = [1, 0, 1, 0, 0]
    Nin[3] = [0, 1, 1, 0, 1]

    """
    lfsr_poly = lfsr_poly[::-1]
    data = data[::-1]

    shift_by = len(data)
    lfsr_poly_size = len(lfsr_poly)
    assert lfsr_poly_size > 1
    assert len(lfsr_cur) == lfsr_poly_size

    lfsr_next = list(lfsr_cur)
    for j in range(shift_by):
        lfsr_upper_bit = lfsr_next[lfsr_poly_size-1]
        for i in range(lfsr_poly_size-1, 0, -1):
            if lfsr_poly[i]:
                lfsr_next[i] = lfsr_next[i-1] ^ lfsr_upper_bit ^ data[j]
            else:
                lfsr_next[i] = lfsr_next[i-1]
        lfsr_next[0] = lfsr_upper_bit ^ data[j]
    return list(lfsr_next[::-1])

def print_matrix(crc_width, cols_nin, cols_min):
    """
    >>> crc_width = 5
    >>> data_width = 4
    >>> poly_list = [0, 0, 1, 0, 1]
    >>> _, cols_nin, cols_min = build_matrix(poly_list, data_width)
    >>> print_matrix(crc_width, cols_nin, cols_min)
       0 d[ 0],      ,      , d[ 3],      , c[ 1],      ,      , c[ 4]
       1      , d[ 1],      ,      ,      ,      , c[ 2],      ,
       2 d[ 0],      , d[ 2], d[ 3],      , c[ 1],      , c[ 3], c[ 4]
       3      , d[ 1],      , d[ 3],      ,      , c[ 2],      , c[ 4]
       4      ,      , d[ 2],      , c[ 0],      ,      , c[ 3],
    """
    for i in range(crc_width):
        text_xor = []
        for j, use in enumerate(cols_nin[i]):
            if use:
                text_xor.append('d[%2i]' % j)
            else:
                text_xor.append('     ')
        for j, use in enumerate(cols_min[i]):
            if use:
                text_xor.append('c[%2i]' % j)
            else:
                text_xor.append('     ')
        print("{:4d} {}".format(i, ", ".join("{:>5s}".format(x) for x in text_xor).rstrip()))

def build_matrix(lfsr_poly, data_width):
    """
    >>> print("\\n".join(build_matrix([0,0,1,0,1], 4)[0]))
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [1, 0, 0, 0]) = [0, 0, 1, 0, 1]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 1, 0, 0]) = [0, 1, 0, 1, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 0, 1, 0]) = [1, 0, 1, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1]) = [0, 1, 1, 0, 1]
    <BLANKLINE>
    lfsr([0, 0, 1, 0, 1], [1, 0, 0, 0, 0], [0, 0, 0, 0]) = [1, 0, 0, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 0, 0, 0]) = [0, 0, 1, 0, 1]
    lfsr([0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 0]) = [0, 1, 0, 1, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0]) = [1, 0, 1, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0]) = [0, 1, 1, 0, 1]
    <BLANKLINE>
    Mout[4] = [0, 0, 1, 0] [1, 0, 0, 1, 0]
    Mout[3] = [0, 1, 0, 1] [0, 0, 1, 0, 1]
    Mout[2] = [1, 0, 1, 1] [0, 1, 0, 1, 1]
    Mout[1] = [0, 1, 0, 0] [0, 0, 1, 0, 0]
    Mout[0] = [1, 0, 0, 1] [0, 1, 0, 0, 1]
    """
    lfsr_poly_size = len(lfsr_poly)

    # data_width*lfsr_polysize matrix == lfsr(0,Nin)
    rows_nin = []

    # (a) calculate the N values when Min=0 and Build NxM matrix
    #  - Each value is one hot encoded (there is only one bit)
    #  - IE N=4, 0x1, 0x2, 0x4, 0x8
    #  - Mout = F(Nin,Min=0)
    #  - Each row contains the results of (a)
    #  - IE row[0] == 0x1, row[1] == 0x2
    #  - Output is M-bit wide (CRC width)
    #  - Each column of the matrix represents an output bit Mout[i] as a function of Nin
    info = []
    for i in range(data_width):
        # lfsr_cur = [0,...,0] = Min
        lfsr_cur = [0,]*lfsr_poly_size
        # data = [0,..,1,..,0] = Nin
        data = [0,]*data_width
        data[i] = 1
        # Calculate the CRC
        rows_nin.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_nin[-1]))
    assert len(rows_nin) == data_width
    cols_nin = cols(rows_nin)[::-1]

    # lfsr_polysize*lfsr_polysize matrix == lfsr(Min,0)
    info.append("")
    rows_min = []
    for i in range(lfsr_poly_size):
        # lfsr_cur = [0,..,1,...,0] = Min
        lfsr_cur = [0,]*lfsr_poly_size
        lfsr_cur[i] = 1
        # data = [0,..,0] = Nin
        data = [0,]*data_width
        # Calculate the crc
        rows_min.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_min[-1]))
    assert len(rows_min) == lfsr_poly_size
    cols_min = cols(rows_min)[::-1]

    # (c) Calculate CRC for the M values when Nin=0 and Build MxM matrix
    #  - Each value is one hot encoded
    #  - Mout = F(Nin=0,Min)
    #  - Each row contains results from (7)
    info.append("")
    for i in range(data_width, -1, -1):
        info.append("Mout[%i] = %r %r" % (i, cols_nin[i], cols_min[i]))

    return info, cols_nin, cols_min

@ResetInserter()
class TxParallelCrcGenerator(Module):
    """
    Transmit CRC Generator

    TxParallelCrcGenerator generates a running CRC.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 8.3.5
    https://en.wikipedia.org/wiki/Cyclic_redundancy_check

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the CRC.

    polynomial : int
        CRC polynomial in integer form.

    initial : int
        Initial value of the CRC register before data starts shifting in.

    Input Ports
    ------------
    i_data_payload : Signal(8)
        Byte wide data to generate CRC for.

    i_data_strobe : Signal(1)
        Strobe signal for the payload.

    Output Ports
    ------------
    o_crc : Signal(width)
        Current CRC value.

    """

    def __init__(self, data_width, crc_width, polynomial, initial=0):
        self.i_data_payload = Signal(data_width)
        self.i_data_strobe = Signal()
        self.o_crc = Signal(crc_width)
        crc_dat = Signal(data_width)
        crc_cur = Signal(crc_width, reset=initial)
        crc_next = Signal(crc_width, reset_less=True)

        crc_cur_reset_bits = [int(i) for i in "{0:0{width}b}".format(crc_cur.reset.value,width=crc_width)[::-1]]

        self.comb += [
            crc_dat.eq(self.i_data_payload[::-1]),
            # FIXME: Is XOR ^ initial actually correct here?
            self.o_crc.eq(crc_cur[::-1] ^ initial),
        ]

        self.sync += [
            If(self.i_data_strobe,
                crc_cur.eq(crc_next),
            ),
        ]

        poly_list = []
        for i in range(crc_width):
            poly_list.insert(0, polynomial >> i & 0x1)
        assert len(poly_list) == crc_width

        _, cols_nin, cols_min = build_matrix(poly_list, data_width)

        crc_next_reset_bits = list(crc_cur_reset_bits)
        for i in range(crc_width):
            to_xor = []
            crc_next_reset_bit_i = []
            for j, use in enumerate(cols_nin[i]):
                if use:
                    to_xor.append(crc_dat[j])
                    crc_next_reset_bit_i.append(0)
            for j, use in enumerate(cols_min[i]):
                if use:
                    to_xor.append(crc_cur[j])
                    crc_next_reset_bit_i.append(crc_cur_reset_bits[j])

            crc_next_reset_bits[i] = functools.reduce(operator.xor, crc_next_reset_bit_i)

            self.comb += [
                crc_next[i].eq(functools.reduce(operator.xor, to_xor)),
            ]

        crc_next_reset_value = int("0b"+"".join(str(i) for i in crc_next_reset_bits[::-1]), 2)
        crc_next.reset.value = crc_next_reset_value

class TxCrcPipeline(Module):
    def __init__(self):
        self.i_data_payload = Signal(8)
        self.o_data_ack = Signal()
        self.o_crc16 = Signal(16)

        self.reset = reset = Signal()
        reset_n1 = Signal()
        reset_n2 = Signal()
        self.ce = ce = Signal()

        self.sync += [
            reset_n2.eq(reset_n1),
            reset_n1.eq(reset),
        ]

        self.submodules.shifter = shifter = TxShifter(width=8)
        self.comb += [
            shifter.i_data.eq(self.i_data_payload),
            shifter.reset.eq(reset),
            shifter.ce.eq(ce),
            self.o_data_ack.eq(shifter.o_get),
        ]

        self.submodules.crc = crc_calc = TxSerialCrcGenerator(
            width      = 16,
            polynomial = 0b1000000000000101,
            initial    = 0b1111111111111111,
        )
        self.comb += [
            crc_calc.i_data.eq(shifter.o_data),
            crc_calc.reset.eq(reset_n2),
            crc_calc.ce.eq(ce),
            self.o_crc16.eq(crc_calc.o_crc),
        ]

class TxPipeline(Module):
    def __init__(self):
        self.i_bit_strobe = Signal()

        self.i_data_payload = Signal(8)
        self.o_data_strobe = Signal()

        self.i_oe = Signal()

        self.o_usbp = Signal()
        self.o_usbn = Signal()
        self.o_oe = Signal()

        self.o_pkt_end = Signal()

        tx_pipeline_fsm = FSM()
        self.submodules.tx_pipeline_fsm = ClockDomainsRenamer("usb_12")(tx_pipeline_fsm)
        shifter = TxShifter(width=8)
        self.submodules.shifter = ClockDomainsRenamer("usb_12")(shifter)
        bitstuff = TxBitstuffer()
        self.submodules.bitstuff = ClockDomainsRenamer("usb_12")(bitstuff)
        nrzi = TxNRZIEncoder()
        self.submodules.nrzi = ClockDomainsRenamer("usb_48")(nrzi)

        sync_pulse = Signal(8)

        self.fit_dat = fit_dat = Signal()
        self.fit_oe  = fit_oe  = Signal()

        da_reset_shifter = Signal()
        da_reset_bitstuff = Signal() # Need to reset the bit stuffer 1 cycle after the shifter.
        stall = Signal()

        # These signals are set during the sync pulse
        sp_reset_bitstuff = Signal()
        sp_reset_shifter = Signal()
        sp_bit = Signal()
        sp_o_data_strobe = Signal()

        # 12MHz domain
        da_stalled_reset = Signal()
        bitstuff_valid_data = Signal()

        # Keep a Gray counter around to smoothly transition between states
        state_gray = Signal(2)
        state_data = Signal()
        state_sync = Signal()

        self.comb += [
            shifter.i_data.eq(self.i_data_payload),
            # Send a data strobe when we're two bits from the end of the sync pulse.
            # This is because the pipeline takes two bit times, and we want to ensure the pipeline has spooled up enough by the time we're there.

            shifter.reset.eq(da_reset_shifter | sp_reset_shifter),
            shifter.ce.eq(~stall),

            bitstuff.reset.eq(da_reset_bitstuff),
            bitstuff.i_data.eq(shifter.o_data),
            stall.eq(bitstuff.o_stall),

            sp_bit.eq(sync_pulse[0]),
            sp_reset_bitstuff.eq(sync_pulse[0]),

            # The shifter has one clock cycle of latency, so reset it one cycle before the end of the sync byte.
            sp_reset_shifter.eq(sync_pulse[1]),

            sp_o_data_strobe.eq(sync_pulse[5]),

            state_data.eq(state_gray[0] & state_gray[1]),
            state_sync.eq(state_gray[0] & ~state_gray[1]),

            fit_oe.eq(state_data | state_sync),
            fit_dat.eq((state_data & shifter.o_data & ~bitstuff.o_stall) | sp_bit),
            self.o_data_strobe.eq((state_data & shifter.o_get & ~stall & self.i_oe) | sp_o_data_strobe),
        ]

        # If we reset the shifter, then o_empty will go high on the next cycle.

        self.sync.usb_12 += [
            # If the shifter runs out of data, percolate the "reset" signal to the shifter, and then down to the bitstuffer.
            # da_reset_shifter.eq(~stall & shifter.o_empty & ~da_stalled_reset),
            # da_stalled_reset.eq(da_reset_shifter),
            # da_reset_bitstuff.eq(~stall & da_reset_shifter),
            bitstuff_valid_data.eq(~stall & shifter.o_get & self.i_oe),
        ]

        tx_pipeline_fsm.act('IDLE',
            If(self.i_oe,
                NextState('SEND_SYNC'),
                NextValue(sync_pulse, 1 << 7),
                NextValue(state_gray, 0b01),
            ).Else(
                NextValue(state_gray, 0b00),
            )
        )

        tx_pipeline_fsm.act('SEND_SYNC',
            NextValue(sync_pulse, sync_pulse >> 1),

            If(sync_pulse[0],
                NextState('SEND_DATA'),
                NextValue(state_gray, 0b11),
            ).Else(
                NextValue(state_gray, 0b01),
            ),
        )

        tx_pipeline_fsm.act('SEND_DATA',
            If(~self.i_oe & shifter.o_empty & ~bitstuff.o_stall,
                If(bitstuff.o_will_stall,
                    NextState('STUFF_LAST_BIT')
                ).Else(
                    NextValue(state_gray, 0b10),
                    NextState('IDLE'),
                )
            ).Else(
                NextValue(state_gray, 0b11),
            ),
        )

        tx_pipeline_fsm.act('STUFF_LAST_BIT',
            NextValue(state_gray, 0b10),
            NextState('IDLE'),
        )

        # 48MHz domain
        # NRZI encoding
        nrzi_dat = Signal()
        nrzi_oe = Signal()

        # Cross the data from the 12MHz domain to the 48MHz domain
        cdc_dat = MultiReg(fit_dat, nrzi_dat, odomain="usb_48", n=3)
        cdc_oe  = MultiReg(fit_oe, nrzi_oe, odomain="usb_48", n=3)
        self.specials += [cdc_dat, cdc_oe]

        self.comb += [
            nrzi.i_valid.eq(self.i_bit_strobe),
            nrzi.i_data.eq(nrzi_dat),
            nrzi.i_oe.eq(nrzi_oe),

            self.o_usbp.eq(nrzi.o_usbp),
            self.o_usbn.eq(nrzi.o_usbn),
            self.o_oe.eq(nrzi.o_oe),
        ]

class EndpointType(IntEnum):
    IN = 1
    OUT = 2
    BIDIR = IN | OUT

    @classmethod
    def epaddr(cls, ep_num, ep_dir):
        assert ep_dir != cls.BIDIR
        return ep_num << 1 | (ep_dir == cls.IN)

    @classmethod
    def epnum(cls, ep_addr):
        return ep_addr >> 1

    @classmethod
    def epdir(cls, ep_addr):
        if ep_addr & 0x1 == 0:
            return cls.OUT
        else:
            return cls.IN

class EndpointResponse(IntEnum):
    """
    >>> # Clearing top bit of STALL -> NAK
    >>> assert (EndpointResponse.STALL & EndpointResponse.RESET_MASK) == EndpointResponse.NAK
    """

    STALL = 0b11
    ACK   = 0b00
    NAK   = 0b01
    NONE  = 0b10

    RESET_MASK = 0b01

class PacketHeaderDecode(Module):
    def __init__(self, rx):
        self.submodules.rx = rx

        self.o_pid = Signal(4)
        self.o_addr = Signal(7)
        endp4 = Signal()
        self.o_endp = Signal(4)
        crc5 = Signal(5)
        self.o_decoded = Signal()

        # FIXME: This whole module should just be in the usb_12 clock domain?
        self.submodules.fsm = fsm = ClockDomainsRenamer("usb_12")(FSM())
        fsm.act("IDLE",
            If(rx.o_pkt_start,
                NextState("WAIT_PID"),
            ),
        )
        pid = rx.o_data_payload[0:4]
        fsm.act("WAIT_PID",
            If(rx.o_data_strobe,
                NextValue(self.o_pid, pid),
                Case(pid & PIDTypes.TYPE_MASK, {
                    PIDTypes.TOKEN:     NextState("WAIT_BYTE0"),
                    PIDTypes.DATA:      NextState("END"),
                    PIDTypes.HANDSHAKE: NextState("END"),
                }),
            ),
        )
        fsm.act("WAIT_BYTE0",
            If(rx.o_data_strobe,
                NextValue(self.o_addr[0:7], rx.o_data_payload[0:7]),
                NextValue(endp4, rx.o_data_payload[7]),
                NextState("WAIT_BYTE1"),
            ),
        )
        fsm.act("WAIT_BYTE1",
            If(rx.o_data_strobe,
                NextValue(self.o_endp, Cat(endp4, rx.o_data_payload[0:3])),
                NextValue(crc5, rx.o_data_payload[4:]),
                NextState("END"),
            ),
        )
        fsm.act("END",
            self.o_decoded.eq(1),
            NextState("IDLE"),
        )

class TxPacketSend(Module):
    def __init__(self, tx, auto_crc=True):
        self.submodules.tx = tx

        self.i_pkt_start = Signal()
        self.o_pkt_end = Signal()

        self.i_pid = Signal(4)
        self.i_data_payload = Signal(8)
        self.i_data_ready = Signal()
        self.o_data_ack = Signal()

        o_oe12 = Signal()
        self.specials += MultiReg(tx.o_oe, o_oe12, odomain="usb_12", n=1)

        pid = Signal(4)

        fsm = FSM()
        self.submodules.fsm = fsm = ClockDomainsRenamer("usb_12")(fsm)
        fsm.act('IDLE',
            NextValue(tx.i_oe, self.i_pkt_start),
            If(self.i_pkt_start,
                # If i_pkt_start is set, then send the next packet.
                # We pre-queue the SYNC byte here to cut down on latency.
                NextState('QUEUE_SYNC'),
            ).Else(
                NextValue(tx.i_oe, 0),
            )
        )

        # Send the QUEUE_SYNC byte
        fsm.act('QUEUE_SYNC',
            # The PID might change mid-sync, because we're still figuring out what the response ought to be.
            NextValue(pid, self.i_pid),
            tx.i_data_payload.eq(1),
            If(tx.o_data_strobe,
                NextState('QUEUE_PID'),
            ),
        )

        # Send the PID byte
        fsm.act('QUEUE_PID',
            tx.i_data_payload.eq(Cat(pid, pid ^ 0b1111)),
            If(tx.o_data_strobe,
                If(pid & PIDTypes.TYPE_MASK == PIDTypes.HANDSHAKE,
                    NextState('WAIT_TRANSMIT'),
                ).Elif(pid & PIDTypes.TYPE_MASK == PIDTypes.DATA,
                    NextState('QUEUE_DATA0'),
                ).Else(
                    NextState('ERROR'),
                ),
            ),
        )

        nextstate = 'WAIT_TRANSMIT'
        if auto_crc:
            nextstate = 'QUEUE_CRC0'

        fsm.act('QUEUE_DATA0',
            If(~self.i_data_ready,
                NextState(nextstate),
            ).Else(
                NextState('QUEUE_DATAn'),
            ),
        )

        # Keep transmitting data bytes until the i_data_ready signal is not high on a o_data_strobe event.
        fsm.act('QUEUE_DATAn',
            tx.i_data_payload.eq(self.i_data_payload),
            self.o_data_ack.eq(tx.o_data_strobe),
            If(~self.i_data_ready,
                NextState(nextstate),
            ),
        )

        if auto_crc:
            crc = TxParallelCrcGenerator(
                crc_width  = 16,
                data_width = 8,
                polynomial = 0b1000000000000101, # polynomial = (16, 15, 2, 0)
                initial    = 0b1111111111111111, # seed = 0xFFFF
            )
            self.submodules.crc = crc = ClockDomainsRenamer("usb_12")(crc)

            self.comb += [
                crc.i_data_payload.eq(self.i_data_payload),
                crc.reset.eq(fsm.ongoing('QUEUE_PID')),
                If(fsm.ongoing('QUEUE_DATAn'),
                    crc.i_data_strobe.eq(tx.o_data_strobe),
                ),
            ]

            fsm.act('QUEUE_CRC0',
                tx.i_data_payload.eq(crc.o_crc[:8]),
                If(tx.o_data_strobe,
                    NextState('QUEUE_CRC1'),
                ),
            )
            fsm.act('QUEUE_CRC1',
                tx.i_data_payload.eq(crc.o_crc[8:]),
                If(tx.o_data_strobe,
                    NextState('WAIT_TRANSMIT'),
                ),
            )

        fsm.act('WAIT_TRANSMIT',
            NextValue(tx.i_oe, 0),
            If(~o_oe12,
                self.o_pkt_end.eq(1),
                NextState('IDLE'),
            ),
        )

        fsm.act('ERROR')

class UsbTransfer(Module):
    def __init__(self, iobuf, auto_crc=True):
        self.submodules.iobuf = ClockDomainsRenamer("usb_48")(iobuf)

        self.submodules.tx = tx = TxPipeline()
        self.submodules.txstate = txstate = TxPacketSend(tx, auto_crc=auto_crc)

        self.submodules.rx = rx = RxPipeline()
        self.submodules.rxstate = rxstate = PacketHeaderDecode(rx)

        # ----------------------
        # USB 48MHz bit strobe
        # ----------------------
        self.comb += [
            tx.i_bit_strobe.eq(rx.o_bit_strobe),
        ]

        # Whether to reset the FSM
        self.reset = Signal()

        # The state of the USB reset (SE0) signal
        self.usb_reset = Signal()
        self.comb += self.usb_reset.eq(rx.o_reset)

        # ----------------------
        # Data paths
        # ----------------------
        self.data_recv_put = Signal()
        self.data_recv_payload = Signal(8)

        self.data_send_get = Signal()
        self.data_send_have = Signal()
        self.data_send_payload = Signal(8)

        # ----------------------
        # State signally
        # ----------------------
        # The value of these signals are generally dependent on endp, so we need to wait for the rdy signal to use them.
        self.rdy  = Signal(reset=1)
        self.dtb  = Signal()
        self.arm  = Signal()
        self.sta  = Signal()
        self.addr = Signal(7)       # If the address doesn't match, we won't respond

        # ----------------------
        # Tristate
        # ----------------------
        self.submodules.iobuf = iobuf
        self.comb += [
            rx.i_usbp.eq(iobuf.usb_p_rx),
            rx.i_usbn.eq(iobuf.usb_n_rx),
            iobuf.usb_tx_en.eq(tx.o_oe),
            iobuf.usb_p_tx.eq(tx.o_usbp),
            iobuf.usb_n_tx.eq(tx.o_usbn),
        ]

        self.tok    = Signal(4)     # Contains the transfer token type
        self.endp   = Signal(4)

        self.idle   = Signal(reset=0)      # Asserted when in the "WAIT_TOKEN" state
        self.start  = Signal()      # Asserted when a transfer is starting
        self.poll   = Signal()      # Asserted when polling for a response (i.e. one cycle after `self.start`)
        self.setup  = Signal()      # Asserted when a transfer is a setup
        self.commit = Signal()      # Asserted when a transfer succeeds
        self.retry  = Signal()      # Asserted when the host sends an IN without an ACK
        self.abort  = Signal()      # Asserted when a transfer fails
        self.end    = Signal()      # Asserted when transfer ends
        self.data_end=Signal()      # Asserted when a DATAx transfer finishes
        self.error  = Signal()      # Asserted when in the ERROR state
        self.comb += [
            self.end.eq(self.commit | self.abort),
        ]

        # Host->Device data path (Out + Setup data path)
        #
        # Token
        # Data
        # Handshake
        #
        # Setup --------------------
        # >Setup
        # >Data0[bmRequestType, bRequest, wValue, wIndex, wLength]
        # <Ack
        # --------------------------
        #
        # Data ---------------------
        # >Out        >Out        >Out
        # >DataX[..]  >DataX[..]  >DataX
        # <Ack        <Nak        <Stall
        #
        # Status -------------------
        # >Out
        # >Data0[]
        # <Ack
        # ---------------------------
        #
        # Host<-Device data path (In data path)
        # --------------------------
        # >In         >In     >In
        # <DataX[..]  <Stall  <Nak
        # >Ack
        # ---------------------------
        # >In
        # <Data0[]
        # >Ack
        # ---------------------------
        transfer = ResetInserter()(FSM(reset_state="WAIT_TOKEN"))
        self.submodules.transfer = transfer = ClockDomainsRenamer("usb_12")(transfer)
        self.comb += transfer.reset.eq(self.reset)
        transfer.act("ERROR",
            self.error.eq(1),
        )

        transfer.act("WAIT_TOKEN",
            self.idle.eq(1),
            If(rx.o_pkt_start,
                NextState("RECV_TOKEN"),
            ),
        )

        transfer.act("RECV_TOKEN",
            self.idle.eq(0),
            If(rxstate.o_decoded,
                # If the address doesn't match, go back and wait for a new token.
                If(rxstate.o_addr != self.addr,
                    NextState("WAIT_TOKEN"),
                ).Else(
                    self.start.eq(1),
                    NextValue(self.tok,  rxstate.o_pid),
                    NextValue(self.endp, rxstate.o_endp),
                    NextState("POLL_RESPONSE"),
                ),
            ),
        )

        response_pid = Signal(4)
        transfer.act("POLL_RESPONSE",
            self.poll.eq(1),
            If(self.rdy,
                # Work out the response
                If(self.tok == PID.SETUP,
                    NextValue(response_pid, PID.ACK),
                ).Elif(self.sta,
                    NextValue(response_pid, PID.STALL),
                ).Elif(self.arm,
                    NextValue(response_pid, PID.ACK),
                ).Else(
                    NextValue(response_pid, PID.NAK),
                ),

                If(rxstate.o_pid == PID.SOF,
                    NextState("WAIT_TOKEN"),
                ).Elif(self.tok == PID.SETUP,
                    NextState("WAIT_DATA"),
                ).Elif(self.tok == PID.OUT,
                    NextState("WAIT_DATA"),
                ).Elif(self.tok == PID.IN,
                    If(~self.arm | self.sta,
                        NextState("SEND_HAND"),
                    ).Else(
                        NextState("SEND_DATA"),
                    ),
                ).Else(
                    NextState("WAIT_TOKEN"),
                ),
            ),
        )

        # Out + Setup pathway
        transfer.act("WAIT_DATA",
            If(rxstate.o_decoded,
                If((rxstate.o_pid & PIDTypes.TYPE_MASK) == PIDTypes.DATA,
                    NextState("RECV_DATA"),
                ).Elif(rxstate.o_pid == PID.SOF,
                    NextState("WAIT_DATA"),
                ).Else(
                    NextState("ERROR"),
                )
            ),
        )

        transfer.act("RECV_DATA",
            # If we've indicated that we'll accept the data, put it into `data_recv_payload` and strobe `data_recv_put` every time a full byte comes in.
            If(response_pid == PID.ACK,
                self.data_recv_put.eq(rx.o_data_strobe),
            ),
            If(rx.o_pkt_end,
                NextState("SEND_HAND"),
            ),
        )
        self.comb += [
            self.data_recv_payload.eq(rx.o_data_payload),
        ]

        # In pathway
        transfer.act("SEND_DATA",
            If(self.dtb,
                txstate.i_pid.eq(PID.DATA1),
            ).Else(
                txstate.i_pid.eq(PID.DATA0),
            ),
            self.data_send_get.eq(txstate.o_data_ack),
            self.data_end.eq(txstate.o_pkt_end),
            If(txstate.o_pkt_end, NextState("WAIT_HAND")),
        )
        self.comb += [
            txstate.i_data_payload.eq(self.data_send_payload),
            txstate.i_data_ready.eq(self.data_send_have),
        ]

        # Handshake
        transfer.act("WAIT_HAND",
            If(rxstate.o_decoded,
                self.commit.eq(1),
                If(rxstate.o_pid == PID.ACK,
                    NextState("WAIT_TOKEN"),
                ).Elif(rxstate.o_pid == PID.IN,
                    self.retry.eq(1),
                    NextState("SEND_DATA"),
                ).Else(
                    NextState("ERROR"),
                )
            ),
        )
        transfer.act("SEND_HAND",
            txstate.i_pid.eq(response_pid),
            If(txstate.o_pkt_end,
                self.setup.eq(self.tok == PID.SETUP),
                If(response_pid == PID.ACK,
                    self.commit.eq(1),
                ).Else(
                    self.abort.eq(1),
                ),
                NextState("WAIT_TOKEN"),
            ),
        )

        # Code to reset header decoder when entering the WAIT_XXX states.
        self.comb += [
            If(tx.o_oe,
                rx.reset.eq(1),
            ),
        ]

        # Code to initiate the sending of packets when entering the SEND_XXX states.
        self.comb += [
            If(transfer.before_entering("SEND_DATA"),
                If(self.dtb,
                    txstate.i_pid.eq(PID.DATA1),
                ).Else(
                    txstate.i_pid.eq(PID.DATA0),
                ),
                txstate.i_pkt_start.eq(1),
            ),
            If(transfer.before_entering("SEND_HAND"),
                txstate.i_pid.eq(response_pid),
                txstate.i_pkt_start.eq(1),
            ),
        ]

class USBWishboneBridge(Module):

    def __init__(self, usb_core, clk_freq=12000000, magic_packet=0x43, cdc=False):
        self.wishbone = WishboneInterface()

        """USB Wishbone Bridge

        This bridge provides a transparent bridge to the target device's Wishbone bus over USB.
        It can operate without interfering with the device's USB stack.  It is simple enough to
        be able to work even if the USB stack is not enumerated, though the host may not cooperate."""

        """USB Wishbone Debug Protocol

        The protocol transfers four bytes a time in big-endian (i.e. USB) order.  It uses SETUP packets
        with the special type (0x43) as an `attention` word.  This is then followed by an ``OUT`` packet.

            .. wavedrom::
                :caption: Write to Wishbone

                { "signal": [
                    ["Request",
                        {  "name": 'data',        "wave": 'x222...22x', "data": '0x43 0x00 [ADDRESS] 0x04 0x00'   },
                        {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
                        {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
                    ],
                    {},
                    ["Payload",
                        {  "name": 'data',        "wave": 'x3...x', "data": '[DATA]'},
                        {  "name": 'data bits',   "wave": 'x3333x', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x3...x', "data": 'OUT'  },
                        {  "name": 'usb byte',    "wave": 'x3333x', "data": '1 2 3 4'}
                    ]
                ]}

        To read data from the device, set the top bit of the `bRequestType`, followed by an ``IN`` packet.

            .. wavedrom::
                :caption: Read from Wishbone

                { "signal": [
                    ['Request',
                        {  "name": 'data',        "wave": 'x222...22x', "data": '0xC3 0x00 [ADDRESS] 0x04 0x00'   },
                        {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
                        {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
                    ],
                    {},
                    ["Payload",
                        {  "name": 'data',        "wave": 'x5...x', "data": '[DATA]'},
                        {  "name": 'data bits',   "wave": 'x5555x', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x5...x', "data": 'IN'  },
                        {  "name": 'usb byte',    "wave": 'x5555x', "data": '1 2 3 4'}
                    ]
                ]}
        """

        byte_counter = Signal(3, reset_less=True)
        byte_counter_reset = Signal()
        byte_counter_ce = Signal()
        self.sync.usb_12 += If(byte_counter_reset, byte_counter.eq(0)).Elif(byte_counter_ce, byte_counter.eq(byte_counter + 1))

        # Unlike the UART or Ethernet bridges, we explicitly only support two commands: reading and writing.
        # This gets integrated into the USB protocol, so it's not really a state.  1 is "USB Device to Host",
        # and is therefore a "read", while 0 is "USB Host to Device", and is therefore a "write".
        cmd = Signal(1, reset_less=True)
        cmd_ce = Signal()

        # Add a bridge to allow this module (in the usb_12 domain) to access the main Wishbone bridge (potentially in some other domain).
        # Ensure this bridge is placed in the "sys" domain.
        send_to_wishbone = Signal()
        reply_from_wishbone = Signal()
        transfer_active = Signal()
        if cdc:
            self.submodules.wb_cd_bridge = wb_cd_bridge = FSM(reset_state="IDLE")
            self.submodules.usb_to_wb = usb_to_wb = PulseSynchronizer("usb_12", "sys")
            self.submodules.wb_to_uwb = wb_to_usb = PulseSynchronizer("sys", "usb_12")
            send_to_wishbone = usb_to_wb.i
            reply_from_wishbone = wb_to_usb.o
        else:
            self.comb += [
                If(send_to_wishbone | transfer_active, self.wishbone.stb.eq(1), self.wishbone.we.eq(~cmd), self.wishbone.cyc.eq(1), ),
                reply_from_wishbone.eq(self.wishbone.ack | self.wishbone.err),
            ]

        # Instead of self.source and self.sink, we let the wrapping module handle packing and unpacking the data.
        self.sink_data = Signal(8)

        # True when the "sink" value has data
        self.sink_valid = Signal()

        self.send_ack = Signal()

        # Indicates whether a "debug" packet is currently being processed
        self.n_debug_in_progress = Signal(reset=1)

        address = Signal(32, reset_less=True)
        address_ce = Signal()

        data = Signal(32, reset_less=True)
        rd_data = Signal(32, reset_less=True)
        rx_data_ce = Signal()

        # wishbone_response = Signal(32, reset_less=True)
        self.sync.usb_12 += [
            If(cmd_ce, cmd.eq(usb_core.data_recv_payload[7:8])),
            If(address_ce, address.eq(Cat(address[8:32], usb_core.data_recv_payload))),
            If(rx_data_ce, data.eq(Cat(data[8:32], usb_core.data_recv_payload)))
        ]

        # The Litex Wishbone `dat_r` line is a shared medium, meaning the value changes often.
        # Capture our own copy of this data when a wishbone ACK occurs.
        self.sync.sys += [ If(self.wishbone.ack, rd_data.eq(self.wishbone.dat_r)) ]

        fsm = ResetInserter()(ClockDomainsRenamer("usb_12")(FSM(reset_state="IDLE")))
        self.submodules += fsm
        fsm.act("IDLE",
            self.n_debug_in_progress.eq(1),
            If(usb_core.data_recv_put,
                If(usb_core.tok == PID.SETUP,
                    If(usb_core.endp == 0,
                        # If we get a SETUP packet with a "Vendor" type going to this device, treat that as a DEBUG packet.
                        cmd_ce.eq(1),
                        byte_counter_reset.eq(1),
                        If(usb_core.data_recv_payload[0:7] == magic_packet,
                            NextState("RECEIVE_ADDRESS"),
                        ).Else(
                            # Wait for the end of the packet, to avoid messing with normal USB operation
                            NextState("WAIT_PKT_END"),
                        ),
                    )
                )
            )
        )

        # The target address comes as the wValue and wIndex in the SETUP packet.  Once we get that data, we're ready to do the operation.
        fsm.act("RECEIVE_ADDRESS",
            self.n_debug_in_progress.eq(0),
            If(usb_core.data_recv_put,
                byte_counter_ce.eq(1),
                If((byte_counter >= 1),
                    If((byte_counter <= 4),
                        address_ce.eq(1),
                    ),
                ),
            ),
            # We don't need to explicitly ACK the SETUP packet, because they're always acknowledged implicitly.
            # Wait until the packet ends (i.e. until we've sent the ACK packet) before moving to the next state.
            If(usb_core.end,
                byte_counter_reset.eq(1),
                If(cmd,
                    send_to_wishbone.eq(1),
                    NextState("READ_DATA"),
                ).Else(
                    NextState("RECEIVE_DATA"),
                ),
            ),
        )

        fsm.act("RECEIVE_DATA",
            # Set the "ACK" bit to 1, so we acknowledge the packet once it comes in, and so that we're in a position to receive data.
            self.send_ack.eq(usb_core.endp == 0),
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp == 0,
                If(usb_core.data_recv_put,
                    rx_data_ce.eq(1),
                    byte_counter_ce.eq(1),
                    If(byte_counter == 3,
                        NextState("WAIT_RECEIVE_DATA_END"),
                    ).Elif(usb_core.end,
                        send_to_wishbone.eq(1),
                        NextState("WRITE_DATA"),
                    )
                )
            )
        )

        fsm.act("WAIT_RECEIVE_DATA_END",
            self.n_debug_in_progress.eq(0),
            self.send_ack.eq(1),
            # Wait for the end of the USB packet, if it hasn't come already.
            If(usb_core.end,
                send_to_wishbone.eq(1),
                NextState("WRITE_DATA")
            )
        )

        if cdc:
            wb_cd_bridge.act("IDLE", If(usb_to_wb.o, NextState("DO_OP"), ), )
            wb_cd_bridge.act("DO_OP",
                self.wishbone.stb.eq(1),
                self.wishbone.we.eq(~cmd),
                self.wishbone.cyc.eq(1),
                If(self.wishbone.ack | self.wishbone.err,
                    NextState("IDLE"),
                    wb_to_usb.i.eq(1),
                ),
            )

        self.comb += [
            # Trim off the last two bits of the address, because wishbone addresses are word-based, and a word is 32-bits.
            # Therefore, the last two bits should always be zero.
            self.wishbone.adr.eq(address[2:]),
            self.wishbone.dat_w.eq(data),
            self.wishbone.sel.eq(2**len(self.wishbone.sel) - 1)
        ]

        fsm.act("WRITE_DATA",
            self.n_debug_in_progress.eq(0),
            transfer_active.eq(1),
            If(reply_from_wishbone,
                NextState("WAIT_SEND_ACK_START"),
            )
        )

        fsm.act("READ_DATA",
            self.n_debug_in_progress.eq(0),
            transfer_active.eq(1),
            If(reply_from_wishbone,
                NextState("SEND_DATA_WAIT_START")
            )
        )

        fsm.act("SEND_DATA_WAIT_START",
            self.n_debug_in_progress.eq(0),
            byte_counter_reset.eq(1),
            If(usb_core.start,
                NextState("SEND_DATA"),
            ),
        )

        self.comb += chooser(rd_data, byte_counter, self.sink_data, n=4, reverse=False)

        fsm.act("SEND_DATA",
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp != 0,
                NextState("SEND_DATA_WAIT_START"),
            ),

            # Keep sink_valid high during the packet, which indicates we have data to send.
            # This also causes an "ACK" to be transmitted.
            self.sink_valid.eq(usb_core.endp == 0),
            If(usb_core.data_send_get, byte_counter_ce.eq(1), ),
            If(byte_counter == 4,
                NextState("WAIT_SEND_ACK_START")
            ),
            If(usb_core.end,
                NextState("WAIT_SEND_ACK_START")
            )
        )

        # To validate the transaction was successful, the host will now send an "IN" request.
        # Acknowledge that by setting self.send_ack, without putting anything in self.sink_data.
        fsm.act("WAIT_SEND_ACK_START",
            self.n_debug_in_progress.eq(0),
            If(usb_core.start,
                NextState("SEND_ACK")
            ),
        )

        # Send the ACK.  If the endpoint number is incorrect, go back and wait again.
        fsm.act("SEND_ACK",
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp != 0,
                NextState("WAIT_SEND_ACK_START")
            ),
            # If(usb_core.retry,
            #     If(cmd,
            #         byte_counter_reset.eq(1),
            #         NextState("SEND_DATA"),
            #     ),
            # ),
            self.send_ack.eq(usb_core.endp == 0),
            If(usb_core.end,
                NextState("IDLE"),
            )
        )

        fsm.act("WAIT_PKT_END",
            self.n_debug_in_progress.eq(1),
            If(usb_core.end,
                NextState("IDLE"),
            )
        )

"""
Register Interface:

pullup_out_read: Read the status of the USB "FS" pullup.
pullup_out_write: Write the USB "FS" pullup state

SETUP - Responding to a SETUP packet from the host
setup_read: Read the contents of the last SETUP transaction
setup_ack: Write a "1" here to advance the data_read fifo
setup_empty: "0" if there is no SETUP data.
setup_epno: The endpoint the SETUP packet was destined for

EPOUT - Data from the host to this device
epout_data_read: Read the contents of the last transaction on the EP0
epout_data_ack: Write a "1" here to advance the data_read fifo
epout_last_tok: Bits 2 and 3 of the last token, from the following table:
   USB_PID_OUT   = 0
   USB_PID_SOF   = 1
   USB_PID_IN    = 2
   USB_PID_SETUP = 3
epout_epno: Which endpoint contained the last data
epout_queued: A response is queued and has yet to be acknowledged by the host

EPIN - Requests from the host to read data from this device
epin_data_write: Write 8 bits to the EP0 queue
epin_data_empty: Return 1 if the queue is empty
epin_epno: Which endpoint the data is for.  You must write this byte to indicate data is ready to be sent.
epin_queued: A response is queued and has yet to be acknowledged by the host

ep_stall: a 32-bit field representing endpoitns to respond with STALL.
"""

class TriEndpointInterface(Module, AutoCSR):
    """Implements a CPU interface with three FIFOs:
        * SETUP
        * IN
        * OUT

    Each of the three FIFOs has a relatively similar register set.

    Args
    ----

    iobuf (:obj:`io.IoBuf`): PHY interface to the raw pins.  This object
        encapsulate the pin interface to the outside world so that
        `TriEndpointInterface` does not need to have platform-specific
        IO handling.

    debug (bool, optional): Whether to add a debug bridge to this interface.
        Adding a debug bridge generates a Wishbone Master, which can take
        a large number of resources.  In exchange, it offers transparent debug.

    cdc (bool, optional): By default, ``eptri`` assumes that the CSR bus is in
        the same 12 MHz clock domain as the USB stack.  If ``cdc`` is set to
        True, then additional buffers will be placed on the ``.we`` and ``.re``
        lines to handle this difference.

    Attributes
    ----------

    debug_bridge (:obj:`wishbone.Interface`): The wishbone interface master for debug
        If `debug=True`, this attribute will contain the Wishbone Interface
        master for you to connect to your desired Wishbone bus.
    """

    def __init__(self, iobuf, debug=False, cdc=False):

        """USB Device Tri-FIFO

        This is a three-FIFO USB device.  It presents one FIFO each for ``IN``, ``OUT``,
        and ``SETUP`` data.  This allows for up to 16 ``IN`` and 16 ``OUT`` endpoints
        without sacrificing many FPGA resources.

        USB supports four types of transfers: control, bulk, interrupt, and isochronous.
        This device does not yet support isochronous transfers, however it supports the
        other types of transfers.
        """

        """Interrupt and Bulk Transfers

        Interrupt and bulk transfers are similar from an implementation standpoint --
        they differ only in terms of how often they are transmitted.

        These transfers can be made to any endpoint, and may even be interleaved.  However,
        due to the nature of ``TriEndpointInterface`` any attempt by the host to interleave
        transfers will result in a ``NAK``, and the host will retry later when the buffer
        is empty.

        IN Transfers
        ^^^^^^^^^^^^

        To make an ``IN`` transfer (i.e. to send data to the host), write the data to
        ``IN_DATA``.  This is a FIFO, and each write to this endpoint will advance the
        FIFO pointer automatically.  This FIFO is 64 bytes deep.  USB ``DATA`` packets
        contain a CRC16 checksum, which is automatically added to any ``IN`` transfers.

        ``TriEndpointInterface`` will continue to respond ``NAK`` until you arm the buffer.
        Do this by writing the endpoint number to ``IN_CTRL.EPNO``.  This will tell the device
        that it should send the data the next time the host asks for it.

        Once the data has been transferred, the device will raise an interrupt and you
        can begin re-filling the buffer, or fill it with data for a different endpoint.

        To send an empty packet, avoid writing any data to ``IN_DATA`` and simply write
        the endpoint number to ``IN_CTRL.EPNO``.

        The CRC16 will be automatically appended to the end of the transfer.

        OUT Transfers
        ^^^^^^^^^^^^^

        To respond to an ``OUT`` transfer (i.e. to receive data from the host), enable
        a particular endpoint by writing to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.ENABLE``
        bit set.  This will tell the device to stop responding ``NAK`` to that particular
        endpoint and to accept any incoming data into a 66-byte FIFO, provided the FIFO
        is empty.

        Once the host sends data, an interrupt will be raised and that particular endpoint's
        ``ENABLE`` will be set to ``0``.  This prevents any additional data from entering
        the FIFO while the device examines the data.

        The FIFO will contain two extra bytes, which are the two-byte CRC16 of the packet.
        You can safely discard these bytes.  Because of this, a zero-byte transfer will
        be two-bytes, and a full 64-byte transfer will be 66 bytes.

        To determine which endpoint the ``OUT`` packet was sent to, refer to
        ``OUT_STATUS.EPNO``.  This field is only updated when a successful packet is received,
        and will not change until the ``OUT`` FIFO is re-armed.

        The ``OUT`` FIFO will continue to respond to the host with with ``NAK`` until the
        ``OUT_EV_PENDING.DONE`` bit is cleared.

        Additionally, to continue receiving data on that particular endpoint, you will need
        to re-enable it by writing the endpoint number, along with the ``OUT_CTRL.ENABLE``
        to ``OUT_CTRL``.
        """

        """Control Transfers

        Control transfers are complicated, and are the first sort of transfer that
        the host uses.  Such transfers have three distinct phases.

        The first phase is the ``SETUP`` phase, where the host sends an 8-byte ``SETUP``
        packet.  These ``SETUP`` packets must always be acknowledged, so any such packet
        from the host will get loaded into the ``SETUP`` FIFO immediately, and an interrupt
        event raised.  If, for some reason, the device hasn't drained this ``SETUP``
        FIFO from a previous transaction, the FIFO will be cleared automatically.

        Once the ``SETUP`` packet is handled, the host will send an ``IN`` or ``OUT``
        packet.  If the host sends an ``OUT`` packet, then the ``OUT`` buffer must be
        cleared, the ``OUT.DONE`` interrupt handled, and the ``OUT_CTRL.ENABLE`` bit
        must be set for the appropriate endpoint, usually EP0.  The device will not
        accept any data as long as these three conditions are not met.

        If the host sends an ``IN`` packet, the device will respond with ``NAK`` if
        no data has queued.  To queue data, fill the ``IN_DATA`` buffer, then write
        ``0`` to ``IN_CTRL``.

        You can continue to fill the buffer (for ``IN`` packets) or drain the buffer
        and re-enable the endpoint (for ``OUT`` packets) until the host has finished
        the transfer.

        When the host has finished, it will send the opposite packet type.  If it
        is making ``IN`` transfers, it will send a single ``OUT`` packet, or if it
        is making ``OUT`` transfers it will send a single ``IN`` packet.
        You must handle this transaction yourself.

        Stalling an Endpoint
        ^^^^^^^^^^^^^^^^^^^^

        When the host sends a request that cannot be processed -- for example requesting
        a descriptor that does not exist -- the device must respond with ``STALL``.

        Each endpoint keeps track of its own ``STALL`` state, though a ``SETUP`` packet
        will clear the ``STALL`` state for the specified endpoint (usually EP0).

        To set or clear the ``STALL`` bit of an ``IN`` endpoint, write its endpoint number
        to ``IN_CTRL.EPNO`` with the ``IN_CTRL.STALL`` bit either set or clear.  If
        this bit is set, then the device will respond to the next ``IN`` packet from the
        host to that particular endpoint with ``STALL``.  If the bit is clear, then
        the next ``IN`` packet will be responded to with ``ACK`` and the contents of
        the ``IN`` FIFO.

        To stall an ``OUT`` endpoint, write to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.STALL``
        bit set.  To unstall, write to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.STALL`` bit
        cleared.  Note that ``OUT_CTRL.ENABLE`` should not be set at the same time as
        ``OUT_CTRL.STALL``, as this will cause a conflict.
        """

        # USB Core
        self.submodules.usb_core = usb_core = UsbTransfer(iobuf)

        self.submodules.pullup = GPIOOut(usb_core.iobuf.usb_pullup)
        self.iobuf = usb_core.iobuf

        # Generate debug signals, in case debug is enabled.
        debug_packet_detected = Signal()

        # Wire up debug signals if required
        if debug:
            self.submodules.debug_bridge = debug_bridge = USBWishboneBridge(self.usb_core, cdc=cdc)
            self.comb += [
                debug_packet_detected.eq(~self.debug_bridge.n_debug_in_progress),
            ]

        ems = []

        # When the USB host sends a USB reset, set our address back to 0.
        self.address = ResetInserter()(CSRStorage("address",
            fields=[CSRField("addr", 7, description="Write the USB address from USB ``SET_ADDRESS`` packets.")],
            description="""
                Sets the USB device address, in order to ignore packets
                going to other devices on the bus. This value is reset when the host
                issues a USB Device Reset condition.
            """))
        self.comb += self.address.reset.eq(usb_core.usb_reset)

        self.next_ev = CSRStatus("next_ev",
            fields=[
                CSRField("in", 1, description="``1`` if the next event is an ``IN`` event"),
                CSRField("out", 1, description="``1`` if the next event is an ``OUT`` event"),
                CSRField("setup", 1, description="``1`` if the next event is an ``SETUP`` event"),
                CSRField("reset", 1, description="``1`` if the next event is a ``RESET`` event"),
            ],
            description="""
                In ``eptri``, there are three endpoints.  It is possible for an IRQ to fire
                and have all three bits set.  Under these circumstances it can be difficult
                to know which event to process first.  Use this register to determine which
                event needs to be processed first.
                Only one bit will ever be set at a time.
            """,
        )

        # Handlers
        self.submodules.setup = setup_handler = ClockDomainsRenamer("usb_12")(SetupHandler(usb_core))
        self.comb += setup_handler.usb_reset.eq(usb_core.usb_reset)
        ems.append(setup_handler.ev)

        in_handler = ClockDomainsRenamer("usb_12")(InHandler(usb_core))
        self.submodules.__setattr__("in", in_handler)
        ems.append(in_handler.ev)

        self.submodules.out = out_handler = ClockDomainsRenamer("usb_12")(OutHandler(usb_core))
        ems.append(out_handler.ev)

        self.submodules.ev = SharedIRQ(*ems)

        in_next = Signal()
        out_next = Signal()
        self.sync += [
            If(usb_core.usb_reset,
                in_next.eq(0),
                out_next.eq(0),
            # If the in_handler is set but not the out_handler, that one is next
            ).Elif(in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(1),
                out_next.eq(0),
            # If the out_handler is set first, mark that as `next`
            ).Elif(~in_handler.ev.packet.pending & out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(1),
            # If neither is set, then clear the bits.
            ).Elif(~in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(0),
            ),
            # If both are set, don't do anything.
        ]
        self.comb += [
            If(setup_handler.ev.reset.pending,
                self.next_ev.fields.reset.eq(1),
            ).Elif(in_next,
                getattr(self.next_ev.fields, "in").eq(1),
            ).Elif(out_next,
                self.next_ev.fields.out.eq(out_next),
            ).Elif(setup_handler.ev.packet.pending,
                self.next_ev.fields.setup.eq(1),
            )
        ]

        # If a debug packet comes in, the DTB should be 1.
        # Otherwise, the DTB should be whatever the in_handler says it is.
        self.comb += usb_core.dtb.eq(in_handler.dtb | debug_packet_detected)
        usb_core_reset = Signal()

        self.submodules.stage = stage = ClockDomainsRenamer("usb_12")(ResetInserter()(FSM(reset_state="IDLE")))
        self.comb += stage.reset.eq(usb_core.usb_reset)

        stage.act("IDLE",
            NextValue(usb_core.addr, self.address.storage),

            If(usb_core.start, NextState("CHECK_TOK"))
        )

        stage.act("CHECK_TOK",
            If(usb_core.idle,
                NextState("IDLE"),
            ).Elif(usb_core.tok == PID.SETUP,
                NextState("SETUP"),
                setup_handler.begin.eq(1),
                in_handler.dtb_reset.eq(1),
                # SETUP packets must be ACKed unconditionally
                usb_core.sta.eq(0),
                usb_core.arm.eq(1),
            ).Elif(usb_core.tok == PID.IN,
                NextState("IN"),
                usb_core.sta.eq(in_handler.stalled),
                usb_core.arm.eq(in_handler.response),
            ).Elif(usb_core.tok == PID.OUT,
                NextState("OUT"),
                usb_core.sta.eq(out_handler.stalled),
                usb_core.arm.eq(out_handler.response),
            ).Else(
                NextState("IDLE"),
            )
        )

        if debug:
            stage.act("DEBUG",
                usb_core.data_send_payload.eq(self.debug_bridge.sink_data),
                usb_core.data_send_have.eq(self.debug_bridge.sink_valid),
                usb_core.sta.eq(0),
                If(usb_core.endp == 0, usb_core.arm.eq(self.debug_bridge.send_ack | self.debug_bridge.sink_valid),).Else( usb_core.arm.eq(0)),
                If(~debug_packet_detected,
                    NextState("IDLE")
                )
            )
        else:
            stage.act("DEBUG", NextState("IDLE"))

        stage.act("SETUP",
            # SETUP packet
            setup_handler.data_recv_payload.eq(usb_core.data_recv_payload),
            setup_handler.data_recv_put.eq(usb_core.data_recv_put),

            # We aren't allowed to STALL a SETUP packet
            usb_core.sta.eq(0),

            # Always ACK a SETUP packet
            usb_core.arm.eq(1),

            If(debug_packet_detected, NextState("DEBUG")),
            If(usb_core.end, NextState("IDLE"), ),
        )

        stage.act("IN",
            If(usb_core.tok == PID.IN,
                # IN packet (device-to-host)
                usb_core.data_send_have.eq(in_handler.data_out_have),
                usb_core.data_send_payload.eq(in_handler.data_out),
                in_handler.data_out_advance.eq(usb_core.data_send_get),

                usb_core.sta.eq(in_handler.stalled),
                usb_core.arm.eq(in_handler.response),

                # After an IN transfer, the host sends an OUT packet.  We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE"), ),
            ),
        )

        stage.act("OUT",
            If(usb_core.tok == PID.OUT,
                # OUT packet (host-to-device)
                out_handler.data_recv_payload.eq(usb_core.data_recv_payload),
                out_handler.data_recv_put.eq(usb_core.data_recv_put),

                usb_core.sta.eq(out_handler.stalled),
                usb_core.arm.eq(out_handler.response),

                # After an OUT transfer, the host sends an IN packet.  We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE"), ),
            ),
        )

        self.comb += usb_core.reset.eq(usb_core.error | usb_core_reset)

class SetupHandler(Module, AutoCSR):
    """Handle ``SETUP`` packets

    ``SETUP`` packets must always respond with ``ACK``.  They are followed by a ``DATA0``
    packet, and may be followed by additional DATA stages.

    Since SETUP packets must always be handled, there is a separate FIFO that
    handles this data.  Hence the name `eptri`.

    The device must always acknowledge the ``SETUP`` packet right away, but need
    not send the acknowledgement stage right away.  You can use this to parse
    the data at a leisurely pace.

    When the device receives a ``SETUP`` transaction, an interrupt will fire
    and the ``SETUP_STATUS`` register will have ``SETUP_STATUS.HAVE`` set to ``1``.
    Drain the FIFO by reading from ``SETUP_DATA``, then setting
    ``SETUP_CTRL.ADVANCE``.

    Attributes
    ----------

    reset : Signal
        Asserting this resets the entire SetupHandler object.  You should do this at boot, or if
        you're switching applications.

    begin : Signal
        Assert this when a ``SETUP`` token is received.  This will clear out the current buffer
        (if any) and prepare the endpoint to receive data.

    epno : Signal(4)
        The endpoint number the SETUP packet came in on (probably is always ``0``)

    is_in : Signal
        This is a ``1`` if the ``SETUP`` packet will be followed by an ``IN`` stage.

    usb_reset : Signal
        This signal feeds into the EventManager, which is used to indicate to the device
        that a USB reset has occurred.

    """

    def __init__(self, usb_core):

        self.reset = Signal()
        self.begin = Signal()
        self.epno = epno = Signal()
        self.usb_reset = Signal()

        # Register Interface
        self.data = data = CSRStatus("data",
            fields=[CSRField("data", 8, description="The next byte of ``SETUP`` data")],
            description="Data from the last ``SETUP`` transactions.  It will be 10 bytes long, because it will include the CRC16.  This is a FIFO, and the queue is advanced automatically."
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[CSRField("reset", offset=5, description="Write a ``1`` here to reset the `SETUP` handler.", pulse=True), ],
            description="Controls for managing how to handle ``SETUP`` transactions."
        )

        self.status = status = CSRStatus("status",
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent SETUP token."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
                CSRField("is_in", description="``1`` if an IN stage was detected."),
                CSRField("data", description="``1`` if a DATA stage is expected."),
            ],
            description="Status about the most recent ``SETUP`` transactions, and the state of the FIFO."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="ready", description="Indicates a ``SETUP`` packet has arrived and is waiting in the ``SETUP`` FIFO.")
        self.ev.submodules.reset = EventSourceProcess(name="reset", description="Indicates a USB ``RESET`` condition has occurred, and the ``ADDRESS`` is now ``0``.")
        self.ev.finalize()
        self.trigger = trigger = self.ev.packet.trigger
        self.pending = pending = self.ev.packet.pending
        self.comb += self.ev.reset.trigger.eq(~self.usb_reset)

        self.data_recv_payload = data_recv_payload = Signal(8)
        self.data_recv_put = data_recv_put = Signal()

        # Since we must always ACK a SETUP packet, set this to 0.
        self.response = Signal()

        class SetupHandlerInner(Module):
            def __init__(self):
                self.submodules.data = buf = _SyncFIFOBuffered(width=8, depth=10)

                # Indicates which byte of `SETUP` data we're currently on.
                data_byte = Signal(4)

                # If the incoming `SETUP` token indicates there will be a DATA stage, this will be set to 1.
                self.have_data_stage = have_data_stage = Signal()

                # If the incoming `SETUP` token is an OUT packet, this will be 1.
                self.is_in = is_in = Signal()

                self.empty = Signal()
                self.comb += self.empty.eq(~buf.readable)

                # Wire up the `STATUS` register
                self.comb += [
                    status.fields.have.eq(buf.readable),
                    status.fields.is_in.eq(is_in),
                    status.fields.epno.eq(epno),
                    status.fields.pend.eq(pending),
                    status.fields.data.eq(have_data_stage),
                ]

                # Wire up the "SETUP" endpoint.
                self.comb += [
                    # Set the FIFO output to be the current buffer HEAD
                    data.fields.data.eq(buf.dout),

                    # Advance the FIFO when a byte is read
                    buf.re.eq(data.we),

                    If(usb_core.tok == PID.SETUP, buf.din.eq(data_recv_payload), buf.we.eq(data_recv_put), ),

                    # Tie the trigger to the STATUS.HAVE bit
                    trigger.eq(buf.readable & usb_core.setup),
                ]

                self.sync += [
                    # The 6th and 7th bytes of SETUP data are the wLength field.
                    # If these are nonzero, then there will be a Data stage following this Setup stage.
                    If(data_recv_put,
                        If(data_byte == 0,
                            epno.eq(usb_core.endp),
                            is_in.eq(data_recv_payload[7]),
                        ).Elif(data_byte == 6,
                            If(data_recv_payload,
                                have_data_stage.eq(1),
                            ),
                        ).Elif(data_byte == 7,
                            If(data_recv_payload,
                                have_data_stage.eq(1),
                            ),
                        ),
                        data_byte.eq(data_byte + 1),
                    )
                ]

        self.submodules.inner = inner = ResetInserter()(SetupHandlerInner())
        self.comb += [
            inner.reset.eq(self.reset | self.begin | ctrl.fields.reset),
            self.ev.packet.clear.eq(self.begin),
        ]

        # Expose relevant Inner signals to the top
        self.have_data_stage = inner.have_data_stage
        self.is_in = inner.is_in
        self.empty = inner.empty

class InHandler(Module, AutoCSR):
    """Endpoint for Device->Host transactions.

    When a host requests data from a device, it sends an ``IN`` token.  The device
    should then respond with ``DATA0`, ``DATA1``, or ``NAK``.  This handler is
    responsible for managing this response, as well as supplying the USB system
    with data.

    To send data, fill the FIFO by writing bytes to ``IN_DATA``.  When you're ready
    to transmit, write the destination endpoint number to ``IN_CTRL``.

    Attributes
    ----------

    """
    def __init__(self, usb_core):
        self.dtb = Signal()

        # Keep track of the current DTB for each of the 16 endpoints
        dtbs = Signal(16, reset=0x0001)

        # A list of endpoints that are stalled
        stall_status = Signal(16)

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=64))

        self.data = CSRStorage("data",
            fields=[CSRField("data", 8, description="The next byte to add to the queue."), ],
            description="""
                Each byte written into this register gets added to an outgoing FIFO.
                Any bytes that are written here will be transmitted in the order in which they were added.
                The FIFO queue is automatically advanced with each write.
                The FIFO queue is 64 bytes deep.
                If you exceed this amount, the result is undefined."""
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4, description="The endpoint number for the transaction that is queued in the FIFO."),
                CSRField("reset", offset=5, description="Write a ``1`` here to clear the contents of the FIFO.", pulse=True),
                CSRField("stall", description="Write a ``1`` here to stall the EP written in ``EP``.", pulse=True),
            ],
            description="Enables transmission of data in response to ``IN`` tokens, or resets the contents of the FIFO."
        )

        self.status = CSRStatus("status",
            fields=[
                CSRField("idle", description="This value is ``1`` if the packet has finished transmitting."),
                CSRField("have", offset=4, description="This value is ``0`` if the FIFO is empty."),
                CSRField("pend", offset=5, description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the IN handler.  As soon as you write to `IN_DATA`, ``IN_STATUS.HAVE`` should go to ``1``."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="done", description="Indicates that the host has successfully transferred an ``IN`` packet, and that the FIFO is now empty.")
        self.ev.finalize()

        # Control bits
        ep_stall_mask = Signal(16)
        self.comb += [
            ep_stall_mask.eq(1 << ctrl.fields.epno),
        ]

        # Keep track of which endpoints are currently stalled
        self.stalled = Signal()
        self.comb += self.stalled.eq(stall_status >> usb_core.endp)
        self.sync += [
            If(ctrl.fields.reset,
                stall_status.eq(0),
            ).Elif(usb_core.setup | (ctrl.re & ~ctrl.fields.stall),
                # If a SETUP packet comes in, clear the STALL bit.
                stall_status.eq(stall_status & ~ep_stall_mask),
            ).Elif(ctrl.re,
                stall_status.eq(stall_status | ep_stall_mask),
            ),
        ]

        # How to respond to requests:
        #  - 0 - ACK
        #  - 1 - NAK
        self.response = Signal()

        # This value goes "1" when data is pending, and returns to "0" when it's done.
        queued = Signal()
        was_queued = Signal()

        # This goes to "1" when "queued" is 1 when a "start" occurs.  It is used
        # to avoid skipping packets when a packet is queued during a transmission.
        transmitted = Signal()

        self.dtb_reset = Signal()
        self.comb += [
            buf.reset.eq(ctrl.fields.reset | (usb_core.commit & transmitted & queued)),
        ]

        # Outgoing data will be placed on this signal
        self.data_out = Signal(8)

        # This is "1" if `data_out` contains data
        self.data_out_have = Signal()

        # Pulse this to advance the data output
        self.data_out_advance = Signal()

        # Used to detect when an IN packet finished
        is_our_packet = Signal()
        is_in_packet = Signal()

        self.comb += [
            # We will respond with "ACK" if the register matches the current endpoint number
            self.response.eq(queued & is_our_packet & is_in_packet),

            # Wire up the "status" register
            self.status.fields.have.eq(buf.readable),
            self.status.fields.idle.eq(~queued),
            self.status.fields.pend.eq(self.ev.packet.pending),

            # Cause a trigger event when the `queued` value goes to 0
            self.ev.packet.trigger.eq(~queued & was_queued),

            self.dtb.eq(dtbs >> usb_core.endp),

            self.data_out.eq(buf.dout),
            self.data_out_have.eq(buf.readable),
            buf.re.eq(self.data_out_advance & is_in_packet & is_our_packet),
            buf.we.eq(self.data.re),
            buf.din.eq(self.data.storage),
            is_our_packet.eq(usb_core.endp == ctrl.fields.epno),
            is_in_packet.eq(usb_core.tok == PID.IN),
        ]

        self.sync += [
            If(ctrl.fields.reset,
                queued.eq(0),
                was_queued.eq(0),
                transmitted.eq(0),
                dtbs.eq(0x0001),
            ).Elif(self.dtb_reset,
                dtbs.eq(dtbs | 1),
            )
            # When the user updates the `ctrl` register, enable writing.
            .Elif(ctrl.re & ~ctrl.fields.stall,
                queued.eq(1),
            )
            .Elif(usb_core.poll & self.response,
                transmitted.eq(1),
            )
            # When the USB core finishes operating on this packet, de-assert the queue flag
            .Elif(usb_core.commit & transmitted & self.response & ~self.stalled,
                queued.eq(0),
                transmitted.eq(0),
                # Toggle the "DTB" line if we transmitted data
                dtbs.eq(dtbs ^ (1 << ctrl.fields.epno)),
            ).Else(
                was_queued.eq(queued),
            ),
        ]

class OutHandler(Module, AutoCSR):
    """
    Endpoint for Host->Device transaction

    When a host wants to send data to a device, it sends an ``OUT`` token.  The device
    should then respond with ``ACK``, or ``NAK``.  This handler is responsible for managing
    this response, as well as reading data from the USB subsystem.

    To enable receiving data, write a ``1`` to the ``OUT_CTRL.ENABLE`` bit.

    To drain the FIFO, read from ``OUT.DATA``.  Don't forget to re-
    enable the FIFO by ensuring ``OUT_CTRL.ENABLE`` is set after advancing the FIFO!

    Attributes
    ----------

    """
    def __init__(self, usb_core):

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=66))

        self.data = data = CSRStatus("data",
            fields=[
                CSRField("data", 8, description="The top byte of the receive FIFO."),
            ],
            description="""
                Data received from the host will go into a FIFO.
                This register reflects the contents of the top byte in that FIFO.
                Reading from this register advances the FIFO pointer."""
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4, description="The endpoint number to update the ``enable`` and ``status`` bits for."),
                CSRField("enable", description="Write a ``1`` here to enable receiving data"),
                CSRField("reset", pulse=True, description="Write a ``1`` here to reset the ``OUT`` handler"),
                CSRField("stall", description="Write a ``1`` here to stall an endpoint"),
            ],
            description="""
                Controls for receiving packet data.  To enable an endpoint, write its value to ``epno``,
                with the ``enable`` bit set to ``1`` to enable an endpoint, or ``0`` to disable it.
                Resetting the OutHandler will set all ``enable`` bits to 0.

                Similarly, you can adjust the ``STALL`` state by setting or clearing the ``stall`` bit."""
        )

        self.status = CSRStatus("status",
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent ``OUT`` packet."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the current state of the `OUT` endpoint."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="done", description="""
            Indicates that an ``OUT`` packet has successfully been transferred from the host.  This bit must be cleared in order to receive additional packets.""")
        self.ev.finalize()

        self.usb_reset = Signal()

        self.stalled = Signal()
        self.enabled = Signal()
        stall_status = Signal(16)
        enable_status = Signal(16)
        ep_mask = Signal(16, reset=1)
        self.comb += [
            If(usb_core.setup | usb_core.commit,
                ep_mask.eq(1 << usb_core.endp),
            ).Else(
                ep_mask.eq(1 << ctrl.fields.epno),
            ),
            self.stalled.eq(stall_status >> usb_core.endp),
            self.enabled.eq(enable_status >> usb_core.endp),
        ]
        self.sync += [
            If(ctrl.fields.reset | self.usb_reset,
                stall_status.eq(0),
            ).Elif(usb_core.setup | (ctrl.re & ~ctrl.fields.stall),
                # If a SETUP packet comes in, clear the STALL bit.
                stall_status.eq(stall_status & ~ep_mask),
            ).Elif(ctrl.re,
                stall_status.eq(stall_status | ep_mask),
            ),
        ]

        # The endpoint number of the most recently received packet
        epno = Signal(4)

        # How to respond to requests:
        #  - 1 - ACK
        #  - 0 - NAK
        # Send a NAK if the buffer contains data, or if "ENABLE" has not been set.
        self.response = Signal()
        responding = Signal()
        is_out_packet = Signal()

        # Keep track of whether we're currently responding.
        self.comb += is_out_packet.eq(usb_core.tok == PID.OUT)
        self.comb += self.response.eq(self.enabled & is_out_packet & ~self.ev.packet.pending)
        self.sync += If(usb_core.poll, responding.eq(self.response))

        # Connect the buffer to the USB system
        self.data_recv_payload = Signal(8)
        self.data_recv_put = Signal()
        self.comb += [
            buf.din.eq(self.data_recv_payload),
            buf.we.eq(self.data_recv_put & responding),
            buf.reset.eq(ctrl.fields.reset),
            self.data.fields.data.eq(buf.dout),

            # When data is read, advance the FIFO
            buf.re.eq(data.we),

            self.status.fields.epno.eq(epno),
            self.status.fields.have.eq(buf.readable),
            self.status.fields.pend.eq(self.ev.packet.pending),

            # When data is successfully transferred, the buffer becomes full.
            # This is true even if "no" data was transferred, because the buffer will then contain two bytes of CRC16 data.
            # Therefore, if the FIFO is readable, an interrupt must be triggered.
            self.ev.packet.trigger.eq(responding & usb_core.commit),
        ]

        # If we get a packet, turn off the "IDLE" flag and keep it off until the packet has finished.
        self.sync += [
            If(ctrl.fields.reset,
                enable_status.eq(0),
            ).Elif(usb_core.commit & responding,
                epno.eq(usb_core.endp),
                # Disable this EP when a transfer finishes
                enable_status.eq(enable_status & ~ep_mask),
                responding.eq(0),
            ).Elif(ctrl.re,
                # Enable or disable the EP as necessary
                If(ctrl.fields.enable,
                    enable_status.eq(enable_status | ep_mask),
                ).Else(
                    enable_status.eq(enable_status & ~ep_mask),
                ),
            ),
        ]

# Hack the AutoCSR objects to enable access only via Module attributes.
class CSRTransform(ModuleTransformer):
    def __init__(self, parent):
        self.parent = parent

    def transform_instance(self, i):
        # Capture all the available CSRs, then burn the bridge.
        v = i.get_csrs()
        i.get_csrs = None

        for c in v:
            # Skip over modules already exposed, should handle potential renaming here.
            #if hasattr(i, c.name):
            #    pass

            # Attach csr as module attribute
            setattr(i, c.name,c)

            if isinstance(c, CSR):
                ...
            else:
                # Clear the finalise function so these aren't altered further.
                # Maybe not required?
                def _null(*kwargs):
                    ...
                c.finalize = _null

                # Attach these to our modules submodules, needed to ensure the objects are elaborated?
                self.parent.submodules += c

            # create extra bindings to support dev writing
            if isinstance(c, CSRStorage):
                # .re is used to determine when .storage has been updated.
                # so we need to create delayed re signal, we'll rename this to re0
                setattr(c, "re0", c.re)
                setattr(c.re0, "name", c.name + '_re0')

                # Our personal .re signal will then update .re0 alongside .storage
                setattr(c, "re", Signal(name=c.name + '_re'))
                c.sync += c.re0.eq(c.re)

                if hasattr(c, "fields"):
                    setattr(c, "dat_w", Record([]))
                    for a in c.fields.fields:
                        s = Signal(a.size,name=f'{c.name}_{a.name}0')

                        c.sync += If(c.re, c.storage[a.offset:a.offset + a.size].eq(s))
                        setattr(c.dat_w, a.name, s)
                else:
                    # if the CSRStorage doesn't have any fields, just provide .dat_w
                    setattr(c, "dat_w", Signal(c.size))
                    c.sync += If(c.re, c.storage.eq(c.dat_w))

class CDCUsb(Module, AutoCSR):
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug=False, vid=0x1209, pid=0x5bf2, product="OrangeCrab CDC", manufacturer="GsD"):

        self.submodules.phy = phy = ClockDomainsRenamer("usb_12")(CDCUsbPHY(iobuf, debug=debug, vid=vid, pid=pid, product=product, manufacturer=manufacturer))

        # create interface for UART
        self._rxtx = CSR("rxtx", 8)
        self._txfull = CSRStatus("txfull")
        self._rxempty = CSRStatus("rxempty")

        self.submodules.ev = EventManager()
        self.ev.tx = EventSourceProcess()
        self.ev.rx = EventSourceProcess()
        self.ev.finalize()

        self._tuning_word = CSRStorage("tuning_word", 32, reset=0)

        self._configured = CSR("configured")

        self.sink   = Endpoint([("data", 8)])
        self.source = Endpoint([("data", 8)])

        self.rts = Signal()
        self.dtr = Signal()

        self.async_rst = Signal()

        self.specials += MultiReg(phy.rts, self.rts)
        self.specials += MultiReg(phy.dtr, self.dtr)

        self.submodules.configure_pulse = PulseSynchronizer("sys", "usb_12")

        self.comb += [
                #phy.source.connect(self.source),
                #self.sink.connect(phy.sink),

                self.source.connect(phy.source),
                phy.sink.connect(self.sink),

                self.async_rst.eq(phy.dtr),

                self.configure_pulse.i.eq(self._configured.re),
                self.phy.configure_set.eq(self.configure_pulse.o),
            ]

        # TX
        tx_fifo = ClockDomainsRenamer({"write":"sys","read":"usb_12"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        #tx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False)))
        #tx_fifo = SyncFIFO([("data", 8)], 4, buffered=True)
        self.submodules += tx_fifo

        self.comb += [
            tx_fifo.sink.valid.eq(self._rxtx.re),
            tx_fifo.sink.data.eq(self._rxtx.r),
            self._txfull.status.eq(~tx_fifo.sink.ready),
            tx_fifo.source.connect(self.source),
            # Generate TX IRQ when tx_fifo becomes non-full
            self.ev.tx.trigger.eq(~tx_fifo.sink.ready)
        ]

        # RX
        rx_fifo = ClockDomainsRenamer({"write":"usb_12","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        #rx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False)))
        #rx_fifo = SyncFIFO([("data", 8)], 4, buffered=True)
        self.submodules += rx_fifo

        self.comb += [
            self.sink.connect(rx_fifo.sink),
            self._rxempty.status.eq(~rx_fifo.source.valid),
            self._rxtx.w.eq(rx_fifo.source.data),
            rx_fifo.source.ready.eq(self.ev.rx.clear | (False & self._rxtx.we)),
            # Generate RX IRQ when tx_fifo becomes non-empty
            self.ev.rx.trigger.eq(~rx_fifo.source.valid)
        ]

class CDCUsbPHY(Module):
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug, vid, pid, product, manufacturer):

        # Create the eptri USB interface
        usb = TriEndpointInterface(iobuf, debug=debug)
        #usb.finalize()
        self.submodules.eptri = usb = CSRTransform(self)(usb)

        self.sink   = Endpoint([("data", 8)])
        self.source = Endpoint([("data", 8)])

        self.rts = Signal()
        self.dtr = Signal()

        # Ato attach on power up
        self.comb += [
            usb.pullup_out.dat_w.eq(~ResetSignal()),
            usb.pullup_out.re.eq(1),
        ]

        def make_usbstr(s):
            usbstr = bytearray(2)
            # The first byte is the number of characters in the string.
            # Because strings are utf_16_le, each character is two-bytes.
            # That leaves 126 bytes as the maximum length
            assert(len(s) <= 126)
            usbstr[0] = (len(s)*2)+2
            usbstr[1] = 3
            usbstr.extend(bytes(s, 'utf_16_le'))
            return list(usbstr)

        # Start with 0x8006
        descriptors = {
            # Config descriptor
            # 80 06 00 02
            0x0002: [
                0x09, # bLength
                0x02, # bDescriptorType
                62, 0x00, # wTotalLength
                0x02, # bNumInterfaces
                0x01, # bConfigurationValue
                0x00, # iConfiguration
                0x80, # bmAttributes
                0x32, # bMaxPower

                # Interface descriptor
                0x09, # bLength
                0x04, # bDescriptorType
                0x00, # bInterfaceNumber
                0x00, # bAlternateSetting
                0x01, # bNumEndpoints
                0x02, # bInterfaceClass (2: Communications Interface)
                0x02, # bInterfaceSubClass (2: Abstract Control Model)
                0x00, # bInterfacePrototcol
                0x00, # iInterface

                # Header Functional Descriptor
                0x05, # bFunctionLength
                0x24, # bDescriptorType (24: CS_INTERFACE)
                0x00, # bDescriptorSubtype
                0x10, 0x01, # bcdCDC

                # ACM Functional Descriptor
                0x04, # bFunctionLength
                0x24, # bDescriptorType
                0x02, # bDescriptorSubtype
                0x02, # bmCapabilities

                # Union Functional Description
                0x05, # bLength
                0x24, # bDescriptorType
                0x06, # bDescriptorSubtype
                0x00, # bControlInterfoce
                0x01, # bSubordinateInterface0

                # Control Endpoint Descriptior
                0x07, # bLength
                0x05, # bDescriptorType (5: ENDPOINT)
                0x81, # bEndpointAddress
                0x03, # bmAttributes (XFER_INTERRUPT)
                0x08, 0x00, # wMaxPacketSize
                0x40, # bInterval

                0x09, # bLength            = sizeof(tusb_desc_interface_t),
                0x04, # bDescriptorType    = TUSB_DESC_TYPE_INTERFACE,
                0x01, # bInterfaceNumber   = 5,
                0x00, # bAlternateSetting  = 0x00,
                0x02, # bNumEndpoints      = 2,
                0x0A, # bInterfaceClass    = TUSB_CLASS_CDC_DATA,
                0x00, # bInterfaceSubClass = 0,
                0x00, # bInterfaceProtocol = 0,
                0x00, # iInterface         = 0x00

                0x07, # bLength          = sizeof(tusb_desc_endpoint_t),
                0x05, # bDescriptorType  = TUSB_DESC_TYPE_ENDPOINT,
                0x02, # bEndpointAddress = 5,
                0x02, # bmAttributes     = { .xfer = TUSB_XFER_BULK },
                0x40, 0x00, # wMaxPacketSize   = 64,
                0x00, # bInterval        = 0

                0x07, # bLength          = sizeof(tusb_desc_endpoint_t),
                0x05, # bDescriptorType  = TUSB_DESC_TYPE_ENDPOINT,
                0x82, # bEndpointAddress = 0x85,
                0x02, # bmAttributes     = { .xfer = TUSB_XFER_BULK },
                0x40, 0x00, # wMaxPacketSize   = 64,
                0x00, # bInterval        = 0
            ],

            # Device descriptor
            # 80 06 00 01
            0x0001: [
                0x12, # Length
                0x01, # bDescriptorType
                0x00, 0x02, # bcdUSB
                0x02, # bDeviceClass
                0x00, # bDeviceSubClass
                0x00, # bDeviceProtocol
                0x40, # bMaxPacketSize0
                (vid>>0)&0xff, (vid>>8)&0xff, # idVendor
                (pid>>0)&0xff, (pid>>8)&0xff, # idProduct
                0x01, 0x01, # bcdDevice
                0x01, # iManufacture
                0x02, # iProduct
                0x00, # iSerialNumber
                0x01, # bNumConfigurations
            ],

            # String 0
            0x0003: [
                0x04, 0x03, 0x09, 0x04,
            ],

            # String 1 (manufacturer)
            0x0103: make_usbstr(manufacturer),

            # String 2 (Product)
            0x0203: make_usbstr(product),

            # BOS descriptor
            0x000f: [
                0x05, 0x0f, 0x1d, 0x00, 0x01, 0x18, 0x10, 0x05,
                0x00, 0x38, 0xb6, 0x08, 0x34, 0xa9, 0x09, 0xa0,
                0x47, 0x8b, 0xfd, 0xa0, 0x76, 0x88, 0x15, 0xb6,
                0x65, 0x00, 0x01, 0x02, 0x01,
            ],

            0xee03: [
                0x12, 0x03, 0x4d, 0x53, 0x46, 0x54, 0x31, 0x30,
                0x30, 0x7e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00,
            ],
        }

        # Starts with 0xc07e or 0xc17e
        usb_ms_compat_id_descriptor = [
            0x28, 0x00, 0x00, 0x00, 0x00, 0x01, 0x04, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x01, 0x57, 0x49, 0x4e, 0x55, 0x53, 0x42,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]

        class MemoryContents:
            def __init__(self):
                self.contents = [0x00]
                self.offsets = {}
                self.lengths = {}

            def add(self, wRequestAndType, wValue, mem):
                self.offsets[wRequestAndType << 16 | wValue] = len(self.contents)
                self.lengths[wRequestAndType << 16 | wValue] = len(mem)
                self.contents = self.contents + mem

        mem = MemoryContents()
        for key, value in descriptors.items():
            mem.add(0x8006, key, value)

        mem.add(0xc07e, 0x0000, usb_ms_compat_id_descriptor)
        mem.add(0x8000, 0x0000, [0, 0]) # Get device status
        mem.add(0x0009, 0x0100, []) # Set configuration 1

        mem.add(0xA121, 0x0000, [0x00, 0xC2, 0x01, 0x00, 0x00, 0x00, 0x08]) # Get line_coding
        #mem.add(0xA120, 0x0000, [0x00,0x00]) # SerialState

        out_buffer = self.specials.out_buffer = Memory("out_buffer", 8, len(mem.contents), mem.contents)
        self.specials.out_buffer_rd = out_buffer_rd = out_buffer.get_port(write_capable=False, clock_domain="usb_12")
        self.autocsr_exclude = ['out_buffer']

        # Needs to be able to index Memory
        response_addr = Signal(9)
        response_len = Signal(6)
        response_ack = Signal()
        bytes_remaining = Signal(6)
        bytes_addr = Signal(9)

        new_address = Signal(7)

        configured = Signal()
        configured_delay = Signal(16, reset=2**16-1)

        self.configure_set = Signal()

        self.sync += [
            If(self.dtr & (configured_delay > 0),
                configured_delay.eq(configured_delay - 1)
            ).Elif(self.configure_set,
                configured_delay.eq(0)
            )
        ]
        self.comb += configured.eq(configured_delay == 0)

        # SETUP packets contain a DATA segment that is always 8 bytes.
        # However, we're only ever interested in the first 4 bytes, plus the last byte.
        usbPacket = Signal(32)
        wRequestAndType = Signal(16)
        wValue = Signal(16)
        wLength = Signal(8)
        self.comb += [
            wRequestAndType.eq(usbPacket[16:32]),
            wValue.eq(usbPacket[0:16]),
        ]
        setup_index = Signal(4)

        # Respond to various descriptor requests
        cases = {}
        for key in mem.offsets:
            cases[key] = [
                response_len.eq(mem.lengths[key]),
                response_addr.eq(mem.offsets[key]),
            ]
        self.comb += Case(usbPacket, cases)

        self.submodules.config = config = FSM(reset_state="IDLE")

        toggle = Signal()

        config.act("IDLE",
            #usb.address.dat_w.eq(new_address),
            usb.address.dat_w.addr.eq(new_address),
            usb.address.re.eq(1),

            usb.out_ctrl.dat_w.epno.eq(2),
            usb.out_ctrl.dat_w.enable.eq(1),
            usb.out_ctrl.re.eq(1),

            NextState("WAIT"),
        )

        config.act("WAIT",
            #usb.in_ctrl.dat_w.epno.eq(0),
            #usb.in_ctrl.re.eq(1),

            usb.out_ctrl.dat_w.epno.eq(0),
            usb.out_ctrl.dat_w.enable.eq(1),
            usb.out_ctrl.re.eq(1),

            If(usb.setup_status.fields.have,
                NextState("SETUP"),
                NextValue(setup_index, 0),
                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

            ),

            # Data RX?
            If(usb.out_ev_pending.w,
                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

                If((usb.out_status.fields.epno == 2) & usb.out_status.fields.pend,
                    NextState("DRAIN-RX")
                )
            ),

            # UART_FIFO data?
            If(self.source.valid & configured,
                NextState("FILL-TX"),
            )
        )

        delayed_re = Signal()
        config.act("FILL-TX",
            usb.in_data.dat_w.data.eq(self.source.data),

            usb.in_data.re.eq(delayed_re & self.source.valid),
            NextValue(delayed_re,0),

            self.source.ready.eq(delayed_re & self.source.valid),

            If(self.source.valid,
                NextValue(delayed_re,self.source.valid),
            ).Else(
                usb.in_ctrl.dat_w.epno.eq(2),
                usb.in_ctrl.re.eq(1),
                NextState("WAIT-TRANSACTION"),
            )
        )

        # OUT data always captures 2 extra bytes from CRC
        # Since we don't know in advance how long the transaction was we need to account for this now
        data_d1 = Signal(8)
        re_d1 = Signal()

        data_d2 = Signal(8)
        re_d2 = Signal()

        config.act("DRAIN-RX",
            self.sink.data.eq(data_d2),

            usb.out_data.we.eq(delayed_re & usb.out_status.fields.have & self.sink.ready),
            NextValue(delayed_re,0),

            self.sink.valid.eq(re_d2 & usb.out_status.fields.have & self.sink.ready),

            If(usb.out_status.fields.have,
                NextValue(delayed_re,usb.out_status.fields.have),

                If(self.sink.ready,
                    NextValue(data_d1, usb.out_data.fields.data),
                    NextValue(data_d2, data_d1),

                    NextValue(re_d1, delayed_re),
                    NextValue(re_d2, re_d1),
                )
            ).Else(
                    NextValue(data_d1, 0),
                    NextValue(data_d2, 0),

                    NextValue(re_d1, 0),
                    NextValue(re_d2, 0),
                    NextValue(delayed_re,0),

                    NextState("IDLE"),
            )
        )

        config.act("SETUP",
           # read out setup packets to determine what to do
           If(usb.setup_status.fields.have,
                NextValue(setup_index,setup_index + 1),
                Case(setup_index, {
                    0: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    1: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    2: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    3: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    # 4: wIndex.eq(data_recv_payload_delayed),
                    # 5: wIndex.eq(Cat(wIndex[0:8], data_recv_payload_delayed)),
                    6: NextValue(wLength,usb.setup_data.fields.data),
                    # 7: wLength.eq(Cat(wLength[0:8], data_recv_payload_delayed)),
                }),
                usb.setup_data.we.eq(1)
            ),

            # Determine which state next
            If(setup_index == 0xA,
                # Ack with a blank IN packet
                usb.in_ctrl.dat_w.epno.eq(0),
                usb.in_ctrl.re.eq(1),

                NextState("WAIT-TRANSACTION"),
                If(wRequestAndType == 0x0005,
                    # Set Address
                    NextValue(new_address,wValue[8:15]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif(wRequestAndType == 0x2122,
                    # Set Address
                    NextValue(self.rts,wValue[9]),
                    NextValue(self.dtr,wValue[8]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif((usb.setup_status.fields.is_in) & (response_len > 0),
                    NextState("SETUP-IN"),
                    If(response_len > wLength,
                        NextValue(bytes_remaining,wLength),
                    ).Else(
                        NextValue(bytes_remaining,response_len),
                    ),
                    NextValue(bytes_addr,response_addr),
                ),
            )
        )

        config.act("SETUP-IN",
            usb.in_data.dat_w.data.eq(out_buffer_rd.dat_r),

            usb.in_data.re.eq(delayed_re),
            NextValue(delayed_re,0),

            If(bytes_remaining,
                NextValue(delayed_re,1),
                NextValue(bytes_addr, bytes_addr + 1),
                NextValue(bytes_remaining, bytes_remaining - 1),
            ).Elif(usb.in_ev_pending.w,
                NextState("WAIT-TRANSACTION"),
            )
        ),

        config.act("WAIT-TRANSACTION",
            usb.out_data.we.eq(1),
            If(usb.in_ev_pending.w,
                usb.in_ev_pending.r.eq(1),
                usb.in_ev_pending.re.eq(1),

                NextState("IDLE"),
            )
        )

        config.act("WAIT-OUT",
            If(usb.in_ev_pending.w & usb.out_ev_pending.w,
                usb.in_ev_pending.r.eq(1),
                usb.in_ev_pending.re.eq(1),

                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

                NextState("IDLE"),
            )
        )

        self.comb += [ out_buffer_rd.adr.eq(bytes_addr), ]
