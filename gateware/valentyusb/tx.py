import functools, operator

from eigen.fhdl.decorators import CEInserter, ClockDomainsRenamer, ResetInserter
from eigen.fhdl.module import Module
from eigen.fhdl.structure import If, Signal

from eigen.genlib.cdc import MultiReg
from eigen.genlib.fsm import FSM, NextState, NextValue

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
