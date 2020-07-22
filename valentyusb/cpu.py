from migen import *
from migen.fhdl.decorators import ModuleTransformer

from migen.genlib.cdc import MultiReg, PulseSynchronizer
from migen.genlib.fifo import SyncFIFOBuffered
from migen.genlib.fsm import FSM, NextState
from migen.genlib.misc import chooser
from migen.genlib.record import Record

from litex.soc.cores.gpio import GPIOOut
from litex.soc.integration.doc import AutoDoc, ModuleDoc
from litex.soc.interconnect import stream, wishbone
from litex.soc.interconnect import csr_eventmanager as ev
from litex.soc.interconnect.csr import AutoCSR, CSR, CSRField, CSRStatus, CSRStorage
from litex.soc.interconnect.csr_eventmanager import *

from .pid import PID
from .sm import UsbTransfer

class USBWishboneBridge(Module, AutoDoc):

    def __init__(self, usb_core, clk_freq=12000000, magic_packet=0x43, cdc=False):
        self.wishbone = wishbone.Interface()

        self.background = ModuleDoc(title="USB Wishbone Bridge", body="""
            This bridge provides a transparent bridge to the target device's Wishbone bus over USB.
            It can operate without interfering with the device's USB stack.  It is simple enough to
            be able to work even if the USB stack is not enumerated, though the host may not cooperate.""")

        self.protocol = ModuleDoc(title="USB Wishbone Debug Protocol", body="""
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
        """)

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

class TriEndpointInterface(Module, AutoCSR, AutoDoc):
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

        self.background = ModuleDoc(title="USB Device Tri-FIFO", body="""
            This is a three-FIFO USB device.  It presents one FIFO each for ``IN``, ``OUT``,
            and ``SETUP`` data.  This allows for up to 16 ``IN`` and 16 ``OUT`` endpoints
            without sacrificing many FPGA resources.

            USB supports four types of transfers: control, bulk, interrupt, and isochronous.
            This device does not yet support isochronous transfers, however it supports the
            other types of transfers.
            """)

        self.interrupt_bulk_transfers = ModuleDoc(title="Interrupt and Bulk Transfers", body="""
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
            """)

        self.control_transfers = ModuleDoc(title="Control Transfers", body="""
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
            """)

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
        self.address = ResetInserter()(CSRStorage(
            name="address",
            fields=[CSRField("addr", 7, description="Write the USB address from USB ``SET_ADDRESS`` packets.")],
            description="""
                Sets the USB device address, in order to ignore packets
                going to other devices on the bus. This value is reset when the host
                issues a USB Device Reset condition.
            """))
        self.comb += self.address.reset.eq(usb_core.usb_reset)

        self.next_ev = CSRStatus(
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

        self.submodules.ev = ev.SharedIRQ(*ems)

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
        self.data = data = CSRStatus(
            fields=[CSRField("data", 8, description="The next byte of ``SETUP`` data")],
            description="Data from the last ``SETUP`` transactions.  It will be 10 bytes long, because it will include the CRC16.  This is a FIFO, and the queue is advanced automatically."
        )

        self.ctrl = ctrl = CSRStorage(
            fields=[CSRField("reset", offset=5, description="Write a ``1`` here to reset the `SETUP` handler.", pulse=True), ],
            description="Controls for managing how to handle ``SETUP`` transactions."
        )

        self.status = status = CSRStatus(
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent SETUP token."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
                CSRField("is_in", description="``1`` if an IN stage was detected."),
                CSRField("data", description="``1`` if a DATA stage is expected."),
            ],
            description="Status about the most recent ``SETUP`` transactions, and the state of the FIFO."
        )

        self.submodules.ev = ev.EventManager()
        self.ev.submodules.packet = ev.EventSourcePulse(name="ready", description="Indicates a ``SETUP`` packet has arrived and is waiting in the ``SETUP`` FIFO.")
        self.ev.submodules.reset = ev.EventSourceProcess(name="reset", description="Indicates a USB ``RESET`` condition has occurred, and the ``ADDRESS`` is now ``0``.")
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
                self.submodules.data = buf = SyncFIFOBuffered(width=8, depth=10)

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

        self.submodules.data_buf = buf = ResetInserter()(SyncFIFOBuffered(width=8, depth=64))

        self.data = CSRStorage(
            fields=[CSRField("data", 8, description="The next byte to add to the queue."), ],
            description="""
                Each byte written into this register gets added to an outgoing FIFO.
                Any bytes that are written here will be transmitted in the order in which they were added.
                The FIFO queue is automatically advanced with each write.
                The FIFO queue is 64 bytes deep.
                If you exceed this amount, the result is undefined."""
        )

        self.ctrl = ctrl = CSRStorage(
            fields=[
                CSRField("epno", 4, description="The endpoint number for the transaction that is queued in the FIFO."),
                CSRField("reset", offset=5, description="Write a ``1`` here to clear the contents of the FIFO.", pulse=True),
                CSRField("stall", description="Write a ``1`` here to stall the EP written in ``EP``.", pulse=True),
            ],
            description="Enables transmission of data in response to ``IN`` tokens, or resets the contents of the FIFO."
        )

        self.status = CSRStatus(
            fields=[
                CSRField("idle", description="This value is ``1`` if the packet has finished transmitting."),
                CSRField("have", offset=4, description="This value is ``0`` if the FIFO is empty."),
                CSRField("pend", offset=5, description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the IN handler.  As soon as you write to `IN_DATA`, ``IN_STATUS.HAVE`` should go to ``1``."
        )

        self.submodules.ev = ev.EventManager()
        self.ev.submodules.packet = ev.EventSourcePulse(name="done", description="Indicates that the host has successfully transferred an ``IN`` packet, and that the FIFO is now empty.")
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

        self.submodules.data_buf = buf = ResetInserter()(SyncFIFOBuffered(width=8, depth=66))

        self.data = data = CSRStatus(
            fields=[
                CSRField("data", 8, description="The top byte of the receive FIFO."),
            ],
            description="""
                Data received from the host will go into a FIFO.
                This register reflects the contents of the top byte in that FIFO.
                Reading from this register advances the FIFO pointer."""
        )

        self.ctrl = ctrl = CSRStorage(
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

        self.status = CSRStatus(
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent ``OUT`` packet."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the current state of the `OUT` endpoint."
        )

        self.submodules.ev = ev.EventManager()
        self.ev.submodules.packet = ev.EventSourcePulse(name="done", description="""
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
        # These are useful for debugging
        # self.enable_status = CSRStatus(8, description)
        # self.comb += self.enable_status.status.eq(enable_status)
        # self.stall_status = CSRStatus(8)
        # self.comb += self.stall_status.status.eq(stall_status)

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

class CDCUsb(Module, AutoDoc, ModuleDoc, AutoCSR):
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug=False, vid=0x1209, pid=0x5bf2, product="OrangeCrab CDC", manufacturer="GsD"):

        self.submodules.phy = phy = ClockDomainsRenamer("usb_12")(CDCUsbPHY(iobuf, debug=debug, vid=vid, pid=pid, product=product, manufacturer=manufacturer))

        # create interface for UART
        self._rxtx = CSR(8)
        self._txfull = CSRStatus()
        self._rxempty = CSRStatus()

        self.submodules.ev = EventManager()
        self.ev.tx = EventSourceProcess()
        self.ev.rx = EventSourceProcess()
        self.ev.finalize()

        self._tuning_word = CSRStorage(32, reset=0)

        self._configured = CSR()

        self.sink   = stream.Endpoint([("data", 8)])
        self.source = stream.Endpoint([("data", 8)])

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
        tx_fifo = ClockDomainsRenamer({"write":"sys","read":"usb_12"})(stream.AsyncFIFO([("data", 8)], 4, buffered=False))
        #tx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(stream.AsyncFIFO([("data", 8)], 4, buffered=False)))
        #tx_fifo = stream.SyncFIFO([("data", 8)], 4, buffered=True)
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
        rx_fifo = ClockDomainsRenamer({"write":"usb_12","read":"sys"})(stream.AsyncFIFO([("data", 8)], 4, buffered=False))
        #rx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(stream.AsyncFIFO([("data", 8)], 4, buffered=False)))
        #rx_fifo = stream.SyncFIFO([("data", 8)], 4, buffered=True)
        self.submodules += rx_fifo

        self.comb += [
            self.sink.connect(rx_fifo.sink),
            self._rxempty.status.eq(~rx_fifo.source.valid),
            self._rxtx.w.eq(rx_fifo.source.data),
            rx_fifo.source.ready.eq(self.ev.rx.clear | (False & self._rxtx.we)),
            # Generate RX IRQ when tx_fifo becomes non-empty
            self.ev.rx.trigger.eq(~rx_fifo.source.valid)
        ]

class CDCUsbPHY(Module, AutoDoc, ModuleDoc):
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug, vid, pid, product, manufacturer):

        # Create the eptri USB interface
        usb = TriEndpointInterface(iobuf, debug=debug)
        #usb.finalize()
        self.submodules.eptri = usb = CSRTransform(self)(usb)

        self.sink   = stream.Endpoint([("data", 8)])
        self.source = stream.Endpoint([("data", 8)])

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

        out_buffer = self.specials.out_buffer = Memory(8, len(mem.contents), init=mem.contents)
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
