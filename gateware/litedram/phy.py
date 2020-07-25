import math

from eigen.fhdl.module import Module
from eigen.fhdl.specials import Instance, Tristate
from eigen.fhdl.structure import Case, Cat, ClockSignal, If, log2_int, ResetSignal, Signal

from eigen.genlib.cdc import MultiReg
from eigen.genlib.misc import timeline
from eigen.genlib.record import DIR_M_TO_S, DIR_S_TO_M, Record

from gateware.csr import AutoCSR, CSR, CSRStatus, CSRStorage

from .common import BitSlip, get_cl_cw, get_sys_latency, get_sys_phases, PHYPadsCombiner, PhySettings

def phase_cmd_description(addressbits, bankbits, nranks):
    return [
        ("address", addressbits, DIR_M_TO_S),
        ("bank",       bankbits, DIR_M_TO_S),
        ("cas_n",             1, DIR_M_TO_S),
        ("cs_n",         nranks, DIR_M_TO_S),
        ("ras_n",             1, DIR_M_TO_S),
        ("we_n",              1, DIR_M_TO_S),
        ("cke",          nranks, DIR_M_TO_S),
        ("odt",          nranks, DIR_M_TO_S),
        ("reset_n",           1, DIR_M_TO_S),
        ("act_n",             1, DIR_M_TO_S)
    ]

def phase_wrdata_description(databits):
    return [
        ("wrdata",         databits, DIR_M_TO_S),
        ("wrdata_en",             1, DIR_M_TO_S),
        ("wrdata_mask", databits//8, DIR_M_TO_S)
    ]

def phase_rddata_description(databits):
    return [
        ("rddata_en",           1, DIR_M_TO_S),
        ("rddata",       databits, DIR_S_TO_M),
        ("rddata_valid",        1, DIR_S_TO_M)
    ]

def phase_description(addressbits, bankbits, nranks, databits):
    r = phase_cmd_description(addressbits, bankbits, nranks)
    r += phase_wrdata_description(databits)
    r += phase_rddata_description(databits)
    return r

class DFIInterface(Record):
    def __init__(self, addressbits, bankbits, nranks, databits, nphases=1):
        layout = [("p"+str(i), phase_description(addressbits, bankbits, nranks, databits)) for i in range(nphases)]
        Record.__init__(self, layout)
        self.phases = [getattr(self, "p"+str(i)) for i in range(nphases)]
        for p in self.phases:
            p.cas_n.reset = 1
            p.cs_n.reset = (2**nranks-1)
            p.ras_n.reset = 1
            p.we_n.reset = 1
            p.act_n.reset = 1

    # Returns pairs (DFI-mandated signal name, Eigen signal object)
    def get_standard_names(self, m2s=True, s2m=True):
        r = []
        add_suffix = len(self.phases) > 1
        for n, phase in enumerate(self.phases):
            for field, size, direction in phase.layout:
                if (m2s and direction == DIR_M_TO_S) or (s2m and direction == DIR_S_TO_M):
                    if add_suffix:
                        if direction == DIR_M_TO_S:
                            suffix = "_p" + str(n)
                        else:
                            suffix = "_w" + str(n)
                    else:
                        suffix = ""
                    r.append(("dfi_" + field + suffix, getattr(phase, field)))
        return r

class Interconnect(Module):
    def __init__(self, master, slave):
        self.comb += master.connect(slave)

# 1:2 frequency-ratio DDR3 PHY for Lattice's ECP5
# DDR3: 800 MT/s

class ECP5DDRPHYInit(Module):
    def __init__(self):
        self.pause = Signal()
        self.stop  = Signal()
        self.delay = Signal()
        self.reset = Signal()

        new_lock = Signal()
        update   = Signal()
        stop     = Signal()
        freeze   = Signal()
        pause    = Signal()
        reset    = Signal()

        # DDRDLLA instance
        _lock = Signal()
        delay = Signal()
        self.specials += Instance("DDRDLLA",
            i_RST      = ResetSignal("init"),
            i_CLK      = ClockSignal("sys2x"),
            i_UDDCNTLN = ~update,
            i_FREEZE   = freeze,
            o_DDRDEL   = delay,
            o_LOCK     = _lock
        )
        lock   = Signal()
        lock_d = Signal()
        self.specials += MultiReg(_lock, lock, "init")
        self.sync.init += lock_d.eq(lock)
        self.comb += new_lock.eq(lock & ~lock_d)

        # DDRDLLA/DDQBUFM/ECLK initialization sequence
        t = 8 # in cycles
        self.sync.init += [
            # Wait DDRDLLA Lock
            timeline(new_lock, [
                (1*t,  [freeze.eq(1)]), # Freeze DDRDLLA
                (2*t,  [stop.eq(1)]),   # Stop ECLK domain
                (3*t,  [reset.eq(1)]),  # Reset ECLK domain
                (4*t,  [reset.eq(0)]),  # Release ECLK domain reset
                (5*t,  [stop.eq(0)]),   # Release ECLK domain stop
                (6*t,  [freeze.eq(0)]), # Release DDRDLLA freeze
                (7*t,  [pause.eq(1)]),  # Pause DQSBUFM
                (8*t,  [update.eq(1)]), # Update DDRDLLA
                (9*t,  [update.eq(0)]), # Release DDRDMMA update
                (10*t, [pause.eq(0)]),  # Release DQSBUFM pause
            ])
        ]

        self.comb += [
            self.pause.eq(pause),
            self.stop.eq(stop),
            self.delay.eq(delay),
            self.reset.eq(reset),
        ]

class ECP5DDRPHY(Module, AutoCSR):
    def __init__(self, pads, sys_clk_freq=100e6):
        pads        = PHYPadsCombiner(pads)
        memtype     = "DDR3"
        tck         = 2/(2*2*sys_clk_freq)
        addressbits = len(pads.a)
        bankbits    = len(pads.ba)
        nranks      = 1 if not hasattr(pads, "cs_n") else len(pads.cs_n)
        databits    = len(pads.dq)
        nphases     = 2
        assert databits%8 == 0

        # Init
        self.submodules.init = ECP5DDRPHYInit()

        # Parameters
        cl, cwl         = get_cl_cw(memtype, tck)
        cl_sys_latency  = get_sys_latency(nphases, cl)
        cwl_sys_latency = get_sys_latency(nphases, cwl)

        # Registers
        self._dly_sel = CSRStorage(databits//8)

        self._rdly_dq_rst         = CSR()
        self._rdly_dq_inc         = CSR()
        self._rdly_dq_bitslip_rst = CSR()
        self._rdly_dq_bitslip     = CSR()

        self._burstdet_clr  = CSR()
        self._burstdet_seen = CSRStatus(databits//8)

        # Observation
        self.datavalid = Signal(databits//8)

        # PHY settings
        rdcmdphase, rdphase = get_sys_phases(nphases, cl_sys_latency, cl)
        wrcmdphase, wrphase = get_sys_phases(nphases, cwl_sys_latency, cwl)
        self.settings = PhySettings(
            phytype       = "ECP5DDRPHY",
            memtype       = memtype,
            databits      = databits,
            dfi_databits  = 4*databits,
            nranks        = nranks,
            nphases       = nphases,
            rdphase       = rdphase,
            wrphase       = wrphase,
            rdcmdphase    = rdcmdphase,
            wrcmdphase    = wrcmdphase,
            cl            = cl,
            cwl           = cwl,
            read_latency  = 2 + cl_sys_latency + 2 + log2_int(4//nphases) + 5,
            write_latency = cwl_sys_latency
        )

        # DFI Interface
        self.dfi = dfi = DFIInterface(addressbits, bankbits, nranks, 4*databits, 4)

        bl8_chunk = Signal()

        # Iterate on pads groups
        for pads_group in range(len(pads.groups)):
            pads.sel_group(pads_group)

            # Clock
            for i in range(len(pads.clk_p)):
                sd_clk_se = Signal()
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = 0,
                    i_D1   = 1,
                    i_D2   = 0,
                    i_D3   = 1,
                    o_Q    = pads.clk_p[i]
                )

            # Addresses and Commands
            for i in range(addressbits):
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = dfi.phases[0].address[i],
                    i_D1   = dfi.phases[0].address[i],
                    i_D2   = dfi.phases[1].address[i],
                    i_D3   = dfi.phases[1].address[i],
                    o_Q    = pads.a[i]
                )
            for i in range(bankbits):
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = dfi.phases[0].bank[i],
                    i_D1   = dfi.phases[0].bank[i],
                    i_D2   = dfi.phases[1].bank[i],
                    i_D3   = dfi.phases[1].bank[i],
                    o_Q    = pads.ba[i]
                )
            controls = ["ras_n", "cas_n", "we_n", "cke", "odt"]
            if hasattr(pads, "reset_n"):
                controls.append("reset_n")
            if hasattr(pads, "cs_n"):
                controls.append("cs_n")
            for name in controls:
                for i in range(len(getattr(pads, name))):
                    self.specials += Instance("ODDRX2F",
                        i_RST  = ResetSignal("sys"),
                        i_SCLK = ClockSignal("sys"),
                        i_ECLK = ClockSignal("sys2x"),
                        i_D0   = getattr(dfi.phases[0], name)[i],
                        i_D1   = getattr(dfi.phases[0], name)[i],
                        i_D2   = getattr(dfi.phases[1], name)[i],
                        i_D3   = getattr(dfi.phases[1], name)[i],
                        o_Q    = getattr(pads, name)[i]
                    )

        # DQ
        dq_oe         = Signal()
        dqs_re        = Signal()
        dqs_oe        = Signal()
        dqs_postamble = Signal()
        dqs_preamble  = Signal()
        for i in range(databits//8):
            # DQSBUFM
            dqs_i   = Signal()
            dqsr90  = Signal()
            dqsw270 = Signal()
            dqsw    = Signal()
            rdpntr  = Signal(3)
            wrpntr  = Signal(3)
            rdly    = Signal(7)
            burstdet  = Signal()
            self.sync += [
                If(self._dly_sel.storage[i] & self._rdly_dq_rst.re, rdly.eq(0)),
                If(self._dly_sel.storage[i] & self._rdly_dq_inc.re, rdly.eq(rdly + 1))
            ]
            self.specials += Instance("DQSBUFM",
                p_DQS_LI_DEL_ADJ = "MINUS",
                p_DQS_LI_DEL_VAL = 1,
                p_DQS_LO_DEL_ADJ = "MINUS",
                p_DQS_LO_DEL_VAL = 4,
                # Clocks / Reset
                i_RST            = ResetSignal("sys"),
                i_SCLK           = ClockSignal("sys"),
                i_ECLK           = ClockSignal("sys2x"),
                i_DDRDEL         = self.init.delay,
                i_PAUSE          = self.init.pause | self._dly_sel.storage[i],

                # Control
                # Assert LOADNs to use DDRDEL control
                i_RDLOADN        = 0,
                i_RDMOVE         = 0,
                i_RDDIRECTION    = 1,
                i_WRLOADN        = 0,
                i_WRMOVE         = 0,
                i_WRDIRECTION    = 1,

                # Reads (generate shifted DQS clock for reads)
                i_READ0          = dqs_re,
                i_READ1          = dqs_re,
                i_READCLKSEL0    = rdly[0],
                i_READCLKSEL1    = rdly[1],
                i_READCLKSEL2    = rdly[2],
                i_DQSI           = dqs_i,
                o_DQSR90         = dqsr90,
                o_RDPNTR0        = rdpntr[0],
                o_RDPNTR1        = rdpntr[1],
                o_RDPNTR2        = rdpntr[2],
                o_WRPNTR0        = wrpntr[0],
                o_WRPNTR1        = wrpntr[1],
                o_WRPNTR2        = wrpntr[2],
                o_DATAVALID      = self.datavalid[i],
                o_BURSTDET       = burstdet,

                # Writes (generate shifted ECLK clock for writes)
                o_DQSW270        = dqsw270,
                o_DQSW           = dqsw
            )
            burstdet_d = Signal()
            self.sync += [
                burstdet_d.eq(burstdet),
                If(self._burstdet_clr.re,  self._burstdet_seen.status[i].eq(0)),
                If(burstdet & ~burstdet_d, self._burstdet_seen.status[i].eq(1)),
            ]

            # DQS and DM
            dm_o_data       = Signal(8)
            dm_o_data_d     = Signal(8)
            dm_o_data_muxed = Signal(4)
            self.comb += dm_o_data.eq(Cat(
                dfi.phases[0].wrdata_mask[0*databits//8+i],
                dfi.phases[0].wrdata_mask[1*databits//8+i],
                dfi.phases[0].wrdata_mask[2*databits//8+i],
                dfi.phases[0].wrdata_mask[3*databits//8+i],

                dfi.phases[1].wrdata_mask[0*databits//8+i],
                dfi.phases[1].wrdata_mask[1*databits//8+i],
                dfi.phases[1].wrdata_mask[2*databits//8+i],
                dfi.phases[1].wrdata_mask[3*databits//8+i]),
            )
            self.sync += dm_o_data_d.eq(dm_o_data)
            dm_bl8_cases = {}
            dm_bl8_cases[0] = dm_o_data_muxed.eq(dm_o_data[:4])
            dm_bl8_cases[1] = dm_o_data_muxed.eq(dm_o_data_d[4:])
            self.sync += Case(bl8_chunk, dm_bl8_cases)
            self.specials += Instance("ODDRX2DQA",
                i_RST     = ResetSignal("sys"),
                i_SCLK    = ClockSignal("sys"),
                i_ECLK    = ClockSignal("sys2x"),
                i_DQSW270 = dqsw270,
                i_D0      = dm_o_data_muxed[0],
                i_D1      = dm_o_data_muxed[1],
                i_D2      = dm_o_data_muxed[2],
                i_D3      = dm_o_data_muxed[3],
                o_Q       = pads.dm[i]
            )

            dqs      = Signal()
            dqs_oe_n = Signal()
            self.specials += [
                Instance("ODDRX2DQSB",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_DQSW = dqsw,
                    i_D0   = 0,
                    i_D1   = 1,
                    i_D2   = 0,
                    i_D3   = 1,
                    o_Q    = dqs
                ),
                Instance("TSHX2DQSA",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_DQSW = dqsw,
                    i_T0   = ~(dqs_oe | dqs_postamble),
                    i_T1   = ~(dqs_oe | dqs_preamble),
                    o_Q    = dqs_oe_n
                ),
                Tristate(pads.dqs_p[i], dqs, ~dqs_oe_n, dqs_i)
            ]

            for j in range(8*i, 8*(i+1)):
                dq_o            = Signal()
                dq_i            = Signal()
                dq_oe_n         = Signal()
                dq_i_delayed    = Signal()
                dq_i_data       = Signal(4)
                dq_o_data       = Signal(8)
                dq_o_data_d     = Signal(8)
                dq_o_data_muxed = Signal(4)
                self.comb += dq_o_data.eq(Cat(
                    dfi.phases[0].wrdata[0*databits+j],
                    dfi.phases[0].wrdata[1*databits+j],
                    dfi.phases[0].wrdata[2*databits+j],
                    dfi.phases[0].wrdata[3*databits+j],

                    dfi.phases[1].wrdata[0*databits+j],
                    dfi.phases[1].wrdata[1*databits+j],
                    dfi.phases[1].wrdata[2*databits+j],
                    dfi.phases[1].wrdata[3*databits+j])
                )
                self.sync += dq_o_data_d.eq(dq_o_data)
                dq_bl8_cases = {}
                dq_bl8_cases[0] = dq_o_data_muxed.eq(dq_o_data[:4])
                dq_bl8_cases[1] = dq_o_data_muxed.eq(dq_o_data_d[4:])
                self.sync += Case(bl8_chunk, dq_bl8_cases)
                self.specials += [
                    Instance("ODDRX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSW270 = dqsw270,
                        i_D0      = dq_o_data_muxed[0],
                        i_D1      = dq_o_data_muxed[1],
                        i_D2      = dq_o_data_muxed[2],
                        i_D3      = dq_o_data_muxed[3],
                        o_Q       = dq_o
                    ),
                    Instance("DELAYF",
                        p_DEL_MODE  = "DQS_ALIGNED_X2",
                        i_LOADN     = 1,
                        i_MOVE      = 0,
                        i_DIRECTION = 0,
                        i_A         = dq_i,
                        o_Z         = dq_i_delayed
                    ),
                    Instance("IDDRX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSR90  = dqsr90,
                        i_RDPNTR0 = rdpntr[0],
                        i_RDPNTR1 = rdpntr[1],
                        i_RDPNTR2 = rdpntr[2],
                        i_WRPNTR0 = wrpntr[0],
                        i_WRPNTR1 = wrpntr[1],
                        i_WRPNTR2 = wrpntr[2],
                        i_D       = dq_i_delayed,
                        o_Q0      = dq_i_data[0],
                        o_Q1      = dq_i_data[1],
                        o_Q2      = dq_i_data[2],
                        o_Q3      = dq_i_data[3],
                    )
                ]

                dq_i_bitslip = BitSlip(4,
                    rst    = self._dly_sel.storage[i] & self._rdly_dq_bitslip_rst.re,
                    slp    = self._dly_sel.storage[i] & self._rdly_dq_bitslip.re,
                    cycles = 1)
                self.submodules += dq_i_bitslip
                dq_i_bitslip_o_d = Signal(4)
                self.comb += dq_i_bitslip.i.eq(dq_i_data)
                self.sync += dq_i_bitslip_o_d.eq(dq_i_bitslip.o)
                self.comb += [
                    dfi.phases[0].rddata[0*databits+j].eq(dq_i_bitslip_o_d[0]),
                    dfi.phases[0].rddata[1*databits+j].eq(dq_i_bitslip_o_d[1]),
                    dfi.phases[0].rddata[2*databits+j].eq(dq_i_bitslip_o_d[2]),
                    dfi.phases[0].rddata[3*databits+j].eq(dq_i_bitslip_o_d[3]),
                    dfi.phases[1].rddata[0*databits+j].eq(dq_i_bitslip.o[0]),
                    dfi.phases[1].rddata[1*databits+j].eq(dq_i_bitslip.o[1]),
                    dfi.phases[1].rddata[2*databits+j].eq(dq_i_bitslip.o[2]),
                    dfi.phases[1].rddata[3*databits+j].eq(dq_i_bitslip.o[3]),
                ]
                self.specials += [
                    Instance("TSHX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSW270 = dqsw270,
                        i_T0      = ~dq_oe,
                        i_T1      = ~dq_oe,
                        o_Q       = dq_oe_n,
                    ),
                    Tristate(pads.dq[j], dq_o, ~dq_oe_n, dq_i)
                ]

        # Read Control Path
        #
        # Creates a shift register of read commands coming from the DFI interface. This shift register
        # is used to control DQS read (internal read pulse of the DQSBUF) and to indicate to the
        # DFI interface that the read data is valid.
        #
        # The DQS read must be asserted for 2 sys_clk cycles before the read data is coming back from
        # the DRAM (see 6.2.4 READ Pulse Positioning Optimization of FPGA-TN-02035-1.2)
        #
        # The read data valid is asserted for 1 sys_clk cycle when the data is available on the DFI
        # interface, the latency is the sum of the ODDRX2DQA, CAS, IDDRX2DQA latencies.

        rddata_en = Signal(self.settings.read_latency)
        rddata_en_last = Signal.like(rddata_en)
        self.comb += rddata_en.eq(Cat(dfi.phases[self.settings.rdphase].rddata_en, rddata_en_last))
        self.sync += rddata_en_last.eq(rddata_en)
        self.sync += [phase.rddata_valid.eq(rddata_en[-1]) for phase in dfi.phases]
        self.comb += dqs_re.eq(rddata_en[cl_sys_latency + 1] | rddata_en[cl_sys_latency + 2])

        # Write Control Path
        #
        # Creates a shift register of write commands coming from the DFI interface. This shift register
        # is used to control DQ/DQS tristates and to select write data of the DRAM burst from the DFI
        # interface: The PHY is operating in halfrate mode (so provide 4 datas every sys_clk cycles:
        # 2x for DDR, 2x for halfrate) but DDR3 requires a burst of 8 datas (BL8) for best efficiency.
        # Writes are then performed in 2 sys_clk cycles and data needs to be selected for each cycle.

        wrdata_en = Signal(cwl_sys_latency + 4)
        wrdata_en_last = Signal.like(wrdata_en)
        self.comb += wrdata_en.eq(Cat(dfi.phases[self.settings.wrphase].wrdata_en, wrdata_en_last))
        self.sync += wrdata_en_last.eq(wrdata_en)
        self.comb += dq_oe.eq(wrdata_en[cwl_sys_latency + 1] | wrdata_en[cwl_sys_latency + 2])
        self.comb += bl8_chunk.eq(wrdata_en[cwl_sys_latency + 1])
        self.comb += dqs_oe.eq(dq_oe)

        # Write DQS Postamble/Preamble Control Path
        #
        # Generates DQS Preamble 1 cycle before the first write and Postamble 1 cycle after the last
        # write. During writes, DQS tristate is configured as output for at least 4 sys_clk cycles:
        # 1 for Preamble, 2 for the Write and 1 for the Postamble.

        self.comb += dqs_preamble.eq( wrdata_en[cwl_sys_latency + 0]  & ~wrdata_en[cwl_sys_latency + 1])
        self.comb += dqs_postamble.eq(wrdata_en[cwl_sys_latency + 3]  & ~wrdata_en[cwl_sys_latency + 2])
