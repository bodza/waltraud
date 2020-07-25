from math import ceil, log2
from collections import OrderedDict
from functools import reduce
from operator import add, and_, or_

from .eigen import *

burst_lengths = {
    "SDR":   1,
    "DDR":   4,
    "LPDDR": 4,
    "DDR2":  4,
    "DDR3":  8,
    "DDR4":  8
}

def get_cl_cw(memtype, tck):
    f_to_cl_cwl = OrderedDict()
    if memtype == "DDR2":
        f_to_cl_cwl[400e6]  = (3, 2)
        f_to_cl_cwl[533e6]  = (4, 3)
        f_to_cl_cwl[677e6]  = (5, 4)
        f_to_cl_cwl[800e6]  = (6, 5)
        f_to_cl_cwl[1066e6] = (7, 5)
    elif memtype == "DDR3":
        f_to_cl_cwl[800e6]  = ( 6, 5)
        f_to_cl_cwl[1066e6] = ( 7, 6)
        f_to_cl_cwl[1333e6] = (10, 7)
        f_to_cl_cwl[1600e6] = (11, 8)
    elif memtype == "DDR4":
        f_to_cl_cwl[1600e6] = (11,  9)
    else:
        raise ValueError
    for f, (cl, cwl) in f_to_cl_cwl.items():
        if tck >= 2/f:
            return cl, cwl
    raise ValueError

def get_sys_latency(nphases, cas_latency):
    return ceil(cas_latency/nphases)

def get_sys_phases(nphases, sys_latency, cas_latency):
    dat_phase = sys_latency*nphases - cas_latency
    cmd_phase = (dat_phase - 1)%nphases
    return cmd_phase, dat_phase

class PHYPadsReducer:
    """PHY Pads Reducer

    Reduce DRAM pads to only use specific modules.

    For testing purposes, we often need to use only some of the DRAM modules. PHYPadsReducer allows
    selecting specific modules and avoid re-definining dram pins in the Platform for this.
    """
    def __init__(self, pads, modules):
        self.pads    = pads
        self.modules = modules

    def __getattr__(self, name):
        if name in ["dq"]:
            return Array([getattr(self.pads, name)[8*i + j]
                for i in self.modules
                for j in range(8)])
        if name in ["dm", "dqs", "dqs_p", "dqs_n"]:
            return Array([getattr(self.pads, name)[i] for i in self.modules])
        else:
            return getattr(self.pads, name)

class PHYPadsCombiner:
    """PHY Pads Combiner

    Combine DRAM pads from fully dissociated chips in a unique DRAM pads structure.

    Most generally, DRAM chips are sharing command/address lines between chips (using a fly-by
    topology since DDR3). On some boards, the DRAM chips are using separate command/address lines
    and this combiner can be used to re-create a single pads structure (that will be compatible with
    LiteDRAM's PHYs) to create a single DRAM controller from multiple fully dissociated DRAMs chips.
    """
    def __init__(self, pads):
        if not isinstance(pads, list):
            self.groups = [pads]
        else:
            self.groups = pads
        self.sel = 0

    def sel_group(self, n):
        self.sel = n

    def __getattr__(self, name):
        if name in ["dm", "dq", "dqs", "dqs_p", "dqs_n"]:
            return Array([getattr(self.groups[j], name)[i]
                for i in range(len(getattr(self.groups[0], name)))
                for j in range(len(self.groups))])
        else:
            return getattr(self.groups[self.sel], name)

class BitSlip(Module):
    def __init__(self, dw, rst=None, slp=None, cycles=1):
        self.i = Signal(dw)
        self.o = Signal(dw)
        self.rst = Signal() if rst is None else rst
        self.slp = Signal() if slp is None else slp

        value = Signal(max=cycles*dw)
        self.sync += If(self.slp, value.eq(value + 1))
        self.sync += If(self.rst, value.eq(0))

        r = Signal((cycles+1)*dw, reset_less=True)
        self.sync += r.eq(Cat(r[dw:], self.i))
        cases = {}
        for i in range(cycles*dw):
            cases[i] = self.o.eq(r[i:dw+i])
        self.comb += Case(value, cases)

class DQSPattern(Module):
    def __init__(self, preamble=None, postamble=None, wlevel_en=0, wlevel_strobe=0, register=False):
        self.preamble  = Signal() if preamble  is None else preamble
        self.postamble = Signal() if postamble is None else postamble
        self.o = Signal(8)

        self.comb += [
            self.o.eq(0b01010101),
            If(self.preamble,
                self.o.eq(0b00010101)
            ),
            If(self.postamble,
                self.o.eq(0b01010100)
            ),
            If(wlevel_en,
                self.o.eq(0b00000000),
                If(wlevel_strobe,
                    self.o.eq(0b00000001)
                )
            )
        ]
        if register:
            o = Signal.like(self.o)
            self.sync += o.eq(self.o)
            self.o = o

class Settings:
    def set_attributes(self, attributes):
        for k, v in attributes.items():
            setattr(self, k, v)

class PhySettings(Settings):
    def __init__(self, phytype, memtype, databits, dfi_databits,
                 nphases,
                 rdphase, wrphase,
                 rdcmdphase, wrcmdphase,
                 cl, read_latency, write_latency, nranks=1, cwl=None):
        self.set_attributes(locals())
        self.cwl = cl if cwl is None else cwl
        self.is_rdimm = False

    # Optional DDR3/DDR4 electrical settings:
    # rtt_nom: Non-Writes on-die termination impedance
    # rtt_wr: Writes on-die termination impedance
    # ron: Output driver impedance
    def add_electrical_settings(self, rtt_nom, rtt_wr, ron):
        assert self.memtype in ["DDR3", "DDR4"]
        self.set_attributes(locals())

    # Optional RDIMM configuration
    def set_rdimm(self, tck, rcd_pll_bypass, rcd_ca_cs_drive, rcd_odt_cke_drive, rcd_clk_drive):
        assert self.memtype == "DDR4"
        self.is_rdimm = True
        self.set_attributes(locals())

class GeomSettings(Settings):
    def __init__(self, bankbits, rowbits, colbits):
        self.set_attributes(locals())
        self.addressbits = max(rowbits, colbits)

class TimingSettings(Settings):
    def __init__(self, tRP, tRCD, tWR, tWTR, tREFI, tRFC, tFAW, tCCD, tRRD, tRC, tRAS, tZQCS):
        self.set_attributes(locals())

def cmd_layout(address_width):
    return [
        ("valid",            1, DIR_M_TO_S),
        ("ready",            1, DIR_S_TO_M),
        ("we",               1, DIR_M_TO_S),
        ("addr", address_width, DIR_M_TO_S),
        ("lock",             1, DIR_S_TO_M), # only used internally

        ("wdata_ready",      1, DIR_S_TO_M),
        ("rdata_valid",      1, DIR_S_TO_M)
    ]

def data_layout(data_width):
    return [
        ("wdata",       data_width, DIR_M_TO_S),
        ("wdata_we", data_width//8, DIR_M_TO_S),
        ("rdata",       data_width, DIR_S_TO_M)
    ]

def cmd_description(address_width):
    return [
        ("we",   1),
        ("addr", address_width)
    ]

def wdata_description(data_width):
    return [
        ("data", data_width),
        ("we",   data_width//8)
    ]

def rdata_description(data_width):
    return [("data", data_width)]

def cmd_request_layout(a, ba):
    return [
        ("a",     a),
        ("ba",   ba),
        ("cas",   1),
        ("ras",   1),
        ("we",    1)
    ]

def cmd_request_rw_layout(a, ba):
    return cmd_request_layout(a, ba) + [
        ("is_cmd", 1),
        ("is_read", 1),
        ("is_write", 1)
    ]

class LiteDRAMInterface(Record):
    def __init__(self, address_align, settings):
        rankbits = log2_int(settings.phy.nranks)
        self.address_align = address_align
        self.address_width = settings.geom.rowbits + settings.geom.colbits + rankbits - address_align
        self.data_width    = settings.phy.dfi_databits*settings.phy.nphases
        self.nbanks   = settings.phy.nranks*(2**settings.geom.bankbits)
        self.nranks   = settings.phy.nranks
        self.settings = settings

        layout = [("bank"+str(i), cmd_layout(self.address_width)) for i in range(self.nbanks)]
        layout += data_layout(self.data_width)
        Record.__init__(self, layout)

class LiteDRAMNativePort(Settings):
    def __init__(self, mode, address_width, data_width, clock_domain="sys", id=0):
        self.set_attributes(locals())

        self.lock = Signal()

        self.cmd   = Endpoint(cmd_description(address_width))
        self.wdata = Endpoint(wdata_description(data_width))
        self.rdata = Endpoint(rdata_description(data_width))

        self.flush = Signal()

        # retro-compatibility # FIXME: remove
        self.aw = self.address_width
        self.dw = self.data_width
        self.cd = self.clock_domain

    def get_bank_address(self, bank_bits, cba_shift):
        cba_upper = cba_shift + bank_bits
        return self.cmd.addr[cba_shift:cba_upper]

    def get_row_column_address(self, bank_bits, rca_bits, cba_shift):
        cba_upper = cba_shift + bank_bits
        if cba_shift < rca_bits:
            if cba_shift:
                return Cat(self.cmd.addr[:cba_shift], self.cmd.addr[cba_upper:])
            else:
                return self.cmd.addr[cba_upper:]
        else:
            return self.cmd.addr[:cba_shift]

class LiteDRAMNativeWritePort(LiteDRAMNativePort):
    def __init__(self, *args, **kwargs):
        LiteDRAMNativePort.__init__(self, "write", *args, **kwargs)

class LiteDRAMNativeReadPort(LiteDRAMNativePort):
    def __init__(self, *args, **kwargs):
        LiteDRAMNativePort.__init__(self, "read", *args, **kwargs)

class tXXDController(Module):
    def __init__(self, txxd):
        self.valid = valid = Signal()
        self.ready = ready = Signal(reset=txxd is None)
        ready.attr.add("no_retiming")

        if txxd is not None:
            count = Signal(max=max(txxd, 2))
            self.sync += \
                If(valid,
                    count.eq(txxd - 1),
                    If((txxd - 1) == 0,
                        ready.eq(1)
                    ).Else(
                        ready.eq(0)
                    )
                ).Elif(~ready,
                    count.eq(count - 1),
                    If(count == 1,
                        ready.eq(1)
                    )
                )

class tFAWController(Module):
    def __init__(self, tfaw):
        self.valid = valid = Signal()
        self.ready = ready = Signal(reset=1)
        ready.attr.add("no_retiming")

        if tfaw is not None:
            count  = Signal(max=max(tfaw, 2))
            window = Signal(tfaw)
            self.sync += window.eq(Cat(valid, window))
            self.comb += count.eq(reduce(add, [window[i] for i in range(tfaw)]))
            self.sync += \
                If(count < 4,
                    If(count == 3,
                        ready.eq(~valid)
                    ).Else(
                        ready.eq(1)
                    )
                )

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
        self._dly_sel = CSRStorage("dly_sel", databits // 8)

        self._rdly_dq_rst         = CSR("rdly_dq_rst")
        self._rdly_dq_inc         = CSR("rdly_dq_inc")
        self._rdly_dq_bitslip_rst = CSR("rdly_dq_bitslip_rst")
        self._rdly_dq_bitslip     = CSR("rdly_dq_bitslip")

        self._burstdet_clr  = CSR("burstdet_clr")
        self._burstdet_seen = CSRStatus("burstdet_seen", databits // 8)

        # Observation
        self.datavalid = Signal(databits // 8)

        # PHY settings
        rdcmdphase, rdphase = get_sys_phases(nphases, cl_sys_latency, cl)
        wrcmdphase, wrphase = get_sys_phases(nphases, cwl_sys_latency, cwl)
        self.settings = PhySettings(
            phytype       = "ECP5DDRPHY",
            memtype       = memtype,
            databits      = databits,
            dfi_databits  = 4 * databits,
            nranks        = nranks,
            nphases       = nphases,
            rdphase       = rdphase,
            wrphase       = wrphase,
            rdcmdphase    = rdcmdphase,
            wrcmdphase    = wrcmdphase,
            cl            = cl,
            cwl           = cwl,
            read_latency  = 2 + cl_sys_latency + 2 + log2_int(4 // nphases) + 5,
            write_latency = cwl_sys_latency
        )

        # DFI Interface
        self.dfi = dfi = DFIInterface(addressbits, bankbits, nranks, 4 * databits, 4)

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

class PhaseInjector(Module, AutoCSR):
    def __init__(self, phase):
        self._command       = CSRStorage("command", 6)  # cs, we, cas, ras, wren, rden
        self._command_issue = CSR("command_issue")
        self._address       = CSRStorage("address", len(phase.address), reset_less=True)
        self._baddress      = CSRStorage("baddress", len(phase.bank),    reset_less=True)
        self._wrdata        = CSRStorage("wrdata", len(phase.wrdata),  reset_less=True)
        self._rddata        = CSRStatus("rddata", len(phase.rddata))

        self.comb += [
            If(self._command_issue.re,
                phase.cs_n.eq(Replicate(~self._command.storage[0], len(phase.cs_n))),
                phase.we_n.eq(~self._command.storage[1]),
                phase.cas_n.eq(~self._command.storage[2]),
                phase.ras_n.eq(~self._command.storage[3])
            ).Else(
                phase.cs_n.eq(Replicate(1, len(phase.cs_n))),
                phase.we_n.eq(1),
                phase.cas_n.eq(1),
                phase.ras_n.eq(1)
            ),
            phase.address.eq(self._address.storage),
            phase.bank.eq(self._baddress.storage),
            phase.wrdata_en.eq(self._command_issue.re & self._command.storage[4]),
            phase.rddata_en.eq(self._command_issue.re & self._command.storage[5]),
            phase.wrdata.eq(self._wrdata.storage),
            phase.wrdata_mask.eq(0)
        ]
        self.sync += If(phase.rddata_valid, self._rddata.status.eq(phase.rddata))

class DFIInjector(Module, AutoCSR):
    def __init__(self, addressbits, bankbits, nranks, databits, nphases=1):
        inti        = DFIInterface(addressbits, bankbits, nranks, databits, nphases)
        self.slave  = DFIInterface(addressbits, bankbits, nranks, databits, nphases)
        self.master = DFIInterface(addressbits, bankbits, nranks, databits, nphases)

        self._control = CSRStorage("control", fields=[
            CSRField("sel",     size=1, values=[
                ("``0b0``", "Software (CPU) control."),
                ("``0b1`",  "Hardware control (default)."),
            ], reset=0b1), # Defaults to HW control.
            CSRField("cke",     size=1),
            CSRField("odt",     size=1),
            CSRField("reset_n", size=1),
        ])

        for n, phase in enumerate(inti.phases):
            setattr(self.submodules, "pi" + str(n), PhaseInjector(phase))

        self.comb += If(self._control.fields.sel,
                self.slave.connect(self.master)
            ).Else(
                inti.connect(self.master)
            )
        for i in range(nranks):
            self.comb += [phase.cke[i].eq(self._control.fields.cke) for phase in inti.phases]
            self.comb += [phase.odt[i].eq(self._control.fields.odt) for phase in inti.phases if hasattr(phase, "odt")]
        self.comb += [phase.reset_n.eq(self._control.fields.reset_n) for phase in inti.phases if hasattr(phase, "reset_n")]

class RefreshExecuter(Module):
    """Refresh Executer

    Execute the refresh sequence to the DRAM:
    - Send a "Precharge All" command
    - Wait tRP
    - Send an "Auto Refresh" command
    - Wait tRFC
    """
    def __init__(self, cmd, trp, trfc):
        self.start = Signal()
        self.done  = Signal()

        self.sync += [
            cmd.a.eq(  0),
            cmd.ba.eq( 0),
            cmd.cas.eq(0),
            cmd.ras.eq(0),
            cmd.we.eq( 0),
            self.done.eq(0),
            # Wait start
            timeline(self.start, [
                # Precharge All
                (0, [
                    cmd.a.eq(  2**10),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(1),
                    cmd.we.eq( 1)
                ]),
                # Auto Refresh after tRP
                (trp, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(1),
                    cmd.ras.eq(1),
                    cmd.we.eq( 0),
                ]),
                # Done after tRP + tRFC
                (trp + trfc, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 0),
                    self.done.eq(1),
                ]),
            ])
        ]

class RefreshSequencer(Module):
    """Refresh Sequencer

    Sequence N refreshs to the DRAM.
    """
    def __init__(self, cmd, trp, trfc, postponing=1):
        self.start = Signal()
        self.done  = Signal()

        executer = RefreshExecuter(cmd, trp, trfc)
        self.submodules += executer

        count = Signal(bits_for(postponing), reset=postponing-1)
        self.sync += [
            If(self.start,
                count.eq(count.reset)
            ).Elif(executer.done,
                If(count != 0,
                    count.eq(count - 1)
                )
            )
        ]
        self.comb += executer.start.eq(self.start | (count != 0))
        self.comb += self.done.eq(executer.done & (count == 0))

class RefreshTimer(Module):
    """Refresh Timer

    Generate periodic pulses (tREFI period) to trigger DRAM refresh.
    """
    def __init__(self, trefi):
        self.wait  = Signal()
        self.done  = Signal()
        self.count = Signal(bits_for(trefi))

        done  = Signal()
        count = Signal(bits_for(trefi), reset=trefi-1)

        self.sync += [
            If(self.wait & ~self.done,
                count.eq(count - 1)
            ).Else(
                count.eq(count.reset)
            )
        ]
        self.comb += [
            done.eq(count == 0),
            self.done.eq(done),
            self.count.eq(count)
        ]

class RefreshPostponer(Module):
    """Refresh Postponer

    Postpone N Refresh requests and generate a request when N is reached.
    """
    def __init__(self, postponing=1):
        self.req_i = Signal()
        self.req_o = Signal()

        count = Signal(bits_for(postponing), reset=postponing-1)
        self.sync += [
            self.req_o.eq(0),
            If(self.req_i,
                count.eq(count - 1),
                If(count == 0,
                    count.eq(count.reset),
                    self.req_o.eq(1)
                )
            )
        ]

class ZQCSExecuter(Module):
    """ZQ Short Calibration Executer

    Execute the ZQCS sequence to the DRAM:
    - Send a "Precharge All" command
    - Wait tRP
    - Send an "ZQ Short Calibration" command
    - Wait tZQCS
    """
    def __init__(self, cmd, trp, tzqcs):
        self.start = Signal()
        self.done  = Signal()

        self.sync += [
            # Note: Don't set cmd to 0 since already done in RefreshExecuter
            self.done.eq(0),
            # Wait start
            timeline(self.start, [
                # Precharge All
                (0, [
                    cmd.a.eq(  2**10),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(1),
                    cmd.we.eq( 1)
                ]),
                # ZQ Short Calibration after tRP
                (trp, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 1),
                ]),
                # Done after tRP + tZQCS
                (trp + tzqcs, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 0),
                    self.done.eq(1)
                ]),
            ])
        ]

class Refresher(Module):
    """Refresher

    Manage DRAM refresh.

    The DRAM needs to be periodically refreshed with a tREFI period to avoid data corruption. During
    a refresh, the controller send a "Precharge All" command to close and precharge all rows and then
    send a "Auto Refresh" command.

    Before executing the refresh, the Refresher advertises the Controller that a refresh should occur,
    this allows the Controller to finish the current transaction and block next transactions. Once all
    transactions are done, the Refresher can execute the refresh Sequence and release the Controller.

    """
    def __init__(self, settings, clk_freq, zqcs_freq=1e0, postponing=1):
        assert postponing <= 8
        abits  = settings.geom.addressbits
        babits = settings.geom.bankbits + log2_int(settings.phy.nranks)
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a=abits, ba=babits))

        wants_refresh = Signal()
        wants_zqcs    = Signal()

        # Refresh Timer ----------------------------------------------------------------------------
        timer = RefreshTimer(settings.timing.tREFI)
        self.submodules.timer = timer
        self.comb += timer.wait.eq(~timer.done)

        # Refresh Postponer ------------------------------------------------------------------------
        postponer = RefreshPostponer(postponing)
        self.submodules.postponer = postponer
        self.comb += postponer.req_i.eq(self.timer.done)
        self.comb += wants_refresh.eq(postponer.req_o)

        # Refresh Sequencer ------------------------------------------------------------------------
        sequencer = RefreshSequencer(cmd, settings.timing.tRP, settings.timing.tRFC, postponing)
        self.submodules.sequencer = sequencer

        if settings.timing.tZQCS is not None:
            # ZQCS Timer ---------------------------------------------------------------------------
            zqcs_timer = RefreshTimer(int(clk_freq/zqcs_freq))
            self.submodules.zqcs_timer = zqcs_timer
            self.comb += wants_zqcs.eq(zqcs_timer.done)

            # ZQCS Executer ------------------------------------------------------------------------
            zqcs_executer = ZQCSExecuter(cmd, settings.timing.tRP, settings.timing.tZQCS)
            self.submodules.zqs_executer = zqcs_executer
            self.comb += zqcs_timer.wait.eq(~zqcs_executer.done)

        # Refresh FSM ------------------------------------------------------------------------------
        self.submodules.fsm = fsm = FSM()
        fsm.act("IDLE",
            If(settings.with_refresh,
                If(wants_refresh,
                    NextState("WAIT-BANK-MACHINES")
                )
            )
        )
        fsm.act("WAIT-BANK-MACHINES",
            cmd.valid.eq(1),
            If(cmd.ready,
                sequencer.start.eq(1),
                NextState("DO-REFRESH")
            )
        )
        if settings.timing.tZQCS is None:
            fsm.act("DO-REFRESH",
                cmd.valid.eq(1),
                If(sequencer.done,
                    cmd.valid.eq(0),
                    cmd.last.eq(1),
                    NextState("IDLE")
                )
            )
        else:
            fsm.act("DO-REFRESH",
                cmd.valid.eq(1),
                If(sequencer.done,
                    If(wants_zqcs,
                        zqcs_executer.start.eq(1),
                        NextState("DO-ZQCS")
                    ).Else(
                        cmd.valid.eq(0),
                        cmd.last.eq(1),
                        NextState("IDLE")
                    )
                )
            )
            fsm.act("DO-ZQCS",
                cmd.valid.eq(1),
                If(zqcs_executer.done,
                    cmd.valid.eq(0),
                    cmd.last.eq(1),
                    NextState("IDLE")
                )
            )

class _AddressSlicer:
    """Helper for extracting row/col from address

    Column occupies lower bits of the address, row - higher bits. Address has
    a forced alignment, so column does not contain alignment bits.
    """
    def __init__(self, colbits, address_align):
        self.colbits       = colbits
        self.address_align = address_align

    def row(self, address):
        split = self.colbits - self.address_align
        return address[split:]

    def col(self, address):
        split = self.colbits - self.address_align
        return Cat(Replicate(0, self.address_align), address[:split])

class BankMachine(Module):
    """Converts requests from ports into DRAM commands

    BankMachine abstracts single DRAM bank by keeping track of the currently
    selected row. It converts requests from LiteDRAMCrossbar to targetted
    to that bank into DRAM commands that go to the Multiplexer, inserting any
    needed activate/precharge commands (with optional auto-precharge). It also
    keeps track and enforces some DRAM timings (other timings are enforced in
    the Multiplexer).

    BankMachines work independently from the data path (which connects
    LiteDRAMCrossbar with the Multiplexer directly).

    Stream of requests from LiteDRAMCrossbar is being queued, so that reqeust
    can be "looked ahead", and auto-precharge can be performed (if enabled in
    settings).

    Lock (cmd_layout.lock) is used to synchronise with LiteDRAMCrossbar. It is
    being held when:
     - there is a valid command awaiting in `cmd_buffer_lookahead` - this buffer
       becomes ready simply when the next data gets fetched to the `cmd_buffer`
     - there is a valid command in `cmd_buffer` - `cmd_buffer` becomes ready
       when the BankMachine sends wdata_ready/rdata_valid back to the crossbar

    Parameters
    ----------
    n : int
        Bank number
    address_width : int
        LiteDRAMInterface address width
    address_align : int
        Address alignment depending on burst length
    nranks : int
        Number of separate DRAM chips (width of chip select)
    settings : ControllerSettings
        LiteDRAMController settings

    Attributes
    ----------
    req : Record(cmd_layout)
        Stream of requests from LiteDRAMCrossbar
    refresh_req : Signal(), in
        Indicates that refresh needs to be done, connects to Refresher.cmd.valid
    refresh_gnt : Signal(), out
        Indicates that refresh permission has been granted, satisfying timings
    cmd : Endpoint(cmd_request_rw_layout)
        Stream of commands to the Multiplexer
    """
    def __init__(self, n, address_width, address_align, nranks, settings):
        self.req = req = Record(cmd_layout(address_width))
        self.refresh_req = refresh_req = Signal()
        self.refresh_gnt = refresh_gnt = Signal()

        a  = settings.geom.addressbits
        ba = settings.geom.bankbits + log2_int(nranks)
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a, ba))

        auto_precharge = Signal()

        # Command buffer ---------------------------------------------------------------------------
        cmd_buffer_layout    = [("we", 1), ("addr", len(req.addr))]
        cmd_buffer_lookahead = SyncFIFO(
            cmd_buffer_layout, settings.cmd_buffer_depth,
            buffered=settings.cmd_buffer_buffered)
        cmd_buffer = Buffer(cmd_buffer_layout) # 1 depth buffer to detect row change
        self.submodules += cmd_buffer_lookahead, cmd_buffer
        self.comb += [
            req.connect(cmd_buffer_lookahead.sink, keep={"valid", "ready", "we", "addr"}),
            cmd_buffer_lookahead.source.connect(cmd_buffer.sink),
            cmd_buffer.source.ready.eq(req.wdata_ready | req.rdata_valid),
            req.lock.eq(cmd_buffer_lookahead.source.valid | cmd_buffer.source.valid),
        ]

        slicer = _AddressSlicer(settings.geom.colbits, address_align)

        # Row tracking -----------------------------------------------------------------------------
        row        = Signal(settings.geom.rowbits)
        row_opened = Signal()
        row_hit    = Signal()
        row_open   = Signal()
        row_close  = Signal()
        self.comb += row_hit.eq(row == slicer.row(cmd_buffer.source.addr))
        self.sync += \
            If(row_close,
                row_opened.eq(0)
            ).Elif(row_open,
                row_opened.eq(1),
                row.eq(slicer.row(cmd_buffer.source.addr))
            )

        # Address generation -----------------------------------------------------------------------
        row_col_n_addr_sel = Signal()
        self.comb += [
            cmd.ba.eq(n),
            If(row_col_n_addr_sel,
                cmd.a.eq(slicer.row(cmd_buffer.source.addr))
            ).Else(
                cmd.a.eq((auto_precharge << 10) | slicer.col(cmd_buffer.source.addr))
            )
        ]

        # tWTP (write-to-precharge) controller -----------------------------------------------------
        write_latency = ceil(settings.phy.cwl / settings.phy.nphases)
        precharge_time = write_latency + settings.timing.tWR + settings.timing.tCCD # AL=0
        self.submodules.twtpcon = twtpcon = tXXDController(precharge_time)
        self.comb += twtpcon.valid.eq(cmd.valid & cmd.ready & cmd.is_write)

        # tRC (activate-activate) controller -------------------------------------------------------
        self.submodules.trccon = trccon = tXXDController(settings.timing.tRC)
        self.comb += trccon.valid.eq(cmd.valid & cmd.ready & row_open)

        # tRAS (activate-precharge) controller -----------------------------------------------------
        self.submodules.trascon = trascon = tXXDController(settings.timing.tRAS)
        self.comb += trascon.valid.eq(cmd.valid & cmd.ready & row_open)

        # Auto Precharge generation ----------------------------------------------------------------
        # generate auto precharge when current and next cmds are to different rows
        if settings.with_auto_precharge:
            self.comb += \
                If(cmd_buffer_lookahead.source.valid & cmd_buffer.source.valid,
                    If(slicer.row(cmd_buffer_lookahead.source.addr) !=
                       slicer.row(cmd_buffer.source.addr),
                        auto_precharge.eq(row_close == 0)
                    )
                )

        # Control and command generation FSM -------------------------------------------------------
        # Note: tRRD, tFAW, tCCD, tWTR timings are enforced by the multiplexer
        self.submodules.fsm = fsm = FSM()
        fsm.act("REGULAR",
            If(refresh_req,
                NextState("REFRESH")
            ).Elif(cmd_buffer.source.valid,
                If(row_opened,
                    If(row_hit,
                        cmd.valid.eq(1),
                        If(cmd_buffer.source.we,
                            req.wdata_ready.eq(cmd.ready),
                            cmd.is_write.eq(1),
                            cmd.we.eq(1),
                        ).Else(
                            req.rdata_valid.eq(cmd.ready),
                            cmd.is_read.eq(1)
                        ),
                        cmd.cas.eq(1),
                        If(cmd.ready & auto_precharge,
                           NextState("AUTOPRECHARGE")
                        )
                    ).Else(  # row_opened & ~row_hit
                        NextState("PRECHARGE")
                    )
                ).Else(  # ~row_opened
                    NextState("ACTIVATE")
                )
            )
        )
        fsm.act("PRECHARGE",
            # Note: we are presenting the column address, A10 is always low
            If(twtpcon.ready & trascon.ready,
                cmd.valid.eq(1),
                If(cmd.ready,
                    NextState("TRP")
                ),
                cmd.ras.eq(1),
                cmd.we.eq(1),
                cmd.is_cmd.eq(1)
            ),
            row_close.eq(1)
        )
        fsm.act("AUTOPRECHARGE",
            If(twtpcon.ready & trascon.ready,
                NextState("TRP")
            ),
            row_close.eq(1)
        )
        fsm.act("ACTIVATE",
            If(trccon.ready,
                row_col_n_addr_sel.eq(1),
                row_open.eq(1),
                cmd.valid.eq(1),
                cmd.is_cmd.eq(1),
                If(cmd.ready,
                    NextState("TRCD")
                ),
                cmd.ras.eq(1)
            )
        )
        fsm.act("REFRESH",
            If(twtpcon.ready,
                refresh_gnt.eq(1),
            ),
            row_close.eq(1),
            cmd.is_cmd.eq(1),
            If(~refresh_req,
                NextState("REGULAR")
            )
        )
        fsm.delayed_enter("TRP", "ACTIVATE", settings.timing.tRP - 1)
        fsm.delayed_enter("TRCD", "REGULAR", settings.timing.tRCD - 1)

class Bandwidth(Module, AutoCSR):
    """Measures LiteDRAM bandwidth

    This module works by counting the number of read/write commands issued by
    the controller during a fixed time period. To copy the values registered
    during the last finished period, user must write to the `update` register.

    Parameters
    ----------
    cmd : Endpoint(cmd_request_rw_layout)
        Multiplexer endpoint on which all read/write requests are being sent
    data_width : int, in
        Data width that can be read back from CSR
    period_bits : int, in
        Defines length of bandwidth measurement period = 2^period_bits

    Attributes
    ----------
    update : CSR, in
        Copy the values from last finished period to the status registers
    nreads : CSRStatus, out
        Number of READ commands issued during a period
    nwrites : CSRStatus, out
        Number of WRITE commands issued during a period
    data_width : CSRStatus, out
        Can be read to calculate bandwidth in bits/sec as:
            bandwidth = (nreads+nwrites) * data_width / period
    """
    def __init__(self, cmd, data_width, period_bits=24):
        self.update     = CSR("update")
        self.nreads     = CSRStatus("nreads", period_bits + 1)
        self.nwrites    = CSRStatus("nwrites", period_bits + 1)
        self.data_width = CSRStatus("data_width", bits_for(data_width), reset=data_width)

        cmd_valid    = Signal()
        cmd_ready    = Signal()
        cmd_is_read  = Signal()
        cmd_is_write = Signal()
        self.sync += [
            cmd_valid.eq(cmd.valid),
            cmd_ready.eq(cmd.ready),
            cmd_is_read.eq(cmd.is_read),
            cmd_is_write.eq(cmd.is_write)
        ]

        counter   = Signal(period_bits)
        period    = Signal()
        nreads    = Signal(period_bits + 1)
        nwrites   = Signal(period_bits + 1)
        nreads_r  = Signal(period_bits + 1)
        nwrites_r = Signal(period_bits + 1)
        self.sync += [
            Cat(counter, period).eq(counter + 1),
            If(period,
                nreads_r.eq(nreads),
                nwrites_r.eq(nwrites),
                nreads.eq(0),
                nwrites.eq(0),
                # don't miss command if there is one on period boundary
                If(cmd_valid & cmd_ready,
                    If(cmd_is_read, nreads.eq(1)),
                    If(cmd_is_write, nwrites.eq(1)),
                )
            ).Elif(cmd_valid & cmd_ready,
                If(cmd_is_read, nreads.eq(nreads + 1)),
                If(cmd_is_write, nwrites.eq(nwrites + 1)),
            ),
            If(self.update.re,
                self.nreads.status.eq(nreads_r),
                self.nwrites.status.eq(nwrites_r)
            )
        ]

class _CommandChooser(Module):
    """Arbitrates between requests, filtering them based on their type

    Uses RoundRobin to choose current request, filters requests based on
    `want_*` signals.

    Parameters
    ----------
    requests : [Endpoint(cmd_request_rw_layout), ...]
        Request streams to consider for arbitration

    Attributes
    ----------
    want_reads : Signal, in
        Consider read requests
    want_writes : Signal, in
        Consider write requests
    want_cmds : Signal, in
        Consider command requests (without ACT)
    want_activates : Signal, in
        Also consider ACT commands
    cmd : Endpoint(cmd_request_rw_layout)
        Currently selected request stream (when ~cmd.valid, cas/ras/we are 0)
    """
    def __init__(self, requests):
        self.want_reads     = Signal()
        self.want_writes    = Signal()
        self.want_cmds      = Signal()
        self.want_activates = Signal()

        a  = len(requests[0].a)
        ba = len(requests[0].ba)

        # cas/ras/we are 0 when valid is inactive
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a, ba))

        n = len(requests)

        valids = Signal(n)
        for i, request in enumerate(requests):
            is_act_cmd = request.ras & ~request.cas & ~request.we
            command = request.is_cmd & self.want_cmds & (~is_act_cmd | self.want_activates)
            read = request.is_read == self.want_reads
            write = request.is_write == self.want_writes
            self.comb += valids[i].eq(request.valid & (command | (read & write)))

        arbiter = RoundRobin(n, SP_CE)
        self.submodules += arbiter
        choices = Array(valids[i] for i in range(n))
        self.comb += [
            arbiter.request.eq(valids),
            cmd.valid.eq(choices[arbiter.grant])
        ]

        for name in ["a", "ba", "is_read", "is_write", "is_cmd"]:
            choices = Array(getattr(req, name) for req in requests)
            self.comb += getattr(cmd, name).eq(choices[arbiter.grant])

        for name in ["cas", "ras", "we"]:
            # we should only assert those signals when valid is 1
            choices = Array(getattr(req, name) for req in requests)
            self.comb += \
                If(cmd.valid,
                    getattr(cmd, name).eq(choices[arbiter.grant])
                )

        for i, request in enumerate(requests):
            self.comb += \
                If(cmd.valid & cmd.ready & (arbiter.grant == i),
                    request.ready.eq(1)
                )
        # Arbitrate if a command is being accepted or if the command is not valid to ensure a valid
        # command is selected when cmd.ready goes high.
        self.comb += arbiter.ce.eq(cmd.ready | ~cmd.valid)

    # helpers
    def accept(self):
        return self.cmd.valid & self.cmd.ready

    def activate(self):
        return self.cmd.ras & ~self.cmd.cas & ~self.cmd.we

    def write(self):
        return self.cmd.is_write

    def read(self):
        return self.cmd.is_read

(STEER_NOP, STEER_CMD, STEER_REQ, STEER_REFRESH) = range(4)

class _Steerer(Module):
    """Connects selected request to DFI interface

    cas/ras/we/is_write/is_read are connected only when `cmd.valid & cmd.ready`.
    Rank bits are decoded and used to drive cs_n in multi-rank systems,
    STEER_REFRESH always enables all ranks.

    Parameters
    ----------
    commands : [Endpoint(cmd_request_rw_layout), ...]
        Command streams to choose from. Must be of len=4 in the order:
            NOP, CMD, REQ, REFRESH
        NOP can be of type Record(cmd_request_rw_layout) instead, so that it is
        always considered invalid (because of lack of the `valid` attribute).
    dfi : DFIInterface
        DFI interface connected to PHY

    Attributes
    ----------
    sel : [Signal(max=len(commands)), ...], in
        Signals for selecting which request gets connected to the corresponding
        DFI phase. The signals should take one of the values from STEER_* to
        select given source.
    """
    def __init__(self, commands, dfi):
        ncmd = len(commands)
        nph  = len(dfi.phases)
        self.sel = [Signal(max=ncmd) for i in range(nph)]

        def valid_and(cmd, attr):
            if not hasattr(cmd, "valid"):
                return 0
            else:
                return cmd.valid & cmd.ready & getattr(cmd, attr)

        for i, (phase, sel) in enumerate(zip(dfi.phases, self.sel)):
            nranks   = len(phase.cs_n)
            rankbits = log2_int(nranks)
            if hasattr(phase, "reset_n"):
                self.comb += phase.reset_n.eq(1)
            self.comb += phase.cke.eq(Replicate(Signal(reset=1), nranks))
            if hasattr(phase, "odt"):
                # FIXME: add dynamic drive for multi-rank (will be needed for high frequencies)
                self.comb += phase.odt.eq(Replicate(Signal(reset=1), nranks))
            if rankbits:
                rank_decoder = Decoder(nranks)
                self.submodules += rank_decoder
                self.comb += rank_decoder.i.eq((Array(cmd.ba[-rankbits:] for cmd in commands)[sel]))
                if i == 0: # Select all ranks on refresh.
                    self.sync += If(sel == STEER_REFRESH, phase.cs_n.eq(0)).Else(phase.cs_n.eq(~rank_decoder.o))
                else:
                    self.sync += phase.cs_n.eq(~rank_decoder.o)
                self.sync += phase.bank.eq(Array(cmd.ba[:-rankbits] for cmd in commands)[sel])
            else:
                self.sync += phase.cs_n.eq(0)
                self.sync += phase.bank.eq(Array(cmd.ba[:] for cmd in commands)[sel])

            self.sync += [
                phase.address.eq(Array(cmd.a for cmd in commands)[sel]),
                phase.cas_n.eq(~Array(valid_and(cmd, "cas") for cmd in commands)[sel]),
                phase.ras_n.eq(~Array(valid_and(cmd, "ras") for cmd in commands)[sel]),
                phase.we_n.eq(~Array(valid_and(cmd, "we") for cmd in commands)[sel])
            ]

            rddata_ens = Array(valid_and(cmd, "is_read") for cmd in commands)
            wrdata_ens = Array(valid_and(cmd, "is_write") for cmd in commands)
            self.sync += [
                phase.rddata_en.eq(rddata_ens[sel]),
                phase.wrdata_en.eq(wrdata_ens[sel])
            ]

class Multiplexer(Module, AutoCSR):
    """Multplexes requets from BankMachines to DFI

    This module multiplexes requests from BankMachines (and Refresher) and
    connects them to DFI. Refresh commands are coordinated between the Refresher
    and BankMachines to ensure there are no conflicts. Enforces required timings
    between commands (some timings are enforced by BankMachines).

    Parameters
    ----------
    settings : ControllerSettings
        Controller settings (with .phy, .geom and .timing settings)
    bank_machines : [BankMachine, ...]
        Bank machines that generate command requests to the Multiplexer
    refresher : Refresher
        Generates REFRESH command requests
    dfi : DFIInterface
        DFI connected to the PHY
    interface : LiteDRAMInterface
        Data interface connected directly to LiteDRAMCrossbar
    """
    def __init__(self, settings, bank_machines, refresher, dfi, interface):
        assert(settings.phy.nphases == len(dfi.phases))

        ras_allowed = Signal(reset=1)
        cas_allowed = Signal(reset=1)

        # Command choosing -------------------------------------------------------------------------
        requests = [bm.cmd for bm in bank_machines]
        self.submodules.choose_cmd = choose_cmd = _CommandChooser(requests)
        self.submodules.choose_req = choose_req = _CommandChooser(requests)
        if settings.phy.nphases == 1:
            # When only 1 phase, use choose_req for all requests
            choose_cmd = choose_req
            self.comb += choose_req.want_cmds.eq(1)
            self.comb += choose_req.want_activates.eq(ras_allowed)

        # Command steering -------------------------------------------------------------------------
        nop = Record(cmd_request_layout(settings.geom.addressbits, log2_int(len(bank_machines))))
        # nop must be 1st
        commands = [nop, choose_cmd.cmd, choose_req.cmd, refresher.cmd]
        steerer = _Steerer(commands, dfi)
        self.submodules += steerer

        # tRRD timing (Row to Row delay) -----------------------------------------------------------
        self.submodules.trrdcon = trrdcon = tXXDController(settings.timing.tRRD)
        self.comb += trrdcon.valid.eq(choose_cmd.accept() & choose_cmd.activate())

        # tFAW timing (Four Activate Window) -------------------------------------------------------
        self.submodules.tfawcon = tfawcon = tFAWController(settings.timing.tFAW)
        self.comb += tfawcon.valid.eq(choose_cmd.accept() & choose_cmd.activate())

        # RAS control ------------------------------------------------------------------------------
        self.comb += ras_allowed.eq(trrdcon.ready & tfawcon.ready)

        # tCCD timing (Column to Column delay) -----------------------------------------------------
        self.submodules.tccdcon = tccdcon = tXXDController(settings.timing.tCCD)
        self.comb += tccdcon.valid.eq(choose_req.accept() & (choose_req.write() | choose_req.read()))

        # CAS control ------------------------------------------------------------------------------
        self.comb += cas_allowed.eq(tccdcon.ready)

        # tWTR timing (Write to Read delay) --------------------------------------------------------
        write_latency = ceil(settings.phy.cwl / settings.phy.nphases)
        self.submodules.twtrcon = twtrcon = tXXDController(
            settings.timing.tWTR + write_latency +
            # tCCD must be added since tWTR begins after the transfer is complete
            settings.timing.tCCD if settings.timing.tCCD is not None else 0)
        self.comb += twtrcon.valid.eq(choose_req.accept() & choose_req.write())

        # Read/write turnaround --------------------------------------------------------------------
        read_available = Signal()
        write_available = Signal()
        reads = [req.valid & req.is_read for req in requests]
        writes = [req.valid & req.is_write for req in requests]
        self.comb += [
            read_available.eq(reduce(or_, reads)),
            write_available.eq(reduce(or_, writes))
        ]

        def anti_starvation(timeout):
            en = Signal()
            max_time = Signal()
            if timeout:
                t = timeout - 1
                time = Signal(max=t+1)
                self.comb += max_time.eq(time == 0)
                self.sync += If(~en,
                        time.eq(t)
                    ).Elif(~max_time,
                        time.eq(time - 1)
                    )
            else:
                self.comb += max_time.eq(0)
            return en, max_time

        read_time_en,   max_read_time = anti_starvation(settings.read_time)
        write_time_en, max_write_time = anti_starvation(settings.write_time)

        # Refresh ----------------------------------------------------------------------------------
        self.comb += [bm.refresh_req.eq(refresher.cmd.valid) for bm in bank_machines]
        go_to_refresh = Signal()
        bm_refresh_gnts = [bm.refresh_gnt for bm in bank_machines]
        self.comb += go_to_refresh.eq(reduce(and_, bm_refresh_gnts))

        # Datapath ---------------------------------------------------------------------------------
        all_rddata = [p.rddata for p in dfi.phases]
        all_wrdata = [p.wrdata for p in dfi.phases]
        all_wrdata_mask = [p.wrdata_mask for p in dfi.phases]
        self.comb += [
            interface.rdata.eq(Cat(*all_rddata)),
            Cat(*all_wrdata).eq(interface.wdata),
            Cat(*all_wrdata_mask).eq(~interface.wdata_we)
        ]

        def steerer_sel(steerer, r_w_n):
            r = []
            for i in range(settings.phy.nphases):
                s = steerer.sel[i].eq(STEER_NOP)
                if r_w_n == "read":
                    if i == settings.phy.rdphase:
                        s = steerer.sel[i].eq(STEER_REQ)
                    elif i == settings.phy.rdcmdphase:
                        s = steerer.sel[i].eq(STEER_CMD)
                elif r_w_n == "write":
                    if i == settings.phy.wrphase:
                        s = steerer.sel[i].eq(STEER_REQ)
                    elif i == settings.phy.wrcmdphase:
                        s = steerer.sel[i].eq(STEER_CMD)
                else:
                    raise ValueError
                r.append(s)
            return r

        # Control FSM ------------------------------------------------------------------------------
        self.submodules.fsm = fsm = FSM()
        fsm.act("READ",
            read_time_en.eq(1),
            choose_req.want_reads.eq(1),
            If(settings.phy.nphases == 1,
                choose_req.cmd.ready.eq(cas_allowed & (~choose_req.activate() | ras_allowed))
            ).Else(
                choose_cmd.want_activates.eq(ras_allowed),
                choose_cmd.cmd.ready.eq(~choose_cmd.activate() | ras_allowed),
                choose_req.cmd.ready.eq(cas_allowed)
            ),
            steerer_sel(steerer, "read"),
            If(write_available,
                # TODO: switch only after several cycles of ~read_available?
                If(~read_available | max_read_time,
                    NextState("RTW")
                )
            ),
            If(go_to_refresh,
                NextState("REFRESH")
            )
        )
        fsm.act("WRITE",
            write_time_en.eq(1),
            choose_req.want_writes.eq(1),
            If(settings.phy.nphases == 1,
                choose_req.cmd.ready.eq(cas_allowed & (~choose_req.activate() | ras_allowed))
            ).Else(
                choose_cmd.want_activates.eq(ras_allowed),
                choose_cmd.cmd.ready.eq(~choose_cmd.activate() | ras_allowed),
                choose_req.cmd.ready.eq(cas_allowed),
            ),
            steerer_sel(steerer, "write"),
            If(read_available,
                If(~write_available | max_write_time,
                    NextState("WTR")
                )
            ),
            If(go_to_refresh,
                NextState("REFRESH")
            )
        )
        fsm.act("REFRESH",
            steerer.sel[0].eq(STEER_REFRESH),
            refresher.cmd.ready.eq(1),
            If(refresher.cmd.last,
                NextState("READ")
            )
        )
        fsm.act("WTR",
            If(twtrcon.ready,
                NextState("READ")
            )
        )
        # TODO: reduce this, actual limit is around (cl+1)/nphases
        fsm.delayed_enter("RTW", "WRITE", settings.phy.read_latency-1)

        if settings.with_bandwidth:
            data_width = settings.phy.dfi_databits*settings.phy.nphases
            self.submodules.bandwidth = Bandwidth(self.choose_req.cmd, data_width)

class ControllerSettings(Settings):
    def __init__(self,
        # Command buffers
        cmd_buffer_depth    = 8,
        cmd_buffer_buffered = False,

        # Read/Write times
        read_time           = 32,
        write_time          = 16,

        # Bandwidth
        with_bandwidth      = False,

        # Refresh
        with_refresh        = True,
        refresh_cls         = Refresher,
        refresh_zqcs_freq   = 1e0,
        refresh_postponing  = 1,

        # Auto-Precharge
        with_auto_precharge = True,

        # Address mapping
        address_mapping     = "ROW_BANK_COL"):
        self.set_attributes(locals())

class LiteDRAMController(Module):
    def __init__(self, phy_settings, geom_settings, timing_settings, clk_freq,
        controller_settings=ControllerSettings()):
        burst_length = phy_settings.nphases * (1 if phy_settings.memtype == "SDR" else 2)
        address_align = log2_int(burst_length)

        # Settings ---------------------------------------------------------------------------------
        self.settings        = controller_settings
        self.settings.phy    = phy_settings
        self.settings.geom   = geom_settings
        self.settings.timing = timing_settings

        nranks = phy_settings.nranks
        nbanks = 2**geom_settings.bankbits

        # LiteDRAM Interface (User) ----------------------------------------------------------------
        self.interface = interface = LiteDRAMInterface(address_align, self.settings)

        # DFI Interface (Memory) -------------------------------------------------------------------
        self.dfi = DFIInterface(
            addressbits = geom_settings.addressbits,
            bankbits    = geom_settings.bankbits,
            nranks      = phy_settings.nranks,
            databits    = phy_settings.dfi_databits,
            nphases     = phy_settings.nphases)

        # Refresher --------------------------------------------------------------------------------
        self.submodules.refresher = self.settings.refresh_cls(self.settings,
            clk_freq   = clk_freq,
            zqcs_freq  = self.settings.refresh_zqcs_freq,
            postponing = self.settings.refresh_postponing)

        # Bank Machines ----------------------------------------------------------------------------
        bank_machines = []
        for n in range(nranks*nbanks):
            bank_machine = BankMachine(n,
                address_width = interface.address_width,
                address_align = address_align,
                nranks        = nranks,
                settings      = self.settings)
            bank_machines.append(bank_machine)
            self.submodules += bank_machine
            self.comb += getattr(interface, "bank"+str(n)).connect(bank_machine.req)

        # Multiplexer ------------------------------------------------------------------------------
        self.submodules.multiplexer = Multiplexer(
            settings      = self.settings,
            bank_machines = bank_machines,
            refresher     = self.refresher,
            dfi           = self.dfi,
            interface     = interface)

    def get_csrs(self):
        return self.multiplexer.get_csrs()

class LiteDRAMCrossbar(Module):
    """Multiplexes LiteDRAMController (slave) between ports (masters)

    To get a port to LiteDRAM, use the `get_port` method. It handles data width
    conversion and clock domain crossing, returning LiteDRAMNativePort.

    The crossbar routes requests from masters to the BankMachines
    (bankN.cmd_layout) and connects data path directly to the Multiplexer
    (data_layout). It performs address translation based on chosen
    `controller.settings.address_mapping`.
    Internally, all masters are multiplexed between controller banks based on
    the bank address (extracted from the presented address). Each bank has
    a RoundRobin arbiter, that selects from masters that want to access this
    bank and are not already locked.

    Locks (cmd_layout.lock) make sure that, when a master starts a transaction
    with given bank (which may include multiple reads/writes), no other bank
    will be assigned to it during this time.
    Arbiter (of a bank) considers given master as a candidate for selection if:
     - given master's command is valid
     - given master addresses the arbiter's bank
     - given master is not locked
       * i.e. it is not during transaction with another bank
       * i.e. no other bank's arbiter granted permission for this master (with
         bank.lock being active)

    Data ready/valid signals for banks are routed from bankmachines with
    a latency that synchronizes them with the data coming over datapath.

    Parameters
    ----------
    controller : LiteDRAMInterface
        Interface to LiteDRAMController

    Attributes
    ----------
    masters : [LiteDRAMNativePort, ...]
        LiteDRAM memory ports
    """
    def __init__(self, controller):
        self.controller = controller

        self.rca_bits         = controller.address_width
        self.nbanks           = controller.nbanks
        self.nranks           = controller.nranks
        self.cmd_buffer_depth = controller.settings.cmd_buffer_depth
        self.read_latency     = controller.settings.phy.read_latency + 1
        self.write_latency    = controller.settings.phy.write_latency + 1

        self.bank_bits = log2_int(self.nbanks, False)
        self.rank_bits = log2_int(self.nranks, False)

        self.masters = []

    def get_port(self, mode="both", data_width=None, clock_domain="sys", reverse=False):
        if self.finalized:
            raise FinalizeError

        if data_width is None:
            # use internal data_width when no width adaptation is requested
            data_width = self.controller.data_width

        # Crossbar port ----------------------------------------------------------------------------
        port = LiteDRAMNativePort(
            mode          = mode,
            address_width = self.rca_bits + self.bank_bits - self.rank_bits,
            data_width    = self.controller.data_width,
            clock_domain  = "sys",
            id            = len(self.masters))
        self.masters.append(port)

        # Clock domain crossing --------------------------------------------------------------------
        if clock_domain != "sys":
            new_port = LiteDRAMNativePort(
                mode          = mode,
                address_width = port.address_width,
                data_width    = port.data_width,
                clock_domain  = clock_domain,
                id            = port.id)
            self.submodules += LiteDRAMNativePortCDC(new_port, port)
            port = new_port

        # Data width convertion --------------------------------------------------------------------
        if data_width != self.controller.data_width:
            if data_width > self.controller.data_width:
                addr_shift = -log2_int(data_width//self.controller.data_width)
            else:
                addr_shift = log2_int(self.controller.data_width//data_width)
            new_port = LiteDRAMNativePort(
                mode          = mode,
                address_width = port.address_width + addr_shift,
                data_width    = data_width,
                clock_domain  = clock_domain,
                id            = port.id)
            self.submodules += ClockDomainsRenamer(clock_domain)(
                LiteDRAMNativePortConverter(new_port, port, reverse))
            port = new_port

        return port

    def do_finalize(self):
        controller = self.controller
        nmasters   = len(self.masters)

        # Address mapping --------------------------------------------------------------------------
        cba_shifts = {"ROW_BANK_COL": controller.settings.geom.colbits - controller.address_align}
        cba_shift = cba_shifts[controller.settings.address_mapping]
        m_ba      = [m.get_bank_address(self.bank_bits, cba_shift)for m in self.masters]
        m_rca     = [m.get_row_column_address(self.bank_bits, self.rca_bits, cba_shift) for m in self.masters]

        master_readys       = [0]*nmasters
        master_wdata_readys = [0]*nmasters
        master_rdata_valids = [0]*nmasters

        arbiters = [RoundRobin(nmasters, SP_CE) for n in range(self.nbanks)]
        self.submodules += arbiters

        for nb, arbiter in enumerate(arbiters):
            bank = getattr(controller, "bank"+str(nb))

            # For each master, determine if another bank locks it ----------------------------------
            master_locked = []
            for nm, master in enumerate(self.masters):
                locked = Signal()
                for other_nb, other_arbiter in enumerate(arbiters):
                    if other_nb != nb:
                        other_bank = getattr(controller, "bank"+str(other_nb))
                        locked = locked | (other_bank.lock & (other_arbiter.grant == nm))
                master_locked.append(locked)

            # Arbitrate ----------------------------------------------------------------------------
            bank_selected  = [(ba == nb) & ~locked for ba, locked in zip(m_ba, master_locked)]
            bank_requested = [bs & master.cmd.valid for bs, master in zip(bank_selected, self.masters)]
            self.comb += [
                arbiter.request.eq(Cat(*bank_requested)),
                arbiter.ce.eq(~bank.valid & ~bank.lock)
            ]

            # Route requests -----------------------------------------------------------------------
            self.comb += [
                bank.addr.eq(Array(m_rca)[arbiter.grant]),
                bank.we.eq(Array(self.masters)[arbiter.grant].cmd.we),
                bank.valid.eq(Array(bank_requested)[arbiter.grant])
            ]
            master_readys = [master_ready | ((arbiter.grant == nm) & bank_selected[nm] & bank.ready)
                for nm, master_ready in enumerate(master_readys)]
            master_wdata_readys = [master_wdata_ready | ((arbiter.grant == nm) & bank.wdata_ready)
                for nm, master_wdata_ready in enumerate(master_wdata_readys)]
            master_rdata_valids = [master_rdata_valid | ((arbiter.grant == nm) & bank.rdata_valid)
                for nm, master_rdata_valid in enumerate(master_rdata_valids)]

        # Delay write/read signals based on their latency
        for nm, master_wdata_ready in enumerate(master_wdata_readys):
            for i in range(self.write_latency):
                new_master_wdata_ready = Signal()
                self.sync += new_master_wdata_ready.eq(master_wdata_ready)
                master_wdata_ready = new_master_wdata_ready
            master_wdata_readys[nm] = master_wdata_ready

        for nm, master_rdata_valid in enumerate(master_rdata_valids):
            for i in range(self.read_latency):
                new_master_rdata_valid = Signal()
                self.sync += new_master_rdata_valid.eq(master_rdata_valid)
                master_rdata_valid = new_master_rdata_valid
            master_rdata_valids[nm] = master_rdata_valid

        for master, master_ready in zip(self.masters, master_readys):
            self.comb += master.cmd.ready.eq(master_ready)
        for master, master_wdata_ready in zip(self.masters, master_wdata_readys):
            self.comb += master.wdata.ready.eq(master_wdata_ready)
        for master, master_rdata_valid in zip(self.masters, master_rdata_valids):
            self.comb += master.rdata.valid.eq(master_rdata_valid)

        # Route data writes ------------------------------------------------------------------------
        wdata_cases = {}
        for nm, master in enumerate(self.masters):
            wdata_cases[2**nm] = [
                controller.wdata.eq(master.wdata.data),
                controller.wdata_we.eq(master.wdata.we)
            ]
        wdata_cases["default"] = [
            controller.wdata.eq(0),
            controller.wdata_we.eq(0)
        ]
        self.comb += Case(Cat(*master_wdata_readys), wdata_cases)

        # Route data reads -------------------------------------------------------------------------
        for master in self.masters:
            self.comb += master.rdata.data.eq(controller.rdata)

class LiteDRAMCore(Module, AutoCSR):
    def __init__(self, phy, geom_settings, timing_settings, clk_freq, **kwargs):
        self.submodules.dfii = DFIInjector(
            addressbits = geom_settings.addressbits,
            bankbits    = geom_settings.bankbits,
            nranks      = phy.settings.nranks,
            databits    = phy.settings.dfi_databits,
            nphases     = phy.settings.nphases)
        self.comb += self.dfii.master.connect(phy.dfi)

        self.submodules.controller = controller = LiteDRAMController(
            phy_settings    = phy.settings,
            geom_settings   = geom_settings,
            timing_settings = timing_settings,
            clk_freq        = clk_freq,
            **kwargs)
        self.comb += controller.dfi.connect(self.dfii.slave)

        self.submodules.crossbar = LiteDRAMCrossbar(controller.interface)

cmds = {
    "PRECHARGE_ALL": "DFII_COMMAND_RAS|DFII_COMMAND_WE|DFII_COMMAND_CS",
    "MODE_REGISTER": "DFII_COMMAND_RAS|DFII_COMMAND_CAS|DFII_COMMAND_WE|DFII_COMMAND_CS",
    "AUTO_REFRESH":  "DFII_COMMAND_RAS|DFII_COMMAND_CAS|DFII_COMMAND_CS",
    "UNRESET":       "DFII_CONTROL_ODT|DFII_CONTROL_RESET_N",
    "CKE":           "DFII_CONTROL_CKE|DFII_CONTROL_ODT|DFII_CONTROL_RESET_N"
}

def get_sdr_phy_init_sequence(phy_settings, timing_settings):
    cl = phy_settings.cl
    bl = phy_settings.nphases
    mr = log2_int(bl) + (cl << 4)
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_ddr_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 4
    mr  = log2_int(bl) + (cl << 4)
    emr = 0
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register", emr, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_lpddr_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 4
    mr  = log2_int(bl) + (cl << 4)
    emr = 0
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register", emr, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_ddr2_phy_init_sequence(phy_settings, timing_settings):
    cl   = phy_settings.cl
    bl   = 4
    wr   = 2
    mr   = log2_int(bl) + (cl << 4) + (wr << 9)
    emr  = 0
    emr2 = 0
    emr3 = 0
    ocd  = 7 << 7
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register 3", emr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register 2", emr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register", emr, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200),
        ("Load Extended Mode Register / OCD Default", emr+ocd, 1, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register / OCD Exit", emr, 1, cmds["MODE_REGISTER"], 0),
    ]

    return init_sequence, None

def get_ddr3_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 8
    cwl = phy_settings.cwl

    def format_mr0(bl, cl, wr, dll_reset):
        bl_to_mr0 = {
            4: 0b10,
            8: 0b00
        }
        cl_to_mr0 = {
             5: 0b0010,
             6: 0b0100,
             7: 0b0110,
             8: 0b1000,
             9: 0b1010,
            10: 0b1100,
            11: 0b1110,
            12: 0b0001,
            13: 0b0011,
            14: 0b0101
        }
        wr_to_mr0 = {
            16: 0b000,
             5: 0b001,
             6: 0b010,
             7: 0b011,
             8: 0b100,
            10: 0b101,
            12: 0b110,
            14: 0b111
        }
        mr0 = bl_to_mr0[bl]
        mr0 |= (cl_to_mr0[cl] & 1) << 2
        mr0 |= ((cl_to_mr0[cl] >> 1) & 0b111) << 4
        mr0 |= dll_reset << 8
        mr0 |= wr_to_mr0[wr] << 9
        return mr0

    def format_mr1(ron, rtt_nom):
        mr1 = ((ron >> 0) & 1) << 1
        mr1 |= ((ron >> 1) & 1) << 5
        mr1 |= ((rtt_nom >> 0) & 1) << 2
        mr1 |= ((rtt_nom >> 1) & 1) << 6
        mr1 |= ((rtt_nom >> 2) & 1) << 9
        return mr1

    def format_mr2(cwl, rtt_wr):
        mr2 = (cwl-5) << 3
        mr2 |= rtt_wr << 9
        return mr2

    z_to_rtt_nom = {
        "disabled" : 0,
        "60ohm"    : 1,
        "120ohm"   : 2,
        "40ohm"    : 3,
        "20ohm"    : 4,
        "30ohm"    : 5
    }

    z_to_rtt_wr = {
        "disabled" : 0,
        "60ohm"    : 1,
        "120ohm"   : 2,
    }

    z_to_ron = {
        "40ohm" : 0,
        "34ohm" : 1,
    }

    # default electrical settings (point to point)
    rtt_nom = "60ohm"
    rtt_wr  = "60ohm"
    ron     = "34ohm"

    # override electrical settings if specified
    if hasattr(phy_settings, "rtt_nom"):
        rtt_nom = phy_settings.rtt_nom
    if hasattr(phy_settings, "rtt_wr"):
        rtt_wr = phy_settings.rtt_wr
    if hasattr(phy_settings, "ron"):
        ron = phy_settings.ron

    wr  = max(timing_settings.tWTR*phy_settings.nphases, 5) # >= ceiling(tWR/tCK)
    mr0 = format_mr0(bl, cl, wr, 1)
    mr1 = format_mr1(z_to_ron[ron], z_to_rtt_nom[rtt_nom])
    mr2 = format_mr2(cwl, z_to_rtt_wr[rtt_wr])
    mr3 = 0

    init_sequence = [
        ("Release reset", 0x0000, 0, cmds["UNRESET"], 50000),
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 10000),
        ("Load Mode Register 2, CWL={0:d}".format(cwl), mr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 3", mr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 1", mr1, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 0, CL={0:d}, BL={1:d}".format(cl, bl), mr0, 0, cmds["MODE_REGISTER"], 200),
        ("ZQ Calibration", 0x0400, 0, "DFII_COMMAND_WE|DFII_COMMAND_CS", 200),
    ]

    return init_sequence, mr1

def get_ddr4_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 8
    cwl = phy_settings.cwl

    def format_mr0(bl, cl, wr, dll_reset):
        bl_to_mr0 = {
            4: 0b10,
            8: 0b00
        }
        cl_to_mr0 = {
             9: 0b00000,
            10: 0b00001,
            11: 0b00010,
            12: 0b00011,
            13: 0b00100,
            14: 0b00101,
            15: 0b00110,
            16: 0b00111,
            18: 0b01000,
            20: 0b01001,
            22: 0b01010,
            24: 0b01011,
            23: 0b01100,
            17: 0b01101,
            19: 0b01110,
            21: 0b01111,
            25: 0b10000,
            26: 0b10001,
            27: 0b10010,
            28: 0b10011,
            29: 0b10100,
            30: 0b10101,
            31: 0b10110,
            32: 0b10111,
        }
        wr_to_mr0 = {
            10: 0b0000,
            12: 0b0001,
            14: 0b0010,
            16: 0b0011,
            18: 0b0100,
            20: 0b0101,
            24: 0b0110,
            22: 0b0111,
            26: 0b1000,
            28: 0b1001,
        }
        mr0 = bl_to_mr0[bl]
        mr0 |= (cl_to_mr0[cl] & 0b1) << 2
        mr0 |= ((cl_to_mr0[cl] >> 1) & 0b111) << 4
        mr0 |= ((cl_to_mr0[cl] >> 4) & 0b1) << 12
        mr0 |= dll_reset << 8
        mr0 |= (wr_to_mr0[wr] & 0b111) << 9
        mr0 |= (wr_to_mr0[wr] >> 3) << 13
        return mr0

    def format_mr1(dll_enable, ron, rtt_nom):
        mr1 = dll_enable
        mr1 |= ((ron >> 0) & 0b1) << 1
        mr1 |= ((ron >> 1) & 0b1) << 2
        mr1 |= ((rtt_nom >> 0) & 0b1) << 8
        mr1 |= ((rtt_nom >> 1) & 0b1) << 9
        mr1 |= ((rtt_nom >> 2) & 0b1) << 10
        return mr1

    def format_mr2(cwl, rtt_wr):
        cwl_to_mr2 = {
             9: 0b000,
            10: 0b001,
            11: 0b010,
            12: 0b011,
            14: 0b100,
            16: 0b101,
            18: 0b110,
            20: 0b111
        }
        mr2 = cwl_to_mr2[cwl] << 3
        mr2 |= rtt_wr << 9
        return mr2

    def format_mr3(fine_refresh_mode):
        fine_refresh_mode_to_mr3 = {
            "1x": 0b000,
            "2x": 0b001,
            "4x": 0b010
        }
        mr3 = fine_refresh_mode_to_mr3[fine_refresh_mode] << 6
        return mr3

    def format_mr6(tccd):
        tccd_to_mr6 = {
            4: 0b000,
            5: 0b001,
            6: 0b010,
            7: 0b011,
            8: 0b100
        }
        mr6 = tccd_to_mr6[tccd] << 10
        return mr6

    z_to_rtt_nom = {
        "disabled" : 0b000,
        "60ohm"    : 0b001,
        "120ohm"   : 0b010,
        "40ohm"    : 0b011,
        "240ohm"   : 0b100,
        "48ohm"    : 0b101,
        "80ohm"    : 0b110,
        "34ohm"    : 0b111
    }

    z_to_rtt_wr = {
        "disabled" : 0b000,
        "120ohm"   : 0b001,
        "240ohm"   : 0b010,
        "high-z"   : 0b011,
        "80ohm"    : 0b100,
    }

    z_to_ron = {
        "34ohm" : 0b00,
        "48ohm" : 0b01,
    }

    # default electrical settings (point to point)
    rtt_nom = "40ohm"
    rtt_wr  = "120ohm"
    ron     = "34ohm"

    # override electrical settings if specified
    if hasattr(phy_settings, "rtt_nom"):
        rtt_nom = phy_settings.rtt_nom
    if hasattr(phy_settings, "rtt_wr"):
        rtt_wr = phy_settings.rtt_wr
    if hasattr(phy_settings, "ron"):
        ron = phy_settings.ron

    wr  = max(timing_settings.tWTR*phy_settings.nphases, 10) # >= ceiling(tWR/tCK)
    mr0 = format_mr0(bl, cl, wr, 1)
    mr1 = format_mr1(1, z_to_ron[ron], z_to_rtt_nom[rtt_nom])
    mr2 = format_mr2(cwl, z_to_rtt_wr[rtt_wr])
    mr3 = format_mr3(timing_settings.fine_refresh_mode)
    mr4 = 0
    mr5 = 0
    mr6 = format_mr6(4) # FIXME: tCCD

    rdimm_init = []
    if phy_settings.is_rdimm:
        def get_coarse_speed(tck, pll_bypass):
            # JESD82-31A page 78
            f_to_coarse_speed = {
                1600e6: 0,
                1866e6: 1,
                2133e6: 2,
                2400e6: 3,
                2666e6: 4,
                2933e6: 5,
                3200e6: 6,
            }
            if pll_bypass:
                return 7
            else:
                for f, speed in f_to_coarse_speed.items():
                        if tck >= 2/f:
                            return speed
                raise ValueError
        def get_fine_speed(tck):
            # JESD82-31A page 83
            freq = 2/tck
            fine_speed = (freq - 1240e6) // 20e6
            fine_speed = max(fine_speed, 0)
            fine_speed = min(fine_speed, 0b1100001)
            return fine_speed

        coarse_speed = get_coarse_speed(phy_settings.tck, phy_settings.rcd_pll_bypass)
        fine_speed = get_fine_speed(phy_settings.tck)

        rcd_reset = 0x060 | 0x0                          # F0RC06: command space control; 0: reset RCD

        f0rc0f = 0x0F0 | 0x4                             # F0RC05: 0 nCK latency adder

        f0rc03 = 0x030 | phy_settings.rcd_ca_cs_drive    # F0RC03: CA/CS drive strength
        f0rc04 = 0x040 | phy_settings.rcd_odt_cke_drive  # F0RC04: ODT/CKE drive strength
        f0rc05 = 0x050 | phy_settings.rcd_clk_drive      # F0RC04: ODT/CKE drive strength

        f0rc0a = 0x0A0 | coarse_speed                    # F0RC0A: coarse speed selection and PLL bypass
        f0rc3x = 0x300 | fine_speed                      # F0RC3x: fine speed selection

        rdimm_init = [
            ("Reset RCD", rcd_reset, 7, cmds["MODE_REGISTER"], 50000),
            ("Load RCD F0RC0F", f0rc0f, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC03", f0rc03, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC04", f0rc04, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC05", f0rc05, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC0A", f0rc0a, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC3X", f0rc3x, 7, cmds["MODE_REGISTER"], 100),
        ]

    init_sequence = [
        ("Release reset", 0x0000, 0, cmds["UNRESET"], 50000),
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 10000),
    ] + rdimm_init + [
        ("Load Mode Register 3", mr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 6", mr6, 6, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 5", mr5, 5, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 4", mr4, 4, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 2, CWL={0:d}".format(cwl), mr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 1", mr1, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 0, CL={0:d}, BL={1:d}".format(cl, bl), mr0, 0, cmds["MODE_REGISTER"], 200),
        ("ZQ Calibration", 0x0400, 0, "DFII_COMMAND_WE|DFII_COMMAND_CS", 200),
    ]

    return init_sequence, mr1

def get_sdram_phy_init_sequence(phy_settings, timing_settings):
    return {
        "SDR"  : get_sdr_phy_init_sequence,
        "DDR"  : get_ddr_phy_init_sequence,
        "LPDDR": get_lpddr_phy_init_sequence,
        "DDR2" : get_ddr2_phy_init_sequence,
        "DDR3" : get_ddr3_phy_init_sequence,
        "DDR4" : get_ddr4_phy_init_sequence,
    }[phy_settings.memtype](phy_settings, timing_settings)

def get_sdram_phy_c_header(phy_settings, timing_settings):
    r = "#ifndef __GENERATED_SDRAM_PHY_H\n#define __GENERATED_SDRAM_PHY_H\n"
    r += "#include <hw/common.h>\n"
    r += "#include <generated/csr.h>\n"
    r += "\n"

    r += "#define DFII_CONTROL_SEL        0x01\n"
    r += "#define DFII_CONTROL_CKE        0x02\n"
    r += "#define DFII_CONTROL_ODT        0x04\n"
    r += "#define DFII_CONTROL_RESET_N    0x08\n"
    r += "\n"

    r += "#define DFII_COMMAND_CS         0x01\n"
    r += "#define DFII_COMMAND_WE         0x02\n"
    r += "#define DFII_COMMAND_CAS        0x04\n"
    r += "#define DFII_COMMAND_RAS        0x08\n"
    r += "#define DFII_COMMAND_WRDATA     0x10\n"
    r += "#define DFII_COMMAND_RDDATA     0x20\n"
    r += "\n"

    phytype = phy_settings.phytype.upper()
    nphases = phy_settings.nphases

    # Define PHY type and number of phases
    r += "#define SDRAM_PHY_"+phytype+"\n"
    r += "#define SDRAM_PHY_PHASES "+str(nphases)+"\n"

    # Define Read/Write Leveling capability
    if phytype in ["USDDRPHY", "USPDDRPHY", "K7DDRPHY", "V7DDRPHY"]:
        r += "#define SDRAM_PHY_WRITE_LEVELING_CAPABLE\n"
    if phytype in ["USDDRPHY", "USPDDRPHY"]:
        r += "#define SDRAM_PHY_WRITE_LEVELING_REINIT\n"
    if phytype in ["USDDRPHY", "USPDDRPHY", "A7DDRPHY", "K7DDRPHY", "V7DDRPHY", "ECP5DDRPHY"]:
        r += "#define SDRAM_PHY_READ_LEVELING_CAPABLE\n"

    # Define number of modules/delays/bitslips
    if phytype in ["USDDRPHY", "USPDDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/2\n"
        r += "#define SDRAM_PHY_DELAYS 512\n"
        r += "#define SDRAM_PHY_BITSLIPS 16\n"
    elif phytype in ["A7DDRPHY", "K7DDRPHY", "V7DDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/2\n"
        r += "#define SDRAM_PHY_DELAYS 32\n"
        r += "#define SDRAM_PHY_BITSLIPS 16\n"
    elif phytype in ["ECP5DDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/4\n"
        r += "#define SDRAM_PHY_DELAYS 8\n"
        r += "#define SDRAM_PHY_BITSLIPS 4\n"

    if phy_settings.is_rdimm:
        assert phy_settings.memtype == "DDR4"
        r += "#define SDRAM_PHY_DDR4_RDIMM\n"

    r += "\n"

    r += "static void cdelay(int i);\n"

    # commands_px functions
    for n in range(nphases):
        r += """
__attribute__((unused)) static void command_p{n}(int cmd)
{{
    sdram_dfii_pi{n}_command_write(cmd);
    sdram_dfii_pi{n}_command_issue_write(1);
}}""".format(n=str(n))
    r += "\n\n"

    # rd/wr access macros
    r += """
#define sdram_dfii_pird_address_write(X) sdram_dfii_pi{rdphase}_address_write(X)
#define sdram_dfii_piwr_address_write(X) sdram_dfii_pi{wrphase}_address_write(X)
#define sdram_dfii_pird_baddress_write(X) sdram_dfii_pi{rdphase}_baddress_write(X)
#define sdram_dfii_piwr_baddress_write(X) sdram_dfii_pi{wrphase}_baddress_write(X)
#define command_prd(X) command_p{rdphase}(X)
#define command_pwr(X) command_p{wrphase}(X)
""".format(rdphase=str(phy_settings.rdphase), wrphase=str(phy_settings.wrphase))
    r += "\n"

    #
    # sdrrd/sdrwr functions utilities
    #
    r += "#define DFII_PIX_DATA_SIZE CSR_SDRAM_DFII_PI0_WRDATA_SIZE\n"
    sdram_dfii_pix_wrdata_addr = []
    for n in range(nphases):
        sdram_dfii_pix_wrdata_addr.append("CSR_SDRAM_DFII_PI{n}_WRDATA_ADDR".format(n=n))
    r += """
const unsigned long sdram_dfii_pix_wrdata_addr[SDRAM_PHY_PHASES] = {{
\t{sdram_dfii_pix_wrdata_addr}
}};
""".format(sdram_dfii_pix_wrdata_addr=",\n\t".join(sdram_dfii_pix_wrdata_addr))

    sdram_dfii_pix_rddata_addr = []
    for n in range(nphases):
        sdram_dfii_pix_rddata_addr.append("CSR_SDRAM_DFII_PI{n}_RDDATA_ADDR".format(n=n))
    r += """
const unsigned long sdram_dfii_pix_rddata_addr[SDRAM_PHY_PHASES] = {{
\t{sdram_dfii_pix_rddata_addr}
}};
""".format(sdram_dfii_pix_rddata_addr=",\n\t".join(sdram_dfii_pix_rddata_addr))
    r += "\n"

    init_sequence, mr1 = get_sdram_phy_init_sequence(phy_settings, timing_settings)

    if phy_settings.memtype in ["DDR3", "DDR4"]:
        # the value of MR1 needs to be modified during write leveling
        r += "#define DDRX_MR1 {}\n\n".format(mr1)

    r += "static void init_sequence(void)\n{\n"
    for comment, a, ba, cmd, delay in init_sequence:
        invert_masks = [(0, 0), ]
        if phy_settings.is_rdimm:
            assert phy_settings.memtype == "DDR4"
            # JESD82-31A page 38
            #
            # B-side chips have certain usually-inconsequential address and BA
            # bits inverted by the RCD to reduce SSO current. For mode register
            # writes, however, we must compensate for this. BG[1] also directs
            # writes either to the A side (BG[1]=0) or B side (BG[1]=1)
            #
            # The 'ba != 7' is because we don't do this to writes to the RCD
            # itself.
            if ba != 7:
                invert_masks.append((0b10101111111000, 0b1111))

        for a_inv, ba_inv in invert_masks:
            r += "\t/* {0} */\n".format(comment)
            r += "\tsdram_dfii_pi0_address_write({0:#x});\n".format(a ^ a_inv)
            r += "\tsdram_dfii_pi0_baddress_write({0:d});\n".format(ba ^ ba_inv)
            if cmd[:12] == "DFII_CONTROL":
                r += "\tsdram_dfii_control_write({0});\n".format(cmd)
            else:
                r += "\tcommand_p0({0});\n".format(cmd)
            if delay:
                r += "\tcdelay({0:d});\n".format(delay)
            r += "\n"
    r += "}\n"

    r += "#endif\n"

    return r

def get_sdram_phy_py_header(phy_settings, timing_settings):
    r = ""
    r += "dfii_control_sel     = 0x01\n"
    r += "dfii_control_cke     = 0x02\n"
    r += "dfii_control_odt     = 0x04\n"
    r += "dfii_control_reset_n = 0x08\n"
    r += "\n"
    r += "dfii_command_cs     = 0x01\n"
    r += "dfii_command_we     = 0x02\n"
    r += "dfii_command_cas    = 0x04\n"
    r += "dfii_command_ras    = 0x08\n"
    r += "dfii_command_wrdata = 0x10\n"
    r += "dfii_command_rddata = 0x20\n"
    r += "\n"

    init_sequence, mr1 = get_sdram_phy_init_sequence(phy_settings, timing_settings)

    if mr1 is not None:
        r += "ddrx_mr1 = 0x{:x}\n".format(mr1)
        r += "\n"

    r += "init_sequence = [\n"
    for comment, a, ba, cmd, delay in init_sequence:
        r += "    "
        r += "(\"" + comment + "\", "
        r += str(a) + ", "
        r += str(ba) + ", "
        r += cmd.lower() + ", "
        r += str(delay) + "),"
        r += "\n"
    r += "]\n"
    return r

class LiteDRAMNativePortCDC(Module):
    def __init__(self, port_from, port_to,
                 cmd_depth   = 4,
                 wdata_depth = 16,
                 rdata_depth = 16):
        assert port_from.address_width == port_to.address_width
        assert port_from.data_width    == port_to.data_width
        assert port_from.mode          == port_to.mode

        address_width     = port_from.address_width
        data_width        = port_from.data_width
        mode              = port_from.mode
        clock_domain_from = port_from.clock_domain
        clock_domain_to   = port_to.clock_domain

        cmd_fifo = AsyncFIFO(
            [("we", 1), ("addr", address_width)], cmd_depth)
        cmd_fifo = ClockDomainsRenamer(
            {"write": clock_domain_from,
             "read":  clock_domain_to})(cmd_fifo)
        self.submodules += cmd_fifo
        self.submodules += Pipeline(
            port_from.cmd, cmd_fifo, port_to.cmd)

        if mode == "write" or mode == "both":
            wdata_fifo = AsyncFIFO(
                [("data", data_width), ("we", data_width//8)], wdata_depth)
            wdata_fifo = ClockDomainsRenamer(
                {"write": clock_domain_from,
                 "read":  clock_domain_to})(wdata_fifo)
            self.submodules += wdata_fifo
            self.submodules += Pipeline(
                port_from.wdata, wdata_fifo, port_to.wdata)

        if mode == "read" or mode == "both":
            rdata_fifo = AsyncFIFO([("data", data_width)], rdata_depth)
            rdata_fifo = ClockDomainsRenamer(
                {"write": clock_domain_to,
                 "read":  clock_domain_from})(rdata_fifo)
            self.submodules += rdata_fifo
            self.submodules += Pipeline(
                port_to.rdata, rdata_fifo, port_from.rdata)

class LiteDRAMNativePortDownConverter(Module):
    """LiteDRAM port DownConverter

    This module reduces user port data width to fit controller data width.
    With N = port_from.data_width/port_to.data_width:
    - Address is adapted (multiplied by N + internal increments)
    - A write from the user is splitted and generates N writes to the
    controller.
    - A read from the user generates N reads to the controller and returned
      datas are regrouped in a single data presented to the user.
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    > port_to.data_width
        assert port_from.mode         == port_to.mode
        if port_from.data_width % port_to.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_from.data_width//port_to.data_width
        mode  = port_from.mode

        counter       = Signal(max=ratio)
        counter_reset = Signal()
        counter_ce    = Signal()
        self.sync += \
            If(counter_reset,
                counter.eq(0)
            ).Elif(counter_ce,
                counter.eq(counter + 1)
            )

        self.submodules.fsm = fsm = FSM(reset_state="IDLE")
        fsm.act("IDLE",
            counter_reset.eq(1),
            If(port_from.cmd.valid,
                NextState("CONVERT")
            )
        )
        fsm.act("CONVERT",
            port_to.cmd.valid.eq(1),
            port_to.cmd.we.eq(port_from.cmd.we),
            port_to.cmd.addr.eq(port_from.cmd.addr*ratio + counter),
            If(port_to.cmd.ready,
                counter_ce.eq(1),
                If(counter == ratio - 1,
                    port_from.cmd.ready.eq(1),
                    NextState("IDLE")
                )
            )
        )

        if mode == "write" or mode == "both":
            wdata_converter = StrideConverter(
                port_from.wdata.description,
                port_to.wdata.description,
                reverse=reverse)
            self.submodules += wdata_converter
            self.submodules += Pipeline(
                port_from.wdata, wdata_converter, port_to.wdata)

        if mode == "read" or mode == "both":
            rdata_converter = StrideConverter(
                port_to.rdata.description,
                port_from.rdata.description,
                reverse=reverse)
            self.submodules += rdata_converter
            self.submodules += Pipeline(
                port_to.rdata, rdata_converter, port_from.rdata)

class LiteDRAMNativeWritePortUpConverter(Module):
    # TODO: finish and remove hack
    """LiteDRAM write port UpConverter

    This module increase user port data width to fit controller data width.
    With N = port_to.data_width/port_from.data_width:
    - Address is adapted (divided by N)
    - N writes from user are regrouped in a single one to the controller
    (when possible, ie when consecutive and bursting)
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    < port_to.data_width
        assert port_from.mode         == port_to.mode
        assert port_from.mode         == "write"
        if port_to.data_width % port_from.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_to.data_width//port_from.data_width

        we      = Signal()
        address = Signal(port_to.address_width)

        counter       = Signal(max=ratio)
        counter_reset = Signal()
        counter_ce    = Signal()
        self.sync += \
            If(counter_reset,
                counter.eq(0)
            ).Elif(counter_ce,
                counter.eq(counter + 1)
            )

        self.submodules.fsm = fsm = FSM(reset_state="IDLE")
        fsm.act("IDLE",
            port_from.cmd.ready.eq(1),
            If(port_from.cmd.valid,
                counter_ce.eq(1),
                NextValue(we, port_from.cmd.we),
                NextValue(address, port_from.cmd.addr),
                NextState("RECEIVE")
            )
        )
        fsm.act("RECEIVE",
            port_from.cmd.ready.eq(1),
            If(port_from.cmd.valid,
                counter_ce.eq(1),
                If(counter == ratio-1,
                    NextState("GENERATE")
                )
            )
        )
        fsm.act("GENERATE",
            port_to.cmd.valid.eq(1),
            port_to.cmd.we.eq(we),
            port_to.cmd.addr.eq(address[log2_int(ratio):]),
            If(port_to.cmd.ready,
                NextState("IDLE")
            )
        )

        wdata_converter = StrideConverter(
            port_from.wdata.description,
            port_to.wdata.description,
            reverse=reverse)
        self.submodules += wdata_converter
        self.submodules += Pipeline(
            port_from.wdata,
            wdata_converter,
            port_to.wdata)

class LiteDRAMNativeReadPortUpConverter(Module):
    """LiteDRAM port UpConverter

    This module increase user port data width to fit controller data width.
    With N = port_to.data_width/port_from.data_width:
    - Address is adapted (divided by N)
    - N read from user are regrouped in a single one to the controller
    (when possible, ie when consecutive and bursting)
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    < port_to.data_width
        assert port_from.mode         == port_to.mode
        assert port_from.mode         == "read"
        if port_to.data_width % port_from.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_to.data_width//port_from.data_width

        # Command ----------------------------------------------------------------------------------
        cmd_buffer = SyncFIFO([("sel", ratio)], 4)
        self.submodules += cmd_buffer

        counter = Signal(max=ratio)
        counter_ce = Signal()
        self.sync += \
            If(counter_ce,
                counter.eq(counter + 1)
            )

        self.comb += \
            If(port_from.cmd.valid,
                If(counter == 0,
                    port_to.cmd.valid.eq(1),
                    port_to.cmd.addr.eq(port_from.cmd.addr[log2_int(ratio):]),
                    port_from.cmd.ready.eq(port_to.cmd.ready),
                    counter_ce.eq(port_to.cmd.ready)
                ).Else(
                    port_from.cmd.ready.eq(1),
                    counter_ce.eq(1)
                )
            )

        # TODO: fix sel
        self.comb += \
            If(port_to.cmd.valid & port_to.cmd.ready,
                cmd_buffer.sink.valid.eq(1),
                cmd_buffer.sink.sel.eq(2**ratio-1)
            )

        # Datapath ---------------------------------------------------------------------------------
        rdata_buffer    = Buffer(port_to.rdata.description)
        rdata_converter = StrideConverter(
            port_to.rdata.description,
            port_from.rdata.description,
            reverse=reverse)
        self.submodules +=  rdata_buffer, rdata_converter

        rdata_chunk       = Signal(ratio, reset=1)
        rdata_chunk_valid = Signal()
        self.sync += \
            If(rdata_converter.source.valid &
               rdata_converter.source.ready,
                rdata_chunk.eq(Cat(rdata_chunk[ratio-1], rdata_chunk[:ratio-1]))
            )

        self.comb += [
            port_to.rdata.connect(rdata_buffer.sink),
            rdata_buffer.source.connect(rdata_converter.sink),
            rdata_chunk_valid.eq((cmd_buffer.source.sel & rdata_chunk) != 0),
            If(port_from.flush,
                rdata_converter.source.ready.eq(1)
            ).Elif(cmd_buffer.source.valid,
                If(rdata_chunk_valid,
                    port_from.rdata.valid.eq(rdata_converter.source.valid),
                    port_from.rdata.data.eq(rdata_converter.source.data),
                    rdata_converter.source.ready.eq(port_from.rdata.ready)
                ).Else(
                    rdata_converter.source.ready.eq(1)
                )
            ),
            cmd_buffer.source.ready.eq(
                rdata_converter.source.ready & rdata_chunk[ratio-1])
        ]

class LiteDRAMNativePortConverter(Module):
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.mode         == port_to.mode

        mode = port_from.mode

        if port_from.data_width > port_to.data_width:
            converter = LiteDRAMNativePortDownConverter(port_from, port_to, reverse)
            self.submodules += converter
        elif port_from.data_width < port_to.data_width:
            if mode == "write":
                converter = LiteDRAMNativeWritePortUpConverter(port_from, port_to, reverse)
            elif mode == "read":
                converter = LiteDRAMNativeReadPortUpConverter(port_from, port_to, reverse)
            else:
                raise NotImplementedError
            self.submodules += converter
        else:
            self.comb += [
                port_from.cmd.connect(port_to.cmd),
                port_from.wdata.connect(port_to.wdata),
                port_to.rdata.connect(port_from.rdata)
            ]

class LiteDRAMWishbone2Native(Module):
    def __init__(self, wishbone, port, base_address=0x00000000):
        wishbone_data_width = len(wishbone.dat_w)
        port_data_width     = 2**int(log2(len(port.wdata.data))) # Round to lowest power 2
        assert wishbone_data_width >= port_data_width

        adr_offset = base_address >> log2_int(port.data_width//8)

        # Write Datapath ---------------------------------------------------------------------------
        wdata_converter = StrideConverter(
            [("data", wishbone_data_width), ("we", wishbone_data_width//8)],
            [("data", port_data_width),     ("we", port_data_width//8)],
        )
        self.submodules += wdata_converter
        self.comb += [
            wdata_converter.sink.valid.eq(wishbone.cyc & wishbone.stb & wishbone.we),
            wdata_converter.sink.data.eq(wishbone.dat_w),
            wdata_converter.sink.we.eq(wishbone.sel),
            wdata_converter.source.connect(port.wdata)
        ]

        # Read Datapath ----------------------------------------------------------------------------
        rdata_converter = StrideConverter(
            [("data", port_data_width)],
            [("data", wishbone_data_width)],
        )
        self.submodules += rdata_converter
        self.comb += [
            port.rdata.connect(rdata_converter.sink),
            rdata_converter.source.ready.eq(1),
            wishbone.dat_r.eq(rdata_converter.source.data),
        ]

        # Control ----------------------------------------------------------------------------------
        ratio = wishbone_data_width//port_data_width
        count = Signal(max=max(ratio, 2))
        self.submodules.fsm = fsm = FSM(reset_state="CMD")
        fsm.act("CMD",
            port.cmd.valid.eq(wishbone.cyc & wishbone.stb),
            port.cmd.we.eq(wishbone.we),
            port.cmd.addr.eq(wishbone.adr*ratio + count - adr_offset),
            If(port.cmd.valid & port.cmd.ready,
                NextValue(count, count + 1),
                If(count == (ratio - 1),
                    NextValue(count, 0),
                    If(wishbone.we,
                        NextState("WAIT-WRITE")
                    ).Else(
                        NextState("WAIT-READ")
                    )
                )
            )
        )
        fsm.act("WAIT-WRITE",
            If(wdata_converter.sink.ready,
                wishbone.ack.eq(1),
                NextState("CMD")
            )
        )
        fsm.act("WAIT-READ",
            If(rdata_converter.source.valid,
               wishbone.ack.eq(1),
               NextState("CMD")
            )
        )

_technology_timings = ["tREFI", "tWTR", "tCCD", "tRRD", "tZQCS"]

class _TechnologyTimings(Settings):
    def __init__(self, tREFI, tWTR, tCCD, tRRD, tZQCS=None):
        self.set_attributes(locals())

_speedgrade_timings = ["tRP", "tRCD", "tWR", "tRFC", "tFAW", "tRAS"]

class _SpeedgradeTimings(Settings):
    def __init__(self, tRP, tRCD, tWR, tRFC, tFAW, tRAS):
        self.set_attributes(locals())

def _read_field(byte, nbits, shift):
    mask = 2**nbits - 1
    return (byte & (mask << shift)) >> shift

def _twos_complement(value, nbits):
    if value & (1 << (nbits - 1)):
        value -= (1 << nbits)
    return value

def _word(msb, lsb):
    return (msb << 8) | lsb

# most signifficant (upper) / least signifficant (lower) nibble
def _msn(byte):
    return _read_field(byte, nbits=4, shift=4)

def _lsn(byte):
    return _read_field(byte, nbits=4, shift=0)

class SDRAMModule:
    """SDRAM module geometry and timings.

    SDRAM controller has to ensure that all geometry and
    timings parameters are fulfilled. Timings parameters
    can be expressed in ns, in SDRAM clock cycles or both
    and controller needs to use the greater value.

    SDRAM modules with the same geometry exist can have
    various speedgrades.
    """
    registered = False
    def __init__(self, clk_freq, rate, speedgrade=None, fine_refresh_mode=None):
        self.clk_freq      = clk_freq
        self.rate          = rate
        self.speedgrade    = speedgrade
        self.geom_settings = GeomSettings(
            bankbits = log2_int(self.nbanks),
            rowbits  = log2_int(self.nrows),
            colbits  = log2_int(self.ncols),
        )
        assert not (self.memtype != "DDR4" and fine_refresh_mode != None)
        assert fine_refresh_mode in [None, "1x", "2x", "4x"]
        if (fine_refresh_mode is None) and (self.memtype == "DDR4"):
            fine_refresh_mode = "1x"
        self.timing_settings = TimingSettings(
            tRP   = self.ns_to_cycles(self.get("tRP")),
            tRCD  = self.ns_to_cycles(self.get("tRCD")),
            tWR   = self.ns_to_cycles(self.get("tWR")),
            tREFI = self.ns_to_cycles(self.get("tREFI", fine_refresh_mode), False),
            tRFC  = self.ck_ns_to_cycles(*self.get("tRFC", fine_refresh_mode)),
            tWTR  = self.ck_ns_to_cycles(*self.get("tWTR")),
            tFAW  = None if self.get("tFAW") is None else self.ck_ns_to_cycles(*self.get("tFAW")),
            tCCD  = None if self.get("tCCD") is None else self.ck_ns_to_cycles(*self.get("tCCD")),
            tRRD  = None if self.get("tRRD") is None else self.ck_ns_to_cycles(*self.get("tRRD")),
            tRC   = None  if self.get("tRAS") is None else self.ns_to_cycles(self.get("tRP") + self.get("tRAS")),
            tRAS  = None if self.get("tRAS") is None else self.ns_to_cycles(self.get("tRAS")),
            tZQCS = None if self.get("tZQCS") is None else self.ck_ns_to_cycles(*self.get("tZQCS"))
        )
        self.timing_settings.fine_refresh_mode = fine_refresh_mode

    def get(self, name, key=None):
        r = None
        if name in _speedgrade_timings:
            if hasattr(self, "speedgrade_timings"):
                speedgrade = "default" if self.speedgrade is None else self.speedgrade
                r = getattr(self.speedgrade_timings[speedgrade], name)
            else:
                name = name + "_" + self.speedgrade if self.speedgrade is not None else name
                try:
                    r = getattr(self, name)
                except:
                    pass
        else:
            if hasattr(self, "technology_timings"):
                r = getattr(self.technology_timings, name)
            else:
                try:
                    r = getattr(self, name)
                except:
                    pass
        if (r is not None) and (key is not None):
            r = r[key]
        return r

    def ns_to_cycles(self, t, margin=True):
        clk_period_ns = 1e9/self.clk_freq
        if margin:
            margins = {
                "1:1" : 0,
                "1:2" : clk_period_ns/2,
                "1:4" : 3*clk_period_ns/4
            }
            t += margins[self.rate]
        return ceil(t/clk_period_ns)

    def ck_to_cycles(self, c):
        d = {
            "1:1" : 1,
            "1:2" : 2,
            "1:4" : 4
        }
        return ceil(c/d[self.rate])

    def ck_ns_to_cycles(self, c, t):
        c = 0 if c is None else c
        t = 0 if t is None else t
        return max(self.ck_to_cycles(c), self.ns_to_cycles(t))

class SDRAMRegisteredModule(SDRAMModule): registered = True

class DDR3Module(SDRAMModule):                     memtype = "DDR3"
class DDR3RegisteredModule(SDRAMRegisteredModule): memtype = "DDR3"

class MT41K64M16(DDR3Module):
    memtype = "DDR3"
    # geometry
    nbanks = 8
    nrows  = 8192
    ncols  = 1024
    # timings
    technology_timings = _TechnologyTimings(tREFI=64e6/8192, tWTR=(4, 7.5), tCCD=(4, None), tRRD=(4, 10), tZQCS=(64, 80))
    speedgrade_timings = {
        "800":  _SpeedgradeTimings(tRP=13.1,  tRCD=13.1,  tWR=13.1,  tRFC=(64,  None), tFAW=(None, 50), tRAS=37.5),
        "1066": _SpeedgradeTimings(tRP=13.1,  tRCD=13.1,  tWR=13.1,  tRFC=(86,  None), tFAW=(None, 50), tRAS=37.5),
        "1333": _SpeedgradeTimings(tRP=13.5,  tRCD=13.5,  tWR=13.5,  tRFC=(107, None), tFAW=(None, 45), tRAS=36),
        "1600": _SpeedgradeTimings(tRP=13.75, tRCD=13.75, tWR=13.75, tRFC=(128, None), tFAW=(None, 40), tRAS=35),
    }
    speedgrade_timings["default"] = speedgrade_timings["1600"]
