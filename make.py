#!/usr/bin/env python3

import argparse, inspect, logging, math, os, struct, subprocess

from shutil import which
from sysconfig import get_platform

from migen.fhdl.bitcontainer import log2_int, value_bits_sign
from migen.fhdl.module import Module
from migen.fhdl.simplify import FullMemoryWE
from migen.fhdl.specials import Instance, Memory, Tristate
from migen.fhdl.structure import ClockDomain, _Fragment, If, Signal

from migen.genlib.record import Record
from migen.genlib.resetsync import AsyncResetSynchronizer

from litex.build.io import CRG, DDRInput, DDROutput, SDRInput, SDROutput
#from litex.build.io import *

from litex.gen.fhdl import verilog

from litex.soc.cores.clock import ECP5PLL
from litex.soc.cores.timer import Timer
from litex.soc.interconnect import csr_bus, wishbone
from litex.soc.interconnect.csr import AutoCSR, CSRStatus, CSRStorage

from gateware.picorv32.core import PicoRV32

from gateware.litedram.core import LiteDRAMCore
from gateware.litedram.frontend import LiteDRAMWishbone2Native
from gateware.litedram.init import get_sdram_phy_c_header
from gateware.litedram.modules import MT41K64M16
from gateware.litedram.phy import ECP5DDRPHY

from gateware.valentyusb.cpu import CDCUsb
from gateware.valentyusb.io import IoBuf

def _language_by_filename(name):
    extension = name.rsplit(".")[-1]
    if extension in ["v", "vh", "vo"]:
        return "verilog"
    elif extension in ["vhd", "vhdl", "vho"]:
        return "vhdl"
    elif extension in ["sv"]:
        return "systemverilog"
    return None

def _write_file(filename, contents):
    old_contents = None
    if os.path.exists(filename):
        with open(filename, "r") as f:
            old_contents = f.read()
    if old_contents != contents:
        with open(filename, "w") as f:
            f.write(contents)

logging.basicConfig(level=logging.INFO)

def colorer(s, color="bright"):
    header  = {
        "bright": "\x1b[1m",
        "green":  "\x1b[32m",
        "cyan":   "\x1b[36m",
        "red":    "\x1b[31m",
        "yellow": "\x1b[33m",
        "underline": "\x1b[4m"}[color]
    trailer = "\x1b[0m"
    return header + str(s) + trailer

def SoCConstant(value):
    return value

class SoCRegion:
    def __init__(self, origin=None, size=None, mode="rw", cached=True, linker=False):
        self.logger    = logging.getLogger("SoCRegion")
        self.origin    = origin
        self.size      = size
        if size != 2**log2_int(size, False):
            self.logger.info("Region size {} internally from {} to {}.".format(
                colorer("rounded", color="cyan"),
                colorer("0x{:08x}".format(size)),
                colorer("0x{:08x}".format(2**log2_int(size, False)))))
        self.size_pow2 = 2**log2_int(size, False)
        self.mode      = mode
        self.cached    = cached
        self.linker    = linker

    def decoder(self, bus):
        origin = self.origin
        size   = self.size_pow2
        if (origin & (size - 1)) != 0:
            self.logger.error("Origin needs to be aligned on size:")
            self.logger.error(self)
            raise
        origin >>= int(math.log2(bus.data_width//8)) # bytes to words aligned
        size   >>= int(math.log2(bus.data_width//8)) # bytes to words aligned
        return lambda a: (a[log2_int(size):] == (origin >> log2_int(size)))

    def __str__(self):
        r = ""
        if self.origin is not None:
            r += "Origin: {}, ".format(colorer("0x{:08x}".format(self.origin)))
        if self.size is not None:
            r += "Size: {}, ".format(colorer("0x{:08x}".format(self.size)))
        r += "Mode: {}, ".format(colorer(self.mode.upper()))
        r += "Cached: {} ".format(colorer(self.cached))
        r += "Linker: {}".format(colorer(self.linker))
        return r

class SoCIORegion(SoCRegion): pass

class SoCCSRRegion:
    def __init__(self, origin, busword, obj):
        self.origin  = origin
        self.busword = busword
        self.obj     = obj

class SoCBusHandler(Module):
    supported_standard      = ["wishbone"]
    supported_data_width    = [32, 64]
    supported_address_width = [32]

    def __init__(self, standard, data_width=32, address_width=32, timeout=1e6, reserved_regions={}):
        self.logger = logging.getLogger("SoCBusHandler")

        # Check Standard
        if standard not in self.supported_standard:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Bus standard", color="red"),
                colorer(standard),
                colorer(", ".join(self.supported_standard))))
            raise

        # Check Data Width
        if data_width not in self.supported_data_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Data Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_data_width))))
            raise

        # Check Address Width
        if address_width not in self.supported_address_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Address Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_address_width))))
            raise

        # Create Bus
        self.standard      = standard
        self.data_width    = data_width
        self.address_width = address_width
        self.masters       = {}
        self.slaves        = {}
        self.regions       = {}
        self.io_regions    = {}
        self.timeout       = timeout
        self.logger.info("{}-bit {} Bus, {}GiB Address Space.".format(colorer(data_width), colorer(standard), colorer(2**address_width/2**30)))

        # Adding reserved regions
        for name, region in reserved_regions.items():
            if isinstance(region, int):
                region = SoCRegion(origin=region, size=0x1000000)
            self.add_region(name, region)

    def add_region(self, name, region):
        allocated = False
        if name in self.regions.keys() or name in self.io_regions.keys():
            self.logger.error("{} already declared as Region:".format(colorer(name, color="red")))
            self.logger.error(self)
            raise
        # Check if SoCIORegion
        if isinstance(region, SoCIORegion):
            self.io_regions[name] = region
            overlap = self.check_regions_overlap(self.io_regions)
            if overlap is not None:
                self.logger.error("IO Region {} between {} and {}:".format(colorer("overlap", color="red"), colorer(overlap[0]), colorer(overlap[1])))
                self.logger.error(str(self.io_regions[overlap[0]]))
                self.logger.error(str(self.io_regions[overlap[1]]))
                raise
            self.logger.info("{} Region {} at {}.".format(colorer(name, color="underline"), colorer("added", color="green"), str(region)))
        # Check if SoCRegion
        elif isinstance(region, SoCRegion):
            # If no origin specified, allocate region.
            if region.origin is None:
                allocated = True
                region    = self.alloc_region(name, region.size, region.cached)
                self.regions[name] = region
            # Else add region and check for overlaps.
            else:
                if not region.cached:
                    if not self.check_region_is_io(region):
                        self.logger.error("{} Region {}: {}.".format(
                            colorer(name),
                            colorer("not in IO region", color="red"),
                            str(region)))
                        self.logger.error(self)
                        raise
                self.regions[name] = region
                overlap = self.check_regions_overlap(self.regions)
                if overlap is not None:
                    self.logger.error("Region {} between {} and {}:".format(
                        colorer("overlap", color="red"),
                        colorer(overlap[0]),
                        colorer(overlap[1])))
                    self.logger.error(str(self.regions[overlap[0]]))
                    self.logger.error(str(self.regions[overlap[1]]))
                    raise
            self.logger.info("{} Region {} at {}.".format(
                colorer(name, color="underline"),
                colorer("allocated" if allocated else "added", color="cyan" if allocated else "green"),
                str(region)))
        else:
            self.logger.error("{} is not a supported Region.".format(colorer(name, color="red")))
            raise

    def alloc_region(self, name, size, cached=True):
        self.logger.info("Allocating {} Region of size {}...".format(colorer("Cached" if cached else "IO"), colorer("0x{:08x}".format(size))))

        # Limit Search Regions
        if cached == False:
            search_regions = self.io_regions
        else:
            search_regions = {"main": SoCRegion(origin=0x00000000, size=2**self.address_width-1)}

        # Iterate on Search_Regions to find a Candidate
        for _, search_region in search_regions.items():
            origin = search_region.origin
            while (origin + size) < (search_region.origin + search_region.size_pow2):
                # Create a Candicate.
                candidate = SoCRegion(origin=origin, size=size, cached=cached)
                overlap   = False
                # Check Candidate does not overlap with allocated existing regions
                for _, allocated in self.regions.items():
                    if self.check_regions_overlap({"0": allocated, "1": candidate}) is not None:
                        origin  = allocated.origin + allocated.size_pow2
                        overlap = True
                        break
                if not overlap:
                    # If no overlap, the Candidate is selected
                    return candidate

        self.logger.error("Not enough Address Space to allocate Region.")
        raise

    def check_regions_overlap(self, regions, check_linker=False):
        i = 0
        while i < len(regions):
            n0 =  list(regions.keys())[i]
            r0 = regions[n0]
            for n1 in list(regions.keys())[i+1:]:
                r1 = regions[n1]
                if r0.linker or r1.linker:
                    if not check_linker:
                        continue
                if r0.origin >= (r1.origin + r1.size_pow2):
                    continue
                if r1.origin >= (r0.origin + r0.size_pow2):
                    continue
                return (n0, n1)
            i += 1
        return None

    def check_region_is_in(self, region, container):
        is_in = True
        if not (region.origin >= container.origin):
            is_in = False
        if not ((region.origin + region.size) < (container.origin + container.size)):
            is_in = False
        return is_in

    def check_region_is_io(self, region):
        is_io = False
        for _, io_region in self.io_regions.items():
            if self.check_region_is_in(region, io_region):
                is_io = True
        return is_io

    def add_adapter(self, name, interface, direction="m2s"):
        assert direction in ["m2s", "s2m"]

        if isinstance(interface, wishbone.Interface):
            new_interface = wishbone.Interface(data_width=self.data_width)
            if direction == "m2s":
                converter = wishbone.Converter(master=interface, slave=new_interface)
            if direction == "s2m":
                converter = wishbone.Converter(master=new_interface, slave=interface)
            self.submodules += converter
        else:
            raise TypeError(interface)

        fmt = "{name} Bus {converted} from {frombus} {frombits}-bit to {tobus} {tobits}-bit."
        frombus  = "Wishbone" if isinstance(interface, wishbone.Interface) else "AXILite"
        tobus    = "Wishbone" if isinstance(new_interface, wishbone.Interface) else "AXILite"
        frombits = interface.data_width
        tobits   = new_interface.data_width
        if frombus != tobus or frombits != tobits:
            self.logger.info(fmt.format(
                name      = colorer(name),
                converted = colorer("converted", color="cyan"),
                frombus   = colorer("Wishbone" if isinstance(interface, wishbone.Interface) else "AXILite"),
                frombits  = colorer(interface.data_width),
                tobus     = colorer("Wishbone" if isinstance(new_interface, wishbone.Interface) else "AXILite"),
                tobits    = colorer(new_interface.data_width)))
        return new_interface

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            self.logger.error("{} {} as Bus Master:".format(
                colorer(name),
                colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        master = self.add_adapter(name, master, "m2s")
        self.masters[name] = master
        self.logger.info("{} {} as Bus Master.".format(
            colorer(name,    color="underline"),
            colorer("added", color="green")))

    def add_slave(self, name=None, slave=None, region=None):
        no_name   = name is None
        no_region = region is None
        if no_name and no_region:
            self.logger.error("Please {} {} or/and {} of Bus Slave.".format(
                colorer("specify", color="red"),
                colorer("name"),
                colorer("region")))
            raise
        if no_name:
            name = "slave{:d}".format(len(self.slaves))
        if no_region:
            region = self.regions.get(name, None)
            if region is None:
                self.logger.error("{} Region {}.".format(
                    colorer(name),
                    colorer("not found", color="red")))
                raise
        else:
             self.add_region(name, region)
        if name in self.slaves.keys():
            self.logger.error("{} {} as Bus Slave:".format(
                colorer(name),
                colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        slave = self.add_adapter(name, slave, "s2m")
        self.slaves[name] = slave
        self.logger.info("{} {} as Bus Slave.".format(
            colorer(name, color="underline"),
            colorer("added", color="green")))

    def __str__(self):
        r = "{}-bit {} Bus, {}GiB Address Space.\n".format(
            colorer(self.data_width), colorer(self.standard), colorer(2**self.address_width/2**30))
        r += "IO Regions: ({})\n".format(len(self.io_regions.keys())) if len(self.io_regions.keys()) else ""
        io_regions = {k: v for k, v in sorted(self.io_regions.items(), key=lambda item: item[1].origin)}
        for name, region in io_regions.items():
           r += colorer(name, color="underline") + " "*(20-len(name)) + ": " + str(region) + "\n"
        r += "Bus Regions: ({})\n".format(len(self.regions.keys())) if len(self.regions.keys()) else ""
        regions = {k: v for k, v in sorted(self.regions.items(), key=lambda item: item[1].origin)}
        for name, region in regions.items():
           r += colorer(name, color="underline") + " "*(20-len(name)) + ": " + str(region) + "\n"
        r += "Bus Masters: ({})\n".format(len(self.masters.keys())) if len(self.masters.keys()) else ""
        for name in self.masters.keys():
           r += "- {}\n".format(colorer(name, color="underline"))
        r += "Bus Slaves: ({})\n".format(len(self.slaves.keys())) if len(self.slaves.keys()) else ""
        for name in self.slaves.keys():
           r += "- {}\n".format(colorer(name, color="underline"))
        r = r[:-1]
        return r

class SoCLocHandler(Module):
    def __init__(self, name, n_locs):
        self.name   = name
        self.locs   = {}
        self.n_locs = n_locs

    def add(self, name, n=None, use_loc_if_exists=False):
        allocated = False
        if not (use_loc_if_exists and name in self.locs.keys()):
            if name in self.locs.keys():
                self.logger.error("{} {} name {}.".format(colorer(name), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n in self.locs.values():
                self.logger.error("{} {} Location {}.".format(colorer(n), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n is None:
                allocated = True
                n = self.alloc(name)
            else:
                if n < 0:
                    self.logger.error("{} {} Location should be {}.".format(colorer(n), self.name, colorer("positive", color="red")))
                    raise
                if n > self.n_locs:
                    self.logger.error("{} {} Location {} than maximum: {}.".format(colorer(n), self.name, colorer("higher", color="red"), colorer(self.n_locs)))
                    raise
            self.locs[name] = n
        else:
            n = self.locs[name]
        self.logger.info("{} {} {} at Location {}.".format(
            colorer(name, color="underline"),
            self.name,
            colorer("allocated" if allocated else "added", color="cyan" if allocated else "green"),
            colorer(n)))

    def alloc(self, name):
        for n in range(self.n_locs):
            if n not in self.locs.values():
                return n
        self.logger.error("Not enough Locations.")
        self.logger.error(self)
        raise

    def __str__(self):
        r = "{} Locations: ({})\n".format(self.name, len(self.locs.keys())) if len(self.locs.keys()) else ""
        locs = {k: v for k, v in sorted(self.locs.items(), key=lambda item: item[1])}
        length = 0
        for name in locs.keys():
            if len(name) > length: length = len(name)
        for name in locs.keys():
           r += "- {}{}: {}\n".format(colorer(name, color="underline"), " "*(length + 1 - len(name)), colorer(self.locs[name]))
        return r

class SoCCSRHandler(SoCLocHandler):
    supported_data_width    = [8, 32]
    supported_address_width = [14+i for i in range(4)]
    supported_alignment     = [32]
    supported_paging        = [0x800*2**i for i in range(4)]

    def __init__(self, data_width=32, address_width=14, alignment=32, paging=0x800, reserved_csrs={}):
        SoCLocHandler.__init__(self, "CSR", n_locs=alignment // 8 * (2**address_width) // paging)
        self.logger = logging.getLogger("SoCCSRHandler")

        # Check Data Width
        if data_width not in self.supported_data_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Data Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_data_width))))
            raise

        # Check Address Width
        if address_width not in self.supported_address_width:
            self.logger.error("Unsupported {} {} supporteds: {:s}".format(
                colorer("Address Width", color="red"),
                colorer(address_width),
                colorer(", ".join(str(x) for x in self.supported_address_width))))
            raise

        # Check Alignment
        if alignment not in self.supported_alignment:
            self.logger.error("Unsupported {}: {} supporteds: {:s}".format(
                colorer("Alignment", color="red"),
                colorer(alignment),
                colorer(", ".join(str(x) for x in self.supported_alignment))))
            raise
        if data_width > alignment:
            self.logger.error("Alignment ({}) {} Data Width ({})".format(
                colorer(alignment),
                colorer("should be >=", color="red"),
                colorer(data_width)))
            raise

        # Check Paging
        if paging not in self.supported_paging:
            self.logger.error("Unsupported {} 0x{}, supporteds: {:s}".format(
                colorer("Paging", color="red"),
                colorer("{:x}".format(paging)),
                colorer(", ".join("0x{:x}".format(x) for x in self.supported_paging))))
            raise

        # Create CSR Handler
        self.data_width    = data_width
        self.address_width = address_width
        self.alignment     = alignment
        self.paging        = paging
        self.masters       = {}
        self.regions       = {}
        self.logger.info("{}-bit CSR Bus, {}-bit Aligned, {}KiB Address Space, {}B Paging (Up to {} Locations).".format(
            colorer(self.data_width),
            colorer(self.alignment),
            colorer(2**self.address_width/2**10),
            colorer(self.paging),
            colorer(self.n_locs)))

        # Adding reserved CSRs
        for name, n in reserved_csrs.items():
            self.add(name, n)

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            self.logger.error("{} {} as CSR Master:".format(colorer(name), colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        if master.data_width != self.data_width:
            self.logger.error("{} Master/Handler Data Width {} ({} vs {}).".format(
                colorer(name),
                colorer("missmatch", color="red"),
                colorer(master.data_width),
                colorer(self.data_width)))
            raise
        self.masters[name] = master
        self.logger.info("{} {} as CSR Master.".format(colorer(name, color="underline"), colorer("added", color="green")))

    def add_region(self, name, region):
        # FIXME: add checks
        self.regions[name] = region

    def address_map(self, name, memory):
        if memory is not None:
            name = name + "_" + memory.name_override
        if self.locs.get(name, None) is None:
            self.logger.error("CSR {} {}.".format(colorer(name), colorer("not found", color="red")))
            self.logger.error(self)
            raise
        return self.locs[name]

    def __str__(self):
        r = "{}-bit CSR Bus, {}-bit Aligned, {}KiB Address Space, {}B Paging (Up to {} Locations).\n".format(
            colorer(self.data_width),
            colorer(self.alignment),
            colorer(2**self.address_width/2**10),
            colorer(self.paging),
            colorer(self.n_locs))
        r += SoCLocHandler.__str__(self)
        r = r[:-1]
        return r

class SoCIRQHandler(SoCLocHandler):
    def __init__(self, n_irqs=32, reserved_irqs={}):
        SoCLocHandler.__init__(self, "IRQ", n_locs=n_irqs)
        self.logger = logging.getLogger("SoCIRQHandler")

        # Check IRQ Number
        if n_irqs > 32:
            self.logger.error("Unsupported IRQs number: {} supporteds: {:s}".format(colorer(n, color="red"), colorer("Up to 32", color="green")))
            raise

        # Adding reserved IRQs
        for name, n in reserved_irqs.items():
            self.add(name, n)

    def __str__(self):
        r ="IRQ Handler (up to {} Locations).\n".format(colorer(self.n_locs))
        r += SoCLocHandler.__str__(self)
        r = r[:-1]
        return r

class SoCController(Module, AutoCSR):
    def __init__(self, with_reset = True, with_scratch = True, with_errors = True):

        if with_reset:
            self._reset = CSRStorage(1, description="""Write a ``1`` to this register to reset the SoC.""")
        if with_scratch:
            self._scratch = CSRStorage(32, reset=0x12345678, description="""
                Use this register as a scratch space to verify that software read/write accesses
                to the Wishbone/CSR bus are working correctly. The initial reset value of 0x1234578
                can be used to verify endianness.""")
        if with_errors:
            self._bus_errors = CSRStatus(32, description="Total number of Wishbone bus errors (timeouts) since start.")

        # Reset
        if with_reset:
            self.reset = Signal()
            self.comb += self.reset.eq(self._reset.re)

        # Errors
        if with_errors:
            self.bus_error = Signal()
            bus_errors     = Signal(32)
            self.sync += [
                If(bus_errors != (2**len(bus_errors)-1),
                    If(self.bus_error, bus_errors.eq(bus_errors + 1))
                )
            ]
            self.comb += self._bus_errors.status.eq(bus_errors)

class ConstraintError(Exception):
    pass

class Pins:
    def __init__(self, *identifiers):
        self.identifiers = []
        for i in identifiers:
            if isinstance(i, int):
                self.identifiers += ["X"]*i
            else:
                self.identifiers += i.split()

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, " ".join(self.identifiers))

class IOStandard:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, self.name)

class Drive:
    def __init__(self, strength):
        self.strength = strength

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, self.strength)

class Misc:
    def __init__(self, misc):
        self.misc = misc

    def __repr__(self):
        return "{}({})".format(self.__class__.__name__, repr(self.misc))

class Inverted:
    def __repr__(self):
        return "{}()".format(self.__class__.__name__)

class Subsignal:
    def __init__(self, name, *constraints):
        self.name = name
        self.constraints = list(constraints)

    def __repr__(self):
        return "{}('{}', {})".format(self.__class__.__name__, self.name, ", ".join([repr(constr) for constr in self.constraints]))

class PlatformInfo:
    def __init__(self, info):
        self.info = info

    def __repr__(self):
        return "{}({})".format(self.__class__.__name__, repr(self.info))

def _format_constraint(c):
    if isinstance(c, Pins):
        return ("LOCATE COMP ", " SITE " + "\"" + c.identifiers[0] + "\"")
    elif isinstance(c, IOStandard):
        return ("IOBUF PORT ", " IO_TYPE=" + c.name)
    elif isinstance(c, Misc):
        return ("IOBUF PORT ", " " + c.misc)

def _format_lpf(signame, pin, others, resname):
    fmt_c = [_format_constraint(c) for c in ([Pins(pin)] + others)]
    lpf = []
    for pre, suf in fmt_c:
        lpf.append(pre + "\"" + signame + "\"" + suf + ";")
    return "\n".join(lpf)

def _build_lpf(named_sc, named_pc, build_name):
    lpf = []
    lpf.append("BLOCK RESETPATHS;")
    lpf.append("BLOCK ASYNCPATHS;")
    for sig, pins, others, resname in named_sc:
        if len(pins) > 1:
            for i, p in enumerate(pins):
                lpf.append(_format_lpf(sig + "[" + str(i) + "]", p, others, resname))
        else:
            lpf.append(_format_lpf(sig, pins[0], others, resname))
    if named_pc:
        lpf.append("\n\n".join(named_pc))
    _write_file(build_name + ".lpf", "\n".join(lpf))

_yosys_template = [
    "verilog_defaults -push",
    "verilog_defaults -add -defer",
    "{read_files}",
    "verilog_defaults -pop",
    "attrmap -tocase keep -imap keep=\"true\" keep=1 -imap keep=\"false\" keep=0 -remove keep=0",
    "synth_ecp5 -abc9 {nwl} -json {build_name}.json -top {build_name}",
]

def _yosys_import_sources(platform):
    includes = ""
    reads = []
    for path in platform.verilog_include_paths:
        includes += " -I" + path
    for filename, language, library in platform.sources:
        reads.append("read_{}{} {}".format(
            language, includes, filename))
    return "\n".join(reads)

def _build_yosys(template, platform, nowidelut, build_name):
    ys = []
    for l in template:
        ys.append(l.format(
            build_name = build_name,
            nwl        = "-nowidelut" if nowidelut else "",
            read_files = _yosys_import_sources(platform)
        ))
    _write_file(build_name + ".ys", "\n".join(ys))

def nextpnr_ecp5_parse_device(device):
    device      = device.lower()
    family      = device.split("-")[0]
    size        = device.split("-")[1]
    speed_grade = device.split("-")[2][0]
    if speed_grade not in ["6", "7", "8"]:
       raise ValueError("Invalid speed grade {}".format(speed_grade))
    package     = device.split("-")[2][1:]
    if "256" in package:
        package = "CABGA256"
    elif "285" in package:
        package = "CSFBGA285"
    elif "381" in package:
        package = "CABGA381"
    elif "554" in package:
        package = "CABGA554"
    elif "756" in package:
        package = "CABGA756"
    else:
       raise ValueError("Invalid package {}".format(package))
    return (family, size, speed_grade, package)

nextpnr_ecp5_architectures = {
    "lfe5u-12f"   : "12k",
    "lfe5u-25f"   : "25k",
    "lfe5u-45f"   : "45k",
    "lfe5u-85f"   : "85k",
    "lfe5um-25f"  : "um-25k",
    "lfe5um-45f"  : "um-45k",
    "lfe5um-85f"  : "um-85k",
    "lfe5um5g-25f": "um5g-25k",
    "lfe5um5g-45f": "um5g-45k",
    "lfe5um5g-85f": "um5g-85k",
}

_build_template = [
    "yosys {build_name}.ys",
    "nextpnr-ecp5 --json {build_name}.json --lpf {build_name}.lpf --textcfg {build_name}.config  \
    --{architecture} --package {package} --speed {speed_grade} {timefailarg} {ignoreloops} --seed {seed}",
    "ecppack {build_name}.config --bit {build_name}.bit --bootaddr {bootaddr}"
]

def _build_script(source, build_template, build_name, architecture, package, speed_grade, timingstrict, ignoreloops, bootaddr, seed):
    s = "set -e\n"

    for line in build_template:
        s += (line + "\n").format(
            build_name   = build_name,
            architecture = architecture,
            package      = package,
            speed_grade  = speed_grade,
            timefailarg  = "--timing-allow-fail" if not timingstrict else "",
            ignoreloops  = "--ignore-loops" if ignoreloops else "",
            bootaddr     = bootaddr,
            seed         = seed)

    script_file = "build.sh"
    _write_file(script_file, s)

    return script_file

class LatticeECP5AsyncResetSynchronizerImpl(Module):
    def __init__(self, cd, async_reset):
        rst1 = Signal()
        self.specials += [
            Instance("FD1S3BX",
                i_D  = 0,
                i_PD = async_reset,
                i_CK = cd.clk,
                o_Q  = rst1),
            Instance("FD1S3BX",
                i_D  = rst1,
                i_PD = async_reset,
                i_CK = cd.clk,
                o_Q  = cd.rst)
        ]

class LatticeECP5AsyncResetSynchronizer:
    @staticmethod
    def lower(dr):
        return LatticeECP5AsyncResetSynchronizerImpl(dr.cd, dr.async_reset)

class LatticeECP5SDRInputImpl(Module):
    def __init__(self, i, o, clk):
        self.specials += Instance("IFS1P3BX",
            i_SCLK = clk,
            i_PD   = 0,
            i_SP   = 1,
            i_D    = i,
            o_Q    = o,
        )

class LatticeECP5SDRInput:
    @staticmethod
    def lower(dr):
        return LatticeECP5SDRInputImpl(dr.i, dr.o, dr.clk)

class LatticeECP5SDROutputImpl(Module):
    def __init__(self, i, o, clk):
        self.specials += Instance("OFS1P3BX",
            i_SCLK = clk,
            i_PD   = 0,
            i_SP   = 1,
            i_D    = i,
            o_Q    = o,
        )

class LatticeECP5SDROutput:
    @staticmethod
    def lower(dr):
        return LatticeECP5SDROutputImpl(dr.i, dr.o, dr.clk)

class LatticeECP5DDRInputImpl(Module):
    def __init__(self, i, o1, o2, clk):
        self.specials += Instance("IDDRX1F",
            i_SCLK = clk,
            i_D    = i,
            o_Q0   = o1,
            o_Q1   = o2,
        )

class LatticeECP5DDRInput:
    @staticmethod
    def lower(dr):
        return LatticeECP5DDRInputImpl(dr.i, dr.o1, dr.o2, dr.clk)

class LatticeECP5DDROutputImpl(Module):
    def __init__(self, i1, i2, o, clk):
        self.specials += Instance("ODDRX1F",
            i_SCLK = clk,
            i_D0   = i1,
            i_D1   = i2,
            o_Q    = o,
        )

class LatticeECP5DDROutput:
    @staticmethod
    def lower(dr):
        return LatticeECP5DDROutputImpl(dr.i1, dr.i2, dr.o, dr.clk)

class LatticeECP5TrellisTristateImpl(Module):
    def __init__(self, io, o, oe, i):
        nbits, sign = value_bits_sign(io)
        for bit in range(nbits):
            self.specials += Instance("TRELLIS_IO",
                p_DIR = "BIDIR",
                i_B   = io[bit] if nbits > 1 else io,
                i_I   = o[bit]  if nbits > 1 else o,
                o_O   = i[bit]  if nbits > 1 else i,
                i_T   = ~oe
            )

class LatticeECP5TrellisTristate(Module):
    @staticmethod
    def lower(dr):
        return LatticeECP5TrellisTristateImpl(dr.target, dr.o, dr.oe, dr.i)

lattice_ecp5_trellis_special_overrides = {
    AsyncResetSynchronizer: LatticeECP5AsyncResetSynchronizer,
    Tristate:               LatticeECP5TrellisTristate,
    SDRInput:               LatticeECP5SDRInput,
    SDROutput:              LatticeECP5SDROutput,
    DDRInput:               LatticeECP5DDRInput,
    DDROutput:              LatticeECP5DDROutput
}

class LatticeTrellisToolchain:
    attr_translate = {
        "keep": ("keep", "true"),
        "no_retiming":      None,
        "async_reg":        None,
        "mr_ff":            None,
        "mr_false_path":    None,
        "ars_ff1":          None,
        "ars_ff2":          None,
        "ars_false_path":   None,
        "no_shreg_extract": None
    }

    special_overrides = lattice_ecp5_trellis_special_overrides

    def __init__(self):
        self.yosys_template = _yosys_template
        self.build_template = _build_template
        self.false_paths = set() # FIXME: use it

    def build(self, platform, fragment,
        build_dir      = "build",
        build_name     = "top",
        run            = True,
        nowidelut      = False,
        timingstrict   = False,
        ignoreloops    = False,
        bootaddr       = 0,
        seed           = 1):

        # Create build directory
        os.makedirs(build_dir, exist_ok=True)
        cwd = os.getcwd()
        os.chdir(build_dir)

        # Finalize design
        if not isinstance(fragment, _Fragment):
            fragment = fragment.get_fragment()
        platform.finalize(fragment)

        # Generate verilog
        v_output = platform.get_verilog(fragment, name=build_name)
        named_sc, named_pc = platform.resolve_signals(v_output.ns)
        top_file = build_name + ".v"
        v_output.write(top_file)
        platform.add_source(top_file)

        # Generate design constraints file (.lpf)
        _build_lpf(named_sc, named_pc, build_name)

        # Generate Yosys script
        _build_yosys(self.yosys_template, platform, nowidelut, build_name)

        # Translate device to Nextpnr architecture/package/speed_grade
        (family, size, speed_grade, package) = nextpnr_ecp5_parse_device(platform.device)
        architecture = nextpnr_ecp5_architectures[(family + "-" + size)]

        # Generate build script
        script = _build_script(False, self.build_template, build_name, architecture, package, speed_grade, timingstrict, ignoreloops, bootaddr, seed)
        # Run
        if run:
            if subprocess.call(["bash"] + [script]) != 0:
                raise OSError("Subprocess failed")

        os.chdir(cwd)

        return v_output.ns

    def add_period_constraint(self, platform, clk, period):
        platform.add_platform_command("""FREQUENCY PORT "{clk}" {freq} MHz;""".format(freq=str(float(1 / period) * 1000), clk="{clk}"), clk=clk)

def _lookup(description, name, number):
    for resource in description:
        if resource[0] == name and (number is None or resource[1] == number):
            return resource
    raise ConstraintError("Resource not found: {}:{}".format(name, number))

def _resource_type(resource):
    t = None
    i = None
    for element in resource[2:]:
        if isinstance(element, Pins):
            assert(t is None)
            t = len(element.identifiers)
        elif isinstance(element, Subsignal):
            if t is None:
                t = []
            if i is None:
                i = []

            assert(isinstance(t, list))
            n_bits = None
            inverted = False
            for c in element.constraints:
                if isinstance(c, Pins):
                    assert(n_bits is None)
                    n_bits = len(c.identifiers)
                if isinstance(c, Inverted):
                    inverted = True

            t.append((element.name, n_bits))
            i.append((element.name, inverted))

    return t, i

class ConnectorManager:
    def __init__(self, connectors):
        self.connector_table = dict()
        for connector in connectors:
            cit = iter(connector)
            conn_name = next(cit)
            if isinstance(connector[1], str):
                pin_list = []
                for pins in cit:
                    pin_list += pins.split()
                pin_list = [None if pin == "None" else pin for pin in pin_list]
            elif isinstance(connector[1], dict):
                pin_list = connector[1]
            else:
                raise ValueError("Unsupported pin list type {} for connector {}".format(type(connector[1]), conn_name))
            if conn_name in self.connector_table:
                raise ValueError("Connector specified more than once: {}".format(conn_name))

            self.connector_table[conn_name] = pin_list

    def resolve_identifiers(self, identifiers):
        r = []
        for identifier in identifiers:
            if ":" in identifier:
                conn, pn = identifier.split(":")
                if pn.isdigit():
                    pn = int(pn)

                r.append(self.connector_table[conn][pn])
            else:
                r.append(identifier)

        return r

def _separate_pins(constraints):
    pins = None
    others = []
    for c in constraints:
        if isinstance(c, Pins):
            assert(pins is None)
            pins = c.identifiers
        else:
            others.append(c)

    return pins, others

class ConstraintManager:
    def __init__(self, io, connectors):
        self.available = list(io)
        self.matched = []
        self.platform_commands = []
        self.connector_manager = ConnectorManager(connectors)

    def request(self, name, number=None):
        resource = _lookup(self.available, name, number)
        rt, ri = _resource_type(resource)
        if number is None:
            resource_name = name
        else:
            resource_name = name + str(number)
        if isinstance(rt, int):
            obj = Signal(rt, name_override=resource_name)
        else:
            obj = Record(rt, name=resource_name)
            for name, inverted in ri:
                if inverted:
                    getattr(obj, name).inverted = True

        for element in resource[2:]:
            if isinstance(element, Inverted):
                if isinstance(obj, Signal):
                    obj.inverted = True
            if isinstance(element, PlatformInfo):
                obj.platform_info = element.info
                break

        self.available.remove(resource)
        self.matched.append((resource, obj))
        return obj

    def lookup_request(self, name, number=None, loose=False):
        subname = None
        if ":" in name: name, subname = name.split(":")
        for resource, obj in self.matched:
            if resource[0] == name and (number is None or resource[1] == number):
                if subname is not None:
                    return getattr(obj, subname)
                else:
                    return obj

        if loose:
            return None
        else:
            raise ConstraintError("Resource not found: {}:{}".format(name, number))

    def add_platform_command(self, command, **signals):
        self.platform_commands.append((command, signals))

    def get_io_signals(self):
        r = set()
        for resource, obj in self.matched:
            if isinstance(obj, Signal):
                r.add(obj)
            else:
                r.update(obj.flatten())

        return r

    def get_sig_constraints(self):
        r = []
        for resource, obj in self.matched:
            name = resource[0]
            number = resource[1]
            has_subsignals = False
            top_constraints = []
            for element in resource[2:]:
                if isinstance(element, Subsignal):
                    has_subsignals = True
                else:
                    top_constraints.append(element)

            if has_subsignals:
                for element in resource[2:]:
                    if isinstance(element, Subsignal):
                        sig = getattr(obj, element.name)
                        pins, others = _separate_pins(top_constraints + element.constraints)
                        pins = self.connector_manager.resolve_identifiers(pins)
                        r.append((sig, pins, others, (name, number, element.name)))
            else:
                pins, others = _separate_pins(top_constraints)
                pins = self.connector_manager.resolve_identifiers(pins)
                r.append((obj, pins, others, (name, number, None)))

        return r

    def get_platform_commands(self):
        return self.platform_commands

_io_r0_2 = [
    ("clk48", 0, Pins("A9"),  IOStandard("LVCMOS33")),
    ("rst_n", 0, Pins("V17"), IOStandard("LVCMOS33")),

    ("usr_btn", 0, Pins("J17"), IOStandard("SSTL135_I")),

    ("ddram", 0,
        Subsignal("a",       Pins("C4 D2 D3 A3 A4 D4 C3 B2", "B1 D1 A7 C2 B6 C1 A2 C7"),                 IOStandard("SSTL135_I")),
        Subsignal("ba",      Pins("D6 B7 A6"),                                                           IOStandard("SSTL135_I"),),
        Subsignal("ras_n",   Pins("C12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("cas_n",   Pins("D13"),                                                                IOStandard("SSTL135_I")),
        Subsignal("we_n",    Pins("B12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("cs_n",    Pins("A12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("dm",      Pins("D16 G16"),                                                            IOStandard("SSTL135_I")),
        Subsignal("dq",      Pins("C17 D15 B17 C16 A15 B13 A17 A13", "F17 F16 G15 F15 J16 C18 H16 F18"), IOStandard("SSTL135_I"),  Misc("TERMINATION=75")),
        Subsignal("dqs_p",   Pins("B15 G18"),                                                            IOStandard("SSTL135D_I"), Misc("TERMINATION=OFF"), Misc("DIFFRESISTOR=100")),
        Subsignal("clk_p",   Pins("J18"),                                                                IOStandard("SSTL135D_I")),
        Subsignal("cke",     Pins("D18"),                                                                IOStandard("SSTL135_I")),
        Subsignal("odt",     Pins("C13"),                                                                IOStandard("SSTL135_I")),
        Subsignal("reset_n", Pins("L18"),                                                                IOStandard("SSTL135_I")),
        Subsignal("vccio",   Pins("K16 D17 K15 K17 B18 C6"),                                             IOStandard("SSTL135_II")),
        Subsignal("gnd",     Pins("L15 L16"),                                                            IOStandard("SSTL135_II")),
        Misc("SLEWRATE=FAST")
    ),

    ("usb", 0,
        Subsignal("d_p",    Pins("N1")),
        Subsignal("d_n",    Pins("M2")),
        Subsignal("pullup", Pins("N2")),
        IOStandard("LVCMOS33")
    ),
]

_connectors_r0_2 = [
    ("GPIO", "N17 M18 C10 C9 - B10 B9 - - C8 B8 A8 H2 J2 N15 R17 N16 - L4 N3 N4 H4 G4 T17"),
]

class _CRG(Module):
    def __init__(self, platform, sys_clk_freq):
        self.clock_domains.cd_init     = ClockDomain()
        self.clock_domains.cd_por      = ClockDomain(reset_less=True)
        self.clock_domains.cd_sys      = ClockDomain()
        self.clock_domains.cd_sys2x    = ClockDomain()
        self.clock_domains.cd_sys2x_i  = ClockDomain(reset_less=True)
        self.clock_domains.cd_sys2x_eb = ClockDomain(reset_less=True)

        self.stop  = Signal()
        self.reset = Signal()

        clk48 = platform.request("clk48")
        rst_n = platform.request("usr_btn")

        por_count = Signal(16, reset=2**16-1)
        por_done  = Signal()
        self.comb += self.cd_por.clk.eq(clk48)
        self.comb += por_done.eq(por_count == 0)
        self.sync.por += If(~por_done, por_count.eq(por_count - 1))

        sys2x_clk_ecsout = Signal()
        self.submodules.pll = pll = ECP5PLL()
        pll.register_clkin(clk48, 48e6)
        pll.create_clkout(self.cd_sys2x_i, 2*sys_clk_freq)
        pll.create_clkout(self.cd_init, 24e6)
        self.specials += [
            Instance("ECLKBRIDGECS",
                i_CLK0   = self.cd_sys2x_i.clk,
                i_SEL    = 0,
                o_ECSOUT = sys2x_clk_ecsout),
            Instance("ECLKSYNCB",
                i_ECLKI = sys2x_clk_ecsout,
                i_STOP  = self.stop,
                o_ECLKO = self.cd_sys2x.clk),
            Instance("CLKDIVF",
                p_DIV     = "2.0",
                i_ALIGNWD = 0,
                i_CLKI    = self.cd_sys2x.clk,
                i_RST     = self.reset,
                o_CDIVX   = self.cd_sys.clk),
            AsyncResetSynchronizer(self.cd_init,  ~por_done | ~pll.locked | ~rst_n),
            AsyncResetSynchronizer(self.cd_sys,   ~por_done | ~pll.locked | ~rst_n | self.reset),
            AsyncResetSynchronizer(self.cd_sys2x, ~por_done | ~pll.locked | ~rst_n | self.reset),
        ]

        self.clock_domains.cd_usb_12 = ClockDomain()
        self.clock_domains.cd_usb_48 = ClockDomain()
        self.submodules.usb_pll = usb_pll = ECP5PLL()
        usb_pll.register_clkin(clk48, 48e6)
        usb_pll.create_clkout(self.cd_usb_48, 48e6)
        usb_pll.create_clkout(self.cd_usb_12, 12e6)

class OrangeCrab:
    revision = "0.2"

    def __init__(self, name=None):
        self.device = "LFE5U-25F-8MG285C"
        self.constraint_manager = ConstraintManager(_io_r0_2, _connectors_r0_2)
        if name is None:
            name = self.__module__.split(".")[-1]
        self.name = name
        self.sources = []
        self.verilog_include_paths = []
        self.output_dir = None
        self.finalized = False
        self.toolchain = LatticeTrellisToolchain()

    def request(self, *args, **kwargs):
        return self.constraint_manager.request(*args, **kwargs)

    def lookup_request(self, *args, **kwargs):
        return self.constraint_manager.lookup_request(*args, **kwargs)

    def add_period_constraint(self, clk, period):
        if clk is not None:
            if hasattr(clk, "p"):
                clk = clk.p
            self.toolchain.add_period_constraint(self, clk, period)

    def add_platform_command(self, *args, **kwargs):
        return self.constraint_manager.add_platform_command(*args, **kwargs)

    def finalize(self, fragment):
        if self.finalized:
            raise ConstraintError("Already finalized")

        self.add_period_constraint(self.lookup_request("clk48", loose=True), 1e9/48e6)

        self.finalized = True

    def add_source(self, filename, language=None, library=None):
        if language is None:
            language = _language_by_filename(filename)
        if library is None:
            library = "work"
        for f, _, _ in self.sources:
            if f == filename:
                return
        self.sources.append((os.path.abspath(filename), language, library))

    def resolve_signals(self, vns):
        # resolve signal names in constraints
        sc = self.constraint_manager.get_sig_constraints()
        named_sc = [(vns.get_name(sig), pins, others, resource) for sig, pins, others, resource in sc]
        # resolve signal names in platform commands
        pc = self.constraint_manager.get_platform_commands()
        named_pc = []
        for template, args in pc:
            name_dict = dict((k, vns.get_name(sig)) for k, sig in args.items())
            named_pc.append(template.format(**name_dict))

        return named_sc, named_pc

    def get_verilog(self, fragment, **kwargs):
        return verilog.convert(fragment,
            self.constraint_manager.get_io_signals(),
            create_clock_domains=False,
            special_overrides=self.toolchain.special_overrides,
            attr_translate=self.toolchain.attr_translate,
            **kwargs)

    def build(self, *args, **kwargs):
        return self.toolchain.build(self, *args, **kwargs)

class Waltraud(Module):
    mem_map = {
        "rom":      0x00000000,
        "sram":     0x20000000,
        "main_ram": 0x40000000,
        "csr":      0xf0000000,
    }

    def __init__(self,
        sys_clk_freq         = 64e6,
        # Bus parameters
        bus_standard         = "wishbone",
        bus_data_width       = 32,
        bus_address_width    = 32,
        bus_timeout          = 1e6,
        bus_reserved_regions = {},
        # CSR parameters
        csr_data_width       = 8,
        csr_address_width    = 14,
        csr_paging           = 0x800,
        csr_reserved_csrs    = {
            "ctrl":   0,
            "uart":   2,
            "timer0": 3,
        },
        # Interrupt parameters
        irq_n_irqs           = 32,
        irq_reserved_irqs    = {
            "timer0": 3,
            "uart":   4,
        }):

        self.platform     = OrangeCrab()
        self.sys_clk_freq = sys_clk_freq

        self.submodules.bus = SoCBusHandler(
            standard         = bus_standard,
            data_width       = bus_data_width,
            address_width    = bus_address_width,
            timeout          = bus_timeout,
            reserved_regions = bus_reserved_regions,
        )

        self.submodules.csr = SoCCSRHandler(
            data_width    = csr_data_width,
            address_width = csr_address_width,
            alignment     = 32,
            paging        = csr_paging,
            reserved_csrs = csr_reserved_csrs,
        )

        self.submodules.irq = SoCIRQHandler(
            n_irqs        = irq_n_irqs,
            reserved_irqs = irq_reserved_irqs,
        )

        self.logger = logging.getLogger("Waltraud")
        self.logger.info("FPGA device : {}.".format(self.platform.device))
        self.logger.info("System clock: {:3.2f}MHz.".format(self.sys_clk_freq / 1e6))
        self.logger.info(colorer("-"*80, color="bright"))

        self.constants = {}
        self.add_config("CLOCK_FREQUENCY", int(self.sys_clk_freq))

        # Add SoCController
        self.submodules.ctrl = SoCController()
        self.csr.add("ctrl", use_loc_if_exists=True)

        # Add CPU
        self.submodules.cpu = PicoRV32(self.platform, "minimal")
        for n, (origin, size) in enumerate(self.cpu.io_regions.items()):
            self.bus.add_region("io{}".format(n), SoCIORegion(origin=origin, size=size, cached=False))
        self.mem_map.update(self.cpu.mem_map)
        self.cpu.set_reset_address(self.mem_map["rom"])
        for n, cpu_bus in enumerate(self.cpu.periph_buses):
            self.bus.add_master(name="cpu_bus{}".format(n), master=cpu_bus)
        self.csr.add("cpu", use_loc_if_exists=True)
        for name, loc in self.cpu.interrupts.items():
            self.irq.add(name, loc)
        if hasattr(self.ctrl, "reset"):
            self.comb += self.cpu.reset.eq(self.ctrl.reset)
        if hasattr(self.cpu, "nop"):
            self.add_constant("CONFIG_CPU_NOP", self.cpu.nop)

        # Add integrated ROM and SRAM
        self.add_rom("rom",  self.mem_map["rom"],   0x8000)
        self.add_ram("sram", self.mem_map["sram"], 0x10000)

        # Add UART
        usb_pads = self.platform.request("usb")
        usb_iobuf = IoBuf(usb_pads.d_p, usb_pads.d_n, usb_pads.pullup)
        self.submodules.uart = CDCUsb(usb_iobuf)
        self.csr.add("uart_phy", use_loc_if_exists=True)
        self.csr.add("uart", use_loc_if_exists=True)
        self.irq.add("uart", use_loc_if_exists=True)

        # Add Timer
        self.submodules.timer0 = Timer()
        self.csr.add("timer0", use_loc_if_exists=True)
        self.irq.add("timer0", use_loc_if_exists=True)

        # Add CSR bridge
        self.add_csr_bridge(self.mem_map["csr"])

        self.submodules.crg = _CRG(self.platform, self.sys_clk_freq)

        self.submodules.ddrphy = ECP5DDRPHY(self.platform.request("ddram"), sys_clk_freq=self.sys_clk_freq)
        self.csr.add("ddrphy", use_loc_if_exists=True)
        self.comb += self.crg.stop.eq(self.ddrphy.init.stop)
        self.comb += self.crg.reset.eq(self.ddrphy.init.reset)
        self.add_sdram("sdram", self.ddrphy, MT41K64M16(self.sys_clk_freq, "1:2"), self.mem_map["main_ram"], size=0x40000000, l2_cache_size=2048)

    def add_constant(self, name, value=None):
        name = name.upper()
        if name in self.constants.keys():
            self.logger.error("{} Constant already {}.".format(colorer(name), colorer("declared", color="red")))
            raise
        self.constants[name] = SoCConstant(value)

    def add_config(self, name, value=None):
        name = "CONFIG_" + name
        if isinstance(value, str):
            self.add_constant(name + "_" + value)
        else:
            self.add_constant(name, value)

    def add_ram(self, name, origin, size, contents=[], mode="rw"):
        ram_bus = wishbone.Interface(data_width=self.bus.data_width)
        ram     = wishbone.SRAM(size, bus=ram_bus, init=contents, read_only=(mode == "r"))
        self.bus.add_slave(name, ram.bus, SoCRegion(origin=origin, size=size, mode=mode))
        setattr(self.submodules, name, ram)

    def add_rom(self, name, origin, size, contents=[]):
        self.add_ram(name, origin, size, contents, mode="r")

    def initialize_rom(self, data):
        self.rom.mem.init = data

    def add_csr_bridge(self, origin):
        self.submodules.csr_bridge = wishbone.Wishbone2CSR(
            bus_csr       = csr_bus.Interface(
            address_width = self.csr.address_width,
            data_width    = self.csr.data_width),
        )
        csr_size   = 2**(self.csr.address_width + 2)
        csr_region = SoCRegion(origin=origin, size=csr_size, cached=False)
        self.bus.add_slave("csr", self.csr_bridge.wishbone, csr_region)
        self.csr.add_master(name="bridge", master=self.csr_bridge.csr)
        self.add_config("CSR_DATA_WIDTH", self.csr.data_width)
        self.add_config("CSR_ALIGNMENT",  self.csr.alignment)

    def add_sdram(self, name, phy, module, origin, size=None,
        l2_cache_size           = 8192,
        l2_cache_min_data_width = 128,
        l2_cache_reverse        = True,
        l2_cache_full_memory_we = True):

        # LiteDRAM core
        self.submodules.sdram = LiteDRAMCore(
            phy             = phy,
            geom_settings   = module.geom_settings,
            timing_settings = module.timing_settings,
            clk_freq        = self.sys_clk_freq,
        )
        self.csr.add("sdram")

        # Compute/Check SDRAM size
        sdram_size = 2**(module.geom_settings.bankbits + module.geom_settings.rowbits + module.geom_settings.colbits) * phy.settings.databits // 8
        if size is not None:
            sdram_size = min(sdram_size, size)

        # Add SDRAM region
        self.bus.add_region("main_ram", SoCRegion(origin=origin, size=sdram_size))

        # Request a LiteDRAM native port.
        port = self.sdram.crossbar.get_port()
        port.data_width = 2**int(math.log2(port.data_width))

        # Create Wishbone Slave.
        wb_sdram = wishbone.Interface()
        self.bus.add_slave("main_ram", wb_sdram)

        # L2 Cache
        if l2_cache_size != 0:
            # Insert L2 cache inbetween Wishbone bus and LiteDRAM
            l2_cache_size = max(l2_cache_size, int(2 * port.data_width / 8))
            l2_cache_size = 2**int(math.log2(l2_cache_size))
            l2_cache_data_width = max(port.data_width, l2_cache_min_data_width)
            l2_cache            = wishbone.Cache(
                cachesize = l2_cache_size // 4,
                master    = wb_sdram,
                slave     = wishbone.Interface(l2_cache_data_width),
                reverse   = l2_cache_reverse,
            )
            if l2_cache_full_memory_we:
                l2_cache = FullMemoryWE()(l2_cache)
            self.submodules.l2_cache = l2_cache
            litedram_wb = self.l2_cache.slave
        else:
            litedram_wb = wishbone.Interface(port.data_width)
            self.submodules += wishbone.Converter(wb_sdram, litedram_wb)
        self.add_config("L2_SIZE", l2_cache_size)

        # Wishbone Slave <--> LiteDRAM bridge
        self.submodules.wishbone_bridge = LiteDRAMWishbone2Native(litedram_wb, port, base_address = self.bus.regions["main_ram"].origin)

    def do_finalize(self):
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(self.bus)
        self.logger.info(self.csr)
        self.logger.info(self.irq)
        self.logger.info(colorer("-"*80, color="bright"))

        if len(self.bus.masters) and len(self.bus.slaves):
            # If 1 bus_master, 1 bus_slave and no address translation, use InterconnectPointToPoint.
            if ((len(self.bus.masters) == 1) and (len(self.bus.slaves) == 1) and (next(iter(self.bus.regions.values())).origin == 0)):
                self.submodules.bus_interconnect = wishbone.InterconnectPointToPoint(
                    master = next(iter(self.bus.masters.values())),
                    slave  = next(iter(self.bus.slaves.values())),
                )
            # Otherwise, use InterconnectShared.
            else:
                self.submodules.bus_interconnect = wishbone.InterconnectShared(
                    masters        = self.bus.masters.values(),
                    slaves         = [(self.bus.regions[n].decoder(self.bus), s) for n, s in self.bus.slaves.items()],
                    register       = True,
                    timeout_cycles = self.bus.timeout,
                )
                if hasattr(self, "ctrl") and self.bus.timeout is not None:
                    if hasattr(self.ctrl, "bus_error"):
                        self.comb += self.ctrl.bus_error.eq(self.bus_interconnect.timeout.error)
            self.bus.logger.info("Interconnect: {} ({} <-> {}).".format(colorer(self.bus_interconnect.__class__.__name__), colorer(len(self.bus.masters)), colorer(len(self.bus.slaves))))

        self.add_constant("CONFIG_BUS_STANDARD",      self.bus.standard.upper())
        self.add_constant("CONFIG_BUS_DATA_WIDTH",    self.bus.data_width)
        self.add_constant("CONFIG_BUS_ADDRESS_WIDTH", self.bus.address_width)

        self.submodules.csr_bankarray = csr_bus.CSRBankArray(self,
            address_map        = self.csr.address_map,
            data_width         = self.csr.data_width,
            address_width      = self.csr.address_width,
            alignment          = self.csr.alignment,
            paging             = self.csr.paging,
            soc_bus_data_width = self.bus.data_width)
        if len(self.csr.masters):
            self.submodules.csr_interconnect = csr_bus.InterconnectShared(
                masters = list(self.csr.masters.values()),
                slaves  = self.csr_bankarray.get_buses(),
            )

        # Add CSRs regions
        for name, csrs, mapaddr, rmap in self.csr_bankarray.banks:
            self.csr.add_region(name, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword = self.csr.data_width,
                obj     = csrs,
            ))

        # Add Memory regions
        for name, memory, mapaddr, mmap in self.csr_bankarray.srams:
            self.csr.add_region(name + "_" + memory.name_override, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword = self.csr.data_width,
                obj     = memory,
            ))

        # Sort CSR regions by origin
        self.csr.regions = {k: v for k, v in sorted(self.csr.regions.items(), key=lambda item: item[1].origin)}

        # Add CSRs / Config items to constants
        for name, constant in self.csr_bankarray.constants:
            self.add_constant(name + "_" + constant.name, constant.value.value)

        for name, loc in sorted(self.irq.locs.items()):
            if name in self.cpu.interrupts.keys():
                continue
            if hasattr(self, name):
                module = getattr(self, name)
                if not hasattr(module, "ev"):
                    self.logger.error("EventManager {} in {} SubModule.".format(colorer("not found", color="red"), colorer(name)))
                    raise
                self.comb += self.cpu.interrupt[loc].eq(module.ev.irq)
            self.add_constant(name + "_INTERRUPT", loc)

        # Retro-compatibility
        for region in self.bus.regions.values():
            region.length = region.size
            region.type   = "cached" if region.cached else "io"
            if region.linker:
                region.type += "+linker"

    def build(self, *args, **kwargs):
        self.build_name = kwargs.pop("build_name", self.platform.name)
        kwargs.update({"build_name": self.build_name})
        return self.platform.build(self, *args, **kwargs)

def _get_mem_data(filename_or_regions, endianness="big"):
    if isinstance(filename_or_regions, dict):
        regions = filename_or_regions
    else:
        regions = {filename_or_regions: "0x00000000"}

    data_size = 0
    for filename, base in regions.items():
        data_size = max(int(base, 16) + os.path.getsize(filename), data_size)
    assert data_size > 0

    data = [0] * math.ceil(data_size / 4)
    for filename, base in regions.items():
        with open(filename, "rb") as f:
            i = 0
            while True:
                w = f.read(4)
                if not w:
                    break
                if len(w) != 4:
                    for _ in range(len(w), 4):
                        w += b'\x00'
                if endianness == "little":
                    data[int(base, 16) // 4 + i] = struct.unpack("<I", w)[0]
                else:
                    data[int(base, 16) // 4 + i] = struct.unpack(">I", w)[0]
                i += 1
    return data

def _get_cpu_mak(cpu, compile_software):
    # select between clang and gcc
    clang = os.getenv("CLANG", "")
    if clang != "":
        clang = bool(int(clang))
    else:
        clang = None
    if not hasattr(cpu, "clang_triple"):
        if clang:
            raise ValueError(cpu.name + "not supported with clang.")
        else:
            clang = False
    else:
        # Default to gcc unless told otherwise
        if clang is None:
            clang = False
    assert isinstance(clang, bool)
    if clang:
        triple = cpu.clang_triple
        flags = cpu.clang_flags
    else:
        triple = cpu.gcc_triple
        flags = cpu.gcc_flags

    # select triple when more than one
    def select_triple(triple):
        r = None
        if not isinstance(triple, tuple):
            triple = (triple,)
        p = get_platform()
        for i in range(len(triple)):
            t = triple[i]
            # use native toolchain if host and target platforms are the same
            if t == 'riscv64-unknown-elf' and p == 'linux-riscv64':
                r = '--native--'
                break
            if which(t+"-gcc"):
                r = t
                break
        if r is None:
            if not compile_software:
                return "--not-found--"
            msg = "Unable to find any of the cross compilation toolchains:\n"
            for i in range(len(triple)):
                msg += "- " + triple[i] + "\n"
            raise OSError(msg)
        return r

    # return informations
    return [
        ("TRIPLE", select_triple(triple)),
        ("CPU", cpu.name),
        ("CPUFLAGS", flags),
        ("CPUENDIANNESS", cpu.endianness),
        ("CLANG", str(int(clang))),
        ("CPU_DIRECTORY", os.path.dirname(inspect.getfile(cpu.__class__))),
    ]

def _get_linker_output_format(cpu):
    return "OUTPUT_FORMAT(\"" + cpu.linker_output_format + "\")\n"

def _get_linker_regions(regions):
    r = "MEMORY {\n"
    for name, region in regions.items():
        r += "\t{} : ORIGIN = 0x{:08x}, LENGTH = 0x{:08x}\n".format(name, region.origin, region.length)
    r += "}\n"
    return r

def _get_mem_header(regions):
    r = "#ifndef __GENERATED_MEM_H\n#define __GENERATED_MEM_H\n\n"
    for name, region in regions.items():
        r += "#ifndef {name}\n".format(name=name.upper())
        r += "#define {name}_BASE 0x{base:08x}L\n#define {name}_SIZE 0x{size:08x}\n\n".format(
            name=name.upper(), base=region.origin, size=region.length)
        r += "#endif\n"
    r += "#endif\n"
    return r

def _get_soc_header(constants, with_access_functions=True):
    r = "#ifndef __GENERATED_SOC_H\n#define __GENERATED_SOC_H\n"
    for name, value in constants.items():
        if value is None:
            r += "#define "+name+"\n"
            continue
        if isinstance(value, str):
            value = "\"" + value + "\""
            ctype = "const char *"
        else:
            value = str(value)
            ctype = "int"
        r += "#define "+name+" "+value+"\n"
        if with_access_functions:
            r += "static inline "+ctype+" "+name.lower()+"_read(void) {\n"
            r += "\treturn "+value+";\n}\n"

    r += "\n#endif\n"
    return r

def _get_rw_functions_c(reg_name, reg_base, nwords, busword, alignment, read_only, with_access_functions):
    r = ""

    addr_str = "CSR_{}_ADDR".format(reg_name.upper())
    size_str = "CSR_{}_SIZE".format(reg_name.upper())
    r += "#define {} (CSR_BASE + {}L)\n".format(addr_str, hex(reg_base))
    r += "#define {} {}\n".format(size_str, nwords)

    size = nwords*busword//8
    if size > 8:
        # downstream should select appropriate `csr_[rd|wr]_buf_uintX()` pair!
        return r
    elif size > 4:
        ctype = "uint64_t"
    elif size > 2:
        ctype = "uint32_t"
    elif size > 1:
        ctype = "uint16_t"
    else:
        ctype = "uint8_t"

    stride = alignment//8;
    if with_access_functions:
        r += "static inline {} {}_read(void) {{\n".format(ctype, reg_name)
        if nwords > 1:
            r += "\t{} r = csr_read_simple(CSR_BASE + {}L);\n".format(ctype, hex(reg_base))
            for sub in range(1, nwords):
                r += "\tr <<= {};\n".format(busword)
                r += "\tr |= csr_read_simple(CSR_BASE + {}L);\n".format(hex(reg_base+sub*stride))
            r += "\treturn r;\n}\n"
        else:
            r += "\treturn csr_read_simple(CSR_BASE + {}L);\n}}\n".format(hex(reg_base))

        if not read_only:
            r += "static inline void {}_write({} v) {{\n".format(reg_name, ctype)
            for sub in range(nwords):
                shift = (nwords-sub-1)*busword
                if shift:
                    v_shift = "v >> {}".format(shift)
                else:
                    v_shift = "v"
                r += "\tcsr_write_simple({}, CSR_BASE + {}L);\n".format(v_shift, hex(reg_base+sub*stride))
            r += "}\n"
    return r

def _get_csr_header(regions, constants, csr_base=None, with_access_functions=True):
    alignment = constants.get("CONFIG_CSR_ALIGNMENT", 32)
    r = ""
    if with_access_functions: # FIXME
        r += "#include <generated/soc.h>\n"
    r += "#ifndef __GENERATED_CSR_H\n#define __GENERATED_CSR_H\n"
    if with_access_functions:
        r += "#include <stdint.h>\n"
        r += "#include <system.h>\n"
        r += "#ifndef CSR_ACCESSORS_DEFINED\n"
        r += "#include <hw/common.h>\n"
        r += "#endif\n"
    csr_base = csr_base if csr_base is not None else regions[next(iter(regions))].origin
    r += "#ifndef CSR_BASE\n"
    r += "#define CSR_BASE {}L\n".format(hex(csr_base))
    r += "#endif\n"
    for name, region in regions.items():
        origin = region.origin - csr_base
        r += "\n/* "+name+" */\n"
        r += "#define CSR_"+name.upper()+"_BASE (CSR_BASE + "+hex(origin)+"L)\n"
        if not isinstance(region.obj, Memory):
            for csr in region.obj:
                nr = (csr.size + region.busword - 1)//region.busword
                r += _get_rw_functions_c(name + "_" + csr.name, origin, nr, region.busword, alignment, isinstance(csr, CSRStatus), with_access_functions)
                origin += alignment//8*nr
                if hasattr(csr, "fields"):
                    for field in csr.fields.fields:
                        r += "#define CSR_"+name.upper()+"_"+csr.name.upper()+"_"+field.name.upper()+"_OFFSET "+str(field.offset)+"\n"
                        r += "#define CSR_"+name.upper()+"_"+csr.name.upper()+"_"+field.name.upper()+"_SIZE "+str(field.size)+"\n"

    r += "\n#endif\n"
    return r

class Builder:
    def __init__(self, soc, output_dir="build", compile_gateware=True):
        self.soc = soc

        self.output_dir = os.path.abspath(output_dir)

        self.gateware_dir  = os.path.join(self.output_dir,   "gateware")
        self.software_dir  = os.path.join(self.output_dir,   "software")
        self.include_dir   = os.path.join(self.software_dir, "include")
        self.generated_dir = os.path.join(self.include_dir,  "generated")

        self.compile_gateware = compile_gateware

        self.software_packages = []
        for name in [ "libcompiler_rt", "libbase", "liblitedram", "bios" ]:
            src_dir = os.path.abspath(os.path.join("software", name))
            self.software_packages.append((name, src_dir))

    def _generate_includes(self):
        os.makedirs(self.include_dir, exist_ok=True)
        os.makedirs(self.generated_dir, exist_ok=True)

        variables_contents = []
        def define(k, v):
            variables_contents.append("{}={}\n".format(k, v.replace("\\", "\\\\")))

        for k, v in _get_cpu_mak(self.soc.cpu, True):
            define(k, v)
        variables_contents.append("export BUILDINC_DIRECTORY\n")
        define("BUILDINC_DIRECTORY", self.include_dir)
        for name, src_dir in self.software_packages:
            define(name.upper() + "_DIRECTORY", src_dir)

        _write_file(os.path.join(self.generated_dir, "variables.mak"), "".join(variables_contents))
        _write_file(os.path.join(self.generated_dir, "output_format.ld"), _get_linker_output_format(self.soc.cpu))
        _write_file(os.path.join(self.generated_dir, "regions.ld"), _get_linker_regions(self.soc.bus.regions))

        _write_file(os.path.join(self.generated_dir, "mem.h"), _get_mem_header(self.soc.bus.regions))
        _write_file(os.path.join(self.generated_dir, "soc.h"), _get_soc_header(self.soc.constants))
        _write_file(os.path.join(self.generated_dir, "csr.h"), _get_csr_header(regions=self.soc.csr.regions, constants=self.soc.constants, csr_base=self.soc.bus.regions['csr'].origin))

        _write_file(os.path.join(self.generated_dir, "sdram_phy.h"), get_sdram_phy_c_header(self.soc.sdram.controller.settings.phy, self.soc.sdram.controller.settings.timing))

    def _prepare_rom_software(self):
        for name, src_dir in self.software_packages:
            dst_dir = os.path.join(self.software_dir, name)
            os.makedirs(dst_dir, exist_ok=True)

    def _generate_rom_software(self):
         for name, src_dir in self.software_packages:
            dst_dir = os.path.join(self.software_dir, name)
            makefile = os.path.join(src_dir, "Makefile")
            subprocess.check_call(["make", "-C", dst_dir, "-I", src_dir, "-f", makefile])

    def _initialize_rom_software(self):
        bios_file = os.path.join(self.software_dir, "bios", "bios.bin")
        bios_data = _get_mem_data(bios_file, self.soc.cpu.endianness)
        self.soc.initialize_rom(bios_data)

    def build(self, **kwargs):
        os.makedirs(self.gateware_dir, exist_ok=True)
        os.makedirs(self.software_dir, exist_ok=True)

        self.soc.platform.output_dir = self.output_dir
        self.soc.finalize()

        self._generate_includes()
        self._prepare_rom_software()
        self._generate_rom_software()
        self._initialize_rom_software()

        if "run" not in kwargs:
            kwargs["run"] = self.compile_gateware
        vns = self.soc.build(build_dir=self.gateware_dir, **kwargs)
        self.soc.do_exit(vns=vns)
        return vns

class DFUProg:
    def __init__(self, vid, pid):
        self.vid = vid
        self.pid = pid

    def load_bitstream(self, bitstream_file):
        subprocess.call(["cp", "-vip", bitstream_file + ".bit", bitstream_file + ".dfu"])
        subprocess.call(["dfu-suffix", "-v", self.vid, "-p", self.pid, "-a", bitstream_file + ".dfu"])
        subprocess.call(["dfu-util", "--download", bitstream_file + ".dfu"])

def main():
    parser = argparse.ArgumentParser(description="Waltraud on OrangeCrab\n", formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--build", action="store_true", help="Build bitstream")
    parser.add_argument("--load",  action="store_true", help="Load bitstream")
    args = parser.parse_args()

    soc = Waltraud()

    Builder(soc).build(build_name="waltraud", run=args.build)

    if args.load:
        DFUProg(vid="1209", pid="5af0").load_bitstream("build/gateware/waltraud")

if __name__ == "__main__":
    main()
