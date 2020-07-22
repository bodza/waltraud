#!/usr/bin/env python3

import argparse, datetime, logging, math, os, subprocess, time

from migen import ClockDomain, FullMemoryWE, If, Instance, log2_int, Module, Signal

from migen.genlib.resetsync import AsyncResetSynchronizer

from litex import get_data_mod
from litex.build.dfu import DFUProg
from litex.build.generic_platform import IOStandard, Misc, Pins, Subsignal
from litex.build.lattice import LatticePlatform
from litex.build.tools import write_to_file

from litex.soc.cores import cpu
from litex.soc.cores.clock import ECP5PLL
from litex.soc.cores.identifier import Identifier
from litex.soc.cores.timer import Timer
from litex.soc.integration import common, export
from litex.soc.interconnect.csr import AutoCSR, CSRStatus, CSRStorage
from litex.soc.interconnect import axi, csr_bus, wishbone

from litedram.modules import MT41K64M16
from litedram.phy import ECP5DDRPHY

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

def build_time(with_time=True):
    fmt = "%Y-%m-%d %H:%M:%S" if with_time else "%Y-%m-%d"
    return datetime.datetime.fromtimestamp(time.time()).strftime(fmt)

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
        self.logger.info("Creating Bus Handler...")

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
        self.logger.info("{}-bit {} Bus, {}GiB Address Space.".format(
            colorer(data_width), colorer(standard), colorer(2**address_width/2**30)))

        # Adding reserved regions
        self.logger.info("Adding {} Bus Regions...".format(colorer("reserved", color="cyan")))
        for name, region in reserved_regions.items():
            if isinstance(region, int):
                region = SoCRegion(origin=region, size=0x1000000)
            self.add_region(name, region)

        self.logger.info("Bus Handler {}.".format(colorer("created", color="green")))

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
                self.logger.error("IO Region {} between {} and {}:".format(
                    colorer("overlap", color="red"),
                    colorer(overlap[0]),
                    colorer(overlap[1])))
                self.logger.error(str(self.io_regions[overlap[0]]))
                self.logger.error(str(self.io_regions[overlap[1]]))
                raise
            self.logger.info("{} Region {} at {}.".format(
                colorer(name,    color="underline"),
                colorer("added", color="green"),
                str(region)))
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
        self.logger.info("Allocating {} Region of size {}...".format(
            colorer("Cached" if cached else "IO"),
            colorer("0x{:08x}".format(size))))

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
        elif isinstance(interface, axi.AXILiteInterface):
            # Data width conversion
            intermediate = axi.AXILiteInterface(data_width=self.data_width)
            if direction == "m2s":
                converter = axi.AXILiteConverter(master=interface, slave=intermediate)
            if direction == "s2m":
                converter = axi.AXILiteConverter(master=intermediate, slave=interface)
            self.submodules += converter
            # Bus type conversion
            new_interface = wishbone.Interface(data_width=self.data_width)
            if direction == "m2s":
                converter = axi.AXILite2Wishbone(axi_lite=intermediate, wishbone=new_interface)
            elif direction == "s2m":
                converter = axi.Wishbone2AXILite(wishbone=new_interface, axi_lite=intermediate)
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
                self.logger.error("{} {} name {}.".format(
                    colorer(name), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n in self.locs.values():
                self.logger.error("{} {} Location {}.".format(
                    colorer(n), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n is None:
                allocated = True
                n = self.alloc(name)
            else:
                if n < 0:
                    self.logger.error("{} {} Location should be {}.".format(
                        colorer(n),
                        self.name,
                        colorer("positive", color="red")))
                    raise
                if n > self.n_locs:
                    self.logger.error("{} {} Location {} than maximum: {}.".format(
                        colorer(n),
                        self.name,
                        colorer("higher", color="red"),
                        colorer(self.n_locs)))
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
        SoCLocHandler.__init__(self, "CSR", n_locs=alignment//8*(2**address_width)//paging)
        self.logger = logging.getLogger("SoCCSRHandler")
        self.logger.info("Creating CSR Handler...")

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
        self.logger.info("Adding {} CSRs...".format(colorer("reserved", color="cyan")))
        for name, n in reserved_csrs.items():
            self.add(name, n)

        self.logger.info("CSR Handler {}.".format(colorer("created", color="green")))

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            self.logger.error("{} {} as CSR Master:".format(
                colorer(name),
                colorer("already declared", color="red")))
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
        self.logger.info("{} {} as CSR Master.".format(
            colorer(name,    color="underline"),
            colorer("added", color="green")))

    def add_region(self, name, region):
        # FIXME: add checks
        self.regions[name] = region

    def address_map(self, name, memory):
        if memory is not None:
            name = name + "_" + memory.name_override
        if self.locs.get(name, None) is None:
            self.logger.error("CSR {} {}.".format(
                colorer(name),
                colorer("not found", color="red")))
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
        self.logger.info("Creating IRQ Handler...")

        # Check IRQ Number
        if n_irqs > 32:
            self.logger.error("Unsupported IRQs number: {} supporteds: {:s}".format(
                colorer(n, color="red"), colorer("Up to 32", color="green")))
            raise

        # Create IRQ Handler
        self.logger.info("IRQ Handler (up to {} Locations).".format(colorer(n_irqs)))

        # Adding reserved IRQs
        self.logger.info("Adding {} IRQs...".format(colorer("reserved", color="cyan")))
        for name, n in reserved_irqs.items():
            self.add(name, n)

        self.logger.info("IRQ Handler {}.".format(colorer("created", color="green")))

    def __str__(self):
        r ="IRQ Handler (up to {} Locations).\n".format(colorer(self.n_locs))
        r += SoCLocHandler.__str__(self)
        r = r[:-1]
        return r

class SoCController(Module, AutoCSR):
    def __init__(self,
        with_reset    = True,
        with_scratch  = True,
        with_errors   = True):

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

class SoC(Module):
    mem_map = {}

    def __init__(self, platform, sys_clk_freq,
        bus_standard         = "wishbone",
        bus_data_width       = 32,
        bus_address_width    = 32,
        bus_timeout          = 1e6,
        bus_reserved_regions = {},

        csr_data_width       = 32,
        csr_address_width    = 14,
        csr_paging           = 0x800,
        csr_reserved_csrs    = {},

        irq_n_irqs           = 32,
        irq_reserved_irqs    = {},
        ):

        self.logger = logging.getLogger("SoC")
        self.logger.info(colorer("        __   _ __      _  __  ", color="bright"))
        self.logger.info(colorer("       / /  (_) /____ | |/_/  ", color="bright"))
        self.logger.info(colorer("      / /__/ / __/ -_)>  <    ", color="bright"))
        self.logger.info(colorer("     /____/_/\\__/\\__/_/|_|  ", color="bright"))
        self.logger.info(colorer("  Build your hardware, easily!", color="bright"))

        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(colorer("Creating SoC... ({})".format(build_time())))
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info("FPGA device : {}.".format(platform.device))
        self.logger.info("System clock: {:3.2f}MHz.".format(sys_clk_freq/1e6))

        self.platform     = platform
        self.sys_clk_freq = sys_clk_freq
        self.constants    = {}
        self.csr_regions  = {}

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
            reserved_irqs = irq_reserved_irqs
        )

        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(colorer("Initial SoC:"))
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(self.bus)
        self.logger.info(self.csr)
        self.logger.info(self.irq)
        self.logger.info(colorer("-"*80, color="bright"))

        self.add_config("CLOCK_FREQUENCY", int(sys_clk_freq))

    def check_if_exists(self, name):
        if hasattr(self, name):
            self.logger.error("{} SubModule already {}.".format(
                colorer(name),
                colorer("declared", color="red")))
            raise

    def add_constant(self, name, value=None):
        name = name.upper()
        if name in self.constants.keys():
            self.logger.error("{} Constant already {}.".format(
                colorer(name),
                colorer("declared", color="red")))
            raise
        self.constants[name] = SoCConstant(value)

    def add_config(self, name, value=None):
        name = "CONFIG_" + name
        if isinstance(value, str):
            self.add_constant(name + "_" + value)
        else:
            self.add_constant(name, value)

    def add_controller(self, name="ctrl", **kwargs):
        self.check_if_exists(name)
        setattr(self.submodules, name, SoCController(**kwargs))
        self.csr.add(name, use_loc_if_exists=True)

    def add_ram(self, name, origin, size, contents=[], mode="rw"):
        ram_bus = wishbone.Interface(data_width=self.bus.data_width)
        ram     = wishbone.SRAM(size, bus=ram_bus, init=contents, read_only=(mode == "r"))
        self.bus.add_slave(name, ram.bus, SoCRegion(origin=origin, size=size, mode=mode))
        self.check_if_exists(name)
        self.logger.info("RAM {} {} {}.".format(
            colorer(name),
            colorer("added", color="green"),
            self.bus.regions[name]))
        setattr(self.submodules, name, ram)

    def add_rom(self, name, origin, size, contents=[]):
        self.add_ram(name, origin, size, contents, mode="r")

    def add_csr_bridge(self, origin):
        self.submodules.csr_bridge = wishbone.Wishbone2CSR(
            bus_csr       = csr_bus.Interface(
            address_width = self.csr.address_width,
            data_width    = self.csr.data_width))
        csr_size   = 2**(self.csr.address_width + 2)
        csr_region = SoCRegion(origin=origin, size=csr_size, cached=False)
        self.bus.add_slave("csr", self.csr_bridge.wishbone, csr_region)
        self.csr.add_master(name="bridge", master=self.csr_bridge.csr)
        self.add_config("CSR_DATA_WIDTH", self.csr.data_width)
        self.add_config("CSR_ALIGNMENT",  self.csr.alignment)

    def add_cpu(self, name="vexriscv", variant="standard", cls=None, reset_address=None):
        if name not in cpu.CPUS.keys():
            self.logger.error("{} CPU {}, supporteds: {}.".format(
                colorer(name),
                colorer("not supported", color="red"),
                colorer(", ".join(cpu.CPUS.keys()))))
            raise
        # Add CPU
        cpu_cls = cls if cls is not None else cpu.CPUS[name]
        if variant not in cpu_cls.variants:
            self.logger.error("{} CPU variant {}, supporteds: {}.".format(
                colorer(variant),
                colorer("not supported", color="red"),
                colorer(", ".join(cpu_cls.variants))))
            raise
        self.submodules.cpu = cpu_cls(self.platform, variant)
        # Update SoC with CPU constraints
        for n, (origin, size) in enumerate(self.cpu.io_regions.items()):
            self.bus.add_region("io{}".format(n), SoCIORegion(origin=origin, size=size, cached=False))
        self.mem_map.update(self.cpu.mem_map) # FIXME
        # Add Bus Masters/CSR/IRQs
        if not isinstance(self.cpu, cpu.CPUNone):
            if reset_address is None:
                reset_address = self.mem_map["rom"]
            self.cpu.set_reset_address(reset_address)
            for n, cpu_bus in enumerate(self.cpu.periph_buses):
                self.bus.add_master(name="cpu_bus{}".format(n), master=cpu_bus)
            self.csr.add("cpu", use_loc_if_exists=True)
            if hasattr(self.cpu, "interrupt"):
                for name, loc in self.cpu.interrupts.items():
                    self.irq.add(name, loc)
                self.add_config("CPU_HAS_INTERRUPT")
            if hasattr(self, "ctrl"):
                if hasattr(self.ctrl, "reset"):
                    self.comb += self.cpu.reset.eq(self.ctrl.reset)
            self.add_config("CPU_RESET_ADDR", reset_address)
        # Add constants
        self.add_config("CPU_TYPE",    str(name))
        self.add_config("CPU_VARIANT", str(variant.split('+')[0]))
        self.add_constant("CONFIG_CPU_HUMAN_NAME", getattr(self.cpu, "human_name", "Unknown"))
        if hasattr(self.cpu, "nop"):
            self.add_constant("CONFIG_CPU_NOP", self.cpu.nop)

    def add_timer(self, name="timer0"):
        self.check_if_exists(name)
        setattr(self.submodules, name, Timer())
        self.csr.add(name, use_loc_if_exists=True)
        if hasattr(self.cpu, "interrupt"):
            self.irq.add(name, use_loc_if_exists=True)

    def do_finalize(self):
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(colorer("Finalized SoC:"))
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(self.bus)
        self.logger.info(self.csr)
        self.logger.info(self.irq)
        self.logger.info(colorer("-"*80, color="bright"))

        if len(self.bus.masters) and len(self.bus.slaves):
            # If 1 bus_master, 1 bus_slave and no address translation, use InterconnectPointToPoint.
            if ((len(self.bus.masters) == 1)  and
                (len(self.bus.slaves)  == 1)  and
                (next(iter(self.bus.regions.values())).origin == 0)):
                self.submodules.bus_interconnect = wishbone.InterconnectPointToPoint(
                    master = next(iter(self.bus.masters.values())),
                    slave  = next(iter(self.bus.slaves.values())))
            # Otherwise, use InterconnectShared.
            else:
                self.submodules.bus_interconnect = wishbone.InterconnectShared(
                    masters        = self.bus.masters.values(),
                    slaves         = [(self.bus.regions[n].decoder(self.bus), s) for n, s in self.bus.slaves.items()],
                    register       = True,
                    timeout_cycles = self.bus.timeout)
                if hasattr(self, "ctrl") and self.bus.timeout is not None:
                    if hasattr(self.ctrl, "bus_error"):
                        self.comb += self.ctrl.bus_error.eq(self.bus_interconnect.timeout.error)
            self.bus.logger.info("Interconnect: {} ({} <-> {}).".format(
                colorer(self.bus_interconnect.__class__.__name__),
                colorer(len(self.bus.masters)),
                colorer(len(self.bus.slaves))))
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
                slaves  = self.csr_bankarray.get_buses())

        # Add CSRs regions
        for name, csrs, mapaddr, rmap in self.csr_bankarray.banks:
            self.csr.add_region(name, SoCCSRRegion(
                origin   = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword  = self.csr.data_width,
                obj      = csrs))

        # Add Memory regions
        for name, memory, mapaddr, mmap in self.csr_bankarray.srams:
            self.csr.add_region(name + "_" + memory.name_override, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword = self.csr.data_width,
                obj     = memory))

        # Sort CSR regions by origin
        self.csr.regions = {k: v for k, v in sorted(self.csr.regions.items(), key=lambda item: item[1].origin)}

        # Add CSRs / Config items to constants
        for name, constant in self.csr_bankarray.constants:
            self.add_constant(name + "_" + constant.name, constant.value.value)

        if not isinstance(self.cpu, cpu.CPUNone):
            if "sram" not in self.bus.regions.keys():
                self.logger.error("CPU needs {} Region to be {} as Bus or Linker Region.".format(
                    colorer("sram"),
                    colorer("defined", color="red")))
                self.logger.error(self.bus)
                raise
            cpu_reset_address_valid = False
            for name, container in self.bus.regions.items():
                if self.bus.check_region_is_in(
                    region    = SoCRegion(origin=self.cpu.reset_address, size=self.bus.data_width//8),
                    container = container):
                    cpu_reset_address_valid = True
                    if name == "rom":
                        self.cpu.use_rom = True
            if not cpu_reset_address_valid:
                self.logger.error("CPU needs {} to be in a {} Region.".format(
                    colorer("reset address 0x{:08x}".format(self.cpu.reset_address)),
                    colorer("defined", color="red")))
                self.logger.error(self.bus)
                raise

        if hasattr(self, "cpu"):
            if hasattr(self.cpu, "interrupt"):
                for name, loc in sorted(self.irq.locs.items()):
                    if name in self.cpu.interrupts.keys():
                        continue
                    if hasattr(self, name):
                        module = getattr(self, name)
                        if not hasattr(module, "ev"):
                            self.logger.error("EventManager {} in {} SubModule.".format(
                                colorer("not found", color="red"),
                                colorer(name)))
                            raise
                        self.comb += self.cpu.interrupt[loc].eq(module.ev.irq)
                    self.add_constant(name + "_INTERRUPT", loc)

    def build(self, *args, **kwargs):
        self.build_name = kwargs.pop("build_name", self.platform.name)
        kwargs.update({"build_name": self.build_name})
        return self.platform.build(self, *args, **kwargs)

    def add_identifier(self, name="identifier", identifier="LiteX SoC", with_build_time=True):
        self.check_if_exists(name)
        if with_build_time:
            identifier += " " + build_time()
        setattr(self.submodules, name, Identifier(identifier))
        self.csr.add(name + "_mem", use_loc_if_exists=True)

    def add_uart(self, name, baudrate=115200, fifo_depth=16):
        from litex.soc.cores import uart

        # USB ACM (with ValentyUSB core)
        if name in ["usb_acm"]:
            from valentyusb.cpu import CDCUsb
            from valentyusb.io import IoBuf
            usb_pads = self.platform.request("usb")
            usb_iobuf = IoBuf(usb_pads.d_p, usb_pads.d_n, usb_pads.pullup)
            self.submodules.uart = CDCUsb(usb_iobuf)

        # Classic UART
        else:
            self.submodules.uart_phy = uart.UARTPHY(
                pads     = self.platform.request(name),
                clk_freq = self.sys_clk_freq,
                baudrate = baudrate)
            self.submodules.uart = ResetInserter()(uart.UART(self.uart_phy,
                tx_fifo_depth = fifo_depth,
                rx_fifo_depth = fifo_depth))

        self.csr.add("uart_phy", use_loc_if_exists=True)
        self.csr.add("uart", use_loc_if_exists=True)
        if hasattr(self.cpu, "interrupt"):
            self.irq.add("uart", use_loc_if_exists=True)
        else:
            self.add_constant("UART_POLLING")

    def add_sdram(self, name, phy, module, origin, size=None, with_soc_interconnect=True,
        l2_cache_size           = 8192,
        l2_cache_min_data_width = 128,
        l2_cache_reverse        = True,
        l2_cache_full_memory_we = True,
        **kwargs):

        # Imports
        from litedram.common import LiteDRAMNativePort
        from litedram.core import LiteDRAMCore
        from litedram.frontend.wishbone import LiteDRAMWishbone2Native
        from litedram.frontend.axi import LiteDRAMAXI2Native

        # LiteDRAM core
        self.submodules.sdram = LiteDRAMCore(
            phy             = phy,
            geom_settings   = module.geom_settings,
            timing_settings = module.timing_settings,
            clk_freq        = self.sys_clk_freq,
            **kwargs)
        self.csr.add("sdram")

        # Save SPD data to be able to verify it at runtime
        if hasattr(module, "_spd_data"):
            # pack the data into words of bus width
            bytes_per_word = self.bus.data_width // 8
            mem = [0] * math.ceil(len(module._spd_data) / bytes_per_word)
            for i in range(len(mem)):
                for offset in range(bytes_per_word):
                    mem[i] <<= 8
                    if self.cpu.endianness == "little":
                        offset = bytes_per_word - 1 - offset
                    spd_byte = i * bytes_per_word + offset
                    if spd_byte < len(module._spd_data):
                        mem[i] |= module._spd_data[spd_byte]
            self.add_rom(
                name="spd",
                origin=self.mem_map.get("spd", None),
                size=len(module._spd_data),
                contents=mem,
            )

        if not with_soc_interconnect: return

        # Compute/Check SDRAM size
        sdram_size = 2**(module.geom_settings.bankbits +
                         module.geom_settings.rowbits +
                         module.geom_settings.colbits)*phy.settings.databits//8
        if size is not None:
            sdram_size = min(sdram_size, size)

        # Add SDRAM region
        self.bus.add_region("main_ram", SoCRegion(origin=origin, size=sdram_size))

        if len(self.cpu.memory_buses):
            # When CPU has at least a direct memory bus, connect them directly to LiteDRAM.
            for mem_bus in self.cpu.memory_buses:
                # Request a LiteDRAM native port.
                port = self.sdram.crossbar.get_port()
                port.data_width = 2**int(math.log2(port.data_width)) # Round to nearest power of 2.

                # Check if bus is an AXI bus and connect it.
                if isinstance(mem_bus, axi.AXIInterface):
                    # If same data_width, connect it directly.
                    if port.data_width == mem_bus.data_width:
                        self.logger.info("Matching AXI MEM data width ({})\n".format(port.data_width))
                        self.submodules += LiteDRAMAXI2Native(
                            axi          = self.cpu.mem_axi,
                            port         = port,
                            base_address = self.bus.regions["main_ram"].origin)
                    # If different data_width, do the adaptation and connect it via Wishbone.
                    else:
                        self.logger.info("Converting MEM data width: {} to {} via Wishbone".format(
                            port.data_width,
                            self.cpu.mem_axi.data_width))
                        # FIXME: replace WB data-width converter with native AXI converter!!!
                        mem_wb  = wishbone.Interface(
                            data_width = self.cpu.mem_axi.data_width,
                            adr_width  = 32-log2_int(self.cpu.mem_axi.data_width//8))
                        # NOTE: AXI2Wishbone FSMs must be reset with the CPU!
                        mem_a2w = ResetInserter()(axi.AXI2Wishbone(
                            axi          = self.cpu.mem_axi,
                            wishbone     = mem_wb,
                            base_address = 0))
                        self.comb += mem_a2w.reset.eq(ResetSignal() | self.cpu.reset)
                        self.submodules += mem_a2w
                        litedram_wb = wishbone.Interface(port.data_width)
                        self.submodules += LiteDRAMWishbone2Native(
                            wishbone     = litedram_wb,
                            port         = port,
                            base_address = origin)
                        self.submodules += wishbone.Converter(mem_wb, litedram_wb)
                # Check if bus is a Native bus and connect it.
                if isinstance(mem_bus, LiteDRAMNativePort):
                    # If same data_width, connect it directly.
                    if port.data_width == mem_bus.data_width:
                        self.comb += mem_bus.cmd.connect(port.cmd)
                        self.comb += mem_bus.wdata.connect(port.wdata)
                        self.comb += port.rdata.connect(mem_bus.rdata)
                    # Else raise Error.
                    else:
                        raise NotImplementedError
        else:
            # When CPU has no direct memory interface, create a Wishbone Slave interface to LiteDRAM.

            # Request a LiteDRAM native port.
            port = self.sdram.crossbar.get_port()
            port.data_width = 2**int(math.log2(port.data_width)) # Round to nearest power of 2.

            # Create Wishbone Slave.
            wb_sdram = wishbone.Interface()
            self.bus.add_slave("main_ram", wb_sdram)

            # L2 Cache
            if l2_cache_size != 0:
                # Insert L2 cache inbetween Wishbone bus and LiteDRAM
                l2_cache_size = max(l2_cache_size, int(2*port.data_width/8)) # Use minimal size if lower
                l2_cache_size = 2**int(math.log2(l2_cache_size))                  # Round to nearest power of 2
                l2_cache_data_width = max(port.data_width, l2_cache_min_data_width)
                l2_cache            = wishbone.Cache(
                    cachesize = l2_cache_size//4,
                    master    = wb_sdram,
                    slave     = wishbone.Interface(l2_cache_data_width),
                    reverse   = l2_cache_reverse)
                if l2_cache_full_memory_we:
                    l2_cache = FullMemoryWE()(l2_cache)
                self.submodules.l2_cache = l2_cache
                litedram_wb = self.l2_cache.slave
            else:
                litedram_wb     = wishbone.Interface(port.data_width)
                self.submodules += wishbone.Converter(wb_sdram, litedram_wb)
            self.add_config("L2_SIZE", l2_cache_size)

            # Wishbone Slave <--> LiteDRAM bridge
            self.submodules.wishbone_bridge = LiteDRAMWishbone2Native(litedram_wb, port,
                base_address = self.bus.regions["main_ram"].origin)

_io_r0_2 = [
    ("clk48", 0, Pins("A9"),  IOStandard("LVCMOS33")),
    ("rst_n", 0, Pins("V17"), IOStandard("LVCMOS33")),

    ("usr_btn", 0, Pins("J17"), IOStandard("SSTL135_I")),

    ("rgb_led", 0,
        Subsignal("r", Pins("K4"), IOStandard("LVCMOS33")),
        Subsignal("g", Pins("M3"), IOStandard("LVCMOS33")),
        Subsignal("b", Pins("J3"), IOStandard("LVCMOS33")),
    ),

    ("user_led", 0, Pins("K4"), IOStandard("LVCMOS33")), # rgb_led.r
    ("user_led", 1, Pins("M3"), IOStandard("LVCMOS33")), # rgb_led.g
    ("user_led", 2, Pins("J3"), IOStandard("LVCMOS33")), # rgb_led.b

    ("ddram", 0,
        Subsignal("a", Pins(
            "C4 D2 D3 A3 A4 D4 C3 B2",
            "B1 D1 A7 C2 B6 C1 A2 C7"),
            IOStandard("SSTL135_I")),
        Subsignal("ba",    Pins("D6 B7 A6"), IOStandard("SSTL135_I"),),
        Subsignal("ras_n", Pins("C12"), IOStandard("SSTL135_I")),
        Subsignal("cas_n", Pins("D13"), IOStandard("SSTL135_I")),
        Subsignal("we_n",  Pins("B12"), IOStandard("SSTL135_I")),
        Subsignal("cs_n",  Pins("A12"), IOStandard("SSTL135_I")),
        Subsignal("dm", Pins("D16 G16"), IOStandard("SSTL135_I")),
        Subsignal("dq", Pins(
            "C17 D15 B17 C16 A15 B13 A17 A13",
            "F17 F16 G15 F15 J16 C18 H16 F18"),
            IOStandard("SSTL135_I"),
            Misc("TERMINATION=75")),
        Subsignal("dqs_p", Pins("B15 G18"), IOStandard("SSTL135D_I"),
            Misc("TERMINATION=OFF"),
            Misc("DIFFRESISTOR=100")),
        Subsignal("clk_p", Pins("J18"), IOStandard("SSTL135D_I")),
        Subsignal("cke",   Pins("D18"), IOStandard("SSTL135_I")),
        Subsignal("odt",   Pins("C13"), IOStandard("SSTL135_I")),
        Subsignal("reset_n", Pins("L18"), IOStandard("SSTL135_I")),
        Subsignal("vccio", Pins("K16 D17 K15 K17 B18 C6"), IOStandard("SSTL135_II")),
        Subsignal("gnd",   Pins("L15 L16"), IOStandard("SSTL135_II")),
        Misc("SLEWRATE=FAST")
    ),

    ("usb", 0,
        Subsignal("d_p", Pins("N1")),
        Subsignal("d_n", Pins("M2")),
        Subsignal("pullup", Pins("N2")),
        IOStandard("LVCMOS33")
    ),
]

_connectors_r0_2 = [
    ("GPIO", "N17 M18 C10 C9 - B10 B9 - - C8 B8 A8 H2 J2 N15 R17 N16 - L4 N3 N4 H4 G4 T17"),
]

class Platform(LatticePlatform):
    default_clk_name   = "clk48"
    default_clk_period = 1e9/48e6

    def __init__(self):
        self.revision = "0.2"
        LatticePlatform.__init__(self, "LFE5U-25F-8MG285C", _io_r0_2, _connectors_r0_2, toolchain="trellis")

    def do_finalize(self, fragment):
        LatticePlatform.do_finalize(self, fragment)
        self.add_period_constraint(self.lookup_request("clk48", loose=True), 1e9/48e6)

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

def platform_request_all(platform, name):
    from litex.build.generic_platform import ConstraintError
    r = []
    while True:
        try:
            r += [platform.request(name, len(r))]
        except ConstraintError:
            break
    if r == []:
        raise ValueError
    return r

class Waltraud(SoC):
    csr_map = {
        "ctrl":     0,
        "uart":     2,
        "timer0":   3,
    }
    irq_map = {
        "uart":     0,
        "timer0":   1,
    }
    mem_map = {
        "rom":      0x00000000,
        "sram":     0x01000000,
        "main_ram": 0x40000000,
        "csr":      0xf0000000,
    }

    def __init__(self, _sys_clk_freq=64e6):

        platform = Platform()

        SoC.__init__(self, platform, _sys_clk_freq,
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
            csr_reserved_csrs    = self.csr_map,

            irq_n_irqs           = 32,
            irq_reserved_irqs    = {},
        )

        # Attributes
        self.mem_regions = self.bus.regions
        self.clk_freq    = self.sys_clk_freq
        self.mem_map     = self.mem_map
        self.config      = {}

        self.cpu_type    = "picorv32"
        self.cpu_variant = "minimal"
        self.cpu_cls     = None

        self.integrated_rom_size        = 0x10000
        self.integrated_rom_initialized = False
        #self.integrated_sram_size       = integrated_sram_size
        #self.integrated_main_ram_size   = integrated_main_ram_size

        #self.csr_data_width             = csr_data_width

        self.wb_slaves = {}

        # Add SoCController
        self.add_controller("ctrl")

        # Add CPU
        self.add_cpu(name=self.cpu_type, variant=self.cpu_variant, cls=self.cpu_cls, reset_address=None)

        # Add User's interrupts
        for name, loc in self.irq_map.items():
            self.irq.add(name, loc)

        # Add integrated ROM
        self.add_rom("rom", self.cpu.reset_address, self.integrated_rom_size, [])

        # Add integrated SRAM
        self.add_ram("sram", self.mem_map["sram"], 0x2000)

        # Add Identifier
        self.add_identifier("identifier", identifier="Waltraud on OrangeCrab", with_build_time=True)

        # Add UART
        self.add_uart(name="usb_acm", baudrate=1e6, fifo_depth=16)

        # Add Timer
        self.add_timer(name="timer0")

        # Add CSR bridge
        self.add_csr_bridge(self.mem_map["csr"])

        self.submodules.crg = _CRG(platform, _sys_clk_freq)

        self.submodules.ddrphy = ECP5DDRPHY(platform.request("ddram"), sys_clk_freq=_sys_clk_freq)
        self.add_csr("ddrphy")
        self.comb += self.crg.stop.eq(self.ddrphy.init.stop)
        self.comb += self.crg.reset.eq(self.ddrphy.init.reset)
        self.add_sdram("sdram",
            phy                     = self.ddrphy,
            module                  = MT41K64M16(_sys_clk_freq, "1:2"),
            origin                  = self.mem_map["main_ram"],
            size                    = 0x40000000,
            l2_cache_size           = 2048,
            l2_cache_min_data_width = 128,
            l2_cache_reverse        = True
        )

    def add_interrupt(self, interrupt_name, interrupt_id=None, use_loc_if_exists=False):
        self.irq.add(interrupt_name, interrupt_id, use_loc_if_exists=use_loc_if_exists)

    def add_csr(self, csr_name, csr_id=None, use_loc_if_exists=False):
        self.csr.add(csr_name, csr_id, use_loc_if_exists=use_loc_if_exists)

    def initialize_rom(self, data):
        self.rom.mem.init = data

    def add_wb_master(self, wbm):
        self.bus.add_master(master=wbm)

    def add_wb_slave(self, address, interface, size=None):
        wb_name = None
        for name, region in self.bus.regions.items():
            if address == region.origin:
                wb_name = name
                break
        if wb_name is None:
            self.wb_slaves[address] = interface
        else:
            self.bus.add_slave(name=wb_name, slave=interface)

    def add_memory_region(self, name, origin, length, type="cached"):
        self.bus.add_region(name, SoCRegion(origin=origin, size=length,
            cached="cached" in type,
            linker="linker" in type))

    def register_mem(self, name, address, interface, size=0x10000000):
        self.bus.add_slave(name, interface, SoCRegion(origin=address, size=size))

    def register_rom(self, interface, rom_size=0xa000):
        self.bus.add_slave("rom", interface, SoCRegion(origin=self.cpu.reset_address, size=rom_size))

    def add_csr_region(self, name, origin, busword, obj):
        self.csr_regions[name] = SoCCSRRegion(origin, busword, obj)

    def do_finalize(self):
        # Retro-compatibility
        for address, interface in self.wb_slaves.items():
            wb_name = None
            for name, region in self.bus.regions.items():
                if address == region.origin:
                    wb_name = name
                    break
            self.bus.add_slave(name=wb_name, slave=interface)

        SoC.do_finalize(self)

        # Retro-compatibility
        for region in self.bus.regions.values():
            region.length = region.size
            region.type   = "cached" if region.cached else "io"
            if region.linker:
                region.type += "+linker"
        self.csr_regions = self.csr.regions
        for name, value in self.config.items():
            self.add_config(name, value)

soc_directory = os.path.abspath(os.path.join(os.path.dirname(__file__), "."))

def _makefile_escape(s):
    return s.replace("\\", "\\\\")

class Builder:
    def __init__(self, soc,
        output_dir       = None,
        gateware_dir     = None,
        software_dir     = None,
        include_dir      = None,
        generated_dir    = None,
        compile_software = True,
        compile_gateware = True,
        csr_json         = None,
        csr_csv          = None,
        csr_svd          = None,
        memory_x         = None,
        bios_options     = None):
        self.soc = soc

        # From Python doc: makedirs() will become confused if the path elements to create include '..'
        self.output_dir    = os.path.abspath(output_dir    or os.path.join("build", soc.platform.name))
        self.gateware_dir  = os.path.abspath(gateware_dir  or os.path.join(self.output_dir,   "gateware"))
        self.software_dir  = os.path.abspath(software_dir  or os.path.join(self.output_dir,   "software"))
        self.include_dir   = os.path.abspath(include_dir   or os.path.join(self.software_dir, "include"))
        self.generated_dir = os.path.abspath(generated_dir or os.path.join(self.include_dir,  "generated"))

        self.compile_software = compile_software
        self.compile_gateware = compile_gateware
        self.csr_csv  = csr_csv
        self.csr_json = csr_json
        self.csr_svd  = csr_svd
        self.memory_x = memory_x
        self.bios_options = bios_options

        self.software_packages = []
        for name in [ "libcompiler_rt", "libbase", "liblitedram", "bios" ]:
            self.add_software_package(name)

    def add_software_package(self, name, src_dir=None):
        if src_dir is None:
            src_dir = os.path.join(soc_directory, "software", name)
        self.software_packages.append((name, src_dir))

    def _generate_includes(self):
        os.makedirs(self.include_dir, exist_ok=True)
        os.makedirs(self.generated_dir, exist_ok=True)

        if self.soc.cpu_type is not None:
            variables_contents = []
            def define(k, v):
                variables_contents.append("{}={}\n".format(k, _makefile_escape(v)))

            for k, v in export.get_cpu_mak(self.soc.cpu, self.compile_software):
                define(k, v)
            define("COMPILER_RT_DIRECTORY", get_data_mod("software", "compiler_rt").data_location)
            define("SOC_DIRECTORY", soc_directory)
            variables_contents.append("export BUILDINC_DIRECTORY\n")
            define("BUILDINC_DIRECTORY", self.include_dir)
            for name, src_dir in self.software_packages:
                define(name.upper() + "_DIRECTORY", src_dir)

            if self.bios_options is not None:
                for option in self.bios_options:
                    define(option, "1")

            write_to_file(os.path.join(self.generated_dir, "variables.mak"), "".join(variables_contents))
            write_to_file(os.path.join(self.generated_dir, "output_format.ld"), export.get_linker_output_format(self.soc.cpu))
            write_to_file(os.path.join(self.generated_dir, "regions.ld"), export.get_linker_regions(self.soc.mem_regions))

        write_to_file(os.path.join(self.generated_dir, "mem.h"), export.get_mem_header(self.soc.mem_regions))
        write_to_file(os.path.join(self.generated_dir, "soc.h"), export.get_soc_header(self.soc.constants))
        write_to_file(os.path.join(self.generated_dir, "csr.h"), export.get_csr_header(regions=self.soc.csr_regions, constants=self.soc.constants, csr_base=self.soc.mem_regions['csr'].origin))
        write_to_file(os.path.join(self.generated_dir, "git.h"), export.get_git_header())

        if hasattr(self.soc, "sdram"):
            from litedram.init import get_sdram_phy_c_header
            write_to_file(os.path.join(self.generated_dir, "sdram_phy.h"), get_sdram_phy_c_header(self.soc.sdram.controller.settings.phy, self.soc.sdram.controller.settings.timing))

    def _generate_csr_map(self):
        if self.csr_json is not None:
            csr_dir = os.path.dirname(os.path.realpath(self.csr_json))
            os.makedirs(csr_dir, exist_ok=True)
            write_to_file(self.csr_json, export.get_csr_json(self.soc.csr_regions, self.soc.constants, self.soc.mem_regions))

        if self.csr_csv is not None:
            csr_dir = os.path.dirname(os.path.realpath(self.csr_csv))
            os.makedirs(csr_dir, exist_ok=True)
            write_to_file(self.csr_csv, export.get_csr_csv(self.soc.csr_regions, self.soc.constants, self.soc.mem_regions))

        if self.csr_svd is not None:
            svd_dir = os.path.dirname(os.path.realpath(self.csr_svd))
            os.makedirs(svd_dir, exist_ok=True)
            write_to_file(self.csr_svd, export.get_csr_svd(self.soc))

    def _generate_mem_region_map(self):
        if self.memory_x is not None:
            memory_x_dir = os.path.dirname(os.path.realpath(self.memory_x))
            os.makedirs(memory_x_dir, exist_ok=True)
            write_to_file(self.memory_x, export.get_memory_x(self.soc))

    def _prepare_rom_software(self):
        for name, src_dir in self.software_packages:
            dst_dir = os.path.join(self.software_dir, name)
            os.makedirs(dst_dir, exist_ok=True)

    def _generate_rom_software(self, compile_bios=True):
         for name, src_dir in self.software_packages:
            if name == "bios" and not compile_bios:
                pass
            else:
                dst_dir = os.path.join(self.software_dir, name)
                makefile = os.path.join(src_dir, "Makefile")
                if self.compile_software:
                    subprocess.check_call(["make", "-C", dst_dir, "-f", makefile])

    def _initialize_rom_software(self):
        bios_file = os.path.join(self.software_dir, "bios", "bios.bin")
        bios_data = common.get_mem_data(bios_file, self.soc.cpu.endianness)
        self.soc.initialize_rom(bios_data)

    def build(self, **kwargs):
        self.soc.platform.output_dir = self.output_dir
        os.makedirs(self.gateware_dir, exist_ok=True)
        os.makedirs(self.software_dir, exist_ok=True)

        self.soc.finalize()

        self._generate_includes()
        self._generate_csr_map()
        self._generate_mem_region_map()
        if self.soc.cpu_type is not None:
            if self.soc.cpu.use_rom:
                self._prepare_rom_software()
                self._generate_rom_software(not self.soc.integrated_rom_initialized)
                if self.soc.integrated_rom_size and self.compile_software:
                    if not self.soc.integrated_rom_initialized:
                        self._initialize_rom_software()

        if "run" not in kwargs:
            kwargs["run"] = self.compile_gateware
        vns = self.soc.build(build_dir=self.gateware_dir, **kwargs)
        self.soc.do_exit(vns=vns)
        return vns

def main():
    parser = argparse.ArgumentParser(description="Waltraud on OrangeCrab\n", formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--build", action="store_true", help="Build bitstream")
    parser.add_argument("--load",  action="store_true", help="Load bitstream")
    args = parser.parse_args()

    soc = Waltraud()

    Builder(soc, output_dir="build", csr_json="build/csr.json", bios_options=[]).build(build_name="waltraud", run=args.build)

    if args.load:
        DFUProg(vid="1209", pid="5af0").load_bitstream("build/gateware/waltraud.bit")

if __name__ == "__main__":
    main()
