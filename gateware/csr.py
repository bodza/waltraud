from enum import IntEnum
from functools import reduce
from operator import or_

from eigen.fhdl.module import Module
from eigen.fhdl.specials import Memory
from eigen.fhdl.structure import bits_for, Case, Cat, DUID, If, log2_int, Signal
from eigen.fhdl.tracer import get_obj_var_name

from eigen.genlib.misc import chooser
from eigen.genlib.record import DIR_M_TO_S, DIR_S_TO_M, Record, set_layout_parameters

from eigen.util.misc import xdir

"""
Configuration and Status Registers
**********************************

The lowest-level description of a register is provided by the ``CSR`` class,
which maps to the value at a single address on the target bus. Also provided
are helper classes for dealing with values larger than the CSR buses data
width.

 * ``CSRConstant``, for constant values.
 * ``CSRStatus``,   for providing information to the CPU.
 * ``CSRStorage``,  for allowing control via the CPU.

Generating register banks
=========================
A module can provide bus-independent CSRs by implementing a ``get_csrs`` method
that returns a list of instances of the classes described above.

Similarly, bus-independent memories can be returned as a list by a
``get_memories`` method.

To avoid listing those manually, a module can inherit from the ``AutoCSR``
class, which provides ``get_csrs`` and ``get_memories`` methods that scan for
CSR and memory attributes and return their list.
"""

class _CSRBase(DUID):
    def __init__(self, size, name):
        DUID.__init__(self)
        self.name = get_obj_var_name(name)
        if self.name is None:
            raise ValueError("Cannot extract CSR name from code, need to specify.")
        self.size = size

class CSRConstant(DUID):
    """Register which contains a constant value.

    Useful for providing information on how a HDL was instantiated to firmware
    running on the device.
    """

    def __init__(self, value, bits_sign=None, name=None):
        DUID.__init__(self)
        self.value = Constant(value, bits_sign)
        self.name = get_obj_var_name(name)
        if self.name is None:
            raise ValueError("Cannot extract CSR name from code, need to specify.")

    def read(self):
        """Read method for simulation."""
        return self.value.value

class CSR(_CSRBase):
    """Basic CSR register.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits.
        Must be less than CSR bus width!

    name : string
        Provide (or override the name) of the CSR register.

    Attributes
    ----------
    r : Signal(size), out
        Contains the data written from the bus interface.
        ``r`` is only valid when ``re`` is high.

    re : Signal(), out
        The strobe signal for ``r``.
        It is active for one cycle, after or during a write from the bus.

    w : Signal(size), in
        The value to be read from the bus.
        Must be provided at all times.

    we : Signal(), out
        The strobe signal for ``w``.
        It is active for one cycle, after or during a read from the bus.
    """

    def __init__(self, size=1, name=None):
        _CSRBase.__init__(self, size, name)
        self.re = Signal(name=self.name + "_re")
        self.r  = Signal(self.size, name=self.name + "_r")
        self.we = Signal(name=self.name + "_we")
        self.w  = Signal(self.size, name=self.name + "_w")

    def read(self):
        """Read method for simulation."""
        yield self.we.eq(1)
        value = (yield self.w)
        yield
        yield self.we.eq(0)
        return value

    def write(self, value):
        """Write method for simulation."""
        yield self.r.eq(value)
        yield self.re.eq(1)
        yield
        yield self.re.eq(0)

class _CompoundCSR(_CSRBase, Module):
    def __init__(self, size, name):
        _CSRBase.__init__(self, size, name)
        self.simple_csrs = []

    def get_simple_csrs(self):
        if not self.finalized:
            raise FinalizeError
        return self.simple_csrs

    def do_finalize(self, busword):
        raise NotImplementedError

class CSRAccess(IntEnum):
    WriteOnly = 0
    ReadOnly  = 1
    ReadWrite = 2

class CSRField(Signal):
    """CSR Field.

    Parameters / Attributes
    -----------------------
    name : string
        Name of the CSR field.

    size : int
        Size of the CSR field in bits.

    offset : int (optional)
        Offset of the CSR field on the CSR register in bits.

    reset: int (optional)
        Reset value of the CSR field.

    description: string (optional)
        Description of the CSR Field (can be used to document the code and/or to be reused by tools
        to create the documentation).

    pulse: boolean (optional)
        Field value is only valid for one cycle when set to True. Only valid for 1-bit fields.

    access: enum (optional)
        Access type of the CSR field.

    values: list (optional)
        A list of supported values.
        If this is specified, a table will be generated containing the values in the specified order.
        The `value` must be an integer in order to allow for automatic constant generation in an IDE,
        except "do not care" bits are allowed.
        In the three-tuple variation, the middle value represents an enum value that can be displayed
        instead of the value.
                    [
                        ("0b0000", "disable the timer"),
                        ("0b0001", "slow", "slow timer"),
                        ("0b1xxx", "fast timer"),
                    ]
    """

    def __init__(self, name, size=1, offset=None, reset=0, description=None, pulse=False, access=None, values=None):
        assert access is None or (access in CSRAccess.values())
        self.name        = name
        self.size        = size
        self.offset      = offset
        self.reset_value = reset
        self.description = description
        self.access      = access
        self.pulse       = pulse
        self.values      = values
        Signal.__init__(self, size, name=name, reset=reset)

class CSRFieldAggregate:
    """CSR Field Aggregate."""

    def __init__(self, fields, access):
        self.check_names(fields)
        self.check_ordering_overlap(fields)
        self.fields = fields
        for field in fields:
            if field.access is None:
                field.access = access
            elif field.access == CSRAccess.ReadOnly:
                assert not field.pulse
                assert field.access == CSRAccess.ReadOnly
            elif field.access == CSRAccess.ReadWrite:
                assert field.access in [CSRAccess.ReadWrite, CSRAccess.WriteOnly]
                if field.pulse:
                    field.access = CSRAccess.WriteOnly
            setattr(self, field.name, field)

    @staticmethod
    def check_names(fields):
        names = []
        for field in fields:
            if field.name in names:
                raise ValueError("CSRField \"{}\" name is already used in CSR register".format(field.name))
            else:
                names.append(field.name)

    @staticmethod
    def check_ordering_overlap(fields):
        offset = 0
        for field in fields:
            if field.offset is not None:
                if field.offset < offset:
                    raise ValueError("CSRField ordering/overlap issue on \"{}\" field".format(field.name))
                offset = field.offset
            else:
                field.offset = offset
            offset += field.size

    def get_size(self):
        return self.fields[-1].offset + self.fields[-1].size

    def get_reset(self):
        reset = 0
        for field in self.fields:
            reset |= (field.reset_value << field.offset)
        return reset

class CSRStatus(_CompoundCSR):
    """Status Register.

    The ``CSRStatus`` class is meant to be used as a status register that is read-only from the CPU.

    The user design is expected to drive its ``status`` signal.

    The advantage of using ``CSRStatus`` instead of using ``CSR`` and driving ``w`` is that the
    width of ``CSRStatus`` can be arbitrary.

    Status registers larger than the bus word width are automatically broken down into several
    ``CSR`` registers to span several addresses.

    *Be careful, though:* the atomicity of reads is not guaranteed.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits.
        Can be bigger than the CSR bus width.

    reset : string
        Value of the register after reset.

    name : string
        Provide (or override the name) of the ``CSRStatus`` register.

    Attributes
    ----------
    status : Signal(size), in
        The value of the CSRStatus register.
    """

    def __init__(self, size=1, reset=0, fields=[], name=None, description=None):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadOnly)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, size, name)
        self.description = description
        self.status = Signal(self.size, reset=reset)
        self.we = Signal()
        for field in fields:
            self.comb += self.status[field.offset:field.offset + field.size].eq(getattr(self.fields, field.name))

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1)//busword
        for i in reversed(range(nwords)):
            nbits = min(self.size - i*busword, busword)
            sc = CSR(nbits, self.name + str(i) if nwords > 1 else self.name)
            self.comb += sc.w.eq(self.status[i*busword:i*busword+nbits])
            self.simple_csrs.append(sc)
        self.comb += self.we.eq(sc.we)

    def read(self):
        """Read method for simulation."""
        yield self.we.eq(1)
        value = (yield self.status)
        yield
        yield self.we.eq(0)
        return value

class CSRStorage(_CompoundCSR):
    """Control Register.

    The ``CSRStorage`` class provides a memory location that can be read and written by the CPU, and read and optionally written by the design.

    It can span several CSR addresses.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits. Can be bigger than the CSR bus width.

    reset : string
        Value of the register after reset.

    reset_less : bool
        If `True`, do not generate reset logic for CSRStorage.

    atomic_write : bool
        Provide an mechanism for atomic CPU writes is provided. When enabled, writes to the first
        CSR addresses go to a back-buffer whose contents are atomically copied to the main buffer
        when the last address is written.

    write_from_dev : bool
        Allow the design to update the CSRStorage value. *Warning*: The atomicity of reads by the
         CPU is not guaranteed.

    name : string
        Provide (or override the name) of the ``CSRStatus`` register.

    Attributes
    ----------
    storage : Signal(size), out
        Signal providing the value of the ``CSRStorage`` object.

    re : Signal(), in
        The strobe signal indicating a write to the ``CSRStorage`` register from the CPU. It is active
        for one cycle, after or during a write from the bus.

    we : Signal(), out
        The strobe signal to write to the ``CSRStorage`` register from the logic. Only available when
        ``write_from_dev == True``

    dat_w : Signal(), out
        The write data to write to the ``CSRStorage`` register from the logic. Only available when
        ``write_from_dev == True``
    """

    def __init__(self, size=1, reset=0, reset_less=False, fields=[], atomic_write=False, write_from_dev=False, name=None, description=None):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadWrite)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, size, name)
        self.description = description
        self.storage = Signal(self.size, reset=reset, reset_less=reset_less)
        self.atomic_write = atomic_write
        self.re = Signal()
        if write_from_dev:
            self.we = Signal()
            self.dat_w = Signal(self.size)
            self.sync += If(self.we, self.storage.eq(self.dat_w))
        for field in [*fields]:
            field_assign = getattr(self.fields, field.name).eq(self.storage[field.offset:field.offset + field.size])
            if field.pulse:
                self.comb += If(self.re, field_assign)
            else:
                self.comb += field_assign

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1)//busword
        if nwords > 1 and self.atomic_write:
            backstore = Signal(self.size - busword, name=self.name + "_backstore")
        for i in reversed(range(nwords)):
            nbits = min(self.size - i*busword, busword)
            sc = CSR(nbits, self.name + str(i) if nwords else self.name)
            self.simple_csrs.append(sc)
            lo = i*busword
            hi = lo+nbits
            # read
            self.comb += sc.w.eq(self.storage[lo:hi])
            # write
            if nwords > 1 and self.atomic_write:
                if i:
                    self.sync += If(sc.re, backstore[lo-busword:hi-busword].eq(sc.r))
                else:
                    self.sync += If(sc.re, self.storage.eq(Cat(sc.r, backstore)))
            else:
                self.sync += If(sc.re, self.storage[lo:hi].eq(sc.r))
        self.sync += self.re.eq(sc.re)

    def read(self):
        """Read method for simulation."""
        return (yield self.storage)

    def write(self, value):
        """Write method for simulation."""
        yield self.storage.eq(value)
        yield self.re.eq(1)
        if hasattr(self, "fields"):
            for field in [*self.fields.fields]:
                yield getattr(self.fields, field.name).eq((value >> field.offset) & (2**field.size -1))
        yield
        yield self.re.eq(0)
        if hasattr(self, "fields"):
            for field in [*self.fields.fields]:
                if field.pulse:
                    yield getattr(self.fields, field.name).eq(0)

def csrprefix(prefix, csrs, done):
    for csr in csrs:
        if csr.duid not in done:
            csr.name = prefix + csr.name
            done.add(csr.duid)

def memprefix(prefix, memories, done):
    for memory in memories:
        if memory.duid not in done:
            memory.name_override = prefix + memory.name_override
            done.add(memory.duid)

def _make_gatherer(method, cls, prefix_cb):
    def gatherer(self):
        try:
            exclude = self.autocsr_exclude
        except AttributeError:
            exclude = {}
        try:
            prefixed = self.__prefixed
        except AttributeError:
            prefixed = self.__prefixed = set()
        r = []
        for k, v in xdir(self, True):
            if k not in exclude:
                if isinstance(v, cls):
                    r.append(v)
                elif hasattr(v, method) and callable(getattr(v, method)):
                    items = getattr(v, method)()
                    prefix_cb(k + "_", items, prefixed)
                    r += items
        return sorted(r, key=lambda x: x.duid)
    return gatherer

class AutoCSR:
    """MixIn to provide bus independent access to CSR registers.

    A module can inherit from the ``AutoCSR`` class, which provides ``get_csrs``, ``get_memories``
    and ``get_constants`` methods that scan for CSR and memory attributes and return their list.

    If the module has child objects that implement ``get_csrs``, ``get_memories`` or ``get_constants``,
    they will be called by the``AutoCSR`` methods and their CSR and memories added to the lists returned,
    with the child objects' names as prefixes.
    """
    get_memories = _make_gatherer("get_memories", Memory, memprefix)
    get_csrs = _make_gatherer("get_csrs", _CSRBase, csrprefix)
    get_constants = _make_gatherer("get_constants", CSRConstant, csrprefix)

class GenericBank(Module):
    def __init__(self, description, busword):
        # Turn description into simple CSRs and claim ownership of compound CSR modules
        self.simple_csrs = []
        for c in description:
            if isinstance(c, CSR):
                assert c.size <= busword
                self.simple_csrs.append(c)
            else:
                c.finalize(busword)
                self.simple_csrs += c.get_simple_csrs()
                self.submodules += c
        self.decode_bits = bits_for(len(self.simple_csrs)-1)

"""
CSR-2 bus
=========

The CSR-2 bus is a low-bandwidth, resource-sensitive bus designed for accessing
the configuration and status registers of cores from software.
"""

_csr_bus_layout = [
    ("adr",  "address_width", DIR_M_TO_S),
    ("we",                 1, DIR_M_TO_S),
    ("dat_w",   "data_width", DIR_M_TO_S),
    ("dat_r",   "data_width", DIR_S_TO_M)
]

class CSRBusInterface(Record):
    def __init__(self, data_width=8, address_width=14, alignment=32):
        self.data_width    = data_width
        self.address_width = address_width
        self.alignment     = alignment
        Record.__init__(self, set_layout_parameters(_csr_bus_layout, data_width=data_width, address_width=address_width))
        self.adr.reset_less   = True
        self.dat_w.reset_less = True
        self.dat_r.reset_less = True

    @classmethod
    def like(self, other):
        return CSRBusInterface(len(other.dat_w), len(other.adr))

    def write(self, adr, dat):
        yield self.adr.eq(adr)
        yield self.dat_w.eq(dat)
        yield self.we.eq(1)
        yield
        yield self.we.eq(0)

    def read(self, adr):
        yield self.adr.eq(adr)
        yield
        yield
        return (yield self.dat_r)

class CSRBusInterconnect(Module):
    def __init__(self, master, slaves):
        self.comb += master.connect(*slaves)

class CSRBusInterconnectShared(Module):
    def __init__(self, masters, slaves):
        intermediate = CSRBusInterface.like(masters[0])
        self.comb += [
            intermediate.adr.eq(reduce(or_, [masters[i].adr for i in range(len(masters))])),
            intermediate.we.eq(reduce(or_, [masters[i].we for i in range(len(masters))])),
            intermediate.dat_w.eq(reduce(or_, [masters[i].dat_w for i in range(len(masters))]))
        ]
        for i in range(len(masters)):
            self.comb += masters[i].dat_r.eq(intermediate.dat_r)
        self.comb += intermediate.connect(*slaves)

class CSRBusSRAM(Module):
    def __init__(self, mem_or_size, address, read_only=None, init=None, bus=None, paging=0x800, soc_bus_data_width=32):
        if bus is None:
            bus = CSRBusInterface()
        self.bus = bus
        aligned_paging = paging//(soc_bus_data_width//8)
        data_width = len(self.bus.dat_w)
        if isinstance(mem_or_size, Memory):
            mem = mem_or_size
        else:
            mem = Memory(data_width, mem_or_size//(data_width//8), init=init)
        mem_size = int(mem.width*mem.depth/8)
        csrw_per_memw = (mem.width + data_width - 1)//data_width
        word_bits = log2_int(csrw_per_memw)
        page_bits = log2_int((mem.depth*csrw_per_memw + aligned_paging - 1)//aligned_paging, False)
        if page_bits:
            self._page = CSRStorage(page_bits, name=mem.name_override + "_page")
            printf("WARNING: SRAM CSR memory will requires paged access.")
        else:
            self._page = None
        if read_only is None:
            if hasattr(mem, "bus_read_only"):
                read_only = mem.bus_read_only
            else:
                read_only = False

        port = mem.get_port(write_capable=not read_only)
        self.specials += mem, port

        sel = Signal()
        sel_r = Signal()
        self.sync += sel_r.eq(sel)
        self.comb += sel.eq(self.bus.adr[log2_int(aligned_paging):] == address)

        if word_bits:
            word_index    = Signal(word_bits, reset_less=True)
            word_expanded = Signal(csrw_per_memw*data_width)
            self.sync += word_index.eq(self.bus.adr[:word_bits])
            self.comb += [
                word_expanded.eq(port.dat_r),
                If(sel_r, chooser(word_expanded, word_index, self.bus.dat_r, n=csrw_per_memw, reverse=True))
            ]
            if not read_only:
                wregs = []
                for i in range(csrw_per_memw-1):
                    wreg = Signal(data_width, reset_less=True)
                    self.sync += If(sel & self.bus.we & (self.bus.adr[:word_bits] == i), wreg.eq(self.bus.dat_w))
                    wregs.append(wreg)
                memword_chunks = [self.bus.dat_w] + list(reversed(wregs))
                self.comb += [
                    port.we.eq(sel & self.bus.we & (self.bus.adr[:word_bits] == csrw_per_memw - 1)),
                    port.dat_w.eq(Cat(*memword_chunks))
                ]
        else:
            self.comb += If(sel_r, self.bus.dat_r.eq(port.dat_r))
            if not read_only:
                self.comb += [
                    port.we.eq(sel & self.bus.we),
                    port.dat_w.eq(self.bus.dat_w)
                ]

        if self._page is None:
            self.comb += port.adr.eq(self.bus.adr[word_bits:word_bits+len(port.adr)])
        else:
            pv = self._page.storage
            self.comb += port.adr.eq(Cat(self.bus.adr[word_bits:word_bits+len(port.adr)-len(pv)], pv))

    def get_csrs(self):
        if self._page is None:
            return []
        else:
            return [self._page]

class CSRBank(GenericBank):
    def __init__(self, description, address=0, bus=None, paging=0x800, soc_bus_data_width=32):
        if bus is None:
            bus = CSRBusInterface()
        self.bus = bus
        aligned_paging = paging // (soc_bus_data_width // 8)

        GenericBank.__init__(self, description, len(self.bus.dat_w))

        sel = Signal()
        self.comb += sel.eq(self.bus.adr[log2_int(aligned_paging):] == address)

        for i, c in enumerate(self.simple_csrs):
            self.comb += [
                c.r.eq(self.bus.dat_w[:c.size]),
                c.re.eq(sel & self.bus.we & (self.bus.adr[:self.decode_bits] == i)),
                c.we.eq(sel & ~self.bus.we & (self.bus.adr[:self.decode_bits] == i)),
            ]

        brcases = dict((i, self.bus.dat_r.eq(c.w)) for i, c in enumerate(self.simple_csrs))
        self.sync += [
            self.bus.dat_r.eq(0),
            If(sel, Case(self.bus.adr[:self.decode_bits], brcases))
        ]

# address_map(name, memory) returns the CSR offset at which to map the CSR object (register bank or memory).
# If memory=None, the object is the register bank of object source.name.
# Otherwise, it is a memory object belonging to source.name.
# address_map is called exactly once for each object at each call to scan(), so it can have side effects.

class CSRBankArray(Module):
    def __init__(self, source, address_map, *ifargs, paging=0x800, soc_bus_data_width=32, **ifkwargs):
        self.source             = source
        self.address_map        = address_map
        self.paging             = paging
        self.soc_bus_data_width = soc_bus_data_width
        self.scan(ifargs, ifkwargs)

    def scan(self, ifargs, ifkwargs):
        self.banks = []
        self.srams = []
        self.constants = []
        for name, obj in xdir(self.source, True):
            if hasattr(obj, "get_csrs"):
                csrs = obj.get_csrs()
            else:
                csrs = []
            if hasattr(obj, "get_memories"):
                memories = obj.get_memories()
                for memory in memories:
                    if isinstance(memory, tuple):
                        read_only, memory = memory
                    else:
                        read_only = False
                    mapaddr = self.address_map(name, memory)
                    if mapaddr is None:
                        continue
                    sram_bus = CSRBusInterface(*ifargs, **ifkwargs)
                    mmap = CSRBusSRAM(memory, mapaddr,
                        read_only = read_only,
                        bus       = sram_bus,
                        paging    = self.paging)
                    self.submodules += mmap
                    csrs += mmap.get_csrs()
                    self.srams.append((name, memory, mapaddr, mmap))
            if hasattr(obj, "get_constants"):
                for constant in obj.get_constants():
                    self.constants.append((name, constant))
            if csrs:
                mapaddr = self.address_map(name, None)
                if mapaddr is None:
                    continue
                bank_bus = CSRBusInterface(*ifargs, **ifkwargs)
                rmap = CSRBank(csrs, mapaddr,
                    bus                = bank_bus,
                    paging             = self.paging,
                    soc_bus_data_width = self.soc_bus_data_width)
                self.submodules += rmap
                self.banks.append((name, csrs, mapaddr, rmap))

    def get_rmaps(self):
        return [rmap for name, csrs, mapaddr, rmap in self.banks]

    def get_mmaps(self):
        return [mmap for name, memory, mapaddr, mmap in self.srams]

    def get_buses(self):
        return [i.bus for i in self.get_rmaps() + self.get_mmaps()]
