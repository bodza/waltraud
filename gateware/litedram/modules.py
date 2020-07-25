from math import ceil

from eigen.fhdl.structure import log2_int

from .common import Settings, GeomSettings, TimingSettings

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
