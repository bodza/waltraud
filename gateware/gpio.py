from eigen.fhdl.module import Module

from eigen.genlib.cdc import MultiReg

from gateware.csr import AutoCSR, CSRStatus, CSRStorage

class GPIOIn(Module, AutoCSR):
    def __init__(self, signal):
        self._in = CSRStatus("in", len(signal), description="GPIO Input(s) Status.")
        self.specials += MultiReg(signal, self._in.status)

class GPIOOut(Module, AutoCSR):
    def __init__(self, signal):
        self._out = CSRStorage("out", len(signal), description="GPIO Output(s) Control.")
        self.comb += signal.eq(self._out.storage)

class GPIOInOut(Module):
    def __init__(self, in_signal, out_signal):
        self.submodules.gpio_in  = GPIOIn(in_signal)
        self.submodules.gpio_out = GPIOOut(out_signal)

    def get_csrs(self):
        return self.gpio_in.get_csrs() + self.gpio_out.get_csrs()
