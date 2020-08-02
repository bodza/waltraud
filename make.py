#!/usr/bin/env python3

import argparse, math, os, struct, subprocess

from gateware.waltraud import CSRStatus, Memory, Waltraud, write_file

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
    def __init__(self, soc, output_dir="build"):
        self.soc = soc

        self.output_dir = os.path.abspath(output_dir)

        self.gateware_dir  = os.path.join(self.output_dir,   "gateware")
        self.software_dir  = os.path.join(self.output_dir,   "software")
        self.include_dir   = os.path.join(self.software_dir, "include")
        self.generated_dir = os.path.join(self.include_dir,  "generated")

        self.software_packages = []
        for name in [ "bios" ]:
            src_dir = os.path.abspath(os.path.join("software", name))
            self.software_packages.append((name, src_dir))

    def _generate_includes(self):
        os.makedirs(self.include_dir, exist_ok=True)
        os.makedirs(self.generated_dir, exist_ok=True)

        variables_contents = []
        def define(k, v):
            variables_contents.append("{}={}\n".format(k, v.replace("\\", "\\\\")))

        define("CPU", self.soc.cpu.name)
        define("CPUFLAGS", self.soc.cpu.gcc_flags)
        define("CPUENDIANNESS", self.soc.cpu.endianness)

        variables_contents.append("export BUILDINC_DIRECTORY\n")
        define("BUILDINC_DIRECTORY", self.include_dir)
        for name, src_dir in self.software_packages:
            define(name.upper() + "_DIRECTORY", src_dir)

        write_file(os.path.join(self.generated_dir, "variables.mak"), "".join(variables_contents))
        write_file(os.path.join(self.generated_dir, "output_format.ld"), _get_linker_output_format(self.soc.cpu))
        write_file(os.path.join(self.generated_dir, "regions.ld"), _get_linker_regions(self.soc.bus.regions))

        write_file(os.path.join(self.generated_dir, "mem.h"), _get_mem_header(self.soc.bus.regions))
        write_file(os.path.join(self.generated_dir, "soc.h"), _get_soc_header(self.soc.constants))
        write_file(os.path.join(self.generated_dir, "csr.h"), _get_csr_header(regions=self.soc.csr.regions, constants=self.soc.constants, csr_base=self.soc.bus.regions['csr'].origin))

    def _create_firmware(self):
        for name, src_dir in self.software_packages:
            dst_dir = os.path.join(self.software_dir, name)
            os.makedirs(dst_dir, exist_ok=True)
            makefile = os.path.join(src_dir, "Makefile")
            subprocess.check_call(["make", "-C", dst_dir, "-I", src_dir, "-f", makefile])

    def _set_firmware(self):
        bios_file = os.path.join(self.software_dir, "bios", "bios.bin")
        bios_data = _get_mem_data(bios_file, self.soc.cpu.endianness)
        self.soc.set_firmware(bios_data)

    def build(self, build_name, run):
        os.makedirs(self.gateware_dir, exist_ok=True)
        os.makedirs(self.software_dir, exist_ok=True)

        self.soc.platform.output_dir = self.output_dir
        self.soc.finalize()

        self._generate_includes()
        self._create_firmware()
        self._set_firmware()

        vns = self.soc.build(self.gateware_dir, build_name, run)
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

    Builder(soc).build("waltraud", args.build)

    if args.load:
        DFUProg(vid="1209", pid="5af0").load_bitstream("build/gateware/waltraud")

if __name__ == "__main__":
    main()
