include ../include/generated/variables.mak
include ../common.mak

OBJECTS = isr.o main.o

all: bios.bin
	$(PYTHON) -m litex.soc.software.memusage bios.elf $(CURDIR)/../include/generated/regions.ld riscv64-unknown-elf

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@
	chmod -x $@
ifeq ($(CPUENDIANNESS),little)
	$(PYTHON) -m litex.soc.software.mkmscimg $@ --little
else
	$(PYTHON) -m litex.soc.software.mkmscimg $@
endif

bios.elf: $(BIOS_DIRECTORY)/linker.ld $(OBJECTS)

%.elf: ../libbase/crt0.o ../libcompiler_rt/libcompiler_rt.a ../libbase/libbase-nofloat.a ../liblitedram/liblitedram.a
	$(LD) $(LDFLAGS) -T $(BIOS_DIRECTORY)/linker.ld -N -o $@ ../libbase/crt0.o $(OBJECTS) -L../libcompiler_rt -L../libbase -L../liblitedram -llitedram -lbase-nofloat -lcompiler_rt
	chmod -x $@

-include $(OBJECTS:.o=.d)

%.o: $(BIOS_DIRECTORY)/%.c
	$(compile)

clean:
	$(RM) $(OBJECTS) bios.elf bios.bin

.PHONY: all clean
