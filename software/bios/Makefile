include ../include/generated/variables.mak
include ../common.mak

OBJECTS = crt0.o main.o uart.o

all: bios.bin
	$(BIOS_DIRECTORY)/../memusage.py bios.elf $(CURDIR)/../include/generated/regions.ld riscv64-unknown-elf

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@
	chmod -x $@
ifeq ($(CPUENDIANNESS),little)
	$(BIOS_DIRECTORY)/../mkmscimg.py $@ --little
else
	$(BIOS_DIRECTORY)/../mkmscimg.py $@
endif

bios.elf: $(BIOS_DIRECTORY)/linker.ld $(OBJECTS)
	$(LD) $(LDFLAGS) -T $(BIOS_DIRECTORY)/linker.ld -N -o $@ $(OBJECTS)
	chmod -x $@

-include $(OBJECTS:.o=.d)

%.o: $(BIOS_DIRECTORY)/%.c
	$(compile)

%.o: $(BIOS_DIRECTORY)/%.S
	$(assemble)

clean:
	$(RM) $(OBJECTS) bios.elf bios.bin

.PHONY: all clean
