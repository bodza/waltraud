include ../include/generated/variables.mak
include ../common.mak

OBJECTS = exception.o libc.o errno.o crc16.o crc32.o console.o system.o uart.o time.o strtod.o strcasecmp.o div64.o progress.o memtest.o

all: crt0.o libbase-nofloat.a # libbase.a

libbase.a: $(OBJECTS) vsnprintf.o
	$(AR) crs libbase.a $(OBJECTS) vsnprintf.o

libbase-nofloat.a: $(OBJECTS) vsnprintf-nofloat.o
	$(AR) crs libbase-nofloat.a $(OBJECTS) vsnprintf-nofloat.o

-include $(OBJECTS:.o=.d)

vsnprintf-nofloat.o: $(LIBBASE_DIRECTORY)/vsnprintf.c
	$(call compile,-DNO_FLOAT)

%.o: $(LIBBASE_DIRECTORY)/%.c
	$(compile)

%.o: $(LIBBASE_DIRECTORY)/%.S
	$(assemble)

crt0.o: $(CPU_DIRECTORY)/crt0.S
	$(assemble)

.PHONY: all clean

clean:
	$(RM) $(OBJECTS) crt0.o vsnprintf.o vsnprintf-nofloat.o
	$(RM) libbase.a libbase-nofloat.a
