include ../include/generated/variables.mak
include ../common.mak

OBJECTS = console.o libc.o uart.o vsnprintf.o

all: crt0.o libbase.a

libbase.a: $(OBJECTS)
	$(AR) crs libbase.a $(OBJECTS)

-include $(OBJECTS:.o=.d)

%.o: $(LIBBASE_DIRECTORY)/%.c
	$(compile)

%.o: $(LIBBASE_DIRECTORY)/%.S
	$(assemble)

crt0.o: $(CPU_DIRECTORY)/crt0.S
	$(assemble)

.PHONY: all clean

clean:
	$(RM) $(OBJECTS) crt0.o
	$(RM) libbase.a
