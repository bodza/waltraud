include ../include/generated/variables.mak
include ../common.mak

ifeq ($(CPUENDIANNESS),big)
CFLAGS+=-D_YUGA_LITTLE_ENDIAN=0 -D_YUGA_BIG_ENDIAN=1 -Wno-missing-prototypes
else
CFLAGS+=-D_YUGA_LITTLE_ENDIAN=1 -D_YUGA_BIG_ENDIAN=0 -Wno-missing-prototypes
endif

OBJECTS=udivsi3.o umodsi3.o divsi3.o modsi3.o lshrdi3.o muldi3.o divdi3.o ashldi3.o ashrdi3.o udivmoddi4.o clzsi2.o ctzsi2.o udivdi3.o umoddi3.o moddi3.o ucmpdi2.o

all: libcompiler_rt.a

libcompiler_rt.a: $(OBJECTS)
	$(CC) -c $(CFLAGS) $(1) $(LIBCOMPILER_RT_DIRECTORY)/mulsi3.c -o mulsi3.o
	$(AR) crs libcompiler_rt.a $(OBJECTS) mulsi3.o

-include $(OBJECTS:.o=.d)

mulsi3.o: $(LIBCOMPILER_RT_DIRECTORY)/mulsi3.c
	$(compile)

%.o: $(LIBCOMPILER_RT_DIRECTORY)/builtins/%.c
	$(compile)

.PHONY: all clean

clean:
	$(RM) $(OBJECTS) $(OBJECTS:.o=.ts) $(OBJECTS:.o=.d) libcompiler_rt.a
