include ../include/generated/variables.mak
include ../common.mak

CFLAGS += -Wno-missing-prototypes

OBJECTS = clzsi2.o mulsi3.o udivsi3.o umodsi3.o

all: libcompiler_rt.a

libcompiler_rt.a: $(OBJECTS)
	$(AR) crs libcompiler_rt.a $(OBJECTS)

-include $(OBJECTS:.o=.d)

%.o: $(LIBCOMPILER_RT_DIRECTORY)/%.c
	$(compile)

.PHONY: all clean

clean:
	$(RM) $(OBJECTS) $(OBJECTS:.o=.ts) $(OBJECTS:.o=.d) libcompiler_rt.a
