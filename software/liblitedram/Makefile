include ../include/generated/variables.mak
include ../common.mak

OBJECTS = sdram.o

all: liblitedram.a

liblitedram.a: $(OBJECTS)
	$(AR) crs liblitedram.a $(OBJECTS)

-include $(OBJECTS:.o=.d)

%.o: $(LIBLITEDRAM_DIRECTORY)/%.c
	$(compile)

%.o: %.S
	$(assemble)

.PHONY: all clean

clean:
	$(RM) $(OBJECTS) liblitedram.a
