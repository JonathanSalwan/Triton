SRC  	= triton-stubs.c
CFLAGS 	= -c -fno-stack-protector -fno-builtin -fPIC
CC 	= gcc

all: 64b 32b

64b:
	$(CC) $(SRC) $(CFLAGS) -o triton-x8664-systemv-stubs.o

32b:
	$(CC) $(SRC) $(CFLAGS) -m32 -o triton-i386-systemv-stubs.o

clean:
	rm triton-x8664-systemv-stubs.o

.PHONY: clean install all
