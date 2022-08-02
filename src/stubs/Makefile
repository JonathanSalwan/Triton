SRC  	= triton-stubs.c
CFLAGS 	= -c -fno-stack-protector -fno-builtin -fPIC -fno-asynchronous-unwind-tables
CC 	= gcc

all: 64b 32b

64b:
	$(CC) $(SRC) $(CFLAGS) -o triton-x8664-systemv-stubs.o -D STUB_ABI=sysv_abi
	$(CC) $(SRC) $(CFLAGS) -o triton-x8664-ms-stubs.o -D STUB_ABI=ms_abi

32b:
	$(CC) $(SRC) $(CFLAGS) -m32 -o triton-i386-cdecl-stubs.o -D STUB_ABI=cdecl
	$(CC) $(SRC) $(CFLAGS) -m32 -o triton-i386-stdcall-stubs.o -D STUB_ABI=stdcall
	$(CC) $(SRC) $(CFLAGS) -m32 -o triton-i386-fastcall-stubs.o -D STUB_ABI=fastcall

clean:
	rm triton-x8664-systemv-stubs.o
	rm triton-x8664-ms-stubs.o
	rm triton-i386-cdecl-stubs.o
	rm triton-i386-stdcall-stubs.o
	rm triton-i386-fastcall-stubs.o

.PHONY: clean install all
