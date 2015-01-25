rm -rf obj-intel64
mkdir obj-intel64

CFLAGS="-DBIGARRAY_MULTIPLIER=1 -DUSING_XED -Wall -Werror -Wno-unknown-pragmas -fno-stack-protector -DTARGET_IA32E -DHOST_IA32E -fPIC -DTARGET_LINUX  -I../../../source/include/pin -I../../../source/include/pin/gen -I../../../extras/components/include -I./z3/src/api/c++ -I../../../extras/xed2-intel64/include -I../../../source/tools/InstLib -I./src/includes -O3 -fomit-frame-pointer -fno-strict-aliasing"

g++ $CFLAGS -c -o obj-intel64/core.o ./src/core/core.cpp 
echo "[+] core.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/instruction.o ./src/core/instructions.cpp 
echo "[+] instruction.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/image.o ./src/core/image.cpp 
echo "[+] image.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/symbolicElement.o ./src/core/symbolicElement.cpp 
echo "[+] symbolicElement.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/utils.o ./src/core/utils.cpp 
echo "[+] utils.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/pop.o ./src/ir/pop.cpp 
echo "[+] pop.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/push.o ./src/ir/push.cpp 
echo "[+] push.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/mov.o ./src/ir/mov.cpp 
echo "[+] mov.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/add.o ./src/ir/add.cpp 
echo "[+] add.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/cmp.o ./src/ir/cmp.cpp 
echo "[+] cmp.cpp compiled"

g++ $CFLAGS -c -o obj-intel64/notImplemented.o ./src/ir/notImplemented.cpp 
echo "[+] notImplemented.cpp compiled"


g++ -shared -Wl,--hash-style=sysv -Wl,-Bsymbolic -Wl,--version-script=../../../source/include/pin/pintool.ver \
-o obj-intel64/dse.so obj-intel64/*.o  -L../../../intel64/lib -L../../../intel64/lib-ext -L../../../intel64/runtime/glibc \
-L../../../extras/xed2-intel64/lib -lpin -lxed -ldwarf -lelf -ldl -lz3

