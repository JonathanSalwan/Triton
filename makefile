
NAME = 		triton

CXXFLAGS = 	-DBIGARRAY_MULTIPLIER=1 -DUSING_XED -Wall -Werror -Wno-unknown-pragmas \
		-fno-stack-protector -DTARGET_IA32E -DHOST_IA32E -fPIC -DTARGET_LINUX  \
		-I../../../source/include/pin -I../../../source/include/pin/gen \
		-I../../../extras/components/include -I./z3/src/api/c++ -I../../../extras/xed2-intel64/include \
		-I../../../source/tools/InstLib -I./src/includes -O3 -fomit-frame-pointer -fno-strict-aliasing

SRC = 		./src/core/core.cpp \
		./src/core/image.cpp \
		./src/core/instructions.cpp \
		./src/core/symbolicElement.cpp \
		./src/core/utils.cpp \
		./src/ir/pop.cpp \
		./src/ir/push.cpp \
		./src/ir/mov.cpp \
		./src/ir/add.cpp \
		./src/ir/cmp.cpp \
		./src/ir/notImplemented.cpp

OBJ = $(SRC:.cpp=.o)

all: $(NAME)

$(NAME): $(OBJ)
	g++ -shared -Wl,--hash-style=sysv -Wl,-Bsymbolic -Wl,--version-script=../../../source/include/pin/pintool.ver \
	-o $(NAME).so $(OBJ) -L../../../intel64/lib -L../../../intel64/lib-ext -L../../../intel64/runtime/glibc \
	-L../../../extras/xed2-intel64/lib -lpin -lxed -ldwarf -lelf -ldl -lz3

clean:
	 /bin/rm -f $(OBJ)
	 /bin/rm -f $(NAME).so

