# Path to the pin kit directory
PIN_ROOT =	"../../.."

NAME = 		triton

CXX =		g++

INCLUDES =	-I$(PIN_ROOT)/source/include/pin \
		-I$(PIN_ROOT)/source/include/pin/gen \
		-I$(PIN_ROOT)/extras/components/include \
		-I$(PIN_ROOT)/extras/xed2-intel64/include \
		-I$(PIN_ROOT)/source/tools/InstLib \
		-I./src/includes

CXXFLAGS = 	$(INCLUDES) -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -Wall -Werror -Wno-unknown-pragmas \
		-fno-stack-protector -DTARGET_IA32E -DHOST_IA32E -fPIC -DTARGET_LINUX  \
		-O3 -fomit-frame-pointer -fno-strict-aliasing

LIBS =		-L$(PIN_ROOT)/intel64/lib \
		-L$(PIN_ROOT)/intel64/lib-ext \
		-L$(PIN_ROOT)/intel64/runtime/glibc \
		-L$(PIN_ROOT)/extras/xed2-intel64/lib \
		-lpin \
		-lxed \
		-ldwarf \
		-lelf \
		-ldl \
		-lz3

SRC = 		./src/core/core.cpp \
		./src/core/image.cpp \
		./src/core/instructions.cpp \
		./src/core/symbolicElement.cpp \
		./src/core/utils.cpp \
		./src/ir/add.cpp \
		./src/ir/branchs.cpp \
		./src/ir/cmp.cpp \
		./src/ir/mov.cpp \
		./src/ir/notImplemented.cpp \
		./src/ir/pop.cpp \
		./src/ir/push.cpp \
		./src/smt2lib/utils.cpp

OBJ = $(SRC:.cpp=.o)

all: $(NAME)

$(NAME): $(OBJ)
	$(CXX) -shared -Wl,--hash-style=sysv -Wl,-Bsymbolic -Wl,--version-script=$(PIN_ROOT)/source/include/pin/pintool.ver -o $(NAME).so $(OBJ) $(LIBS)

clean:
	 /bin/rm -f $(OBJ)

cleanall: clean
	 /bin/rm -f $(NAME).so

