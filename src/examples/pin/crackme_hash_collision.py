
from triton     import *
from triton.ast import *
from pintool    import *

#
# This example breaks a simple hash routine.
#
# Check the ./src/samples/crackmes/crackme_hash.c file. This file builds 
# a 'hash' and checks the checksum 0xad6d.
#
# The needed password is 'elite'. Example:
# $ ./src/samples/crackmes/crackme_hash elite
# Win
#
# This Triton code will try to break and find a hash collision.
#
# $ ./build/triton ./src/examples/pin/crackme_hash_collision.py ./src/samples/crackmes/crackme_hash aaaaa
# [+] Please wait, computing in progress...
# {0L: "0x6c, 'l'", 1L: "0x72, 'r'", 2L: "0x64, 'd'", 3L: "0x78, 'x'", 4L: "0x71, 'q'"}
# {0L: "0x70, 'p'", 1L: "0x61, 'a'", 2L: "0x69, 'i'", 3L: "0x71, 'q'", 4L: "0x64, 'd'"}
# {0L: "0x70, 'p'", 1L: "0x69, 'i'", 2L: "0x69, 'i'", 3L: "0x71, 'q'", 4L: "0x6c, 'l'"}
# {0L: "0x70, 'p'", 1L: "0x69, 'i'", 2L: "0x61, 'a'", 3L: "0x69, 'i'", 4L: "0x6c, 'l'"}
# {0L: "0x70, 'p'", 1L: "0x69, 'i'", 2L: "0x71, 'q'", 3L: "0x79, 'y'", 4L: "0x6c, 'l'"}
# {0L: "0x70, 'p'", 1L: "0x61, 'a'", 2L: "0x71, 'q'", 3L: "0x79, 'y'", 4L: "0x64, 'd'"}
# {0L: "0x68, 'h'", 1L: "0x61, 'a'", 2L: "0x71, 'q'", 3L: "0x61, 'a'", 4L: "0x64, 'd'"}
# {0L: "0x68, 'h'", 1L: "0x69, 'i'", 2L: "0x71, 'q'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# {0L: "0x68, 'h'", 1L: "0x69, 'i'", 2L: "0x79, 'y'", 3L: "0x69, 'i'", 4L: "0x6c, 'l'"}
# {0L: "0x68, 'h'", 1L: "0x61, 'a'", 2L: "0x79, 'y'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# {0L: "0x68, 'h'", 1L: "0x65, 'e'", 2L: "0x75, 'u'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# {0L: "0x68, 'h'", 1L: "0x65, 'e'", 2L: "0x75, 'u'", 3L: "0x69, 'i'", 4L: "0x64, 'd'"}
# {0L: "0x68, 'h'", 1L: "0x6d, 'm'", 2L: "0x75, 'u'", 3L: "0x69, 'i'", 4L: "0x6c, 'l'"}
# {0L: "0x64, 'd'", 1L: "0x6d, 'm'", 2L: "0x71, 'q'", 3L: "0x69, 'i'", 4L: "0x6c, 'l'"}
# {0L: "0x6c, 'l'", 1L: "0x6d, 'm'", 2L: "0x71, 'q'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# {0L: "0x6c, 'l'", 1L: "0x6d, 'm'", 2L: "0x71, 'q'", 3L: "0x69, 'i'", 4L: "0x64, 'd'"}
# {0L: "0x64, 'd'", 1L: "0x6d, 'm'", 2L: "0x61, 'a'", 3L: "0x61, 'a'", 4L: "0x64, 'd'"}
# {0L: "0x64, 'd'", 1L: "0x75, 'u'", 2L: "0x61, 'a'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# {0L: "0x6c, 'l'", 1L: "0x75, 'u'", 2L: "0x71, 'q'", 3L: "0x69, 'i'", 4L: "0x6c, 'l'"}
# {0L: "0x64, 'd'", 1L: "0x65, 'e'", 2L: "0x71, 'q'", 3L: "0x61, 'a'", 4L: "0x6c, 'l'"}
# loose
#
# Triton found several collisions. Example with the first collision:
# $ ./src/samples/crackmes/crackme_hash lrdxq
# Win
# $
#


def cafter(instruction):

    # movzx  eax,BYTE PTR [rax]
    # RAX points on the user password
    if instruction.getAddress() == 0x40057b:
        convertRegisterToSymbolicVariable(REG.RSI)

    # mov eax,DWORD PTR [rbp-0x4]
    # RAX must be equal to 0xad6d to win
    if instruction.getAddress() == 0x4005ce:
        print '[+] Please wait, computing in progress...'
        raxId = getSymbolicRegisterId(REG.RAX)
        raxExpr = getFullAstFromId(raxId)

        SymVar_0 = getSymbolicVariableFromName('SymVar_0')
        SymVar_1 = getSymbolicVariableFromName('SymVar_1')
        SymVar_2 = getSymbolicVariableFromName('SymVar_2')
        SymVar_3 = getSymbolicVariableFromName('SymVar_3')
        SymVar_4 = getSymbolicVariableFromName('SymVar_4')

        # We want printable characters
        expr = compound([
                 assert_(bvugt(variable(SymVar_0), bv(96,  CPUSIZE.QWORD_BIT))),
                 assert_(bvult(variable(SymVar_0), bv(123, CPUSIZE.QWORD_BIT))),
                 assert_(bvugt(variable(SymVar_1), bv(96,  CPUSIZE.QWORD_BIT))),
                 assert_(bvult(variable(SymVar_1), bv(123, CPUSIZE.QWORD_BIT))),
                 assert_(bvugt(variable(SymVar_2), bv(96,  CPUSIZE.QWORD_BIT))),
                 assert_(bvult(variable(SymVar_2), bv(123, CPUSIZE.QWORD_BIT))),
                 assert_(bvugt(variable(SymVar_3), bv(96,  CPUSIZE.QWORD_BIT))),
                 assert_(bvult(variable(SymVar_3), bv(123, CPUSIZE.QWORD_BIT))),
                 assert_(bvugt(variable(SymVar_4), bv(96,  CPUSIZE.QWORD_BIT))),
                 assert_(bvult(variable(SymVar_4), bv(123, CPUSIZE.QWORD_BIT))),
                 assert_(equal(raxExpr, bv(0xad6d, CPUSIZE.QWORD_BIT)))  # collision: (assert (= rax 0xad6d)
               ])

        # Get max 20 different models
        models = getModels(expr, 20)
        for model in models:
            print {k: "0x%x, '%c'" % (v.getValue(), v.getValue()) for k, v in model.items()}


if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    startAnalysisFromSymbol('check')
    insertCall(cafter, INSERT_POINT.AFTER)
    runProgram()

