
# Using: $ ./build/triton ./src/examples/pin/runtime_memory_tainting.py ./src/samples/crackmes/crackme_xor a

from triton  import *
from pintool import *

GREEN = "\033[92m"
ENDC  = "\033[0m"


# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed,
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):
    if instruction.getAddress() == 0x400574:
        rax = getCurrentRegisterValue(REG.RAX)
        taintMemory(rax)


def cafter(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
    for se in instruction.getSymbolicExpressions():
        if se.isTainted() == True:
            print '\t -> %s%s%s' %(GREEN, se.getAst(), ENDC)
        else:
            print '\t -> %s' %(se.getAst())
    print


if __name__ == '__main__':

    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    insertCall(cbeforeSymProc,  INSERT_POINT.BEFORE_SYMPROC)
    insertCall(cafter,          INSERT_POINT.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

