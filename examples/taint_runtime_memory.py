
from triton import *

GREEN = "\033[92m"
ENDC  = "\033[0m"

# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed,
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):

    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)


def cafter(instruction):
    print '%#x: %s' %(instruction.address, instruction.assembly)
    for se in instruction.symbolicElements:
        if se.isTainted == True:
            print '\t -> %s%s%s' %(GREEN, se.expression, ENDC)
        else:
            print '\t -> %s' %(se.expression)
    print



if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

