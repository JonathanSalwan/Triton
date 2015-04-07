
from triton import *

if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    # Taint the RAX and RBX registers when the address 0x40058e is executed
    taintRegFromAddr(0x40058e, [IDREF.REG.RAX, IDREF.REG.RBX])

    # Untaint the RCX register when the address 0x40058e is executed
    untaintRegFromAddr(0x40058e, [IDREF.REG.RCX])

    # Dump the symbolic trace at the end of the execution
    dumpTrace(True)

    # Run the instrumentation - Never returns
    runProgram()

