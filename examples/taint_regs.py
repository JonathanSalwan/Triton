
from triton import *


def fini():
    saveTrace('trace.log')


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    # Taint the RAX and RBX registers when the address 0x40058e is executed
    taintRegFromAddr(0x40058e, [IDREF.REG.RAX, IDREF.REG.RBX])

    # Untaint the RCX register when the address 0x40058e is executed
    untaintRegFromAddr(0x40058e, [IDREF.REG.RCX])

    # When the instruction is over, call the fini function
    addCallback(fini, IDREF.CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()

