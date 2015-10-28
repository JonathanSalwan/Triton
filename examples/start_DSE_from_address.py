
from triton import *

def cbefore(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())

if __name__ == '__main__':

    # Start the symbolic analysis from the 0x40056d to 0x4005c9
    startAnalysisFromAddr(0x40056d)
    stopAnalysisFromAddr(0x4005c9)

    addCallback(cbefore, IDREF.CALLBACK.BEFORE)

    # Run the instrumentation - Never returns
    runProgram()

