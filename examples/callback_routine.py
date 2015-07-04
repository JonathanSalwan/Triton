
from triton import *

# Output
#
# $ ./triton examples/callback_routine.py  ./samples/vulns/testSuite
# -> malloc(0x20)
# <- 0x8fc010
# -> malloc(0x20)
# <- 0x8fc040
# -> malloc(0x20)
# <- 0x8fc010


def mallocEntry(threadId):
    sizeAllocated = getRegValue(IDREF.REG.RDI)
    print '-> malloc(%#x)' %(sizeAllocated)


def mallocExit(threadId):
    ptrAllocated = getRegValue(IDREF.REG.RAX)
    print '<- %#x' %(ptrAllocated)


if __name__ == '__main__':

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Add a callback.
    addCallback(mallocEntry, IDREF.CALLBACK.ROUTINE_ENTRY, "malloc")
    addCallback(mallocExit, IDREF.CALLBACK.ROUTINE_EXIT, "malloc")

    # Run the instrumentation - Never returns
    runProgram()

