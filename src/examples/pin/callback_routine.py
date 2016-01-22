
from triton  import *
from pintool import *

# Output
#
# $ ./triton ./src/examples/pin/callback_routine.py  ./src/samples/vulns/testSuite
# -> malloc(0x20)
# <- 0x8fc010
# -> malloc(0x20)
# <- 0x8fc040
# -> malloc(0x20)
# <- 0x8fc010


def mallocEntry(threadId):
    sizeAllocated = getCurrentRegisterValue(REG.RDI)
    print '-> malloc(%#x)' %(sizeAllocated)


def mallocExit(threadId):
    ptrAllocated = getCurrentRegisterValue(REG.RAX)
    print '<- %#x' %(ptrAllocated)


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Add a callback.
    addCallback(mallocEntry, CALLBACK.ROUTINE_ENTRY, "malloc")
    addCallback(mallocExit, CALLBACK.ROUTINE_EXIT, "malloc")

    # Run the instrumentation - Never returns
    runProgram()

