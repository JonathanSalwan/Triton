
from triton  import ARCH
from pintool import *

# Output
#
# $ ./build/triton ./src/examples/pin/callback_routine.py  ./src/samples/vulns/testSuite
# -> malloc(0x20)
# <- 0x8fc010
# -> malloc(0x20)
# <- 0x8fc040
# -> malloc(0x20)
# <- 0x8fc010

Triton = getTritonContext()

def mallocEntry(threadId):
    sizeAllocated = getCurrentRegisterValue(Triton.registers.rdi)
    print '-> malloc(%#x)' %(sizeAllocated)


def mallocExit(threadId):
    ptrAllocated = getCurrentRegisterValue(Triton.registers.rax)
    print '<- %#x' %(ptrAllocated)


if __name__ == '__main__':

    # Set the architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Add a callback.
    insertCall(mallocEntry, INSERT_POINT.ROUTINE_ENTRY, "malloc")
    insertCall(mallocExit, INSERT_POINT.ROUTINE_EXIT, "malloc")

    # Run the instrumentation - Never returns
    runProgram()

