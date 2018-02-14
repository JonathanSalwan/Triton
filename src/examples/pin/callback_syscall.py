
from triton  import ARCH, SYSCALL64
from pintool import *

# Output
#
# $ ./build/triton ./src/examples/pin/callback_syscall.py  ./src/samples/crackmes/crackme_xor a
# sys_write(1, 7fb7f06e1000, 6)
# loose
#

def my_callback_syscall_entry(threadId, std):
    if getSyscallNumber(std) == SYSCALL64.WRITE:
        arg0 = getSyscallArgument(std, 0)
        arg1 = getSyscallArgument(std, 1)
        arg2 = getSyscallArgument(std, 2)
        print 'sys_write(%x, %x, %x)' %(arg0, arg1, arg2)


if __name__ == '__main__':
    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    insertCall(my_callback_syscall_entry, INSERT_POINT.SYSCALL_ENTRY)

    # Run the instrumentation - Never returns
    runProgram()
