
from triton  import *
from pintool import *

# Output
#
# $ ./triton examples/callback_syscall.py  ./samples/crackmes/crackme_xor a
# sys_write(1, 7fb7f06e1000, 6)
# loose
#

def my_callback_syscall_entry(threadId, std):
    if getSyscallNumber(std) == SYSCALL.WRITE:
        arg0 = getSyscallArgument(std, 0)
        arg1 = getSyscallArgument(std, 1)
        arg2 = getSyscallArgument(std, 2)
        print 'sys_write(%x, %x, %x)' %(arg0, arg1, arg2)


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    addCallback(my_callback_syscall_entry, CALLBACK.SYSCALL_ENTRY)

    # Run the instrumentation - Never returns
    runProgram()

