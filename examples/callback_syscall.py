
from triton import *

# Output
#
# $ ./triton examples/callback_syscall.py  ./samples/crackmes/crackme_xor a
# -> Syscall Entry: fstat
# <- Syscall return 0
# -> Syscall Entry: mmap
# <- Syscall return 7fb7f06e1000
# -> Syscall Entry: write
#    sys_write(1, 7fb7f06e1000, 6)
# loose
# <- Syscall return 6

def my_callback_syscall_entry(threadId, std):

    print '-> Syscall Entry: %s' %(syscallToString(std, getSyscallNumber(std)))

    if getSyscallNumber(std) == IDREF.SYSCALL.LINUX_64.WRITE:
        arg0 = getSyscallArgument(std, 0)
        arg1 = getSyscallArgument(std, 1)
        arg2 = getSyscallArgument(std, 2)
        print '   sys_write(%x, %x, %x)' %(arg0, arg1, arg2)


def my_callback_syscall_exit(threadId, std):
    print '<- Syscall return %x' %(getSyscallReturn(std))


if __name__ == '__main__':

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    addCallback(my_callback_syscall_entry,  IDREF.CALLBACK.SYSCALL_ENTRY)
    addCallback(my_callback_syscall_exit,   IDREF.CALLBACK.SYSCALL_EXIT)

    # Run the instrumentation - Never returns
    runProgram()

