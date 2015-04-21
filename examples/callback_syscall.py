
from triton import *


def my_callback_after(instruction):
    print '%#x: %s' %(instruction.address, instruction.assembly)


def my_callback_syscall_entry(threadId, std):
    print 'Syscall Entry !'


def my_callback_syscall_exit(threadId, std):
    print 'Syscall Exit !'


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('main')

    addCallback(my_callback_after,          IDREF.CALLBACK.AFTER)
    addCallback(my_callback_syscall_entry,  IDREF.CALLBACK.SYSCALL_ENTRY)
    addCallback(my_callback_syscall_exit,   IDREF.CALLBACK.SYSCALL_EXIT)

    # Run the instrumentation - Never returns
    runProgram()

