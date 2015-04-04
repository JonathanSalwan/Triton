
from triton import *


def my_callback_before(addr, threadId):
    print 'Before addr: %x | thread: %x' %(addr, threadId)


def my_callback_after(addr, threadId):
    print 'After addr: %x | thread: %x' %(addr, threadId)


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    # Add a callback
    addCallback(my_callback_before, CB_BEFORE)
    addCallback(my_callback_after, CB_AFTER)

    # Run the instrumentation - Never returns
    runProgram()

