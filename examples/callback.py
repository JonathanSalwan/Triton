
from triton import *


def my_callback_before(instruction):
    print 'TID (%d) %#x %s' %(instruction['threadId'], instruction['address'], instruction['assembly'])


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    # Add a callback
    addCallback(my_callback_before, CB_BEFORE)

    # Run the instrumentation - Never returns
    runProgram()

