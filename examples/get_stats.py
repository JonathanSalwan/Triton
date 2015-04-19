
from triton import *

# $ ../../../pin -t ./triton.so -script ./examples/get_stats.py -- ./samples/crackmes/crackme_xor a
# loose
# Number of branches:              230
# Number of expressions:           2063
# Number of unknown expression:    582
# Time of the execution:           6
# $

def fini():
    stats = getStats()
    print 'Number of branches:              %d' %(stats['branches'])
    print 'Number of expressions:           %d' %(stats['expressions'])
    print 'Number of unknown expression:    %d' %(stats['unknownExpr'])
    print 'Time of the execution:           %d' %(stats['time'])


if __name__ == '__main__':

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Dump stats at the end of the execution
    addCallback(fini, CB_FINI)

    # Run the instrumentation - Never returns
    runProgram()

