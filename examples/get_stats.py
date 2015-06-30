
from triton import *

# $ ./triton ./examples/get_stats.py ./samples/crackmes/crackme_xor elite
# Win
# Number of branches:              141
# Number of expressions:           3535
# Number of unknown expression:    103
# Time of the execution:           16 seconds
# $

def fini():
    stats = getStats()
    print 'Number of branches:              %d' %(stats['branches'])
    print 'Number of expressions:           %d' %(stats['expressions'])
    print 'Number of unknown expression:    %d' %(stats['unknownExpr'])
    print 'Time of the execution:           %d seconds' %(stats['time'])


if __name__ == '__main__':

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Dump stats at the end of the execution
    addCallback(fini, IDREF.CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()

