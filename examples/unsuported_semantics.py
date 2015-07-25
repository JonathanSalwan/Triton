
# Note: Display the list of unsuported semantics

from operator   import itemgetter
from triton     import *


unsuportedSemantics = dict()


def cbefore(instruction):
    if len(instruction.getSymbolicExpressions()) == 0:
        mnemonic = opcodeToString(instruction.getOpcode())
        if mnemonic in unsuportedSemantics:
            unsuportedSemantics[mnemonic] += 1
        else:
            unsuportedSemantics.update({mnemonic: 1})
    return


def cfini():
    stats = getStats()
    print '============================================================='
    print 'Stats'
    print '============================================================='
    print 'Number of branches:              %d' %(stats['branches'])
    print 'Number of expressions:           %d' %(stats['expressions'])
    print 'Number of unknown expression:    %d' %(stats['unknownExpr'])
    print 'Time of the execution:           %d seconds' %(stats['time'])
    l = unsuportedSemantics.items()
    l.sort(key=itemgetter(1), reverse=True)
    print '============================================================='
    print 'Unsuported Semantics'
    print '============================================================='
    for i in l:
        print '%s: %d' %(i[0].lower(), i[1])
    print '============================================================='
    return


if __name__ == '__main__':
    startAnalysisFromSymbol('main')
    addCallback(cbefore, IDREF.CALLBACK.BEFORE)
    addCallback(cfini, IDREF.CALLBACK.FINI)
    runProgram()

