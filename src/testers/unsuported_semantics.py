
# Note: Display the list of unsuported semantics

from operator   import itemgetter
from triton     import *
from pintool    import *


unsuportedSemantics = dict()


def cbefore(instruction):
    if len(instruction.getSymbolicExpressions()) == 0:
        mnemonic = instruction.getDisassembly().split(' ')[0]
        if mnemonic in unsuportedSemantics:
            unsuportedSemantics[mnemonic] += 1
        else:
            print instruction
            unsuportedSemantics.update({mnemonic: 1})
    return


def cafter(instruction):
    resetEngines()
    return


def cfini():
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
    setArchitecture(ARCH.X86_64)
    startAnalysisFromEntry()
    insertCall(cbefore, INSERT_POINT.BEFORE)
    insertCall(cafter,  INSERT_POINT.AFTER)
    insertCall(cfini,   INSERT_POINT.FINI)
    runProgram()

