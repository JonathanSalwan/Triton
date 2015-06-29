
# Note: Display the list of unsuported semantics

from operator   import itemgetter
from triton     import *


unsuportedSemantics = dict()


def cbefore(instruction):
    if len(instruction.symbolicExpressions) == 0:
        mnemonic = opcodeToString(instruction.opcode)
        if mnemonic in unsuportedSemantics:
            unsuportedSemantics[mnemonic] += 1
        else:
            unsuportedSemantics.update({mnemonic: 1})
    return


def cfini():
    l = unsuportedSemantics.items()
    l.sort(key=itemgetter(1), reverse=True)
    for i in l:
        print '%s: %d' %(i[0].lower(), i[1])
    return


if __name__ == '__main__':
    startAnalysisFromSymbol('main')
    addCallback(cbefore, IDREF.CALLBACK.BEFORE)
    addCallback(cfini, IDREF.CALLBACK.FINI)
    runProgram()

