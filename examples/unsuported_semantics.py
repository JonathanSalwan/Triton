
# Note: Display the list of unsuported semantics

from operator   import itemgetter
from triton     import *


unsuportedSemantics = dict()


def cbefore(instruction):
    if len(instruction.symbolicElements) == 0:
        mnemonic = opcodeToString(instruction.opcode)
        if mnemonic in unsuportedSemantics:
            unsuportedSemantics[mnemonic][1] += 1
        else:
            unsuportedSemantics.update({mnemonic: [instruction.address,1]})
    return


def cfini():
    l = unsuportedSemantics.items()
    l.sort(key=itemgetter(1), reverse=True)
    for i in l:
        print '%s at %x' %(i[0].lower(), i[1][0])
    return


if __name__ == '__main__':
    startAnalysisFromSymbol('main')
    addCallback(cbefore, IDREF.CALLBACK.BEFORE)
    addCallback(cfini, IDREF.CALLBACK.FINI)
    runProgram()

