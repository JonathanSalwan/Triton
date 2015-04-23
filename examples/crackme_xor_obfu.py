
from triton import *

_GREEN = "\033[92m"
_ENDC  = "\033[0m"


# Solution for ./samples/crackmes/crackme_xor_obfu.
#
# NOTE: doesn't works yet. Need more semantics supported.


def cbeforeSymProc(instruction):
    
    # 400544 mov [rbp+user_password], rdi
    # RDI points on the user password
    if instruction.address == 0x400544:
        rdi = getRegValue(IDREF.REG.RDI)
        taintMem(rdi)


def cafter(instruction):
    
    print '%#x: %s' %(instruction.address, instruction.assembly)

    for se in instruction.symbolicElements:
        if se.isTainted == True:
            print '%s\t -> %s%s' %(_GREEN, se.expression, _ENDC)
        else:
            print '%s\t -> %s%s' %(_ENDC, se.expression, _ENDC)

    # 400B69 cmp ecx, eax
    # eax = serial
    # ecx = user pwd
    if instruction.address == 0x400b69:
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        expr = getBacktrackedSymExpr(zfId)
        print {k: "0x%x, '%c'" % (v, v) for k, v in getModel(expr).items()}


def fini():
    saveTrace('trace.log')


if __name__ == '__main__':

    startAnalysisFromSymbol('check')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)
    addCallback(fini, IDREF.CALLBACK.FINI)

    runProgram()


