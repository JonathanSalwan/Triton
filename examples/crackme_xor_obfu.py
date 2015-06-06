
import smt2lib
from triton import *

# PoC. Doesn't work yet
# $ triton ./examples/crackme_xor_obfu.py ./samples/crackmes/crackme_xor_obfu a

_GREEN = "\033[92m"
_ENDC  = "\033[0m"


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

    if instruction.address == 0x4011ed:
        raxId = getRegSymbolicID(IDREF.REG.RAX)
        raxExpr = getBacktrackedSymExpr(raxId)
        expr = smt2lib.smtAssert(smt2lib.equal(raxExpr, smt2lib.bv(0, 64))) # (assert (= rax 0)
        print expr
        print getModel(expr)


if __name__ == '__main__':

    startAnalysisFromAddr(0x4011dd)
    stopAnalysisFromAddr(0x40120b)

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    runProgram()

