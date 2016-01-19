
from triton  import *
from smt2lib import *
from pintool import *

import sys

BLUE  = "\033[94m"
ENDC  = "\033[0m"
GREEN = "\033[92m"
RED   = "\033[91m"

# Output
#
# $ ./triton ./src/testers/check_semantics.py ./src/samples/ir_test_suite/ir
# [...]
# [OK] 0x400645: idiv rcx
# [OK] 0x400648: mov rax, 0x1
# [OK] 0x40064f: mov rcx, 0x2
# [OK] 0x400656: mov rdx, 0x3
# [OK] 0x40065d: mov rsi, 0x4
# [OK] 0x400664: imul sil
# [KO] 0x400667: imul cx (2 error)
#      Register       : cf
#      Symbolic Value : 0000000000000001
#      Concrete Value : 0000000000000000
#      Expression     : (ite (= ((_ extract 15 0) #348) ((_ extract 15 0) (_ bv2 64))) (_ bv0 1) (_ bv1 1))
#      Register       : of
#      Symbolic Value : 0000000000000001
#      Concrete Value : 0000000000000000
#      Expression     : (ite (= ((_ extract 15 0) #348) ((_ extract 15 0) (_ bv2 64))) (_ bv0 1) (_ bv1 1))


def sbefore(instruction):
    concretizeAllMem()
    concretizeAllReg()
    return


def cafter(instruction):

    bad  = list()
    regs = getParentRegisters()

    for reg in regs:

        cvalue = getCurrentRegisterValue(reg)
        seid   = getSymbolicRegisterId(reg)

        if seid == SYMEXPR.UNSET:
            continue

        expr   = getFullAstFromId(seid)
        svalue = evaluateAst(expr)

        if cvalue != svalue:
            bad.append({
                'reg':    reg.getName(),
                'svalue': svalue,
                'cvalue': cvalue,
                'expr':   expr
            })

    if len(instruction.getSymbolicExpressions()) == 0:
        print "[%s??%s] %#x: %s" %(BLUE, ENDC, instruction.getAddress(), instruction.getDisassembly())
        return

    if not bad:
        print "[%sOK%s] %#x: %s" %(GREEN, ENDC, instruction.getAddress(), instruction.getDisassembly())

    else:
        print "[%sKO%s] %#x: %s (%s%d error%s)" %(RED, ENDC, instruction.getAddress(), instruction.getDisassembly(), RED, len(bad), ENDC)
        for w in bad:
            print "     Register       : %s" %(w['reg'])
            print "     Symbolic Value : %016x" %(w['svalue'])
            print "     Concrete Value : %016x" %(w['cvalue'])
            print "     Expression     : %s" %(w['expr'])

    return


if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    startAnalysisFromEntry()
    addCallback(cafter,  CALLBACK.AFTER)
    addCallback(sbefore, CALLBACK.BEFORE_SYMPROC)
    runProgram()

