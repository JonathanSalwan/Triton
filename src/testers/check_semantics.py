
from triton import *
import pintool as Pintool

import sys
import time

BLUE  = "\033[94m"
ENDC  = "\033[0m"
GREEN = "\033[92m"
RED   = "\033[91m"


# Get the Triton context over the pintool
Triton = Pintool.getTritonContext()

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
# [KO] 0x400667: imul cx (2 register error(s))
#      Register       : cf
#      Symbolic Value : 0000000000000001
#      Concrete Value : 0000000000000000
#      Expression     : (ite (= ((_ extract 15 0) #348) ((_ extract 15 0) (_ bv2 64))) (_ bv0 1) (_ bv1 1))
#      Register       : of
#      Symbolic Value : 0000000000000001
#      Concrete Value : 0000000000000000
#      Expression     : (ite (= ((_ extract 15 0) #348) ((_ extract 15 0) (_ bv2 64))) (_ bv0 1) (_ bv1 1))


def sbefore(instruction):
    Triton.concretizeAllMemory()
    Triton.concretizeAllRegister()
    return


def cafter(instruction):

    good = True
    bad  = list()
    regs = Triton.getParentRegisters()

    for reg in regs:

        cvalue = Pintool.getCurrentRegisterValue(reg)
        seid   = Triton.getSymbolicRegisterId(reg)

        if seid == SYMEXPR.UNSET:
            continue

        expr   = Triton.getFullAstFromId(seid)
        svalue = expr.evaluate()
        #svalue = Triton.evaluateAstViaZ3(expr)

        # Check register
        if cvalue != svalue:
            good = False
            bad.append({
                'reg':    reg.getName(),
                'svalue': svalue,
                'cvalue': cvalue,
                'expr':   expr
            })

    if bad:
        print "[%sKO%s] %#x: %s (%s%d register error(s)%s)" %(RED, ENDC, instruction.getAddress(), instruction.getDisassembly(), RED, len(bad), ENDC)
        for w in bad:
            print "     Register       : %s" %(w['reg'])
            print "     Symbolic Value : %016x" %(w['svalue'])
            print "     Concrete Value : %016x" %(w['cvalue'])
            print "     Expression     : %s" %(w['expr'])

    # Check memory access
    for op in instruction.getOperands():
        if op.getType() == OPERAND.MEM:
            nativeAddress = op.getAddress()
            astAddress = op.getLeaAst().evaluate()
            if nativeAddress != astAddress:
                good = False
                print "[%sKO%s] %#x: %s (%smemory error%s)" %(RED, ENDC, instruction.getAddress(), instruction.getDisassembly(), RED, ENDC)
                print "     Native address   : %016x" %(nativeAddress)
                print "     Symbolic address : %016x" %(astAddress)

    if len(instruction.getSymbolicExpressions()) == 0:
        print "[%s??%s] %#x: %s" %(BLUE, ENDC, instruction.getAddress(), instruction.getDisassembly())
        return

    if good:
        print "[%sOK%s] %#x: %s" %(GREEN, ENDC, instruction.getAddress(), instruction.getDisassembly())
        return
    else:
        #time.sleep(2)
        pass

    # Reset everything
    Triton.resetEngines()

    return


if __name__ == '__main__':
    Triton.setArchitecture(ARCH.X86_64)
    Pintool.startAnalysisFromEntry()
    #Pintool.startAnalysisFromSymbol('check')
    Pintool.insertCall(cafter,  Pintool.INSERT_POINT.AFTER)
    Pintool.insertCall(sbefore, Pintool.INSERT_POINT.BEFORE_SYMPROC)
    Pintool.runProgram()

