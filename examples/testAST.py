from triton import *
import sys

GREEN = "\033[92m"
RED   = "\033[91m"
ENDC  = "\033[0m"

# Output
#
# $ ./triton ./examples/testAST.py ./samples/ir_test_suite/ir
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
    if instruction.address < 0x600000: # To bypass external lib

        bad  = list()
        regs = getRegs()

        for reg, data in regs.items():

            cvalue = data['concreteValue']
            seid   = data['symbolicExpr']


            if seid == IDREF.MISC.UNSET:
                continue
            #print "cvalue : %d"%cvalue
            #print "seid : %d"%seid
            #print "getSymExpr(seid)"
            #print dir(getSymExpr(seid))
            #print "getSymExpr(seid).getAst() : "
            #print getSymExpr(seid).getAst()

            expr   = getFullExpression(getSymExpr(seid).getAst())
            svalue = evaluateAST(expr)
            #print "expr : "
            #print dir(expr)
            #print "evaluateAST(expr) : "
            #print evaluateAST(expr)

            if cvalue != svalue:
                bad.append({
                    'reg': getRegName(reg),
                    'svalue': svalue,
                    'cvalue': cvalue,
                    'expr': getSymExpr(seid).getAst()
                })

        if not bad:
            print "[%sOK%s] %#x: %s" %(GREEN, ENDC, instruction.address, instruction.assembly)
        else:
            print "[%sKO%s] %#x: %s (%s%d error%s)" %(RED, ENDC, instruction.address, instruction.assembly, RED, len(bad), ENDC)
            for w in bad:
                print "     Register       : %s" %(w['reg'])
                print "     Symbolic Value : %016x" %(w['svalue'])
                print "     Concrete Value : %016x" %(w['cvalue'])
                print "     Expression     : %s" %(w['expr'])
    return


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cafter, IDREF.CALLBACK.AFTER)
    addCallback(sbefore, IDREF.CALLBACK.BEFORE_SYMPROC)

    # Run the instrumentation - Never returns
    runProgram()

