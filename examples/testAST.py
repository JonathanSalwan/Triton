from triton import *
import sys

GREEN = "\033[92m"
RED   = "\033[91m"
ENDC  = "\033[0m"

# Output
#
# $ ./triton ./examples/testAST.py ./samples/crackmes/crackme_xor a
# $ ./triton ./examples/testAST.py ./samples/ir_test_suite/ir
#
# Berfore to start this script, check if all instructions are suported with unsuported_semantics.py


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

            if seid == IDREF.MISC.UNSET or (reg >= IDREF.FLAG.AF and reg <= IDREF.FLAG.ZF):
                continue

            expr   = getFullExpression(getSymExpr(seid).getAst())
            svalue = evaluateAST(expr)

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
                sys.exit(-1)
    return


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cafter, IDREF.CALLBACK.AFTER)
    addCallback(sbefore, IDREF.CALLBACK.BEFORE_SYMPROC)

    # Run the instrumentation - Never returns
    runProgram()

