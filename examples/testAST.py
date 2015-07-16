from triton import *

GREEN = "\033[92m"
RED   = "\033[91m"
ENDC  = "\033[0m"

# Output
#
# $ ./triton ./examples/testAST.py ./samples/crackmes/crackme_xor a
# $ ./triton ./examples/testAST.py ./samples/ir_test_suite/ir
#
# Berfore to start this script, check if all instructions are suported with unsuported_semantics.py

def cafter(instruction):
    if instruction.address < 0x600000: # To bypass external lib
        for op in instruction.operands:
            # TODO: should be a diff with all registers - getRegs()
            if op.type == IDREF.OPERAND.REG:
                idrefreg = op.value
                sid = getRegSymbolicID(idrefreg)
                if sid != IDREF.MISC.UNSET:

                    val = getRegValue(idrefreg)
                    exp = getFullExpression(getSymExpr(sid).getAst())

                    valAST =  evaluateAST(exp)

                    if valAST == val:
                        print "[%sOK%s] %#x: %s" %(GREEN, ENDC, instruction.address, instruction.assembly)
                    else:
                        print "[%sKO%s] %#x: %s" %(RED, ENDC, instruction.address, instruction.assembly)
                        print "    AST Value      :", hex(valAST)
                        print "    Expected Value :", hex(val)
                        print "    Expression     :", getSymExpr(sid).getAst() # print short expression (with references)
    return

if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

