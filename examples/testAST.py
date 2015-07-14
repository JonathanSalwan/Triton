from triton import *
# Output
#
# $ ./triton ./examples/testAST.py ./samples/crackmes/crackme_xor a
# $ ./triton ./examples/testAST.py ./samples/ir_test_suite/ir
#
# Berfore to start this script, check if all instructions are suported with unsuported_semantics.py

def cafter(instruction):
    if instruction.address < 0x600000: # To bypass external lib
        print instruction.assembly
        for op in instruction.operands:
            if op.type == IDREF.OPERAND.REG:
                idrefreg = op.value
                sid = getRegSymbolicID(idrefreg)
                if sid != IDREF.MISC.UNSET:

                    val = getRegValue(idrefreg)
                    exp = getFullExpression(getSymExpr(sid).getAst())

                    valAST =  evaluateAST(exp)

                    if valAST != val:
                        print "Error:"
                        print "\tAST Value:\t", hex(valAST)
                        print "\tRegister Value:\t", hex(val)
                        print "\tAddress:\t", hex(instruction.address)
                        print "\t", instruction.assembly
                        print getSymExpr(sid).getAst() # print short expression (with references)
                        #print exp # Print full expression
    return

if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

