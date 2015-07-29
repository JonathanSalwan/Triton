from triton import *
import  smt2lib
import sys

GREEN = "\033[92m"
RED   = "\033[91m"
ENDC  = "\033[0m"

#
# Test 1
# Symbolic memory check
#
def sbefore(instruction):
    concretizeAllMem()
    concretizeAllReg()
    for op in instruction.getOperands():
        if op.getType() == IDREF.OPERAND.MEM_R or op.getType() == IDREF.OPERAND.MEM_W: # The instruction must have a memory access
            symId = getMemSymbolicID(op.getMem().getAddress())
            if symId == IDREF.MISC.UNSET: # Case which wasn't handle
                addr = op.getMem().getAddress()
                if addr != 0: # Check valid address
                    print instruction.getDisassembly(), "at", hex(addr)
                    print "Operand mem size:", op.getMem().getSize()
                    s = convertMemToSymVar(addr, op.getMem().getSize(), "test") # convertMemToSymVar
                    print "New symbolic variable:"
                    print "[+] Comment:", s.getComment()
                    print "[+] Size: %d" % (s.getSize())
                    print "[+] Concrete value: 0x%x" % (s.getConcreteValue())
                    print "[+] Address: 0x%x" % (s.getKindValue())
                    memExpr = getFullExpression(getSymExpr(getMemSymbolicID(op.getMem().getAddress())).getAst())
                    expr = smt2lib.smtAssert(smt2lib.equal(memExpr, smt2lib.bv(1, s.getSize())))
                    print expr
                    model = getModel(expr)
                    print model

    return

if __name__ == '__main__':
    startAnalysisFromSymbol('check')
    addCallback(sbefore, IDREF.CALLBACK.BEFORE_SYMPROC)
    runProgram()

