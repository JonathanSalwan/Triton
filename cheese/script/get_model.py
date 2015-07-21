
import smt2lib
from   triton import *

# $ ../../../pin -t ./triton.so -script ./examples/get_model.py -- ./samples/crackmes/crackme_xor elite
# {'SymVar_0': "0x65, 'e'"}
# {'SymVar_1': "0x6c, 'l'"}
# {'SymVar_2': "0x69, 'i'"}
# {'SymVar_3': "0x74, 't'"}
# {'SymVar_4': "0x65, 'e'"}
# Win
# $

# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed, 
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):
    if instruction.address == 0x400559:
        rax = getRegValue(IDREF.REG.RAX)
        print "%#x"%rax
        taintMem(rax)


# 0x4005ae: cmp ecx, eax
def cafter(instruction):
    
    if instruction.address == 0x400559:
        print instruction.assembly
        for se in instruction.symbolicElements:
            print "%#x :: %s"%(instruction.address, se.expression)

    if instruction.address == 0x400561:

        #for se in instruction.symbolicElements:
            #print dir(se)
            #print "%d : %s"%(se.id, se.expression)
        print dir(smt2lib)
        print "### take one"
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        zfExpr = getBacktrackedSymExpr(zfId)

        
        print "zfId"
        print zfId
        print "zfExpr"
        print zfExpr
        print "smt2lib.bvtrue"
        print smt2lib.bvtrue()
        expr = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvfalse())) # (assert (= zf True))
        print expr
        print "getmodel"
        print getModel(expr)
        
        print {k: "0x%x, '%c'" % (v, v) for k, v in getModel(expr).items()}
    """
    if instruction.address == 0x400567:
        print "### take two"
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        zfExpr = getBacktrackedSymExpr(zfId)
        print zfId
        print zfExpr
        print "-"
        print smt2lib.bvtrue()
        expr = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvfalse())) # (assert (= zf True))
        print getModel(expr)
        
        print {k: "0x%x, '%c'" % (v, v) for k, v in getModel(expr).items()}
    """

if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('main')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()
