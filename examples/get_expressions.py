
from triton import *

# $ ../../../pin -t ./triton.so -script ./examples/get_expressions.py -- ./samples/crackmes/crackme_xor elite
# Expression: (ite (= (bvsub ((_ extract 31 0) ((_ extract 31 0) (bvxor ((_ extract 31 0) (bvsub ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) SymVar_0))) (_ bv1 32))) (_ bv85 32)))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv49 8)))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
# Expression: (ite (= (bvsub ((_ extract 31 0) ((_ extract 31 0) (bvxor ((_ extract 31 0) (bvsub ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) SymVar_1))) (_ bv1 32))) (_ bv85 32)))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv62 8)))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
# Expression: (ite (= (bvsub ((_ extract 31 0) ((_ extract 31 0) (bvxor ((_ extract 31 0) (bvsub ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) SymVar_2))) (_ bv1 32))) (_ bv85 32)))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv61 8)))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
# Expression: (ite (= (bvsub ((_ extract 31 0) ((_ extract 31 0) (bvxor ((_ extract 31 0) (bvsub ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) SymVar_3))) (_ bv1 32))) (_ bv85 32)))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv38 8)))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
# Expression: (ite (= (bvsub ((_ extract 31 0) ((_ extract 31 0) (bvxor ((_ extract 31 0) (bvsub ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) SymVar_4))) (_ bv1 32))) (_ bv85 32)))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv49 8)))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
# Win
# $ 

# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed, 
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):

    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)


# 0x4005ae: cmp ecx, eax
def cafter(instruction):

    if instruction.address == 0x4005ae:
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        expr = getBacktrackedSymExpr(zfId)
        print "Expression: %s" %(expr)


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

