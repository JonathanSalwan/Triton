
from triton import *


# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed, 
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):

    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)

# $ ../../../pin -t ./triton.so -script ./examples/get_expressions.py -- ./samples/crackmes/crackme_xor a
# [...]
# 0x400588: add rax, rdx
#          ->  #15 = (bvadd #14 ((_ extract 63 0) #13))
#          ->  #16 = (assert (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #15 (bvxor #14 ((_ extract 63 0) #13))))))
#          ->  #17 = (assert (bvult #15 #14))
#          ->  #18 = (assert (= ((_ extract 63 63) (bvand (bvxor #14 (bvnot ((_ extract 63 0) #13))) (bvxor #14 #15))) (_ bv1 1)))
#          ->  #19 = (assert (= (parity_flag ((_ extract 7 0) #15)) (_ bv0 1)))
#          ->  #20 = (assert (= ((_ extract 63 63) #15) (_ bv1 1)))
#          ->  #21 = (assert (= #15 (_ bv0 64)))
#
#
# 0x40058b: movzx eax, byte ptr [rax]
#          ->  #22 = SymVar_0           <------ So, RAX is now a symbolic variable.
#
#
# 0x40058e: movsx eax, al
#          ->  #23 = ((_ sign_extend 24) ((_ extract 7 0) #22))
# 0x400591: sub eax, 0x1
#          ->  #24 = (bvsub #23 (_ bv1 32))
#          ->  #25 = (assert (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #24 (bvxor #23 (_ bv1 32))))))
#          ->  #26 = (assert (bvult #24 #23))
#          ->  #27 = (assert (= ((_ extract 31 31) (bvand (bvxor #23 (bvnot (_ bv1 32))) (bvxor #23 #24))) (_ bv1 1)))
#          ->  #28 = (assert (= (parity_flag ((_ extract 7 0) #24)) (_ bv0 1)))
#          ->  #29 = (assert (= ((_ extract 31 31) #24) (_ bv1 1)))
#          ->  #30 = (assert (= #24 (_ bv0 32)))
# [...]
def cafter(instruction):

    print '%#x: %s' %(instruction.address, instruction.assembly)

    for se in instruction.symbolicElements:
        print '\t -> ', se.expression

    print



if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

