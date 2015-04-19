
from triton import *

# $ ../../../pin -t ./triton.so -script ./examples/get_model.py -- ./samples/crackmes/crackme_xor elite
# {'SymVar_0': 101}
# {'SymVar_1': 108}
# {'SymVar_2': 105}
# {'SymVar_3': 116}
# {'SymVar_4': 101}
# Win
# $

# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed, 
# we taint the memory that RAX holds.
def cbefore(instruction):

    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)


# 0x4005ae: cmp ecx, eax
def cafter(instruction):

    if instruction.address == 0x4005ae:
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        expr = getBacktrackedSymExpr(zfId)
        print getModel(expr)


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbefore, IDREF.CALLBACK.BEFORE)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

