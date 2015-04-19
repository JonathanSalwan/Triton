
from triton import *

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
def cbefore(instruction):

    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)


# 0x4005ae: cmp ecx, eax
def cafter(instruction):

    if instruction.address == 0x4005ae:
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        expr = getBacktrackedSymExpr(zfId)
        print {k: "0x%x, '%c'" % (v, v) for k, v in getModel(expr).items()}


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbefore, IDREF.CALLBACK.BEFORE)
    addCallback(cafter, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

