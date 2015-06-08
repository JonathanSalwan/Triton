
import smt2lib
from triton import *

# $ triton ./examples/crackme_xor_obfu.py ./samples/crackmes/crackme_xor_obfu A

def cafter(instruction):

    print '%#x: %s' %(instruction.address, instruction.assembly)

    # [R:1]  0x400798: movsx eax, byte ptr [rcx+rax*1]  R:0x7fffb63d610a: 41 (0x41)
    # [W:8]  0x40079c: mov qword ptr [rbp-0x50], rax    W:0x7fffb63d52b0: 41 00 00 00 00 00 00 00 (0x41)
    # [R:8]  0x400891: mov rax, qword ptr [rbp-0x50]    R:0x7fffb63d52b0: 41 00 00 00 00 00 00 00 (0x41)
    if instruction.address == 0x400891:
        raxId = getRegSymbolicID(IDREF.REG.RAX)
        convertExprToSymVar(raxId, 8)

    if instruction.address == 0x400b69:
        zfId = getRegSymbolicID(IDREF.FLAG.ZF)
        zfExpr = getBacktrackedSymExpr(zfId)
        expr = str()
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_0', smt2lib.bv(96, 64)))    # printable char
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_0', smt2lib.bv(123, 64)))   # printable char
        expr += smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvtrue()))          # (assert (= zf true)
        print getModel(expr)

    return


if __name__ == '__main__':
    startAnalysisFromAddr(0x0000000000400891)
    stopAnalysisFromAddr(0x0000000000400b76)
    addCallback(cafter, IDREF.CALLBACK.AFTER)
    runProgram()

