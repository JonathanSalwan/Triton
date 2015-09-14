
from triton import *
import  smt2lib

#
# This example breaks a simple hash routine.
#
# Check the ./samples/crackmes/crackme_hash.c file. This file builds 
# a 'hash' and checks the checksum 0xad6d.
#
# The needed password is 'elite'. Example:
# $ ./samples/crackmes/crackme_hash elite
# Win
#
# This Triton code will try to break and find a hash collision.
#
# $ ./triton ./examples/crackme_hash_collision.py ./samples/crackmes/crackme_hash aaaaa
# [+] Please wait, computing in progress...
# {'SymVar_1': "0x72, 'r'", 'SymVar_0': "0x6c, 'l'", 'SymVar_3': "0x78, 'x'", 'SymVar_2': "0x64, 'd'", 'SymVar_4': "0x71, 'q'"}
# {'SymVar_1': "0x78, 'x'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x61, 'a'", 'SymVar_4': "0x6a, 'j'"}
# {'SymVar_1': "0x68, 'h'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x61, 'a'", 'SymVar_4': "0x7a, 'z'"}
# {'SymVar_1': "0x70, 'p'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x61, 'a'", 'SymVar_4': "0x62, 'b'"}
# {'SymVar_1': "0x72, 'r'", 'SymVar_0': "0x6f, 'o'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x62, 'b'"}
# {'SymVar_1': "0x7a, 'z'", 'SymVar_0': "0x6f, 'o'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x6a, 'j'"}
# {'SymVar_1': "0x7a, 'z'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x63, 'c'", 'SymVar_4': "0x6a, 'j'"}
# {'SymVar_1': "0x78, 'x'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x62, 'b'", 'SymVar_2': "0x63, 'c'", 'SymVar_4': "0x68, 'h'"}
# {'SymVar_1': "0x78, 'x'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x72, 'r'", 'SymVar_2': "0x63, 'c'", 'SymVar_4': "0x78, 'x'"}
# {'SymVar_1': "0x7a, 'z'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x70, 'p'", 'SymVar_2': "0x63, 'c'", 'SymVar_4': "0x78, 'x'"}
# {'SymVar_1': "0x7a, 'z'", 'SymVar_0': "0x6f, 'o'", 'SymVar_3': "0x70, 'p'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x78, 'x'"}
# {'SymVar_1': "0x70, 'p'", 'SymVar_0': "0x6b, 'k'", 'SymVar_3': "0x72, 'r'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x74, 't'"}
# {'SymVar_1': "0x72, 'r'", 'SymVar_0': "0x6f, 'o'", 'SymVar_3': "0x70, 'p'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x72, 'r'", 'SymVar_0': "0x6f, 'o'", 'SymVar_3': "0x72, 'r'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x72, 'r'"}
# {'SymVar_1': "0x72, 'r'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x73, 's'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x62, 'b'", 'SymVar_0': "0x6e, 'n'", 'SymVar_3': "0x63, 'c'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x6a, 'j'", 'SymVar_0': "0x66, 'f'", 'SymVar_3': "0x73, 's'", 'SymVar_2': "0x62, 'b'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x62, 'b'", 'SymVar_0': "0x62, 'b'", 'SymVar_3': "0x73, 's'", 'SymVar_2': "0x66, 'f'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x62, 'b'", 'SymVar_0': "0x62, 'b'", 'SymVar_3': "0x70, 'p'", 'SymVar_2': "0x67, 'g'", 'SymVar_4': "0x70, 'p'"}
# {'SymVar_1': "0x62, 'b'", 'SymVar_0': "0x62, 'b'", 'SymVar_3': "0x72, 'r'", 'SymVar_2': "0x67, 'g'", 'SymVar_4': "0x72, 'r'"}
# loose
#
# Triton found several collisions. Example with the first collision:
# $ ./samples/crackmes/crackme_hash lrdxq
# Win
# $
#


def cafter(instruction):

    # movzx esi,BYTE PTR [rax]
    # RAX points on the user password
    if instruction.getAddress() == 0x400572:
        convertRegToSymVar(IDREF.REG.RSI, 64)

    # mov eax,DWORD PTR [rbp-0x4]
    # RAX must be equal to 0xad6d to win
    if instruction.getAddress() == 0x4005c5:
        print '[+] Please wait, computing in progress...'
        raxId = getRegSymbolicID(IDREF.REG.RAX)
        raxExpr = getFullExpression(getSymExpr(raxId).getAst())

        # We want printable characters
        expr = smt2lib.compound([
                 smt2lib.smtAssert(smt2lib.bvugt(smt2lib.variable('SymVar_0'), smt2lib.bv(96,  64))),
                 smt2lib.smtAssert(smt2lib.bvult(smt2lib.variable('SymVar_0'), smt2lib.bv(123, 64))),
                 smt2lib.smtAssert(smt2lib.bvugt(smt2lib.variable('SymVar_1'), smt2lib.bv(96,  64))),
                 smt2lib.smtAssert(smt2lib.bvult(smt2lib.variable('SymVar_1'), smt2lib.bv(123, 64))),
                 smt2lib.smtAssert(smt2lib.bvugt(smt2lib.variable('SymVar_2'), smt2lib.bv(96,  64))),
                 smt2lib.smtAssert(smt2lib.bvult(smt2lib.variable('SymVar_2'), smt2lib.bv(123, 64))),
                 smt2lib.smtAssert(smt2lib.bvugt(smt2lib.variable('SymVar_3'), smt2lib.bv(96,  64))),
                 smt2lib.smtAssert(smt2lib.bvult(smt2lib.variable('SymVar_3'), smt2lib.bv(123, 64))),
                 smt2lib.smtAssert(smt2lib.bvugt(smt2lib.variable('SymVar_4'), smt2lib.bv(96,  64))),
                 smt2lib.smtAssert(smt2lib.bvult(smt2lib.variable('SymVar_4'), smt2lib.bv(123, 64))),
                 smt2lib.smtAssert(smt2lib.equal(raxExpr, smt2lib.bv(0xad6d, 64)))  # collision: (assert (= rax 0xad6d)
               ])

        # Get max 20 different models
        models = getModels(expr, 20)
        for model in models:
            print {k: "0x%x, '%c'" % (v, v) for k, v in model.items()}


if __name__ == '__main__':

    startAnalysisFromSymbol('check')
    addCallback(cafter, IDREF.CALLBACK.AFTER)
    runProgram()

