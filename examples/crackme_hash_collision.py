
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
# $ triton ./examples/crackme_hash_collision.py ./samples/crackmes/crackme_hash aaaaa
# [+] Please wait, computing in progress...
# {
#   'SymVar_0': "0x6c, 'l'", 
#   'SymVar_1': "0x72, 'r'", 
#   'SymVar_2': "0x64, 'd'", 
#   'SymVar_3': "0x78, 'x'", 
#   'SymVar_4': "0x71, 'q'"
# }
# loose
#
# Triton found the collision : lrdxq
#
# $ ./samples/crackmes/crackme_hash lrdxq
# Win
# $
#


def cafter(instruction):
    
    # movzx esi,BYTE PTR [rax]
    # RAX points on the user password
    if instruction.address == 0x400572:
        rsiId = getRegSymbolicID(IDREF.REG.RSI)
        convertExprToSymVar(rsiId, 8)

    # mov eax,DWORD PTR [rbp-0x4]
    # RAX must be equal to 0xad6d to win
    if instruction.address == 0x4005c5:
        print '[+] Please wait, computing in progress...'
        raxId = getRegSymbolicID(IDREF.REG.RAX)
        raxExpr = getBacktrackedSymExpr(raxId)
        expr = str()

        # We want printable characters
        # (assert (bvsgt SymVar_0 96)
        # (assert (bvslt SymVar_0 123)
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_0', smt2lib.bv(96, 64)))
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_0', smt2lib.bv(123, 64)))

        # (assert (bvsgt SymVar_1 96)
        # (assert (bvslt SymVar_1 123)
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_1', smt2lib.bv(96, 64)))
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_1', smt2lib.bv(123, 64)))

        # (assert (bvsgt SymVar_2 96)
        # (assert (bvslt SymVar_2 123)
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_2', smt2lib.bv(96, 64)))
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_2', smt2lib.bv(123, 64)))

        # (assert (bvsgt SymVar_3 96)
        # (assert (bvslt SymVar_3 123)
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_3', smt2lib.bv(96, 64)))
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_3', smt2lib.bv(123, 64)))

        # (assert (bvsgt SymVar_4 96)
        # (assert (bvslt SymVar_4 123)
        expr += smt2lib.smtAssert(smt2lib.bvugt('SymVar_4', smt2lib.bv(96, 64)))
        expr += smt2lib.smtAssert(smt2lib.bvult('SymVar_4', smt2lib.bv(123, 64)))

        # We want the collision
        # (assert (= rax 0xad6d)
        expr += smt2lib.smtAssert(smt2lib.equal(raxExpr, smt2lib.bv(0xad6d, 64)))
        print {k: "0x%x, '%c'" % (v, v) for k, v in getModel(expr).items()}


if __name__ == '__main__':

    startAnalysisFromSymbol('check')
    addCallback(cafter, IDREF.CALLBACK.AFTER)
    runProgram()

