#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## $ ./build/triton ./src/examples/pin/sym_only_on_tainted.py ./src/samples/crackmes/crackme_xor a
##

from pintool import *
from triton  import ARCH, MODE


def cb_ir(inst):
    if inst.getAddress() == 0x400574:
        rax = getCurrentRegisterValue(getTritonContext().registers.rax)
        getTritonContext().taintMemory(rax)
    return


def cb_before(inst):
    print inst
    for expr in inst.getSymbolicExpressions():
        print '\t', expr
    return


if __name__ == '__main__':
    # Set arch
    getTritonContext().setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromSymbol('check')

    # Perform symbolic execution only on tainted instructions
    getTritonContext().enableMode(MODE.ONLY_ON_TAINTED, True)

    # Add callback
    insertCall(cb_ir,       INSERT_POINT.BEFORE_SYMPROC)
    insertCall(cb_before,   INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

