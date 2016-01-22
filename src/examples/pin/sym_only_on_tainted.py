#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## $ ./triton ./src/examples/pin/sym_only_on_tainted.py ./src/samples/crackmes/crackme_xor a
##

import sys

from pintool import *
from triton  import *


def cb_ir(inst):
    if inst.getAddress() == 0x40058b:
        rax = getCurrentRegisterValue(REG.RAX)
        taintAddr(rax)
    return


def cb_before(inst):
    print inst
    for expr in inst.getSymbolicExpressions():
        print '\t', expr
    return


if __name__ == '__main__':
    # Set arch
    setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromSymbol('check')

    # Perform symbolic execution only on tainted instructions
    enableSymbolicOptimization(OPTIMIZATION.ONLY_ON_TAINTED)

    # Add callback
    addCallback(cb_ir, CALLBACK.BEFORE_SYMPROC)
    addCallback(cb_before, CALLBACK.BEFORE)

    # Run Program
    runProgram()

