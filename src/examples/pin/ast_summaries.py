#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## $ ./triton ./src/examples/pin/ast_summaries.py ./src/samples/crackmes/crackme_xor a
##

import sys

from pintool import *
from triton  import *


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

    # Use AST Summaries
    enableSymbolicOptimization(OPTIMIZATION.AST_SUMMARIES)

    # Add callback
    addCallback(cb_before, CALLBACK.BEFORE)

    # Run Program
    runProgram()

