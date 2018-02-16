#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from pintool import *
from triton  import ARCH


def mycb(inst):
    print inst
    return


if __name__ == '__main__':
    ctx = getTritonContext()
    ctx.enableSymbolicEngine(False)
    ctx.enableTaintEngine(False)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()
