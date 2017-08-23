#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from pintool import *
from triton  import ARCH


def mycb(inst):
    print inst
    return


if __name__ == '__main__':
    # Set arch
    getTritonContext().setArchitecture(ARCH.X86_64)
    getTritonContext().enableSymbolicEngine(False)
    getTritonContext().enableTaintEngine(False)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()
