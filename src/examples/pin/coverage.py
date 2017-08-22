#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##

import sys

from pintool import *
from triton  import *



def mycb(inst):
    #print inst
    if inst.isBranch():
        tag = CovTag(inst.getAddress(), inst.isConditionTaken())
        import IPython
        IPython.embed()
        sys.exit()
        print tag
    return


if __name__ == '__main__':
    # Set arch
    getTritonContext().setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    #startAnalysisFromSymbol('check')
    startAnalysisFromEntry()

    # Perform symbolic execution only on tainted instructions
    #enableMode(MODE.ONLY_ON_TAINTED, True)

    # Add callback
    #insertCall(cb_ir,       INSERT_POINT.BEFORE_SYMPROC)

    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

