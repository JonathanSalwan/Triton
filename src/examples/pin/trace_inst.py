#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys

from pintool import *
from triton  import *


def mycb(inst):
    print inst
    return


if __name__ == '__main__':
    # Set arch
    setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

