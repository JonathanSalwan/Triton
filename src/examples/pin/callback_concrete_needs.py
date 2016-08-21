#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys

from pintool import *
from triton  import *


def mycb(inst):
    print 'Processing instruction at', inst, '\n'
    return

def reg_hit(reg):
    print 'Need concrete register value:', reg
    return

def mem_hit(mem):
    print 'Need concrete memory value:', mem
    return

if __name__ == '__main__':
    # Set arch
    setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    addCallback(mem_hit, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
    addCallback(reg_hit, CALLBACK.GET_CONCRETE_REGISTER_VALUE)

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

