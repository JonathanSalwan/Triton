#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys

from pintool import *
from triton  import *


def mycb(inst):
    print inst
    print
    return

def reg_hit(reg):
    print reg
    return

def mem_hit(addr, size):
    print hex(addr), size
    return

if __name__ == '__main__':
    # Set arch
    setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    addCallback(mem_hit, CALLBACK.MEMORY_LOAD)
    addCallback(reg_hit, CALLBACK.REGISTER_GET)

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

