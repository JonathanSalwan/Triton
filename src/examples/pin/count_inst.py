#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from pintool import *
from triton  import *

count = 0

def mycb(inst):
    global count
    count += 1

def fini():
    print count

if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    startAnalysisFromEntry()
    insertCall(mycb, INSERT_POINT.BEFORE)
    insertCall(fini, INSERT_POINT.FINI)
    runProgram()

