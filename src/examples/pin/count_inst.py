#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from pintool import *
from triton  import ARCH

count = 0

def mycb(inst):
    global count
    count += 1

def fini():
    print "Instruction count : ", count

if __name__ == '__main__':
    getTritonContext().setArchitecture(ARCH.X86_64)
    getTritonContext().enableSymbolicEngine(False)
    getTritonContext().enableTaintEngine(False)
    startAnalysisFromEntry()
    insertCall(mycb, INSERT_POINT.BEFORE)
    insertCall(fini, INSERT_POINT.FINI)
    runProgram()
