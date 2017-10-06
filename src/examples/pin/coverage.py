#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##

import sys

from pintool import *
from triton import *



def mycb(inst):
    #print inst
    if inst.isBranch():
        tagDict = {'address': hex(inst.getAddress()), 'isTaken': inst.isConditionTaken()}
        tag = TaintTag(tagDict)
        print tag.getData()
    return


if __name__ == '__main__':
    # Set arch
    getTritonContext().setArchitecture(ARCH.X86_64)

    startAnalysisFromEntry()

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()

