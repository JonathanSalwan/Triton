#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./triton ./src/examples/pin/runtime_register_modification.py ./src/samples/crackmes/crackme_xor a
##  4005f9: mov dword ptr [rbp - 4], eax
##          #180 = ((_ extract 31 24) (_ bv0 32)) ; byte reference - MOV operation
##          #181 = ((_ extract 23 16) (_ bv0 32)) ; byte reference - MOV operation
##          #182 = ((_ extract 15 8) (_ bv0 32)) ; byte reference - MOV operation
##          #183 = ((_ extract 7 0) (_ bv0 32)) ; byte reference - MOV operation
##          #184 = (concat ((_ extract 31 24) (_ bv0 32)) ((_ extract 23 16) (_ bv0 32)) ((_ extract 15 8) (_ bv0 32)) ((_ extract 7 0) (_ bv0 32))) ; concat reference - MOV operation
##          #185 = (_ bv4195836 64) ; Program Counter
##  Win
##

import sys
from   pintool import *
from   triton  import *


def cb1(inst):
    if inst.getAddress() == 0x4005f9:
        setCurrentRegisterValue(REG.RAX, 0)

def cb2(inst):
    if inst.getAddress() == 0x4005f9:
        print inst
        for expr in inst.getSymbolicExpressions():
            print '\t', expr


if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    setupImageWhitelist(['crackme'])
    startAnalysisFromSymbol('main')
    addCallback(cb1, CALLBACK.BEFORE_SYMPROC)
    addCallback(cb2, CALLBACK.BEFORE)
    runProgram()

