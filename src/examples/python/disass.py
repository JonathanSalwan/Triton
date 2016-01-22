#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./disass.py
##  40000: imul sil
##          sil:8 bv[7..0]
##
##  40003: imul cx
##          cx:16 bv[15..0]
##
##  40006: imul rcx
##          rcx:64 bv[63..0]
##
##  40009: imul ecx, ecx, 1
##          ecx:32 bv[31..0]
##          ecx:32 bv[31..0]
##          0x1:32 bv[31..0]
##
##  4000c: imul ecx, edx
##          ecx:32 bv[31..0]
##          edx:32 bv[31..0]
##
##  4000f: imul rdx, rcx, 4
##          rdx:64 bv[63..0]
##          rcx:64 bv[63..0]
##          0x4:64 bv[63..0]
##

import  sys
from    triton import *


trace = [
    (0x40000, "\x40\xf6\xee"),      # imul   sil
    (0x40003, "\x66\xf7\xe9"),      # imul   cx
    (0x40006, "\x48\xf7\xe9"),      # imul   rcx
    (0x40009, "\x6b\xc9\x01"),      # imul   ecx,ecx,0x1
    (0x4000c, "\x0f\xaf\xca"),      # imul   ecx,edx
    (0x4000f, "\x48\x6b\xd1\x04"),  # imul   rdx,rcx,0x4
]



if __name__ == '__main__':

    #Set the arch
    setArchitecture(ARCH.X86_64)

    for (addr, opcodes) in trace:
        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(opcodes)

        # Setup Address
        inst.setAddress(addr)

        # Process everything
        processing(inst)

        # Display instruction
        print inst
        for op in inst.getOperands():
            print '\t', op
            if op.getType() == OPERAND.MEM:
                print '\t', op.getBaseReg()
                print '\t', op.getIndexReg()
                print '\t', op.getScale()
                print '\t', op.getDisplacement()

        print

    sys.exit(0)

