#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ python src/examples/python/disass.py
##  40000: imul sil
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: sil:8 bv[7..0]
##      ---------------
##  40003: imul cx
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: cx:16 bv[15..0]
##      ---------------
##  40006: imul rcx
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: rcx:64 bv[63..0]
##      ---------------
##  40009: imul ecx, ecx, 1
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: ecx:32 bv[31..0]
##      ---------------
##      Operand: ecx:32 bv[31..0]
##      ---------------
##      Operand: 0x1:32 bv[31..0]
##      ---------------
##  4000c: imul ecx, edx
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: ecx:32 bv[31..0]
##      ---------------
##      Operand: edx:32 bv[31..0]
##      ---------------
##  4000f: imul rdx, rcx, 4
##      ---------------
##      Is memory read : False
##      Is memory write: False
##      ---------------
##      Operand: rdx:64 bv[63..0]
##      ---------------
##      Operand: rcx:64 bv[63..0]
##      ---------------
##      Operand: 0x4:64 bv[63..0]
##      ---------------
##
##  40013: mov byte ptr [rax], 1
##      ---------------
##      Is memory read : False
##      Is memory write: True
##      ---------------
##      Operand: [@0x0]:8 bv[7..0]
##      - base : rax:64 bv[63..0]
##      - index: unknown:1 bv[0..0]
##      - scale: 0x1:8 bv[7..0]
##      - disp : 0x0:8 bv[7..0]
##      ---------------
##      Operand: 0x1:8 bv[7..0]
##      ---------------
##
##  40016: mov rdx, qword ptr [rax]
##      ---------------
##      Is memory read : True
##      Is memory write: False
##      ---------------
##      Operand: rdx:64 bv[63..0]
##      ---------------
##      Operand: [@0x0]:64 bv[63..0]
##      - base : rax:64 bv[63..0]
##      - index: unknown:1 bv[0..0]
##      - scale: 0x1:64 bv[63..0]
##      - disp : 0x0:64 bv[63..0]
##      ---------------
##
##  40019: call rax
##      ---------------
##      Is memory read : False
##      Is memory write: True
##      ---------------
##      Operand: rax:64 bv[63..0]
##      ---------------
##
##  4001b: ret
##      ---------------
##      Is memory read : True
##      Is memory write: False
##      ---------------
##
##  4001c: add byte ptr [rax], 1
##      ---------------
##      Is memory read : True
##      Is memory write: True
##      ---------------
##      Operand: [@0x0]:8 bv[7..0]
##      - base : rax:64 bv[63..0]
##      - index: unknown:1 bv[0..0]
##      - scale: 0x1:8 bv[7..0]
##      - disp : 0x0:8 bv[7..0]
##      ---------------
##      Operand: 0x1:8 bv[7..0]
##      ---------------

import  sys
from    triton import *


code = [
    (0x40000, "\x40\xf6\xee"),      # imul   sil
    (0x40003, "\x66\xf7\xe9"),      # imul   cx
    (0x40006, "\x48\xf7\xe9"),      # imul   rcx
    (0x40009, "\x6b\xc9\x01"),      # imul   ecx,ecx,0x1
    (0x4000c, "\x0f\xaf\xca"),      # imul   ecx,edx
    (0x4000f, "\x48\x6b\xd1\x04"),  # imul   rdx,rcx,0x4
    (0x40013, "\xC6\x00\x01"),      # mov    BYTE PTR [rax],0x1
    (0x40016, "\x48\x8B\x10"),      # mov    rdx,QWORD PTR [rax]
    (0x40019, "\xFF\xD0"),          # call   rax
    (0x4001b, "\xc3"),              # ret
    (0x4001c, "\x80\x00\x01"),      # add    BYTE PTR [rax],0x1
    (0x4001f, "\x64\x48\x8B\x03"),  # mov    rax,QWORD PTR fs:[rbx]
]



if __name__ == '__main__':

    #Set the arch
    setArchitecture(ARCH.X86_64)

    for (addr, opcodes) in code:
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
        print '    ---------------'
        print '    Is memory read :', inst.isMemoryRead()
        print '    Is memory write:', inst.isMemoryWrite()
        print '    ---------------'
        for op in inst.getOperands():
            print '    Operand:', op
            if op.getType() == OPERAND.MEM:
                print '    - segment :', op.getSegmentRegister()
                print '    - base    :', op.getBaseRegister()
                print '    - index   :', op.getIndexRegister()
                print '    - scale   :', op.getScale()
                print '    - disp    :', op.getDisplacement()
            print '    ---------------'

        print

    sys.exit(0)

