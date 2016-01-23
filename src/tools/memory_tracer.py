#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Triton tool to trace memory access.
##  Jonathan Salwan - 2015-04-30
##
## Description:
## ------------
##
## This tool is used to trace all memory access. With this tool, you know
## which instruction read or write in memory, where it reads/writes,
## the access' size and the value. May be useful to track quickly some
## specific data.
##
## Output:
## -------
##
## $ ./triton ./src/tools/memory_tracer.py ./src/samples/crackmes/crackme_xor A
## [...]
## [08] 0x00007f27d55157f0: mov rbx, qword ptr [r13]             0x00007ffe99e386b8: 98 89 72 d5 27 7f 00 00 (0x7f27d5728998)
## [01] 0x00007f27d55157f4: movzx eax, byte ptr [rbx + 0x314]    0x00007f27d5728cac: 1d (0x1d)
## [01] 0x00007f27d5515802: mov byte ptr [rbx + 0x314], al       0x00007f27d5728cac: 1d (0x1d)
## [08] 0x00007f27d5515808: mov rax, qword ptr [rbx + 0x110]     0x00007f27d5728aa8: 00 00 00 00 00 00 00 00 (0x0)
## [08] 0x00007f27d5515890: mov rdx, qword ptr [rbx + 0xa8]      0x00007f27d5728a40: 00 00 00 00 00 00 00 00 (0x0)
## [04] 0x00007f27d5515865: mov esi, dword ptr [rbp - 0x34]      0x00007ffe99e386fc: 00 00 00 00 (0x0)
## [04] 0x00007f27d551586c: mov ecx, dword ptr [rip + 0x21252e]  0x00007f27d5727da0: 00 00 00 00 (0x0)
## [04] 0x00007f27d551587a: sub dword ptr [rbx + 0x310], 1       0x00007f27d5728ca8: 01 00 00 00 (0x1)
## [...]
##

from triton import *
from pintool import *


def dump(instruction, operand):
    memoryAccess     = operand.getAddress()
    memoryAccessSize = operand.getSize()

    a = str()
    d = '[%02d] 0x%016x: %s' %(memoryAccessSize, instruction.getAddress(), instruction.getDisassembly())

    if checkReadAccess(memoryAccess) and checkReadAccess(memoryAccess+memoryAccessSize):
        a = '0x%016x:' %(memoryAccess)
        for i in range(memoryAccessSize):
            a += ' %02x' %(getCurrentMemoryValue(memoryAccess+i))
        print '%s%s%s (%#x)' %(d, ' '*(70-len(d)), a, getCurrentMemoryValue(memoryAccess, memoryAccessSize))

    return


def before(instruction):
    for operand in instruction.getOperands():
        if operand.getType() == OPERAND.MEM:
            dump(instruction, operand)
            return
    return


if __name__ == '__main__':
    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the entry point
    startAnalysisFromEntry()

    # Add a callback.
    addCallback(before, CALLBACK.BEFORE)

    # Run the instrumentation - Never returns
    runProgram()


