#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Triton tool to trace the R and W memory access.
##  Jonathan Salwan - 2015-04-30
##
## Description:
## ------------
##
## This tool is used to trace all memory access. With this tool, you know
## which instruction read and write in memory, where it read/write,
## the access' size and the value. May be useful to track quickly some
## specific data.
##
## Output:
## -------
##
## $ ./triton ./tools/memory_tracer.py ./samples/vulns/testSuite
## [...]
## [R:4] 0x0000004005fa: mov eax, dword ptr [rbp-0x8]      R:0x00007fff51aa7c08: 04 00 00 00 (0x4)
## [W:1] 0x000000400606: mov byte ptr [rax], 0x45          W:0x00007fff51aa7c08: 45 (0x45)
## [R:4] 0x000000400609: add dword ptr [rbp-0x8], 0x1      R:0x00007fff51aa7c08: 45 00 00 00 (0x45)
## [R:4] 0x00000040060d: mov eax, dword ptr [rbp-0x8]      R:0x00007fff51aa7c08: 46 00 00 00 (0x46)
## [R:8] 0x000000400615: pop rbp                           R:0x00007fff51aa7c10: 50 7c aa 51 ff 7f 00 00 (0x7fff51aa7c50)
## [R:8] 0x000000400616: ret                               R:0x00007fff51aa7c18: f8 06 40 00 00 00 00 00 (0x4006f8)
## [R:8] 0x0000004006f8: mov rax, qword ptr [rbp-0x8]      R:0x00007fff51aa7c48: 40 b0 73 01 00 00 00 00 (0x173b040)
## [W:8] 0x0000004006ff: call 0x400460                     W:0x00007fff51aa7c18: 04 07 40 00 00 00 00 00 (0x400704)
## [R:8] 0x000000400460: jmp qword ptr [rip+0x200bb2]      R:0x0000000000601018: 00 b1 0e dd 9b 7f 00 00 (0x7f9bdd0eb100)
## [R:8] 0x7f9bdd0eb100: mov rax, qword ptr [rip+0x315de1] R:0x00007f9bdd400ee8: e8 37 40 dd 9b 7f 00 00 (0x7f9bdd4037e8)
## [R:8] 0x7f9bdd0eb107: mov rax, qword ptr [rax]          R:0x00007f9bdd4037e8: 00 00 00 00 00 00 00 00 (0x0)
## [R:8] 0x7f9bdd0eb114: mov rax, qword ptr [rdi-0x8]      R:0x000000000173b038: 31 00 00 00 00 00 00 00 (0x31)
## [W:8] 0x7f9bdd0e7890: push r15                          W:0x00007fff51aa7c10: 00 00 00 00 00 00 00 00 (0x0)
## [W:8] 0x7f9bdd0e7892: push r14                          W:0x00007fff51aa7c08: 00 00 00 00 00 00 00 00 (0x0)
## [W:8] 0x7f9bdd0e7894: push r13                          W:0x00007fff51aa7c00: 30 7d aa 51 ff 7f 00 00 (0x7fff51aa7d30)
## [W:8] 0x7f9bdd0e7896: push r12                          W:0x00007fff51aa7bf8: a0 04 40 00 00 00 00 00 (0x4004a0)
## [W:8] 0x7f9bdd0e7898: push rbp                          W:0x00007fff51aa7bf0: 50 7c aa 51 ff 7f 00 00 (0x7fff51aa7c50)
## [W:8] 0x7f9bdd0e7899: push rbx                          W:0x00007fff51aa7be8: 00 00 00 00 00 00 00 00 (0x0)
## [R:8] 0x7f9bdd0e78a1: mov rax, qword ptr [rsi+0x8]      R:0x000000000173b038: 31 00 00 00 00 00 00 00 (0x31)
## [...]
##

from triton import *


def dump(opType, instruction, operand):

    opAccess         = 'R' if opType == IDREF.OPERAND.MEM_R else 'W'
    memoryAccess     = operand.getValue()
    memoryAccessSize = operand.getSize()

    a = str()
    d = '[%c:%d] 0x%016x: %s' %(opAccess, memoryAccessSize, instruction.getAddress(), instruction.getDisassembly())

    if checkReadAccess(memoryAccess):
        a = '%c:0x%016x:' %(opAccess, memoryAccess)
        for i in range(memoryAccessSize):
            a += ' %02x' %(getMemValue(memoryAccess+i, 1))

    print '%s%s%s (%#x)' %(d, ' '*(70-len(d)), a, getMemValue(memoryAccess, memoryAccessSize))
    return


def before(instruction):
    for operand in instruction.getOperands():
        if operand.getType() == IDREF.OPERAND.MEM_R:
            dump(IDREF.OPERAND.MEM_R, instruction, operand)
            return
    return


def after(instruction):
    for operand in instruction.getOperands():
        if operand.getType() == IDREF.OPERAND.MEM_W:
            dump(IDREF.OPERAND.MEM_W, instruction, operand)
            return
    return


if __name__ == '__main__':

    # Start the symbolic analysis from the entry point
    startAnalysisFromSymbol('main')

    # Add a callback.
    addCallback(before, IDREF.CALLBACK.BEFORE)
    addCallback(after,  IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()


