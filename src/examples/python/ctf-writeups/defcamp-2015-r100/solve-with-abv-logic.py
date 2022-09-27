#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Description: This file is the same than solve.py but it uses the memory
##               array logic. It's mainly used as unit test to verify the
##               ABV logic.
##

from __future__ import print_function
from triton     import ARCH, TritonContext, Instruction, MODE, MemoryAccess, CPUSIZE

import os
import sys


# Emulate the CheckSolution() function.
def emulate(ctx, pc):
    astCtxt = ctx.getAstContext()
    print('[+] Starting emulation.')
    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the ctx instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        ctx.processing(instruction)
        print(instruction)

        # 40078B: cmp eax, 1
        # eax must be equal to 1 at each round.
        if instruction.getAddress() == 0x40078B:
            # Slice expressions
            rax   = ctx.getSymbolicRegister(ctx.registers.rax)
            eax   = astCtxt.extract(31, 0, rax.getAst())

            # Define constraint
            cstr  = astCtxt.land([
                        ctx.getPathPredicate(),
                        astCtxt.equal(eax, astCtxt.bv(1, 32))
                    ])

            print('[+] Asking for a model, please wait...')
            model = ctx.getModel(cstr)
            for k, v in list(sorted(model.items())):
                value = v.getValue()
                ctx.setConcreteVariableValue(ctx.getSymbolicVariable(k), value)
                print('[+] Symbolic variable %02d = %02x (%c)' %(k, value, chr(value)))

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    print('[+] Emulation done.')
    return


# Load segments into triton.
def loadBinary(path):
    import lief
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        print('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))
    return


def solution(ctx):
    flag = bytearray(12)

    for k, v in sorted(ctx.getSymbolicVariables().items())[:len(flag)]:
        flag[k] = ctx.getConcreteVariableValue(v)

    if flag == b'Code_Talkers':
        print('[+] Flag found: %s' %flag)
        return 0

    return -1


if __name__ == '__main__':
    # Define the target architecture
    ctx = TritonContext(ARCH.X86_64)

    # Define symbolic optimizations
    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
    ctx.setMode(MODE.MEMORY_ARRAY, True)
    ctx.setMode(MODE.SYMBOLIZE_LOAD, True)
    ctx.setMode(MODE.SYMBOLIZE_STORE, True)

    # Load the binary
    loadBinary(os.path.join(os.path.dirname(__file__), 'r100.bin'))

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, 0x7fffffff)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, 0x6fffffff)

    # Define an user input
    ctx.setConcreteRegisterValue(ctx.registers.rdi, 0x10000000)

    # Symbolize user inputs (30 bytes)
    for index in range(30):
        ctx.symbolizeMemory(MemoryAccess(0x10000000+index, CPUSIZE.BYTE))

    # Emulate from the verification function
    emulate(ctx, 0x4006FD)

    sys.exit(solution(ctx))
