#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2016-08-02
##
##  Description: Solution of the r100 challenge from the Defcamp 2015 CTF.
##  In this solution, we fully emulate the CheckSolution() function and we
##  solve each branch to go through the good path.
##
##  Output:
##
##  $ python ./solve.py
##  [...]
##  400784: movsx eax, al
##  400787: sub edx, eax
##  400789: mov eax, edx
##  40078b: cmp eax, 1
##  [+] Asking for a model, please wait...
##  [+] Symbolic variable 00 = 43 (C)
##  [+] Symbolic variable 01 = 6f (o)
##  [+] Symbolic variable 02 = 64 (d)
##  [+] Symbolic variable 03 = 65 (e)
##  [+] Symbolic variable 04 = 5f (_)
##  [+] Symbolic variable 05 = 54 (T)
##  [+] Symbolic variable 06 = 61 (a)
##  [+] Symbolic variable 07 = 6c (l)
##  [+] Symbolic variable 08 = 6b (k)
##  [+] Symbolic variable 09 = 65 (e)
##  [+] Symbolic variable 10 = 72 (r)
##  [+] Symbolic variable 11 = 73 (s)
##  40078e: je 0x400797
##  400797: add dword ptr [rbp - 0x24], 1
##  40079b: cmp dword ptr [rbp - 0x24], 0xb
##  40079f: jle 0x40072d
##  4007a1: mov eax, 0
##  4007a6: pop rbp
##  4007a7: ret
##  [+] Emulation done.
##

from triton import ARCH, TritonContext, Instruction, MODE, MemoryAccess, CPUSIZE

import os
import sys

Triton = TritonContext()


# Emulate the CheckSolution() function.
def emulate(pc):
    astCtxt = Triton.getAstContext()
    print '[+] Starting emulation.'
    while pc:
        # Fetch opcode
        opcode = Triton.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        Triton.processing(instruction)
        print instruction

        # 40078B: cmp eax, 1
        # eax must be equal to 1 at each round.
        if instruction.getAddress() == 0x40078B:
            # Slice expressions
            rax   = Triton.getSymbolicExpressionFromId(Triton.getSymbolicRegisterId(Triton.registers.rax))
            eax   = astCtxt.extract(31, 0, rax.getAst())

            # Define constraint
            cstr  = astCtxt.land([
                        Triton.getPathConstraintsAst(),
                        astCtxt.equal(eax, astCtxt.bv(1, 32))
                    ])

            print '[+] Asking for a model, please wait...'
            model = Triton.getModel(cstr)
            for k, v in model.items():
                value = v.getValue()
                Triton.setConcreteSymbolicVariableValue(Triton.getSymbolicVariableFromId(k), value)
                print '[+] Symbolic variable %02d = %02x (%c)' %(k, value, chr(value))

        # Next
        pc = Triton.getConcreteRegisterValue(Triton.registers.rip)

    print '[+] Emulation done.'
    return


# Load segments into triton.
def loadBinary(path):
    import lief
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        print '[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size)
        Triton.setConcreteMemoryAreaValue(vaddr, phdr.content)
    return


if __name__ == '__main__':
    # Define the target architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Define symbolic optimizations
    Triton.enableMode(MODE.ALIGNED_MEMORY, True)
    Triton.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Load the binary
    loadBinary(os.path.join(os.path.dirname(__file__), 'r100.bin'))

    # Define a fake stack
    Triton.setConcreteRegisterValue(Triton.registers.rbp, 0x7fffffff)
    Triton.setConcreteRegisterValue(Triton.registers.rsp, 0x6fffffff)

    # Define an user input
    Triton.setConcreteRegisterValue(Triton.registers.rdi, 0x10000000)

    # Symbolize user inputs (30 bytes)
    for index in range(30):
        Triton.convertMemoryToSymbolicVariable(MemoryAccess(0x10000000+index, CPUSIZE.BYTE))

    # Emulate from the verification function
    emulate(0x4006FD)

    sys.exit(0)

