#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2016-08-01
##
##  Description: Solution of the baby-re challenge from the Defcon Quals 2016.
##  In this solution, we fully emulate the CheckSolution() function and we solve
##  each branch to go through the good path. The emulation start from a memory
##  dump (baby-re.dump) which has been done via peda-gdb (see gdb-peda-fulldump.patch)
##  at the CheckSolution() prologue.
##
##  Output:
##
##   $ python ./solve.py
##   [...]
##   [+] Win
##   [+] Emulation done.
##   [+] Final solution:
##   [+] Symbolic variable 0 = 4d (M)
##   [+] Symbolic variable 1 = 61 (a)
##   [+] Symbolic variable 2 = 74 (t)
##   [+] Symbolic variable 3 = 68 (h)
##   [+] Symbolic variable 4 = 20 ( )
##   [+] Symbolic variable 5 = 69 (i)
##   [+] Symbolic variable 6 = 73 (s)
##   [+] Symbolic variable 7 = 20 ( )
##   [+] Symbolic variable 8 = 68 (h)
##   [+] Symbolic variable 9 = 61 (a)
##   [+] Symbolic variable 10 = 72 (r)
##   [+] Symbolic variable 11 = 64 (d)
##   [+] Symbolic variable 12 = 21 (!)
##

from __future__ import print_function
from triton     import *

import os
import sys

# Symbolic variables with random inputs at the first iteration.
variables = {
    0x00: 61,
    0x01: 61,
    0x02: 61,
    0x03: 61,
    0x04: 61,
    0x05: 61,
    0x06: 61,
    0x07: 61,
    0x08: 61,
    0x09: 61,
    0x0a: 61,
    0x0b: 61,
    0x0c: 61,
}

# Good values at specific points to take good branches.
goodBranches = {
    0x40168C: 0x01468753,
    0x4017D4: 0x00162F30,
    0x401920: 0xFFB2939C,
    0x401A6B: 0xFFAC90E3,
    0x401BB7: 0x0076D288,
    0x401D06: 0xFF78BF99,
    0x401E52: 0xFFF496E3,
    0x401FA0: 0xFF525E90,
    0x4020E8: 0xFFFD7704,
    0x402234: 0x00897CBB,
    0x402378: 0xFFC05F9F,
    0x402499: 0x003E4761,
    0x4025BA: 0x001B4945,
}

# Memory caching on the fly to speed up the dump loading.
memoryCache = list()



def load_dump(ctx, path):
    global memoryCache

    # Open the dump
    fd = open(path)
    data = eval(fd.read())
    fd.close()

    # Extract registers and memory
    regs = data[0]
    mems = data[1]

    # Load registers and memory into the libctx
    print('[+] Define registers')
    ctx.setConcreteRegisterValue(ctx.registers.rax,    regs['rax'])
    ctx.setConcreteRegisterValue(ctx.registers.rbx,    regs['rbx'])
    ctx.setConcreteRegisterValue(ctx.registers.rcx,    regs['rcx'])
    ctx.setConcreteRegisterValue(ctx.registers.rdx,    regs['rdx'])
    ctx.setConcreteRegisterValue(ctx.registers.rdi,    regs['rdi'])
    ctx.setConcreteRegisterValue(ctx.registers.rsi,    regs['rsi'])
    ctx.setConcreteRegisterValue(ctx.registers.rbp,    regs['rbp'])
    ctx.setConcreteRegisterValue(ctx.registers.rsp,    regs['rsp'])
    ctx.setConcreteRegisterValue(ctx.registers.rip,    regs['rip'])
    ctx.setConcreteRegisterValue(ctx.registers.r8,     regs['r8'])
    ctx.setConcreteRegisterValue(ctx.registers.r9,     regs['r9'])
    ctx.setConcreteRegisterValue(ctx.registers.r10,    regs['r10'])
    ctx.setConcreteRegisterValue(ctx.registers.r11,    regs['r11'])
    ctx.setConcreteRegisterValue(ctx.registers.r12,    regs['r12'])
    ctx.setConcreteRegisterValue(ctx.registers.r13,    regs['r13'])
    ctx.setConcreteRegisterValue(ctx.registers.r14,    regs['r14'])
    ctx.setConcreteRegisterValue(ctx.registers.eflags, regs['eflags'])

    print('[+] Define memory areas')
    for mem in mems:
        start = mem['start']
        end   = mem['end']
        print('[+] Memory caching %x-%x' %(start, end))
        if mem['memory']:
            memoryCache.append({
                'start':  start,
                'size':   end - start,
                'memory': mem['memory'],
            })

    return


def symbolizeInputs(ctx):
    global variables

    # First argument of the CheckSolution() function.
    user_input = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Inject concrete models into the memory
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+0,  CPUSIZE.DWORD), variables[0x00])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+4,  CPUSIZE.DWORD), variables[0x01])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+8,  CPUSIZE.DWORD), variables[0x02])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+12, CPUSIZE.DWORD), variables[0x03])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+16, CPUSIZE.DWORD), variables[0x04])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+20, CPUSIZE.DWORD), variables[0x05])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+24, CPUSIZE.DWORD), variables[0x06])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+28, CPUSIZE.DWORD), variables[0x07])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+32, CPUSIZE.DWORD), variables[0x08])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+36, CPUSIZE.DWORD), variables[0x09])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+40, CPUSIZE.DWORD), variables[0x0a])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+44, CPUSIZE.DWORD), variables[0x0b])
    ctx.setConcreteMemoryValue(MemoryAccess(user_input+48, CPUSIZE.DWORD), variables[0x0c])

    # Create symbolic variables.
    ctx.symbolizeMemory(MemoryAccess(user_input+0,  CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+4,  CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+8,  CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+12, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+16, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+20, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+24, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+28, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+32, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+36, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+40, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+44, CPUSIZE.DWORD))
    ctx.symbolizeMemory(MemoryAccess(user_input+48, CPUSIZE.DWORD))

    return


# Print the final solution.
def solution():
    global variables
    print('[+] Final solution:')
    for k, v in list(variables.items()):
        print('[+] Symbolic variable %d = %02x (%c)' %(k, v, chr(v)))
    return


# Emulate the CheckSolution() function.
def emulate(ctx, pc):
    global variables
    global goodBranches

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

        # End of the CheckSolution() function
        if pc == 0x4025E6:
            break

        if pc == 0x4025CC:
            print('[+] Win')
            break

        if pc in goodBranches:
            astCtxt = ctx.getAstContext()

            # Slice expressions
            rax   = ctx.getSymbolicRegister(ctx.registers.rax)
            eax   = astCtxt.extract(31, 0, rax.getAst())

            # Push a new constraint to the current path predicate
            ctx.pushPathConstraint(eax == goodBranches[pc])

            # Solve the path predicate
            cstr = ctx.getPathPredicate()

            print('[+] Asking for a model, please wait...')
            model = ctx.getModel(cstr)

            # Save new state
            for k, v in list(model.items()):
                print('[+]', v)
                variables[k] = v.getValue()

            # Go deeper
            del goodBranches[pc]

            # Restart emulation with a good input.
            ctx = initialize()

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    print('[+] Emulation done.')
    return


# Memory caching on the fly to speed up the dump loading.
def memoryCaching(ctx, mem):
    global memoryCache

    addr = mem.getAddress()
    size = mem.getSize()
    for index in range(size):
        if not ctx.isConcreteMemoryValueDefined(addr+index, 1):
            for r in memoryCache:
                if addr+index >= r['start'] and addr+index < r['start'] + r['size']:
                    i = ((addr + index) - r['start'])
                    value = ord(r['memory'][i : i+1])
                    ctx.setConcreteMemoryValue(addr+index, value)
                    return

    return


def initialize():
    ctx = TritonContext()

    # Define the target architecture
    ctx.setArchitecture(ARCH.X86_64)

    # Define symbolic optimizations
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    # Define internal callbacks.
    ctx.addCallback(memoryCaching,   CALLBACK.GET_CONCRETE_MEMORY_VALUE)

    # Load the meory dump
    load_dump(ctx, os.path.join(os.path.dirname(__file__), "baby-re.dump"))

    # Symbolize user inputs
    symbolizeInputs(ctx)

    return ctx


if __name__ == '__main__':
    # Initialize symbolic emulation
    ctx = initialize()

    # Emulate from the dump
    emulate(ctx, ctx.getConcreteRegisterValue(ctx.registers.rip))

    # Print the final solution
    solution()

    sys.exit(0)
