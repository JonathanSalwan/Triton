#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2020-04-26
##
##
##  Output:
##
##  $ time python3 ./solve.py
##  [+] Loading 0x400040 - 0x400238
##  [+] Loading 0x400238 - 0x400254
##  [+] Loading 0x400000 - 0x401ecc
##  [+] Loading 0x602e10 - 0x6030b7
##  [+] Loading 0x602e28 - 0x602ff8
##  [+] Loading 0x400254 - 0x400298
##  [+] Loading 0x401b44 - 0x401bf0
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x602e10 - 0x603000
##  [+] Hooking strncpy
##  [+] Hooking strlen
##  [+] Hooking __libc_start_main
##  [+] Hooking rand
##  [+] Starting emulation.
##  [+] __libc_start_main hooked
##  [+] argv[0] = b'fairlight'
##  [+] argv[1] = b'aaaaaaaaaaaaaa'
##  [+] strlen hooked
##  [+] strncpy hooked
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 40089b
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 4009d7
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 400b14
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 400c51
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 400d8b
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 400ec5
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 401002
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 40113c
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 401279
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 4013b3
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 4014f0
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 401645
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 40179c
##  [+] rand hooked
##  [+] rand hooked
##  [+] Solve constraint at 4018f3
##  [+] OK - ACCESS GRANTED: CODE{b'4ngrman4gem3nt'}
##  python3 solve.py  21.63s user 0.03s system 99% cpu 21.690 total
##

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os

TARGET = os.path.join(os.path.dirname(__file__), 'fairlight')
DEBUG  = True

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_STACK = 0x9fffffff

# conditions where ZF must be equal to 1
conditions = [
    0x40089B, # solve check_0
    0x4009D7, # solve check_1
    0x400B14, # solve check_2
    0x400C51, # solve check_3
    0x400D8B, # solve check_4
    0x400EC5, # solve check_5
    0x401002, # solve check_6
    0x40113C, # solve check_7
    0x401279, # solve check_8
    0x4013B3, # solve check_9
    0x4014F0, # solve check_10
    0x401645, # solve check_11
    0x40179C, # solve check_12
    0x4018F3, # solve check_13
]


def getMemoryString(ctx, addr):
    s = str()
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def strncpyHandler(ctx):
    debug('[+] strncpy hooked')

    dst = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    src = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    cnt = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    for index in range(cnt):
        dmem  = MemoryAccess(dst + index, 1)
        smem  = MemoryAccess(src + index, 1)
        cell = ctx.getMemoryAst(smem)
        expr = ctx.newSymbolicExpression(cell, "strncpy byte")
        ctx.setConcreteMemoryValue(dmem, cell.evaluate())
        ctx.assignSymbolicExpressionToMemory(expr, dmem)

    return dst


def strlenHandler(ctx):
    debug('[+] strlen hooked')
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    return len(arg1)


def randHandler(ctx):
    debug('[+] rand hooked')
    return random.randrange(0xffffffff)


def libcMainHandler(ctx):
    debug('[+] __libc_start_main hooked')

    # Get arguments
    main = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Push the return value to jump into the main() function
    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD)
    ctx.setConcreteMemoryValue(ret2main, main)

    # Setup argc / argv
    ctx.concretizeRegister(ctx.registers.rdi)
    ctx.concretizeRegister(ctx.registers.rsi)

    argvs = [
        bytes(TARGET.encode('utf-8')),  # argv[0]
        bytes(b'a' * 14),               # argv[1]
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, argv+b'\x00')
        base += len(argv)+1
        debug('[+] argv[%d] = %s' %(index, argv))
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    ctx.setConcreteRegisterValue(ctx.registers.rdi, argc)
    ctx.setConcreteRegisterValue(ctx.registers.rsi, argv)

    # Symbolize argv[1]
    argv1 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi) + 8, CPUSIZE.QWORD))
    for index in range(len(argvs[1])):
        var = ctx.symbolizeMemory(MemoryAccess(argv1+index, CPUSIZE.BYTE))

    return 0


# Functions to emulate
customRelocation = [
    ('__libc_start_main', libcMainHandler, BASE_PLT + 0),
    ('rand',              randHandler,     BASE_PLT + 1),
    ('strlen',            strlenHandler,   BASE_PLT + 2),
    ('strncpy',           strncpyHandler,  BASE_PLT + 3),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)

            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)

            # Restore RSP (simulate the ret)
            ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
    return


def denied_access():
    debug('NOPE - ACCESS DENIED!')
    sys.exit(-1)


# Emulate the binary.
def emulate(ctx, pc):
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # In this challenge there are a lot of instructions which are not
        # supported by Triton, like:
        #
        #   .text:00000000004008D4 cvtsi2ss xmm0, eax
        #   .text:00000000004008D8 movss   xmm1, cs:dword_401B40
        #   .text:00000000004008E0 divss   xmm0, xmm1
        #   .text:00000000004008E4 movss   [rbp+var_4], xmm0
        #   .text:00000000004008E9 movss   xmm0, [rbp+var_4]
        #   .text:00000000004008EE mulss   xmm0, [rbp+var_8]
        #   .text:00000000004008F3 movss   [rbp+var_4], xmm0
        #   .text:00000000004008F8 movss   xmm0, [rbp+var_8]
        #   .text:00000000004008FD addss   xmm0, [rbp+var_4]
        #
        # Luckily, these instructions do not infer in constraints to solve the
        # challenge. So, in this case we just skip them :).
        if ctx.processing(instruction) == EXCEPTION.FAULT_UD:
            pc = instruction.getNextAddress()
            continue

        if instruction.getAddress() == 0x40074D:
            denied_access()

        if instruction.getAddress() == 0x401A55:
            code = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.edx))
            code = bytearray(14)
            for k, v in sorted(ctx.getSymbolicVariables().items()):
                code[k] = ctx.getConcreteVariableValue(v) & 0xff

            if code == b'4ngrman4gem3nt':
                debug('[+] OK - ACCESS GRANTED: CODE{%s}' %(bytes(code)))
                sys.exit(0)
            else:
                denied_access()

        if instruction.getAddress() in conditions:
            zf  = ctx.getSymbolicRegister(ctx.registers.zf).getAst()
            ast = ctx.getAstContext()
            ctx.pushPathConstraint(zf == 1)
            mod = ctx.getModel(ctx.getPathPredicate())
            for k,v in list(mod.items()):
                ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())
            debug('[+] Solve constraint at %x' %(instruction.getAddress()))

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

        count += 1


    debug('[+] Instruction executed: %d' %(count))
    return


def loadBinary(ctx, binary):
    # Map the binary into the memory
    phdrs = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        debug('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))
    return


def makeRelocation(ctx, binary):
    # Perform our own relocations
    try:
        for rel in binary.pltgot_relocations:
            symbolName = rel.symbol.name
            symbolRelo = rel.address
            for crel in customRelocation:
                if symbolName == crel[0]:
                    debug('[+] Hooking %s' %(symbolName))
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
    except:
        pass

    # Perform our own relocations
    try:
        for rel in binary.dynamic_relocations:
            symbolName = rel.symbol.name
            symbolRelo = rel.address
            for crel in customRelocation:
                if symbolName == crel[0]:
                    debug('[+] Hooking %s' %(symbolName))
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
    except:
        pass
    return


def run(ctx, binary):
    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def main():
    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.X86_64)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Init and emulate
    run(ctx, binary)
    return -1


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
