#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2022-05-27
##  Crackme from: https://crackmes.one/crackme/61a0f51433c5d413767c9bd6
##
##  Output:
##
##  $ time python ./solve.py
##  [+] Loading 0x400040 - 0x400350
##  [+] Loading 0x400350 - 0x40036c
##  [+] Loading 0x400000 - 0x4006d8
##  [+] Loading 0x401000 - 0x4015b5
##  [+] Loading 0x402000 - 0x402150
##  [+] Loading 0x403e00 - 0x404050
##  [+] Loading 0x408000 - 0x41013c
##  [+] Loading 0x403e20 - 0x403ff0
##  [+] Loading 0x400370 - 0x400390
##  [+] Loading 0x400390 - 0x4003d4
##  [+] Loading 0x400370 - 0x400390
##  [+] Loading 0x402050 - 0x402084
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x403e00 - 0x404000
##  Hooking puts
##  Hooking strlen
##  Hooking printf
##  Hooking fgets
##  Hooking mprotect
##  Hooking fwrite
##  Hooking __libc_start_main
##  [+] Starting emulation.
##  mprotect hooked
##  [+] Instruction executed: 565
##  [+] __libc_start_main hooked
##  [+] argv[0] = b'/home/jonathan/Works/Tools/Triton/src/examples/python/ctf-writeups/cm002/cm002'
##  puts hooked
##  Enter password:
##  fgets hooked
##  Injecting 12 symbolic variables at 0x9ffffee0
##  [+] strlen hooked
##  [+] strlen hooked
##  [+] Injecting SymVar_4:8 = 0x4d
##  [+] Injecting SymVar_9:8 = 0x20
##  [+] Injecting SymVar_5:8 = 0x22
##  printf hooked
##  You found the password: bytearray(b'AAAAM"AAA A\x00')
##  python solve.py  0.18s user 0.04s system 99% cpu 0.217 total
##

from __future__ import print_function
from triton     import *

import string
import sys
import lief
import os

TARGET = os.path.join(os.path.dirname(__file__), 'cm002')
DEBUG  = True

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_STACK = 0x9fffffff


def getMemoryString(ctx, addr):
    s = str()
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def strlenHandler(ctx):
    debug('[+] strlen hooked')
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    return len(arg1)


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

    return 0


def putsHandler(ctx):
    debug('puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def fgetsHandler(ctx):
    debug('fgets hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    debug(f'Injecting 12 symbolic variables at {arg1:#x}')
    ctx.setConcreteMemoryAreaValue(arg1, b'AAAAAAAAAAAA')
    for i in range(12):
        ctx.symbolizeMemory(MemoryAccess(arg1 + i, CPUSIZE.BYTE))

    # Return value
    return arg1


def fwriteHandler(ctx):
    debug('fwrite hooked')
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1)
    return len(arg1)


def mprotectHandler(ctx):
    debug('mprotect hooked')
    return 0


# Simulate the printf() function
def printfHandler(ctx):
    debug('printf hooked')

    password = bytearray(12)

    index = 0
    for _, var in sorted(ctx.getSymbolicVariables().items()):
        password[index] = ctx.getConcreteVariableValue(var)
        index += 1

    debug(f'You found the password: {password}')
    sys.exit(not (password == b'AAAAM"AAA A\x00'))


# Functions to emulate
customRelocation = [
    ['__libc_start_main', libcMainHandler, None],
    ['fgets',             fgetsHandler,    None],
    ['fwrite',            fwriteHandler,   None],
    ['mprotect',          mprotectHandler, None],
    ['printf',            printfHandler,   None],
    ['puts',              putsHandler,     None],
    ['strlen',            strlenHandler,   None],
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


def inject_model(ctx, crt):
    model, sat, _ = ctx.getModel(crt, status=True)

    if sat == SOLVER_STATE.UNSAT:
        debug('UNSAT')
        sys.exit(-1)

    for k, m in model.items():
        v = m.getVariable()
        ctx.setConcreteVariableValue(v, m.getValue())
        debug(f'[+] Injecting {m}')

    return


# Emulate the binary.
def emulate(ctx, pc):
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction(pc, opcodes)
        ctx.processing(instruction)

        if instruction.getAddress() == 0x410107:
            zf = ctx.getRegisterAst(ctx.registers.zf)
            inject_model(ctx, zf == 1)

        if instruction.getAddress() == 0x41010e:
            zf = ctx.getRegisterAst(ctx.registers.zf)
            inject_model(ctx, zf == 1)

        if instruction.getAddress() == 0x410115:
            zf = ctx.getRegisterAst(ctx.registers.zf)
            inject_model(ctx, zf == 1)

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
    # Setup plt
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    relocations = [x for x in binary.pltgot_relocations]
    relocations.extend([x for x in binary.dynamic_relocations])

    # Perform our own relocations
    for rel in relocations:
        symbolName = rel.symbol.name
        symbolRelo = rel.address
        for crel in customRelocation:
            if symbolName == crel[0]:
                debug('Hooking %s' %(symbolName))
                ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                break
    return


def run(ctx, binary):
    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, 0x4010F0) # decode routine
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def main():
    # Get a Triton context
    ctx = TritonContext(ARCH.X86_64)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.CONSTANT_FOLDING, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Init and emulate
    run(ctx, binary)
    return 0


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
