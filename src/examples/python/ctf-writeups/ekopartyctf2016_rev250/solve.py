#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2020-04-26
##
##  Output:
##
##  $ time python3 ./solve.py
##  [+] Loading 0x400040 - 0x400238
##  [+] Loading 0x400238 - 0x400254
##  [+] Loading 0x400000 - 0x405804
##  [+] Loading 0x605df0 - 0x6060a8
##  [+] Loading 0x605e08 - 0x605ff8
##  [+] Loading 0x400254 - 0x400298
##  [+] Loading 0x4056dc - 0x405710
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x605df0 - 0x606000
##  [+] Hooking setvbuf
##  [+] Hooking printf
##  [+] Hooking fflush
##  [+] Hooking read
##  [+] argv[0] = b'FUck_binary'
##  [+] Starting emulation.
##  [+] setvbuf hooked
##  [+] setvbuf hooked
##  [+] printf hooked
##  Hello, what's your team name? [+] fflush hooked
##  [+] read hooked
##  [+] symbolyzing stdin
##  Valid input is: ''@ (G @@ ^@v@  @/5vC\p D AC`P `  $  @#@   X  @@@P h@?@  WAU" A( Lq@ @p@ F$tH w60 * B k[Qn @@NCp@0I@@'
##  [+] Instruction executed: 2220
##  [+] Emulation done.
##  python3 solve.py  2.60s user 0.02s system 99% cpu 2.626 total
##
##  $ ./FUck_binary
##  Hello, what's your team name? '@ (G @@ ^@v@  @/5vC\p D AC`P `  $  @#@   X  @@@P h@?@  WAU" A( Lq@ @p@ F$tH w60 * B k[Qn @@NCp@0I@@
##  BOOM
##

from __future__ import print_function
from triton     import *

import string
import sys
import lief
import os
import time

TARGET = os.path.join(os.path.dirname(__file__), 'FUck_binary')
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


def getFormatString(ctx, addr):
    return getMemoryString(ctx, addr)                                               \
           .replace("%s", "{}").replace("%d", "{:d}").replace("%#02x", "{:#02x}")   \
           .replace("%#x", "{:#x}").replace("%x", "{:x}").replace("%02X", "{:02x}") \
           .replace("%c", "{:c}").replace("%02x", "{:02x}").replace("%ld", "{:d}")  \
           .replace("%*s", "").replace("%lX", "{:x}").replace("%08x", "{:08x}")     \
           .replace("%u", "{:d}").replace("%lu", "{:d}")                            \


def setvbufHandler(ctx):
    debug('[+] setvbuf hooked')
    return 0


def fflushHandler(ctx):
    debug('[+] fflush hooked')
    return 0


def printfHandler(ctx):
    debug('[+] printf hooked')

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg6   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg1.format(*args)

    if DEBUG:
        sys.stdout.write(s)

    return len(s)


# Simulate the read() function
def readHandler(ctx):
    debug('[+] read hooked')

    # Get arguments
    fd   = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    buff = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    size = 100

    debug('[+] symbolyzing stdin')
    for index in range(size):
        ast  = ctx.getAstContext()
        var  = ctx.symbolizeMemory(MemoryAccess(buff + index, CPUSIZE.BYTE))
        vast = ast.variable(var)
        ctx.pushPathConstraint(ast.land([vast >= ord(b' '), vast <= ord(b'~')]))

    return size


# Functions to emulate
customRelocation = [
    ('setvbuf',           setvbufHandler,  BASE_PLT + 1),
    ('fflush',            fflushHandler,   BASE_PLT + 2),
    ('printf',            printfHandler,   BASE_PLT + 3),
    ('read',              readHandler,     BASE_PLT + 4),
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


# Emulate the binary.
def emulate(ctx, pc):
    ret   = -1
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Just skip the __afl_maybe_log() function
        if instruction.getAddress() == 0x405228:
            ctx.processing(Instruction(b"\xc3")) # just return
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
            continue

        if ctx.processing(instruction) == EXCEPTION.FAULT_UD:
            break

        #if instruction.isSymbolized():
        #    print("\033[92m" + str(instruction) + "\033[0m")
        #else:
        #    print(instruction)

        if instruction.getAddress() == 0x4039E4:
            valid_input = bytearray(100)
            for k, var in sorted(ctx.getSymbolicVariables().items()):
                value = ctx.getConcreteVariableValue(var)
                valid_input[k] = value
            print('Valid input is: \'%s\'' %(valid_input.decode("utf-8")))
            ret = 0
            break

        if instruction.isBranch() and instruction.isSymbolized():
            ast = ctx.getAstContext()
            # 1) Save the last constraint
            # 2) Pop the last constraint from the current path predicate if it takes the bad branch
            # 3) Push a new constraint which invert the last one
            # 4) Reset rip to the correct branch
            last = ctx.getPathConstraints()[-1]
            if last.getTakenAddress() >= 0x403A7E:
                ctx.popPathConstraint()
                ctx.pushPathConstraint(ast.lnot(last.getTakenPredicate()))
                mod = ctx.getModel(ctx.getPathPredicate())
                for k, v in sorted(mod.items()):
                    ctx.setConcreteVariableValue(ctx.getSymbolicVariable(k), v.getValue())
                ctx.setConcreteRegisterValue(ctx.registers.rip, instruction.getNextAddress())

        if instruction.getType() == OPCODE.X86.HLT:
            ret = -1
            break

        # Simulate routines
        hookingHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

        count += 1

    debug('[+] Instruction executed: %d' %(count))
    return ret


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

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    ret = emulate(ctx, 0x400B68)
    debug('[+] Emulation done.')
    return ret


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
    return run(ctx, binary)


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
