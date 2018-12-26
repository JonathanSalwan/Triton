#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2018-12-26
##
##  A custom crackme to test the AArch64 architecture.
##
##  Output:
##
##

import random
import string
import sys
import lief
import os

from triton import *

TARGET = os.path.join(os.path.dirname(__file__), 'crackme_hash')
DEBUG  = True

# The debug function
def debug(s):
    if DEBUG: print s

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


# Simulate the puts() function
def putsHandler(ctx):
    debug('[+] puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.x0))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def exitHandler(ctx):
    debug('[+] exit hooked')
    sys.exit(0)


def libcMainHandler(ctx):
    debug('[+] __libc_start_main hooked')

    # Get arguments
    main = ctx.getConcreteRegisterValue(ctx.registers.x0)

    # Push the return value to jump into the main() function
    ctx.concretizeRegister(ctx.registers.sp)
    ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.pc)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.QWORD)
    ctx.concretizeMemory(ret2main)
    ctx.setConcreteMemoryValue(ret2main, main)

    # Setup argc / argv
    ctx.concretizeRegister(ctx.registers.x0)
    ctx.concretizeRegister(ctx.registers.x1)

    argvs = [
        TARGET, # argv[0]
        "love aarch64"
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, argv+'\x00')
        for indexCell in range(len(argv)):
            var = ctx.convertMemoryToSymbolicVariable(MemoryAccess(base+indexCell, CPUSIZE.BYTE))
            var.setComment('argv[%d][%d]' %(index, indexCell))
        debug('[+] argv[%d] = %s' %(index, argv))
        base += len(argv)+1
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    ctx.setConcreteRegisterValue(ctx.registers.x0, argc)
    ctx.setConcreteRegisterValue(ctx.registers.x1, argv)

    return None


# Functions to emulate
customRelocation = [
    ('__libc_start_main', libcMainHandler, BASE_PLT + 0),
    ('exit',              exitHandler,     BASE_PLT + 1),
    ('puts',              putsHandler,     BASE_PLT + 2),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.pc)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.concretizeRegister(ctx.registers.x0)
                ctx.setConcreteRegisterValue(ctx.registers.x0, ret_value)

            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            ctx.concretizeRegister(ctx.registers.pc)
            ctx.setConcreteRegisterValue(ctx.registers.pc, ret_addr)

            # Restore RSP (simulate the ret)
            ctx.concretizeRegister(ctx.registers.sp)
            ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)+CPUSIZE.QWORD)
    return


# Emulate the binary.
def emulate(ctx, pc):
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 4)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Process
        if ctx.processing(instruction) == False:
            debug('[-] Instruction not supported: %s' %(str(instruction)))
            break

        count += 1

        print instruction
        #for x in instruction.getSymbolicExpressions():
        #    print x

        if instruction.getType() == OPCODE.AARCH64.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.pc)

    debug('[+] Instruction executed: %d' %(count))
    return


def loadBinary(ctx, binary):
    # Map the binary into the memory
    phdrs = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        debug('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)
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
    # Concretize previous context
    ctx.concretizeAllMemory()
    ctx.concretizeAllRegister()

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.sp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def main():
    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.AARCH64)

    # Set optimization
    ctx.enableMode(MODE.ALIGNED_MEMORY, True)
    ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

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
