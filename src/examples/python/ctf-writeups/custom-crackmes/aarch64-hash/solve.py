#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2018-12-26
##
##  A custom crackme to test the AArch64 architecture. The goal is to find an
##  hash collision to take the 'Win' branch. Firs we run the binary with a random
##  seed, then we calculate the hash collision and run a second time the binary with
##  the good input to take the 'Win' branch.
##
##  Output:
##
##  $ time ./solve.py
##  [+] Loading 0x000040 - 0x000238
##  [+] Loading 0x000238 - 0x000253
##  [+] Loading 0x000000 - 0x000a3c
##  [+] Loading 0x010db8 - 0x011040
##  [+] Loading 0x010dc8 - 0x010fa8
##  [+] Loading 0x000254 - 0x000274
##  [+] Loading 0x000948 - 0x000984
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x010db8 - 0x011000
##  [+] Hooking __libc_start_main
##  [+] Hooking puts
##  [+] Starting emulation.
##  [+] __libc_start_main hooked
##  [+] argv[0] = ./crackme_hash
##  [+] argv[1] = arm64
##  [+] Please wait, calculating hash collisions...
##  [+] Found several hash collisions:
##  {0L: "0x6c, 'l'", 1L: "0x78, 'x'", 2L: "0x75, 'u'", 3L: "0x70, 'p'", 4L: "0x6e, 'n'"}
##  {0L: "0x63, 'c'", 1L: "0x78, 'x'", 2L: "0x62, 'b'", 3L: "0x70, 'p'", 4L: "0x62, 'b'"}
##  {0L: "0x73, 's'", 1L: "0x68, 'h'", 2L: "0x62, 'b'", 3L: "0x70, 'p'", 4L: "0x62, 'b'"}
##  {0L: "0x71, 'q'", 1L: "0x66, 'f'", 2L: "0x62, 'b'", 3L: "0x70, 'p'", 4L: "0x62, 'b'"}
##  {0L: "0x75, 'u'", 1L: "0x66, 'f'", 2L: "0x66, 'f'", 3L: "0x70, 'p'", 4L: "0x62, 'b'"}
##  {0L: "0x75, 'u'", 1L: "0x67, 'g'", 2L: "0x67, 'g'", 3L: "0x70, 'p'", 4L: "0x62, 'b'"}
##  {0L: "0x75, 'u'", 1L: "0x6f, 'o'", 2L: "0x67, 'g'", 3L: "0x78, 'x'", 4L: "0x62, 'b'"}
##  {0L: "0x75, 'u'", 1L: "0x6f, 'o'", 2L: "0x67, 'g'", 3L: "0x70, 'p'", 4L: "0x6a, 'j'"}
##  {0L: "0x75, 'u'", 1L: "0x6f, 'o'", 2L: "0x67, 'g'", 3L: "0x74, 't'", 4L: "0x6e, 'n'"}
##  {0L: "0x75, 'u'", 1L: "0x6f, 'o'", 2L: "0x67, 'g'", 3L: "0x75, 'u'", 4L: "0x6f, 'o'"}
##  {0L: "0x76, 'v'", 1L: "0x70, 'p'", 2L: "0x67, 'g'", 3L: "0x75, 'u'", 4L: "0x6f, 'o'"}
##  {0L: "0x77, 'w'", 1L: "0x70, 'p'", 2L: "0x66, 'f'", 3L: "0x75, 'u'", 4L: "0x6f, 'o'"}
##  {0L: "0x77, 'w'", 1L: "0x70, 'p'", 2L: "0x66, 'f'", 3L: "0x71, 'q'", 4L: "0x6b, 'k'"}
##  {0L: "0x76, 'v'", 1L: "0x70, 'p'", 2L: "0x67, 'g'", 3L: "0x71, 'q'", 4L: "0x6b, 'k'"}
##  {0L: "0x76, 'v'", 1L: "0x70, 'p'", 2L: "0x67, 'g'", 3L: "0x70, 'p'", 4L: "0x6a, 'j'"}
##  {0L: "0x77, 'w'", 1L: "0x70, 'p'", 2L: "0x66, 'f'", 3L: "0x70, 'p'", 4L: "0x6a, 'j'"}
##  {0L: "0x77, 'w'", 1L: "0x70, 'p'", 2L: "0x66, 'f'", 3L: "0x72, 'r'", 4L: "0x6c, 'l'"}
##  {0L: "0x77, 'w'", 1L: "0x6e, 'n'", 2L: "0x64, 'd'", 3L: "0x72, 'r'", 4L: "0x6c, 'l'"}
##  {0L: "0x75, 'u'", 1L: "0x6c, 'l'", 2L: "0x64, 'd'", 3L: "0x72, 'r'", 4L: "0x6c, 'l'"}
##  {0L: "0x75, 'u'", 1L: "0x6e, 'n'", 2L: "0x66, 'f'", 3L: "0x72, 'r'", 4L: "0x6c, 'l'"}
##  [+] Pick up the first serial: lxupn
##  [+] puts hooked
##  fail
##  [+] Instruction executed: 240
##  [+] Emulation done.
##  [+] Start a second emualtion with the good serial to validate the chall
##  [+] Starting emulation.
##  [+] __libc_start_main hooked
##  [+] argv[0] = ./crackme_hash
##  [+] argv[1] = lxupn
##  [+] puts hooked
##  Win
##  [+] Instruction executed: 240
##  [+] Emulation done.
##
##  ./solve.py  0.10s user 0.00s system 99% cpu 0.105 total
##

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os

DEBUG  = True
INPUT  = 'arm64'
SERIAL = None
TARGET = os.path.join(os.path.dirname(__file__), 'crackme_hash')
VALID  = False

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
        bytes(TARGET.encode('utf-8')), # argv[0]
        bytes(INPUT.encode('utf-8'))
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, argv+b'\x00')
        if index == 1:
            # Only symbolized argv[1]
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
    global SERIAL
    global VALID

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

        #print(instruction)

        # .text:0000000000000864 ADRP  X0, #aWin@PAGE ; "Win"
        # .text:0000000000000868 ADD   X0, X0, #aWin@PAGEOFF ; "Win"
        # .text:000000000000086C BL    .puts
        if pc == 0x868:
            # We validated the crackme
            VALID = True

        # .text:0000000000000858 MOV   W0, #0xAD6D
        # .text:000000000000085C CMP   W1, W0
        # .text:0000000000000860 B.NE  loc_874
        if pc == 0x85c and SERIAL is None:
            print('[+] Please wait, calculating hash collisions...')
            x1 = ctx.getSymbolicRegister(ctx.registers.x1)

            SymVar_0 = ctx.getSymbolicVariableFromName('SymVar_0')
            SymVar_1 = ctx.getSymbolicVariableFromName('SymVar_1')
            SymVar_2 = ctx.getSymbolicVariableFromName('SymVar_2')
            SymVar_3 = ctx.getSymbolicVariableFromName('SymVar_3')
            SymVar_4 = ctx.getSymbolicVariableFromName('SymVar_4')

            astCtxt = ctx.getAstContext()

            # We want printable characters
            expr = astCtxt.land([
                     astCtxt.bvugt(astCtxt.variable(SymVar_0), astCtxt.bv(96,  CPUSIZE.BYTE_BIT)),
                     astCtxt.bvult(astCtxt.variable(SymVar_0), astCtxt.bv(123, CPUSIZE.BYTE_BIT)),
                     astCtxt.bvugt(astCtxt.variable(SymVar_1), astCtxt.bv(96,  CPUSIZE.BYTE_BIT)),
                     astCtxt.bvult(astCtxt.variable(SymVar_1), astCtxt.bv(123, CPUSIZE.BYTE_BIT)),
                     astCtxt.bvugt(astCtxt.variable(SymVar_2), astCtxt.bv(96,  CPUSIZE.BYTE_BIT)),
                     astCtxt.bvult(astCtxt.variable(SymVar_2), astCtxt.bv(123, CPUSIZE.BYTE_BIT)),
                     astCtxt.bvugt(astCtxt.variable(SymVar_3), astCtxt.bv(96,  CPUSIZE.BYTE_BIT)),
                     astCtxt.bvult(astCtxt.variable(SymVar_3), astCtxt.bv(123, CPUSIZE.BYTE_BIT)),
                     astCtxt.bvugt(astCtxt.variable(SymVar_4), astCtxt.bv(96,  CPUSIZE.BYTE_BIT)),
                     astCtxt.bvult(astCtxt.variable(SymVar_4), astCtxt.bv(123, CPUSIZE.BYTE_BIT)),
                     astCtxt.equal(x1.getAst(), astCtxt.bv(0xad6d, CPUSIZE.QWORD_BIT)) # collision: (assert (= x1 0xad6d)
                   ])

            # Get max 20 different models
            models = ctx.getModels(expr, 20)
            print('[+] Found several hash collisions:')
            for model in models:
                print({k: "0x%x, '%c'" % (v.getValue(), v.getValue()) for k, v in list(model.items())})

            SERIAL = str()
            for _, v in list(models[0].items()):
                SERIAL += "%c" % (v.getValue())

            print('[+] Pick up the first serial: %s' %(SERIAL))

        # Inc the number of instructions exected
        count += 1

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
    global INPUT
    global SERIAL

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

    # First emulation
    run(ctx, binary)

    # Replace the input with the good serial to validate the chall
    INPUT = SERIAL

    # Second emulation
    print('[+] Start a second emualtion with the good serial to validate the chall')
    run(ctx, binary)

    return not VALID == True


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
