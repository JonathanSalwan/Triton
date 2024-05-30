#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  May 2024. Based on Jonathan Salwan - 2018-12-26
##
##  A custom crackme to test the RISCV64 architecture. The goal is to find a hash
##  collision to take the 'Win' branch. First we run the binary with a random
##  seed, then we calculate the hash collision and run a second time the binary with
##  the good input to take the 'Win' branch.
##
##  Output:
##
##  $ time ./solve-with-abv-logic.py
## [+] Loading 0x000040 - 0x000270
## [+] Loading 0x000270 - 0x000291
## [+] Loading 0x000000 - 0x00003c
## [+] Loading 0x000000 - 0x0007b4
## [+] Loading 0x001df8 - 0x002058
## [+] Loading 0x001e10 - 0x002000
## [+] Loading 0x000294 - 0x0002d8
## [+] Loading 0x000770 - 0x000784
## [+] Loading 0x000000 - 0x000000
## [+] Loading 0x001df8 - 0x002000
## [+] Hooking __libc_start_main
## [+] Hooking puts
## [+] Hooking __libc_start_main
## [+] Hooking puts
## [+] Starting emulation.
## [+] __libc_start_main hooked
## [+] argv[0] = b'./crackme_hash'
## [+] argv[1] = b'riscv'
## [+] Please wait, calculating hash collisions...
## [+] Found several hash collisions:
## {0: "0x69, 'i'", 4: "0x65, 'e'", 3: "0x62, 'b'", 1: "0x61, 'a'", 2: "0x6c, 'l'"}
## {0: "0x61, 'a'", 4: "0x6a, 'j'", 1: "0x62, 'b'", 3: "0x6a, 'j'", 2: "0x70, 'p'"}
## {0: "0x71, 'q'", 4: "0x6e, 'n'", 1: "0x62, 'b'", 3: "0x6a, 'j'", 2: "0x64, 'd'"}
## {0: "0x71, 'q'", 4: "0x6e, 'n'", 1: "0x63, 'c'", 3: "0x6c, 'l'", 2: "0x67, 'g'"}
## {0: "0x75, 'u'", 4: "0x6a, 'j'", 1: "0x63, 'c'", 3: "0x6c, 'l'", 2: "0x67, 'g'"}
## {0: "0x75, 'u'", 4: "0x6e, 'n'", 1: "0x67, 'g'", 3: "0x6c, 'l'", 2: "0x67, 'g'"}
## {0: "0x75, 'u'", 4: "0x6e, 'n'", 1: "0x6f, 'o'", 3: "0x74, 't'", 2: "0x67, 'g'"}
## {0: "0x65, 'e'", 4: "0x6e, 'n'", 1: "0x6f, 'o'", 3: "0x64, 'd'", 2: "0x67, 'g'"}
## {0: "0x6d, 'm'", 4: "0x6e, 'n'", 1: "0x6f, 'o'", 3: "0x64, 'd'", 2: "0x6f, 'o'"}
## {0: "0x6d, 'm'", 4: "0x68, 'h'", 1: "0x6f, 'o'", 3: "0x64, 'd'", 2: "0x65, 'e'"}
## {0: "0x6d, 'm'", 4: "0x69, 'i'", 1: "0x6f, 'o'", 3: "0x64, 'd'", 2: "0x64, 'd'"}
## {0: "0x6d, 'm'", 4: "0x69, 'i'", 1: "0x6c, 'l'", 3: "0x64, 'd'", 2: "0x65, 'e'"}
## {0: "0x6d, 'm'", 4: "0x69, 'i'", 1: "0x6e, 'n'", 3: "0x64, 'd'", 2: "0x67, 'g'"}
## {0: "0x65, 'e'", 4: "0x6d, 'm'", 1: "0x6a, 'j'", 3: "0x64, 'd'", 2: "0x67, 'g'"}
## {0: "0x65, 'e'", 4: "0x69, 'i'", 1: "0x6e, 'n'", 3: "0x6c, 'l'", 2: "0x67, 'g'"}
## {0: "0x6d, 'm'", 4: "0x69, 'i'", 1: "0x6e, 'n'", 3: "0x6c, 'l'", 2: "0x6f, 'o'"}
## {0: "0x65, 'e'", 4: "0x6d, 'm'", 1: "0x6e, 'n'", 3: "0x6c, 'l'", 2: "0x6b, 'k'"}
## {0: "0x65, 'e'", 4: "0x69, 'i'", 1: "0x6a, 'j'", 3: "0x6c, 'l'", 2: "0x6b, 'k'"}
## {0: "0x6d, 'm'", 4: "0x6d, 'm'", 1: "0x6a, 'j'", 3: "0x64, 'd'", 2: "0x6f, 'o'"}
## {0: "0x6d, 'm'", 4: "0x6d, 'm'", 1: "0x6b, 'k'", 3: "0x64, 'd'", 2: "0x6c, 'l'"}
## [+] Pick up the first serial: qcgln
## [+] puts hooked
## fail
## [+] Instruction executed: 93
## [+] Emulation done.
## [+] Start a second emulation with the good serial to validate the chall
## [+] Loading 0x000040 - 0x000270
## [+] Loading 0x000270 - 0x000291
## [+] Loading 0x000000 - 0x00003c
## [+] Loading 0x000000 - 0x0007b4
## [+] Loading 0x001df8 - 0x002058
## [+] Loading 0x001e10 - 0x002000
## [+] Loading 0x000294 - 0x0002d8
## [+] Loading 0x000770 - 0x000784
## [+] Loading 0x000000 - 0x000000
## [+] Loading 0x001df8 - 0x002000
## [+] Hooking __libc_start_main
## [+] Hooking puts
## [+] Hooking __libc_start_main
## [+] Hooking puts
## [+] Starting emulation.
## [+] __libc_start_main hooked
## [+] argv[0] = b'./crackme_hash'
## [+] argv[1] = b'qcgln'
## [+] puts hooked
## Win
## [+] Instruction executed: 94
## [+] Emulation done.
## ./solve-with-abv-logic.py  0,91s user 0,22s system 98% cpu 1,137 total

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os


DEBUG  = True
MY_INPUT = 'riscv'
SERIAL = None
TARGET = os.path.join(os.path.dirname(__file__), 'crackme_hash')
VALID  = False

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT    = 0x10000000
BASE_ARGV   = 0x20000000
BASE_SERIAL = 0x30000000
BASE_SERIAL_ADDR = 0x2008
BASE_STACK  = 0x9fffffff


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
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.x10))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def exitHandler(ctx):
    debug('[+] exit hooked')
    sys.exit(0)


def libcMainHandler(ctx):
    global MY_INPUT
    debug('[+] __libc_start_main hooked')

    # Setup argc / argv
    ctx.concretizeRegister(ctx.registers.x10)
    ctx.concretizeRegister(ctx.registers.x11)

    argvs = [
        bytes(TARGET.encode('utf-8')), # argv[0]
        bytes(MY_INPUT.encode('utf-8'))
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, argv+b'\x00\x00\x00')
        if index == 1:
            # Only symbolized argv[1]
            for indexCell in range(len(argv)):
                var = ctx.symbolizeMemory(MemoryAccess(base+indexCell, CPUSIZE.BYTE))
                var.setComment('argv[%d][%d]' %(index, indexCell))
        debug('[+] argv[%d] = %s' %(index, argv))
        base += len(argv)+1
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    ctx.setConcreteRegisterValue(ctx.registers.x10, argc)
    ctx.setConcreteRegisterValue(ctx.registers.x11, argv)

    return None


# Functions to emulate
customRelocation = [
    ('__libc_start_main', libcMainHandler, BASE_PLT + 0),
    ('exit',              exitHandler,     BASE_PLT + 1 << 2),
    ('puts',              putsHandler,     BASE_PLT + 2 << 2),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.pc)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            x10 = ctx.getConcreteRegisterValue(ctx.registers.x10)
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.x10, ret_value)

            # Get the return address
            ret_addr = ctx.getConcreteRegisterValue(ctx.registers.x1)
            # Set ret_addr to main() address when __libc_start_main is hooked
            if pc == BASE_PLT:
                ret_addr = x10

            # Hijack RIP to skip the call
            ctx.setConcreteRegisterValue(ctx.registers.pc, ret_addr)

            # Restore RSP (simulate the ret)
            ctx.setConcreteRegisterValue(ctx.registers.x2, ctx.getConcreteRegisterValue(ctx.registers.x2)+CPUSIZE.QWORD)
    return

# Emulate the binary.
def emulate(ctx, pc):
    global SERIAL
    global VALID
    # Set serial string address loaded by:
    # 6c8:   94483803                ld      a6,-1724(a6) # 2008 <serial>
    ctx.setConcreteMemoryAreaValue(BASE_SERIAL_ADDR, b"\x00\x00\x00\x30\x00\x00\x00\x00")
    # Set serial string content
    ctx.setConcreteMemoryAreaValue(BASE_SERIAL, '1>=&1'.encode('utf-8')+b'\x00\x00\x00')

    ctx.setConcreteRegisterValue(ctx.registers.pc, pc)
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 4)

        # Create the Triton instruction

        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Process
        if ctx.processing(instruction) == EXCEPTION.FAULT_UD:
            debug('[-] Instruction not supported: %s' %(str(instruction)))
            break
        #else:
        #    debug('[~] Instruction processing: %s' %(str(instruction)))

        # Load main() address
        #  5fe:   a4653503                ld      a0,-1466(a0) # 2040 <_GLOBAL_OFFSET_TABLE_+0x10>
        if pc == 0x5fe:
            ctx.setConcreteRegisterValue(ctx.registers.x10, 0x5b0)

        # 5de:   00000517                auipc   a0,0x0
        # 5e2:   17a50513                addi    a0,a0,378 # 758 <_IO_stdin_used+0x8>
        # 5e6:   fbbff0ef                jal     ra,5a0 <puts@plt>
        #        ...
        # 758:   006e6957                .4byte  0x6e6957 # "Win"

        if pc == 0x5e6:
            # We validated the crackme
            VALID = True

        # 6c2:   652d                    lui     a0,0xb
        # 6c4:   00002817                auipc   a6,0x2
        # 6c8:   94483803                ld      a6,-1724(a6) # 2008 <serial>
        # 6cc:   bcd50513                addi    a0,a0,-1075 # abcd <__global_pointer$+0x83cd>

        # 5c6:   00f50c63                beq     a0,a5,5de <main+0x2e>  # jump to Win puts if equal
        if pc == 0x5c6 and SERIAL is None:
            print('[+] Please wait, calculating hash collisions...')

            SymVar_0 = ctx.getSymbolicVariable('SymVar_0')
            SymVar_1 = ctx.getSymbolicVariable('SymVar_1')
            SymVar_2 = ctx.getSymbolicVariable('SymVar_2')
            SymVar_3 = ctx.getSymbolicVariable('SymVar_3')
            SymVar_4 = ctx.getSymbolicVariable('SymVar_4')

            astCtxt = ctx.getAstContext()

            # We want printable characters
            a0 = ctx.getSymbolicRegister(ctx.registers.x10)
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
                     astCtxt.equal(a0.getAst(), astCtxt.bv(0xad6d, CPUSIZE.QWORD_BIT)) # collision: (assert (= a4 0xad6d)
                   ])

            # Get max 20 different models
            models = ctx.getModels(expr, 20)
            if len(models) == 0:
                print('OOOPS! No models')
                return
            print('[+] Found several hash collisions:')
            for model in models:
                print({k: "0x%x, '%c'" % (v.getValue(), v.getValue()) for k, v in list(model.items())})

            SERIAL = str()
            for _, v in list(sorted(models[3].items())):
                # NOTE only readable allowed
                SERIAL += "%c" % (v.getValue())

            print('[+] Pick up the first serial: %s' %(SERIAL))

        # Return from main
        if pc == 0x5f0:
            break

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
    # Concretize previous context
    ctx.concretizeAllMemory()
    ctx.concretizeAllRegister()

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.x2, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def main():
    global MY_INPUT
    global SERIAL
    SERIAL = None

    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.RV64)

    # Set optimization
    ctx.setMode(MODE.MEMORY_ARRAY, True)
    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # First emulation
    run(ctx, binary)

    # Replace the input with the good serial to validate the chall
    MY_INPUT = SERIAL

    # Second emulation
    print('[+] Start a second emulation with the good serial to validate the chall')
    run(ctx, binary)

    return not VALID == True


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
