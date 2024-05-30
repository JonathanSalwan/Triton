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
##  $ time ./solve.py
## [+] Loading 0x010034 - 0x010174
## [+] Loading 0x010174 - 0x010196
## [+] Loading 0x000000 - 0x000053
## [+] Loading 0x010000 - 0x010554
## [+] Loading 0x011ef8 - 0x012010
## [+] Loading 0x011f04 - 0x011ff4
## [+] Loading 0x010198 - 0x0101b8
## [+] Loading 0x01044c - 0x010490
## [+] Loading 0x000000 - 0x000000
## [+] Loading 0x011ef8 - 0x012000
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
## {0: "0x70, 'p'", 1: "0x62, 'b'", 4: "0x78, 'x'", 3: "0x78, 'x'", 2: "0x61, 'a'"}
## {0: "0x78, 'x'", 1: "0x62, 'b'", 4: "0x78, 'x'", 3: "0x70, 'p'", 2: "0x61, 'a'"}
## {0: "0x70, 'p'", 1: "0x6a, 'j'", 4: "0x68, 'h'", 3: "0x70, 'p'", 2: "0x61, 'a'"}
## {0: "0x70, 'p'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x74, 't'", 2: "0x61, 'a'"}
## {0: "0x78, 'x'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x6c, 'l'", 2: "0x61, 'a'"}
## {0: "0x78, 'x'", 1: "0x62, 'b'", 4: "0x68, 'h'", 3: "0x6c, 'l'", 2: "0x65, 'e'"}
## {0: "0x78, 'x'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x68, 'h'", 2: "0x65, 'e'"}
## {0: "0x62, 'b'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x62, 'b'", 2: "0x65, 'e'"}
## {0: "0x7a, 'z'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x6a, 'j'", 2: "0x65, 'e'"}
## {0: "0x78, 'x'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x6a, 'j'", 2: "0x67, 'g'"}
## {0: "0x70, 'p'", 1: "0x66, 'f'", 4: "0x68, 'h'", 3: "0x72, 'r'", 2: "0x67, 'g'"}
## {0: "0x70, 'p'", 1: "0x66, 'f'", 4: "0x6a, 'j'", 3: "0x72, 'r'", 2: "0x65, 'e'"}
## {0: "0x70, 'p'", 1: "0x62, 'b'", 4: "0x64, 'd'", 3: "0x72, 'r'", 2: "0x67, 'g'"}
## {0: "0x70, 'p'", 1: "0x62, 'b'", 4: "0x64, 'd'", 3: "0x70, 'p'", 2: "0x65, 'e'"}
## {0: "0x68, 'h'", 1: "0x66, 'f'", 4: "0x64, 'd'", 3: "0x64, 'd'", 2: "0x65, 'e'"}
## {0: "0x68, 'h'", 1: "0x6a, 'j'", 4: "0x64, 'd'", 3: "0x64, 'd'", 2: "0x61, 'a'"}
## {0: "0x68, 'h'", 1: "0x66, 'f'", 4: "0x61, 'a'", 3: "0x65, 'e'", 2: "0x61, 'a'"}
## {0: "0x68, 'h'", 1: "0x66, 'f'", 4: "0x61, 'a'", 3: "0x67, 'g'", 2: "0x63, 'c'"}
## {0: "0x68, 'h'", 1: "0x6a, 'j'", 4: "0x65, 'e'", 3: "0x67, 'g'", 2: "0x63, 'c'"}
## [+] Pick up the first serial: pbaxx
## [+] puts hooked
## fail
## [+] Instruction executed: 92
## [+] Emulation done.
## [+] Start a second emulation with the good serial to validate the chall
## [+] Starting emulation.
## [+] __libc_start_main hooked
## [+] argv[0] = b'./crackme_hash'
## [+] argv[1] = b'pbaxx'
## [+] puts hooked
## Win
## [+] Instruction executed: 93
## [+] Emulation done.
## ./solve.py  0,08s user 0,02s system 99% cpu 0,094 total


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
BASE_SERIAL_ADDR = 0x1200c
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
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.DWORD), addr)
        base += CPUSIZE.DWORD

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
            ctx.setConcreteRegisterValue(ctx.registers.x2, ctx.getConcreteRegisterValue(ctx.registers.x2)+CPUSIZE.DWORD)
    return

# Emulate the binary.
def emulate(ctx, pc):
    global SERIAL
    global VALID
    # Set serial string address loaded by:
    # 10404: 00c7a883                lw      a7,12(a5) # 1200c <serial>

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

        # 10358: 6541                    lui     a0,0x10
        # 1035a: 43850513                addi    a0,a0,1080 # 10438 <_IO_stdin_used+0x4>
        # 1035e: 37c9                    jal     10320 <puts@plt>
        #        ...
        # 10438: 006e6957                .4byte  0x6e6957 # "Win"


        if pc == 0x1035e:
            # We validated the crackme
            VALID = True

        # 10400: 67c9                    lui     a5,0x12
        # 10402: 652d                    lui     a0,0xb
        # 10404: 00c7a883                lw      a7,12(a5) # 1200c <serial>
        # 10408: bcd50513                addi    a0,a0,-1075 # abcd <__abi_tag-0x55cb>

        # 10344: 00f50a63                beq     a0,a5,10358 <main+0x28> # jump to Win puts if equal
        if pc == 0x10344 and SERIAL is None:
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
                     astCtxt.equal(a0.getAst(), astCtxt.bv(0xad6d, CPUSIZE.DWORD_BIT)) # collision: (assert (= a4 0xad6d)
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
            for _, v in list(sorted(models[1].items())):
                # NOTE only readable allowed
                SERIAL += "%c" % (v.getValue())

            print('[+] Pick up the first serial: %s' %(SERIAL))

        # Return from main
        if pc == 0x10364:
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
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.DWORD), crel[2])
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
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.DWORD), crel[2])
    except:
        pass
    return


def run(ctx, binary):
    # Concretize previous context
    ctx.concretizeAllMemory()
    ctx.concretizeAllRegister()

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
    ctx.setArchitecture(ARCH.RV32)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
    #ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

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
