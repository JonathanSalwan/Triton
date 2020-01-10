#! /usr/bin/env python
## -*- coding: utf-8 -*-

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os

DEBUG  = True
INPUT  = 'arm32'
SERIAL = None
TARGET = os.path.join(os.path.dirname(__file__), 'crackme_hash-thumb')
VALID  = False

FINISH = False
MAX_INSTRS = 10000

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


# Simulate the printf() function
def printfHandler(ctx):
    debug('[+] printf hooked')

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.r0))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.r1)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.r2)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.r3)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r4)
    arg6   = ctx.getConcreteRegisterValue(ctx.registers.r5)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg1.format(*args)

    sys.stdout.write(s + "\n")

    # Return value
    return len(s)


# Simulate the puts() function
def putsHandler(ctx):
    debug('[+] puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.r0))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def abortHandler(ctx):
    global FINISH

    debug('[+] abort hooked')
    # sys.exit(0)
    FINISH = True


def libcMainHandler(ctx):
    debug('[+] __libc_start_main hooked')

    # Get main function address.
    main_addr = ctx.getConcreteRegisterValue(ctx.registers.r0)

    # Setup argc / argv
    ctx.concretizeRegister(ctx.registers.r0)
    ctx.concretizeRegister(ctx.registers.r1)

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

    ctx.setConcreteRegisterValue(ctx.registers.r0, argc)
    ctx.setConcreteRegisterValue(ctx.registers.r1, argv)

    # Simulate call to main
    # debug('[+] Simulating call to main...')
    ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)-CPUSIZE.DWORD)
    push_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
    ctx.setConcreteMemoryValue(push_addr, main_addr)
    # debug('    Pushing {:x} at {:x}'.format(main_addr, ctx.getConcreteRegisterValue(ctx.registers.sp)))

    return None


# Functions to emulate
customRelocation = [
    ('printf',            printfHandler,   BASE_PLT + 0),
    ('puts',              putsHandler,     BASE_PLT + 1),
    ('__libc_start_main', libcMainHandler, BASE_PLT + 2),
    ('abort',             abortHandler,    BASE_PLT + 4),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.pc)
    for rel in customRelocation:
        if rel[2] == pc:
            # Simulate push {lr}
            # debug('[+] Simulating "push {lr}"')
            ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)-CPUSIZE.DWORD)
            push_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
            ctx.setConcreteMemoryValue(push_addr, ctx.getConcreteRegisterValue(ctx.registers.r14))
            # debug('    lr : {:x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r14)))

            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.r0, ret_value)

            # Simulate pop {lr}
            # debug('[+] Simulating "pop {pc}"')
            pop_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
            pc = ctx.getConcreteMemoryValue(pop_addr)
            ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)+CPUSIZE.DWORD)
            # debug("    pc : {:x}".format(pc))

            # Update PC
            ctx.setConcreteRegisterValue(ctx.registers.pc, pc)
    return


# Emulate the binary.
def emulate(ctx, pc):
    global SERIAL
    global VALID

    # TODO: Remove?
    ctx.setConcreteRegisterValue(ctx.registers.pc, pc)

    count = 0
    while pc and count < MAX_INSTRS and not FINISH:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 4)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Process
        if ctx.processing(instruction) == False:
            opcodes_str = " ".join(["{:02x}".format(ord(b)) for b in opcodes])
            debug('[-] Instruction not supported: %s\t%s' %(opcodes_str, str(instruction)))
            break

        # debug(instruction)

        # .text:000104BE                 LDR     R3, =unk_107BC
        # .text:000104C0                 MOVS    R0, R3          ; s
        # .text:000104C2                 BL      j_puts
        # .text:000104C6                 B       loc_104D0
        if pc == 0x104C2:
            # We validated the crackme
            VALID = True

        # .text:000104B8                 LDR     R2, =0xAD6D
        # .text:000104BA                 CMP     R3, R2
        # .text:000104BC                 BNE     loc_104C8
        if pc == 0x104BA and SERIAL is None:
            print('[+] Please wait, calculating hash collisions...')
            r3 = ctx.getSymbolicRegister(ctx.registers.r3)

            SymVar_0 = ctx.getSymbolicVariable('SymVar_0')
            SymVar_1 = ctx.getSymbolicVariable('SymVar_1')
            SymVar_2 = ctx.getSymbolicVariable('SymVar_2')
            SymVar_3 = ctx.getSymbolicVariable('SymVar_3')
            SymVar_4 = ctx.getSymbolicVariable('SymVar_4')

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
                     astCtxt.equal(r3.getAst(), astCtxt.bv(0xad6d, CPUSIZE.DWORD_BIT)) # collision: (assert (= r3 0xad6d)
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

        # Inc the number of instructions executed
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
                    debug('    {:x} : {:x}'.format(symbolRelo, crel[2]))
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
                    debug('    {:x} : {:x}'.format(symbolRelo, crel[2]))
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.DWORD), crel[2])
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
    global FINISH

    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.ARM32)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # First emulation
    run(ctx, binary)

    FINISH = False

    # Replace the input with the good serial to validate the chall
    INPUT = SERIAL

    # Second emulation
    print('[+] Start a second emualtion with the good serial to validate the chall')
    run(ctx, binary)

    return not VALID == True

    return 0


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
