#! /usr/bin/env python3
## -*- coding: utf-8 -*-

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os


DEBUG  = False
# DEBUG  = True
TARGET = os.path.join(os.path.dirname(__file__), './bin/crypto_test-nothumb-Os.bin')
STOP_ADDR = None
MAX_INSTRS = 100000


# The debug function
def debug(s):
    if DEBUG: print(s)


def print_state(ctx):
    print('[+] r0   (r0): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r0)))
    print('[+] r1   (r1): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r1)))
    print('[+] r2   (r2): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r2)))
    print('[+] r3   (r3): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r3)))
    print('[+] r4   (r4): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r4)))
    print('[+] r5   (r5): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r5)))
    print('[+] r6   (r6): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r6)))
    print('[+] r6   (r6): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r6)))
    print('[+] r7   (r7): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r7)))
    print('[+] r8   (r8): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r8)))
    print('[+] r9   (r9): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r9)))
    print('[+] r10 (r10): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r10)))
    print('[+] r11  (fp): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r11)))
    print('[+] r12  (ip): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r12)))
    print('[+] r13  (sp): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.sp)))
    print('[+] r14  (lr): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r14)))
    print('[+] r15  (pc): {:08x}'.format(ctx.getConcreteRegisterValue(ctx.registers.pc)))


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


# Simulate the aeabi_memclr() function
def aeabi_memclrHandler(ctx):
    print('[+] __aeabi_memclr hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.r0)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.r1)

    print('\targ1: {:x}'.format(arg1))
    print('\targ2: {:x}'.format(arg2))

    for i in range(0, arg2):
        ctx.setConcreteMemoryValue(arg1 + i, 0)


# Simulate the __aeabi_memcpy() function
def aeabi_memcpyHandler(ctx):
    print('[+] __aeabi_memcpy hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.r0)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.r1)
    arg3 = ctx.getConcreteRegisterValue(ctx.registers.r2)

    print('\targ1: {:x}'.format(arg1))
    print('\targ2: {:x}'.format(arg2))
    print('\targ3: {:x}'.format(arg3))

    for i in range(0, arg3):
        b = ctx.getConcreteMemoryValue(arg2 + i)
        ctx.setConcreteMemoryValue(arg1 + i, b)


# Simulate the puts() function
def putsHandler(ctx):
    print('[+] puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.r0))

    print('\targ1: "{}" ({:08x})'.format(arg1, ctx.getConcreteRegisterValue(ctx.registers.r0)))

    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def libcInitHandler(ctx):
    global STOP_ADDR

    print('[+] __libc_init hooked')

    # Get return address of __libc_init
    STOP_ADDR = ctx.getConcreteRegisterValue(ctx.registers.r14)

    print('[+] Set stop address to: {:x}'.format(STOP_ADDR))

    # Get address of main function.
    main_addr = ctx.getConcreteRegisterValue(ctx.registers.r2)

    debug('[+] Address of main function: {:x}'.format(main_addr))

    # Setup argc / argv
    argvs = [
        bytes(TARGET.encode('utf-8')), # argv[0]
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, argv+b'\x00')
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
    debug('[+] Simulating call to main...')
    ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)-CPUSIZE.DWORD)
    push_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
    ctx.setConcreteMemoryValue(push_addr, main_addr)
    debug('    Pushing {:x} at {:x}'.format(main_addr, ctx.getConcreteRegisterValue(ctx.registers.sp)))

    return None


# Functions to emulate
customRelocation = [
    ('__libc_init',     libcInitHandler,     BASE_PLT + 0 * 8),
    ('puts',            putsHandler,         BASE_PLT + 1 * 8),
    ('__aeabi_memclr8', aeabi_memclrHandler, BASE_PLT + 2 * 8),
    ('__aeabi_memclr',  aeabi_memclrHandler, BASE_PLT + 3 * 8),
    ('__aeabi_memcpy',  aeabi_memcpyHandler, BASE_PLT + 4 * 8),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.pc)
    for rel in customRelocation:
        if rel[2] == pc:
            # Simulate push {lr}
            debug('[+] Simulating "push {lr}"')
            ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)-CPUSIZE.DWORD)
            push_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
            ctx.setConcreteMemoryValue(push_addr, ctx.getConcreteRegisterValue(ctx.registers.r14))
            debug('    lr : {:x}'.format(ctx.getConcreteRegisterValue(ctx.registers.r14)))

            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.r0, ret_value)

            # Simulate pop {lr}
            debug('[+] Simulating "pop {pc}"')
            pop_addr = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.sp), CPUSIZE.DWORD)
            pc = ctx.getConcreteMemoryValue(pop_addr)
            ctx.setConcreteRegisterValue(ctx.registers.sp, ctx.getConcreteRegisterValue(ctx.registers.sp)+CPUSIZE.DWORD)
            debug("    pc : {:x}".format(pc))

            # Update PC
            ctx.setConcreteRegisterValue(ctx.registers.pc, pc)
    return


# Emulate the binary.
def emulate(ctx, pc):
    ctx.setConcreteRegisterValue(ctx.registers.pc, pc)

    ret_value = None
    count = 0
    while pc and count < MAX_INSTRS:
        if STOP_ADDR and pc == STOP_ADDR:
            debug("[+] Emulation reached stop address...")
            break

        if count >= MAX_INSTRS:
            print("[-] Emulation exceeded max number of instructions!")
            break

        if pc == 0x880:
            r0 = ctx.getConcreteRegisterValue(ctx.registers.r0)
            debug("[+] Return value: {:#x}".format(r0))
            ret_value = r0

        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 4)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Process
        if ctx.processing(instruction):
            opcodes_str = " ".join(["{:02x}".format(b) for b in bytearray(instruction.getOpcode())])
            debug('[-] Instruction not supported: %s\t%s' %(opcodes_str, str(instruction)))
            break

        opcodes_str = " ".join(["{:02x}".format(b) for b in bytearray(instruction.getOpcode())])

        debug('{}\t{}'.format(opcodes_str, instruction))

        # print_state(ctx)

        # Inc the number of instructions executed
        count += 1

        # Simulate routines
        hookingHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.pc)

    debug('[+] Instruction executed: %d' %(count))

    if ret_value == None:
        raise Exception("Invalid return code.")

    return ret_value


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
    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.ARM32)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Run emulation
    return run(ctx, binary)


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
