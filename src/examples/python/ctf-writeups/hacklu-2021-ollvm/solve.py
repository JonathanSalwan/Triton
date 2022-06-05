#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
## Jonathan Salwan - 2022-06-05
##
## Solution for the Hack.lu 2021, OLLVM challenge.
##
## Output:
##
##  $ time python solve.py
##  [+] Loading 0x400040 - 0x400238
##  [+] Loading 0x400238 - 0x400254
##  [+] Loading 0x400000 - 0x4799b0
##  [+] Loading 0x679de0 - 0x67b274
##  [+] Loading 0x679df0 - 0x679ff0
##  [+] Loading 0x400254 - 0x400274
##  [+] Loading 0x470184 - 0x4711d0
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x679de0 - 0x67a000
##  [+] Init PLT for: __errno_location
##  [+] Init PLT for: printf
##  [+] Init PLT for: strtoul
##  [+] Init PLT for: memset
##  [+] Init PLT for: __libc_start_main
##  [+] Execution 0, getting hash: 0x6d6972726f725f6d
##  [+] Execution 1, getting hash: 0x6972726f725f6f6e
##  [+] Execution 2, getting hash: 0x5f7468655f77616c
##  [+] Execution 3, getting hash: 0x6c5f77686f735f74
##  [+] Execution 4, getting hash: 0x68655f75676c6965
##  [+] Execution 5, getting hash: 0x73745f68616e646c
##  [+] Execution 6, getting hash: 0x65725f6f665f7468
##  [+] Execution 7, getting hash: 0x656d5f616c6c3f21
##  [+] Flag: b'mirror_mirror_on_the_wall_whos_the_ugliest_handler_of_them_all?!'
##  python solve.py  7.46s user 0.08s system 99% cpu 7.562 total
##

from __future__ import print_function
from triton     import *

import codecs
import string
import sys
import lief
import os

TARGET = os.path.join(os.path.dirname(__file__), 'ollvm')
DEBUG  = False

# The debug function
def debug(s):
    if DEBUG: print(s)

# Global settings
SYMBOLIC = True
CONCRETE = not SYMBOLIC

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_STACK = 0x9ffffff0
ERRNO      = 0xa0000000


def getMemoryString(ctx, addr):
    s = str()
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def getStringPosition(text):
    formatters = ['%s','%d','%#02x', '%#x', '%02x', '%x', '%*s',    \
                  '%02X', '%lX', '%ld', '%08x', '%lu', '%u', '%c']

    text = text.replace("%s", " %s ").replace("%d", " %d ").replace("%#02x", " %#02x ")   \
           .replace("%#x", " %#x ").replace("%x", " %x ").replace("%02X", " %02X ")       \
           .replace("%c", " %c ").replace("%02x", " %02x ").replace("%ld", " %ld ")       \
           .replace("%*s", " %*s ").replace("%lX", " %lX").replace("%08x", " %08x ")      \
           .replace("%u", " %u ").replace("%lu", " %lu ")                                 \


    matches = [y for x in text.split() for y in formatters if y in x]
    indexes = [index for index, value in enumerate(matches) if value == '%s']
    return indexes


def getFormatString(ctx, addr):
    return getMemoryString(ctx, addr)                                               \
           .replace("%s", "{}").replace("%d", "{:d}").replace("%#02x", "{:#02x}")   \
           .replace("%#x", "{:#x}").replace("%x", "{:x}").replace("%02X", "{:02x}") \
           .replace("%c", "{:c}").replace("%02x", "{:02x}").replace("%ld", "{:d}")  \
           .replace("%*s", "").replace("%lX", "{:x}").replace("%08x", "{:08x}")     \
           .replace("%u", "{:d}").replace("%lu", "{:d}").replace("%lx", "{:x}")     \


def libc_start_main(ctx):
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
        b'dead'
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

    return (CONCRETE, 0)


def printf(ctx):
    debug('[+] printf hooked')

    string_pos = getStringPosition(getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi)))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg6   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    rsp    = ctx.getConcreteRegisterValue(ctx.registers.rsp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(rsp + CPUSIZE.QWORD * (i + 1), CPUSIZE.QWORD)))

    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = arg1.format(*args)
    sys.stdout.write(s)

    # Return value
    return (CONCRETE, len(s))


def memset(ctx):
    debug('[+] memset hooked')

    #Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3 = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    for index in range(arg3):
        ctx.setConcreteMemoryValue(MemoryAccess(arg1 + index, CPUSIZE.BYTE), arg2)

    return (CONCRETE, arg1)


def errno_location(ctx):
    debug('[+] __errno_location hooked')
    return (CONCRETE, ERRNO)


def strtoul(ctx):
    debug('[+] strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    endptr = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    base   = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    # Return value
    return (SYMBOLIC, int(nptr, base))


# Functions to emulate
customRelocation = [
    ['__errno_location',  errno_location,   None],
    ['__libc_start_main', libc_start_main,  None],
    ['memset',            memset,           None],
    ['printf',            printf,           None],
    ['strtoul',           strtoul,          None],
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            state, ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)
                if state is SYMBOLIC:
                    debug(f'[+] Symbolizing the return value')
                    ctx.symbolizeRegister(ctx.registers.rax)
            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))
            # Hijack RIP to skip the call
            ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)
            # Restore RSP (simulate the ret)
            ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
    return


# Emulate the binary.
def emulate(ctx, pc, h):
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the instruction
        instruction = Instruction(pc, opcodes)
        ret = ctx.processing(instruction)
        #print(instruction)

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # End point hash output
        if pc == 0x4008E1:
            rsi_s = ctx.getRegisterAst(ctx.registers.rsi)
            m = ctx.getModel(rsi_s == h)
            for k, v in m.items():
                return v.getValue()

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
        print('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
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
                print('[+] Init PLT for: %s' %(symbolName))
                ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                break
    return


def run(ctx, binary, h):
    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    result = emulate(ctx, binary.entrypoint, h)
    debug('[+] Emulation done.')
    return result


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

    # From the README of the challenge: Get your flag by inverting the following values
    # in order, and hex decoding the result.
    hashes = [
        0x875cd4f2e18f8fc4, 0xbb093e17e5d3fa42, 0xada5dd034aae16b4, 0x97322728fea51225,
        0x4124799d72188d0d, 0x2b3e3fbbb4d44981, 0xdfcac668321e4daa, 0xeac2137a35c8923a
    ]

    # Init and emulate
    result = []
    for c, h in enumerate(hashes):
        r = run(ctx, binary, h)
        print(f'[+] Execution {c}, getting hash: {r:#x}')
        result.append(r)

    flag = bytes()
    for r in result:
        flag += codecs.decode(hex(r)[2:], "hex")

    print(f'[+] Flag: {flag}')

    # Used for unittest
    return not flag == b'mirror_mirror_on_the_wall_whos_the_ugliest_handler_of_them_all?!'


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
