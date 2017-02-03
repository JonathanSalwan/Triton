#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## An example of a small symbolic emulator for elf x86-64 binaries.
## Only simulates these following libc functions (but feel free to
## add more ones):
##
##  * __libc_start_main
##  * atoi
##  * atol
##  * atoll
##  * malloc
##  * printf
##  * putchar
##  * puts
##  * raise
##  * rand
##  * signal
##  * strlen
##  * strtoul
##
## Example:
##
##  $ ./small_x86-64_symbolic_emulator.py ./samples/sample_1 hello
##  [Triton] Loading 0x400040 - 0x400270
##  [Triton] Loading 0x400270 - 0x40028c
##  [Triton] Loading 0x400000 - 0x4007a4
##  [Triton] Loading 0x600e10 - 0x601048
##  [Triton] Loading 0x600e28 - 0x600ff8
##  [Triton] Loading 0x40028c - 0x4002ac
##  [Triton] Loading 0x400678 - 0x4006ac
##  [Triton] Loading 0x000000 - 0x000000
##  [Triton] Loading 0x600e10 - 0x601000
##  [Triton] Loading 0x000000 - 0x000000
##  [Triton] Hooking strlen
##  [Triton] Hooking printf
##  [Triton] Hooking __libc_start_main
##  [Triton] Starting emulation
##  [Triton] __libc_start_main hooked
##  [Triton] argv[0] = ./samples/sample_1
##  [Triton] argv[1] = hello
##  [Triton] strlen hooked
##  [Triton] printf hooked
##  Input size = 5
##  [Triton] Instruction executed: 34
##  [Triton] Emulation done
##

import os
import sys
import struct
import ctypes
import string
import random

from triton import *


# Script options
DEBUG = True

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9fffffff

# Signal handlers used by raise() and signal()
sigHandlers = dict()

# Allocation information used by malloc()
mallocCurrentAllocation = 0
mallocMaxAllocation     = 2048
mallocBase              = BASE_ALLOC
mallocChunkSize         = 0x00010000



def getMemoryString(addr):
    s = str()
    index = 0

    while getConcreteMemoryValue(addr+index):
        c = chr(getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def getFormatString(addr):
    return getMemoryString(addr)                                                    \
           .replace("%s", "{}").replace("%d", "{:d}").replace("%#02x", "{:#02x}")   \
           .replace("%#x", "{:#x}").replace("%x", "{:x}").replace("%02X", "{:02x}") \
           .replace("%c", "{:c}").replace("%02x", "{:02x}").replace("%ld", "{:d}")  \
           .replace("%*s", "").replace("%lX", "{:x}").replace("%08x", "{:08x}")     \
           .replace("%u", "{:d}").replace("%lu", "{:d}")                            \


# Simulate the rand() function
def __rand():
    debug('rand hooked')
    # Return value
    return random.randrange(0xffffffff)


# Simulate the malloc() function
def __malloc():
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    debug('malloc hooked')

    # Get arguments
    size = getConcreteRegisterValue(REG.RDI)

    if size > mallocChunkSize:
        debug('malloc failed: size too big')
        sys.exit(-1)

    if mallocCurrentAllocation >= mallocMaxAllocation:
        debug('malloc failed: too many allocations done')
        sys.exit(-1)

    area = mallocBase + (mallocCurrentAllocation * mallocChunkSize)
    mallocCurrentAllocation += 1

    # Return value
    return area


# Simulate the signal() function
def __signal():
    debug('signal hooked')

    # Get arguments
    signal  = getConcreteRegisterValue(REG.RDI)
    handler = getConcreteRegisterValue(REG.RSI)

    global sigHandlers
    sigHandlers.update({signal: handler})

    # Return value (void)
    return getConcreteRegisterValue(REG.RAX)


# Simulate the raise() function
def __raise():
    debug('raise hooked')

    # Get arguments
    signal  = getConcreteRegisterValue(REG.RDI)
    handler = sigHandlers[signal]

    processing(Instruction("\x6A\x00")) # push 0
    emulate(handler)

    # Return value
    return 0


# Simulate the strlen() function
def __strlen():
    debug('strlen hooked')

    # Get arguments
    arg1 = getMemoryString(getConcreteRegisterValue(REG.RDI))

    # Return value
    return len(arg1)


# Simulate the strtoul() function
def __strtoul():
    debug('strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(getConcreteRegisterValue(REG.RDI))
    endptr = getConcreteRegisterValue(REG.RSI)
    base   = getConcreteRegisterValue(REG.RDX)

    # Return value
    return long(nptr, base)


# Simulate the printf() function
def __printf():
    debug('printf hooked')

    # Get arguments
    arg1   = getFormatString(getConcreteRegisterValue(REG.RDI))
    arg2   = getConcreteRegisterValue(REG.RSI)
    arg3   = getConcreteRegisterValue(REG.RDX)
    arg4   = getConcreteRegisterValue(REG.RCX)
    arg5   = getConcreteRegisterValue(REG.R8)
    arg6   = getConcreteRegisterValue(REG.R9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg1.format(*args)

    sys.stdout.write(s)

    # Return value
    return len(s)


# Simulate the putchar() function
def __putchar():
    debug('putchar hooked')

    # Get arguments
    arg1 = getConcreteRegisterValue(REG.RDI)
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def __puts():
    debug('puts hooked')

    # Get arguments
    arg1 = getMemoryString(getConcreteRegisterValue(REG.RDI))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def __libc_start_main():
    debug('__libc_start_main hooked')

    # Get arguments
    main = getConcreteRegisterValue(REG.RDI)

    # Push the return value to jump into the main() function
    concretizeRegister(REG.RSP)
    setConcreteRegisterValue(Register(REG.RSP, getConcreteRegisterValue(REG.RSP)-CPUSIZE.QWORD))

    ret2main = MemoryAccess(getConcreteRegisterValue(REG.RSP), CPUSIZE.QWORD, main)
    concretizeMemory(ret2main)
    setConcreteMemoryValue(ret2main)

    # Setup argc / argv
    concretizeRegister(REG.RDI)
    concretizeRegister(REG.RSI)

    # Setup target argvs
    argvs = [sys.argv[1]] + sys.argv[2:]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        setConcreteMemoryAreaValue(base, argv+'\x00')

        # Tainting argvs
        for i in range(len(argv)):
            taintMemory(base + i)

        base += len(argv)+1
        debug('argv[%d] = %s' %(index, argv))
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD, addr))
        base += CPUSIZE.QWORD

    setConcreteRegisterValue(Register(REG.RDI, argc))
    setConcreteRegisterValue(Register(REG.RSI, argv))

    return 0


# Simulate the atoi() function
def __atoi():
    debug('atoi hooked')

    # Get arguments
    arg1 = getMemoryString(getConcreteRegisterValue(REG.RDI))

    # Return value
    return int(arg1)


# Simulate the atol() function
def __atol():
    debug('atol hooked')

    # Get arguments
    arg1 = getMemoryString(getConcreteRegisterValue(REG.RDI))

    # Return value
    return long(arg1)


# Simulate the atoll() function
def __atoll():
    debug('atoll hooked')

    # Get arguments
    arg1 = getMemoryString(getConcreteRegisterValue(REG.RDI))

    # Return value
    return long(arg1)


customRelocation = [
    ['__libc_start_main', __libc_start_main,    None],
    ['atoi',              __atoi,               None],
    ['atol',              __atol,               None],
    ['atoll',             __atoll,              None],
    ['malloc',            __malloc,             None],
    ['printf',            __printf,             None],
    ['putchar',           __putchar,            None],
    ['puts',              __puts,               None],
    ['raise',             __raise,              None],
    ['rand',              __rand,               None],
    ['signal',            __signal,             None],
    ['strlen',            __strlen,             None],
    ['strtoul',           __strtoul,            None],
]


def hookingHandler():
    pc = getConcreteRegisterValue(REG.RIP)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1]()
            concretizeRegister(REG.RAX)
            setConcreteRegisterValue(Register(REG.RAX, ret_value))

            # Get the return address
            ret_addr = getConcreteMemoryValue(MemoryAccess(getConcreteRegisterValue(REG.RSP), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            concretizeRegister(REG.RIP)
            setConcreteRegisterValue(Register(REG.RIP, ret_addr))

            # Restore RSP (simulate the ret)
            concretizeRegister(REG.RSP)
            setConcreteRegisterValue(Register(REG.RSP, getConcreteRegisterValue(REG.RSP)+CPUSIZE.QWORD))
    return


# Emulate the binary.
def emulate(pc):
    count = 0
    while pc:
        # Fetch opcodes
        opcodes = getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcodes(opcodes)
        instruction.setAddress(pc)

        # Process
        processing(instruction)
        count += 1

        #print instruction

        if instruction.getType() == OPCODE.HLT:
            break

        # Simulate routines
        hookingHandler()

        # Next
        pc = getConcreteRegisterValue(REG.RIP)

    debug('Instruction executed: %d' %(count))
    return


def loadBinary(binary):
    # Map the binary into the memory
    raw = binary.getRaw()
    phdrs = binary.getProgramHeaders()
    for phdr in phdrs:
        offset = phdr.getOffset()
        size   = phdr.getFilesz()
        vaddr  = phdr.getVaddr()
        debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        setConcreteMemoryAreaValue(vaddr, raw[offset:offset+size])
    return


def makeRelocation(binary):
    # Setup plt
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    # Perform our own relocations
    symbols = binary.getSymbolsTable()
    relocations = binary.getRelocationTable()
    for rel in relocations:
        symbolName = symbols[rel.getSymidx()].getName()
        symbolRelo = rel.getOffset()
        for crel in customRelocation:
            if symbolName == crel[0]:
                debug('Hooking %s' %(symbolName))
                setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD, crel[2]))
                break
    return


def debug(s):
    if DEBUG:
        print '[Triton] %s' %(s)
    return


if __name__ == '__main__':
    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Set a symbolic optimization mode
    enableMode(MODE.ALIGNED_MEMORY, True)

    # AST representation as Python syntax
    #setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    if len(sys.argv) < 2:
        debug('Syntax: %s <elf binary> [arg1, arg2, ...]' %(sys.argv[0]))
        sys.exit(1)

    # Parse the binary
    binary = Elf(sys.argv[1])

    # Load the binary
    loadBinary(binary)

    # Perform our own relocations
    makeRelocation(binary)

    # Define a fake stack
    setConcreteRegisterValue(Register(REG.RBP, BASE_STACK))
    setConcreteRegisterValue(Register(REG.RSP, BASE_STACK))

    # Let's emulate the binary from the entry point
    debug('Starting emulation')
    emulate(binary.getHeader().getEntry())
    debug('Emulation done')

    sys.exit(0)

