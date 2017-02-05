#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2017-02-06
##
##  Description: Solution of the reverse-150 challenge (goto - rvs) from the Hackover 2015 CTF.
##  In this solution, we fully emulate the binary to track all memory STORE. The flag is dynamically
##  decoded and written into the memory. So, the main idea is to track all memory STORE of 1 byte.
##  There are a lot of lines here but only 3 lines are used to track the decoded flag (grep NOTE below),
##  all others lines are used to the emulation part.
##
##  Output:
##
##   $ ./solve.py ./rvs
##   PASSWORD:hackover15{I_USE_GOTO_WHEREEVER_I_W4NT}
##

import os
import sys
import string

from triton import *


# Script options
DEBUG = False

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9fffffff

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


# Simulate the printf_chk() function
def __printf_chk():
    debug('__printf_chk hooked')

    # Get arguments
    arg1   = getConcreteRegisterValue(REG.RDI)
    arg2   = getFormatString(getConcreteRegisterValue(REG.RSI))
    arg3   = getConcreteRegisterValue(REG.RDX)
    arg4   = getConcreteRegisterValue(REG.RCX)
    arg5   = getConcreteRegisterValue(REG.R8)
    arg6   = getConcreteRegisterValue(REG.R9)
    nbArgs = arg2.count("{")
    args   = [arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg2.format(*args)

    sys.stdout.write(s)

    # Return value
    return len(s)


# Simulate the __IO_putc() function
def __IO_putc():
    debug('__IO_putc hooked')

    # Get arguments
    arg1 = getConcreteRegisterValue(REG.RDI)
    sys.stdout.write(chr(arg1))

    # Return value
    return 1


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


# Simulate the fgets() function
def __fgets():
    debug('fgets hooked')

    # Get arguments
    arg1 = getConcreteRegisterValue(REG.RDI)
    arg2 = getConcreteRegisterValue(REG.RSI)

    indx = 0
    #user = raw_input("")[:arg2]
    user = "blah blah"

    for c in user:
        mem = MemoryAccess(arg1 + indx, CPUSIZE.BYTE, ord(c))
        concretizeMemory(mem)
        setConcreteMemoryValue(mem)
        indx += 1

    # Return value
    return arg1



customRelocation = [
    ['__libc_start_main', __libc_start_main,    None],
    ['__printf_chk',      __printf_chk,         None],
    ['__IO_putc',         __IO_putc,            None],
    ['fgets',             __fgets,              None],
    ['malloc',            __malloc,             None],
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

        # NOTE: Here is the solution of the challenge. The flag is decoded
        # and written into the memory. So, let's track all memory STORE of
        # 1 byte.
        for mem, memAst in instruction.getStoreAccess():
            if mem.getSize() == CPUSIZE.BYTE:
                sys.stdout.write(chr(mem.getConcreteValue()))
        # End of solution

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

    if len(sys.argv) < 2:
        print 'Syntax: %s ./rvs' %(sys.argv[0])
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
