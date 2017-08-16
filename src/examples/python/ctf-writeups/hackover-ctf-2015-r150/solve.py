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

import sys
import string

from triton import ARCH, TritonContext, CPUSIZE, MemoryAccess, Instruction, OPCODE


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

Triton = TritonContext()



def getMemoryString(addr):
    s = str()
    index = 0

    while Triton.getConcreteMemoryValue(addr+index):
        c = chr(Triton.getConcreteMemoryValue(addr+index))
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
    size = Triton.getConcreteRegisterValue(Triton.registers.rdi)

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
    arg1   = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    arg2   = getFormatString(Triton.getConcreteRegisterValue(Triton.registers.rsi))
    arg3   = Triton.getConcreteRegisterValue(Triton.registers.rdx)
    arg4   = Triton.getConcreteRegisterValue(Triton.registers.rcx)
    arg5   = Triton.getConcreteRegisterValue(Triton.registers.r8)
    arg6   = Triton.getConcreteRegisterValue(Triton.registers.r9)
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
    arg1 = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    sys.stdout.write(chr(arg1))

    # Return value
    return 1


def __libc_start_main():
    debug('__libc_start_main hooked')

    # Get arguments
    main = Triton.getConcreteRegisterValue(Triton.registers.rdi)

    # Push the return value to jump into the main() function
    Triton.concretizeRegister(Triton.registers.rsp)
    Triton.setConcreteRegisterValue(Triton.registers.rsp, Triton.getConcreteRegisterValue(Triton.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(Triton.getConcreteRegisterValue(Triton.registers.rsp), CPUSIZE.QWORD)
    Triton.concretizeMemory(ret2main)
    Triton.setConcreteMemoryValue(ret2main, main)

    # Setup argc / argv
    Triton.concretizeRegister(Triton.registers.rdi)
    Triton.concretizeRegister(Triton.registers.rsi)

    # Setup target argvs
    argvs = [sys.argv[1]] + sys.argv[2:]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        Triton.setConcreteMemoryAreaValue(base, argv+'\x00')

        # Tainting argvs
        for i in range(len(argv)):
            Triton.taintMemory(base + i)

        base += len(argv)+1
        debug('argv[%d] = %s' %(index, argv))
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        Triton.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    Triton.setConcreteRegisterValue(Triton.registers.rdi, argc)
    Triton.setConcreteRegisterValue(Triton.registers.rsi, argv)

    return 0


# Simulate the fgets() function
def __fgets():
    debug('fgets hooked')

    # Get arguments
    arg1 = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    arg2 = Triton.getConcreteRegisterValue(Triton.registers.rsi)

    indx = 0
    #user = raw_input("")[:arg2]
    user = "blah blah"

    for c in user:
        mem = MemoryAccess(arg1 + indx, CPUSIZE.BYTE)
        Triton.concretizeMemory(mem)
        Triton.setConcreteMemoryValue(mem, ord(c))
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
    pc = Triton.getConcreteRegisterValue(Triton.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1]()
            Triton.concretizeRegister(Triton.registers.rax)
            Triton.setConcreteRegisterValue(Triton.registers.rax, ret_value)

            # Get the return address
            ret_addr = Triton.getConcreteMemoryValue(MemoryAccess(Triton.getConcreteRegisterValue(Triton.registers.rsp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            Triton.concretizeRegister(Triton.registers.rip)
            Triton.setConcreteRegisterValue(Triton.registers.rip, ret_addr)

            # Restore RSP (simulate the ret)
            Triton.concretizeRegister(Triton.registers.rsp)
            Triton.setConcreteRegisterValue(Triton.registers.rsp, Triton.getConcreteRegisterValue(Triton.registers.rsp)+CPUSIZE.QWORD)
    return


# Emulate the binary.
def emulate(pc):
    count = 0
    while pc:
        # Fetch opcode
        opcode = Triton.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        Triton.processing(instruction)
        count += 1

        #print instruction

        # NOTE: Here is the solution of the challenge. The flag is decoded
        # and written into the memory. So, let's track all memory STORE of
        # 1 byte.
        for mem, memAst in instruction.getStoreAccess():
            if mem.getSize() == CPUSIZE.BYTE:
                sys.stdout.write(chr(Triton.getConcreteMemoryValue(mem)))
        # End of solution

        if instruction.getType() == OPCODE.HLT:
            break

        # Simulate routines
        hookingHandler()

        # Next
        pc = Triton.getConcreteRegisterValue(Triton.registers.rip)

    debug('Instruction executed: %d' %(count))
    return


def loadBinary(filename):
    """Load in memory every opcode from an elf program."""
    import lief
    binary = lief.parse(filename)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        Triton.setConcreteMemoryAreaValue(vaddr, phdr.content)
    return binary


def makeRelocation(binary):
    # Setup plt
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    # Perform our own relocations
    for rel in binary.pltgot_relocations:
        symbolName = rel.symbol.name
        symbolRelo = rel.address
        for crel in customRelocation:
            if symbolName == crel[0]:
                debug('Hooking %s' %(symbolName))
                Triton.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                break
    return


def debug(s):
    if DEBUG:
        print '[Triton] %s' %(s)
    return


if __name__ == '__main__':
    # Set the architecture
    Triton.setArchitecture(ARCH.X86_64)

    if len(sys.argv) < 2:
        print 'Syntax: %s ./rvs' %(sys.argv[0])
        sys.exit(1)

    # Load the binary
    binary = loadBinary(sys.argv[1])

    # Perform our own relocations
    makeRelocation(binary)

    # Define a fake stack
    Triton.setConcreteRegisterValue(Triton.registers.rbp, BASE_STACK)
    Triton.setConcreteRegisterValue(Triton.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('Starting emulation')
    emulate(binary.entrypoint)
    debug('Emulation done')

    sys.exit(0)
