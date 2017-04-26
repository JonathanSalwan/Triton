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

import sys
import string
import random

from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

Triton = TritonContext()


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


# Simulate the signal() function
def __signal():
    debug('signal hooked')

    # Get arguments
    signal  = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    handler = Triton.getConcreteRegisterValue(Triton.registers.rsi)

    global sigHandlers
    sigHandlers.update({signal: handler})

    # Return value (void)
    return Triton.getConcreteRegisterValue(Triton.registers.rax)


# Simulate the raise() function
def __raise():
    debug('raise hooked')

    # Get arguments
    signal  = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    handler = sigHandlers[signal]

    Triton.processing(Instruction("\x6A\x00")) # push 0
    emulate(handler)

    # Return value
    return 0


# Simulate the strlen() function
def __strlen():
    debug('strlen hooked')

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))

    # Return value
    return len(arg1)


# Simulate the strtoul() function
def __strtoul():
    debug('strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))
    endptr = Triton.getConcreteRegisterValue(Triton.registers.rsi)
    base   = Triton.getConcreteRegisterValue(Triton.registers.rdx)

    # Return value
    return long(nptr, base)


# Simulate the printf() function
def __printf():
    debug('printf hooked')

    # Get arguments
    arg1   = getFormatString(Triton.getConcreteRegisterValue(Triton.registers.rdi))
    arg2   = Triton.getConcreteRegisterValue(Triton.registers.rsi)
    arg3   = Triton.getConcreteRegisterValue(Triton.registers.rdx)
    arg4   = Triton.getConcreteRegisterValue(Triton.registers.rcx)
    arg5   = Triton.getConcreteRegisterValue(Triton.registers.r8)
    arg6   = Triton.getConcreteRegisterValue(Triton.registers.r9)
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
    arg1 = Triton.getConcreteRegisterValue(Triton.registers.rdi)
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def __puts():
    debug('puts hooked')

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


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


# Simulate the atoi() function
def __atoi():
    debug('atoi hooked')

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))

    # Return value
    return int(arg1)


# Simulate the atol() function
def __atol():
    debug('atol hooked')

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))

    # Return value
    return long(arg1)


# Simulate the atoll() function
def __atoll():
    debug('atoll hooked')

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))

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

        if instruction.getType() == OPCODE.HLT:
            break

        # Simulate routines
        hookingHandler()

        # Next
        pc = Triton.getConcreteRegisterValue(Triton.registers.rip)

    debug('Instruction executed: %d' %(count))
    return


def loadBinary(path):
    import lief
    # Map the binary into the memory
    binary = lief.parse(path)
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

    # Set a symbolic optimization mode
    Triton.enableMode(MODE.ALIGNED_MEMORY, True)

    # AST representation as Python syntax
    #setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    if len(sys.argv) < 2:
        debug('Syntax: %s <elf binary> [arg1, arg2, ...]' %(sys.argv[0]))
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

