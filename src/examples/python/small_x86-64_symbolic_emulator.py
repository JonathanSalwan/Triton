#!/usr/bin/env python3
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

from __future__ import print_function
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

import sys
import string
import random


# Script options
DEBUG = True

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9ffffff0

# Signal handlers used by raise() and signal()
sigHandlers = dict()

# Allocation information used by malloc()
mallocCurrentAllocation = 0
mallocMaxAllocation     = 2048
mallocBase              = BASE_ALLOC
mallocChunkSize         = 0x00010000



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
           .replace("%u", "{:d}").replace("%lu", "{:d}")                            \


# Simulate the rand() function
def __rand(ctx):
    debug('rand hooked')
    # Return value
    return random.randrange(0xffffffff)


# Simulate the malloc() function
def __malloc(ctx):
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    debug('malloc hooked')

    # Get arguments
    size = ctx.getConcreteRegisterValue(ctx.registers.rdi)

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
def __signal(ctx):
    debug('signal hooked')

    # Get arguments
    signal  = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    handler = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    global sigHandlers
    sigHandlers.update({signal: handler})

    # Return value (void)
    return ctx.getConcreteRegisterValue(ctx.registers.rax)


# Simulate the raise() function
def __raise(ctx):
    debug('raise hooked')

    # Get arguments
    signal  = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    handler = sigHandlers[signal]

    ctx.processing(Instruction(b"\x6A\x00")) # push 0
    emulate(ctx, handler)

    # Return value
    return 0


# Simulate the strlen() function
def __strlen(ctx):
    debug('strlen hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return len(arg1)


# Simulate the strtoul() function
def __strtoul(ctx):
    debug('strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    endptr = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    base   = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    # Return value
    return int(nptr, base)

# Simulate the printf() function
def __printf(ctx):
    debug('printf hooked')

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
    return len(s)


# Simulate the putchar() function
def __putchar(ctx):
    debug('putchar hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def __puts(ctx):
    debug('puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


def __libc_start_main(ctx):
    debug('__libc_start_main hooked')

    # Get arguments
    main = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Push the return value to jump into the main() function
    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD)
    ctx.setConcreteMemoryValue(ret2main, main)

    # Setup target argvs
    argvs = [sys.argv[1]] + sys.argv[2:]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, bytes(argv.encode('utf8')) + b'\x00')

        # Tainting argvs
        for i in range(len(argv)):
            ctx.taintMemory(base + i)

        base += len(argv)+1
        debug('argv[%d] = %s' %(index, argv))
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    ctx.setConcreteRegisterValue(ctx.registers.rdi, argc)
    ctx.setConcreteRegisterValue(ctx.registers.rsi, argv)

    return 0


# Simulate the atoi() function
def __atoi(ctx):
    debug('atoi hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)


# Simulate the atol() function
def __atol(ctx):
    debug('atol hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)


# Simulate the atoll() function
def __atoll(ctx):
    debug('atoll hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)

def __memcpy(ctx):
    debug('memcpy hooked')

    #Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3 = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    for index in range(arg3):
        value = ctx.getConcreteMemoryValue(arg2 + index)
        ctx.setConcreteMemoryValue(arg1 + index, value)

    return arg1

def __strcat(ctx):
    debug('strcat hooked')

    #Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    src_length = len(getMemoryString(ctx, arg1))
    dest_length = len(getMemoryString(ctx, arg2))
    for index in range(dest_length):
        value = ctx.getConcreteMemoryValue(arg2 + index)
        ctx.setConcreteMemoryValue(arg1 + index + src_length, value)

    return arg1


customRelocation = [
    ['__libc_start_main', __libc_start_main,    None],
    ['atoi',              __atoi,               None],
    ['atol',              __atol,               None],
    ['atoll',             __atoll,              None],
    ['malloc',            __malloc,             None],
    ['memcpy',            __memcpy,             None],
    ['printf',            __printf,             None],
    ['putchar',           __putchar,            None],
    ['puts',              __puts,               None],
    ['raise',             __raise,              None],
    ['rand',              __rand,               None],
    ['signal',            __signal,             None],
    ['strcat',            __strcat,             None],
    ['strlen',            __strlen,             None],
    ['strtoul',           __strtoul,            None],
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)

            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)

            # Restore RSP (simulate the ret)
            ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
    return


# Emulate the binary.
def emulate(ctx, pc):
    count = 0
    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction(pc, opcode)

        # Process
        ctx.processing(instruction)
        count += 1

        #print instruction
        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    debug('Instruction executed: %d' %(count))
    return


def loadBinary(ctx, path):
    import lief
    # Map the binary into the memory
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))
    return binary


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
                debug('Hooking %s' %(symbolName))
                ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                break
    return


def debug(s):
    if DEBUG:
        print('[Triton] %s' %(s))
    return


if __name__ == '__main__':
    # Set the architecture
    ctx = TritonContext(ARCH.X86_64)

    # Set a symbolic optimization mode
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    # AST representation as Python syntax
    #setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    if len(sys.argv) < 2:
        debug('Syntax: %s <elf binary> [arg1, arg2, ...]' %(sys.argv[0]))
        sys.exit(1)

    # Load the binary
    binary = loadBinary(ctx, sys.argv[1])

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('Starting emulation')
    emulate(ctx, binary.entrypoint)
    debug('Emulation done')

    sys.exit(0)
