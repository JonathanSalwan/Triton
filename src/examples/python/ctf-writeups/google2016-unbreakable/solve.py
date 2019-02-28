#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2018-10-26
##
##  Description: Solution of the unbreakable challenge from the Google 2016 CTF.
##  In this solution, we fully emulate the binary and we solve each branch
##  to go through the good path.
##
##  Output:
##
##  $ time python ./solve.py
##  [+] Loading 0x400040 - 0x400200
##  [+] Loading 0x400200 - 0x40021c
##  [+] Loading 0x400000 - 0x403df4
##  [+] Loading 0x604000 - 0x604258
##  [+] Loading 0x604018 - 0x6041e8
##  [+] Loading 0x40021c - 0x400260
##  [+] Loading 0x403590 - 0x40378c
##  [+] Loading 0x000000 - 0x000000
##  [+] Hooking strncpy
##  [+] Hooking puts
##  [+] Hooking printf
##  [+] Hooking __libc_start_main
##  [+] Hooking exit
##  [+] Starting emulation.
##  [+] __libc_start_main hooked
##  [+] argv[0] = ./unbreakable-enterprise-product-activation
##  [+] argv[1] = aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
##  [+] strncpy hooked
##  [+] puts hooked
##  Thank you - product activated!
##  [+] exit hooked
##  Flag: CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}
##  python ./solve.py  14.32s user 0.03s system 99% cpu 14.363 total
##

from __future__ import print_function
from triton     import *

import random
import string
import sys
import lief
import os

TARGET = os.path.join(os.path.dirname(__file__), 'unbreakable-enterprise-product-activation')
DEBUG  = True

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_STACK = 0x9fffffff

# These instruction conditions must set zf to 1.
conditions = [
    0x402819,
    0x402859,
    0x4028A3,
    0x4028F3,
    0x402927,
    0x402969,
    0x4029A9,
    0x4029E0,
    0x402A1F,
    0x402A56,
    0x402A99,
    0x402AD9,
    0x402B07,
    0x402B37,
    0x402B79,
    0x402BA7,
    0x402BD7,
    0x402C22,
    0x402C69,
    0x402CA9,
    0x402CD7,
    0x402D22,
    0x402D73,
    0x402DB0,
    0x402DF9,
    0x402E43,
    0x402E89,
    0x402EC9,
    0x402EF7,
    0x402F30,
    0x402F79,
    0x402FB9,
    0x402FF9,
    0x403039,
    0x403079,
    0x4030C5,
    0x403109,
    0x403149,
    0x403189,
    0x4031B7,
    0x4031F9,
    0x403239,
    0x403270,
    0x4032B0,
    0x403302,
    0x403337,
    0x403379,
    0x4033B9,
    0x4033F0,
    0x403427,
    0x403472,
]


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
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg6   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg1.format(*args)

    if DEBUG:
        sys.stdout.write(s)

    # Return value
    return len(s)


# Simulate the putchar() function
def putcharHandler(ctx):
    debug('[+] putchar hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def putsHandler(ctx):
    debug('[+] puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1


# Simulate the strncpy() function
def strncpyHandler(ctx):
    debug('[+] strncpy hooked')

    dst = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    src = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    cnt = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    for index in range(cnt):
        dmem  = MemoryAccess(dst + index, 1)
        smem  = MemoryAccess(src + index, 1)
        cell = ctx.getMemoryAst(smem)
        expr = ctx.newSymbolicExpression(cell, "strncpy byte")
        ctx.assignSymbolicExpressionToMemory(expr, dmem)
        ctx.setConcreteMemoryValue(dmem, cell.evaluate())

    return dst


def exitHandler(ctx):
    debug('[+] exit hooked')

    ret = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    ast = ctx.getAstContext()
    pco = ctx.getPathConstraintsAst()
    # Ask for a new model which set all symbolic variables to ascii printable characters
    mod = ctx.getModel(ast.land(
            [pco] +
            [ast.variable(ctx.getSymbolicVariableFromId(0))  == ord('C')] +
            [ast.variable(ctx.getSymbolicVariableFromId(1))  == ord('T')] +
            [ast.variable(ctx.getSymbolicVariableFromId(2))  == ord('F')] +
            [ast.variable(ctx.getSymbolicVariableFromId(3))  == ord('{')] +
            [ast.variable(ctx.getSymbolicVariableFromId(50)) == ord('}')] +
            [ast.variable(ctx.getSymbolicVariableFromId(x))  >= 0x20 for x in range(4, 49)] +
            [ast.variable(ctx.getSymbolicVariableFromId(x))  <= 0x7e for x in range(4, 49)] +
            [ast.variable(ctx.getSymbolicVariableFromId(x))  != 0x00 for x in range(4, 49)]
          ))

    flag = str()
    for k, v in sorted(mod.items()):
        flag += chr(v.getValue())
    print('Flag: %s' %(flag))

    sys.exit(not (flag == 'CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}'))


def libcMainHandler(ctx):
    debug('[+] __libc_start_main hooked')

    # Get arguments
    main = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Push the return value to jump into the main() function
    ctx.concretizeRegister(ctx.registers.rsp)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD)
    ctx.concretizeMemory(ret2main)
    ctx.setConcreteMemoryValue(ret2main, main)

    # Setup argc / argv
    ctx.concretizeRegister(ctx.registers.rdi)
    ctx.concretizeRegister(ctx.registers.rsi)

    argvs = [
        bytes(TARGET.encode('utf-8')),  # argv[0]
        bytes(b'a' * 70),               # argv[1]
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

    # Symbolize the first 51 bytes of the argv[1]
    argv1 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi) + 8, CPUSIZE.QWORD))
    for index in range(51):
        var = ctx.convertMemoryToSymbolicVariable(MemoryAccess(argv1+index, CPUSIZE.BYTE))

    return 0


# Functions to emulate
customRelocation = [
    ('__libc_start_main', libcMainHandler, BASE_PLT + 0),
    ('exit',              exitHandler,     BASE_PLT + 1),
    ('printf',            printfHandler,   BASE_PLT + 2),
    ('putchar',           putcharHandler,  BASE_PLT + 3),
    ('puts',              putsHandler,     BASE_PLT + 4),
    ('strncpy',           strncpyHandler,  BASE_PLT + 5),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.concretizeRegister(ctx.registers.rax)
                ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)

            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            ctx.concretizeRegister(ctx.registers.rip)
            ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)

            # Restore RSP (simulate the ret)
            ctx.concretizeRegister(ctx.registers.rsp)
            ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
    return


# Emulate the binary.
def emulate(ctx, pc):
    global conditions

    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcodes)
        instruction.setAddress(pc)

        # Process
        if ctx.processing(instruction) == False:
            debug('[-] Instruction not supported: %s' %(str(instruction)))
            break

        count += 1

        #print instruction

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        if instruction.getAddress() in conditions:
            zf  = ctx.getSymbolicRegister(ctx.registers.zf).getAst()
            ast = ctx.getAstContext()
            pco = ctx.getPathConstraintsAst()
            mod = ctx.getModel(ast.land([pco, zf == 1]))
            for k,v in list(mod.items()):
                ctx.setConcreteVariableValue(ctx.getSymbolicVariableFromId(v.getId()), v.getValue())

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

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

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def main():
    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.X86_64)

    # Set optimization
    ctx.enableMode(MODE.ALIGNED_MEMORY, True)
    ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # AST representation as Python syntax
    ctx.setAstRepresentationMode(AST_REPRESENTATION.SMT)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Init and emulate
    run(ctx, binary)
    return 0


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
