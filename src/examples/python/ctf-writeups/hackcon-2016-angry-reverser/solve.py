#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2018-11-02
##
##  This code solve the angry-reverser from the HackCon 2016 CTF.
##  The particularity of this sample is that we use an external solver to solve
##  queries instead of using the internal Triton's solver (even if in both cases
##  it uses z3). The point here is to show that Triton can provide generic smt2
##  outputs and theses outputs can be send to external solvers and get back
##  model which then are sent to Triton (see the myExternalSolver function of
##  this example).
##
##  Output:
##
##  $ time python solve.py
##  [+] Loading 0x400040 - 0x400200
##  [+] Loading 0x400200 - 0x40021c
##  [+] Loading 0x400000 - 0x405d04
##  [+] Loading 0x605d08 - 0x605f58
##  [+] Loading 0x605d20 - 0x605ef0
##  [+] Loading 0x40021c - 0x400260
##  [+] Loading 0x405bb0 - 0x405bec
##  [+] Loading 0x000000 - 0x000000
##  [+] Hooking puts
##  [+] Hooking printf
##  [+] Hooking __libc_start_main
##  [+] Hooking ptrace
##  [+] Hooking __isoc99_scanf
##  [+] Hooking exit
##  [+] Starting emulation.
##  [+] __libc_start_main hooked
##  [+] argv[0] = yolomolo
##  [+] scanf hooked
##  [+] symbolizing scanf buffer
##  [+] ptrace hooked
##  [+] Solving condition at 0x402c31
##  [+] Solving condition at 0x402ea4
##  [+] Solving condition at 0x403111
##  [+] Solving condition at 0x403380
##  [+] Solving condition at 0x4035ed
##  [+] Solving condition at 0x40385d
##  [+] Solving condition at 0x403aca
##  [+] Solving condition at 0x403d3c
##  [+] Solving condition at 0x403fae
##  [+] Solving condition at 0x40421c
##  [+] Solving condition at 0x40448b
##  [+] Solving condition at 0x4046ff
##  [+] Solving condition at 0x40496d
##  [+] Solving condition at 0x404be1
##  [+] Solving condition at 0x404e4e
##  [+] Solving condition at 0x4050bc
##  [+] Solving condition at 0x40532d
##  [+] Solving condition at 0x40559e
##  [+] Solving condition at 0x4057e9
##  [+] Solving condition at 0x405a20
##  [+] printf hooked
##  YAYY : 2684354496
##  [+] Solving the last query to get the good serial...
##  Serial is: HACKCON{VVhYS04ngrY}
##  [-] Instruction not supported: 0x400579: hlt
##  [+] Instruction executed: 4453
##  [+] Emulation done.
##
##  python solve.py  279.91s user 0.13s system 99% cpu 4:40.07 total
##

from __future__ import print_function
from triton     import *

import random
import string
import sys
import os
import lief

TARGET = os.path.join(os.path.dirname(__file__), 'yolomolo')
DEBUG  = True
SERIAL = str()

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_STACK = 0x9fffffff

# These instruction conditions must set zf to 1.
conditions = [
    0x402C31,
    0x402EA4,
    0x403111,
    0x403380,
    0x4035ED,
    0x40385D,
    0x403ACA,
    0x403D3C,
    0x403FAE,
    0x40421C,
    0x40448B,
    0x4046FF,
    0x40496D,
    0x404BE1,
    0x404E4E,
    0x4050BC,
    0x40532D,
    0x40559E,
    0x4057E9,
    0x405A20,
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


# Simulate the scanf() function
def scanfHandler(ctx):
    debug('[+] scanf hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    # Fill scanf buffer with dummy inputs
    ctx.setConcreteMemoryAreaValue(arg2, b"a" * 30 + b'\n\x00')

    # Symbolize 30 bytes
    debug('[+] symbolizing scanf buffer')
    for index in range(20):
        ctx.taintMemory(MemoryAccess(arg2 + index, CPUSIZE.BYTE))
        var = ctx.convertMemoryToSymbolicVariable(MemoryAccess(arg2 + index, CPUSIZE.BYTE))

    # Return value
    return 21


# Simulate the ptrace() function
def ptraceHandler(ctx):
    debug('[+] ptrace hooked')
    # Don't care about ptrace :)
    # Return value
    return 0


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
    sys.exit(0)


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
        TARGET,     # argv[0]
    ]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, bytes(argv.encode('utf8')) + b'\x00')
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

    return 0


# Functions to emulate
customRelocation = [
    ('__libc_start_main', libcMainHandler, BASE_PLT + 0),
    ('__isoc99_scanf',    scanfHandler,    BASE_PLT + 1),
    ('exit',              exitHandler,     BASE_PLT + 2),
    ('printf',            printfHandler,   BASE_PLT + 3),
    ('ptrace',            ptraceHandler,   BASE_PLT + 4),
    ('putchar',           putcharHandler,  BASE_PLT + 5),
    ('puts',              putsHandler,     BASE_PLT + 6),
    ('strncpy',           strncpyHandler,  BASE_PLT + 7),
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


def getVarSyntax(ctx):
    s = str()
    ast = ctx.getAstContext()
    for k, v in list(ctx.getSymbolicVariables().items()):
        s += str(ast.declare(ast.variable(v))) + '\n'
    return s


def getSSA(ctx, expr):
    s = str()
    ast = ctx.getAstContext()
    ssa = ctx.sliceExpressions(expr)
    for k, v in sorted(ssa.items())[:-1]:
        s += str(v) + '\n'
    s += str(ast.assert_(expr.getAst())) + '\n'
    return s


def myExternalSolver(ctx, node, addr=None):
    """
    The particularity of this sample is that we use an external solver to solve
    queries instead of using the internal Triton's solver (even if in both cases
    it uses z3). The point here is to show that Triton can provide generic smt2
    outputs and theses outputs can be send to external solvers and get back model
    which then are sent to Triton.
    """
    import z3
    expr = ctx.newSymbolicExpression(node, "Custom for Solver")
    smtFormat = '(set-logic QF_BV) %s %s (check-sat) (get-model)' %(getVarSyntax(ctx), getSSA(ctx, expr))
    c = z3.Context()
    s = z3.Solver(ctx=c)
    s.add(z3.parse_smt2_string(smtFormat, ctx=c))
    if addr:
        debug('[+] Solving condition at %#x' %(addr))
    if s.check() == z3.sat:
        ret = dict()
        model = s.model()
        for x in model:
            ret.update({int(str(x).split('_')[1], 10): int(str(model[x]), 10)})
        return ret
    else:
        debug('[-] unsat :(')
        sys.exit(-1)
    return


# Emulate the binary.
def emulate(ctx, pc):
    global SERIAL
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

        #print(instruction)

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        if pc in conditions:
            zf  = ctx.getSymbolicRegister(ctx.registers.zf).getAst()
            ast = ctx.getAstContext()
            pco = ctx.getPathConstraintsAst()
            mod = myExternalSolver(ctx, zf == 1, pc)
            for k, v in list(mod.items()):
                ctx.setConcreteVariableValue(ctx.getSymbolicVariableFromId(k), v)

        # End of the execution
        if pc == 0x405B00:
            debug('[+] Solving the last query to get the good serial...')
            ast = ctx.getAstContext()
            pco = ctx.getPathConstraintsAst()
            mod = myExternalSolver(ctx, ast.land(
                    [pco] +
                    [ast.variable(ctx.getSymbolicVariableFromId(x)) >= 0x20 for x in range(0, 20)] +
                    [ast.variable(ctx.getSymbolicVariableFromId(x)) <= 0x7e for x in range(0, 20)] +
                    [ast.variable(ctx.getSymbolicVariableFromId(x)) != 0x00 for x in range(0, 20)]
                  ))
            serial = str()
            for k, v in sorted(mod.items()):
                serial += chr(v)
            print('Serial is: %s' %(serial))
            SERIAL = serial

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
    return not (SERIAL == 'HACKCON{VVhYS04ngrY}')


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
