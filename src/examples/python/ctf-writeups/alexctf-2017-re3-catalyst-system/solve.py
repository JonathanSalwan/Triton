#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2020-05-03
##
##  Description: Solution of the catalyst system challenge from the ALEXCTF 2017.
##  In this solution, we fully emulate the binary and we solve each branch
##  to go through the good path and print the serial. The particularity of this
##  challenge is that we need to emulate the real behavior of srand and rand of
##  the libc. Thus, we use ctypes to load those two functions. However, in order
##  to be able to use this example as unittest on Linux, Winwdows and OSX, I've
##  hardcoded the return values of rand() with known inputs. If you want to use
##  the ctypes verion, just set the UNITTEST flag to False.
##
##  Output:
##
##  $ time python3 ./solve.py
##  Loading..............................
##  Username: Password: Logging in..............................
##  your flag is: ALEXCTF{1_t41d_y0u_y0u_ar3__gr34t__reverser__s33
##  [+] The username is : catalyst_ceo
##  [+] The password is : sLSVpQ4vK3cGWyW86AiZhggwLHBjmx9CRspVGggj
##  [+] The flag is : 1_t41d_y0u_y0u_ar3__gr34t__reverser__s33
##  Success!
##  python3 ./solve.py  2.68s user 0.02s system 99% cpu 2.709 total
##  $
##

from __future__ import print_function
from triton     import *

import ctypes
import random
import string
import sys
import lief
import os
import platform

TARGET   = os.path.join(os.path.dirname(__file__), 'catalyst')
DEBUG    = False
UNITTEST = True

# The debug function
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x03000000
BASE_STACK = 0x9fffffff

# Allocation information used by malloc()
mallocMaxAllocation = 0x03ffffff
mallocBase = BASE_ALLOC

# Used for srand and rand. Those two functions are
# used for the flag computation and cannot be simulated
# in Python
if not UNITTEST:
    assert(platform.system() == 'Linux')
    libc = ctypes.CDLL('libc.so.6')

# The flag at the end of the analysis
flag = str()

scanf_inputs = [
    b"a" * 12 + b"\x00",
    b"b" * 40 + b"\x00"
]

WITH_PREDICATE = True
conditions = [
    (0x400CBF, REG.X86_64.ZF, 0, WITH_PREDICATE),
    (0x400D2F, REG.X86_64.ZF, 1, WITH_PREDICATE),
    (0x400D5C, REG.X86_64.ZF, 1, WITH_PREDICATE),
    (0x400D77, REG.X86_64.ZF, 1, WITH_PREDICATE),
    (0x400A44, REG.X86_64.ZF, 1, WITH_PREDICATE),
    (0x400A80, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400AAE, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400ADC, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400B0A, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400B38, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400B66, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400B94, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400BC2, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400BF0, REG.X86_64.ZF, 1, not WITH_PREDICATE),
    (0x400C1E, REG.X86_64.ZF, 1, not WITH_PREDICATE),
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


def printfHandler(ctx):
    debug('[+] printf hooked')

    # In this challenge, there is no need of format string
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1)

    # Return value
    return len(arg1)


def putcharHandler(ctx):
    debug('[+] putchar hooked')
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1))
    return arg1


def putsHandler(ctx):
    debug('[+] puts hooked')
    # Don't care about puts in this challenge
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    return len(arg1) + 1


def exitHandler(ctx):
    debug('[+] exit hooked')
    ret = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.exit(ret)


def libcMainHandler(ctx):
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

    return 0


def mallocHandler(ctx):
    global mallocBase
    global mallocMaxAllocation

    debug('[+] malloc hooked')
    size = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    if mallocBase + size > mallocMaxAllocation:
        debug('[+] malloc failed: out of memory')
        sys.exit(-1)
    area = mallocBase
    mallocBase += size

    return area


def strlenHandler(ctx):
    debug('[+] strlen hooked')
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    return len(arg1)


def timeHandler(ctx):
    debug('[+] time hooked')
    return 0


def sleepHandler(ctx):
    debug('[+] sleep hooked')
    return 0


def fflushHandler(ctx):
    debug('[+] fflush hooked')
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    f = [sys.stdin, sys.stdout, sys.stderr]
    f[arg1].flush()
    return 0


def srandHandler(ctx):
    debug('[+] srand hooked')
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    if not UNITTEST:
        libc.srand(arg1)
    return None


def randHandler(ctx):
    debug('[+] rand hooked')
    if not UNITTEST:
        return libc.rand()
    else:
        rax = ctx.getConcreteRegisterValue(ctx.registers.rax)
        oracles = {
            # in rax   :  out rax
            0x030003e8 : 0x00684749,
            0x030003ec : 0x673ce537,
            0x030003f0 : 0x7b4505e7,
            0x030003f4 : 0x70a0b262,
            0x030003f8 : 0x33d5253c,
            0x030003fc : 0x515a7675,
            0x03000400 : 0x596d7d5d,
            0x03000404 : 0x7cd29049,
            0x03000408 : 0x59e72db6,
            0x0300040c : 0x4654600d,
        }
        if rax in oracles:
            return oracles[rax]
    return 0


def scanfHandler(ctx):
    global scanf_inputs
    debug('[+] scanf hooked')

    # Get arguments
    ast  = ctx.getAstContext()
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    seed = scanf_inputs.pop(0)

    # Fill scanf buffer with the input
    ctx.setConcreteMemoryAreaValue(arg2, seed)

    # Symbolize the username and password
    debug('[+] symbolizing scanf buffer')
    for index in range(0, len(seed) - 1):
        var   = ctx.symbolizeMemory(MemoryAccess(arg2 + index, CPUSIZE.BYTE))
        vast  = ast.variable(var)
        chars = ast.lor([
                    ast.land([vast >= ord(b'A'), vast <= ord(b'Z')]),
                    ast.land([vast >= ord(b'a'), vast <= ord(b'z')]),
                    vast == ord(b'_'),
                ])
        ctx.pushPathConstraint(chars)

    # Return value
    return len(seed) - 1


# Functions to emulate
customRelocation = [
    ('__isoc99_scanf',    scanfHandler,    BASE_PLT + 0),
    ('__libc_start_main', libcMainHandler, BASE_PLT + 1),
    ('exit',              exitHandler,     BASE_PLT + 2),
    ('fflush',            fflushHandler,   BASE_PLT + 3),
    ('malloc',            mallocHandler,   BASE_PLT + 4),
    ('printf',            printfHandler,   BASE_PLT + 5),
    ('putchar',           putcharHandler,  BASE_PLT + 6),
    ('puts',              putsHandler,     BASE_PLT + 7),
    ('rand',              randHandler,     BASE_PLT + 8),
    ('sleep',             sleepHandler,    BASE_PLT + 9),
    ('srand',             srandHandler,    BASE_PLT + 10),
    ('strlen',            strlenHandler,   BASE_PLT + 11),
    ('time',              timeHandler,     BASE_PLT + 12),
]


def hookingHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1](ctx)
            if ret_value is not None:
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
    global conditions
    global flag

    count = 0
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction(pc, opcodes)

        # Process
        if ctx.processing(instruction) == EXCEPTION.FAULT_UD:
            debug('[-] Instruction not supported: %s' %(str(instruction)))
            break

        if DEBUG:
            if instruction.isSymbolized():
                print("\033[92m" + str(instruction) + "\033[0m")
            else:
                print(instruction)

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Simulate routines
        hookingHandler(ctx)

        # Here we just restore the password as alphanumeric input
        # to avoid the exit from the loop at loc_4009A4.
        if instruction.getAddress() == 0x400998:
            # The password area from the symbolic variables 12 to 51
            for index in range(12, 52):
                var = ctx.getSymbolicVariable(index)
                ctx.setConcreteVariableValue(var, 0x61)

        for condition in conditions:
            sym_addr, sym_reg, sym_val, with_pp = condition
            if instruction.getAddress() == sym_addr:
                reg = ctx.getRegisterAst(ctx.getRegister(sym_reg))
                ast = ctx.getAstContext()
                mod = (ctx.getModel(ast.land([reg == sym_val, ctx.getPathPredicate()])) if with_pp else ctx.getModel(reg == sym_val))
                for k,v in sorted(mod.items()):
                    ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())

        # Print the flag. Here we just save it for unittest in
        # our solution() function.
        #
        # .text:00000000004008BB movzx   eax, byte ptr [rax]
        # .text:00000000004008BE movsx   eax, al
        # .text:00000000004008C1 xor     eax, edx
        # .text:00000000004008C3 mov     edi, eax
        if instruction.getAddress() == 0x4008C3:
            edi = ctx.getConcreteRegisterValue(ctx.registers.edi)
            flag += chr(edi & 0xff)

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
    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation.')
    emulate(ctx, binary.entrypoint)
    debug('[+] Emulation done.')
    return


def solution(ctx):
    global flag

    inputs = bytearray(52)
    for k, v in sorted(ctx.getSymbolicVariables().items()):
        inputs[k] = ctx.getConcreteVariableValue(v)

    if inputs[:12] != b'catalyst_ceo':
        return -1

    if inputs[12:52] != b'sLSVpQ4vK3cGWyW86AiZhggwLHBjmx9CRspVGggj':
        return -1

    if flag != '1_t41d_y0u_y0u_ar3__gr34t__reverser__s33':
        return -1

    print("\n[+] The username is : %s" %(inputs[:12].decode('utf-8')))
    print("[+] The password is : %s" %(inputs[12:52].decode('utf-8')))
    print("[+] The flag is : %s" %(flag))

    print('Success!')
    return 0



def main():
    # Get a Triton context
    ctx = TritonContext(ARCH.X86_64)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Perform our own relocations
    makeRelocation(ctx, binary)

    # Init and emulate
    run(ctx, binary)

    return solution(ctx)


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
