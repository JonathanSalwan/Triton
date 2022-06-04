#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2021-07-27
##
##  Description: In this challenge, every character of the user input is computed into a
##  signal handler. If a character N is good, the current handler calls the the handler
##  in charge of verifying the character N + 1. Handlers have no dependence between each
##  oter. At the end of each handler execution we can ask for a model to solve the current
##  character. Each character of the user input is computed in order to obtain an hash.
##  In every handler this hash must be equal to 0x3E8.
##
##  Output:
##  $ time python solve.py
##  [+] Loading 0x400040 - 0x400238
##  [+] Loading 0x400238 - 0x400254
##  [+] Loading 0x400000 - 0x40324c
##  [+] Loading 0x603e10 - 0x604088
##  [+] Loading 0x603e28 - 0x603ff8
##  [+] Loading 0x400254 - 0x400298
##  [+] Loading 0x402d8c - 0x402e78
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x603e10 - 0x604000
##  Starting the emulation of all signal handler
##  [+] Symbolic variable 00 = 44 (D)
##  [+] Symbolic variable 01 = 69 (i)
##  [+] Symbolic variable 02 = 64 (d)
##  [+] Symbolic variable 03 = 5f (_)
##  [+] Symbolic variable 04 = 79 (y)
##  [+] Symbolic variable 05 = 6f (o)
##  [+] Symbolic variable 06 = 75 (u)
##  [+] Symbolic variable 07 = 5f (_)
##  [+] Symbolic variable 08 = 6c (l)
##  [+] Symbolic variable 09 = 69 (i)
##  [+] Symbolic variable 10 = 6b (k)
##  [+] Symbolic variable 11 = 65 (e)
##  [+] Symbolic variable 12 = 5f (_)
##  [+] Symbolic variable 13 = 73 (s)
##  [+] Symbolic variable 14 = 69 (i)
##  [+] Symbolic variable 15 = 67 (g)
##  [+] Symbolic variable 16 = 6e (n)
##  [+] Symbolic variable 17 = 61 (a)
##  [+] Symbolic variable 18 = 6c (l)
##  [+] Symbolic variable 19 = 73 (s)
##  [+] Symbolic variable 20 = 3f (?)
##  python solve.py  2.28s user 0.01s system 99% cpu 2.294 total
##

import os
import sys

from triton import *


def emulate(ctx, handler):
    # Define a fake stack for each handler
    ctx.setConcreteRegisterValue(ctx.registers.rbp, 0x7fffffff)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, 0x6fffffff)

    pc = handler
    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the ctx instruction
        instruction = Instruction(pc, opcode)

        # Process
        if ctx.processing(instruction) != EXCEPTION.NO_FAULT:
            return

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
        if pc == 0x400CDA:
            # In the handler 0x400C95, we can skip the basic bloc 0x400CE5
            break

    # Each character of the user input is computed in order to obtain an hash.
    # In every handler this hash must be equal to 0x3E8. EAX contains the result
    # of the hash computation.
    success = ctx.getRegisterAst(ctx.registers.eax)
    model   = ctx.getModel(success == 0x3E8)
    for k, v in list(sorted(model.items())):
        value = v.getValue()
        ctx.setConcreteVariableValue(ctx.getSymbolicVariable(k), value)
        print('[+] Symbolic variable %02d = %02x (%c)' %(k, value, chr(value)))

    return


# Load segments into triton.
def loadBinary(path):
    import lief
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        print('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))
    return


# This function returns 0 if we found the good flag otherwise
# it returns -1. It's mainly used for our unittest system.
def solution(ctx):
    flag = ctx.getConcreteMemoryAreaValue(0x6040C0, 22)
    if flag == b'Did_you_like_signals?\x00':
        return 0
    return -1


if __name__ == '__main__':
    # Define the target architecture
    ctx = TritonContext(ARCH.X86_64)

    # Define symbolic optimizations
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    # Load the binary
    loadBinary(os.path.join(os.path.dirname(__file__), 'stage3.bin'))

    # Symbolize user inputs (22 bytes)
    #
    #                        User input           Handler handling each user character
    # +--------------------+--------------------+-------------------------------------
    # .bss:00000000006040C0 byte_6040C0         ; DATA XREF: sub_4007FD+B↑r
    # .bss:00000000006040C1 byte_6040C1         ; DATA XREF: sub_40085C+12↑r
    # .bss:00000000006040C2 byte_6040C2         ; DATA XREF: sub_4008C7+B↑r
    # .bss:00000000006040C3 byte_6040C3         ; DATA XREF: sub_400926+B↑r
    # .bss:00000000006040C4 byte_6040C4         ; DATA XREF: sub_40098A+B↑r
    # .bss:00000000006040C5 byte_6040C5         ; DATA XREF: sub_4009E8+B↑r
    # .bss:00000000006040C6 byte_6040C6         ; DATA XREF: sub_400A4C+B↑r
    # .bss:00000000006040C7 byte_6040C7         ; DATA XREF: sub_400AB0+B↑r
    # .bss:00000000006040C8 byte_6040C8         ; DATA XREF: sub_400B14+B↑r
    # .bss:00000000006040C9 byte_6040C9         ; DATA XREF: sub_400B73+B↑r
    # .bss:00000000006040CA byte_6040CA         ; DATA XREF: sub_400BD7+B↑r
    # .bss:00000000006040CB byte_6040CB         ; DATA XREF: sub_400C36+B↑r
    # .bss:00000000006040CC byte_6040CC         ; DATA XREF: sub_400C95+B↑r
    # .bss:00000000006040CD byte_6040CD         ; DATA XREF: sub_400D0C+B↑r
    # .bss:00000000006040CE byte_6040CE         ; DATA XREF: sub_400D6B+B↑r
    # .bss:00000000006040CF byte_6040CF         ; DATA XREF: sub_400DCF+B↑r
    # .bss:00000000006040D0 byte_6040D0         ; DATA XREF: sub_400E2E+B↑r
    # .bss:00000000006040D1 byte_6040D1         ; DATA XREF: sub_400E8D+B↑r
    # .bss:00000000006040D2 byte_6040D2         ; DATA XREF: sub_400EEC+B↑r
    # .bss:00000000006040D3 byte_6040D3         ; DATA XREF: sub_400F4B+B↑r
    # .bss:00000000006040D4 byte_6040D4         ; DATA XREF: sub_400FAA+B↑r
    # .bss:00000000006040D5 byte_6040D5         ; DATA XREF: sub_40100E+E↑r
    for index in range(22):
        ctx.symbolizeMemory(MemoryAccess(0x6040C0 + index, CPUSIZE.BYTE))

    # In this challenge, every character of the user input is computed into a
    # signal handler. If a character N is good, the current handler calls the
    # the handler in charge of verifying the character N + 1. Handlers have no
    # dependence between each oter. At the end of each handler execution we can
    # ask for a model to solve the current character. Below the list of all
    # handlers where each handler verify a character.
    print('Starting the emulation of all signal handler')
    handlers = [
        0x4007FD, 0x40085C, 0x4008C7, 0x400926, 0x40098A, 0x4009E8,
        0x400A4C, 0x400AB0, 0x400B14, 0x400B73, 0x400BD7, 0x400C36,
        0x400C95, 0x400D0C, 0x400D6B, 0x400DCF, 0x400E2E, 0x400E8D,
        0x400EEC, 0x400F4B, 0x400FAA, 0x40100E
    ]
    for handler in handlers:
        emulate(ctx, handler)

    sys.exit(solution(ctx))
