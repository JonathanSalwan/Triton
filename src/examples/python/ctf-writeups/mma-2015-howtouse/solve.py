#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2018-11-03
##
##  To solve the challenge we have to execute (in a concrete way) the function
##  fnhowtouse(int) in the howtouse.dll. Calling this function with an index
##  input returns a part of the flag. Calling this function from the index 0
##  to 44 returns the complet flag.
##
##  Output:
##
##  $ time python solve.py
##  [+] Loading 0x10001000 - 0x10001b10
##  [+] Loading 0x10002000 - 0x10002573
##  [+] Loading 0x10003000 - 0x10003364
##  [+] Loading 0x10004000 - 0x100042b0
##  [+] Loading 0x10005000 - 0x1000517e
##  [+] Starting emulation of the function howtouse(0)
##  [+] Starting emulation of the function howtouse(1)
##  [+] Starting emulation of the function howtouse(2)
##  [+] Starting emulation of the function howtouse(3)
##  [+] Starting emulation of the function howtouse(4)
##  [+] Starting emulation of the function howtouse(5)
##  [+] Starting emulation of the function howtouse(6)
##  [+] Starting emulation of the function howtouse(7)
##  [+] Starting emulation of the function howtouse(8)
##  [+] Starting emulation of the function howtouse(9)
##  [+] Starting emulation of the function howtouse(10)
##  [+] Starting emulation of the function howtouse(11)
##  [+] Starting emulation of the function howtouse(12)
##  [+] Starting emulation of the function howtouse(13)
##  [+] Starting emulation of the function howtouse(14)
##  [+] Starting emulation of the function howtouse(15)
##  [+] Starting emulation of the function howtouse(16)
##  [+] Starting emulation of the function howtouse(17)
##  [+] Starting emulation of the function howtouse(18)
##  [+] Starting emulation of the function howtouse(19)
##  [+] Starting emulation of the function howtouse(20)
##  [+] Starting emulation of the function howtouse(21)
##  [+] Starting emulation of the function howtouse(22)
##  [+] Starting emulation of the function howtouse(23)
##  [+] Starting emulation of the function howtouse(24)
##  [+] Starting emulation of the function howtouse(25)
##  [+] Starting emulation of the function howtouse(26)
##  [+] Starting emulation of the function howtouse(27)
##  [+] Starting emulation of the function howtouse(28)
##  [+] Starting emulation of the function howtouse(29)
##  [+] Starting emulation of the function howtouse(30)
##  [+] Starting emulation of the function howtouse(31)
##  [+] Starting emulation of the function howtouse(32)
##  [+] Starting emulation of the function howtouse(33)
##  [+] Starting emulation of the function howtouse(34)
##  [+] Starting emulation of the function howtouse(35)
##  [+] Starting emulation of the function howtouse(36)
##  [+] Starting emulation of the function howtouse(37)
##  [+] Starting emulation of the function howtouse(38)
##  [+] Starting emulation of the function howtouse(39)
##  [+] Starting emulation of the function howtouse(40)
##  [+] Starting emulation of the function howtouse(41)
##  [+] Starting emulation of the function howtouse(42)
##  [+] Starting emulation of the function howtouse(43)
##  [+] Starting emulation of the function howtouse(44)
##  Flag is: MMA{fc7d90ca001fc8712497d88d9ee7efa9e9b32ed8}
##  python solve.py  0.18s user 0.02s system 99% cpu 0.200 total
##

import random
import string
import sys
import lief
import os

from triton import *

TARGET = os.path.join(os.path.dirname(__file__), 'howtouse.dll')
DEBUG  = True

# The debug function
def debug(s):
    if DEBUG: print s

# Memory mapping
BASE_STACK = 0x9fffffff


# Emulate the binary.
def emulate(ctx, pc):
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

        #print instruction

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.eip)
    return


def loadBinary(ctx, binary):
    # Map the binary into the memory
    sections = binary.sections
    for sec in sections:
        size   = sec.virtual_size
        vaddr  = sec.virtual_address + 0x10000000
        debug('[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, sec.content)
    return


def run(ctx, binary, arg):
    # Concretize previous context
    ctx.concretizeAllMemory()
    ctx.concretizeAllRegister()

    # Define a fake stack
    ctx.setConcreteRegisterValue(ctx.registers.ebp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.esp, BASE_STACK)

    ctx.setConcreteMemoryValue(MemoryAccess(BASE_STACK+4, CPUSIZE.DWORD), arg)

    # Let's emulate the binary from the entry point
    debug('[+] Starting emulation of the function howtouse(%d)' %(arg))
    emulate(ctx, 0x10001130)
    return ctx.getConcreteRegisterValue(ctx.registers.eax)


def main():
    # Get a Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.X86)

    # Parse the binary
    binary = lief.parse(TARGET)

    # Load the binary
    loadBinary(ctx, binary)

    # Init and emulate
    flag = str()
    for i in range(45):
        flag += chr(run(ctx, binary, i))

    print 'Flag is: %s' %(flag)
    return not (flag == 'MMA{fc7d90ca001fc8712497d88d9ee7efa9e9b32ed8}')


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
