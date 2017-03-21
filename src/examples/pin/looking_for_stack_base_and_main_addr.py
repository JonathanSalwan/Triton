#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  $ ./build/triton ./src/examples/pin/looking_for_stack_base_and_main_addr.py /usr/bin/id
##  [+] stack base found at 7ffedc52a000
##  [+] main() found at 401900
##  ...
##

from pintool import *
from triton  import *

MAIN_ADDR       = None
STACK_BASE      = None


# This function is looking for the main() function address.
def looking_for_main_addr(instruction):
    global MAIN_ADDR
    if MAIN_ADDR is None and instruction.getType() == OPCODE.CALL:
        # This is the first call into the ___libc_start_main function.
        # Get the main() function address located into RDI.
        MAIN_ADDR = getCurrentRegisterValue(REG.RDI)
        print '[+] main() found at %x' %(MAIN_ADDR)
    return


# This function is looking for the stack base address.
def looking_for_stack_base_addr():
    global STACK_BASE
    if STACK_BASE is None:
        STACK_BASE = getCurrentRegisterValue(REG.RSP)
        STACK_BASE &= 0xfffffffffffff000
        print '[+] stack base found at %x' %(STACK_BASE)
    return


def before(instruction):
    looking_for_stack_base_addr()
    looking_for_main_addr(instruction)
    return


if __name__ == '__main__':
    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Callback
    insertCall(before, INSERT_POINT.BEFORE)

    # Run the instrumentation - Never returns
    runProgram()

