#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./src/examples/python/symbolic_emulation_2.py
##  Curr ip: 40056d: push rbp
##  Next ip: 0x40056eL
##
##  Curr ip: 40056e: mov rax, 0x41424344
##  Next ip: 0x400575L
##
##  Curr ip: 400575: call rax
##  Next ip: 0x41424344L
##
##  Curr ip: 41424344: xor rbx, rbx
##  Next ip: 0x41424347L
##
##  Curr ip: 41424347: ret
##  Next ip: 0x400577L
##
##  Curr ip: 400577: ret
##  Next ip: 0x99999999L
##

import  sys

from triton     import *
from triton.ast import *


function = {
  0x40056d:   "\x55",                         #   push    rbp
  0x40056e:   "\x48\xC7\xC0\x44\x43\x42\x41", #   mov     rax, 0x41424344
  0x400575:   "\xFF\xD0",                     #   call    rax
  0x400577:   "\xc3",                         #   ret
  0x41424344: "\x48\x31\xDB",                 #   xor     rbx, rbx
  0x41424347: "\xc3",                         #   ret
}



# This function emulates the code.
def run(ip):
    while ip in function:
        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(function[ip])

        # Setup Address
        inst.setAddress(ip)

        # Process everything
        processing(inst)

        # Display instruction
        print 'Curr ip:', inst

        # Next instruction
        ip = buildSymbolicRegister(REG.RIP).evaluate()
        print 'Next ip:', hex(ip)
        print
    return



# This function initializes the context memory.
def initContext():
    setConcreteRegisterValue(Register(REG.RSP, 0x7fffffff))
    setConcreteRegisterValue(Register(REG.RBP, 0x99999999))
    return



if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Symbolic optimization
    enableMode(MODE.ALIGNED_MEMORY, True)

    # Define entry point
    ENTRY = 0x40056d

    # Init context memory
    initContext()

    # Emulate
    run(ENTRY)

    sys.exit(0)

