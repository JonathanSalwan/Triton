#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## $ ./src/examples/python/emulation.py
## 400000: movabs rax, 0x4142434445464748
##         #0 = (_ bv4702394921427289928 64) ; MOVABS operation
##         #1 = (_ bv4194314 64) ; Program Counter
##
## 40000a: mov rsi, 8
##         #2 = (_ bv8 64) ; MOV operation
##         #3 = (_ bv4194321 64) ; Program Counter
##
## 400011: mov rdi, 0x10000
##         #4 = (_ bv65536 64) ; MOV operation
##         #5 = (_ bv4194328 64) ; Program Counter
##
## 400018: mov qword ptr [rdi + rsi*2 + 0x1234], rax
##         #6 = ((_ extract 63 56) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #7 = ((_ extract 55 48) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #8 = ((_ extract 47 40) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #9 = ((_ extract 39 32) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #10 = ((_ extract 31 24) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #11 = ((_ extract 23 16) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #12 = ((_ extract 15 8) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #13 = ((_ extract 7 0) ((_ extract 63 0) #0)) ; byte reference - MOV operation
##         #15 = (_ bv4194336 64) ; Program Counter
##
## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
## Instruction : mov qword ptr [rdi + rsi*2 + 0x1234], rax
## Write at    : 0x11244L
## Content     : 0x41424344L
## RAX value   : 0x4142434445464748L
## RSI value   : 0x8L
## RDI value   : 0x10000L



import  sys
from    triton import *


trace = [
    (0x400000, "\x48\xB8\x48\x47\x46\x45\x44\x43\x42\x41"),     # movabs rax, 0x4142434445464748
    (0x40000a, "\x48\xC7\xC6\x08\x00\x00\x00"),                 # mov    rsi, 0x8
    (0x400011, "\x48\xC7\xC7\x00\x00\x01\x00"),                 # mov    rdi, 0x10000
    (0x400018, "\x48\x89\x84\x77\x34\x12\x00\x00"),             # mov    QWORD PTR [rdi+rsi*2+0x1234], rax
]


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Define that we perform emulation
    enableSymbolicEmulation(True)

    for (addr, opcodes) in trace:
        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(opcodes)

        # Setup Address
        inst.setAddress(addr)

        # Process everything
        processing(inst)

        # Display instruction
        print inst

        # Display symbolic expressions
        for expr in inst.getSymbolicExpressions():
            print '\t', expr

        print

    # Display emulated information
    print '~~~~~~~~~~~~~~~~~~~~~~~~~~~'
    write = inst.getOperands()[0].getAddress()
    print 'Instruction :', inst.getDisassembly()
    print 'Write at    :', hex(write)
    print 'Content     :', hex(getMemoryValue(Memory(write+4, CPUSIZE.DWORD)))
    print 'RAX value   :', hex(getRegisterValue(REG.RAX))
    print 'RSI value   :', hex(getRegisterValue(REG.RSI))
    print 'RDI value   :', hex(getRegisterValue(REG.RDI))

    sys.exit(0)

