#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./src/examples/python/symbolic_emulation_1.py
##  400000: movabs rax, 0x4142434445464748
##          ref!0 = (_ bv4702394921427289928 64) ; MOVABS operation
##          ref!1 = (_ bv4194314 64) ; Program Counter
##
##  40000a: mov rsi, 8
##          ref!2 = (_ bv8 64) ; MOV operation
##          ref!3 = (_ bv4194321 64) ; Program Counter
##
##  400011: mov rdi, 0x10000
##          ref!4 = (_ bv65536 64) ; MOV operation
##          ref!5 = (_ bv4194328 64) ; Program Counter
##
##  400018: mov qword ptr [rdi + rsi*2 + 0x1234], rax
##          ref!6 = ((_ extract 63 56) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!7 = ((_ extract 55 48) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!8 = ((_ extract 47 40) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!9 = ((_ extract 39 32) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!10 = ((_ extract 31 24) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!11 = ((_ extract 23 16) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!12 = ((_ extract 15 8) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!13 = ((_ extract 7 0) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!15 = (_ bv4194336 64) ; Program Counter
##
##  Display emulated information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  Instruction : mov qword ptr [rdi + rsi*2 + 0x1234], rax
##  Write at    : 0x11244L
##  Content     : 0x41424344L
##  RAX value   : 0x4142434445464748L
##  RSI value   : 0x8L
##  RDI value   : 0x10000L
##
##  Symbolic registers information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  rsi:64 bv[63..0] ref!2 = (_ bv8 64) ; MOV operation
##  rax:64 bv[63..0] ref!0 = (_ bv4702394921427289928 64) ; MOVABS operation
##  rip:64 bv[63..0] ref!15 = (_ bv4194336 64) ; Program Counter
##  rdi:64 bv[63..0] ref!4 = (_ bv65536 64) ; MOV operation
##
##  Symbolic memory information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  0x11244L ref!13 = ((_ extract 7 0) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11245L ref!12 = ((_ extract 15 8) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11246L ref!11 = ((_ extract 23 16) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11247L ref!10 = ((_ extract 31 24) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11248L ref!9 = ((_ extract 39 32) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11249L ref!8 = ((_ extract 47 40) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x1124aL ref!7 = ((_ extract 55 48) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x1124bL ref!6 = ((_ extract 63 56) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##
##  Craft symbolic stuffs
##  ~~~~~~~~~~~~~~~~~~~~~
##  Memory at 0x11248 : (concat ((_ extract 7 0) ref!6) ((_ extract 7 0) ref!7) ((_ extract 7 0) ref!8) ((_ extract 7 0) ref!9))
##  Compute memory    : 0x41424344L
##  Register AH       : ((_ extract 15 8) ref!0)
##  Compute  AH       : 0x47L
##


import  sys
from    triton import *


code = [
    (0x400000, "\x48\xB8\x48\x47\x46\x45\x44\x43\x42\x41"),     # movabs rax, 0x4142434445464748
    (0x40000a, "\x48\xC7\xC6\x08\x00\x00\x00"),                 # mov    rsi, 0x8
    (0x400011, "\x48\xC7\xC7\x00\x00\x01\x00"),                 # mov    rdi, 0x10000
    (0x400018, "\x48\x89\x84\x77\x34\x12\x00\x00"),             # mov    QWORD PTR [rdi+rsi*2+0x1234], rax
]


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    for (addr, opcodes) in code:
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


    print 'Display emulated information'
    print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
    write = inst.getOperands()[0].getAddress()
    print 'Instruction :', inst.getDisassembly()
    print 'Write at    :', hex(write)
    print 'Content     :', hex(getConcreteMemoryValue(MemoryAccess(write+4, CPUSIZE.DWORD)))
    print 'RAX value   :', hex(getConcreteRegisterValue(REG.RAX))
    print 'RSI value   :', hex(getConcreteRegisterValue(REG.RSI))
    print 'RDI value   :', hex(getConcreteRegisterValue(REG.RDI))


    print
    print 'Symbolic registers information'
    print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
    for k, v in getSymbolicRegisters().items():
        print k, v

    print
    print 'Symbolic memory information'
    print '~~~~~~~~~~~~~~~~~~~~~~~~~~~'
    for k, v in getSymbolicMemory().items():
        print hex(k), v

    print
    print 'Craft symbolic stuffs'
    print '~~~~~~~~~~~~~~~~~~~~~'
    ah  = buildSymbolicRegister(REG.AH)
    mem = buildSymbolicMemory(MemoryAccess(0x11248, 4))
    print 'Memory at 0x11248 :', mem
    print 'Compute memory    :', hex(mem.evaluate())
    print 'Register AH       :', ah
    print 'Compute  AH       :', hex(ah.evaluate())

    sys.exit(0)

