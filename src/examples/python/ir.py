#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output
##
##  $ python ir.py
##  400000: mov rax, qword ptr [rip + 0x13b8]
##          ref!0 = (concat ((_ extract 7 0) (_ bv0 8)) ((_ extract 7 0) (_ bv49 8)) ((_ extract 7 0) (_ bv0 8)) ((_ extract 7 0) (_ bv50 8)) ((_ extract 7 0) (_ bv0 8)) ((_ extract 7 0) (_ bv51 8)) ((_ extract 7 0) (_ bv0 8)) ((_ extract 7 0) (_ bv52 8))) ; MOV operation
##          ref!1 = (_ bv4194311 64) ; Program Counter
##
##  400007: lea rsi, qword ptr [rbx + rax*8]
##          ref!2 = (bvadd (_ bv0 64) (bvadd (_ bv67890 64) (bvmul ((_ extract 63 0) ref!0) (_ bv8 64)))) ; LEA operation
##          ref!3 = (_ bv4194315 64) ; Program Counter
##
##  40000b: lea rsi, dword ptr [ebx + eax*8 + 0xa]
##          ref!4 = ((_ zero_extend 32) (bvadd (_ bv10 32) (bvadd (_ bv67890 32) (bvmul ((_ extract 31 0) ref!0) (_ bv8 32))))) ; LEA operation
##          ref!5 = (_ bv4194321 64) ; Program Counter
##
##  400011: pmovmskb edx, xmm1
##          ref!6 = ((_ zero_extend 32) ((_ zero_extend 16) (concat ((_ extract 127 127) (_ bv0 128)) ((_ extract 119 119) (_ bv0 128)) ((_ extract 111 111) (_ bv0 128)) ((_ extract 103 103) (_ bv0 128)) ((_ extract 95 95) (_ bv0 128)) ((_ extract 87 87) (_ bv0 128)) ((_ extract 79 79) (_ bv0 128)) ((_ extract 71 71) (_ bv0 128)) ((_ extract 63 63) (_ bv0 128)) ((_ extract 55 55) (_ bv0 128)) ((_ extract 47 47) (_ bv0 128)) ((_ extract 39 39) (_ bv0 128)) ((_ extract 31 31) (_ bv0 128)) ((_ extract 23 23) (_ bv0 128)) ((_ extract 15 15) (_ bv0 128)) ((_ extract 7 7) (_ bv0 128))))) ; PMOVMSKB operation
##          ref!7 = (_ bv4194325 64) ; Program Counter
##
##  400015: mov eax, edx
##          ref!8 = ((_ zero_extend 32) ((_ extract 31 0) ref!6)) ; MOV operation
##          ref!9 = (_ bv4194327 64) ; Program Counter
##
##  400017: xor ah, 0x99
##          ref!10 = (concat ((_ extract 63 16) ((_ extract 63 0) ref!8)) (concat (bvxor ((_ extract 15 8) ref!8) (_ bv153 8)) ((_ extract 7 0) ((_ extract 63 0) ref!8)))) ; XOR operation
##          ref!11 = (_ bv0 1) ; Clears carry flag
##          ref!12 = (_ bv0 1) ; Clears overflow flag
##          ref!13 = (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 15 8) ref!10) (_ bv7 8)))) ; Parity flag
##          ref!14 = ((_ extract 15 15) ref!10) ; Sign flag
##          ref!15 = (ite (= ((_ extract 15 8) ref!10) (_ bv0 8)) (_ bv1 1) (_ bv0 1)) ; Zero flag
##          ref!16 = (_ bv4194330 64) ; Program Counter
##

import  sys
from    triton import *


code = [
    (0x400000, "\x48\x8b\x05\xb8\x13\x00\x00"), # mov        rax, QWORD PTR [rip+0x13b8]
    (0x400007, "\x48\x8d\x34\xc3"),             # lea        rsi, [rbx+rax*8]
    (0x40000b, "\x67\x48\x8D\x74\xC3\x0A"),     # lea        rsi, [ebx+eax*8+0xa]
    (0x400011, "\x66\x0F\xD7\xD1"),             # pmovmskb   edx, xmm1
    (0x400015, "\x89\xd0"),                     # mov        eax, edx
    (0x400017, "\x80\xf4\x99"),                 # xor        ah, 0x99
    (0x40001a, "\xC5\xFD\x6F\xCA"),             # vmovdqa    ymm1, ymm2
]



if __name__ == '__main__':

    #Set the arch
    setArchitecture(ARCH.X86_64)

    for (addr, opcodes) in code:
        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(opcodes)

        # Setup Address
        inst.setAddress(addr)

        # optional - Update register state
        inst.updateContext(Register(REG.RAX,  12345));
        inst.updateContext(Register(REG.RBX,  67890));

        # optional - Add memory access <addr, size, content>
        inst.updateContext(MemoryAccess(0x66666666, 8, 0x31003200330034));

        # Process everything
        processing(inst)

        # Display instruction
        print inst

        # Display symbolic expressions
        for expr in inst.getSymbolicExpressions():
            print '\t', expr

        print

    sys.exit(0)

