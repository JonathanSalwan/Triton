#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2020-05-01
##
##  In this CTF challenge, we totally emulate the context of the basic block
##  in charge of the flag computation.
##
##  Output:
##
##  $ time python solve2.py
##  [+] Good flag: ALEXCTF{W3_L0v3_C_W1th_CL45535}
##  python solve2.py  0.32s user 0.00s system 99% cpu 0.322 total
##

from __future__ import print_function
from triton     import *

import os
import sys


def solution(ctx):
    flag = bytearray(31)
    for k, v in sorted(ctx.getSymbolicVariables().items()):
        flag[k] = ctx.getConcreteVariableValue(v)
    if flag == b'ALEXCTF{W3_L0v3_C_W1th_CL45535}':
        print("[+] Good flag: %s" %(flag.decode('utf-8')))
        return 0
    print("[+] Bad flag :(")
    return -1

if __name__ == '__main__':
    ctx = TritonContext(ARCH.X86_64)

    # Define symbolic optimizations
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

    code = [
        (0x400c4b + 0x0000000000000000, b"\x48\x8d\x45\xa0"),             # lea      rax, [rbp-96]
        (0x400c4b + 0x0000000000000004, b"\x48\x89\xc7"),                 # mov      rdi, rax
        (0x400c4b + 0x0000000000000007, b"\x48\x8b\x07"),                 # mov      rax, [rdi]
        (0x400c4b + 0x000000000000000a, b"\x0f\xb6\x10"),                 # movzx    edx, byte ptr [rax]
        (0x400c4b + 0x000000000000000d, b"\x48\x8b\x0d\x3f\x14\x20\x00"), # mov      rcx, qword ptr [rip + 0x20143f] # 0x60209e
        (0x400c4b + 0x0000000000000014, b"\x8b\x45\xec"),                 # mov      eax, [rbp-20]
        (0x400c4b + 0x0000000000000017, b"\x48\x98"),                     # cdqe
        (0x400c4b + 0x0000000000000019, b"\x8b\x04\x85\xc0\x20\x60\x00"), # mov      eax, dword ptr [rax*4 + 0x6020c0]
        (0x400c4b + 0x0000000000000020, b"\x48\x98"),                     # cdqe
        (0x400c4b + 0x0000000000000022, b"\x48\x01\xc8"),                 # add      rax, rcx
        (0x400c4b + 0x0000000000000025, b"\x0f\xb6\x00"),                 # movzx    eax, byte ptr [rax]
        (0x400c4b + 0x0000000000000028, b"\x38\xc2"),                     # cmp      dl, al
        (0x400c4b + 0x000000000000002a, b"\x0f\x95\xc0"),                 # setnz    al
        (0x400c4b + 0x000000000000002d, b"\x84\xc0"),                     # test     al, al
    ]

    key1 =  b"\x24\x00\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x36\x00\x00\x00"
    key1 += b"\x65\x00\x00\x00\x07\x00\x00\x00\x27\x00\x00\x00\x26\x00\x00\x00"
    key1 += b"\x2D\x00\x00\x00\x01\x00\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00"
    key1 += b"\x0D\x00\x00\x00\x56\x00\x00\x00\x01\x00\x00\x00\x03\x00\x00\x00"
    key1 += b"\x65\x00\x00\x00\x03\x00\x00\x00\x2D\x00\x00\x00\x16\x00\x00\x00"
    key1 += b"\x02\x00\x00\x00\x15\x00\x00\x00\x03\x00\x00\x00\x65\x00\x00\x00"
    key1 += b"\x00\x00\x00\x00\x29\x00\x00\x00\x44\x00\x00\x00\x44\x00\x00\x00"
    key1 += b"\x01\x00\x00\x00\x44\x00\x00\x00\x2B\x00\x00\x00"

    key2 = b"L3t_ME_T3ll_Y0u_S0m3th1ng_1mp0rtant_A_{FL4G}_W0nt_b3_3X4ctly_th4t_345y_t0_c4ptur3_H0wev3r_1T_w1ll_b3_C00l_1F_Y0u_g0t_1t\x00"

    # 0x6020c0: Key1
    # 0x001000: Key2
    # 0x002000: User input
    ctx.setConcreteMemoryAreaValue(0x6020c0, key1)
    ctx.setConcreteMemoryAreaValue(0x001000, key2)
    for i in range(31):
        ctx.setConcreteMemoryValue(MemoryAccess(0x002000 + i, CPUSIZE.BYTE), 0x61)
        ctx.symbolizeMemory(MemoryAccess(0x002000 + i, CPUSIZE.BYTE))

    # Context register
    rbp = 0x7fffffffe460
    ctx.setConcreteRegisterValue(ctx.registers.rbp, rbp)
    ctx.setConcreteRegisterValue(ctx.registers.rip, 0x400c4b)

    ctx.setConcreteMemoryValue(MemoryAccess(0x60209e, CPUSIZE.QWORD), 0x001000)
    ctx.setConcreteMemoryValue(MemoryAccess(rbp - 96, CPUSIZE.QWORD), 0x002000)
    ctx.setConcreteMemoryValue(MemoryAccess(rbp - 20, CPUSIZE.DWORD), 0)

    # iterate 31 times on the basic block
    for count in range(31):

        # The basic block in charge of the flag computation
        for addr, op in code:
            instruction = Instruction(addr, op)
            ctx.processing(instruction)
            #if instruction.isSymbolized():
            #    print("\033[92m" + str(instruction) + "\033[0m")
            #else:
            #    print(instruction)

        # Solve each character of the flag
        zf  = ctx.getRegisterAst(ctx.registers.zf)
        ast = ctx.getAstContext()
        ctx.pushPathConstraint(zf == 1)
        mod = ctx.getModel(ctx.getPathPredicate())
        if not mod:
            print('[-] Failed')
            sys.exit(-1)

        for k,v in sorted(mod.items()):
           ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())

        # Incremente pointer and counter
        ctx.setConcreteMemoryValue(MemoryAccess(rbp - 20, CPUSIZE.DWORD), count + 1)
        ctx.setConcreteMemoryValue(MemoryAccess(rbp - 96, CPUSIZE.DWORD), 0x002000 + count + 1)

    sys.exit(solution(ctx))
