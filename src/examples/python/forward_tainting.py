#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
## $ python3 forward_tainting.py
## [tainted] 0x40058e: movsx eax, al
## [tainted] 0x400591: sub eax, 1
## [tainted] 0x400594: xor eax, 0x55
## [tainted] 0x400597: mov ecx, eax
## [tainted] 0x4005ae: cmp ecx, eax
## [tainted] 0x4005b0: je 0x4005b9
##

from __future__ import print_function
from triton     import *

import  sys

# A dumb function to emulate.
function = {
  0x40056d: b"\x55",                           #   push    rbp
  0x40056e: b"\x48\x89\xe5",                   #   mov     rbp,rsp
  0x400571: b"\x48\x89\x7d\xe8",               #   mov     QWORD PTR [rbp-0x18],rdi
  0x400575: b"\xc7\x45\xfc\x00\x00\x00\x00",   #   mov     DWORD PTR [rbp-0x4],0x0
  0x40057c: b"\xeb\x3f",                       #   jmp     4005bd <check+0x50>
  0x40057e: b"\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x400581: b"\x48\x63\xd0",                   #   movsxd  rdx,eax
  0x400584: b"\x48\x8b\x45\xe8",               #   mov     rax,QWORD PTR [rbp-0x18]
  0x400588: b"\x48\x01\xd0",                   #   add     rax,rdx
  0x40058b: b"\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x40058e: b"\x0f\xbe\xc0",                   #   movsx   eax,al
  0x400591: b"\x83\xe8\x01",                   #   sub     eax,0x1
  0x400594: b"\x83\xf0\x55",                   #   xor     eax,0x55
  0x400597: b"\x89\xc1",                       #   mov     ecx,eax
  0x400599: b"\x48\x8b\x15\xa0\x0a\x20\x00",   #   mov     rdx,QWORD PTR [rip+0x200aa0]        # 601040 <serial>
  0x4005a0: b"\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x4005a3: b"\x48\x98",                       #   cdqe
  0x4005a5: b"\x48\x01\xd0",                   #   add     rax,rdx
  0x4005a8: b"\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x4005ab: b"\x0f\xbe\xc0",                   #   movsx   eax,al
  0x4005ae: b"\x39\xc1",                       #   cmp     ecx,eax
  0x4005b0: b"\x74\x07",                       #   je      4005b9 <check+0x4c>
  0x4005b2: b"\xb8\x01\x00\x00\x00",           #   mov     eax,0x1
  0x4005b7: b"\xeb\x0f",                       #   jmp     4005c8 <check+0x5b>
  0x4005b9: b"\x83\x45\xfc\x01",               #   add     DWORD PTR [rbp-0x4],0x1
  0x4005bd: b"\x83\x7d\xfc\x04",               #   cmp     DWORD PTR [rbp-0x4],0x4
  0x4005c1: b"\x7e\xbb",                       #   jle     40057e <check+0x11>
  0x4005c3: b"\xb8\x00\x00\x00\x00",           #   mov     eax,0x0
  0x4005c8: b"\x5d",                           #   pop     rbp
  0x4005c9: b"\xc3",                           #   ret
}



if __name__ == '__main__':
    # Triton context
    ctx = TritonContext()

    # Set the architecture
    ctx.setArchitecture(ARCH.X86_64)

    # Symbolic optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    # Define the Python syntax
    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    # Define entry point
    pc = 0x40056d

    # Define our input context
    ctx.setConcreteMemoryValue(0x1000, ord('a'))
    ctx.setConcreteMemoryValue(0x1001, ord('b'))
    ctx.setConcreteMemoryValue(0x1002, ord('c'))
    ctx.setConcreteMemoryValue(0x1003, ord('d'))
    ctx.setConcreteMemoryValue(0x1004, ord('e'))

    # Define the serial pointer
    ctx.setConcreteMemoryValue(0x601040, 0x00)
    ctx.setConcreteMemoryValue(0x601041, 0x00)
    ctx.setConcreteMemoryValue(0x601042, 0x90)

    # Define the serial context
    ctx.setConcreteMemoryValue(0x900000, 0x31)
    ctx.setConcreteMemoryValue(0x900001, 0x3e)
    ctx.setConcreteMemoryValue(0x900002, 0x3d)
    ctx.setConcreteMemoryValue(0x900003, 0x26)
    ctx.setConcreteMemoryValue(0x900004, 0x31)

    # Point rdi on our buffer
    ctx.setConcreteRegisterValue(ctx.registers.rdi, 0x1000)

    # Setup stack
    ctx.setConcreteRegisterValue(ctx.registers.rsp, 0x7fffffff)
    ctx.setConcreteRegisterValue(ctx.registers.rbp, 0x7fffffff)

    # Let's emulate the function
    while pc in function:
        # Build an instruction
        inst = Instruction()

        # Setup opcode
        inst.setOpcode(function[pc])

        # Setup Address
        inst.setAddress(pc)

        # Process the instruction
        ctx.processing(inst)

        # I know that at 0x40058b the user can control eax, so i'm tainting it.
        if inst.getAddress() == 0x40058b:
            ctx.taintRegister(ctx.registers.eax)

        # Print only instructions that are tainted.
        if inst.isTainted():
            print('[tainted] %s' %(str(inst)))

        # Next instruction
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    sys.exit(0)
