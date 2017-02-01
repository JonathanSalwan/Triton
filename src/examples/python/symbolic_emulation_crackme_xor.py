#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import  sys

from triton     import *
from triton.ast import *

function = {
                                              #   <serial> function
  0x40056d: "\x55",                           #   push    rbp
  0x40056e: "\x48\x89\xe5",                   #   mov     rbp,rsp
  0x400571: "\x48\x89\x7d\xe8",               #   mov     QWORD PTR [rbp-0x18],rdi
  0x400575: "\xc7\x45\xfc\x00\x00\x00\x00",   #   mov     DWORD PTR [rbp-0x4],0x0
  0x40057c: "\xeb\x3f",                       #   jmp     4005bd <check+0x50>
  0x40057e: "\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x400581: "\x48\x63\xd0",                   #   movsxd  rdx,eax
  0x400584: "\x48\x8b\x45\xe8",               #   mov     rax,QWORD PTR [rbp-0x18]
  0x400588: "\x48\x01\xd0",                   #   add     rax,rdx
  0x40058b: "\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x40058e: "\x0f\xbe\xc0",                   #   movsx   eax,al
  0x400591: "\x83\xe8\x01",                   #   sub     eax,0x1
  0x400594: "\x83\xf0\x55",                   #   xor     eax,0x55
  0x400597: "\x89\xc1",                       #   mov     ecx,eax
  0x400599: "\x48\x8b\x15\xa0\x0a\x20\x00",   #   mov     rdx,QWORD PTR [rip+0x200aa0]        # 601040 <serial>
  0x4005a0: "\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x4005a3: "\x48\x98",                       #   cdqe
  0x4005a5: "\x48\x01\xd0",                   #   add     rax,rdx
  0x4005a8: "\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x4005ab: "\x0f\xbe\xc0",                   #   movsx   eax,al
  0x4005ae: "\x39\xc1",                       #   cmp     ecx,eax
  0x4005b0: "\x74\x07",                       #   je      4005b9 <check+0x4c>
  0x4005b2: "\xb8\x01\x00\x00\x00",           #   mov     eax,0x1
  0x4005b7: "\xeb\x0f",                       #   jmp     4005c8 <check+0x5b>
  0x4005b9: "\x83\x45\xfc\x01",               #   add     DWORD PTR [rbp-0x4],0x1
  0x4005bd: "\x83\x7d\xfc\x04",               #   cmp     DWORD PTR [rbp-0x4],0x4
  0x4005c1: "\x7e\xbb",                       #   jle     40057e <check+0x11>
  0x4005c3: "\xb8\x00\x00\x00\x00",           #   mov     eax,0x0
  0x4005c8: "\x5d",                           #   pop     rbp
  0x4005c9: "\xc3",                           #   ret
}



if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Symbolic optimization
    enableMode(MODE.ALIGNED_MEMORY, True)

    # Define entry point
    pc = 0x40056d

    # Define our input context
    setConcreteMemoryValue(0x1000, ord('e'))
    setConcreteMemoryValue(0x1001, ord('l'))
    setConcreteMemoryValue(0x1002, ord('i'))
    setConcreteMemoryValue(0x1003, ord('t'))
    setConcreteMemoryValue(0x1004, ord('e'))

    # Define the serial pointer
    setConcreteMemoryValue(0x601040, 0x00)
    setConcreteMemoryValue(0x601041, 0x00)
    setConcreteMemoryValue(0x601042, 0x90)

    # Define the serial context
    setConcreteMemoryValue(0x900000, 0x31)
    setConcreteMemoryValue(0x900001, 0x3e)
    setConcreteMemoryValue(0x900002, 0x3d)
    setConcreteMemoryValue(0x900003, 0x26)
    setConcreteMemoryValue(0x900004, 0x31)

    # point rdi on our buffer
    setConcreteRegisterValue(Register(REG.RDI, 0x1000))

    # Setup stack
    setConcreteRegisterValue(Register(REG.RSP, 0x7fffffff))
    setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))

    while pc in function:

        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(function[pc])

        # Setup Address
        inst.setAddress(pc)

        # Process everything
        processing(inst)

        # Display instruction
        print inst

        # Next instruction
        pc = buildSymbolicRegister(REG.RIP).evaluate()

    sys.exit(0)

