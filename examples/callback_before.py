
from triton import *

# Output
#
# $ ./triton ./examples/callback_before.py ./samples/crackmes/crackme_xor a
# TID (0) 0x40056d push rbp
# TID (0) 0x40056e mov rbp, rsp
# TID (0) 0x400571 mov qword ptr [rbp-0x18], rdi
# TID (0) 0x400575 mov dword ptr [rbp-0x4], 0x0
# TID (0) 0x40057c jmp 0x4005bd
# TID (0) 0x4005bd cmp dword ptr [rbp-0x4], 0x4
# TID (0) 0x4005c1 jle 0x40057e
# TID (0) 0x40057e mov eax, dword ptr [rbp-0x4]
# TID (0) 0x400581 movsxd rdx, eax
# TID (0) 0x400584 mov rax, qword ptr [rbp-0x18]
# TID (0) 0x400588 add rax, rdx
# TID (0) 0x40058b movzx eax, byte ptr [rax]
# TID (0) 0x40058e movsx eax, al
# TID (0) 0x400591 sub eax, 0x1
# TID (0) 0x400594 xor eax, 0x55
# TID (0) 0x400597 mov ecx, eax
# TID (0) 0x400599 mov rdx, qword ptr [rip+0x200aa0]
# TID (0) 0x4005a0 mov eax, dword ptr [rbp-0x4]
# TID (0) 0x4005a3 cdqe
# TID (0) 0x4005a5 add rax, rdx
# TID (0) 0x4005a8 movzx eax, byte ptr [rax]
# TID (0) 0x4005ab movsx eax, al
# TID (0) 0x4005ae cmp ecx, eax
# TID (0) 0x4005b0 jz 0x4005b9
# TID (0) 0x4005b2 mov eax, 0x1
# TID (0) 0x4005b7 jmp 0x4005c8
# TID (0) 0x4005c8 pop rbp


def my_callback_before(instruction):
    print 'TID (%d) %#x %s' %(instruction.getThreadId(), instruction.getAddress(), instruction.getDisassembly())


if __name__ == '__main__':
    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Add a callback.
    addCallback(my_callback_before, IDREF.CALLBACK.BEFORE)

    # Run the instrumentation - Never returns
    runProgram()

