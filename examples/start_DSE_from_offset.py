
import triton

# Output
#
#  $ ./triton ./examples/start_DSE_from_offset.py ./samples/crackmes/crackme_xor a
#  0x40056d: push rbp
#  0x40056e: mov rbp, rsp
#  0x400571: mov qword ptr [rbp-0x18], rdi
#  0x400575: mov dword ptr [rbp-0x4], 0x0
#  0x40057c: jmp 0x4005bd
#  0x4005bd: cmp dword ptr [rbp-0x4], 0x4
#  0x40057e: mov eax, dword ptr [rbp-0x4]
#  0x400581: movsxd rdx, eax
#  0x400584: mov rax, qword ptr [rbp-0x18]
#  0x400588: add rax, rdx
#  0x40058b: movzx eax, byte ptr [rax]
#  0x40058e: movsx eax, al
#  0x400591: sub eax, 0x1
#  0x400594: xor eax, 0x55
#  0x400597: mov ecx, eax
#  0x400599: mov rdx, qword ptr [rip+0x200aa0]
#  0x4005a0: mov eax, dword ptr [rbp-0x4]
#  0x4005a3: cdqe
#  0x4005a5: add rax, rdx
#  0x4005a8: movzx eax, byte ptr [rax]
#  0x4005ab: movsx eax, al
#  0x4005ae: cmp ecx, eax
#  0x4005b0: jz 0x4005b9
#  0x4005b2: mov eax, 0x1
#  0x4005b7: jmp 0x4005c8
#  0x4005c8: pop rbp
#  loose
#  $


def cafter(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
    return


if __name__ == '__main__':

    # Start the symbolic analysis from the 0x40056d to 0x4005c9
    triton.startAnalysisFromOffset(0x56d)
    triton.stopAnalysisFromOffset(0x5c9)

    triton.addCallback(cafter, triton.IDREF.CALLBACK.AFTER)
    triton.runProgram()

