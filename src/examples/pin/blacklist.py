
from triton  import *
from pintool import *

# Output
#
# $ ./build/triton ./src/examples/pin/blacklist.py ./src/samples/crackmes/crackme_xor a
# 0x4005ca: push rbp
# 0x4005cb: mov rbp, rsp
# 0x4005ce: sub rsp, 0x20
# 0x4005d2: mov dword ptr [rbp-0x14], edi
# 0x4005d5: mov qword ptr [rbp-0x20], rsi
# 0x4005d9: cmp dword ptr [rbp-0x14], 0x2
# 0x4005dd: jz 0x4005e6
# 0x4005e6: mov rax, qword ptr [rbp-0x20]
# 0x4005ea: add rax, 0x8
# 0x4005ee: mov rax, qword ptr [rax]
# 0x4005f1: mov rdi, rax
# 0x4005f4: call 0x40056d
# 0x40056d: push rbp
# 0x40056e: mov rbp, rsp
# 0x400571: mov qword ptr [rbp-0x18], rdi
# 0x400575: mov dword ptr [rbp-0x4], 0x0
# 0x40057c: jmp 0x4005bd
# 0x4005bd: cmp dword ptr [rbp-0x4], 0x4
# 0x4005c1: jle 0x40057e
# 0x40057e: mov eax, dword ptr [rbp-0x4]
# 0x400581: movsxd rdx, eax
# 0x400584: mov rax, qword ptr [rbp-0x18]
# 0x400588: add rax, rdx
# 0x40058b: movzx eax, byte ptr [rax]
# 0x40058e: movsx eax, al
# 0x400591: sub eax, 0x1
# 0x400594: xor eax, 0x55
# 0x400597: mov ecx, eax
# 0x400599: mov rdx, qword ptr [rip+0x200aa0]
# 0x4005a0: mov eax, dword ptr [rbp-0x4]
# 0x4005a3: cdqe
# 0x4005a5: add rax, rdx
# 0x4005a8: movzx eax, byte ptr [rax]
# 0x4005ab: movsx eax, al
# 0x4005ae: cmp ecx, eax
# 0x4005b0: jz 0x4005b9
# 0x4005b2: mov eax, 0x1
# 0x4005b7: jmp 0x4005c8
# 0x4005c8: pop rbp
# 0x4005c9: ret
# 0x4005f9: mov dword ptr [rbp-0x4], eax
# 0x4005fc: cmp dword ptr [rbp-0x4], 0x0
# 0x400600: jnz 0x40060e
# 0x40060e: mov edi, 0x4006ce
# 0x400613: call 0x400450
# 0x400450: jmp qword ptr [rip+0x200bc2]
# 0x400456: push 0x0
# 0x40045b: jmp 0x400440
# loose
# 0x400618: mov eax, dword ptr [rbp-0x4]
# 0x40061b: leave
# $

def mycb(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
    return


if __name__ == '__main__':

    setArchitecture(ARCH.X86_64)

    # libc and ld-linux will be unjited
    setupImageBlacklist(["libc", "ld-linux"])

    startAnalysisFromSymbol('main')
    insertCall(mycb, INSERT_POINT.BEFORE)
    runProgram()

