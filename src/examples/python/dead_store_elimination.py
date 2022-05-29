#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## VMProtect's junk code sample from https://back.engineering/17/05/2021/
##
## [Original basic block] -----------------------------------------------
## 0x140004149: rcl di, cl
## 0x14000414c: pop rax
## 0x14000414d: shld r11w, bx, 1
## 0x140004153: pop r11
## 0x140004155: and dh, 0xca
## 0x140004158: not di
## 0x14000415b: pop rdi
## 0x14000415c: rol r9w, 0xc
## 0x140004161: stc
## 0x140004162: pop r8
## 0x140004164: cmc
## 0x140004165: clc
## 0x140004166: shl r9w, 0xb
## 0x14000416b: pop rdx
## 0x14000416c: cmp cx, 0xd2eb
## 0x140004171: bt rcx, rsi
## 0x140004175: pop r9
## 0x140004177: and r10w, sp
## 0x14000417b: rcl r10d, 0x10
## 0x14000417f: pop r10
## 0x140004181: btc cx, 0xc
## 0x140004186: bswap r12
## 0x140004189: cmp rax, -0x38828b69
## 0x14000418f: pop r12
## 0x140004191: rol cx, cl
## 0x140004194: cmc
## 0x140004195: btr bp, 1
## 0x14000419a: sar r14w, cl
## 0x14000419e: pop rbp
## 0x14000419f: sub r14w, si
## 0x1400041a3: or si, si
## 0x1400041a6: add esi, eax
## 0x1400041a8: xadd si, cx
## 0x1400041ac: popfq
## 0x1400041ad: setg cl
## 0x1400041b0: setle cl
## 0x1400041b3: movsx r14, al
## 0x1400041b7: pop rcx
## 0x1400041b8: not ecx
## 0x1400041ba: pop rcx
## 0x1400041bb: lea r13, [rax - 0x36d7e613]
## 0x1400041c2: not si
## 0x1400041c5: pop r14
## 0x1400041c7: not si
## 0x1400041ca: movsx r13w, dl
## 0x1400041cf: mov r13d, 0xb7486bb2
## 0x1400041d5: pop rsi
## 0x1400041d6: mov r13w, 0x44ca
## 0x1400041db: lea r13, [rbx + 0x14631131]
## 0x1400041e2: bswap r13d
## 0x1400041e5: pop r13
## 0x1400041e7: ret
## [End of original basic block] ----------------------------------------
##
## [Simplified basic block] ---------------------------------------------
## 0x140004149: pop rax
## 0x14000414a: pop r11
## 0x14000414c: pop rdi
## 0x14000414d: pop r8
## 0x14000414f: pop rdx
## 0x140004150: pop r9
## 0x140004152: pop r10
## 0x140004154: pop r12
## 0x140004156: pop rbp
## 0x140004157: popfq
## 0x140004158: pop rcx
## 0x140004159: pop rcx
## 0x14000415a: pop r14
## 0x14000415c: pop rsi
## 0x14000415d: pop r13
## 0x14000415f: ret
## [End of simplified basic block] --------------------------------------
##

from triton import *

ctx = TritonContext(ARCH.X86_64)
block = BasicBlock([
    Instruction(b"\x66\xd3\xd7"),                    # rcl     di, cl
    Instruction(b"\x58"),                            # pop     rax
    Instruction(b"\x66\x41\x0f\xa4\xdb\x01"),        # shld    r11w, bx, 1
    Instruction(b"\x41\x5b"),                        # pop     r11
    Instruction(b"\x80\xe6\xca"),                    # and     dh, 0CAh
    Instruction(b"\x66\xf7\xd7"),                    # not     di
    Instruction(b"\x5f"),                            # pop     rdi
    Instruction(b"\x66\x41\xc1\xc1\x0c"),            # rol     r9w, 0Ch
    Instruction(b"\xf9"),                            # stc
    Instruction(b"\x41\x58"),                        # pop     r8
    Instruction(b"\xf5"),                            # cmc
    Instruction(b"\xf8"),                            # clc
    Instruction(b"\x66\x41\xc1\xe1\x0b"),            # shl     r9w, 0Bh
    Instruction(b"\x5a"),                            # pop     rdx
    Instruction(b"\x66\x81\xf9\xeb\xd2"),            # cmp     cx, 0D2EBh
    Instruction(b"\x48\x0f\xa3\xf1"),                # bt      rcx, rsi
    Instruction(b"\x41\x59"),                        # pop     r9
    Instruction(b"\x66\x41\x21\xe2"),                # and     r10w, sp
    Instruction(b"\x41\xc1\xd2\x10"),                # rcl     r10d, 10h
    Instruction(b"\x41\x5a"),                        # pop     r10
    Instruction(b"\x66\x0f\xba\xf9\x0c"),            # btc     cx, 0Ch
    Instruction(b"\x49\x0f\xcc"),                    # bswap   r12
    Instruction(b"\x48\x3d\x97\x74\x7d\xc7"),        # cmp     rax, 0FFFFFFFFC77D7497h
    Instruction(b"\x41\x5c"),                        # pop     r12
    Instruction(b"\x66\xd3\xc1"),                    # rol     cx, cl
    Instruction(b"\xf5"),                            # cmc
    Instruction(b"\x66\x0f\xba\xf5\x01"),            # btr     bp, 1
    Instruction(b"\x66\x41\xd3\xfe"),                # sar     r14w, cl
    Instruction(b"\x5d"),                            # pop     rbp
    Instruction(b"\x66\x41\x29\xf6"),                # sub     r14w, si
    Instruction(b"\x66\x09\xf6"),                    # or      si, si
    Instruction(b"\x01\xc6"),                        # add     esi, eax
    Instruction(b"\x66\x0f\xc1\xce"),                # xadd    si, cx
    Instruction(b"\x9d"),                            # popfq
    Instruction(b"\x0f\x9f\xc1"),                    # setnle  cl
    Instruction(b"\x0f\x9e\xc1"),                    # setle   cl
    Instruction(b"\x4c\x0f\xbe\xf0"),                # movsx   r14, al
    Instruction(b"\x59"),                            # pop     rcx
    Instruction(b"\xf7\xd1"),                        # not     ecx
    Instruction(b"\x59"),                            # pop     rcx
    Instruction(b"\x4c\x8d\xa8\xed\x19\x28\xc9"),    # lea     r13, [rax-36D7E613h]
    Instruction(b"\x66\xf7\xd6"),                    # not     si
    Instruction(b"\x41\x5e"),                        # pop     r14
    Instruction(b"\x66\xf7\xd6"),                    # not     si
    Instruction(b"\x66\x44\x0f\xbe\xea"),            # movsx   r13w, dl
    Instruction(b"\x41\xbd\xb2\x6b\x48\xb7"),        # mov     r13d, 0B7486BB2h
    Instruction(b"\x5e"),                            # pop     rsi
    Instruction(b"\x66\x41\xbd\xca\x44"),            # mov     r13w, 44CAh
    Instruction(b"\x4c\x8d\xab\x31\x11\x63\x14"),    # lea     r13, [rbx+14631131h]
    Instruction(b"\x41\x0f\xcd"),                    # bswap   r13d
    Instruction(b"\x41\x5d"),                        # pop     r13
    Instruction(b"\xc3"),                            # ret
])


print('[Original basic block] ----------------------------------------------- ')
ctx.disassembly(block, 0x140004149)
print(block)
print('[End of original basic block] ---------------------------------------- ')

print()

print('[Simplified basic block] --------------------------------------------- ')
sblock = ctx.simplify(block)
ctx.disassembly(sblock, 0x140004149)
print(sblock)
print('[End of simplified basic block] -------------------------------------- ')
