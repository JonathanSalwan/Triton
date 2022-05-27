#!/usr/bin/env python3
# coding: utf-8
"""Test Dead Store Elimination."""

import unittest
from triton import *

class TestDeadStoreElimination(unittest.TestCase):

    """Testing dead store elimination."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()

    def test_inst1(self):
        self.ctx.setArchitecture(ARCH.X86_64)
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
        self.ctx.disassembly(block, 0x140004149)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock, 0x140004149)
        self.assertEqual(str(sblock), '0x140004149: pop rax\n'
                                      '0x14000414a: pop r11\n'
                                      '0x14000414c: pop rdi\n'
                                      '0x14000414d: pop r8\n'
                                      '0x14000414f: pop rdx\n'
                                      '0x140004150: pop r9\n'
                                      '0x140004152: pop r10\n'
                                      '0x140004154: pop r12\n'
                                      '0x140004156: pop rbp\n'
                                      '0x140004157: popfq\n'
                                      '0x140004158: pop rcx\n'
                                      '0x140004159: pop rcx\n'
                                      '0x14000415a: pop r14\n'
                                      '0x14000415c: pop rsi\n'
                                      '0x14000415d: pop r13\n'
                                      '0x14000415f: ret')

    def test_inst2(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        block = BasicBlock([
            Instruction(b"\x90"), # nop
            Instruction(b"\x90"), # nop
            Instruction(b"\x90"), # nop
            Instruction(b"\xc9"), # leave
            Instruction(b"\xc3")  # ret
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: leave\n'
                                      '0x1: ret')


    def test_inst3(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        block = BasicBlock([
            Instruction(b"\x48\xc7\xc0\x01\x00\x00\x00"),   # mov rax, 1
            Instruction(b"\x48\x31\xdb"),                   # xor rbx, rbx
            Instruction(b"\x48\xff\xc3"),                   # inc rbx
            Instruction(b"\x48\x0f\xaf\xd8"),               # imul rbx, rax
            Instruction(b"\x9d"),                           # popfq
            Instruction(b"\x48\x89\xc3"),                   # mov rbx, rax
            Instruction(b"\xeb\x62"),                       # jmp 0x64
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: mov rax, 1\n'
                                      '0x7: popfq\n'
                                      '0x8: mov rbx, rax\n'
                                      '0xb: jmp 0x6f')

    def test_inst4(self):
        self.ctx.setArchitecture(ARCH.X86)
        block = BasicBlock([
            Instruction(b"\x50"),             # push eax
            Instruction(b"\x9c"),             # pushfd
            Instruction(b"\x31\xc0"),         # xor eax, eax
            Instruction(b"\x0f\x9b\xc0"),     # setpo al
            Instruction(b"\x52"),             # push edx
            Instruction(b"\x31\xc2"),         # xor edx, eax
            Instruction(b"\xc1\xe2\x02"),     # shl edx, 2
            Instruction(b"\x92"),             # xchg eax, edx
            Instruction(b"\x5a"),             # pop edx
            Instruction(b"\x09\xc8"),         # or eax, ecx
            Instruction(b"\x9d"),             # popfd
            Instruction(b"\x58"),             # pop eax
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: push eax\n'
                                      '0x1: pushfd\n'
                                      '0x2: push edx\n'
                                      '0x3: pop edx\n'
                                      '0x4: popfd\n'
                                      '0x5: pop eax')
