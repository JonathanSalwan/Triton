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
        # Code from VMProtect
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


    def test_inst5(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        # Code from VMProtect
        block = BasicBlock([
            Instruction(b"\x48\x89\xec"),               # mov rsp, rbp
            Instruction(b"\x40\xc0\xde\xaa"),           # rcr sil, 0xaa
            Instruction(b"\x41\x59"),                   # pop r9
            Instruction(b"\x41\x80\xc4\xb8"),           # add r12b, 0xb8
            Instruction(b"\x41\x5d"),                   # pop r13
            Instruction(b"\x4d\x0f\xa3\xd2"),           # bt r10, r10
            Instruction(b"\x41\x5e"),                   # pop r14
            Instruction(b"\x45\x88\xd4"),               # mov r12b, r10b
            Instruction(b"\x44\x0f\xb7\xc7"),           # movzx r8d, di
            Instruction(b"\x5b"),                       # pop rbx
            Instruction(b"\x41\x5c"),                   # pop r12
            Instruction(b"\x48\xff\xcd"),               # dec rbp
            Instruction(b"\x41\x5a"),                   # pop r10
            Instruction(b"\x58"),                       # pop rax
            Instruction(b"\x41\x80\xf8\xce"),           # cmp r8b, 0xce
            Instruction(b"\x5f"),                       # pop rdi
            Instruction(b"\x45\x10\xd7"),               # adc r15b, r10b
            Instruction(b"\x5a"),                       # pop rdx
            Instruction(b"\xb5\x73"),                   # mov ch, 0x73
            Instruction(b"\xf6\xd5"),                   # not ch
            Instruction(b"\x41\x5b"),                   # pop r11
            Instruction(b"\x66\x41\x81\xc0\xbe\x9b"),   # add r8w, 0x9bbe
            Instruction(b"\x40\xd2\xee"),               # shr sil, cl
            Instruction(b"\xf8"),                       # clc
            Instruction(b"\x59"),                       # pop rcx
            Instruction(b"\x5d"),                       # pop rbp
            Instruction(b"\x66\x41\x0f\xbe\xf6"),       # movsx si, r14b
            Instruction(b"\x40\xd2\xce"),               # ror sil, cl
            Instruction(b"\x41\x58"),                   # pop r8
            Instruction(b"\x41\x5f"),                   # pop r15
            Instruction(b"\x48\x0f\xba\xe6\x0b"),       # bt rsi, 11
            Instruction(b"\x9d"),                       # popfq
            Instruction(b"\x5e"),                       # pop rsi
            Instruction(b"\xc3"),                       # ret
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock, 0x83dbc6)
        self.assertEqual(str(sblock), '0x83dbc6: mov rsp, rbp\n'
                                      '0x83dbc9: pop r9\n'
                                      '0x83dbcb: pop r13\n'
                                      '0x83dbcd: pop r14\n'
                                      '0x83dbcf: pop rbx\n'
                                      '0x83dbd0: pop r12\n'
                                      '0x83dbd2: pop r10\n'
                                      '0x83dbd4: pop rax\n'
                                      '0x83dbd5: pop rdi\n'
                                      '0x83dbd6: pop rdx\n'
                                      '0x83dbd7: pop r11\n'
                                      '0x83dbd9: pop rcx\n'
                                      '0x83dbda: pop rbp\n'
                                      '0x83dbdb: pop r8\n'
                                      '0x83dbdd: pop r15\n'
                                      '0x83dbdf: popfq\n'
                                      '0x83dbe0: pop rsi\n'
                                      '0x83dbe1: ret')

    def test_inst6(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        # Code from VMProtect
        block = BasicBlock([
            Instruction(b"\x48\x89\xec"),                   # mov rsp, rbp
            Instruction(b"\x41\x59"),                       # pop r9
            Instruction(b"\x41\x5d"),                       # pop r13
            Instruction(b"\x41\x5e"),                       # pop r14
            Instruction(b"\x66\x45\x85\xe8"),               # test r8w, r13w
            Instruction(b"\x41\x0f\xa3\xe2"),               # bt r10d, esp
            Instruction(b"\x5b"),                           # pop rbx
            Instruction(b"\x66\x98"),                       # cbw
            Instruction(b"\x41\xd2\xe3"),                   # shl r11b, cl
            Instruction(b"\x41\x5c"),                       # pop r12
            Instruction(b"\x41\x5a"),                       # pop r10
            Instruction(b"\x66\x41\x81\xf0\x51\xbe"),       # xor r8w, 0xbe51
            Instruction(b"\xf9"),                           # stc
            Instruction(b"\x58"),                           # pop rax
            Instruction(b"\x66\x41\x0f\xab\xf3"),           # bts r11w, si
            Instruction(b"\x5f"),                           # pop rdi
            Instruction(b"\x41\xf6\xdf"),                   # neg r15b
            Instruction(b"\x66\x45\x0f\xbc\xc4"),           # bsf r8w, r12w
            Instruction(b"\x5a"),                           # pop rdx
            Instruction(b"\x66\x0f\xba\xfd\x0c"),           # btc bp, 12
            Instruction(b"\x45\x09\xd3"),                   # or r11d, r10d
            Instruction(b"\x41\x5b"),                       # pop r11
            Instruction(b"\x81\xc6\x83\x0f\x7f\xff"),       # add esi, 0xff7f0f83
            Instruction(b"\x48\x81\xdd\x6d\x28\xe7\x7d"),   # sbb rbp, 0x7de7286d
            Instruction(b"\x59"),                           # pop rcx
            Instruction(b"\x5d"),                           # pop rbp
            Instruction(b"\x66\x45\x0f\x46\xc5"),           # cmovbe r8w, r13w
            Instruction(b"\x66\x41\xff\xc8"),               # dec r8w
            Instruction(b"\x66\x45\x0f\xbe\xfd"),           # movsx r15w, r13b
            Instruction(b"\x41\x58"),                       # pop r8
            Instruction(b"\x40\xd2\xee"),                   # shr sil, cl
            Instruction(b"\x40\x0f\x9b\xc6"),               # setnp sil
            Instruction(b"\x41\x5f"),                       # pop r15
            Instruction(b"\x49\x0f\xbf\xf6"),               # movsx rsi, r14w
            Instruction(b"\xf8"),                           # clc
            Instruction(b"\x9d"),                           # popfq
            Instruction(b"\x40\x0f\x90\xc6"),               # seto sil
            Instruction(b"\x49\x0f\xb7\xf1"),               # movzx rsi, r9w
            Instruction(b"\x5e"),                           # pop rsi
            Instruction(b"\xc3"),                           # ret
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock, 0x10000)
        self.assertEqual(str(sblock), '0x10000: mov rsp, rbp\n'
                                      '0x10003: pop r9\n'
                                      '0x10005: pop r13\n'
                                      '0x10007: pop r14\n'
                                      '0x10009: pop rbx\n'
                                      '0x1000a: pop r12\n'
                                      '0x1000c: pop r10\n'
                                      '0x1000e: pop rax\n'
                                      '0x1000f: pop rdi\n'
                                      '0x10010: pop rdx\n'
                                      '0x10011: pop r11\n'
                                      '0x10013: pop rcx\n'
                                      '0x10014: pop rbp\n'
                                      '0x10015: pop r8\n'
                                      '0x10017: pop r15\n'
                                      '0x10019: popfq\n'
                                      '0x1001a: pop rsi\n'
                                      '0x1001b: ret')


    def test_inst7(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        # Code from VMProtect
        block = BasicBlock([
            Instruction(b"\x48\x89\xec"),                   # 0x10000: mov rsp, rbp
            Instruction(b"\x41\x59"),                       # 0x10003: pop r9
            Instruction(b"\x41\x5d"),                       # 0x10005: pop r13
            Instruction(b"\x41\x5e"),                       # 0x10007: pop r14
            Instruction(b"\x66\x45\x85\xe8"),               # 0x10009: test r8w, r13w
            Instruction(b"\x41\x0f\xa3\xe2"),               # 0x1000d: bt r10d, esp
            Instruction(b"\x5b"),                           # 0x10011: pop rbx
            Instruction(b"\x66\x98"),                       # 0x10012: cbw
            Instruction(b"\x41\xd2\xe3"),                   # 0x10014: shl r11b, cl
            Instruction(b"\x41\x5c"),                       # 0x10017: pop r12
            Instruction(b"\x41\x5a"),                       # 0x10019: pop r10
            Instruction(b"\x66\x41\x81\xf0\x51\xbe"),       # 0x1001b: xor r8w, 0xbe51
            Instruction(b"\xf9"),                           # 0x10021: stc
            Instruction(b"\x58"),                           # 0x10022: pop rax
            Instruction(b"\x66\x41\x0f\xab\xf3"),           # 0x10023: bts r11w, si
            Instruction(b"\x5f"),                           # 0x10028: pop rdi
            Instruction(b"\x41\xf6\xdf"),                   # 0x10029: neg r15b
            Instruction(b"\x66\x45\x0f\xbc\xc4"),           # 0x1002c: bsf r8w, r12w
            Instruction(b"\x5a"),                           # 0x10031: pop rdx
            Instruction(b"\x66\x0f\xba\xfd\x0c"),           # 0x10032: btc bp, 0xc
            Instruction(b"\x45\x09\xd3"),                   # 0x10037: or r11d, r10d
            Instruction(b"\x41\x5b"),                       # 0x1003a: pop r11
            Instruction(b"\x81\xc6\x83\x0f\x7f\xff"),       # 0x1003c: add esi, 0xff7f0f83
            Instruction(b"\x48\x81\xdd\x6d\x28\xe7\x7d"),   # 0x10042: sbb rbp, 0x7de7286d
            Instruction(b"\x59"),                           # 0x10049: pop rcx
            Instruction(b"\x5d"),                           # 0x1004a: pop rbp
            Instruction(b"\x66\x45\x0f\x46\xc5"),           # 0x1004b: cmovbe r8w, r13w
            Instruction(b"\x66\x41\xff\xc8"),               # 0x10050: dec r8w
            Instruction(b"\x66\x45\x0f\xbe\xfd"),           # 0x10054: movsx r15w, r13b
            Instruction(b"\x41\x58"),                       # 0x10059: pop r8
            Instruction(b"\x40\xd2\xee"),                   # 0x1005b: shr sil, cl
            Instruction(b"\x40\x0f\x9b\xc6"),               # 0x1005e: setnp sil
            Instruction(b"\x41\x5f"),                       # 0x10062: pop r15
            Instruction(b"\x49\x0f\xbf\xf6"),               # 0x10064: movsx rsi, r14w
            Instruction(b"\xf8"),                           # 0x10068: clc
            Instruction(b"\x9d"),                           # 0x10069: popfq
            Instruction(b"\x40\x0f\x90\xc6"),               # 0x1006a: seto sil
            Instruction(b"\x49\x0f\xb7\xf1"),               # 0x1006e: movzx rsi, r9w
            Instruction(b"\x5e"),                           # 0x10072: pop rsi
            Instruction(b"\xc3"),                           # 0x10073: ret
        ])

        self.ctx.disassembly(block, 0x10000)
        sblock = self.ctx.simplify(block, padding=True)
        self.ctx.disassembly(sblock, 0x10000)
        self.assertEqual(block.getFirstAddress(), sblock.getFirstAddress())
        self.assertEqual(block.getLastAddress(), sblock.getLastAddress())
        self.assertEqual(str(sblock), '0x10000: mov rsp, rbp\n'
                                      '0x10003: pop r9\n'
                                      '0x10005: pop r13\n'
                                      '0x10007: pop r14\n'
                                      '0x10009: nop\n'
                                      '0x1000a: nop\n'
                                      '0x1000b: nop\n'
                                      '0x1000c: nop\n'
                                      '0x1000d: nop\n'
                                      '0x1000e: nop\n'
                                      '0x1000f: nop\n'
                                      '0x10010: nop\n'
                                      '0x10011: pop rbx\n'
                                      '0x10012: nop\n'
                                      '0x10013: nop\n'
                                      '0x10014: nop\n'
                                      '0x10015: nop\n'
                                      '0x10016: nop\n'
                                      '0x10017: pop r12\n'
                                      '0x10019: pop r10\n'
                                      '0x1001b: nop\n'
                                      '0x1001c: nop\n'
                                      '0x1001d: nop\n'
                                      '0x1001e: nop\n'
                                      '0x1001f: nop\n'
                                      '0x10020: nop\n'
                                      '0x10021: nop\n'
                                      '0x10022: pop rax\n'
                                      '0x10023: nop\n'
                                      '0x10024: nop\n'
                                      '0x10025: nop\n'
                                      '0x10026: nop\n'
                                      '0x10027: nop\n'
                                      '0x10028: pop rdi\n'
                                      '0x10029: nop\n'
                                      '0x1002a: nop\n'
                                      '0x1002b: nop\n'
                                      '0x1002c: nop\n'
                                      '0x1002d: nop\n'
                                      '0x1002e: nop\n'
                                      '0x1002f: nop\n'
                                      '0x10030: nop\n'
                                      '0x10031: pop rdx\n'
                                      '0x10032: nop\n'
                                      '0x10033: nop\n'
                                      '0x10034: nop\n'
                                      '0x10035: nop\n'
                                      '0x10036: nop\n'
                                      '0x10037: nop\n'
                                      '0x10038: nop\n'
                                      '0x10039: nop\n'
                                      '0x1003a: pop r11\n'
                                      '0x1003c: nop\n'
                                      '0x1003d: nop\n'
                                      '0x1003e: nop\n'
                                      '0x1003f: nop\n'
                                      '0x10040: nop\n'
                                      '0x10041: nop\n'
                                      '0x10042: nop\n'
                                      '0x10043: nop\n'
                                      '0x10044: nop\n'
                                      '0x10045: nop\n'
                                      '0x10046: nop\n'
                                      '0x10047: nop\n'
                                      '0x10048: nop\n'
                                      '0x10049: pop rcx\n'
                                      '0x1004a: pop rbp\n'
                                      '0x1004b: nop\n'
                                      '0x1004c: nop\n'
                                      '0x1004d: nop\n'
                                      '0x1004e: nop\n'
                                      '0x1004f: nop\n'
                                      '0x10050: nop\n'
                                      '0x10051: nop\n'
                                      '0x10052: nop\n'
                                      '0x10053: nop\n'
                                      '0x10054: nop\n'
                                      '0x10055: nop\n'
                                      '0x10056: nop\n'
                                      '0x10057: nop\n'
                                      '0x10058: nop\n'
                                      '0x10059: pop r8\n'
                                      '0x1005b: nop\n'
                                      '0x1005c: nop\n'
                                      '0x1005d: nop\n'
                                      '0x1005e: nop\n'
                                      '0x1005f: nop\n'
                                      '0x10060: nop\n'
                                      '0x10061: nop\n'
                                      '0x10062: pop r15\n'
                                      '0x10064: nop\n'
                                      '0x10065: nop\n'
                                      '0x10066: nop\n'
                                      '0x10067: nop\n'
                                      '0x10068: nop\n'
                                      '0x10069: popfq\n'
                                      '0x1006a: nop\n'
                                      '0x1006b: nop\n'
                                      '0x1006c: nop\n'
                                      '0x1006d: nop\n'
                                      '0x1006e: nop\n'
                                      '0x1006f: nop\n'
                                      '0x10070: nop\n'
                                      '0x10071: nop\n'
                                      '0x10072: pop rsi\n'
                                      '0x10073: ret')


    def test_inst8(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x1234)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x9876)
        block = BasicBlock([
	        Instruction(b"\x48\x8B\x14\x2C"),             #  mov rdx, qword ptr [rsp + rbp]
	        Instruction(b"\x48\x81\xEE\x08\x00\x00\x00"), #  sub rsi, 8
	        Instruction(b"\x48\x89\x16"),                 #  mov qword ptr [rsi], rdx
	        Instruction(b"\x41\x51"),                     #  push r9
	        Instruction(b"\x8b\x03"),                     #  mov eax, dword ptr [rbx]
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: mov rdx, qword ptr [rsp + rbp]\n'
                                      '0x4: sub rsi, 8\n'
                                      '0xb: mov qword ptr [rsi], rdx\n'
                                      '0xe: push r9\n'
                                      '0x10: mov eax, dword ptr [rbx]')

    def test_inst9(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        block = BasicBlock([
            Instruction(b"\x48\xc7\xc6\x00\x00\x00\x00"),   # mov rsi, 0
            Instruction(b"\x48\x89\x16"),                   # mov qword ptr [rsi], rdx
            Instruction(b"\x5e"),                           # pop rsi
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: mov rsi, 0\n'
                                      '0x7: mov qword ptr [rsi], rdx\n'
                                      '0xa: pop rsi')

    def test_inst10(self):
        self.ctx.setArchitecture(ARCH.X86_64)
        block = BasicBlock([
            Instruction(b"\x89\x2c\x24"), # mov dword ptr [rsp], ebp
            Instruction(b"\x89\x1c\x24"), # mov dword ptr [rsp], ebx
            Instruction(b"\x89\x04\x24"), # mov dword ptr [rsp], eax
        ])
        self.ctx.disassembly(block)
        sblock = self.ctx.simplify(block)
        self.ctx.disassembly(sblock)
        self.assertEqual(str(sblock), '0x0: mov dword ptr [rsp], eax')
