#!/usr/bin/env python3
# coding: utf-8
"""Test the x86 parity flag expression."""

import unittest

from triton import ARCH, AST_NODE, Instruction, TritonContext


FORMS = [
    (ARCH.X86_64, b"\x48\x01\xd8", "rax", 0),  # add rax, rbx
    (ARCH.X86_64, b"\x00\xdc", "rax", 8),      # add ah, bl
    (ARCH.X86_64, b"\x48\xff\xc0", "rax", 0),  # inc rax
    (ARCH.X86_64, b"\x48\xc1\xe0\x03", "rax", 0),  # shl rax, 3
    (ARCH.X86_64, b"\x48\xc1\xf8\x03", "rax", 0),  # sar rax, 3
    (ARCH.X86, b"\x01\xd8", "eax", 0),         # add eax, ebx
]


class TestX86ParityFlag(unittest.TestCase):

    def test_parity_flag(self):
        for arch, code, dst, low in FORMS:
            for rax, rbx in ((0, 0), (0x1234, 0x0f0f), (0x7f80, 0x81), (0xffffffff, 1), (0x0300, 0x0500)):
                with self.subTest(code=code.hex(), rax=hex(rax), rbx=hex(rbx)):
                    ctx = TritonContext(arch)
                    ctx.setConcreteRegisterValue(getattr(ctx.registers, "eax" if arch == ARCH.X86 else "rax"), rax)
                    ctx.setConcreteRegisterValue(getattr(ctx.registers, "ebx" if arch == ARCH.X86 else "rbx"), rbx)
                    ctx.processing(Instruction(0x1000, code))
                    byte = ctx.getConcreteRegisterValue(getattr(ctx.registers, dst)) >> low & 0xff
                    self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.pf), bin(byte).count("1") % 2 == 0)

                    # The eight bit extractions share one reference to the result.
                    pf = ctx.getSymbolicRegister(ctx.registers.pf).getAst()
                    self.assertEqual(len(ctx.getAstContext().search(pf, AST_NODE.REFERENCE)), 1)


if __name__ == "__main__":
    unittest.main()
