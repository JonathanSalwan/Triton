#!/usr/bin/env python3
# coding: utf-8
"""Test Symbolic Array."""

import unittest
from triton import *


class TestSymbolicArray(unittest.TestCase):

    """Testing symbolic array."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setMode(MODE.MEMORY_ARRAY, True)

    def test_1(self):
        code = [
            b"\x48\xc7\xc0\x00\x10\x00\x00", # mov rax, 0x1000
            b"\x48\xc7\xc3\x32\x00\x00\x00", # mov rbx, 0x32
            b"\xc7\x04\x18\xad\xde\x00\x00", # mov dword ptr [rax + rbx], 0xdead
            b"\x48\x81\xf6\xef\xbe\x00\x00", # xor rsi, 0xbeef
            b"\x48\x8b\x0e", # mov rcx, [rsi]
            b"\x48\x81\xf9\xad\xde\x00\x00", # cmp rcx, 0xdead
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for op in code:
            i = Instruction(op)
            self.ctx.processing(i)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.getModel(zf == 1)
        self.assertEqual(m[0].getValue(), 0xaedd)
