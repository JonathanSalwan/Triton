#!/usr/bin/env python
# coding: utf-8
"""Test Symbolic Optimizations."""

import unittest
from triton import *


class TestSymbolicOptimizations(unittest.TestCase):

    """Testing ALIGNED_MEMORY."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)


    def test_without_optim(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, False)

        self.ctx.processing(Instruction(b"\x48\xc7\xc0\x01\x00\x00\x00")) # mov rax, 1
        self.ctx.processing(Instruction(b"\x48\x89\x03"))                 # mov [rbx], rax
        self.ctx.processing(Instruction(b"\x48\x8b\x0b"))                 # mov rcx, [rbx]

        rcx = self.ctx.getMemoryAst(MemoryAccess(0, CPUSIZE.QWORD))
        self.assertEqual(rcx.getType(), AST_NODE.CONCAT)
        self.assertEqual(rcx.evaluate(), 1)
        return


    def test_with_optim(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)

        self.ctx.processing(Instruction(b"\x48\xc7\xc0\x01\x00\x00\x00")) # mov rax, 1
        self.ctx.processing(Instruction(b"\x48\x89\x03"))                 # mov [rbx], rax
        self.ctx.processing(Instruction(b"\x48\x8b\x0b"))                 # mov rcx, [rbx]

        rcx = self.ctx.getMemoryAst(MemoryAccess(0, CPUSIZE.QWORD))
        self.assertEqual(rcx.getType(), AST_NODE.REFERENCE)
        self.assertEqual(rcx.evaluate(), 1)
        return
