#!/usr/bin/env python3
# coding: utf-8

import unittest

from triton import *


class TestExclusiveMemoryAccess(unittest.TestCase):

    """Testing exclusive memory access on AArch64."""

    def setUp(self):
        """Define the arch."""
        self.ctx  = TritonContext(ARCH.AARCH64)
        self.data = b"\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc\xdd\xee\xff"

        self.ctx.setConcreteMemoryAreaValue(0x2000, self.data)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1234567890abcdef)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x9, 0xcccccccccccccccc)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0x2000)

    def test_exclusive_memory_access1(self):
        self.ctx.processing(Instruction(b"\x20\x7c\x02\xc8")) # stxr w2, x0, [x1]

        # we can not do the store, status must be equal to 1
        w2   = self.ctx.getConcreteRegisterValue(self.ctx.registers.w2)
        data = self.ctx.getConcreteMemoryAreaValue(0x2000, 15)
        self.assertEqual(w2, 1)
        self.assertEqual(data, self.data)

    def test_exclusive_memory_access2(self):
        self.ctx.processing(Instruction(b"\x23\x7c\x5f\xc8")) # ldxr x3, [x1]       ; set x1 as exclusive address
        self.ctx.processing(Instruction(b"\x20\x7c\x02\xc8")) # stxr w2, x0, [x1]   ; store has the exclusive access

        # we can do the store, status must be equal to 0
        w2 = self.ctx.getConcreteRegisterValue(self.ctx.registers.w2)
        data = self.ctx.getConcreteMemoryAreaValue(0x2000, 15)
        self.assertEqual(w2, 0)
        self.assertEqual(data, b"\xef\xcd\xab\x90\x78\x56\x34\x12\x99\xaa\xbb\xcc\xdd\xee\xff")

        self.ctx.processing(Instruction(b"\x29\x7c\x02\xc8")) # stxr w2, x9, [x1]   ; store has no more the exclusive access

        # we can not do the store anymore, status must be equal to 1
        w2   = self.ctx.getConcreteRegisterValue(self.ctx.registers.w2)
        data = self.ctx.getConcreteMemoryAreaValue(0x2000, 15)
        self.assertEqual(w2, 1)
        self.assertEqual(data, b"\xef\xcd\xab\x90\x78\x56\x34\x12\x99\xaa\xbb\xcc\xdd\xee\xff")
