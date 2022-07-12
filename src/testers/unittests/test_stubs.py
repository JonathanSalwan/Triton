#!/usr/bin/env python3
# coding: utf-8
"""Test Stubs."""

import unittest

from triton import *


class TestStubs(unittest.TestCase):
    """Testing stubs."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setConcreteMemoryAreaValue(0x66600000, STUBS.X8664.SYSTEMV.LIBC.code)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x7fffffff0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff0)

    def emulate(self, pc):
        while pc:
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
        return

    def test_strlen(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strlen"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 12)

    def test_strcmp(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x2000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strcmp"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0)
