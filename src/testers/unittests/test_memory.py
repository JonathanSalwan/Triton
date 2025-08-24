#!/usr/bin/env python3
# coding: utf-8
"""Test memory."""

import unittest

from triton import *


class TestMemory(unittest.TestCase):

    """Testing the MemoryAccess class."""

    def setUp(self):
        """Define the architecture and memory access to check."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.mem = MemoryAccess(0x400f4d3, 8)

    def test_address(self):
        """Check address data is correct."""
        mem = MemoryAccess(0x1122334455667788, 8)
        self.assertEqual(mem.getAddress(), 0x1122334455667788)

        mem = MemoryAccess(0x400f4d3, 8)
        self.assertEqual(mem.getAddress(), 0x400f4d3)

        mem = MemoryAccess(-1, 8)
        self.assertEqual(mem.getAddress(), 0xffffffffffffffff)

        mem = MemoryAccess(-2, 8)
        self.assertEqual(mem.getAddress(), 0xfffffffffffffffe)

        mem = MemoryAccess(-3, 8)
        self.assertEqual(mem.getAddress(), 0xfffffffffffffffd)

    def test_bit_size(self):
        """Check bit size of the accessed memory."""
        self.assertEqual(self.mem.getBitSize(), 64)

    def test_size(self):
        """Check size of the accessed memory."""
        self.assertEqual(self.mem.getSize(), 8)

    def test_type(self):
        """Check type of a memory access."""
        self.assertEqual(self.mem.getType(), OPERAND.MEM)

    def test_base_register(self):
        """Check base register modification."""
        self.assertFalse(self.ctx.isRegisterValid(self.mem.getBaseRegister()))
        self.mem.setBaseRegister(self.ctx.registers.rax)
        self.assertEqual(self.mem.getBaseRegister().getName(), "rax")

    def test_index_register(self):
        """Check index register modification."""
        self.assertFalse(self.ctx.isRegisterValid(self.mem.getIndexRegister()))
        self.mem.setIndexRegister(self.ctx.registers.rcx)
        self.assertEqual(self.mem.getIndexRegister().getName(), "rcx")

    def test_segment_register(self):
        """Check segment register modification."""
        self.assertFalse(self.ctx.isRegisterValid(self.mem.getSegmentRegister()))
        self.mem.setSegmentRegister(self.ctx.registers.fs)
        self.assertEqual(self.mem.getSegmentRegister().getName(), "fs")

    def test_scale(self):
        """Check scale information."""
        self.assertEqual(self.mem.getScale().getValue(), 0)
        self.assertEqual(self.mem.getScale().getBitSize(), 1)

    def test_displacement(self):
        """Check displacement information."""
        self.assertEqual(self.mem.getDisplacement().getValue(), 0)

    def test_ast_gen(self):
        """Check LeaAst."""
        self.assertIsNone(self.mem.getLeaAst())

    def test_overlaping(self):
        """Check overlaping."""
        self.assertTrue(MemoryAccess(0x1000, 2).isOverlapWith(MemoryAccess(0x1001, 2)))
        self.assertTrue(MemoryAccess(0xfff, 2).isOverlapWith(MemoryAccess(0x1000, 2)))
        self.assertTrue(MemoryAccess(0x1000, 4).isOverlapWith(MemoryAccess(0x1003, 2)))
        self.assertTrue(MemoryAccess(0x1000, 4).isOverlapWith(MemoryAccess(0x1002, 1)))
        self.assertTrue(MemoryAccess(0x1002, 1).isOverlapWith(MemoryAccess(0x1000, 4)))

        self.assertFalse(MemoryAccess(0x1000, 4).isOverlapWith(MemoryAccess(0x1004, 4)))
        self.assertFalse(MemoryAccess(0x1000, 4).isOverlapWith(MemoryAccess(0x10000, 4)))
        self.assertFalse(MemoryAccess(0x10000, 4).isOverlapWith(MemoryAccess(0x1000, 4)))

    def test_initLeaAst(self):
        """Check initLeaAst."""
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0x20)
        self.ctx.symbolizeRegister(self.ctx.registers.rax)
        self.ctx.symbolizeRegister(self.ctx.registers.rbx)
        self.ctx.setConcreteMemoryValue(MemoryAccess(0x1020, CPUSIZE.DWORD), 0xdeadbeef)

        mem = MemoryAccess(0, CPUSIZE.DWORD)
        mem.setBaseRegister(self.ctx.registers.rax)
        mem.setIndexRegister(self.ctx.registers.rbx)
        mem.setScale(Immediate(1, CPUSIZE.DWORD))

        self.ctx.initLeaAst(mem)
        self.assertEqual(mem.getLeaAst().evaluate(), 0x1020)
        self.assertEqual(self.ctx.getConcreteMemoryValue(mem), 0xdeadbeef)
