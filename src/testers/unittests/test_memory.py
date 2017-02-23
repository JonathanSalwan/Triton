#!/usr/bin/env python2
# coding: utf-8
"""Test memory."""

import unittest

from triton import setArchitecture, isRegisterValid, ARCH, MemoryAccess, OPERAND, REG


class TestMemory(unittest.TestCase):

    """Testing the MemoryAccess class."""

    def setUp(self):
        """Define the architecture and memory access to check."""
        setArchitecture(ARCH.X86_64)
        self.mem = MemoryAccess(0x400f4d3, 8, 0x6162636465666768)

    def test_address(self):
        """Check address data is correct."""
        mem = MemoryAccess(0x1122334455667788, 8, 0x6162636465666768)
        self.assertEqual(mem.getAddress(), 0x1122334455667788)
        self.assertEqual(self.mem.getAddress(), 0x400f4d3)

    def test_bit_size(self):
        """Check bit size of the accessed memory."""
        self.assertEqual(self.mem.getBitSize(), 64)

    def test_size(self):
        """Check size of the accessed memory."""
        self.assertEqual(self.mem.getSize(), 8)

    def test_type(self):
        """Check type of a memory access."""
        self.assertEqual(self.mem.getType(), OPERAND.MEM)

    def test_set_concrete_value(self):
        """Check memory is correctly set."""
        self.mem.setConcreteValue(0x1000)
        self.assertEqual(self.mem.getConcreteValue(), 0x1000)
        self.assertEqual(self.mem.getSize(), 8)

    def test_base_register(self):
        """Check base register modification."""
        self.assertFalse(isRegisterValid(self.mem.getBaseRegister()))
        self.mem.setBaseRegister(REG.RAX)
        self.assertEqual(self.mem.getBaseRegister().getName(), "rax")

    def test_index_register(self):
        """Check index register modification."""
        self.assertFalse(isRegisterValid(self.mem.getIndexRegister()))
        self.mem.setIndexRegister(REG.RCX)
        self.assertEqual(self.mem.getIndexRegister().getName(), "rcx")

    def test_segment_register(self):
        """Check segment register modification."""
        self.assertFalse(isRegisterValid(self.mem.getSegmentRegister()))
        self.mem.setSegmentRegister(REG.FS)
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

