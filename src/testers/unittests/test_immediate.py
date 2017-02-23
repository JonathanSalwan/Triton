#!/usr/bin/env python2
# coding: utf-8
"""Test immediate."""

import unittest

from triton import setArchitecture, ARCH, CPUSIZE, Immediate, OPERAND


class TestImmediate8(unittest.TestCase):

    """Testing the Immediate class."""

    def setUp(self):
        """Define the arch and Immediate to test."""
        setArchitecture(ARCH.X86_64)
        self.imm = Immediate(0x12, CPUSIZE.BYTE)

    def test_bit_size(self):
        """Check the bitsize."""
        self.assertEqual(self.imm.getBitSize(), 8)

    def test_size(self):
        """Check the size."""
        self.assertEqual(self.imm.getSize(), 1)

    def test_value(self):
        """Check immediate value with different size."""
        self.assertEqual(self.imm.getValue(), 0x12)

    def test_type(self):
        """Check immadiate type."""
        self.assertEqual(self.imm.getType(), OPERAND.IMM)


class TestImmediate16(unittest.TestCase):

    """Testing the Immediate class."""

    def setUp(self):
        """Define the arch and Immediate to test."""
        setArchitecture(ARCH.X86_64)
        self.imm = Immediate(0x1234, CPUSIZE.WORD)

    def test_bit_size(self):
        """Check the bitsize."""
        self.assertEqual(self.imm.getBitSize(), 16)

    def test_size(self):
        """Check the size."""
        self.assertEqual(self.imm.getSize(), 2)

    def test_value(self):
        """Check immediate value with different size."""
        self.assertEqual(self.imm.getValue(), 0x1234)
        self.imm = Immediate(-4, CPUSIZE.BYTE)
        self.assertEqual(self.imm.getValue(), 0xfc)
        self.imm = Immediate(-4, CPUSIZE.WORD)
        self.assertEqual(self.imm.getValue(), 0xfffc)
        self.imm = Immediate(-4, CPUSIZE.DWORD)
        self.assertEqual(self.imm.getValue(), 0xfffffffc)
        self.imm = Immediate(-4, CPUSIZE.QWORD)
        self.assertEqual(self.imm.getValue(), 0xfffffffffffffffc)

    def test_type(self):
        """Check immadiate type."""
        self.assertEqual(self.imm.getType(), OPERAND.IMM)


class TestImmediate32(unittest.TestCase):

    """Testing the Immediate class."""

    def setUp(self):
        """Define the arch and Immediate to test."""
        setArchitecture(ARCH.X86_64)
        self.imm = Immediate(0x12345678, CPUSIZE.DWORD)

    def test_bit_size(self):
        """Check the bitsize."""
        self.assertEqual(self.imm.getBitSize(), 32)

    def test_size(self):
        """Check the size."""
        self.assertEqual(self.imm.getSize(), 4)

    def test_value(self):
        """Check immediate value with different size."""
        self.assertEqual(self.imm.getValue(), 0x12345678)

    def test_type(self):
        """Check immadiate type."""
        self.assertEqual(self.imm.getType(), OPERAND.IMM)


class TestImmediate64(unittest.TestCase):

    """Testing the Immediate class."""

    def setUp(self):
        """Define the arch and Immediate to test."""
        setArchitecture(ARCH.X86_64)
        self.imm = Immediate(0x0123456789abcdef, CPUSIZE.QWORD)

    def test_bit_size(self):
        """Check the bitsize."""
        self.assertEqual(self.imm.getBitSize(), 64)

    def test_size(self):
        """Check the size."""
        self.assertEqual(self.imm.getSize(), 8)

    def test_value(self):
        """Check immediate value with different size."""
        self.assertEqual(self.imm.getValue(), 0x0123456789abcdef)

    def test_type(self):
        """Check immadiate type."""
        self.assertEqual(self.imm.getType(), OPERAND.IMM)


class TestNegativeImmediate(unittest.TestCase):

    """Testing the Immediate class."""

    def setUp(self):
        setArchitecture(ARCH.X86_64)

    def test_value(self):
        """Check immediate value with different size."""
        self.imm = Immediate(-4, CPUSIZE.BYTE)
        self.assertEqual(self.imm.getValue(), 0xfc)

        self.imm = Immediate(-4, CPUSIZE.WORD)
        self.assertEqual(self.imm.getValue(), 0xfffc)

        self.imm = Immediate(-4, CPUSIZE.DWORD)
        self.assertEqual(self.imm.getValue(), 0xfffffffc)

        self.imm = Immediate(-4, CPUSIZE.QWORD)
        self.assertEqual(self.imm.getValue(), 0xfffffffffffffffc)

        self.imm = Immediate(0x7123456789abcdef, CPUSIZE.QWORD)
        self.assertEqual(self.imm.getValue(), 0x7123456789abcdef)

        self.imm = Immediate(0x8123456789abcdef, CPUSIZE.QWORD)
        self.assertEqual(self.imm.getValue(), 0x8123456789abcdef)

