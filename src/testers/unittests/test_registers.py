#!/usr/bin/env python2
# coding: utf-8
"""Test register."""

import unittest

from triton import (ARCH, REG, OPERAND, TritonContext)


class TestRAXRegister(unittest.TestCase):

    """Testing the Register class with RAX."""

    def setUp(self):
        """Define arch and register to check."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.reg = self.Triton.registers.rax

    def test_name(self):
        """Check register name."""
        self.assertEqual(self.reg.getName(), "rax")

    def test_size(self):
        """Check register size."""
        self.assertEqual(self.reg.getSize(), 8)

    def test_bit_size(self):
        """Check register bit size."""
        self.assertEqual(self.reg.getBitSize(), 64)

    def test_parent(self):
        """Check parent register."""
        self.assertEqual(self.Triton.getParentRegister(self.reg).getName(), "rax")

    def test_type(self):
        """Check operand type."""
        self.assertEqual(self.reg.getType(), OPERAND.REG)

    def test_is_valid(self):
        """Check register validity."""
        self.assertTrue(self.Triton.isRegisterValid(self.reg))

    def test_is_flag(self):
        """Check register flag."""
        self.assertFalse(self.Triton.isFlag(self.reg))

    def test_is_register(self):
        """Check register detect."""
        self.assertTrue(self.Triton.isRegister(self.reg))


class TestAHRegister(unittest.TestCase):

    """Testing the Register class with AH."""

    def setUp(self):
        """Define arch and register to check."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.reg = self.Triton.registers.ah

    def test_size(self):
        """Check register size."""
        self.assertEqual(self.reg.getSize(), 1)

    def test_bitvector(self):
        """Check bitvector information."""
        self.assertEqual(self.reg.getBitvector().getHigh(), 15)
        self.assertEqual(self.reg.getBitvector().getLow(), 8)
        self.assertEqual(self.reg.getBitvector().getVectorSize(), 8)

    def test_parent(self):
        """Check parent register on multiple arch."""
        self.assertEqual(self.Triton.getParentRegister(self.reg).getName(), "rax")

        self.Triton.setArchitecture(ARCH.X86)
        self.reg = self.Triton.registers.ah
        self.assertEqual(self.Triton.getParentRegister(self.reg).getName(), "eax")
        self.assertEqual(self.Triton.getParentRegister(self.reg).getBitSize(), 32)


class TestXmmRegister(unittest.TestCase):

    """Testing the Register class with FP/SIMD registers."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

    def test_xmm_on_x86(self):
        """Check xmm on 32 bits arch."""
        self.Triton.setArchitecture(ARCH.X86)
        xmm = self.Triton.registers.xmm1
        self.assertEqual(xmm.getBitSize(), 128)

    def test_ymm(self):
        """Check ymm on 64 bits arch."""
        ymm = self.Triton.registers.ymm1
        self.assertEqual(ymm.getBitSize(), 256)

    def test_zmm(self):
        """Check zmm on 64 bits arch."""
        zmm = self.Triton.registers.zmm2
        self.assertEqual(zmm.getBitSize(), 512)


class TestRegisterValues(unittest.TestCase):

    """Check register values with hierarchies."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

    def test_set_concrete_value(self):
        """Check register value modification."""
        for reg in (REG.X86_64.AH, REG.X86_64.AL):
            # OK
            reg = self.Triton.getRegister(reg)
            self.Triton.setConcreteRegisterValue(reg, 0xff)
            # Not OK
            # TODO : Be more specific on the raise exception type
            with self.assertRaises(Exception):
                self.Triton.setConcreteRegisterValue(reg, 0xff+1)

        reg = self.Triton.registers.zf
        self.Triton.setConcreteRegisterValue(reg, 1)
        with self.assertRaises(Exception):
            self.Triton.setConcreteRegisterValue(reg, 2)

    def test_overlap(self):
        """Check register overlapping."""
        self.assertTrue(self.Triton.registers.ax.isOverlapWith(self.Triton.registers.eax), "overlap with upper")
        self.assertTrue(self.Triton.registers.ax.isOverlapWith(self.Triton.registers.rax), "overlap with parent")
        self.assertTrue(self.Triton.registers.rax.isOverlapWith(self.Triton.registers.ax), "overlap with lower")
        self.assertFalse(self.Triton.registers.ah.isOverlapWith(self.Triton.registers.al))
        self.assertTrue(self.Triton.registers.ah.isOverlapWith(self.Triton.registers.eax))
        self.assertTrue(self.Triton.registers.eax.isOverlapWith(self.Triton.registers.ah))
        self.assertTrue(self.Triton.registers.ax.isOverlapWith(self.Triton.registers.al))
        self.assertTrue(self.Triton.registers.al.isOverlapWith(self.Triton.registers.ax))
        self.assertFalse(self.Triton.registers.eax.isOverlapWith(self.Triton.registers.edx))

