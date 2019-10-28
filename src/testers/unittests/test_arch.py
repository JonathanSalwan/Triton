#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest
import random

from triton import ARCH, TritonContext


class TestArchitecture(unittest.TestCase):

    """Testing the architectures."""

    def test_modify_arch1(self):
        """Check we can change arch at anytime."""
        self.ctx = TritonContext()
        for _ in range(10):
            self.ctx.setArchitecture(random.choice((ARCH.X86_64, ARCH.X86, ARCH.AARCH64)))

    def test_modify_arch2(self):
        """Check we can change arch at anytime."""
        for _ in range(10):
            self.ctx = TritonContext(random.choice((ARCH.X86_64, ARCH.X86, ARCH.AARCH64)))


class TestX86Arch(unittest.TestCase):

    """Testing the X86 Architecture."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.assertFalse(self.ctx.isArchitectureValid())
        self.ctx.setArchitecture(ARCH.X86)
        self.assertTrue(self.ctx.isArchitectureValid())

    def test_registers(self):
        """Check some register can't be accessed on X86 arch."""
        with self.assertRaises(Exception):
            self.ctx.registers.rax.getName()

        with self.assertRaises(Exception):
            self.ctx.registers.zmm1.getName()

        with self.assertRaises(Exception):
            self.ctx.registers.xmm8.getName()

        with self.assertRaises(Exception):
            self.ctx.registers.xmm15.getName()

        self.assertEqual(self.ctx.registers.xmm7.getName(), "xmm7")

    def test_register_bit_size(self):
        """Check GPR register bit size."""
        self.assertEqual(self.ctx.getGprBitSize(), 32)

    def test_register_size(self):
        """Check GPR register size."""
        self.assertEqual(self.ctx.getGprSize(), 4)


class TestX8664Arch(unittest.TestCase):

    """Testing the X8664 Architecture."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.assertFalse(self.ctx.isArchitectureValid())
        self.ctx.setArchitecture(ARCH.X86_64)
        self.assertTrue(self.ctx.isArchitectureValid())

    def test_registers(self):
        """Check X86_64 specific registers exists."""
        self.assertEqual(self.ctx.registers.rax.getName(), "rax")
        self.assertEqual(self.ctx.registers.zmm1.getName(), "zmm1")
        self.assertEqual(self.ctx.registers.xmm15.getName(), "xmm15")

    def test_register_bit_size(self):
        """Check GPR register bit size."""
        self.assertEqual(self.ctx.getGprBitSize(), 64)

    def test_register_size(self):
        """Check GPR register size."""
        self.assertEqual(self.ctx.getGprSize(), 8)

class TestAArch64(unittest.TestCase):

    """Testing the AArch64 Architecture."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.assertFalse(self.ctx.isArchitectureValid())
        self.ctx.setArchitecture(ARCH.AARCH64)
        self.assertTrue(self.ctx.isArchitectureValid())

    def test_registers(self):
        """Check AArch64 specific registers exists."""
        self.assertEqual(self.ctx.registers.x0.getName(), "x0")
        self.assertEqual(self.ctx.registers.w1.getName(), "w1")
        self.assertEqual(self.ctx.getParentRegister(self.ctx.registers.w1).getName(), "x1")

    def test_register_bit_size(self):
        """Check GPR register bit size."""
        self.assertEqual(self.ctx.getGprBitSize(), 64)

    def test_register_size(self):
        """Check GPR register size."""
        self.assertEqual(self.ctx.getGprSize(), 8)
