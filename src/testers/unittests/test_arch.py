#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest
import random

from triton import ARCH, TritonContext


class TestArchitecture(unittest.TestCase):

    """Testing the architectures."""

    def test_modify_arch(self):
        """Check we can change arch at anytime."""
        self.Triton = TritonContext()
        for _ in xrange(10):
            self.Triton.setArchitecture(random.choice((ARCH.X86_64, ARCH.X86)))


class TestX86Arch(unittest.TestCase):

    """Testing the X86 Architecture."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.assertFalse(self.Triton.isArchitectureValid())
        self.Triton.setArchitecture(ARCH.X86)
        self.assertTrue(self.Triton.isArchitectureValid())

    def test_registers(self):
        """Check some register can't be accessed on X86 arch."""
        with self.assertRaises(Exception):
            self.Triton.registers.rax.getName()

        with self.assertRaises(Exception):
            self.Triton.registers.zmm1.getName()

        with self.assertRaises(Exception):
            self.Triton.registers.xmm8.getName()

        with self.assertRaises(Exception):
            self.Triton.registers.xmm15.getName()

        self.assertEqual(self.Triton.registers.xmm7.getName(), "xmm7")

    def test_register_bit_size(self):
        """Check GPR register bit size."""
        self.assertEqual(self.Triton.getRegisterBitSize(), 32)

    def test_register_size(self):
        """Check GPR register size."""
        self.assertEqual(self.Triton.getRegisterSize(), 4)


class TestX8664Arch(unittest.TestCase):

    """Testing the X8664 Architecture."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.assertFalse(self.Triton.isArchitectureValid())
        self.Triton.setArchitecture(ARCH.X86_64)
        self.assertTrue(self.Triton.isArchitectureValid())

    def test_registers(self):
        """Check X86_64 specific registers exists."""
        self.assertEqual(self.Triton.registers.rax.getName(), "rax")
        self.assertEqual(self.Triton.registers.zmm1.getName(), "zmm1")
        self.assertEqual(self.Triton.registers.xmm15.getName(), "xmm15")

    def test_register_bit_size(self):
        """Check GPR register bit size."""
        self.assertEqual(self.Triton.getRegisterBitSize(), 64)

    def test_register_size(self):
        """Check GPR register size."""
        self.assertEqual(self.Triton.getRegisterSize(), 8)
