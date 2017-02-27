#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest
import random

from triton import setArchitecture, ARCH, REG, getRegisterSize, getRegisterBitSize


class TestArchitecture(unittest.TestCase):

    """Testing the architectures."""

    def test_modify_arch(self):
        """Check we can change arch at anytime."""
        for _ in xrange(10):
            setArchitecture(random.choice((ARCH.X86_64, ARCH.X86)))


class TestX86Arch(unittest.TestCase):

    """Testing the X86 Architecture."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86)

    def test_registers(self):
        """Check some register can't be accessed on X86 arch."""
        with self.assertRaises(Exception):
            REG.RAX.getName()

        with self.assertRaises(Exception):
            REG.ZMM1.getName()

        with self.assertRaises(Exception):
            REG.XMM8.getName()

        with self.assertRaises(Exception):
            REG.XMM15.getName()

        self.assertEqual(REG.XMM7.getName(), "xmm7")

    def test_register_bit_size(self):
        """Check GPR register bit size"""
        self.assertEqual(getRegisterBitSize(), 32)

    def test_register_size(self):
        """Check GPR register size"""
        self.assertEqual(getRegisterSize(), 4)


class TestX8664Arch(unittest.TestCase):

    """Testing the X8664 Architecture."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

    def test_registers(self):
        """Check X86_64 specific registers exists."""
        self.assertEqual(REG.RAX.getName(), "rax")
        self.assertEqual(REG.ZMM1.getName(), "zmm1")
        self.assertEqual(REG.XMM15.getName(), "xmm15")

    def test_register_bit_size(self):
        """Check GPR register bit size"""
        self.assertEqual(getRegisterBitSize(), 64)

    def test_register_size(self):
        """Check GPR register size"""
        self.assertEqual(getRegisterSize(), 8)
