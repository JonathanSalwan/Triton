#!/usr/bin/env python3
# coding: utf-8
"""Test architectures."""

import unittest

from triton import ARCH, TritonContext
from random import randrange


class TestX86ConcreteRegisterValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)
        self.ar = self.ctx.getAllRegisters()
        self.pr = self.ctx.getParentRegisters()

    def test_all_registers(self):
        """Check all registers"""
        self.assertEqual(len(self.ar), 166)

    def test_parent_registers(self):
        """Check parent registers"""
        self.assertEqual(len(self.pr), 129)

    def test_set_get_concrete_value(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.ctx.setConcreteRegisterValue(r, 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Set everything to zero"""
        for r in self.ar:
            self.ctx.setConcreteRegisterValue(r, 0)

        """Check if everything is equal to zero"""
        for r in self.ar:
            self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0)

    def test_fp_reg(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 80:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef0123456789dead)

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 80:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef0123456789dead)

    def test_rand_set_get_concrete_value(self):
        """Check setting concrete values"""
        for _ in range(100):
            for reg in self.ar:
                v = randrange(0, reg.getBitvector().getMaxValue() + 1)
                self.ctx.setConcreteRegisterValue(reg, v)
                self.assertEqual(self.ctx.getConcreteRegisterValue(reg), v)


class TestX8664ConcreteRegisterValue(unittest.TestCase):

    """Testing the X86_64 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ar = self.ctx.getAllRegisters()
        self.pr = self.ctx.getParentRegisters()

    def test_all_registers(self):
        """Check all registers"""
        self.assertEqual(len(self.ar), 255)

    def test_parent_registers(self):
        """Check parent registers"""
        self.assertEqual(len(self.pr), 201)

    def test_set_get_concrete_value(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.ctx.setConcreteRegisterValue(r, 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 512:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 512:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Set everything to zero"""
        for r in self.ar:
            self.ctx.setConcreteRegisterValue(r, 0)

        """Check if everything is equal to zero"""
        for r in self.ar:
            self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0)

    def test_fp_reg(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 80:
                self.ctx.setConcreteRegisterValue(r, 0xabcdef0123456789dead)

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 80:
                self.assertEqual(self.ctx.getConcreteRegisterValue(r), 0xabcdef0123456789dead)


class TestX86ConcreteMemoryValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

    def test_set_get_concrete_value(self):
        base = 0x1000
        size = 256
        count = 1

        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        for x in range(size):
            self.ctx.setConcreteMemoryValue(base + x, count & 0xff)
            self.assertEqual(self.ctx.getConcreteMemoryValue(base + x), count & 0xff)
            count += 1

        self.assertTrue(self.ctx.isConcreteMemoryValueDefined(base, size))
        self.ctx.clearConcreteMemoryValue(base, size)
        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x11\x22\x33\x44\x55\x66")
        self.ctx.setConcreteMemoryAreaValue(0x1006, [0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc])
        self.assertEqual(self.ctx.getConcreteMemoryAreaValue(0x1000, 12), b"\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc")


class TestAArch64ConcreteMemoryValue(unittest.TestCase):

    """Testing the AArch64 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.AARCH64)

    def test_set_get_concrete_value(self):
        base = 0x1000
        size = 256
        count = 1

        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        for x in range(size):
            self.ctx.setConcreteMemoryValue(base + x, count & 0xff)
            self.assertEqual(self.ctx.getConcreteMemoryValue(base + x), count & 0xff)
            count += 1

        self.assertTrue(self.ctx.isConcreteMemoryValueDefined(base, size))
        self.ctx.clearConcreteMemoryValue(base, size)
        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x11\x22\x33\x44\x55\x66")
        self.ctx.setConcreteMemoryAreaValue(0x1006, [0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc])
        self.assertEqual(self.ctx.getConcreteMemoryAreaValue(0x1000, 12), b"\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc")


class TestX8664ConcreteMemoryValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

    def test_set_get_concrete_value(self):
        base = 0x2000
        size = 512
        count = 1

        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        for x in range(size):
            self.ctx.setConcreteMemoryValue(base + x, count & 0xff)
            self.assertEqual(self.ctx.getConcreteMemoryValue(base + x), count & 0xff)
            count += 1

        self.assertTrue(self.ctx.isConcreteMemoryValueDefined(base, size))
        self.ctx.clearConcreteMemoryValue(base, size)
        self.assertFalse(self.ctx.isConcreteMemoryValueDefined(base, size))

        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x11\x22\x33\x44\x55\x66")
        self.ctx.setConcreteMemoryAreaValue(0x1006, [0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc])
        self.assertEqual(self.ctx.getConcreteMemoryAreaValue(0x1000, 12), b"\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc")


class TestAArch64ConcreteRegisterValue(unittest.TestCase):

    """Testing the AArch64 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.AARCH64)
        self.ar = self.ctx.getAllRegisters()

    def test_rand_set_get_concrete_value(self):
        """Check setting concrete values"""
        for _ in range(100):
            for reg in self.ar:
                if reg.isMutable() == False:
                    continue
                v = randrange(0, reg.getBitvector().getMaxValue() + 1)
                self.ctx.setConcreteRegisterValue(reg, v)
                self.assertEqual(self.ctx.getConcreteRegisterValue(reg), v)
