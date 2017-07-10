#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest

from triton import ARCH, TritonContext


class TestX86ConcreteRegisterValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86)
        self.ar = self.Triton.getAllRegisters()
        self.pr = self.Triton.getParentRegisters()

    def test_all_registers(self):
        """Check all registers"""
        self.assertEqual(len(self.ar), 103)

    def test_parent_registers(self):
        """Check parent registers"""
        self.assertEqual(len(self.pr), 82)

    def test_set_get_concrete_value(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.Triton.setConcreteRegisterValue(r, 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Set everything to zero"""
        for r in self.ar:
            self.Triton.setConcreteRegisterValue(r, 0)

        """Check if everything is equal to zero"""
        for r in self.ar:
            self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0)

class TestX8664ConcreteRegisterValue(unittest.TestCase):

    """Testing the X86_64 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.ar = self.Triton.getAllRegisters()
        self.pr = self.Triton.getParentRegisters()

    def test_all_registers(self):
        """Check all registers"""
        self.assertEqual(len(self.ar), 192)

    def test_parent_registers(self):
        """Check parent registers"""
        self.assertEqual(len(self.pr), 138)

    def test_set_get_concrete_value(self):
        """Check setting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.Triton.setConcreteRegisterValue(r, 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 512:
                self.Triton.setConcreteRegisterValue(r, 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Check getting concrete values"""
        for r in self.pr:
            if r.getBitSize() == 32:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xdeadbeaf)
            elif r.getBitSize() == 64:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef0123456789)
            elif r.getBitSize() == 128:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 256:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            elif r.getBitSize() == 512:
                self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0xabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcbaabcdef01234567899876543210fedcba)
            else:
                pass

        """Set everything to zero"""
        for r in self.ar:
            self.Triton.setConcreteRegisterValue(r, 0)

        """Check if everything is equal to zero"""
        for r in self.ar:
            self.assertEqual(self.Triton.getConcreteRegisterValue(r), 0)

class TestX86ConcreteMemoryValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86)

    def test_set_get_concrete_value(self):
        base = 0x1000
        size = 256
        count = 1

        self.assertFalse(self.Triton.isMemoryMapped(base, size))

        for x in range(size):
            self.Triton.setConcreteMemoryValue(base + x, count & 0xff)
            self.assertEqual(self.Triton.getConcreteMemoryValue(base + x), count & 0xff)
            count += 1

        self.assertTrue(self.Triton.isMemoryMapped(base, size))
        self.Triton.unmapMemory(base, size)
        self.assertFalse(self.Triton.isMemoryMapped(base, size))

        self.Triton.setConcreteMemoryAreaValue(0x1000, "\x11\x22\x33\x44\x55\x66")
        self.Triton.setConcreteMemoryAreaValue(0x1006, [0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc])
        self.assertEqual(self.Triton.getConcreteMemoryAreaValue(0x1000, 12), "\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc")

class TestX8664ConcreteMemoryValue(unittest.TestCase):

    """Testing the X86 concrete value api."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

    def test_set_get_concrete_value(self):
        base = 0x2000
        size = 512
        count = 1

        self.assertFalse(self.Triton.isMemoryMapped(base, size))

        for x in range(size):
            self.Triton.setConcreteMemoryValue(base + x, count & 0xff)
            self.assertEqual(self.Triton.getConcreteMemoryValue(base + x), count & 0xff)
            count += 1

        self.assertTrue(self.Triton.isMemoryMapped(base, size))
        self.Triton.unmapMemory(base, size)
        self.assertFalse(self.Triton.isMemoryMapped(base, size))

        self.Triton.setConcreteMemoryAreaValue(0x1000, "\x11\x22\x33\x44\x55\x66")
        self.Triton.setConcreteMemoryAreaValue(0x1006, [0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc])
        self.assertEqual(self.Triton.getConcreteMemoryAreaValue(0x1000, 12), "\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc")
