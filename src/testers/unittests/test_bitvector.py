#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest

from triton import TritonContext, ARCH


class TestRAXBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.registers.rax.getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 63)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 0)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 64)

    def test_maxValue(self):
        """Check the max value of the vector."""
        self.assertEqual(self.bv.getMaxValue(), 0xffffffffffffffff)


class TestCHBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.registers.ch.getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 15)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 8)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 8)

    def test_maxValue(self):
        """Check the max value of the vector."""
        self.assertEqual(self.bv.getMaxValue(), 0xff)


class TestDLBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.registers.dl.getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 7)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 0)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 8)

    def test_maxValue(self):
        """Check the max value of the vector."""
        self.assertEqual(self.bv.getMaxValue(), 0xff)

