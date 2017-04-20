#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest

from triton import TritonContext, ARCH, REG


class TestRAXBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.Register(REG.X86_64.RAX).getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 63)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 0)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 64)


class TestCHBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.Register(REG.X86_64.CH).getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 15)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 8)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 8)


class TestDLBitvector(unittest.TestCase):

    """Testing the Bitvector class."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.bv = self.Triton.Register(REG.X86_64.DL).getBitvector()

    def test_high(self):
        """Check the highest bit."""
        self.assertEqual(self.bv.getHigh(), 7)

    def test_low(self):
        """Check the lower bit."""
        self.assertEqual(self.bv.getLow(), 0)

    def test_size(self):
        """Check the vector size."""
        self.assertEqual(self.bv.getVectorSize(), 8)
