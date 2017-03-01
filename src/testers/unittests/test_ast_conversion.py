#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import unittest

from triton     import *
from triton.ast import *


class TestAstConversion(unittest.TestCase):

    """Testing the AST conversion Triton <-> z3."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

        self.v1   = newSymbolicVariable(8)
        self.v2   = newSymbolicVariable(8)

        self.v1.setConcreteValue(0xaa)
        self.v2.setConcreteValue(0x55)

        self.v1  = variable(self.v1)
        self.v2  = variable(self.v2)

        self.node = [
            # Overloaded operators
            (self.v1 & self.v2),
            (self.v1 + self.v2),
            (self.v1 - self.v2),
            (self.v1 ^ self.v2),
            (self.v1 | self.v2),
            (self.v1 * self.v2),
            (self.v1 << self.v2),
            (self.v1 >> self.v2),
            (~self.v1),
            (-self.v1),
            (self.v1 == self.v2),
            (self.v1 != self.v2),
            (self.v1 <= self.v2),
            (self.v1 >= self.v2),
            (self.v1 < self.v2),
            (self.v1 > self.v2),
            # AST API
            bvashr(self.v1, self.v2),
            bvnand(self.v1, self.v2),
            bvnor(self.v1, self.v2),
            bvrol(3, self.v1),
            bvror(2, self.v2),
            distinct(self.v1, self.v2),
            equal(self.v1, self.v2),
            sx(8, self.v1),
            zx(8, self.v1),
            # recent z3 version
            #bvsdiv(self.v1, self.v2),
            #bvsmod(self.v1, self.v2),
            #bvsrem(self.v1, self.v2),
            #bvudiv(self.v1, self.v2),
            #bvurem(self.v1, self.v2),
        ]

    def test_conversion(self):
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        for n in self.node:
            self.assertEqual(n.evaluate(), simplify(n, True).evaluate())

