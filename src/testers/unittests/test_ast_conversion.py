#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import unittest

from triton     import TritonContext, ARCH


class TestAstConversion(unittest.TestCase):

    """Testing the AST conversion Triton <-> z3."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

        self.astCtxt = self.Triton.getAstContext()

        self.sv1   = self.Triton.newSymbolicVariable(8)
        self.sv2   = self.Triton.newSymbolicVariable(8)

        self.v1   = self.astCtxt.variable(self.sv1)
        self.v2   = self.astCtxt.variable(self.sv2)

        self.Triton.setConcreteSymbolicVariableValue(self.sv1, 0xaa)
        self.Triton.setConcreteSymbolicVariableValue(self.sv2, 0x55)

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
            self.astCtxt.bvashr(self.v1, self.v2),
            self.astCtxt.bvnand(self.v1, self.v2),
            self.astCtxt.bvnor(self.v1, self.v2),
            self.astCtxt.bvrol(3, self.v1),
            self.astCtxt.bvror(2, self.v2),
            self.astCtxt.distinct(self.v1, self.v2),
            self.astCtxt.equal(self.v1, self.v2),
            self.astCtxt.sx(8, self.v1),
            self.astCtxt.zx(8, self.v1),
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
            self.assertEqual(n.evaluate(), self.Triton.simplify(n, True).evaluate())

