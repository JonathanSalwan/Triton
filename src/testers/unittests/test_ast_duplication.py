#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import unittest

from triton import TritonContext, ARCH


class TestAstDuplication(unittest.TestCase):

    """Testing the AST duplication."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.astCtxt = self.Triton.getAstContext()

        self.v1  = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        self.v2  = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        self.ref = self.Triton.newSymbolicExpression(self.v1 + self.v2, "ref test")

        self.node = [
            # Overloaded operators
            (self.v1 & self.v2),
            (self.v1 + self.v2),
            (self.v1 - self.v2),
            (self.v1 ^ self.v2),
            (self.v1 | self.v2),
            (self.v1 * self.v2),
            (self.v1 / self.v2),
            (self.v1 % self.v2),
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
            # AST api
            self.astCtxt.bv(2, 8),
            self.astCtxt.bvashr(self.v1, self.v2),
            self.astCtxt.bvfalse(),
            self.astCtxt.bvnand(self.v1, self.v2),
            self.astCtxt.bvnor(self.v1, self.v2),
            self.astCtxt.bvrol(3, self.v1),
            self.astCtxt.bvror(2, self.v2),
            self.astCtxt.bvsdiv(self.v1, self.v2),
            self.astCtxt.bvsge(self.v1, self.v2),
            self.astCtxt.bvsgt(self.v1, self.v2),
            self.astCtxt.bvsle(self.v1, self.v2),
            self.astCtxt.bvslt(self.v1, self.v2),
            self.astCtxt.bvsmod(self.v1, self.v2),
            self.astCtxt.bvtrue(),
            self.astCtxt.bvurem(self.v1, self.v2),
            self.astCtxt.bvxnor(self.v1, self.v2),
            self.astCtxt.concat([self.v1, self.v2]),
            self.astCtxt.distinct(self.v1, self.v2),
            self.astCtxt.equal(self.v1, self.v2),
            self.astCtxt.extract(4, 2, self.v1),
            self.astCtxt.extract(7, 0, self.v1),
            self.astCtxt.ite(self.v1 == 2, self.v1, self.v2),
            self.astCtxt.land([self.v1 == 1, self.v2 == 2]),
            self.astCtxt.let("alias", self.v1, self.v2),
            self.astCtxt.lnot(self.v1 == 0),
            self.astCtxt.lor([self.v1 >= 0, self.v2 <= 10]),
            self.astCtxt.reference(self.ref),
            self.astCtxt.string("test"),
            self.astCtxt.sx(8, self.v1),
            self.astCtxt.zx(8, self.v1),
        ]

    def test_duplication(self):
        for n in self.node:
            self.assertEqual(n.getHash(), self.astCtxt.duplicate(n).getHash())

