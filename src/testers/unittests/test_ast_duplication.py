#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import unittest

from triton     import *
from triton.ast import *


class TestAstDuplication(unittest.TestCase):

    """Testing the AST duplication."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

        self.v1  = variable(newSymbolicVariable(8))
        self.v2  = variable(newSymbolicVariable(8))
        self.ref = newSymbolicExpression(self.v1 + self.v2, "ref test")

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
            assert_(self.v1),
            bv(2, 8),
            bvashr(self.v1, self.v2),
            bvdecl(8),
            bvfalse(),
            bvnand(self.v1, self.v2),
            bvnor(self.v1, self.v2),
            bvrol(3, self.v1),
            bvror(2, self.v2),
            bvsdiv(self.v1, self.v2),
            bvsge(self.v1, self.v2),
            bvsgt(self.v1, self.v2),
            bvsle(self.v1, self.v2),
            bvslt(self.v1, self.v2),
            bvsmod(self.v1, self.v2),
            bvtrue(),
            bvurem(self.v1, self.v2),
            bvxnor(self.v1, self.v2),
            concat([self.v1, self.v2]),
            distinct(self.v1, self.v2),
            equal(self.v1, self.v2),
            extract(4, 2, self.v1),
            extract(7, 0, self.v1),
            ite(self.v1, self.v1, self.v2),
            land(self.v1, self.v2),
            let("alias", self.v1, self.v2),
            lnot(self.v1),
            lor(self.v1, self.v2),
            reference(0),
            string("test"),
            sx(8, self.v1),
            zx(8, self.v1),
        ]

    def test_duplication(self):
        for n in self.node:
            self.assertEqual(n.getHash(), duplicate(n).getHash())

