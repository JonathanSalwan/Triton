#!/usr/bin/env python2
# coding: utf-8
"""Test AST representation."""

import unittest

from triton     import *
from triton.ast import *


class TestAstRepresentation(unittest.TestCase):

    """Testing the AST Representation."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

        self.v1  = variable(newSymbolicVariable(8))
        self.v2  = variable(newSymbolicVariable(8))
        self.ref = newSymbolicExpression(self.v1 + self.v2, "ref test")

        self.node = [
            # Overloaded operators              # SMT                                   # Python
            ((self.v1 & self.v2),               "(bvand SymVar_0 SymVar_1)",            "(SymVar_0 & SymVar_1)"),
            ((self.v1 + self.v2),               "(bvadd SymVar_0 SymVar_1)",            "((SymVar_0 + SymVar_1) & 0xFF)"),
            ((self.v1 - self.v2),               "(bvsub SymVar_0 SymVar_1)",            "((SymVar_0 - SymVar_1) & 0xFF)"),
            ((self.v1 ^ self.v2),               "(bvxor SymVar_0 SymVar_1)",            "(SymVar_0 ^ SymVar_1)"),
            ((self.v1 | self.v2),               "(bvor SymVar_0 SymVar_1)",             "(SymVar_0 | SymVar_1)"),
            ((self.v1 * self.v2),               "(bvmul SymVar_0 SymVar_1)",            "((SymVar_0 * SymVar_1) & 0xFF)"),
            ((self.v1 / self.v2),               "(bvudiv SymVar_0 SymVar_1)",           "(SymVar_0 / SymVar_1)"),
            ((self.v1 % self.v2),               "(bvurem SymVar_0 SymVar_1)",           "(SymVar_0 % SymVar_1)"),
            ((self.v1 << self.v2),              "(bvshl SymVar_0 SymVar_1)",            "((SymVar_0 << SymVar_1) & 0xFF)"),
            ((self.v1 >> self.v2),              "(bvlshr SymVar_0 SymVar_1)",           "(SymVar_0 >> SymVar_1)"),
            ((~self.v1),                        "(bvnot SymVar_0)",                     "(~(SymVar_0) & 0xFF)"),
            ((-self.v1),                        "(bvneg SymVar_0)",                     "-SymVar_0"),
            ((self.v1 == self.v2),              "(= SymVar_0 SymVar_1)",                "(SymVar_0 == SymVar_1)"),
            ((self.v1 != self.v2),              "(not (= SymVar_0 SymVar_1))",          "not (SymVar_0 == SymVar_1)"),
            ((self.v1 <= self.v2),              "(bvule SymVar_0 SymVar_1)",            "(SymVar_0 <= SymVar_1)"),
            ((self.v1 >= self.v2),              "(bvuge SymVar_0 SymVar_1)",            "(SymVar_0 >= SymVar_1)"),
            ((self.v1 < self.v2),               "(bvult SymVar_0 SymVar_1)",            "(SymVar_0 < SymVar_1)"),
            ((self.v1 > self.v2),               "(bvugt SymVar_0 SymVar_1)",            "(SymVar_0 > SymVar_1)"),

            # AST api                           # SMT                                   # Python
            (assert_(self.v1),                  "(assert SymVar_0)",                    "assert(SymVar_0)"),
            (bv(2, 8),                          "(_ bv2 8)",                            "0x2"),
            (bvashr(self.v1, self.v2),          "(bvashr SymVar_0 SymVar_1)",           "(SymVar_0 >> SymVar_1)"),
            (bvdecl(8),                         "(_ BitVec 8)",                         "bvdecl(0x8)"),
            (bvfalse(),                         "(_ bv0 1)",                            "0x0"),
            (bvnand(self.v1, self.v2),          "(bvnand SymVar_0 SymVar_1)",           "(~(SymVar_0 & SymVar_1) & 0xFF)"),
            (bvnor(self.v1, self.v2),           "(bvnor SymVar_0 SymVar_1)",            "(~(SymVar_0 | SymVar_1) & 0xFF)"),
            (bvrol(3, self.v1),                 "((_ rotate_left 3) SymVar_0)",         "rol(0x3, SymVar_0)"),
            (bvror(2, self.v2),                 "((_ rotate_right 2) SymVar_1)",        "ror(0x2, SymVar_1)"),
            (bvsdiv(self.v1, self.v2),          "(bvsdiv SymVar_0 SymVar_1)",           "(SymVar_0 / SymVar_1)"),
            (bvsge(self.v1, self.v2),           "(bvsge SymVar_0 SymVar_1)",            "(SymVar_0 >= SymVar_1)"),
            (bvsgt(self.v1, self.v2),           "(bvsgt SymVar_0 SymVar_1)",            "(SymVar_0 > SymVar_1)"),
            (bvsle(self.v1, self.v2),           "(bvsle SymVar_0 SymVar_1)",            "(SymVar_0 <= SymVar_1)"),
            (bvslt(self.v1, self.v2),           "(bvslt SymVar_0 SymVar_1)",            "(SymVar_0 < SymVar_1)"),
            (bvsmod(self.v1, self.v2),          "(bvsmod SymVar_0 SymVar_1)",           "(SymVar_0 % SymVar_1)"),
            (bvtrue(),                          "(_ bv1 1)",                            "0x1"),
            (bvurem(self.v1, self.v2),          "(bvurem SymVar_0 SymVar_1)",           "(SymVar_0 % SymVar_1)"),
            (bvxnor(self.v1, self.v2),          "(bvxnor SymVar_0 SymVar_1)",           "(~(SymVar_0 ^ SymVar_1) & 0xFF)"),
            (concat([self.v1, self.v2]),        "(concat SymVar_0 SymVar_1)",           "((SymVar_0) << 8 | SymVar_1)"),
            (distinct(self.v1, self.v2),        "(distinct SymVar_0 SymVar_1)",         "(SymVar_0 != SymVar_1)"),
            (equal(self.v1, self.v2),           "(= SymVar_0 SymVar_1)",                "(SymVar_0 == SymVar_1)"),
            (extract(4, 2, self.v1),            "((_ extract 4 2) SymVar_0)",           "((SymVar_0 >> 2) & 0x7)"),
            (extract(7, 0, self.v1),            "((_ extract 7 0) SymVar_0)",           "(SymVar_0 & 0xFF)"),
            (ite(self.v1, self.v1, self.v2),    "(ite SymVar_0 SymVar_0 SymVar_1)",     "(SymVar_0 if SymVar_0 else SymVar_1)"),
            (land(self.v1, self.v2),            "(and SymVar_0 SymVar_1)",              "(SymVar_0 and SymVar_1)"),
            (let("alias", self.v1, self.v2),    "(let ((alias SymVar_0)) SymVar_1)",    "SymVar_1"),
            (lnot(self.v1),                     "(not SymVar_0)",                       "not SymVar_0"),
            (lor(self.v1, self.v2),             "(or SymVar_0 SymVar_1)",               "(SymVar_0 or SymVar_1)"),
            (reference(0),                      "ref!0",                                "ref_0"),
            (string("test"),                    "test",                                 "test"),
            (sx(8, self.v1),                    "((_ sign_extend 8) SymVar_0)",         "sx(0x8, SymVar_0)"),
            (zx(8, self.v1),                    "((_ zero_extend 8) SymVar_0)",         "SymVar_0"),
        ]

    def test_smt_representation(self):
        setAstRepresentationMode(AST_REPRESENTATION.SMT)
        for n in self.node:
            self.assertEqual(str(n[0]), n[1])

    def test_python_representation(self):
        setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
        for n in self.node:
            self.assertEqual(str(n[0]), n[2])

