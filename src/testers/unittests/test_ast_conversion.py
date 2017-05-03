#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import unittest
import operator
import random

from triton import TritonContext, ARCH

import utils


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

    def test_binop(self):
        """
        Check python binary operation.

        Fuzz int8/uint8 binop values and check triton/z3 and python results.
        """
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        binop= [
            # Overloaded operators
            operator.and_,
            operator.add,
            operator.sub,
            operator.xor,
            operator.or_,
            operator.mul,
            operator.lshift,
            operator.rshift,
            operator.eq,
            operator.ne,
            operator.le,
            operator.ge,
            operator.lt,
            operator.gt,
            #operator.div,
            #operator.mod,
        ]


        for run in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            for op in binop:
                n = op(self.v1, self.v2)
                ref = op(cv1, cv2) % (2 ** 8)
                self.assertEqual(ref, n.evaluate(),
                                 "ref = {} and triton value = {} with operator {}"
                                 " operands were {} and {}".format(ref,
                                                                   n.evaluate(),
                                                                   op,
                                                                   cv1,
                                                                   cv2))
                self.assertEqual(str(n), str(self.Triton.simplify(n, True)))
                self.assertEqual(ref, self.Triton.simplify(n, True).evaluate())

    def test_unop(self):
        """
        Check python unary operation.

        Fuzz int8/uint8 binop values and check triton/z3 and python results.
        """
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        unop = [
            operator.invert,
            operator.neg,
        ]

        for cv1 in xrange(0, 256):
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            for op in unop:
                n = op(self.v1)
                ref = op(cv1) % (2 ** 8)
                self.assertEqual(ref, n.evaluate(),
                                 "ref = {} and triton value = {} with operator {}"
                                 " operands was {}".format(ref,
                                                           n.evaluate(),
                                                           op,
                                                           cv1))
                self.assertEqual(str(n), str(self.Triton.simplify(n, True)))
                self.assertEqual(ref, self.Triton.simplify(n, True).evaluate())

    def test_smtbinop(self):
        """
        Check smt binary operation.

        Fuzz int8/uint8 binop values and check triton/z3 and python results.
        """
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        smtbinop = [
            # AST API
            self.astCtxt.bvadd,
            self.astCtxt.bvand,
            self.astCtxt.bvlshr,
            self.astCtxt.bvashr,
            self.astCtxt.bvmul,
            self.astCtxt.bvnand,
            self.astCtxt.bvnor,
            #self.astCtxt.bvrol,
            #self.astCtxt.bvror,
            self.astCtxt.bvor,
            #self.astCtxt.bvsdiv,
            self.astCtxt.bvsge,
            self.astCtxt.bvsgt,
            self.astCtxt.bvshl,
            self.astCtxt.bvsle,
            self.astCtxt.bvslt,
            #self.astCtxt.bvsmod,
            #self.astCtxt.bvsrem,
            self.astCtxt.bvsub,
            #self.astCtxt.bvudiv,
            self.astCtxt.bvuge,
            self.astCtxt.bvugt,
            self.astCtxt.bvule,
            self.astCtxt.bvult,
            #self.astCtxt.bvurem,
            self.astCtxt.bvxnor,
            self.astCtxt.bvxor,
            #self.astCtxt.concat,
            self.astCtxt.distinct,
            self.astCtxt.equal,
            #self.astCtxt.land,
            #self.astCtxt.lor,
        ]

        for run in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            for op in smtbinop:
                n = op(self.v1, self.v2)
                self.assertEqual(n.evaluate(), self.Triton.simplify(n, True).evaluate(),
                                 "triton = {} and z3 = {} with operator {}"
                                 " operands were {} and {}".format(n.evaluate(),
                                                                   self.Triton.simplify(n, True).evaluate(),
                                                                   op,
                                                                   cv1,
                                                                   cv2))

    def test_smt_unop(self):
        """
        Check python unary operation.

        Fuzz int8/uint8 binop values and check triton/z3 and python results.
        """
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        smtunop = [
            self.astCtxt.bvneg,
            self.astCtxt.bvnot,
            #self.astCtxt.lnot,
            lambda x: self.astCtxt.bvrol(3, x),
            lambda x: self.astCtxt.bvror(2, x),
            lambda x: self.astCtxt.sx(8, x),
            lambda x: self.astCtxt.zx(8, x),
        ]

        for cv1 in xrange(0, 256):
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            for op in smtunop:
                n = op(self.v1)
                self.assertEqual(n.evaluate(), self.Triton.simplify(n, True).evaluate())

    @utils.xfail
    def test_z3_assert(self):
        n = self.astCtxt.assert_(self.v1 == self.v1)
        self.Triton.simplify(n, True)
