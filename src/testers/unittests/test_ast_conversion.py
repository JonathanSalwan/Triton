#!/usr/bin/env python2
# coding: utf-8
"""Test AST conversion."""

import operator
import random
import unittest
import utils

from triton import TritonContext, ARCH



class TestAstConversion(unittest.TestCase):

    """Testing the AST conversion Triton <-> z3."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

        # Show seed use for tests
        seed = random.random()
        print "seed use is : ", seed
        random.seed(seed)

        self.astCtxt = self.Triton.getAstContext()

        self.sv1 = self.Triton.newSymbolicVariable(8)
        self.sv2 = self.Triton.newSymbolicVariable(8)

        self.v1 = self.astCtxt.variable(self.sv1)
        self.v2 = self.astCtxt.variable(self.sv2)

    def test_binop(self):
        """
        Check python binary operation.

        Fuzz int8/uint8 binop values and check triton/z3 and python results.
        """
        # No simplification available
        # This only going to test Triton <-> z3 AST conversions.
        binop = [
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
            operator.div,
            operator.mod,
        ]

        for _ in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            for op in binop:
                n = op(self.v1, self.v2)
                if op == operator.div and cv2 == 0:
                    ref = 255
                elif op == operator.mod and cv2 == 0:
                    ref = cv1
                else:
                    ref = op(cv1, cv2) % (2 ** 8)
                self.assertEqual(ref, n.evaluate(),
                                 "ref = {} and triton value = {} with operator {}"
                                 " operands were {} and {}".format(ref,
                                                                   n.evaluate(),
                                                                   op,
                                                                   cv1,
                                                                   cv2))
                self.assertEqual(ref, self.Triton.evaluateAstViaZ3(n))

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
                                 "ref = {} and triton value = {} with operator "
                                 "{} operands was {}".format(ref,
                                                             n.evaluate(),
                                                             op,
                                                             cv1))
                self.assertEqual(ref, self.Triton.evaluateAstViaZ3(n))

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
            self.astCtxt.bvor,
            self.astCtxt.bvsdiv,
            self.astCtxt.bvsge,
            self.astCtxt.bvsgt,
            self.astCtxt.bvshl,
            self.astCtxt.bvsle,
            self.astCtxt.bvslt,
            self.astCtxt.bvsmod,
            self.astCtxt.bvsrem,
            self.astCtxt.bvsub,
            self.astCtxt.bvudiv,
            self.astCtxt.bvuge,
            self.astCtxt.bvugt,
            self.astCtxt.bvule,
            self.astCtxt.bvult,
            self.astCtxt.bvurem,
            self.astCtxt.bvxnor,
            self.astCtxt.bvxor,
            self.astCtxt.concat,
            self.astCtxt.distinct,
            self.astCtxt.equal,
            self.astCtxt.land,
            self.astCtxt.lor,
        ]

        for _ in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            for op in smtbinop:
                if op == self.astCtxt.concat:
                    n = op([self.v1, self.v2])
                elif op in (self.astCtxt.land, self.astCtxt.lor):
                    n = op([self.v1 != 0, self.v2 != 0])
                else:
                    n = op(self.v1, self.v2)
                self.assertEqual(n.evaluate(),
                                 self.Triton.evaluateAstViaZ3(n),
                                 "triton = {} and z3 = {} with operator {}"
                                 " operands were {} and {}".format(n.evaluate(),
                                                                   self.Triton.evaluateAstViaZ3(n),
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
            self.astCtxt.lnot,
            lambda x: self.astCtxt.bvrol(3, x),
            lambda x: self.astCtxt.bvror(2, x),
            lambda x: self.astCtxt.sx(16, x),
            lambda x: self.astCtxt.zx(16, x),
        ]

        for cv1 in xrange(0, 256):
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            for op in smtunop:
                if op == self.astCtxt.lnot:
                    n = op(self.v1 != 0)
                else:
                    n = op(self.v1)
                self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    def test_bvnode(self):
        """Check python bit vector declaration."""
        for _ in xrange(100):
            cv1 = random.randint(-127, 255)
            n = self.astCtxt.bv(cv1, 8)
            self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    def test_extract(self):
        """Check bit extraction from bitvector."""
        for _ in xrange(100):
            cv1 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            for lo in xrange(0, 8):
                for hi in xrange(lo, 8):
                    n = self.astCtxt.extract(hi, lo, self.v1)
                    ref = ((cv1 << (7 - hi)) % 256) >> (7 - hi + lo)
                    self.assertEqual(ref, n.evaluate(),
                                     "ref = {} and triton value = {} with operator"
                                     "'extract' operands was {} low was : {} and "
                                     "hi was : {}".format(ref, n.evaluate(),
                                                          cv1, lo, hi))
                    self.assertEqual(ref, self.Triton.evaluateAstViaZ3(n))

    def test_ite(self):
        """Check ite node."""
        for _ in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            n = self.astCtxt.ite(self.v1 < self.v2, self.v1, self.v2)
            self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    @utils.xfail
    def test_decimal(self):
        # Decimal node is not exported in the python interface
        for cv1 in xrange(0, 256):
            n = self.astCtxt.decimale(cv1)
            self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    @utils.xfail
    def test_let(self):
        # Let node didn't take the variable in its computation
        for run in xrange(100):
            cv1 = random.randint(0, 255)
            cv2 = random.randint(0, 255)
            self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
            self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
            n = self.astCtxt.let("b", self.astCtxt.bvadd(self.v1, self.v2), self.astCtxt.bvadd(self.astCtxt.string("b"), self.v1))
            self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    def test_fuzz(self):
        """
        Fuzz test an ast evaluation.

        It creates an ast node of depth 10 and evaluate it with triton and z3
        and compare result.
        """
        self.in_bool = [
            (self.astCtxt.lnot, 1),
            (self.astCtxt.land, 2),
            (self.astCtxt.lor, 2),
        ]
        self.to_bool = [
            (self.astCtxt.bvsge, 2),
            (self.astCtxt.bvsgt, 2),
            (self.astCtxt.bvsle, 2),
            (self.astCtxt.bvslt, 2),
            (self.astCtxt.bvuge, 2),
            (self.astCtxt.bvugt, 2),
            (self.astCtxt.bvule, 2),
            (self.astCtxt.bvult, 2),
            (self.astCtxt.equal, 2),
        ] + self.in_bool
        self.bvop = [
            (self.astCtxt.bvneg, 1),
            (self.astCtxt.bvnot, 1),
            (lambda x: self.astCtxt.bvrol(3, x), 1),
            (lambda x: self.astCtxt.bvror(2, x), 1),
            (lambda x: self.astCtxt.extract(11, 4, self.astCtxt.sx(16, x)), 1),
            (lambda x: self.astCtxt.extract(11, 4, self.astCtxt.zx(16, x)), 1),

            # BinOp
            (self.astCtxt.bvadd, 2),
            (self.astCtxt.bvand, 2),
            (self.astCtxt.bvlshr, 2),
            (self.astCtxt.bvashr, 2),
            (self.astCtxt.bvmul, 2),
            (self.astCtxt.bvnand, 2),
            (self.astCtxt.bvnor, 2),
            (self.astCtxt.bvor, 2),
            (self.astCtxt.bvsdiv, 2),
            (self.astCtxt.bvshl, 2),
            (self.astCtxt.bvsmod, 2),
            (self.astCtxt.bvsrem, 2),
            (self.astCtxt.bvsub, 2),
            (self.astCtxt.bvudiv, 2),
            (self.astCtxt.bvurem, 2),
            (self.astCtxt.bvxnor, 2),
            (self.astCtxt.bvxor, 2),
            (lambda x, y: self.astCtxt.concat([self.astCtxt.extract(3, 0, x), self.astCtxt.extract(7, 4, y)]), 2),

            (self.astCtxt.ite, -1),

            # value
            (self.v1, 0),
            (self.v2, 0),
        ]
        for _ in xrange(10):
            n = self.new_node(0, self.bvop)
            for _ in xrange(10):
                cv1 = random.randint(0, 255)
                cv2 = random.randint(0, 255)
                self.Triton.setConcreteSymbolicVariableValue(self.sv1, cv1)
                self.Triton.setConcreteSymbolicVariableValue(self.sv2, cv2)
                self.assertEqual(n.evaluate(), self.Triton.evaluateAstViaZ3(n))

    def new_node(self, depth, possible):
        """Recursive function to create a random ast."""
        if depth >= 10:
            # shortcut if the tree is deep enough
            possible = possible[-2:]

        op, nargs = random.choice(possible)
        if op == self.astCtxt.ite:
            return op(self.new_node(depth, self.to_bool),
                      self.new_node(depth + 1, self.bvop),
                      self.new_node(depth + 1, self.bvop))
        elif any(op == ibo for ibo, _ in self.in_bool):
            args = [self.new_node(depth, self.to_bool) for _ in xrange(nargs)]
            if op in (self.astCtxt.land, self.astCtxt.lor):
                return op(args)
            else:
                return op(*args)
        elif nargs == 0:
            return op
        else:
            return op(*[self.new_node(depth + 1, self.bvop) for _ in xrange(nargs)])
