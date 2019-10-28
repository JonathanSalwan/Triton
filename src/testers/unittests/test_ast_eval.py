#!/usr/bin/env python2
# coding: utf-8
"""Testing the arithmetic and logic AST interpreter."""

import unittest

from triton import ARCH, TritonContext, MODE


class TestAstEval(unittest.TestCase):

    """Testing the arithmetic and logic AST interpreter."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.astCtxt = self.Triton.getAstContext()

    def check_ast(self, tests):
        """Check our evaluation is the same as the one from Z3."""
        for test in tests:
            trv = test.evaluate()
            z3v = self.Triton.evaluateAstViaZ3(test)
            self.assertEqual(trv, z3v)

    def test_sub(self):
        """Check sub operations."""
        tests = [
            self.astCtxt.bvsub(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsub(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_add(self):
        """Check add operations."""
        tests = [
            self.astCtxt.bvadd(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvadd(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_xor(self):
        """Check xor operations."""
        tests = [
            self.astCtxt.bvxor(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvxor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_or(self):
        """Check or operations."""
        tests = [
            self.astCtxt.bvor(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_and(self):
        """Check and operations."""
        tests = [
            self.astCtxt.bvand(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_nand(self):
        """Check nand operations."""
        tests = [
            self.astCtxt.bvnand(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvnand(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_nor(self):
        """Check nor operations."""
        tests = [
            self.astCtxt.bvnor(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_xnor(self):
        """Check xnor operations."""
        tests = [
            self.astCtxt.bvxnor(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvxnor(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_mul(self):
        """Check mul operations."""
        tests = [
            self.astCtxt.bvmul(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvmul(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.check_ast(tests)

    def test_neg(self):
        """Check neg operations."""
        tests = [
            self.astCtxt.bvneg(self.astCtxt.bv(0x88888888, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x22345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x32345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x42345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x52345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x62345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x72345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x82345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x92345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xa2345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xb2345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xc2345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xd345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xe2345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x1, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x2, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x3, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x4, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x5, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x6, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xa, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xe, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xf, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x1f, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x2f, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0x3e, 32)),
            self.astCtxt.bvneg(self.astCtxt.bv(0xffff, 32)),
        ]
        self.check_ast(tests)

    def test_not(self):
        """Check not operations."""
        tests = [
            self.astCtxt.bvnot(self.astCtxt.bv(0x88888888, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x22345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x32345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x42345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x52345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x62345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x72345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x82345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x92345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xa2345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xb2345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xc2345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xd345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xe2345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x1, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x2, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x3, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x4, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x5, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x6, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xa, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xe, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xf, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x1f, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x2f, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0x3e, 32)),
            self.astCtxt.bvnot(self.astCtxt.bv(0xffff, 32)),
        ]
        self.check_ast(tests)

    def test_sdiv(self):
        """Check sdiv operations."""
        tests = [
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(0b00000001, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00010010, 8), self.astCtxt.bv(0b00000010, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00010100, 8), self.astCtxt.bv(0b00000100, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00001000, 8), self.astCtxt.bv(0b00001000, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00010000, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00100000, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b01000001, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0b10000010, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b00000011, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00000101, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00000110, 8)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0010001, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0010010, 7), self.astCtxt.bv(0b0000010, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0010100, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0001000, 7), self.astCtxt.bv(0b0001000, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0010000, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0100000, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b1000000, 7), self.astCtxt.bv(0b1000010, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0000110, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0000111, 7)),
            self.astCtxt.bvsdiv(self.astCtxt.bv(291, 16), self.astCtxt.sx(8, self.astCtxt.bv(251, 8))),
            self.astCtxt.bvsdiv(self.astCtxt.bv(4, 16), self.astCtxt.sx(8, self.astCtxt.bv(255, 8))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(16, self.astCtxt.bv(42313, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65491, 16))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(16, self.astCtxt.bv(32768, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65535, 16))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(32, self.astCtxt.bv(4294734073, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967251, 32))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(32, self.astCtxt.bv(2147483648, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967295, 32))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(64, self.astCtxt.bv(18446744073709318393, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551571, 64))),
            self.astCtxt.bvsdiv(self.astCtxt.zx(64, self.astCtxt.bv(9223372036854775808, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551615, 64))),
        ]
        self.check_ast(tests)

    def test_udiv(self):
        """Check udiv operations."""
        tests = [
            self.astCtxt.bvudiv(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(0b00000001, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00010010, 8), self.astCtxt.bv(0b00000010, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00010100, 8), self.astCtxt.bv(0b00000100, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00001000, 8), self.astCtxt.bv(0b00001000, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00010000, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00100000, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b01000001, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0b10000010, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b00000011, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00000101, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00000110, 8)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0010001, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0010010, 7), self.astCtxt.bv(0b0000010, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0010100, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0001000, 7), self.astCtxt.bv(0b0001000, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0010000, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0100000, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b1000000, 7), self.astCtxt.bv(0b1000010, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0000110, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0000111, 7)),
            self.astCtxt.bvudiv(self.astCtxt.bv(291, 16), self.astCtxt.sx(8, self.astCtxt.bv(251, 8))),
            self.astCtxt.bvudiv(self.astCtxt.bv(4, 16), self.astCtxt.sx(8, self.astCtxt.bv(255, 8))),
            self.astCtxt.bvudiv(self.astCtxt.zx(16, self.astCtxt.bv(42313, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65491, 16))),
            self.astCtxt.bvudiv(self.astCtxt.zx(16, self.astCtxt.bv(32768, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65535, 16))),
            self.astCtxt.bvudiv(self.astCtxt.zx(32, self.astCtxt.bv(4294734073, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967251, 32))),
            self.astCtxt.bvudiv(self.astCtxt.zx(32, self.astCtxt.bv(2147483648, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967295, 32))),
            self.astCtxt.bvudiv(self.astCtxt.zx(64, self.astCtxt.bv(18446744073709318393, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551571, 64))),
            self.astCtxt.bvudiv(self.astCtxt.zx(64, self.astCtxt.bv(9223372036854775808, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551615, 64))),
        ]
        self.check_ast(tests)

    def test_ashr(self):
        """Check ashr operations."""
        tests = [
            self.astCtxt.bvashr(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(0b00000001, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00010010, 8), self.astCtxt.bv(0b00000010, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00010100, 8), self.astCtxt.bv(0b00000100, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00001000, 8), self.astCtxt.bv(0b00001000, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00010000, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00100000, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b01000001, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0b10000010, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b00000011, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00000101, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00000110, 8)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0010001, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0010010, 7), self.astCtxt.bv(0b0000010, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0010100, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0001000, 7), self.astCtxt.bv(0b0001000, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0010000, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0100000, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b1000000, 7), self.astCtxt.bv(0b1000010, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0000110, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0000111, 7)),
            self.astCtxt.bvashr(self.astCtxt.bv(0xfe00000000000000, 64), self.astCtxt.bv(8, 64)),
        ]
        self.check_ast(tests)

    def test_lshr(self):
        """Check lshr operations."""
        tests = [
            self.astCtxt.bvlshr(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(4, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(5, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(6, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvlshr(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
        ]
        self.check_ast(tests)

    def test_shl(self):
        """Check shl operations."""
        tests = [
            self.astCtxt.bvshl(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000001, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000011, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00000101, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00001001, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00100001, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b01000001, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b10000011, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b01000101, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00101001, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvshl(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(123, 8)),
        ]
        self.check_ast(tests)

    def test_rol(self):
        """Check rol operations."""
        tests = [
            self.astCtxt.bvrol(self.astCtxt.bv(0x99999999, 32), self.astCtxt.bv(0x88888888, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(1, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(2, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(3, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(32, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(64, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(1, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(2, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(3, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(32, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(64, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvrol(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, False)
        self.check_ast(tests)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.check_ast(tests)

    def test_ror(self):
        """Check ror operations."""
        tests = [
            self.astCtxt.bvror(self.astCtxt.bv(0x99999999, 32), self.astCtxt.bv(0x88888888, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(1, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(2, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(3, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(32, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(64, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(1, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(2, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(3, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(32, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(64, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0xf2345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvror(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
        ]
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, False)
        self.check_ast(tests)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.check_ast(tests)

    def test_smod(self):
        """Check smod operations."""
        tests = [
            self.astCtxt.bvsmod(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(0b00000001, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00010010, 8), self.astCtxt.bv(0b00000010, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00010100, 8), self.astCtxt.bv(0b00000100, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00001000, 8), self.astCtxt.bv(0b00001000, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00010000, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00100000, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b01000001, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0b10000010, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b00000011, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00000101, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00000110, 8)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0010001, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0010010, 7), self.astCtxt.bv(0b0000010, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0010100, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0001000, 7), self.astCtxt.bv(0b0001000, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0010000, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0100000, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b1000000, 7), self.astCtxt.bv(0b1000010, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0000110, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0000111, 7)),
            self.astCtxt.bvsmod(self.astCtxt.bv(291, 16), self.astCtxt.sx(8, self.astCtxt.bv(251, 8))),
            self.astCtxt.bvsmod(self.astCtxt.bv(4, 16), self.astCtxt.sx(8, self.astCtxt.bv(255, 8))),
            self.astCtxt.bvsmod(self.astCtxt.zx(16, self.astCtxt.bv(42313, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65491, 16))),
            self.astCtxt.bvsmod(self.astCtxt.zx(16, self.astCtxt.bv(32768, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65535, 16))),
            self.astCtxt.bvsmod(self.astCtxt.zx(32, self.astCtxt.bv(4294734073, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967251, 32))),
            self.astCtxt.bvsmod(self.astCtxt.zx(32, self.astCtxt.bv(2147483648, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967295, 32))),
            self.astCtxt.bvsmod(self.astCtxt.zx(64, self.astCtxt.bv(18446744073709318393, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551571, 64))),
            self.astCtxt.bvsmod(self.astCtxt.zx(64, self.astCtxt.bv(9223372036854775808, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551615, 64))),
        ]
        self.check_ast(tests)

    def test_srem(self):
        """Check srem operations."""
        tests = [
            self.astCtxt.bvsrem(self.astCtxt.bv(0x88888888, 32), self.astCtxt.bv(0x99999999, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0x12345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(1, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(2, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(3, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(32, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(64, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0xf2345678, 32), self.astCtxt.bv(0x12345678, 32)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(0, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(1, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(2, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(3, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(4, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(5, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(6, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(7, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(8, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(9, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10001000, 8), self.astCtxt.bv(123, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00010001, 8), self.astCtxt.bv(0b00000001, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00010010, 8), self.astCtxt.bv(0b00000010, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00010100, 8), self.astCtxt.bv(0b00000100, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00001000, 8), self.astCtxt.bv(0b00001000, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00010000, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00100000, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b01000001, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b10000000, 8), self.astCtxt.bv(0b10000010, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b01000000, 8), self.astCtxt.bv(0b00000011, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00100000, 8), self.astCtxt.bv(0b00000101, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b00010000, 8), self.astCtxt.bv(0b00000110, 8)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0010001, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0010010, 7), self.astCtxt.bv(0b0000010, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0010100, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0001000, 7), self.astCtxt.bv(0b0001000, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0010000, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0100000, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000001, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b1000000, 7), self.astCtxt.bv(0b1000010, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0000000, 7), self.astCtxt.bv(0b0000100, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0100000, 7), self.astCtxt.bv(0b0000110, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(0b0010000, 7), self.astCtxt.bv(0b0000111, 7)),
            self.astCtxt.bvsrem(self.astCtxt.bv(291, 16), self.astCtxt.sx(8, self.astCtxt.bv(251, 8))),
            self.astCtxt.bvsrem(self.astCtxt.bv(4, 16), self.astCtxt.sx(8, self.astCtxt.bv(255, 8))),
            self.astCtxt.bvsrem(self.astCtxt.zx(16, self.astCtxt.bv(42313, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65491, 16))),
            self.astCtxt.bvsrem(self.astCtxt.zx(16, self.astCtxt.bv(32768, 16)), self.astCtxt.sx(16, self.astCtxt.bv(65535, 16))),
            self.astCtxt.bvsrem(self.astCtxt.zx(32, self.astCtxt.bv(4294734073, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967251, 32))),
            self.astCtxt.bvsrem(self.astCtxt.zx(32, self.astCtxt.bv(2147483648, 32)), self.astCtxt.sx(32, self.astCtxt.bv(4294967295, 32))),
            self.astCtxt.bvsrem(self.astCtxt.zx(64, self.astCtxt.bv(18446744073709318393, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551571, 64))),
            self.astCtxt.bvsrem(self.astCtxt.zx(64, self.astCtxt.bv(9223372036854775808, 64)), self.astCtxt.sx(64, self.astCtxt.bv(18446744073709551615, 64))),
        ]
        self.check_ast(tests)

    def test_iff(self):
        """Check iff operations."""
        tests = [
            self.astCtxt.iff(self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(1, 8)), self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(1, 8))),
            self.astCtxt.iff(self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(1, 8)), self.astCtxt.equal(self.astCtxt.bv(2, 8), self.astCtxt.bv(1, 8))),
            self.astCtxt.iff(self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(2, 8)), self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(1, 8))),
            self.astCtxt.iff(self.astCtxt.equal(self.astCtxt.bv(1, 8), self.astCtxt.bv(2, 8)), self.astCtxt.equal(self.astCtxt.bv(2, 8), self.astCtxt.bv(1, 8))),
        ]
        self.check_ast(tests)

    def test_logical(self):
        """Check logical operations."""
        T = self.astCtxt.bvtrue()
        F = self.astCtxt.bvfalse()
        tests = [
            self.astCtxt.land([T == T, F == F]),
            self.astCtxt.land([F == F, T == F]),
            self.astCtxt.land([T == F, F == T]),
            self.astCtxt.land([F == T, T == T]),
            self.astCtxt.lor([T == T, F == F]),
            self.astCtxt.lor([F == F, T == F]),
            self.astCtxt.lor([T == F, F == T]),
            self.astCtxt.lor([F == T, T == T]),
            self.astCtxt.lxor([T == T, F == F]),
            self.astCtxt.lxor([F == F, T == F]),
            self.astCtxt.lxor([T == F, F == T]),
            self.astCtxt.lxor([F == T, T == T]),
        ]
        self.check_ast(tests)

    def test_reference(self):
        """Check evaluation of reference node after variable update."""
        self.sv1 = self.Triton.newSymbolicVariable(8)
        self.v1 = self.astCtxt.variable(self.sv1)
        subnode = self.astCtxt.bvadd(self.v1, self.v1)
        expr = self.Triton.newSymbolicExpression(subnode)
        final_node = self.astCtxt.bvsub(self.astCtxt.reference(expr), self.astCtxt.bv(8, 8))
        self.Triton.setConcreteVariableValue(self.sv1, 10)
        trv = final_node.evaluate()
        self.assertEqual(trv, 12)
