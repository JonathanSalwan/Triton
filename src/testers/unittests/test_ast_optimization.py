#!/usr/bin/env python2
# coding: utf-8
"""Testing AST optimization."""

import unittest

from triton import ARCH, TritonContext


class TestAstOptimization(unittest.TestCase):

    """Testing AST optimization."""

    def setUp(self):
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86)
        self.ctx = self.Triton.getAstContext()

    def test_add_zero(self):
        a = self.ctx.bv(2, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvadd(a, b)
        self.assertEqual(c, a)

    def test_and_zero(self):
        a = self.ctx.bv(2, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvand(a, b)
        self.assertEqual(c, b)

    def test_and_neg1(self):
        a = self.ctx.bv(2345, 32)
        b = self.ctx.bv(0xffffffff, 32)
        c = self.ctx.bvand(a, b)
        self.assertEqual(c, a)

    def test_ashr_zero(self):
        a = self.ctx.bv(0, 32)
        b = self.ctx.bv(2, 32)
        c = self.ctx.bvashr(a, b)
        self.assertEqual(c, a)

    def test_ashr_by_zero(self):
        a = self.ctx.bv(2, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvashr(a, b)
        self.assertEqual(c, a)

    def test_lshr_zero(self):
        a = self.ctx.bv(0, 32)
        b = self.ctx.bv(12, 32)
        c = self.ctx.bvlshr(a, b)
        self.assertEqual(c, a)

    def test_lshr_by_zero(self):
        a = self.ctx.bv(234, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvlshr(a, b)
        self.assertEqual(c, a)

    def test_lshr_too_much(self):
        a = self.ctx.bv(234, 32)
        b = self.ctx.bv(32, 32)
        c = self.ctx.bvlshr(a, b)
        self.assertEqual(c, self.ctx.bv(0, 32))

    def test_mult_with_zero(self):
        a = self.ctx.bv(0, 32)
        b = self.ctx.bv(2, 32)
        c = self.ctx.bvmul(a, b)
        self.assertEqual(c, a)

    def test_mult_with_1(self):
        a = self.ctx.bv(1, 32)
        b = self.ctx.bv(111, 32)
        c = self.ctx.bvmul(a, b)
        self.assertEqual(c, b)

    def test_or_with_zero(self):
        a = self.ctx.bv(0, 32)
        b = self.ctx.bv(34, 32)
        c = self.ctx.bvor(a, b)
        self.assertEqual(c, b)

    def test_or_neg1(self):
        a = self.ctx.bv(111, 32)
        b = self.ctx.bv(0xffffffff, 32)
        c = self.ctx.bvor(a, b)
        self.assertEqual(c, b)

    def test_rol_by_xlength(self):
        a = 64
        b = self.ctx.bv(465, 32)
        c = self.ctx.bvrol(a, b)
        self.assertEqual(c, b)

    def test_ror_by_xlength(self):
        a = 64
        b = self.ctx.bv(465, 32)
        c = self.ctx.bvror(a, b)
        self.assertEqual(c, b)

    def test_sdiv_by_1(self):
        a = self.ctx.bv(234, 32)
        b = self.ctx.bv(1, 32)
        c = self.ctx.bvsdiv(a, b)
        self.assertEqual(c, a)

    def test_shl_zero(self):
        a = self.ctx.bv(0, 32)
        b = self.ctx.bv(2, 32)
        c = self.ctx.bvshl(a, b)
        self.assertEqual(c, a)

    def test_shl_by_zero(self):
        a = self.ctx.bv(2, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvshl(a, b)
        self.assertEqual(c, a)

    def test_shl_too_many(self):
        a = self.ctx.bv(2, 32)
        b = self.ctx.bv(32, 32)
        c = self.ctx.bvshl(a, b)
        self.assertEqual(c, self.ctx.bv(0, 32))

    def test_sub_zero(self):
        a = self.ctx.bv(23, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvsub(a, b)
        self.assertEqual(c, a)

    def test_udiv_by_1(self):
        a = self.ctx.bv(1251, 32)
        b = self.ctx.bv(1, 32)
        c = self.ctx.bvudiv(a, b)
        self.assertEqual(c, a)

    def test_urem_1(self):
        a = self.ctx.bv(2346, 32)
        b = self.ctx.bv(1, 32)
        c = self.ctx.bvurem(a, b)
        self.assertEqual(c, self.ctx.bv(0, 32))

    def test_xor_zero(self):
        a = self.ctx.bv(24, 32)
        b = self.ctx.bv(0, 32)
        c = self.ctx.bvxor(a, b)
        self.assertEqual(c, a)
        pass

    def test_extract_full(self):
        a = 31
        b = 0
        c = self.ctx.bv(1235, 32)
        d = self.ctx.extract(a, b, c)
        self.assertEqual(d, c)

    def test_sx_zero(self):
        a = 0
        b = self.ctx.bv(234, 32)
        c = self.ctx.sx(a, b)
        self.assertEqual(c, b)

    def test_zx_zero(self):
        a = 0
        b = self.ctx.bv(234, 32)
        c = self.ctx.zx(a, b)
        self.assertEqual(c, b)
