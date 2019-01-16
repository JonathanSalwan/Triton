#!/usr/bin/env python2
# coding: utf-8
"""Testing AST simplification."""

import unittest

from triton import *


class TestAstSimplification1(unittest.TestCase):

    """Testing AST simplification."""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.addCallback(self.xor_1, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        self.ctx.addCallback(self.xor_2, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        self.astCtxt = self.ctx.getAstContext()

    def test_simplification(self):
        a = self.astCtxt.bv(1, 8)
        b = self.astCtxt.bv(2, 8)

        # Example 1
        c = a ^ a
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(_ bv0 8)")

        c = a ^ b
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        c = (a & ~b) | (~a & b)
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme B
        c = (~b & a) | (~a & b)
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme C
        c = (~b & a) | (b & ~a)
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme D
        c = (b & ~a) | (~b & a)
        c = self.ctx.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv2 8) (_ bv1 8))")
        return

    # a ^ a -> a = 0
    @staticmethod
    def xor_1(api, node):
        if node.getType() == AST_NODE.BVXOR:
            if node.getChildren()[0].equalTo(node.getChildren()[1]):
                return api.getAstContext().bv(0, node.getBitvectorSize())
        return node


    # ((a & ~b) | (~a & b)) -> (a ^ b)
    @staticmethod
    def xor_2(api, node):

        def getNot(node):
            a = node.getChildren()[0]
            b = node.getChildren()[1]
            if a.getType() == AST_NODE.BVNOT and b.getType() != AST_NODE.BVNOT:
                return a
            if b.getType() == AST_NODE.BVNOT and a.getType() != AST_NODE.BVNOT:
                return b
            return None

        def getNonNot(node):
            a = node.getChildren()[0]
            b = node.getChildren()[1]
            if a.getType() != AST_NODE.BVNOT and b.getType() == AST_NODE.BVNOT:
                return a
            if b.getType() != AST_NODE.BVNOT and a.getType() == AST_NODE.BVNOT:
                return b
            return None

        if node.getType() == AST_NODE.BVOR:
            c1 = node.getChildren()[0]
            c2 = node.getChildren()[1]
            if c1.getType() == AST_NODE.BVAND and c2.getType() == AST_NODE.BVAND:
                c1_not    = getNot(c1)
                c2_not    = getNot(c2)
                c1_nonNot = getNonNot(c1)
                c2_nonNot = getNonNot(c2)
                if c1_not.equalTo(~c2_nonNot) and c2_not.equalTo(~c1_nonNot):
                    return c1_nonNot ^ c2_nonNot

        return node


class TestAstSimplification2(unittest.TestCase):

    """Testing AST simplification. From #740."""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.addCallback(self.simplification_0, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        self.astCtxt = self.ctx.getAstContext()

    def test_simplification(self):
        #  (bvadd
        #    (bvadd
        #        (bvsub SymVar_2 (_ bv2142533311 64))
        #        (_ bv1 64)
        #    )
        #    (_ bv2142533311 64)
        #  )
        a = self.astCtxt.bv(1, 64)
        b = self.astCtxt.bv(2142533311, 64)
        c = self.astCtxt.variable(self.ctx.newSymbolicVariable(64))
        node = (((c - b) + a) + b)
        snode = self.ctx.simplify(node)
        self.assertEqual(node.getType(), AST_NODE.BVADD)
        self.assertEqual(node.getChildren()[0], c)
        self.assertEqual(node.getChildren()[1], a)

    @staticmethod
    def simplification_0(ctx, node):
        # (((var - val1) + val2) + val1) => (var + val2)
        if node.getType() == AST_NODE.BVADD:
            c0 = node.getChildren()[0] # ((var + val1) + val2)
            c1 = node.getChildren()[1] # val1
            if c0.getType() == AST_NODE.BVADD and c1.getType() == AST_NODE.BV:
                c00 = c0.getChildren()[0] # (var + val1)
                c01 = c0.getChildren()[1] # val2
                # ((var + val1) + val2)
                if c00.getType() == AST_NODE.BVSUB and c01.getType() == AST_NODE.BV:
                        c000 = c00.getChildren()[0] # var
                        c001 = c00.getChildren()[1] # val1
                        # (var + val1)
                        if c001.getType() == AST_NODE.BV and c001.evaluate() == c1.evaluate():
                            # return (var + val2)
                            return c000 + c01
        return node


class TestAstSimplification3(unittest.TestCase):

    """Testing AST simplification"""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)
        self.ast = self.ctx.getAstContext()

    def proof(self, n):
        if self.ctx.isSat(self.ast.lnot(n)) == True:
            return False
        return True

    def test_add1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvadd(a, b)
        self.assertTrue(self.proof(n == a))

    def test_add2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvadd(b, a)
        self.assertTrue(self.proof(n == a))

    def test_and1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvand(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_and2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvand(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_and3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvand(b, a)
        self.assertTrue(self.proof(n == a))

    def test_and4(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvand(a, b)
        self.assertTrue(self.proof(n == a))

    def test_and5(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvand(a, a)
        self.assertTrue(self.proof(n == a))

    def test_ashr1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvashr(a, b)
        self.assertTrue(self.proof(n == a))

    def test_ashr2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvashr(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_lshr1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvlshr(a, b)
        self.assertTrue(self.proof(n == a))

    def test_lshr2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvlshr(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_lshr3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(32, 32)
        n = self.ast.bvlshr(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_mul1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvmul(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_mul2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvmul(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_or1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvor(b, a)
        self.assertTrue(self.proof(n == a))

    def test_or2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvor(a, b)
        self.assertTrue(self.proof(n == a))

    def test_or3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvor(a, b)
        self.assertTrue(self.proof(n == -1))

    def test_or4(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvor(b, a)
        self.assertTrue(self.proof(n == -1))

    def test_or5(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvor(a, a)
        self.assertTrue(self.proof(n == a))

    def test_sdiv1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(1, 32)
        n = self.ast.bvsdiv(a, b)
        self.assertTrue(self.proof(n == a))

    def test_shl1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvshl(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_shl2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvshl(a, b)
        self.assertTrue(self.proof(n == a))

    def test_shl3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(33, 32)
        n = self.ast.bvshl(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_sub1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvsub(a, b)
        self.assertTrue(self.proof(n == a))

    def test_sub2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvsub(b, a)
        self.assertTrue(self.proof(n == -a))

    def test_sub3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvsub(a, a)
        self.assertTrue(self.proof(n == 0))

    def test_udiv(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(1, 32)
        n = self.ast.bvudiv(a, b)
        self.assertTrue(self.proof(n == a))

    def test_xor1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvxor(a, b)
        self.assertTrue(self.proof(n == a))

    def test_xor2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvxor(b, a)
        self.assertTrue(self.proof(n == a))

    def test_xor3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvxor(a, a)
        self.assertTrue(self.proof(n == 0))


class TestAstSimplification4(unittest.TestCase):

    """Testing AST simplification"""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)
        self.ast = self.ctx.getAstContext()
        self.ctx.enableMode(MODE.AST_OPTIMIZATIONS, True)

    def proof(self, n):
        if self.ctx.isSat(self.ast.lnot(n)) == True:
            return False
        return True

    def test_add1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvadd(a, b)
        self.assertTrue(self.proof(n == a))

    def test_add2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvadd(b, a)
        self.assertTrue(self.proof(n == a))

    def test_and1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvand(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_and2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvand(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_and3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvand(b, a)
        self.assertTrue(self.proof(n == a))

    def test_and4(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvand(a, b)
        self.assertTrue(self.proof(n == a))

    def test_and5(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvand(a, a)
        self.assertTrue(self.proof(n == a))

    def test_ashr1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvashr(a, b)
        self.assertTrue(self.proof(n == a))

    def test_ashr2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvashr(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_lshr1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvlshr(a, b)
        self.assertTrue(self.proof(n == a))

    def test_lshr2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvlshr(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_lshr3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(32, 32)
        n = self.ast.bvlshr(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_mul1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvmul(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_mul2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvmul(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_or1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvor(b, a)
        self.assertTrue(self.proof(n == a))

    def test_or2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvor(a, b)
        self.assertTrue(self.proof(n == a))

    def test_or3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvor(a, b)
        self.assertTrue(self.proof(n == -1))

    def test_or4(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(-1, 32)
        n = self.ast.bvor(b, a)
        self.assertTrue(self.proof(n == -1))

    def test_or5(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvor(a, a)
        self.assertTrue(self.proof(n == a))

    def test_sdiv1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(1, 32)
        n = self.ast.bvsdiv(a, b)
        self.assertTrue(self.proof(n == a))

    def test_shl1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvshl(b, a)
        self.assertTrue(self.proof(n == 0))

    def test_shl2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvshl(a, b)
        self.assertTrue(self.proof(n == a))

    def test_shl3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(33, 32)
        n = self.ast.bvshl(a, b)
        self.assertTrue(self.proof(n == 0))

    def test_sub1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvsub(a, b)
        self.assertTrue(self.proof(n == a))

    def test_sub2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvsub(b, a)
        self.assertTrue(self.proof(n == -a))

    def test_sub3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvsub(a, a)
        self.assertTrue(self.proof(n == 0))

    def test_udiv(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(1, 32)
        n = self.ast.bvudiv(a, b)
        self.assertTrue(self.proof(n == a))

    def test_xor1(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvxor(a, b)
        self.assertTrue(self.proof(n == a))

    def test_xor2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(0, 32)
        n = self.ast.bvxor(b, a)
        self.assertTrue(self.proof(n == a))

    def test_xor3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.bvxor(a, a)
        self.assertTrue(self.proof(n == 0))
