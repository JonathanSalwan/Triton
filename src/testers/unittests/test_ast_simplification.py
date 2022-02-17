#!/usr/bin/env python3
# coding: utf-8
"""Testing AST simplification."""

import unittest

from triton import *


class TestAstSimplification1(unittest.TestCase):

    """Testing AST simplification."""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.addCallback(CALLBACK.SYMBOLIC_SIMPLIFICATION, self.xor_1)
        self.ctx.addCallback(CALLBACK.SYMBOLIC_SIMPLIFICATION, self.xor_2)
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
        self.ctx.addCallback(CALLBACK.SYMBOLIC_SIMPLIFICATION, self.simplification_0)
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
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

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

    def test_mul3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.bv(1, 32)
        n = self.ast.bvmul(b, a)
        self.assertEqual(str(n), "SymVar_0")
        n = self.ast.bvmul(a, b)
        self.assertEqual(str(n), "SymVar_0")

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

    def test_extract_concat(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(8))
        n = self.ast.extract(7, 0, self.ast.concat([self.ast.bv(0, 24), a]))
        self.assertEqual(str(n), "SymVar_0")

    def test_extract_concat_2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(8))
        c = [self.ast.bv(1, 8), self.ast.bv(2, 8), self.ast.bv(3, 8), a]
        n = self.ast.extract(7, 0, self.ast.concat(c))
        self.assertEqual(str(n), "SymVar_0")
        n = self.ast.extract(15, 8, self.ast.concat(c))
        self.assertEqual(str(n), "(_ bv3 8)")
        n = self.ast.extract(23, 16, self.ast.concat(c))
        self.assertEqual(str(n), "(_ bv2 8)")
        n = self.ast.extract(31, 24, self.ast.concat(c))
        self.assertEqual(str(n), "(_ bv1 8)")
        n = self.ast.extract(8, 0, self.ast.concat(c))
        self.assertEqual(str(n), "((_ extract 8 0) (concat (_ bv1 8) (_ bv2 8) (_ bv3 8) SymVar_0))")
        n = self.ast.extract(12, 9, self.ast.concat(c))
        self.assertEqual(str(n), "((_ extract 4 1) (_ bv3 8))")
        n = self.ast.extract(17, 16, self.ast.concat(c))
        self.assertEqual(str(n), "((_ extract 1 0) (_ bv2 8))")
        n = self.ast.extract(31, 30, self.ast.concat(c))
        self.assertEqual(str(n), "((_ extract 7 6) (_ bv1 8))")

    def test_extract_concat_3(self):
        c1 = self.ast.concat([self.ast.bv(1, 8), self.ast.bv(2, 24)])
        c2 = self.ast.concat([c1, self.ast.bv(3, 32)])
        c = [self.ast.bv(4, 8), c2, self.ast.bv(5, 8)]
        n = self.ast.extract(43, 41, self.ast.concat(c))
        self.assertEqual(str(n), "((_ extract 3 1) (_ bv2 24))")

    def test_extract_concat_real(self):
        self.ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.ctx.symbolizeRegister(self.ctx.getRegister(REG.X86.EAX), "eax")
        code = [
            b"\xb0\x00",                  # mov al, 0x00
            b"\x84\xc0",                  # test al, al
            b"\x0f\x84\xe9\xbe\xad\xde",  # jz 0xdeadbeef
        ]
        addr = 0x400000
        for opcode in code:
            inst = Instruction(addr, opcode)
            self.ctx.processing(inst)
            addr += len(opcode)
        self.assertEqual(len(self.ctx.getPathConstraints()), 0)

    def test_extract_extract(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.extract(4, 2, self.ast.extract(18, 5, a))
        self.assertEqual(str(n), "((_ extract 9 7) SymVar_0)")

    def test_extract_ref(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(8))
        c = self.ast.concat([self.ast.bv(0, 24), a])
        r1 = self.ast.reference(self.ctx.newSymbolicExpression(c, "r1"))
        r2 = self.ast.reference(self.ctx.newSymbolicExpression(r1, "r2"))
        n = self.ast.extract(7, 0, r2)
        self.assertEqual(str(n), "SymVar_0")


class TestAstSimplification5(unittest.TestCase):

    """Testing AST simplification"""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    def test_extract_zx(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        zx = self.ast.zx(32, a)
        n = self.ast.extract(31, 0, zx)
        self.assertEqual(str(n), "SymVar_0")
        n = self.ast.extract(30, 0, zx)
        self.assertEqual(str(n), "((_ extract 30 0) SymVar_0)")

    def test_extract_zx_real(self):
        self.ctx.symbolizeRegister(self.ctx.getRegister(REG.X86_64.EAX), "eax")
        addr = 0x400000
        code = [
            b"\x89\xc3",  # mov ebx, eax
            b"\x89\xd9",  # mov ecx, ebx
        ]
        for opcode in code:
            inst = Instruction(addr, opcode)
            self.ctx.processing(inst)
            addr += len(opcode)
        ecx = self.ctx.getRegister(REG.X86_64.ECX)
        self.assertEqual(str(self.ctx.getRegisterAst(ecx)), "eax")

    def test_extract_sx(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        sx = self.ast.sx(32, a)
        n = self.ast.extract(31, 0, sx)
        self.assertEqual(str(n), "SymVar_0")
        n = self.ast.extract(30, 0, sx)
        self.assertEqual(str(n), "((_ extract 30 0) SymVar_0)")

    def test_concat_extract(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.concat([self.ast.extract(31, 24, a), self.ast.extract(23, 16, a),
                             self.ast.extract(15, 8, a), self.ast.extract(7, 0, a)])
        self.assertEqual(str(n), "SymVar_0")

    def test_concat_extract_2(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        e = self.ast.extract(15, 8, a)
        r = self.ast.reference(self.ctx.newSymbolicExpression(e, "r"))
        n = self.ast.concat([self.ast.extract(31, 24, a), self.ast.extract(23, 16, a),
                             r, self.ast.extract(7, 0, a)])
        self.assertEqual(str(n), "SymVar_0")

    def test_concat_extract_3(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        e = self.ast.extract(15, 8, a)
        r = self.ast.reference(self.ctx.newSymbolicExpression(e, "r"))
        c1 = self.ast.concat([self.ast.extract(31, 24, a), self.ast.extract(23, 16, a)])
        c2 = self.ast.concat([r, self.ast.extract(7, 0, a)])
        n = self.ast.concat([c1, c2])
        self.assertEqual(str(n), "SymVar_0")

    def test_concat_extract_4(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.concat([self.ast.extract(23, 16, a), self.ast.extract(15, 8, a)])
        self.assertEqual(str(n), "((_ extract 23 8) SymVar_0)")

    def test_concat_extract_intersection(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.concat([self.ast.extract(31, 24, a), self.ast.extract(27, 26, a),
                             self.ast.extract(23, 16, a), self.ast.extract(15, 8, a),
                             self.ast.extract(7, 0, a)])
        self.assertEqual(str(n), ("(concat ((_ extract 31 24) SymVar_0) "
                                  "((_ extract 27 26) SymVar_0) "
                                  "((_ extract 23 16) SymVar_0) "
                                  "((_ extract 15 8) SymVar_0) "
                                  "((_ extract 7 0) SymVar_0))"))

    def test_concat_extract_order(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        n = self.ast.concat([self.ast.extract(15, 0, a), self.ast.extract(31, 16, a)])
        self.assertEqual(str(n), "(concat ((_ extract 15 0) SymVar_0) ((_ extract 31 16) SymVar_0))")

    def test_ite(self):
        a = self.ast.variable(self.ctx.newSymbolicVariable(32))
        b = self.ast.variable(self.ctx.newSymbolicVariable(32))
        c = self.ast.bv(0, 1)
        n = self.ast.ite(c, a, b)
        self.assertEqual(str(n), "SymVar_1")
        c = self.ast.bv(1, 1)
        n = self.ast.ite(c, a, b)
        self.assertEqual(str(n), "SymVar_0")

    def test_issue_1002(self):
        # See #1002
        inst = Instruction(b"\x29\xca")
        self.ctx.processing(inst)
        self.assertEqual("\n".join(str(e) for e in inst.getSymbolicExpressions()),
            ("(define-fun ref!0 () (_ BitVec 32) (_ bv0 32)) ; Extended part - SUB operation\n"
             "(define-fun ref!1 () (_ BitVec 64) ((_ zero_extend 32) ref!0)) ; SUB operation\n"
             "(define-fun ref!2 () (_ BitVec 1) (_ bv0 1)) ; Adjust flag\n"
             "(define-fun ref!3 () (_ BitVec 1) ((_ extract 31 31) (_ bv0 32))) ; Carry flag\n"
             "(define-fun ref!4 () (_ BitVec 1) ((_ extract 31 31) (_ bv0 32))) ; Overflow flag\n"
             "(define-fun ref!5 () (_ BitVec 1) (_ bv1 1)) ; Parity flag\n"
             "(define-fun ref!6 () (_ BitVec 1) ((_ extract 31 31) ref!1)) ; Sign flag\n"
             "(define-fun ref!7 () (_ BitVec 1) (_ bv1 1)) ; Zero flag\n"
             "(define-fun ref!8 () (_ BitVec 64) (_ bv2 64)) ; Program Counter"))

    def test_issue_1002_2(self):
        # See #1002
        inst = Instruction(b"\x48\x29\x0a")
        self.ctx.processing(inst)
        self.assertEqual("\n".join(str(e) for e in inst.getSymbolicExpressions()),
            ("(define-fun ref!0 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!1 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!2 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!3 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!4 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!5 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!6 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!7 () (_ BitVec 8) (_ bv0 8)) ; Byte reference - SUB operation\n"
             "(define-fun ref!8 () (_ BitVec 64) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8))) ; Temporary concatenation reference - SUB operation\n"
             "(define-fun ref!9 () (_ BitVec 1) (_ bv0 1)) ; Adjust flag\n"
             "(define-fun ref!10 () (_ BitVec 1) ((_ extract 63 63) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)))) ; Carry flag\n"
             "(define-fun ref!11 () (_ BitVec 1) ((_ extract 63 63) (_ bv0 64))) ; Overflow flag\n"
             "(define-fun ref!12 () (_ BitVec 1) (_ bv1 1)) ; Parity flag\n"
             "(define-fun ref!13 () (_ BitVec 1) ((_ extract 63 63) ref!8)) ; Sign flag\n"
             "(define-fun ref!14 () (_ BitVec 1) (_ bv1 1)) ; Zero flag\n"
             "(define-fun ref!15 () (_ BitVec 64) (_ bv3 64)) ; Program Counter"))


class TestAstSimplificationLLVM(unittest.TestCase):
    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

    def test_1(self):
        if VERSION.LLVM_INTERFACE is True:
            x = self.ast.variable(self.ctx.newSymbolicVariable(8, 'x'))
            y = self.ast.variable(self.ctx.newSymbolicVariable(8, 'y'))
            n = (x & ~y) | (~x & y)
            o = self.ctx.simplify(n, llvm=True)
            r = str(o) == "(bvxor y x)" or str(o) == "(bvxor x y)"
            self.assertTrue(r)
        return
