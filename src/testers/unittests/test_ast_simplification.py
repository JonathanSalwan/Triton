#!/usr/bin/env python2
# coding: utf-8
"""Testing AST simplification."""

import unittest

from triton import ARCH, TritonContext, CALLBACK, AST_NODE


class TestAstSimplification(unittest.TestCase):

    """Testing AST simplification."""

    def setUp(self):
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.addCallback(self.xor_1, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        self.Triton.addCallback(self.xor_2, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        self.astCtxt = self.Triton.getAstContext()

    def test_simplification(self):
        a = self.astCtxt.bv(1, 8)
        b = self.astCtxt.bv(2, 8)

        # Example 1
        c = a ^ a
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(_ bv0 8)")

        c = a ^ b
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        c = (a & ~b) | (~a & b)
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme B
        c = (~b & a) | (~a & b)
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme C
        c = (~b & a) | (b & ~a)
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme D
        c = (b & ~a) | (~b & a)
        c = self.Triton.simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv2 8) (_ bv1 8))")
        return

    # a ^ a -> a = 0
    @staticmethod
    def xor_1(api, node):
        if node.getKind() == AST_NODE.BVXOR:
            if node.getChildren()[0].equalTo(node.getChildren()[1]):
                return api.getAstContext().bv(0, node.getBitvectorSize())
        return node


    # ((a & ~b) | (~a & b)) -> (a ^ b)
    @staticmethod
    def xor_2(api, node):

        def getNot(node):
            a = node.getChildren()[0]
            b = node.getChildren()[1]
            if a.getKind() == AST_NODE.BVNOT and b.getKind() != AST_NODE.BVNOT:
                return a
            if b.getKind() == AST_NODE.BVNOT and a.getKind() != AST_NODE.BVNOT:
                return b
            return None

        def getNonNot(node):
            a = node.getChildren()[0]
            b = node.getChildren()[1]
            if a.getKind() != AST_NODE.BVNOT and b.getKind() == AST_NODE.BVNOT:
                return a
            if b.getKind() != AST_NODE.BVNOT and a.getKind() == AST_NODE.BVNOT:
                return b
            return None

        if node.getKind() == AST_NODE.BVOR:
            c1 = node.getChildren()[0]
            c2 = node.getChildren()[1]
            if c1.getKind() == AST_NODE.BVAND and c2.getKind() == AST_NODE.BVAND:
                c1_not    = getNot(c1)
                c2_not    = getNot(c2)
                c1_nonNot = getNonNot(c1)
                c2_nonNot = getNonNot(c2)
                if c1_not.equalTo(~c2_nonNot) and c2_not.equalTo(~c1_nonNot):
                    return c1_nonNot ^ c2_nonNot

        return node
