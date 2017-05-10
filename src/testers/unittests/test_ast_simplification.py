#!/usr/bin/env python2
# coding: utf-8
"""Testing AST simplification."""

import unittest

from triton     import *
from triton.ast import *



class TestAstSimplification(unittest.TestCase):

    """Testing AST simplification."""

    def setUp(self):
        setArchitecture(ARCH.X86_64)
        addCallback(self.xor_1, CALLBACK.SYMBOLIC_SIMPLIFICATION)
        addCallback(self.xor_2, CALLBACK.SYMBOLIC_SIMPLIFICATION)

    def test_simplification(self):
        a = bv(1, 8)
        b = bv(2, 8)

        # Example 1
        c = a ^ a
        c = simplify(c)
        self.assertEqual(str(c), "(_ bv0 8)")

        c = a ^ b
        c = simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        c = (a & ~b) | (~a & b)
        c = simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme B
        c = (~b & a) | (~a & b)
        c = simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme C
        c = (~b & a) | (b & ~a)
        c = simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv1 8) (_ bv2 8))")

        # Example 2 - forme D
        c = (b & ~a) | (~b & a)
        c = simplify(c)
        self.assertEqual(str(c), "(bvxor (_ bv2 8) (_ bv1 8))")
        return

    # a ^ a -> a = 0
    @staticmethod
    def xor_1(node):
        if node.getKind() == AST_NODE.BVXOR:
            if node.getChilds()[0].equalTo(node.getChilds()[1]):
                return bv(0, node.getBitvectorSize())
        return node


    # ((a & ~b) | (~a & b)) -> (a ^ b)
    @staticmethod
    def xor_2(node):

        def getNot(node):
            a = node.getChilds()[0]
            b = node.getChilds()[1]
            if a.getKind() == AST_NODE.BVNOT and b.getKind() != AST_NODE.BVNOT:
                return a
            if b.getKind() == AST_NODE.BVNOT and a.getKind() != AST_NODE.BVNOT:
                return b
            return None

        def getNonNot(node):
            a = node.getChilds()[0]
            b = node.getChilds()[1]
            if a.getKind() != AST_NODE.BVNOT and b.getKind() == AST_NODE.BVNOT:
                return a
            if b.getKind() != AST_NODE.BVNOT and a.getKind() == AST_NODE.BVNOT:
                return b
            return None

        if node.getKind() == AST_NODE.BVOR:
            c1 = node.getChilds()[0]
            c2 = node.getChilds()[1]
            if c1.getKind() == AST_NODE.BVAND and c2.getKind() == AST_NODE.BVAND:
                c1_not    = getNot(c1)
                c2_not    = getNot(c2)
                c1_nonNot = getNonNot(c1)
                c2_nonNot = getNonNot(c2)
                if c1_not.equalTo(~c2_nonNot) and c2_not.equalTo(~c1_nonNot):
                    return c1_nonNot ^ c2_nonNot

        return node
