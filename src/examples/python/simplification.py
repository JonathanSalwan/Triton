#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./simplification.py
##  Expr:  (bvxor (_ bv1 8) (_ bv1 8))
##  Simp:  (_ bv0 8)
##
##  Expr:  (bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))
##  Simp:  (bvxor (_ bv1 8) (_ bv2 8))
##
##  Expr:  (bvor (bvand (bvnot (_ bv2 8)) (_ bv1 8)) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))
##  Simp:  (bvxor (_ bv1 8) (_ bv2 8))
##
##  Expr:  (bvor (bvand (bvnot (_ bv2 8)) (_ bv1 8)) (bvand (_ bv2 8) (bvnot (_ bv1 8))))
##  Simp:  (bvxor (_ bv1 8) (_ bv2 8))
##
##  Expr:  (bvor (bvand (_ bv2 8) (bvnot (_ bv1 8))) (bvand (bvnot (_ bv2 8)) (_ bv1 8)))
##  Simp:  (bvxor (_ bv2 8) (_ bv1 8))
##

import sys

from triton import TritonContext, AST_NODE, CALLBACK, ARCH

Triton = TritonContext()


# a ^ a -> a = 0
def xor_1(api, node):
    if node.getKind() == AST_NODE.BVXOR:
        if node.getChildren()[0].equalTo(node.getChildren()[1]):
            return api.getAstContext().bv(0, node.getBitvectorSize())
    return node


# ((a & ~b) | (~a & b)) -> (a ^ b)
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


if __name__ == "__main__":

    # Set arch to init engines
    Triton.setArchitecture(ARCH.X86_64)

    # Record simplifications
    Triton.addCallback(xor_1, CALLBACK.SYMBOLIC_SIMPLIFICATION)
    Triton.addCallback(xor_2, CALLBACK.SYMBOLIC_SIMPLIFICATION)

    astCtxt = Triton.getAstContext()

    a = astCtxt.bv(1, 8)
    b = astCtxt.bv(2, 8)

    # Example 1
    c = a ^ a
    print 'Expr: ', c
    c = Triton.simplify(c)
    print 'Simp: ', c

    print

    # Example 2 - forme A
    c = (a & ~b) | (~a & b)
    print 'Expr: ', c
    c = Triton.simplify(c)
    print 'Simp: ', c

    print

    # Example 2 - forme B
    c = (~b & a) | (~a & b)
    print 'Expr: ', c
    c = Triton.simplify(c)
    print 'Simp: ', c

    print

    # Example 2 - forme C
    c = (~b & a) | (b & ~a)
    print 'Expr: ', c
    c = Triton.simplify(c)
    print 'Simp: ', c

    print

    # Example 2 - forme D
    c = (b & ~a) | (~b & a)
    print 'Expr: ', c
    c = Triton.simplify(c)
    print 'Simp: ', c

    sys.exit(0)

