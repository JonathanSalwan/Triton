#!/usr/bin/env python2
# coding: utf-8
"""Test AST reference."""

import unittest

from triton import TritonContext, ARCH


class TestAstReference(unittest.TestCase):

    """Testing the AST reference."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.astCtxt = self.Triton.getAstContext()

    def test_ssa_ref(self):
        v0   = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        v1   = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        exp0 = self.Triton.newSymbolicExpression(v0, "exp v1")
        exp1 = self.Triton.newSymbolicExpression(v1, "exp v2")
        ref0 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0))
        ref1 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(1))
        ref2 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0)) + 2
        ref3 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0)) + self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(1))

        self.assertEqual(str(ref0), "ref!0")
        self.assertEqual(str(ref1), "ref!1")
        self.assertEqual(str(ref2), "(bvadd ref!0 (_ bv2 8))")
        self.assertEqual(str(ref3), "(bvadd ref!0 ref!1)")

    def test_unroll_ssa_ref(self):
        v0   = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        v1   = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        exp0 = self.Triton.newSymbolicExpression(v0, "exp v1")
        exp1 = self.Triton.newSymbolicExpression(v1, "exp v2")
        ref0 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0))
        ref1 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(1))
        ref2 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0)) + 2
        ref3 = self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0)) + self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(1))

        self.assertEqual(str(self.astCtxt.unrollAst(ref0)), "SymVar_0")
        self.assertEqual(str(self.astCtxt.unrollAst(ref1)), "SymVar_1")
        self.assertEqual(str(self.astCtxt.unrollAst(ref2)), "(bvadd SymVar_0 (_ bv2 8))")
        self.assertEqual(str(self.astCtxt.unrollAst(ref3)), "(bvadd SymVar_0 SymVar_1)")

    def test_unroll_ssa_deep_ref(self):
        v0   = self.astCtxt.variable(self.Triton.newSymbolicVariable(8))
        exp0 = self.Triton.newSymbolicExpression(v0, "exp0")
        exp1 = self.Triton.newSymbolicExpression(self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(0)), "exp1")
        exp2 = self.Triton.newSymbolicExpression(self.astCtxt.reference(self.Triton.getSymbolicExpressionFromId(1)), "exp2")
        self.assertEqual(str(self.astCtxt.unrollAst(exp2.getAst())), "SymVar_0")
