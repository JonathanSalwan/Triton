#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Variable."""

import unittest
from triton import TritonContext, Instruction, ARCH, REG, SYMEXPR


class TestSymbolicExpression(unittest.TestCase):

    """Testing symbolic expression."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        self.inst = Instruction("\x48\x31\xd8")
        self.ctx.setConcreteRegisterValue(self.ctx.Register(REG.X86_64.AL, 0x10))
        self.ctx.setConcreteRegisterValue(self.ctx.Register(REG.X86_64.BL, 0x55))
        self.ctx.processing(self.inst) # xor rax, rbx

        self.expr = self.inst.getSymbolicExpressions()[0]

    def test_expressions(self):
        """Test expressions"""
        self.assertEqual(len(self.inst.getSymbolicExpressions()), 7)

    def test_getAst(self):
        """Test getAst"""
        self.assertEqual(self.expr.getAst().evaluate(), 0x45)

    def test_getComment(self):
        """Test getComment"""
        self.assertEqual(self.expr.getComment(), "XOR operation")

    def test_getId(self):
        """Test getId"""
        self.assertEqual(self.expr.getId(), 0)

    def test_getKind(self):
        """Test getKind"""
        self.assertEqual(self.expr.getKind(), SYMEXPR.REG)

    def test_getNewAst(self):
        """Test getNewAst"""
        self.assertTrue(self.expr.getAst().equalTo(self.expr.getNewAst()))

    def test_getOrigin(self):
        """Test getOrigin"""
        self.assertEqual(self.expr.getOrigin().getId(), REG.X86_64.RAX)
        self.assertEqual(str(self.expr.getOrigin()), "rax:64 bv[63..0]")

    def test_isMemory(self):
        """Test isMemory"""
        self.assertFalse(self.expr.isMemory())

    def test_isRegister(self):
        """Test isRegister"""
        self.assertTrue(self.expr.isRegister())

    def test_isSymbolized(self):
        """Test isSymbolized"""
        self.assertFalse(self.expr.isSymbolized())

    def test_isTainted(self):
        """Test isTainted"""
        self.assertFalse(self.expr.isTainted())

    def test_setAst(self):
        """Test setAst"""
        self.expr.setAst(self.ctx.getAstContext().bv(1, 64))
        self.assertEqual(str(self.expr.getAst()), "(_ bv1 64)")

    def test_setComment(self):
        """Test setComment"""
        self.expr.setComment("test")
        self.assertEqual(self.expr.getComment(), "test")

