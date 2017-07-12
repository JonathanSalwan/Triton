#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Expression."""

import unittest
from triton import TritonContext, Instruction, ARCH, SYMEXPR, REG


class TestSymbolicExpression(unittest.TestCase):

    """Testing symbolic expression."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        self.inst1 = Instruction("\x48\x31\xd8") # xor rax, rbx
        self.ctx.setConcreteRegisterValue(self.ctx.registers.al, 0x10)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.bl, 0x55)

        self.inst2 = Instruction("\x48\x89\x03") # mov [rbx], rax

        self.ctx.processing(self.inst1)
        self.ctx.processing(self.inst2)

        self.expr1 = self.inst1.getSymbolicExpressions()[0]
        self.expr2 = self.inst2.getSymbolicExpressions()[8]

    def test_expressions(self):
        """Test expressions"""
        self.assertEqual(len(self.inst1.getSymbolicExpressions()), 7)

    def test_getAst(self):
        """Test getAst"""
        self.assertEqual(self.expr1.getAst().evaluate(), 0x45)

    def test_getComment(self):
        """Test getComment"""
        self.assertEqual(self.expr1.getComment(), "XOR operation")

    def test_getId(self):
        """Test getId"""
        self.assertEqual(self.expr1.getId(), 0)

    def test_getKind(self):
        """Test getKind"""
        self.assertEqual(self.expr1.getKind(), SYMEXPR.REG)
        self.assertEqual(self.expr2.getKind(), SYMEXPR.MEM)

    def test_getNewAst(self):
        """Test getNewAst"""
        self.assertTrue(self.expr1.getAst().equalTo(self.expr1.getNewAst()))

    def test_getOrigin(self):
        """Test getOrigin"""
        self.assertEqual(self.expr1.getOrigin().getId(), REG.X86_64.RAX)
        self.assertEqual(str(self.expr1.getOrigin()), "rax:64 bv[63..0]")
        self.assertEqual(str(self.expr2.getOrigin()), "[@0x55]:64 bv[63..0]")

    def test_isMemory(self):
        """Test isMemory"""
        self.assertFalse(self.expr1.isMemory())

    def test_isRegister(self):
        """Test isRegister"""
        self.assertTrue(self.expr1.isRegister())

    def test_isSymbolized(self):
        """Test isSymbolized"""
        self.assertFalse(self.expr1.isSymbolized())

    def test_isTainted(self):
        """Test isTainted"""
        self.assertFalse(self.expr1.isTainted())

    def test_setAst(self):
        """Test setAst"""
        self.expr1.setAst(self.ctx.getAstContext().bv(1, 64))
        self.assertEqual(str(self.expr1.getAst()), "(_ bv1 64)")

    def test_setComment(self):
        """Test setComment"""
        self.expr1.setComment("test")
        self.assertEqual(self.expr1.getComment(), "test")

