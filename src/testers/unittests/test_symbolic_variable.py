#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Variable."""

import unittest
from triton import *


class TestSymbolicVariable(unittest.TestCase):

    """Testing symbolic variable."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.v0 = self.ctx.newSymbolicVariable(8)
        self.v1 = self.ctx.newSymbolicVariable(16)
        self.v2 = self.ctx.newSymbolicVariable(32, "test com")
        self.v3 = self.ctx.newSymbolicVariable(32)
        self.v3.setAlias("v3")

    def test_id(self):
        """Test IDs"""
        self.assertEqual(self.v0.getId(), 0)
        self.assertEqual(self.v1.getId(), 1)
        self.assertEqual(self.v2.getId(), 2)

    def test_kind(self):
        """Test kind"""
        self.assertEqual(self.v0.getType(), SYMBOLIC.UNDEFINED_VARIABLE)
        self.assertEqual(self.v1.getType(), SYMBOLIC.UNDEFINED_VARIABLE)
        self.assertEqual(self.v2.getType(), SYMBOLIC.UNDEFINED_VARIABLE)

    def test_name(self):
        """Test name"""
        self.assertEqual(self.v0.getName(), "SymVar_0")
        self.assertEqual(self.v1.getName(), "SymVar_1")
        self.assertEqual(self.v2.getName(), "SymVar_2")

    def test_bitsize(self):
        """Test name"""
        self.assertEqual(self.v0.getBitSize(), 8)
        self.assertEqual(self.v1.getBitSize(), 16)
        self.assertEqual(self.v2.getBitSize(), 32)

    def test_comment(self):
        """Test comment"""
        self.assertEqual(self.v0.getComment(), "")
        self.assertEqual(self.v1.getComment(), "")
        self.assertEqual(self.v2.getComment(), "test com")

        self.v0.setComment("test v0")
        self.v1.setComment("test v1")

        self.assertEqual(self.v0.getComment(), "test v0")
        self.assertEqual(self.v1.getComment(), "test v1")
        self.assertEqual(self.v2.getComment(), "test com")

    def test_str(self):
        """Test variable representation"""
        self.assertEqual(str(self.v0), "SymVar_0:8")
        self.assertEqual(str(self.v1), "SymVar_1:16")
        self.assertEqual(str(self.v2), "SymVar_2:32")

    def test_alias(self):
        """Test alias"""
        self.assertEqual(self.v3.getName(), "SymVar_3")
        self.assertEqual(self.v3.getAlias(), "v3")
        self.assertEqual(str(self.v3), "v3:32")
        self.assertEqual(self.v3.getId(), 3)

    def test_model_with_alias(self):
        var = self.ctx.convertRegisterToSymbolicVariable(self.ctx.registers.rax)
        var.setAlias("rax")
        inst = Instruction("\x48\x31\xd8")
        self.ctx.processing(inst)

        ast = self.ctx.getAstContext()
        rax_ast = ast.unrollAst(self.ctx.getRegisterAst(self.ctx.registers.rax))
        model = self.ctx.getModel(rax_ast == 0x41)
        self.assertEqual(str(rax_ast), "(bvxor rax (_ bv0 64))")
        self.assertEqual(str(model[4]), "rax:64 = 0x41")
        self.assertEqual(str(model[4].getVariable()), "rax:64")
        self.assertEqual(str(model[4].getVariable().getName()), "SymVar_4")
        self.assertEqual(model[4].getVariable().getId(), 4)

        # Reset alias
        var.setAlias("")
        self.assertEqual(str(rax_ast), "(bvxor SymVar_4 (_ bv0 64))")
        self.assertEqual(str(model[4]), "SymVar_4:64 = 0x41")
        self.assertEqual(str(model[4].getVariable()), "SymVar_4:64")
        self.assertEqual(str(model[4].getVariable().getName()), "SymVar_4")
        self.assertEqual(str(model[4].getVariable().getAlias()), "")
        self.assertEqual(model[4].getVariable().getId(), 4)
