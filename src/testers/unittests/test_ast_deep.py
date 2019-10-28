#!/usr/bin/env python2
# coding: utf-8
"""Test deep AST."""

import unittest
from triton import *

DEPTH = 1000



class TestDeep(unittest.TestCase):

    """Test deep AST."""

    def setUp(self):
        """Define the arch."""
        self.triton = TritonContext()
        self.triton.setArchitecture(ARCH.X86_64)
        self.ctx = self.triton.getAstContext()

        self.sym_var = self.ctx.variable(self.triton.symbolizeRegister(self.triton.registers.rax))
        self.triton.setConcreteRegisterValue(self.triton.registers.rbx, 0)

        add_inst = Instruction()
        add_inst.setAddress(0x100)
        add_inst.setOpcode(b"\x48\x01\xC3")      # add   rbx, rax

        sub_inst = Instruction()
        sub_inst.setOpcode(b"\x48\x29\xC3")      # sub   rbx, rax

        # We subtract and add the same symbolic value from rbx N times
        for _ in range(DEPTH):
            self.triton.processing(add_inst)
            sub_inst.setAddress(add_inst.getAddress() + add_inst.getSize())
            self.triton.processing(sub_inst)
            add_inst.setAddress(sub_inst.getAddress() + sub_inst.getSize())

        # And finally add symbolic variable ones
        add_inst.setAddress(add_inst.getAddress() + add_inst.getSize())
        self.triton.processing(add_inst)

        # Now rbx has `SymVar_0` value
        self.complex_ast_tree = self.triton.getSymbolicRegister(self.triton.registers.rbx).getAst()

    def test_z3_conversion(self):
        result = self.triton.simplify(self.complex_ast_tree, True)
        self.assertEqual(str(result), str(self.sym_var))

    def test_duplication(self):
        s = self.ctx.duplicate(self.complex_ast_tree)

    def test_symbolic_variable_update(self):
        self.triton.setConcreteVariableValue(self.sym_var.getSymbolicVariable(), 0xdeadbeaf)
        self.assertEqual(self.complex_ast_tree.evaluate(), 0xdeadbeaf)
