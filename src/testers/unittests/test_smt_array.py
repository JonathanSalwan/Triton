#!/usr/bin/env python3
# coding: utf-8
"""Test SMT Array."""

import unittest
from triton import *


class TestSMTArray(unittest.TestCase):

    """Testing SMT array."""

    def setUp(self):
        self.ctx      = TritonContext(ARCH.X86_64)
        self.ast      = self.ctx.getAstContext()
        self.cellvar  = self.ast.variable(self.ctx.newSymbolicVariable(8, 'cell var'))
        self.indexvar = self.ast.variable(self.ctx.newSymbolicVariable(64, 'index var'))
        self.mem      = self.ast.array(64)

    def test_load_store_eval(self):
        node = self.ast.select(self.mem, 10)
        # There is no value stored at index 10 yet
        self.assertEqual(node.evaluate(), 0)

        # We store 0xff at index 10 of mem
        self.mem = self.ast.store(self.mem, 10, self.ast.bv(0xff, 8))

        # We select the cell at index 10
        node = self.ast.select(self.mem, 10)
        self.assertEqual(node.evaluate(), 0xff)

        # With triton we allow the evaluation of store node
        node = self.ast.store(self.mem, 0x1000, self.ast.bv(0xde, 8))
        self.assertEqual(node.evaluate(), 0xde)
        self.assertEqual(node.getBitvectorSize(), 0) # An array do not have a size

    def test_store_index_symbolic(self):
        # We store 0xCC at a symbolic address
        self.mem = self.ast.store(self.mem, self.indexvar, self.ast.bv(0xcc, 8))
        # We select the mem cell at index 0xdead
        node = self.ast.select(self.mem, 0xdead)

        # We want to select the 0xcc constant
        model = self.ctx.getModel(node == 0xcc)
        self.assertEqual(model[1].getValue(), 0xdead)

        # We can't fetch the 0xff constant
        sat = self.ctx.isSat(node == 0xff)
        self.assertEqual(sat, False)

    def test_load_index_symbolic(self):
        # We store 0xCC at the 0x1000 address
        self.mem = self.ast.store(self.mem, 0x1000, self.ast.bv(0xcc, 8))
        # We select the mem cell at a symbolic address
        node = self.ast.select(self.mem, self.indexvar)

        # We want to select the 0xcc constant
        model = self.ctx.getModel(node == 0xcc)
        self.assertEqual(model[1].getValue(), 0x1000)

        # We can't fetch the 0xff constant
        sat = self.ctx.isSat(node == 0xff)
        self.assertEqual(sat, False)

    def test_store_cell_symbolic(self):
        # We store a "symbolic cell + 1" at 0xdead
        self.mem = self.ast.store(self.mem, 0xdead, self.cellvar + 1)
        # We select the mem cell at 0xdead
        node = self.ast.select(self.mem, 0xdead)

        # We want to select the 0xcc constant (var + 1 == 0xcc)
        model = self.ctx.getModel(node == 0xcc)
        self.assertEqual(model[0].getValue(), 0xcb)

    def test_bitwuzla_1(self):
        if VERSION.BITWUZLA_INTERFACE:
            self.ctx.setSolver(SOLVER.BITWUZLA)

            # We store 0xCC at a symbolic address
            self.mem = self.ast.store(self.mem, self.indexvar, self.ast.bv(0xcc, 8))
            # We select the mem cell at index 0xdead
            node = self.ast.select(self.mem, 0xdead)

            # We want to select the 0xcc constant
            model = self.ctx.getModel(node == 0xcc)
            self.assertEqual(model[1].getValue(), 0xdead)

            # We can't fetch the 0xff constant
            sat = self.ctx.isSat(node == 0xff)
            self.assertEqual(sat, False)

    def test_bitwuzla_2(self):
        if VERSION.BITWUZLA_INTERFACE:
            self.ctx.setSolver(SOLVER.BITWUZLA)

            # We store 0xCC at the 0x1000 address
            self.mem = self.ast.store(self.mem, 0x1000, self.ast.bv(0xcc, 8))
            # We select the mem cell at a symbolic address
            node = self.ast.select(self.mem, self.indexvar)

            # We want to select the 0xcc constant
            model = self.ctx.getModel(node == 0xcc)
            self.assertEqual(model[1].getValue(), 0x1000)

            # We can't fetch the 0xff constant
            sat = self.ctx.isSat(node == 0xff)
            self.assertEqual(sat, False)

    def test_bitwuzla_3(self):
        if VERSION.BITWUZLA_INTERFACE:
            self.ctx.setSolver(SOLVER.BITWUZLA)

            # We store a "symbolic cell + 1" at 0xdead
            self.mem = self.ast.store(self.mem, 0xdead, self.cellvar + 1)
            # We select the mem cell at 0xdead
            node = self.ast.select(self.mem, 0xdead)

            # We want to select the 0xcc constant (var + 1 == 0xcc)
            model = self.ctx.getModel(node == 0xcc)
            self.assertEqual(model[0].getValue(), 0xcb)

    def test_lift_to_dot(self):
        self.mem = self.ast.store(self.mem, 0xdead, self.cellvar + 1)
        node = self.ast.select(self.mem, 0xdead)
        self.assertNotEqual(len(self.ctx.liftToDot(node)), 0)

    def test_lift_to_llvm(self):
        if VERSION.LLVM_INTERFACE:
            self.mem = self.ast.store(self.mem, 0xdead, self.cellvar + 1)
            node = self.ast.select(self.mem, 0xdead)
            self.assertNotEqual(len(self.ctx.liftToLLVM(node)), 0)
