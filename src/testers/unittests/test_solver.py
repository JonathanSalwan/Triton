#!/usr/bin/env python3
# coding: utf-8
"""Test Solver."""

import unittest

from triton import *


class TestSolver(unittest.TestCase):

    """Testing the solver engine."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.X86_64)
        self.astCtxt = self.ctx.getAstContext()

    def solver_a_query(self):
        self.ctx.reset()
        self.ctx.symbolizeRegister(self.ctx.registers.rax, 'my_rax')
        self.ctx.processing(Instruction(b"\x48\x35\x34\x12\x00\x00")) # xor rax, 0x1234
        self.ctx.processing(Instruction(b"\x48\x89\xc1")) # xor rcx, rax
        rcx_expr = self.ctx.getSymbolicRegister(self.ctx.registers.rcx)
        model = self.ctx.getModel(rcx_expr.getAst() == 0xdead)
        self.assertEqual(model[0].getValue(), 0xcc99)
        return

    def test_setSolver(self):
        self.solver_a_query()
        self.ctx.setSolver(SOLVER.Z3)
        self.solver_a_query()
