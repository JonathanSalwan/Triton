#!/usr/bin/env python3
# coding: utf-8
"""Test Solvers."""

import unittest

from triton import *


class TestSolvers(unittest.TestCase):

    """Testing the solver engines."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

    def solve_a_query(self, solver):
        self.ctx.reset()
        self.ctx.setSolver(solver)
        self.ctx.symbolizeRegister(self.ctx.registers.rax, 'my_rax')
        self.ctx.processing(Instruction(b"\x48\x35\x34\x12\x00\x00")) # xor rax, 0x1234
        self.ctx.processing(Instruction(b"\x48\x89\xc1")) # xor rcx, rax
        rcx_expr = self.ctx.getSymbolicRegister(self.ctx.registers.rcx)
        constraint = rcx_expr.getAst() == 0xdead

        # Testing isSat()
        self.assertEqual(self.ctx.isSat(constraint), True)

        # Testing getModels() with status and timeout
        models, status, time = self.ctx.getModels(constraint, 10, status=True, timeout=5000)
        self.assertEqual(status, SOLVER_STATE.SAT)          # must be SAT
        self.assertEqual(len(models), 1)                    # Only one possible model
        self.assertEqual(models[0][0].getValue(), 0xcc99)   # The correct model

        # Testing getModel() with status and timeout
        models, status, time = self.ctx.getModel(constraint, status=True, timeout=5000)
        self.assertEqual(status, SOLVER_STATE.SAT)          # must be SAT
        self.assertEqual(models[0].getValue(), 0xcc99)      # The correct model

        return

    def test_solvers(self):
        # Test if Z3 has been enabled
        if 'Z3' in dir(SOLVER):
            self.solve_a_query(SOLVER.Z3)

        # Test if BITWUZLA has been enabled
        if 'BITWUZLA' in dir(SOLVER):
            self.solve_a_query(SOLVER.BITWUZLA)
