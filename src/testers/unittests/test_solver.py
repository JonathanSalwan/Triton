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

    def solve_a_query(self):
        self.ctx.reset()
        self.ctx.symbolizeRegister(self.ctx.registers.rax, 'my_rax')
        self.ctx.processing(Instruction(b"\x48\x35\x34\x12\x00\x00")) # xor rax, 0x1234
        self.ctx.processing(Instruction(b"\x48\x89\xc1")) # xor rcx, rax
        rcx_expr = self.ctx.getSymbolicRegister(self.ctx.registers.rcx)
        models, status, time = self.ctx.getModels(rcx_expr.getAst() == 0xdead, 10, status=True, timeout=5000)
        self.assertEqual(status, SOLVER_STATE.SAT)          # must be SAT
        self.assertEqual(len(models), 1)                    # Only one possible model
        self.assertEqual(models[0][0].getValue(), 0xcc99)   # The correct model
        return

    def test_setSolver(self):
        # Test if Z3 has been enabled
        if 'Z3' in dir(SOLVER):
            self.solve_a_query()
            self.ctx.setSolver(SOLVER.Z3)
            self.solve_a_query()

        # Test if BITWUZLA has been enabled
        if 'BITWUZLA' in dir(SOLVER):
            self.solve_a_query()
            self.ctx.setSolver(SOLVER.BITWUZLA)
            self.solve_a_query()
