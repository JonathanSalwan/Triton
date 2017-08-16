#!/usr/bin/env python2
# coding: utf-8
"""Test Path Constraint."""

import unittest
from triton import TritonContext, Instruction, ARCH, SYMEXPR


class TestPathConstraint(unittest.TestCase):

    """Testing path constraint."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

        trace = [
            "\x25\xff\xff\xff\x3f",      # and eax, 0x3fffffff
            "\x81\xe3\xff\xff\xff\x3f",  # and ebx, 0x3fffffff
            "\x31\xd1",                  # xor ecx, edx
            "\x31\xfa",                  # xor edx, edi
            "\x31\xD8",                  # xor eax, ebx
            "\x0F\x84\x55\x00\x00\x00",  # je 0x55
        ]

        self.ctx.convertRegisterToSymbolicVariable(self.ctx.registers.eax)
        self.ctx.convertRegisterToSymbolicVariable(self.ctx.registers.ebx)

        for opcodes in trace:
            self.ctx.processing(Instruction(opcodes))

    def test_getPathConstraintsAst(self):
        """Test getPathConstraintsAst"""
        astCtx = self.ctx.getAstContext()
        crst = self.ctx.getPathConstraintsAst()
        self.assertNotEqual(len(self.ctx.getModel(crst)), 0)
        self.assertNotEqual(len(self.ctx.getModel(astCtx.lnot(crst))), 0)

    def test_getPathConstraints(self):
        """Test getPathConstraints"""
        pco = self.ctx.getPathConstraints()
        self.assertEqual(len(pco), 1)

    def test_isMultipleBranches(self):
        pc = self.ctx.getPathConstraints()[0]
        self.assertTrue(pc.isMultipleBranches())

    def test_getTakenPathConstraintAst(self):
        pc = self.ctx.getPathConstraints()[0]
        self.assertEqual(pc.getTakenPathConstraintAst().evaluate(), 1)

    def test_getTakenAddress(self):
        pc = self.ctx.getPathConstraints()[0]
        self.assertEqual(pc.getTakenAddress(), 91)

    def test_getBranchConstraints(self):
        pc = self.ctx.getPathConstraints()[0].getBranchConstraints()

        self.assertTrue(pc[0]['isTaken'])
        self.assertFalse(pc[1]['isTaken'])

        self.assertEqual(pc[0]['srcAddr'], pc[1]['srcAddr'])

        self.assertEqual(pc[0]['dstAddr'], 91)
        self.assertEqual(pc[1]['dstAddr'], 23)

