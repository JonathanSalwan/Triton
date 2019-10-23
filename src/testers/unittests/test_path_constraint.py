#!/usr/bin/env python2
# coding: utf-8
"""Test Path Constraint."""

import unittest
from triton import *


class TestPathConstraint(unittest.TestCase):

    """Testing path constraint."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

        trace = [
            b"\x25\xff\xff\xff\x3f",      # and eax, 0x3fffffff
            b"\x81\xe3\xff\xff\xff\x3f",  # and ebx, 0x3fffffff
            b"\x31\xd1",                  # xor ecx, edx
            b"\x31\xfa",                  # xor edx, edi
            b"\x31\xD8",                  # xor eax, ebx
            b"\x0F\x84\x55\x00\x00\x00",  # je 0x55
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.eax)
        self.ctx.symbolizeRegister(self.ctx.registers.ebx)

        for opcodes in trace:
            self.ctx.processing(Instruction(opcodes))

    def test_getPathPredicate(self):
        """Test getPathPredicate"""
        astCtx = self.ctx.getAstContext()
        crst = self.ctx.getPathPredicate()
        self.assertNotEqual(len(self.ctx.getModel(crst)), 0)
        self.assertNotEqual(len(self.ctx.getModel(astCtx.lnot(crst))), 0)

    def test_getPathConstraints(self):
        """Test getPathConstraints"""
        pco = self.ctx.getPathConstraints()
        self.assertEqual(len(pco), 1)

    def test_isMultipleBranches(self):
        pc = self.ctx.getPathConstraints()[0]
        self.assertTrue(pc.isMultipleBranches())

    def test_getTakenPredicate(self):
        pc = self.ctx.getPathConstraints()[0]
        self.assertEqual(pc.getTakenPredicate().evaluate(), 1)

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

    def test_pushpop(self):
        ast = self.ctx.getAstContext()
        pc  = self.ctx.getPathPredicate()
        opc = pc

        self.assertEqual(str(pc), "(and (= (_ bv1 1) (_ bv1 1)) (= (ite (= ref!35 (_ bv1 1)) (_ bv91 32) (_ bv23 32)) (_ bv91 32)))")
        self.ctx.pushPathConstraint(ast.equal(ast.bvtrue(), ast.bvtrue()))

        pc  = self.ctx.getPathPredicate()
        self.assertEqual(str(pc), "(and (and (= (_ bv1 1) (_ bv1 1)) (= (ite (= ref!35 (_ bv1 1)) (_ bv91 32) (_ bv23 32)) (_ bv91 32))) (= (_ bv1 1) (_ bv1 1)))")

        self.ctx.popPathConstraint()
        pc  = self.ctx.getPathPredicate()
        self.assertEqual(str(pc), str(opc))

    def test_reachingBB(self):
        self.assertEqual(len(self.ctx.getPredicatesToReachAddress(91)), 1)
        self.assertEqual(len(self.ctx.getPredicatesToReachAddress(23)), 1)
        self.assertEqual(len(self.ctx.getPredicatesToReachAddress(20)), 0)

    def test_reachingBB2(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)

        trace = [
            b"\x40",        # inc eax
            b"\xff\xe0",    # jmp eax
        ]

        ctx.symbolizeRegister(ctx.registers.eax)
        ctx.symbolizeRegister(ctx.registers.ebx)

        for opcodes in trace:
            ctx.processing(Instruction(opcodes))

        self.assertEqual(ctx.getModel(ctx.getPredicatesToReachAddress(0x1337)[0])[0].getValue(), 0x1336)
