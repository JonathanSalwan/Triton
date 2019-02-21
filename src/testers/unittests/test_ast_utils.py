#!/usr/bin/env python2
## -*- coding: utf-8 -*-
"""Test AST utils."""

import unittest
from triton import *



class TestAstUtils(unittest.TestCase):

    """Testing the AST utilities."""

    def setUp(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        self.astCtxt = self.ctx.getAstContext()

        self.sv1 = self.ctx.newSymbolicVariable(8)
        self.sv2 = self.ctx.newSymbolicVariable(8)

        self.v1 = self.astCtxt.variable(self.sv1)
        self.v2 = self.astCtxt.variable(self.sv2)

    def test_lookingForNodes(self):
        n = (((self.v1 + self.v2 * 3) + self.v2) - 1)

        # Looking for variables
        l = self.astCtxt.lookingForNodes(n, AST_NODE.VARIABLE)
        self.assertEqual(len(l), 2)
        self.assertEqual(l[0], self.v1)
        self.assertEqual(l[1], self.v2)
        self.assertEqual(l[0].getSymbolicVariable().getName(), self.sv1.getName())
        self.assertEqual(l[1].getSymbolicVariable().getName(), self.sv2.getName())

        l = self.astCtxt.lookingForNodes(n, AST_NODE.ANY)
        self.assertEqual(len(l), 12)

        l = self.astCtxt.lookingForNodes(n, AST_NODE.BVADD)
        self.assertEqual(len(l), 2)

        l = self.astCtxt.lookingForNodes(n, AST_NODE.BVSUB)
        self.assertEqual(len(l), 1)

        l = self.astCtxt.lookingForNodes(n, AST_NODE.BVMUL)
        self.assertEqual(len(l), 1)

        l = self.astCtxt.lookingForNodes(n, AST_NODE.BV)
        self.assertEqual(len(l), 2)
