#!/usr/bin/env python2
# coding: utf-8
"""Test AST_DICTIONARIES."""

import unittest

from triton import ARCH, MODE, TritonContext


class TestAstDictionaries(unittest.TestCase):

    """Testing the AST_DICTIONARIES."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.enableMode(MODE.AST_DICTIONARIES, True)
        self.astCtxt = self.Triton.getAstContext()

    def test_dictionaries(self):
        # d is empty
        d = self.Triton.getAstDictionariesStats()
        for k, v in d.items():
            self.assertEqual(v, 0)

        bv1 = self.astCtxt.bv(1, 8)
        bv2 = self.astCtxt.bv(2, 8)

        d = self.Triton.getAstDictionariesStats()
        self.assertEqual(d['bv'], 2)
        self.assertEqual(d['decimal'], 3)
        self.assertEqual(d['allocatedDictionaries'], 5)
        self.assertEqual(d['allocatedNodes'], 6)

        # Same allocation
        bv1 = self.astCtxt.bv(1, 8)
        bv2 = self.astCtxt.bv(2, 8)

        d = self.Triton.getAstDictionariesStats()
        self.assertEqual(d['bv'], 2)
        self.assertEqual(d['decimal'], 3)
        self.assertEqual(d['allocatedDictionaries'], 5)
        self.assertEqual(d['allocatedNodes'], 12)
