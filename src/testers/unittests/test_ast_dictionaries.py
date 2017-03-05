#!/usr/bin/env python2
# coding: utf-8
"""Test AST_DICTIONARIES."""

import unittest

from triton     import *
from triton.ast import *


class TestAstDictionaries(unittest.TestCase):

    """Testing the AST_DICTIONARIES."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.AST_DICTIONARIES, True)

    def test_dictionaries(self):
        # d is empty
        d = getAstDictionariesStats()
        for k, v in d.items():
            self.assertEqual(v, 0)

        bv1 = bv(1, 8)
        bv2 = bv(2, 8)

        d = getAstDictionariesStats()
        self.assertEqual(d['bv'], 2)
        self.assertEqual(d['decimal'], 3)
        self.assertEqual(d['allocatedDictionaries'], 5)
        self.assertEqual(d['allocatedNodes'], 6)

        # Same allocation
        bv1 = bv(1, 8)
        bv2 = bv(2, 8)

        d = getAstDictionariesStats()
        self.assertEqual(d['bv'], 2)
        self.assertEqual(d['decimal'], 3)
        self.assertEqual(d['allocatedDictionaries'], 5)
        self.assertEqual(d['allocatedNodes'], 12)
