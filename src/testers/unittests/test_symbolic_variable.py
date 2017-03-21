#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Variable."""

import unittest
from triton import *


class TestSymbolicVariable(unittest.TestCase):

    """Testing symbolic variable."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)
        self.v0 = newSymbolicVariable(8)
        self.v1 = newSymbolicVariable(16)
        self.v2 = newSymbolicVariable(32, "test com")

    def test_id(self):
        """Test IDs"""
        self.assertEqual(self.v0.getId(), 0)
        self.assertEqual(self.v1.getId(), 1)
        self.assertEqual(self.v2.getId(), 2)

    def test_kind(self):
        """Test kind"""
        self.assertEqual(self.v0.getKind(), SYMEXPR.UNDEF)
        self.assertEqual(self.v1.getKind(), SYMEXPR.UNDEF)
        self.assertEqual(self.v2.getKind(), SYMEXPR.UNDEF)

    def test_name(self):
        """Test name"""
        self.assertEqual(self.v0.getName(), "SymVar_0")
        self.assertEqual(self.v1.getName(), "SymVar_1")
        self.assertEqual(self.v2.getName(), "SymVar_2")

    def test_name(self):
        """Test name"""
        self.assertEqual(self.v0.getBitSize(), 8)
        self.assertEqual(self.v1.getBitSize(), 16)
        self.assertEqual(self.v2.getBitSize(), 32)

    def test_comment(self):
        """Test comment"""
        self.assertEqual(self.v0.getComment(), "")
        self.assertEqual(self.v1.getComment(), "")
        self.assertEqual(self.v2.getComment(), "test com")

        self.v0.setComment("test v0")
        self.v1.setComment("test v1")

        self.assertEqual(self.v0.getComment(), "test v0")
        self.assertEqual(self.v1.getComment(), "test v1")
        self.assertEqual(self.v2.getComment(), "test com")

    def test_concrete_value(self):
        """Test concrete value"""
        self.assertEqual(self.v0.getConcreteValue(), 0)
        self.assertEqual(self.v1.getConcreteValue(), 0)
        self.assertEqual(self.v2.getConcreteValue(), 0)

        self.v0.setConcreteValue(0x10)
        self.v1.setConcreteValue(0x20)
        self.v2.setConcreteValue(0x30)

        self.assertEqual(self.v0.getConcreteValue(), 0x10)
        self.assertEqual(self.v1.getConcreteValue(), 0x20)
        self.assertEqual(self.v2.getConcreteValue(), 0x30)

    def test_str(self):
        """Test variable representation"""
        self.assertEqual(str(self.v0), "SymVar_0:8")
        self.assertEqual(str(self.v1), "SymVar_1:16")
        self.assertEqual(str(self.v2), "SymVar_2:32")

