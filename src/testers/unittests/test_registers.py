#!/usr/bin/env python2
# coding: utf-8
"""Test register."""

import unittest

from triton import (setArchitecture, isRegister, isRegisterValid, isFlag,
                    ARCH, REG, Register, OPERAND)


class TestRAXRegister(unittest.TestCase):

    """Testing the Register class with RAX."""

    def setUp(self):
        """Define arch and register to check."""
        setArchitecture(ARCH.X86_64)
        self.reg = REG.RAX

    def test_name(self):
        """Check register name."""
        self.assertEqual(self.reg.getName(), "rax")

    def test_size(self):
        """Check register size."""
        self.assertEqual(self.reg.getSize(), 8)

    def test_bit_size(self):
        """Check register bit size."""
        self.assertEqual(self.reg.getBitSize(), 64)

    def test_concrete_value(self):
        """Check concrete value modification."""
        self.assertEqual(self.reg.getConcreteValue(), 0)

        # immutable
        self.reg.setConcreteValue(0x1122334455667788)
        self.assertEqual(self.reg.getConcreteValue(), 0)

        # mutable
        reg2 = Register(self.reg)
        reg2.setConcreteValue(0x1122334455667788)
        self.assertEqual(reg2.getConcreteValue(), 0x1122334455667788)

    def test_parent(self):
        """Check parent register."""
        self.assertEqual(self.reg.getParent().getName(), "rax")

    def test_type(self):
        """Check operand type."""
        self.assertEqual(self.reg.getType(), OPERAND.REG)

    def test_is_valid(self):
        """Check register validity."""
        self.assertTrue(isRegisterValid(self.reg))

    def test_is_flag(self):
        """Check register flag."""
        self.assertFalse(isFlag(self.reg))

    def test_is_register(self):
        """Check register detect."""
        self.assertTrue(isRegister(self.reg))


class TestAHRegister(unittest.TestCase):

    """Testing the Register class with AH."""

    def setUp(self):
        """Define arch and register to check."""
        setArchitecture(ARCH.X86_64)
        self.reg = REG.AH

    def test_size(self):
        """Check register size."""
        self.assertEqual(self.reg.getSize(), 1)

    def test_bitvector(self):
        """Check bitvector information."""
        self.assertEqual(self.reg.getBitvector().getHigh(), 15)
        self.assertEqual(self.reg.getBitvector().getLow(), 8)
        self.assertEqual(self.reg.getBitvector().getVectorSize(), 8)

    def test_parent(self):
        """Check parent register on multiple arch."""
        self.assertEqual(self.reg.getParent().getName(), "rax")

        setArchitecture(ARCH.X86)
        self.reg = REG.AH
        self.assertEqual(self.reg.getParent().getName(), "eax")
        self.assertEqual(self.reg.getParent().getBitSize(), 32)


class TestXmmRegister(unittest.TestCase):

    """Testing the Register class with FP/SIMD registers."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

    def test_xmm_on_x86(self):
        """Check xmm on 32 bits arch."""
        setArchitecture(ARCH.X86)
        xmm = Register(REG.XMM1, 0x112233445566778899aabbccddeeff00)
        self.assertEqual(xmm.getBitSize(), 128)
        self.assertEqual(xmm.getConcreteValue(),
                         0x112233445566778899aabbccddeeff00)

    def test_ymm(self):
        """Check ymm on 64 bits arch."""
        ymm = Register(REG.YMM1, 0x112233445566778899aabbccddeeff00)
        self.assertEqual(ymm.getBitSize(), 256)
        ymm.setConcreteValue(0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
        self.assertEqual(ymm.getConcreteValue(), 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)

    def test_zmm(self):
        """Check zmm on 64 bits arch."""
        zmm = Register(REG.ZMM2, 0)
        self.assertEqual(zmm.getBitSize(), 512)
        zmm.setConcreteValue(0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
        self.assertEqual(zmm.getConcreteValue(), 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)


class TestRegisterValues(unittest.TestCase):

    """Check register values with hierarchies."""

    def test_register_create(self):
        """Check register creation with value."""
        for reg in (REG.AH, REG.AL):
            # OK
            Register(reg, 0xff)
            # Not OK
            # TODO : Be more specific on the raise exception type
            with self.assertRaises(Exception):
                Register(reg, 0xff + 1)

        Register(REG.ZF, 1)
        with self.assertRaises(Exception):
            Register(REG.ZF, 2)

    def test_set_concrete_value(self):
        """Check register value modification."""
        for reg in (REG.AH, REG.AL):
            # OK
            reg = Register(reg)
            reg.setConcreteValue(0xff)
            # Not OK
            # TODO : Be more specific on the raise exception type
            with self.assertRaises(Exception):
                reg.setConcreteValue(0xff + 1)

        reg = Register(REG.ZF)
        reg.setConcreteValue(1)
        with self.assertRaises(Exception):
            reg.setConcreteValue(2)

    def test_overlap(self):
        """Check register overlapping."""
        self.assertTrue(REG.AX.isOverlapWith(REG.EAX), "overlap with upper")
        self.assertTrue(REG.AX.isOverlapWith(REG.RAX), "overlap with parent")
        self.assertTrue(REG.RAX.isOverlapWith(REG.AX), "overlap with lower")
        self.assertFalse(REG.AH.isOverlapWith(REG.AL))
        self.assertTrue(REG.AX.isOverlapWith(REG.AL))
        self.assertTrue(REG.AL.isOverlapWith(REG.AX))
        self.assertFalse(REG.EAX.isOverlapWith(REG.EDX))

