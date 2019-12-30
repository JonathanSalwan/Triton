#!/usr/bin/env python2
# coding: utf-8
"""Test register."""

import unittest
import random

from triton import (ARCH, REG, OPERAND, TritonContext)


class TestRAXRegister(unittest.TestCase):

    """Testing the Register class with RAX."""

    def setUp(self):
        """Define arch and register to check."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.reg = self.ctx.registers.rax

    def test_name(self):
        """Check register name."""
        self.assertEqual(self.reg.getName(), "rax")

    def test_size(self):
        """Check register size."""
        self.assertEqual(self.reg.getSize(), 8)

    def test_bit_size(self):
        """Check register bit size."""
        self.assertEqual(self.reg.getBitSize(), 64)

    def test_parent(self):
        """Check parent register."""
        self.assertEqual(self.ctx.getParentRegister(self.reg).getName(), "rax")

    def test_type(self):
        """Check operand type."""
        self.assertEqual(self.reg.getType(), OPERAND.REG)

    def test_is_valid(self):
        """Check register validity."""
        self.assertTrue(self.ctx.isRegisterValid(self.reg))

    def test_is_flag(self):
        """Check register flag."""
        self.assertFalse(self.ctx.isFlag(self.reg))

    def test_is_register(self):
        """Check register detect."""
        self.assertTrue(self.ctx.isRegister(self.reg))

    def test_is_mutable(self):
        """Check register is mutable."""
        self.assertTrue(self.reg.isMutable())


class TestAHRegister(unittest.TestCase):

    """Testing the Register class with AH."""

    def setUp(self):
        """Define arch and register to check."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.reg = self.ctx.registers.ah

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
        self.assertEqual(self.ctx.getParentRegister(self.reg).getName(), "rax")

        self.ctx.setArchitecture(ARCH.X86)
        self.reg = self.ctx.registers.ah
        self.assertEqual(self.ctx.getParentRegister(self.reg).getName(), "eax")
        self.assertEqual(self.ctx.getParentRegister(self.reg).getBitSize(), 32)


class TestXmmRegister(unittest.TestCase):

    """Testing the Register class with FP/SIMD registers."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

    def test_xmm_on_x86(self):
        """Check xmm on 32 bits arch."""
        self.ctx.setArchitecture(ARCH.X86)
        xmm = self.ctx.registers.xmm1
        self.assertEqual(xmm.getBitSize(), 128)

    def test_ymm(self):
        """Check ymm on 64 bits arch."""
        ymm = self.ctx.registers.ymm1
        self.assertEqual(ymm.getBitSize(), 256)

    def test_zmm(self):
        """Check zmm on 64 bits arch."""
        zmm = self.ctx.registers.zmm2
        self.assertEqual(zmm.getBitSize(), 512)


class TestRegisterValues(unittest.TestCase):

    """Check register values with hierarchies."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

    def test_set_concrete_value(self):
        """Check register value modification."""
        for reg in (REG.X86_64.AH, REG.X86_64.AL):
            # OK
            reg = self.ctx.getRegister(reg)
            self.ctx.setConcreteRegisterValue(reg, 0xff)
            # Not OK
            with self.assertRaises(Exception):
                self.ctx.setConcreteRegisterValue(reg, 0xff+1)

        reg = self.ctx.registers.zf
        self.ctx.setConcreteRegisterValue(reg, 1)
        with self.assertRaises(Exception):
            self.ctx.setConcreteRegisterValue(reg, 2)

    def test_overlap(self):
        """Check register overlapping."""
        self.assertTrue(self.ctx.registers.ax.isOverlapWith(self.ctx.registers.eax), "overlap with upper")
        self.assertTrue(self.ctx.registers.ax.isOverlapWith(self.ctx.registers.rax), "overlap with parent")
        self.assertTrue(self.ctx.registers.rax.isOverlapWith(self.ctx.registers.ax), "overlap with lower")
        self.assertFalse(self.ctx.registers.ah.isOverlapWith(self.ctx.registers.al))
        self.assertTrue(self.ctx.registers.ah.isOverlapWith(self.ctx.registers.eax))
        self.assertTrue(self.ctx.registers.eax.isOverlapWith(self.ctx.registers.ah))
        self.assertTrue(self.ctx.registers.ax.isOverlapWith(self.ctx.registers.al))
        self.assertTrue(self.ctx.registers.al.isOverlapWith(self.ctx.registers.ax))
        self.assertFalse(self.ctx.registers.eax.isOverlapWith(self.ctx.registers.edx))


class TestAArch64Registers(unittest.TestCase):
    """Test AArch64 registers"""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.AARCH64)

    def test_set_concrete_value(self):
        """Check register value modification."""
        for reg in self.ctx.getParentRegisters():
            if reg.isMutable() == False:
                # XZR
                continue
            i = random.randrange(0, 0xffffffffffffffff) & reg.getBitvector().getMaxValue()
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)
            self.ctx.setConcreteRegisterValue(reg, i)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), i)
            self.ctx.setConcreteRegisterValue(reg, 0)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)

        regs = [
            self.ctx.registers.w0, self.ctx.registers.w1, self.ctx.registers.w2,
            self.ctx.registers.w3, self.ctx.registers.w4, self.ctx.registers.w5,
            self.ctx.registers.w6, self.ctx.registers.w7, self.ctx.registers.w8,
            self.ctx.registers.w9, self.ctx.registers.w10, self.ctx.registers.w11,
            self.ctx.registers.w12, self.ctx.registers.w13, self.ctx.registers.w14,
            self.ctx.registers.w15, self.ctx.registers.w16, self.ctx.registers.w17,
            self.ctx.registers.w18, self.ctx.registers.w19, self.ctx.registers.w20,
            self.ctx.registers.w21, self.ctx.registers.w22, self.ctx.registers.w23,
            self.ctx.registers.w24, self.ctx.registers.w25, self.ctx.registers.w26,
            self.ctx.registers.w27, self.ctx.registers.w28, self.ctx.registers.w29,
            self.ctx.registers.w30, self.ctx.registers.wsp, self.ctx.registers.spsr,
        ]

        for reg in regs:
            i = random.randrange(0, 0xffffffff) & reg.getBitvector().getMaxValue()
            self.ctx.setConcreteRegisterValue(reg, i)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), i)
            self.ctx.setConcreteRegisterValue(reg, 0)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)


class TestArm32Registers(unittest.TestCase):
    """Test Arm32 registers"""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.ARM32)

    def test_set_concrete_value(self):
        """Check register value modification."""
        for reg in self.ctx.getParentRegisters():
            if reg.isMutable() == False:
                continue
            if reg.getName() == "pc":
                continue
            i = random.randrange(0, 0xffffffff) & reg.getBitvector().getMaxValue()
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)
            self.ctx.setConcreteRegisterValue(reg, i)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), i)
            self.ctx.setConcreteRegisterValue(reg, 0)
            self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)

        # Check pc register (LSB == 0).
        reg = self.ctx.registers.pc
        i = random.randrange(0, 0xffffffff) & reg.getBitvector().getMaxValue()
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)
        self.ctx.setConcreteRegisterValue(reg, i & ~0x1)
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), i & ~0x1)
        self.ctx.setConcreteRegisterValue(reg, 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)

        # Check pc register (LSB == 1).
        reg = self.ctx.registers.pc
        i = random.randrange(0, 0xffffffff) & reg.getBitvector().getMaxValue()
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)
        self.ctx.setConcreteRegisterValue(reg, i | 0x1)
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), i & ~0x1)
        self.ctx.setConcreteRegisterValue(reg, 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(reg), 0)
