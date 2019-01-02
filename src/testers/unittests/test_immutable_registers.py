#!/usr/bin/env python2
# coding: utf-8
"""Test immutable registers."""

import unittest
import random

from triton import *


class TestImmutableAArch64Registers(unittest.TestCase):

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.AARCH64)

    def test_immutable(self):
        x1  = self.ctx.registers.x1
        x2  = self.ctx.registers.x2
        xzr = self.ctx.registers.xzr
        wzr = self.ctx.registers.wzr

        self.assertEqual(self.ctx.getConcreteRegisterValue(xzr), 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(wzr), 0)

        # Set concrete values
        self.ctx.setConcreteRegisterValue(xzr, 1234)
        self.ctx.setConcreteRegisterValue(x1, 10)
        self.ctx.setConcreteRegisterValue(x2, 20)

        self.assertEqual(self.ctx.getConcreteRegisterValue(xzr), 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(wzr), 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(x1), 10)
        self.assertEqual(self.ctx.getConcreteRegisterValue(x2), 20)

        inst = Instruction("\x3f\x00\x02\x8b") # add xzr, x1, x2
        self.ctx.processing(inst)

        # Concrete
        self.assertEqual(self.ctx.getConcreteRegisterValue(xzr), 0)
        self.assertEqual(self.ctx.getConcreteRegisterValue(wzr), 0)

        # Symbolic
        self.assertEqual(self.ctx.getSymbolicRegisterValue(xzr), 0)
        self.assertEqual(self.ctx.getSymbolicRegisterValue(wzr), 0)

        # Assignment
        self.assertEqual(REG.AARCH64.XZR in self.ctx.getSymbolicRegisters(), False)
        self.assertEqual(REG.AARCH64.WZR in self.ctx.getSymbolicRegisters(), False)
        self.assertEqual(REG.AARCH64.PC in self.ctx.getSymbolicRegisters(), True)
