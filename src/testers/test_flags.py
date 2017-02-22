#!/usr/bin/env python2
# coding: utf-8
"""Test flags."""

import unittest
import random

from triton import (setArchitecture, ARCH, REG, setConcreteRegisterValue,
                    getConcreteRegisterValue, Register)


class TestFlags(unittest.TestCase):

    """Testing the concrete flag values."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

    def test_set_flags(self):
        """Check flags can be set in any order with a correct output result."""
        registers = [REG.ZF, REG.AF, REG.IF, REG.CF, REG.DF, REG.PF, REG.SF,
                     REG.OF, REG.TF]
        values = [0] * len(registers)

        rand_registers = list(registers)
        random.shuffle(rand_registers)

        # Randomnly set flags registers and check result is the one expected
        for reg in rand_registers:
            setConcreteRegisterValue(Register(reg, 1))
            values[registers.index(reg)] = 1
            self.assertListEqual([getConcreteRegisterValue(r) for r in registers], values)

    def test_unset_flags(self):
        """Check flags can be unset in any order with a correct result."""
        registers = [REG.ZF, REG.AF, REG.IF, REG.CF, REG.DF, REG.PF, REG.SF,
                     REG.OF, REG.TF]
        values = [1] * len(registers)
        for reg in registers:
            setConcreteRegisterValue(Register(reg, 1))

        rand_registers = list(registers)
        random.shuffle(rand_registers)

        # Randomnly unset flags registers and check result is the one expected
        for reg in rand_registers:
            setConcreteRegisterValue(Register(reg, 0))
            values[registers.index(reg)] = 0
            self.assertListEqual([getConcreteRegisterValue(r) for r in registers], values)

