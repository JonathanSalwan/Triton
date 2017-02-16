#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import (setArchitecture, ARCH, REG, taintRegister, processing,
                    isRegisterTainted, Instruction)


class TestTaint(unittest.TestCase):

    """Testing the taint engine."""

    def test_register(self):
        """Check tainting result after processing."""
        setArchitecture(ARCH.X86)

        taintRegister(REG.EAX)
        inst = Instruction()
        # lea eax,[esi+eax*1]
        inst.setOpcodes("\x8D\x04\x06")
        processing(inst)

        self.assertTrue(isRegisterTainted(REG.EAX))
        self.assertFalse(isRegisterTainted(REG.EBX))
