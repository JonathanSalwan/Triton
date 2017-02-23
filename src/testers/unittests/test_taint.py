#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import (setArchitecture, ARCH, REG, taintRegister, processing,
                    isRegisterTainted, Instruction, taintMemory, MemoryAccess,
                    isMemoryTainted, untaintMemory, untaintRegister)


class TestTaint(unittest.TestCase):

    """Testing the taint engine."""

    def test_known_issues(self):
        """Check tainting result after processing."""
        setArchitecture(ARCH.X86)

        taintRegister(REG.EAX)
        inst = Instruction()
        # lea eax,[esi+eax*1]
        inst.setOpcodes("\x8D\x04\x06")
        processing(inst)

        self.assertTrue(isRegisterTainted(REG.EAX))
        self.assertFalse(isRegisterTainted(REG.EBX))

    def test_taint_memory(self):
        """Check tainting memory."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isMemoryTainted(0x1000))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintMemory(0x1000)
        taintMemory(MemoryAccess(0x2000, 4))

        self.assertTrue(isMemoryTainted(0x1000))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 2)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2002, 2)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2003, 2)))

        self.assertFalse(isMemoryTainted(MemoryAccess(0x1fff, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertFalse(isMemoryTainted(0x1001))
        self.assertFalse(isMemoryTainted(0x0fff))

        untaintMemory(0x1000)
        untaintMemory(MemoryAccess(0x2000, 4))

        self.assertFalse(isMemoryTainted(0x1000))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 2)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2002, 2)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2003, 2)))

    def test_taint_register(self):
        """Check over tainting register."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))
        untaintRegister(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))

        taintRegister(REG.AH)
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertTrue(isRegisterTainted(REG.EAX))
        self.assertTrue(isRegisterTainted(REG.AX))

        untaintRegister(REG.AH)
        self.assertFalse(isRegisterTainted(REG.RAX))
        self.assertFalse(isRegisterTainted(REG.EAX))
        self.assertFalse(isRegisterTainted(REG.AX))

