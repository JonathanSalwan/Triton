#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import (setArchitecture, ARCH, REG, taintRegister, processing,
                    isRegisterTainted, Instruction, taintMemory, MemoryAccess,
                    isMemoryTainted, untaintMemory, taintAssignmentMemoryImmediate,
                    untaintRegister, taintAssignmentMemoryMemory,
                    taintAssignmentMemoryRegister, taintAssignmentRegisterImmediate,
                    taintAssignmentRegisterMemory, taintAssignmentRegisterRegister)


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

    def test_taint_assignement_memory_immediate(self):
        """Check tainting assignment memory <- immediate."""
        setArchitecture(ARCH.X86_64)

        taintMemory(0x1000)
        self.assertTrue(isMemoryTainted(0x1000))

        taintAssignmentMemoryImmediate(MemoryAccess(0x1000, 1))
        self.assertFalse(isMemoryTainted(0x1000))

        taintMemory(0x1000)
        self.assertTrue(isMemoryTainted(0x1000))

        taintAssignmentMemoryImmediate(MemoryAccess(0x0fff, 2))
        self.assertFalse(isMemoryTainted(0x1000))

        taintMemory(0x1000)
        self.assertTrue(isMemoryTainted(0x1000))

        taintAssignmentMemoryImmediate(MemoryAccess(0x0ffe, 2))
        self.assertTrue(isMemoryTainted(0x1000))

        taintMemory(MemoryAccess(0x1000, 4))
        self.assertTrue(isMemoryTainted(0x1000))
        self.assertTrue(isMemoryTainted(0x1001))
        self.assertTrue(isMemoryTainted(0x1002))
        self.assertTrue(isMemoryTainted(0x1003))
        self.assertFalse(isMemoryTainted(0x1004))

        taintAssignmentMemoryImmediate(MemoryAccess(0x1001, 1))
        self.assertTrue(isMemoryTainted(0x1000))
        self.assertFalse(isMemoryTainted(0x1001))
        self.assertTrue(isMemoryTainted(0x1002))
        self.assertTrue(isMemoryTainted(0x1003))

        taintAssignmentMemoryImmediate(MemoryAccess(0x1000, 4))
        self.assertFalse(isMemoryTainted(0x1000))
        self.assertFalse(isMemoryTainted(0x1001))
        self.assertFalse(isMemoryTainted(0x1002))
        self.assertFalse(isMemoryTainted(0x1003))

    def test_taint_assignement_memory_memory(self):
        """Check tainting assignment memory <- memory."""
        setArchitecture(ARCH.X86_64)

        taintMemory(MemoryAccess(0x2000, 1))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))

        taintAssignmentMemoryMemory(MemoryAccess(0x1000, 1), MemoryAccess(0x2000, 1))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))

        taintAssignmentMemoryMemory(MemoryAccess(0x1000, 1), MemoryAccess(0x3000, 1))
        taintAssignmentMemoryMemory(MemoryAccess(0x2000, 1), MemoryAccess(0x3000, 1))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 1)))

        taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintAssignmentMemoryMemory(MemoryAccess(0x2001, 2), MemoryAccess(0x3000, 1))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))

    def test_taint_assignement_memory_register(self):
        """Check tainting assignment memory <- register."""
        setArchitecture(ARCH.X86_64)

        taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 8)))

        taintAssignmentMemoryRegister(MemoryAccess(0x2002, 2), REG.AX)
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2005, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2006, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2007, 1)))

        taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 8)))

        taintAssignmentMemoryRegister(MemoryAccess(0x1fff, 8), REG.RAX)
        self.assertFalse(isMemoryTainted(MemoryAccess(0x1fff, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2005, 1)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2006, 1)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2007, 1)))

    def test_taint_assignement_register_immediate(self):
        """Check tainting assignment register <- immediate."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintAssignmentRegisterImmediate(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))

    def test_taint_assignement_register_memory(self):
        """Check tainting assignment register <- memory."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintAssignmentRegisterMemory(REG.RAX, MemoryAccess(0x2000, 8))
        self.assertFalse(isRegisterTainted(REG.RAX))

        taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 8)))

        taintAssignmentRegisterMemory(REG.RAX, MemoryAccess(0x2000, 8))
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintAssignmentRegisterMemory(REG.RAX, MemoryAccess(0x3000, 8))
        self.assertFalse(isRegisterTainted(REG.RAX))

    def test_taint_assignement_register_register(self):
        """Check tainting assignment register <- register."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintAssignmentRegisterRegister(REG.RAX, REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        untaintRegister(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))
        taintAssignmentRegisterRegister(REG.RAX, REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))

        self.assertFalse(isRegisterTainted(REG.RBX))
        taintRegister(REG.RBX)
        self.assertTrue(isRegisterTainted(REG.RBX))

        taintAssignmentRegisterRegister(REG.RAX, REG.RBX)
        self.assertTrue(isRegisterTainted(REG.RAX))

