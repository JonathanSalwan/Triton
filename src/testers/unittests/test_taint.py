#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import (setArchitecture, ARCH, REG, taintRegister, processing,
                    isRegisterTainted, Instruction, taintMemory, MemoryAccess,
                    isMemoryTainted, untaintMemory, untaintRegister,
                    taintAssignmentMemoryImmediate, taintAssignmentMemoryMemory,
                    taintAssignmentMemoryRegister, taintAssignmentRegisterImmediate,
                    taintAssignmentRegisterMemory, taintAssignmentRegisterRegister,
                    taintUnionMemoryImmediate, taintUnionMemoryMemory,
                    taintUnionMemoryRegister, taintUnionRegisterImmediate,
                    taintUnionRegisterMemory, taintUnionRegisterRegister,
                    getTaintedRegisters, getTaintedMemory)


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

    def test_taint_union_memory_immediate(self):
        """Check tainting union memory U immediate."""
        setArchitecture(ARCH.X86_64)

        taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintUnionMemoryImmediate(MemoryAccess(0x2000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_memory_memory(self):
        """Check tainting union memory U memory."""
        setArchitecture(ARCH.X86_64)

        taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x3000, 4)))

        untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x3000, 4)))

        taintMemory(MemoryAccess(0x3000, 4))
        taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x3000, 4)))

    def test_taint_union_memory_register(self):
        """Check tainting union memory U register."""
        setArchitecture(ARCH.X86_64)

        taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        taintUnionMemoryRegister(MemoryAccess(0x2000, 4), REG.RAX)
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isRegisterTainted(REG.RAX))

        untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isRegisterTainted(REG.RAX))

        taintUnionMemoryRegister(MemoryAccess(0x2000, 4), REG.RAX)
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(isRegisterTainted(REG.RAX))

        taintRegister(REG.RAX)
        taintUnionMemoryRegister(MemoryAccess(0x2000, 4), REG.RAX)
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(isRegisterTainted(REG.RAX))

    def test_taint_union_register_immediate(self):
        """Check tainting union register U immediate."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintUnionRegisterImmediate(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        untaintRegister(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))
        taintUnionRegisterImmediate(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))

    def test_taint_union_register_memory(self):
        """Check tainting union register U memory."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintUnionRegisterMemory(REG.RAX, MemoryAccess(0x2000, 4))
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))

        untaintRegister(REG.RAX)
        self.assertFalse(isRegisterTainted(REG.RAX))

        taintUnionRegisterMemory(REG.RAX, MemoryAccess(0x2000, 4))
        self.assertFalse(isRegisterTainted(REG.RAX))
        self.assertFalse(isMemoryTainted(MemoryAccess(0x2000, 4)))

        # !T U T
        untaintRegister(REG.RAX)
        taintMemory(MemoryAccess(0x2000, 4))
        taintUnionRegisterMemory(REG.RAX, MemoryAccess(0x2000, 4))
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

        # T U T
        taintRegister(REG.RAX)
        taintMemory(MemoryAccess(0x2000, 4))
        taintUnionRegisterMemory(REG.RAX, MemoryAccess(0x2000, 4))
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertTrue(isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_register_register(self):
        """Check tainting union register U register."""
        setArchitecture(ARCH.X86_64)

        self.assertFalse(isRegisterTainted(REG.RAX))
        taintRegister(REG.RAX)
        self.assertTrue(isRegisterTainted(REG.RAX))

        taintUnionRegisterRegister(REG.RAX, REG.RBX)
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertFalse(isRegisterTainted(REG.RBX))

        taintRegister(REG.RBX)
        taintUnionRegisterRegister(REG.RAX, REG.RBX)
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertTrue(isRegisterTainted(REG.RBX))

        untaintRegister(REG.RAX)
        taintRegister(REG.RBX)
        taintUnionRegisterRegister(REG.RAX, REG.RBX)
        self.assertTrue(isRegisterTainted(REG.RAX))
        self.assertTrue(isRegisterTainted(REG.RBX))

        untaintRegister(REG.RAX)
        untaintRegister(REG.RBX)
        taintUnionRegisterRegister(REG.RAX, REG.RBX)
        self.assertFalse(isRegisterTainted(REG.RAX))
        self.assertFalse(isRegisterTainted(REG.RBX))

    def test_taint_get_tainted_registers(self):
        """Get tainted registers"""
        setArchitecture(ARCH.X86_64)

        r = getTaintedRegisters()
        self.assertTrue(len(r) == 0)

        taintRegister(REG.EAX)
        taintRegister(REG.AX)
        taintRegister(REG.RBX)
        taintRegister(REG.CL)
        taintRegister(REG.DI)

        r = getTaintedRegisters()
        self.assertTrue(REG.RAX in r)
        self.assertTrue(REG.RBX in r)
        self.assertTrue(REG.RCX in r)
        self.assertTrue(REG.RDI in r)

    def test_taint_get_tainted_memory(self):
        """Get tainted memory"""
        setArchitecture(ARCH.X86_64)

        m = getTaintedMemory()
        self.assertTrue(len(m) == 0)

        taintMemory(0x1000)
        taintMemory(0x2000)
        taintMemory(0x3000)
        taintMemory(MemoryAccess(0x4000, 4))

        m = getTaintedMemory()
        self.assertTrue(0x1000 in m)
        self.assertTrue(0x2000 in m)
        self.assertTrue(0x3000 in m)
        self.assertTrue(0x4000 in m)
        self.assertTrue(0x4001 in m)
        self.assertTrue(0x4002 in m)
        self.assertTrue(0x4003 in m)
        self.assertFalse(0x5000 in m)

