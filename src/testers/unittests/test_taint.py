#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import ARCH, REG, Instruction, MemoryAccess, TritonContext


class TestTaint(unittest.TestCase):

    """Testing the taint engine."""

    def test_known_issues(self):
        """Check tainting result after processing."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86)

        Triton.taintRegister(Triton.Register(REG.X86_64.EAX))
        inst = Instruction()
        # lea eax,[esi+eax*1]
        inst.setOpcodes("\x8D\x04\x06")
        Triton.processing(inst)

        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.EAX)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.EBX)))

    def test_taint_memory(self):
        """Check tainting memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isMemoryTainted(0x1000))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintMemory(0x1000)
        Triton.taintMemory(MemoryAccess(0x2000, 4))

        self.assertTrue(Triton.isMemoryTainted(0x1000))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 2)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2002, 2)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2003, 2)))

        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x1fff, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertFalse(Triton.isMemoryTainted(0x1001))
        self.assertFalse(Triton.isMemoryTainted(0x0fff))

        Triton.untaintMemory(0x1000)
        Triton.untaintMemory(MemoryAccess(0x2000, 4))

        self.assertFalse(Triton.isMemoryTainted(0x1000))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 2)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2002, 2)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2003, 2)))

    def test_taint_register(self):
        """Check over tainting register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintRegister(Triton.Register(REG.X86_64.AH))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.EAX)))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.AX)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.AH))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.EAX)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.AX)))

    def test_taint_assignement_memory_immediate(self):
        """Check tainting assignment memory <- immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignmentMemoryImmediate(MemoryAccess(0x1000, 1))
        self.assertFalse(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignmentMemoryImmediate(MemoryAccess(0x0fff, 2))
        self.assertFalse(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignmentMemoryImmediate(MemoryAccess(0x0ffe, 2))
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(MemoryAccess(0x1000, 4))
        self.assertTrue(Triton.isMemoryTainted(0x1000))
        self.assertTrue(Triton.isMemoryTainted(0x1001))
        self.assertTrue(Triton.isMemoryTainted(0x1002))
        self.assertTrue(Triton.isMemoryTainted(0x1003))
        self.assertFalse(Triton.isMemoryTainted(0x1004))

        Triton.taintAssignmentMemoryImmediate(MemoryAccess(0x1001, 1))
        self.assertTrue(Triton.isMemoryTainted(0x1000))
        self.assertFalse(Triton.isMemoryTainted(0x1001))
        self.assertTrue(Triton.isMemoryTainted(0x1002))
        self.assertTrue(Triton.isMemoryTainted(0x1003))

        Triton.taintAssignmentMemoryImmediate(MemoryAccess(0x1000, 4))
        self.assertFalse(Triton.isMemoryTainted(0x1000))
        self.assertFalse(Triton.isMemoryTainted(0x1001))
        self.assertFalse(Triton.isMemoryTainted(0x1002))
        self.assertFalse(Triton.isMemoryTainted(0x1003))

    def test_taint_assignement_memory_memory(self):
        """Check tainting assignment memory <- memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 1))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

        Triton.taintAssignmentMemoryMemory(MemoryAccess(0x1000, 1), MemoryAccess(0x2000, 1))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

        Triton.taintAssignmentMemoryMemory(MemoryAccess(0x1000, 1), MemoryAccess(0x3000, 1))
        Triton.taintAssignmentMemoryMemory(MemoryAccess(0x2000, 1), MemoryAccess(0x3000, 1))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintAssignmentMemoryMemory(MemoryAccess(0x2001, 2), MemoryAccess(0x3000, 1))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

    def test_taint_assignement_memory_register(self):
        """Check tainting assignment memory <- register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 8)))

        Triton.taintAssignmentMemoryRegister(MemoryAccess(0x2002, 2), Triton.Register(REG.X86_64.AX))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2005, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2006, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2007, 1)))

        Triton.taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 8)))

        Triton.taintAssignmentMemoryRegister(MemoryAccess(0x1fff, 8), Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x1fff, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2001, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2002, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2003, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2004, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2005, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2006, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2007, 1)))

    def test_taint_assignement_register_immediate(self):
        """Check tainting assignment register <- immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintAssignmentRegisterImmediate(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_assignement_register_memory(self):
        """Check tainting assignment register <- memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintAssignmentRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 8)))

        Triton.taintAssignmentRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintAssignmentRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x3000, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_assignement_register_register(self):
        """Check tainting assignment register <- register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintAssignmentRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintAssignmentRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RBX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))

        Triton.taintAssignmentRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RBX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_union_memory_immediate(self):
        """Check tainting union memory U immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnionMemoryImmediate(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_memory_memory(self):
        """Check tainting union memory U memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

        Triton.taintMemory(MemoryAccess(0x3000, 4))
        Triton.taintUnionMemoryMemory(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

    def test_taint_union_memory_register(self):
        """Check tainting union memory U register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnionMemoryRegister(MemoryAccess(0x2000, 4), Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintUnionMemoryRegister(MemoryAccess(0x2000, 4), Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        Triton.taintUnionMemoryRegister(MemoryAccess(0x2000, 4), Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_union_register_immediate(self):
        """Check tainting union register U immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintUnionRegisterImmediate(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintUnionRegisterImmediate(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_union_register_memory(self):
        """Check tainting union register U memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintUnionRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintUnionRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        # !T U T
        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        Triton.taintMemory(MemoryAccess(0x2000, 4))
        Triton.taintUnionRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        # T U T
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        Triton.taintMemory(MemoryAccess(0x2000, 4))
        Triton.taintUnionRegisterMemory(Triton.Register(REG.X86_64.RAX), MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_register_register(self):
        """Check tainting union register U register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.taintRegister(Triton.Register(REG.X86_64.RAX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.taintUnionRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RBX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))

        Triton.taintRegister(Triton.Register(REG.X86_64.RBX))
        Triton.taintUnionRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RBX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        Triton.taintRegister(Triton.Register(REG.X86_64.RBX))
        Triton.taintUnionRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RBX))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))

        Triton.untaintRegister(Triton.Register(REG.X86_64.RAX))
        Triton.untaintRegister(Triton.Register(REG.X86_64.RBX))
        Triton.taintUnionRegisterRegister(Triton.Register(REG.X86_64.RAX), Triton.Register(REG.X86_64.RBX))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RBX)))

    def test_taint_get_tainted_registers(self):
        """Get tainted registers"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        r = Triton.getTaintedRegisters()
        self.assertTrue(len(r) == 0)

        Triton.taintRegister(Triton.Register(REG.X86_64.EAX))
        Triton.taintRegister(Triton.Register(REG.X86_64.AX))
        Triton.taintRegister(Triton.Register(REG.X86_64.RBX))
        Triton.taintRegister(Triton.Register(REG.X86_64.CL))
        Triton.taintRegister(Triton.Register(REG.X86_64.DI))

        r = Triton.getTaintedRegisters()
        self.assertTrue(Triton.Register(REG.X86_64.RAX) in r)
        self.assertTrue(Triton.Register(REG.X86_64.RBX) in r)
        self.assertTrue(Triton.Register(REG.X86_64.RCX) in r)
        self.assertTrue(Triton.Register(REG.X86_64.RDI) in r)

    def test_taint_get_tainted_memory(self):
        """Get tainted memory"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        m = Triton.getTaintedMemory()
        self.assertTrue(len(m) == 0)

        Triton.taintMemory(0x1000)
        Triton.taintMemory(0x2000)
        Triton.taintMemory(0x3000)
        Triton.taintMemory(MemoryAccess(0x4000, 4))

        m = Triton.getTaintedMemory()
        self.assertTrue(0x1000 in m)
        self.assertTrue(0x2000 in m)
        self.assertTrue(0x3000 in m)
        self.assertTrue(0x4000 in m)
        self.assertTrue(0x4001 in m)
        self.assertTrue(0x4002 in m)
        self.assertTrue(0x4003 in m)
        self.assertFalse(0x5000 in m)

    def test_taint_set_register(self):
        """Set taint register"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.setTaintRegister(Triton.Register(REG.X86_64.RAX), True)
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.setTaintRegister(Triton.Register(REG.X86_64.RAX), False)
        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

    def test_taint_set_memory(self):
        """Set taint memory"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isMemoryTainted(0x1000))
        Triton.setTaintMemory(MemoryAccess(0x1000, 1), True)
        self.assertTrue(Triton.isMemoryTainted(0x1000))
        Triton.setTaintMemory(MemoryAccess(0x1000, 1), False)
        self.assertFalse(Triton.isMemoryTainted(0x1000))

    def test_taint_off_on(self):
        """Taint off / on"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertTrue(Triton.isTaintEngineEnabled())

        self.assertFalse(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.setTaintRegister(Triton.Register(REG.X86_64.RAX), True)
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

        Triton.enableTaintEngine(False)
        self.assertFalse(Triton.isTaintEngineEnabled())

        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))
        Triton.setTaintRegister(Triton.Register(REG.X86_64.RAX), False)
        self.assertTrue(Triton.isRegisterTainted(Triton.Register(REG.X86_64.RAX)))

