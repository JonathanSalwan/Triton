#!/usr/bin/env python2
# coding: utf-8
"""Test Taint."""

import unittest

from triton import *


class TestTaint(unittest.TestCase):

    """Testing the taint engine."""

    def test_known_issues(self):
        """Check tainting result after processing."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86)

        Triton.taintRegister(Triton.registers.eax)
        inst = Instruction()
        # lea eax,[esi+eax*1]
        inst.setOpcode(b"\x8D\x04\x06")
        Triton.processing(inst)

        self.assertTrue(Triton.isRegisterTainted(Triton.registers.eax))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.ebx))

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

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.untaintRegister(Triton.registers.rax)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintRegister(Triton.registers.ah)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.eax))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.ax))

        Triton.untaintRegister(Triton.registers.ah)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.eax))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.ax))

    def test_taint_assignement_memory_immediate(self):
        """Check tainting assignment memory <- immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignment(MemoryAccess(0x1000, 1), Immediate(1, 1))
        self.assertFalse(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignment(MemoryAccess(0x0fff, 2), Immediate(1, 2))
        self.assertFalse(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(0x1000)
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintAssignment(MemoryAccess(0x0ffe, 2), Immediate(1, 2))
        self.assertTrue(Triton.isMemoryTainted(0x1000))

        Triton.taintMemory(MemoryAccess(0x1000, 4))
        self.assertTrue(Triton.isMemoryTainted(0x1000))
        self.assertTrue(Triton.isMemoryTainted(0x1001))
        self.assertTrue(Triton.isMemoryTainted(0x1002))
        self.assertTrue(Triton.isMemoryTainted(0x1003))
        self.assertFalse(Triton.isMemoryTainted(0x1004))

        Triton.taintAssignment(MemoryAccess(0x1001, 1), Immediate(1, 1))
        self.assertTrue(Triton.isMemoryTainted(0x1000))
        self.assertFalse(Triton.isMemoryTainted(0x1001))
        self.assertTrue(Triton.isMemoryTainted(0x1002))
        self.assertTrue(Triton.isMemoryTainted(0x1003))

        Triton.taintAssignment(MemoryAccess(0x1000, 4), Immediate(1, 4))
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

        Triton.taintAssignment(MemoryAccess(0x1000, 1), MemoryAccess(0x2000, 1))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

        Triton.taintAssignment(MemoryAccess(0x1000, 1), MemoryAccess(0x3000, 1))
        Triton.taintAssignment(MemoryAccess(0x2000, 1), MemoryAccess(0x3000, 1))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x1000, 1)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 1)))

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintAssignment(MemoryAccess(0x2001, 2), MemoryAccess(0x3000, 1))
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

        Triton.taintAssignment(MemoryAccess(0x2002, 2), Triton.registers.ax)
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

        Triton.taintAssignment(MemoryAccess(0x1fff, 8), Triton.registers.rax)
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

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintAssignment(Triton.registers.rax, Immediate(1, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_assignement_register_memory(self):
        """Check tainting assignment register <- memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintAssignment(Triton.registers.rax, MemoryAccess(0x2000, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintMemory(MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 8)))

        Triton.taintAssignment(Triton.registers.rax, MemoryAccess(0x2000, 8))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintAssignment(Triton.registers.rax, MemoryAccess(0x3000, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_assignement_register_register(self):
        """Check tainting assignment register <- register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintAssignment(Triton.registers.rax, Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.untaintRegister(Triton.registers.rax)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintAssignment(Triton.registers.rax, Triton.registers.rax)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rbx))
        Triton.taintRegister(Triton.registers.rbx)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rbx))

        Triton.taintAssignment(Triton.registers.rax, Triton.registers.rbx)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_union_memory_immediate(self):
        """Check tainting union memory U immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnion(MemoryAccess(0x2000, 4), Immediate(1, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_memory_memory(self):
        """Check tainting union memory U memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnion(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnion(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

        Triton.taintMemory(MemoryAccess(0x3000, 4))
        Triton.taintUnion(MemoryAccess(0x2000, 4), MemoryAccess(0x3000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x3000, 4)))

    def test_taint_union_memory_register(self):
        """Check tainting union memory U register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        Triton.taintMemory(MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.taintUnion(MemoryAccess(0x2000, 4), Triton.registers.rax)
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.untaintMemory(MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintUnion(MemoryAccess(0x2000, 4), Triton.registers.rax)
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintRegister(Triton.registers.rax)
        Triton.taintUnion(MemoryAccess(0x2000, 4), Triton.registers.rax)
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_union_register_immediate(self):
        """Check tainting union register U immediate."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintUnion(Triton.registers.rax, Immediate(1, 8))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.untaintRegister(Triton.registers.rax)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintUnion(Triton.registers.rax, Immediate(1, 8))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_union_register_memory(self):
        """Check tainting union register U memory."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintUnion(Triton.registers.rax, MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        Triton.untaintRegister(Triton.registers.rax)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintUnion(Triton.registers.rax, MemoryAccess(0x2000, 4))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertFalse(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        # !T U T
        Triton.untaintRegister(Triton.registers.rax)
        Triton.taintMemory(MemoryAccess(0x2000, 4))
        Triton.taintUnion(Triton.registers.rax, MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

        # T U T
        Triton.taintRegister(Triton.registers.rax)
        Triton.taintMemory(MemoryAccess(0x2000, 4))
        Triton.taintUnion(Triton.registers.rax, MemoryAccess(0x2000, 4))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertTrue(Triton.isMemoryTainted(MemoryAccess(0x2000, 4)))

    def test_taint_union_register_register(self):
        """Check tainting union register U register."""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.taintRegister(Triton.registers.rax)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.taintUnion(Triton.registers.rax, Triton.registers.rbx)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rbx))

        Triton.taintRegister(Triton.registers.rbx)
        Triton.taintUnion(Triton.registers.rax, Triton.registers.rbx)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rbx))

        Triton.untaintRegister(Triton.registers.rax)
        Triton.taintRegister(Triton.registers.rbx)
        Triton.taintUnion(Triton.registers.rax, Triton.registers.rbx)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rbx))

        Triton.untaintRegister(Triton.registers.rax)
        Triton.untaintRegister(Triton.registers.rbx)
        Triton.taintUnion(Triton.registers.rax, Triton.registers.rbx)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rbx))

    def test_taint_get_tainted_registers(self):
        """Get tainted registers"""
        Triton = TritonContext()
        Triton.setArchitecture(ARCH.X86_64)

        r = Triton.getTaintedRegisters()
        self.assertTrue(len(r) == 0)

        Triton.taintRegister(Triton.registers.eax)
        Triton.taintRegister(Triton.registers.ax)
        Triton.taintRegister(Triton.registers.rbx)
        Triton.taintRegister(Triton.registers.cl)
        Triton.taintRegister(Triton.registers.di)

        r = Triton.getTaintedRegisters()
        self.assertTrue(Triton.registers.rax in r)
        self.assertTrue(Triton.registers.rbx in r)
        self.assertTrue(Triton.registers.rcx in r)
        self.assertTrue(Triton.registers.rdi in r)

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

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.setTaintRegister(Triton.registers.rax, True)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.setTaintRegister(Triton.registers.rax, False)
        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))

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

        self.assertFalse(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.setTaintRegister(Triton.registers.rax, True)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

        Triton.enableTaintEngine(False)
        self.assertFalse(Triton.isTaintEngineEnabled())

        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))
        Triton.setTaintRegister(Triton.registers.rax, False)
        self.assertTrue(Triton.isRegisterTainted(Triton.registers.rax))

    def test_taint_through_pointers(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintRegister(ctx.registers.rax)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rax))

        inst = Instruction(b"\x48\x0F\xB6\x18") # movzx  rbx,BYTE PTR [rax]
        inst.setAddress(0)
        ctx.processing(inst)

        self.assertFalse(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rax)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rax))

        inst = Instruction(b"\x48\x0F\xB6\x18") # movzx  rbx,BYTE PTR [rax]
        inst.setAddress(0)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rax)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rax))

        inst = Instruction(b"\x48\x89\x18") # mov [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertFalse(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rbx)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        inst = Instruction(b"\x48\x89\x18") # mov [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rax)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rax))

        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertFalse(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rbx)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintMemory(0)
        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintMemory(0)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rax)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)

        ctx.taintRegister(ctx.registers.rbx)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintRegister(ctx.registers.rax)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rax))

        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertFalse(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintRegister(ctx.registers.rbx)
        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintMemory(0)
        inst = Instruction(b"\x48\x31\x18") # xor [rax], rbx
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isMemoryTainted(0))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintMemory(0)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintRegister(ctx.registers.rax)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertFalse(ctx.isRegisterTainted(ctx.registers.rbx))

        ###########

        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.TAINT_THROUGH_POINTERS, False)

        ctx.taintRegister(ctx.registers.rbx)
        inst = Instruction(b"\x48\x33\x18") # xor rbx, [rax]
        inst.setAddress(0x1000)
        ctx.processing(inst)

        self.assertTrue(ctx.isRegisterTainted(ctx.registers.rbx))
