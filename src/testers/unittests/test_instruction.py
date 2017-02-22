#!/usr/bin/env python2
# coding: utf-8
"""Test instruction."""

import unittest

from triton import (setArchitecture, ARCH, REG, Instruction, Register,
                    processing, PREFIX, OPCODE, setConcreteRegisterValue)


class TestInstruction(unittest.TestCase):

    """Testing the Instruction class."""

    def setUp(self):
        """Define and process the instruction to test."""
        setArchitecture(ARCH.X86_64)
        self.inst = Instruction()
        self.inst.setOpcodes("\x48\x01\xd8")  # add rax, rbx
        self.inst.setAddress(0x400000)
        self.inst.updateContext(Register(REG.RAX, 0x1122334455667788))
        self.inst.updateContext(Register(REG.RBX, 0x8877665544332211))
        processing(self.inst)

    def test_address(self):
        """Check instruction current and next address."""
        self.assertEqual(self.inst.getAddress(), 0x400000)
        self.assertEqual(self.inst.getNextAddress(), 0x400003)

    def test_memory(self):
        """Check memory access."""
        self.assertListEqual(self.inst.getLoadAccess(), [])
        self.assertListEqual(self.inst.getStoreAccess(), [])
        self.assertFalse(self.inst.isMemoryWrite())
        self.assertFalse(self.inst.isMemoryRead())

    def test_registers(self):
        """Check register access."""
        self.assertEqual(len(self.inst.getReadRegisters()), 2, "access RAX and RBX")
        self.assertEqual(len(self.inst.getWrittenRegisters()), 8, "write in RAX, RIP, AF, XF, OF, PF, SF and ZF")

    def test_taints(self):
        """Check taints attributes."""
        self.assertFalse(self.inst.isTainted())

    def test_prefix(self):
        """Check prefix data."""
        self.assertFalse(self.inst.isPrefixed())
        self.assertEqual(self.inst.getPrefix(), PREFIX.INVALID)

    def test_control_flow(self):
        """Check control flow flags."""
        self.assertFalse(self.inst.isControlFlow(), "It is not a jmp, ret or call")
        self.assertFalse(self.inst.isBranch(), "It is not a jmp")

    def test_condition(self):
        """Check condition flags."""
        self.assertFalse(self.inst.isConditionTaken())

    def test_opcode(self):
        """Check opcode informations."""
        self.assertEqual(self.inst.getOpcodes(), "\x48\x01\xd8")
        self.assertEqual(self.inst.getType(), OPCODE.ADD)

    def test_thread(self):
        """Check threads information."""
        self.assertEqual(self.inst.getThreadId(), 0)

    def test_operand(self):
        """Check operand information."""
        self.assertEqual(len(self.inst.getOperands()), 2)
        self.assertEqual(self.inst.getFirstOperand().getName(), "rax")
        self.assertEqual(self.inst.getSecondOperand().getName(), "rbx")
        with self.assertRaises(Exception):
            self.inst.getThirdOperand()

    def test_symbolic(self):
        """Check symbolic information."""
        self.assertEqual(len(self.inst.getSymbolicExpressions()), 8)

    def test_size(self):
        """Check size information."""
        self.assertEqual(self.inst.getSize(), 3)

    def test_disassembly(self):
        """Check disassembly equivalent."""
        self.assertEqual(self.inst.getDisassembly(), "add rax, rbx")


class TestLoadAccess(unittest.TestCase):

    """Testing the LOAD access semantics."""

    def test_load_immediate_fs(self):
        """Check load from fs segment with immediate."""
        setArchitecture(ARCH.X86_64)

        inst = Instruction()
        # mov eax, DWORD PTR fs:0xffffffffffffdf98
        inst.setOpcodes("\x64\x8B\x04\x25\x98\xDF\xFF\xFF")
        inst.setAddress(0x400000)

        setConcreteRegisterValue(Register(REG.FS, 0x7fffda8ab700))
        processing(inst)

        self.assertTrue(inst.getLoadAccess())

        load, _ = inst.getLoadAccess()[0]
        self.assertEqual(load.getAddress(), 0x7fffda8a9698)
        self.assertEqual(load.getBitSize(), 32)

    def test_load_indirect_fs(self):
        """Check load from fs with indirect address."""
        setArchitecture(ARCH.X86_64)

        inst = Instruction()
        # mov rax, QWORD PTR fs:[rax]
        inst.setOpcodes("\x64\x48\x8B\x00")
        inst.setAddress(0x400000)

        setConcreteRegisterValue(Register(REG.FS, 0x7fffda8ab700))
        setConcreteRegisterValue(Register(REG.RAX, 0xffffffffffffdf90))
        processing(inst)

        self.assertTrue(inst.getLoadAccess())

        load, _ = inst.getLoadAccess()[0]
        self.assertEqual(load.getAddress(), 0x7fffda8a9690)
        self.assertEqual(load.getBitSize(), 64)

    def test_load_ds(self):
        """Check load from ds segment."""
        setArchitecture(ARCH.X86)

        inst = Instruction()
        # mov ax, ds:word_40213C
        inst.setOpcodes("\x66\xA1\x3C\x21\x40\x00")
        processing(inst)

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x40213C)
        self.assertEqual(inst.getOperands()[1].getBitSize(), 16)


class TestProcessing(unittest.TestCase):

    """Test processing for some error prone instruction."""

    def test_pop_esp(self):
        """Check pop on esp processing."""
        setArchitecture(ARCH.X86)

        # mov esp, 0x19fe00
        inst1 = Instruction('\xBC\x00\xFE\x19\x00')
        # mov dword ptr [esp], 0x11111111
        inst2 = Instruction('\xC7\x04\x24\x11\x11\x11\x11')
        # pop dword ptr [esp]
        inst3 = Instruction('\x8F\x04\x24')
        processing(inst1)
        processing(inst2)
        processing(inst3)

        self.assertEqual(inst3.getOperands()[0].getAddress(), 0x19fe04, "esp has been poped")
        self.assertEqual(inst3.getOperands()[0].getConcreteValue(), 0x11111111, "new value is still 0x11111111")
        self.assertEqual(inst3.getStoreAccess()[0][0].getAddress(), 0x19fe04, "inst3 set the value in 0x19fe04")
        self.assertEqual(inst3.getStoreAccess()[0][1].evaluate(), 0x11111111, "And this value is 0x11111111")

    def test_pop(self):
        """Check the pop instruction processing."""
        setArchitecture(ARCH.X86)

        # mov esp, 0x19fe00
        inst1 = Instruction('\xBC\x00\xFE\x19\x00')
        # mov edi, 0x19fe00
        inst2 = Instruction('\xBF\x00\xFE\x19\x00')
        # mov dword ptr [esp], 0x11111111
        inst3 = Instruction('\xC7\x04\x24\x11\x11\x11\x11')
        # pop dword ptr [edi]
        inst4 = Instruction('\x8F\x07')
        processing(inst1)
        processing(inst2)
        processing(inst3)
        processing(inst4)

        self.assertEqual(inst4.getOperands()[0].getAddress(), 0x19fe00, "poping edi doesn't change it")
        self.assertEqual(inst4.getOperands()[0].getConcreteValue(), 0x11111111, "pointed value in edi is the previously pointed value by esp")
        self.assertEqual(inst4.getStoreAccess()[0][0].getAddress(), 0x19fe00, "inst4 store the new value in 0x19fe00 (edi value)")
        self.assertEqual(inst4.getStoreAccess()[0][1].evaluate(), 0x11111111, "The stored value is 0x11111111")

    def test_mov_xmm_to_memory(self):
        """Check move and xmm register to memory do not crash."""
        setArchitecture(ARCH.X86_64)

        # movhpd QWORD PTR [rax], xmm1
        processing(Instruction("\x66\x0F\x17\x08"))
        # movhpd xmm1, QWORD PTR [rax]
        processing(Instruction("\x66\x0F\x16\x08"))
        # movhps QWORD PTR [rax], xmm1
        processing(Instruction("\x0F\x17\x08"))
        # movhps xmm1, QWORD PTR [rax]
        processing(Instruction("\x0F\x16\x08"))
        # movlpd QWORD PTR [rax], xmm1
        processing(Instruction("\x66\x0F\x13\x08"))
        # movlpd xmm1, QWORD PTR [rax]
        processing(Instruction("\x66\x0F\x12\x08"))
        # movlps QWORD PTR [rax], xmm1
        processing(Instruction("\x0F\x13\x08"))
        # movlps xmm1, QWORD PTR [rax]
        processing(Instruction("\x0F\x12\x08"))

    def test_mix_high_low_register(self):
        """Check operation on lower and higher register."""
        setArchitecture(ARCH.X86_64)
        inst = Instruction("\x00\xDC")  # add ah,bl
        processing(inst)
