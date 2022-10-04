#!/usr/bin/env python3
# coding: utf-8
"""Test instruction."""

import unittest

from triton import (ARCH, Instruction, PREFIX, OPCODE, TritonContext)


class TestInstruction(unittest.TestCase):

    """Testing the Instruction class."""

    def setUp(self):
        """Define and process the instruction to test."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.inst = Instruction()
        self.inst.setOpcode(b"\x48\x01\xd8")  # add rax, rbx
        self.inst.setAddress(0x400000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0x1122334455667788)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0x8877665544332211)
        self.ctx.processing(self.inst)

    def test_address(self):
        """Check instruction current and next address."""
        self.assertEqual(self.inst.getAddress(), 0x400000)
        self.assertEqual(self.inst.getNextAddress(), 0x400003)

        inst = Instruction()
        inst.setAddress(-1)
        self.assertEqual(inst.getAddress(), 0xffffffffffffffff)

        inst.setAddress(-2)
        self.assertEqual(inst.getAddress(), 0xfffffffffffffffe)

        inst.setAddress(-3)
        self.assertEqual(inst.getAddress(), 0xfffffffffffffffd)

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
        self.assertEqual(self.inst.getPrefix(), PREFIX.X86.INVALID)

    def test_control_flow(self):
        """Check control flow flags."""
        self.assertFalse(self.inst.isControlFlow(), "It is not a jmp, ret or call")
        self.assertFalse(self.inst.isBranch(), "It is not a jmp")

    def test_condition(self):
        """Check condition flags."""
        self.assertFalse(self.inst.isConditionTaken())

    def test_opcode(self):
        """Check opcode informations."""
        self.assertEqual(self.inst.getOpcode(), b"\x48\x01\xd8")
        self.assertEqual(self.inst.getType(), OPCODE.X86.ADD)

    def test_thread(self):
        """Check threads information."""
        self.assertEqual(self.inst.getThreadId(), 0)

    def test_operand(self):
        """Check operand information."""
        self.assertEqual(len(self.inst.getOperands()), 2)
        self.assertEqual(self.inst.getOperands()[0].getName(), "rax")
        self.assertEqual(self.inst.getOperands()[1].getName(), "rbx")
        with self.assertRaises(Exception):
            self.inst.getOperands()[2]

    def test_symbolic(self):
        """Check symbolic information."""
        self.assertEqual(len(self.inst.getSymbolicExpressions()), 8)

    def test_size(self):
        """Check size information."""
        self.assertEqual(self.inst.getSize(), 3)

    def test_disassembly(self):
        """Check disassembly equivalent."""
        self.assertEqual(self.inst.getDisassembly(), "add rax, rbx")

    def test_constructor(self):
        """Check opcode informations."""
        inst1 = Instruction()
        inst2 = Instruction(b"\xc3")
        inst3 = Instruction(0x1000, b"\xc3")
        self.assertEqual(inst1.getOpcode(), b"")
        self.assertEqual(inst1.getAddress(), 0)
        self.assertEqual(inst2.getOpcode(), b"\xc3")
        self.assertEqual(inst2.getAddress(), 0)
        self.assertEqual(inst3.getOpcode(), b"\xc3")
        self.assertEqual(inst3.getAddress(), 0x1000)


class TestLoadAccess(unittest.TestCase):

    """Testing the LOAD access semantics."""

    def test_load_immediate_fs(self):
        """Check load from fs segment with immediate."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        inst = Instruction()
        # mov eax, DWORD PTR fs:0xffffffffffffdf98
        inst.setOpcode(b"\x64\x8B\x04\x25\x98\xDF\xFF\xFF")
        inst.setAddress(0x400000)

        self.ctx.setConcreteRegisterValue(self.ctx.registers.fs, 0x7fffda8ab700)
        self.ctx.processing(inst)

        self.assertTrue(inst.getLoadAccess())

        load, _ = inst.getLoadAccess()[0]
        self.assertEqual(load.getAddress(), 0x7fffda8a9698)
        self.assertEqual(load.getBitSize(), 32)

    def test_load_indirect_fs(self):
        """Check load from fs with indirect address."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        inst = Instruction()
        # mov rax, QWORD PTR fs:[rax]
        inst.setOpcode(b"\x64\x48\x8B\x00")
        inst.setAddress(0x400000)

        self.ctx.setConcreteRegisterValue(self.ctx.registers.fs, 0x7fffda8ab700)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0xffffffffffffdf90)
        self.ctx.processing(inst)

        self.assertTrue(inst.getLoadAccess())

        load, _ = inst.getLoadAccess()[0]
        self.assertEqual(load.getAddress(), 0x7fffda8a9690)
        self.assertEqual(load.getBitSize(), 64)

    def test_load_ds(self):
        """Check load from ds segment."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

        inst = Instruction()
        # mov ax, ds:word_40213C
        inst.setOpcode(b"\x66\xA1\x3C\x21\x40\x00")
        self.ctx.processing(inst)

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x40213C)
        self.assertEqual(inst.getOperands()[1].getBitSize(), 16)


class TestProcessing(unittest.TestCase):

    """Test processing for some error prone instruction."""

    def test_pop_esp(self):
        """Check pop on esp processing."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

        # mov esp, 0x19fe00
        inst1 = Instruction(b'\xBC\x00\xFE\x19\x00')
        # mov dword ptr [esp], 0x11111111
        inst2 = Instruction(b'\xC7\x04\x24\x11\x11\x11\x11')
        # pop dword ptr [esp]
        inst3 = Instruction(b'\x8F\x04\x24')
        self.ctx.processing(inst1)
        self.ctx.processing(inst2)
        self.ctx.processing(inst3)

        self.assertEqual(inst3.getOperands()[0].getAddress(), 0x19fe04, "esp has been poped")
        self.assertEqual(inst3.getStoreAccess()[0][0].getAddress(), 0x19fe04, "inst3 set the value in 0x19fe04")
        self.assertEqual(inst3.getStoreAccess()[0][1].evaluate(), 0x11111111, "And this value is 0x11111111")

    def test_pop(self):
        """Check the pop instruction processing."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)

        # mov esp, 0x19fe00
        inst1 = Instruction(b'\xBC\x00\xFE\x19\x00')
        # mov edi, 0x19fe00
        inst2 = Instruction(b'\xBF\x00\xFE\x19\x00')
        # mov dword ptr [esp], 0x11111111
        inst3 = Instruction(b'\xC7\x04\x24\x11\x11\x11\x11')
        # pop dword ptr [edi]
        inst4 = Instruction(b'\x8F\x07')
        self.ctx.processing(inst1)
        self.ctx.processing(inst2)
        self.ctx.processing(inst3)
        self.ctx.processing(inst4)

        self.assertEqual(inst4.getOperands()[0].getAddress(), 0x19fe00, "poping edi doesn't change it")
        self.assertEqual(inst4.getStoreAccess()[0][0].getAddress(), 0x19fe00, "inst4 store the new value in 0x19fe00 (edi value)")
        self.assertEqual(inst4.getStoreAccess()[0][1].evaluate(), 0x11111111, "The stored value is 0x11111111")

    def test_mov_xmm_to_memory(self):
        """Check move and xmm register to memory do not crash."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        # movhpd QWORD PTR [rax], xmm1
        self.ctx.processing(Instruction(b"\x66\x0F\x17\x08"))
        # movhpd xmm1, QWORD PTR [rax]
        self.ctx.processing(Instruction(b"\x66\x0F\x16\x08"))
        # movhps QWORD PTR [rax], xmm1
        self.ctx.processing(Instruction(b"\x0F\x17\x08"))
        # movhps xmm1, QWORD PTR [rax]
        self.ctx.processing(Instruction(b"\x0F\x16\x08"))
        # movlpd QWORD PTR [rax], xmm1
        self.ctx.processing(Instruction(b"\x66\x0F\x13\x08"))
        # movlpd xmm1, QWORD PTR [rax]
        self.ctx.processing(Instruction(b"\x66\x0F\x12\x08"))
        # movlps QWORD PTR [rax], xmm1
        self.ctx.processing(Instruction(b"\x0F\x13\x08"))
        # movlps xmm1, QWORD PTR [rax]
        self.ctx.processing(Instruction(b"\x0F\x12\x08"))

    def test_mix_high_low_register(self):
        """Check operation on lower and higher register."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        inst = Instruction(b"\x00\xDC")  # add ah,bl
        self.ctx.processing(inst)


class TestMemoryAccess(unittest.TestCase):

    """Testing the memory access."""

    def test_memory_access_1(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        inst = Instruction(b"\x88\x4f\x0d") # mov byte ptr [rdi + 0xd], cl
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getReadRegisters()), 2)

    def test_memory_access_2(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        inst = Instruction(b"\x48\x89\x4f\x0d") # mov [rdi + 0xd], rcx
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getReadRegisters()), 2)

    def test_memory_access_3(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        inst = Instruction(b"\x48\x8b\x4f\x0d") # mov rcx, [rdi + 0xd]
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getReadRegisters()), 1)

    def test_memory_access_4(self):
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        inst = Instruction(b"\x8a\x4f\x0d") # mov cl, byte ptr [rdi + 0xd]
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getReadRegisters()), 1)


class Test869(unittest.TestCase):

    """Testing jcxz instructions."""

    def test_1(self):
        ctx = TritonContext(ARCH.X86_64)
        ctx.processing(Instruction(0x1000, b"\x48\xff\xc1")) # inc rcx
        ctx.processing(Instruction(0x2000, b"\xe3\x30")) # jrcxz 0x32
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.rip), 0x2002)

    def test_2(self):
        ctx = TritonContext(ARCH.X86_64)
        ctx.processing(Instruction(0x1000, b"\x48\x31\xc9")) # xor rcx, rcx
        ctx.processing(Instruction(0x2000, b"\xe3\x30")) # jrcxz 0x32
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.rip), 0x2032)

    def test_3(self):
        ctx = TritonContext(ARCH.X86)
        ctx.processing(Instruction(0x1000, b"\x41")) # inc rcx
        ctx.processing(Instruction(0x2000, b"\xe3\x30")) # jecxz 0x32
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.eip), 0x2002)

    def test_4(self):
        ctx = TritonContext(ARCH.X86)
        ctx.processing(Instruction(0x1000, b"\x31\xc9")) # xor rcx, rcx
        ctx.processing(Instruction(0x2000, b"\xe3\x30")) # jecxz 0x32
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.eip), 0x2032)

class TestX86ParityFlag(unittest.TestCase):

    """Testing the parity flag of Intel x86."""

    def setUp(self):
        """Define and process the instruction to test."""
        self.ctx = TritonContext(ARCH.X86_64)
        self.inst = Instruction(b"\x48\x01\xd8") # add rax, rbx

    def test_pf1(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1100)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 1)

    def test_pf2(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1101)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 0)

    def test_pf3(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1110)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 0)

    def test_pf4(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1111)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 1)

    def test_pf5(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1000000000000001)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 0)

    def test_pf6(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1000000000000011)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 1)

    def test_pf7(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1110000000000011)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 1)

    def test_pf8(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1110000000000010)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 0)

    def test_pf9(self):
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbx, 0b1110000000000000)
        self.ctx.processing(self.inst)
        self.assertEqual(self.ctx.getConcreteRegisterValue(self.ctx.registers.pf), 1)
