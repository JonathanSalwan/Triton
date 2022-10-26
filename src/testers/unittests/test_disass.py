#!/usr/bin/env python3
# coding: utf-8
"""Test disassembly."""

import unittest
from triton import *

class TestAArch64Disass(unittest.TestCase):

    """Testing the AArch64 Architecture diassembly."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.AARCH64)

    def test_inst2(self):
        inst = Instruction(b"\xe1\x0b\x40\xb9") # ldr w1, [sp, #8]

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "ldr w1, [sp, #8]")

        self.assertEqual(len(inst.getOperands()), 2)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]

        self.assertEqual(op0.getName(), "w1")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getBaseRegister(), self.ctx.registers.sp)
        self.assertEqual(op1.getDisplacement().getValue(), 8)
        self.assertEqual(op1.getDisplacement().getSize(), CPUSIZE.QWORD)

    def test_inst3(self):
        inst = Instruction(b"\x20\x08\x02\x8b") # add x0, x1, x2, lsl #2

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add x0, x1, x2, lsl #2")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "x0")
        self.assertEqual(op0.getSize(), CPUSIZE.QWORD)
        self.assertEqual(op1.getName(), "x1")
        self.assertEqual(op1.getSize(), CPUSIZE.QWORD)
        self.assertEqual(op2.getName(), "x2")
        self.assertEqual(op2.getSize(), CPUSIZE.QWORD)

        self.assertEqual(op0.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op1.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getShiftType(), SHIFT.ARM.LSL)
        self.assertEqual(op2.getShiftImmediate(), 2)

    def test_inst4(self):
        inst = Instruction(b"\x20\xc0\x22\x8b") # add x0, x1, w2, sxtw

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add x0, x1, w2, sxtw")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "x0")
        self.assertEqual(op0.getSize(), CPUSIZE.QWORD)
        self.assertEqual(op1.getName(), "x1")
        self.assertEqual(op1.getSize(), CPUSIZE.QWORD)
        self.assertEqual(op2.getName(), "w2")
        self.assertEqual(op2.getSize(), CPUSIZE.DWORD)

        self.assertEqual(op0.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op1.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getExtendType(), EXTEND.ARM.SXTW)
        self.assertEqual(op2.getExtendSize(), 32)

    def test_inst5(self):
        inst = Instruction(b"\x20\x80\x22\x8b") # add x0, x1, w2, sxtb

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add x0, x1, w2, sxtb")

        op2 = inst.getOperands()[2]

        self.assertEqual(op2.getExtendType(), EXTEND.ARM.SXTB)
        self.assertEqual(op2.getExtendSize(), 56)

    def test_inst6(self):
        inst = Instruction(b"\x20\xa0\x22\x8b") # add x0, x1, w2, sxth

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add x0, x1, w2, sxth")

        op2 = inst.getOperands()[2]

        self.assertEqual(op2.getExtendType(), EXTEND.ARM.SXTH)
        self.assertEqual(op2.getExtendSize(), 48)

    def test_inst7(self):
        inst = Instruction(b"\x20\xe0\x22\x8b") # add x0, x1, x2, sxtx

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add x0, x1, x2, sxtx")

        op2 = inst.getOperands()[2]

        self.assertEqual(op2.getExtendType(), EXTEND.ARM.SXTX)
        self.assertEqual(op2.getExtendSize(), 0)


class TestArm32Disass(unittest.TestCase):

    """Testing the Arm32 Architecture diassembly."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.ARM32)

    def test_inst1(self):
        inst = Instruction(b"\x08\x00\x9d\xe5") # ldr r0, [sp, #8]

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "ldr r0, [sp, #8]")

        self.assertEqual(len(inst.getOperands()), 2)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]

        self.assertEqual(op0.getName(), "r0")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getBaseRegister(), self.ctx.registers.sp)
        self.assertEqual(op1.getDisplacement().getValue(), 8)
        self.assertEqual(op1.getDisplacement().getSize(), CPUSIZE.DWORD)

    def test_inst2(self):
        inst = Instruction(b"\x02\x01\x81\xe0") # add r0, r1, r2, lsl #2

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add r0, r1, r2, lsl #2")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "r0")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getName(), "r1")
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op2.getName(), "r2")
        self.assertEqual(op2.getSize(), CPUSIZE.DWORD)

        self.assertEqual(op0.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op1.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getShiftType(), SHIFT.ARM.LSL)
        self.assertEqual(op2.getShiftImmediate(), 2)

    def test_inst3(self):
        inst = Instruction(b"\x12\x03\x81\xe0") # add r0, r1, r2, lsl r3

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add r0, r1, r2, lsl r3")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "r0")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getName(), "r1")
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op2.getName(), "r2")
        self.assertEqual(op2.getSize(), CPUSIZE.DWORD)

        self.assertEqual(op0.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op1.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getShiftType(), SHIFT.ARM.LSL_REG)
        self.assertEqual(self.ctx.getRegister(op2.getShiftRegister()).getName(), "r3")

    def test_inst4(self):
        inst = Instruction(b"\x12\x03\x81\xe0") # add r0, r1, r2, lsl r3

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add r0, r1, r2, lsl r3")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "r0")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getName(), "r1")
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op2.getName(), "r2")
        self.assertEqual(op2.getSize(), CPUSIZE.DWORD)

        self.assertEqual(op0.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op1.getShiftType(), SHIFT.ARM.INVALID)
        self.assertEqual(op2.getShiftType(), SHIFT.ARM.LSL_REG)
        self.assertEqual(self.ctx.getRegister(op2.getShiftRegister()).getName(), "r3")

    def test_inst5(self):
        inst = Instruction(b"\x04\x00\x80\xe2") # add r0, r0, #4

        self.ctx.disassembly(inst)
        self.assertEqual(inst.getDisassembly(), "add r0, r0, #4")

        self.assertEqual(len(inst.getOperands()), 3)

        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]

        self.assertEqual(op0.getName(), "r0")
        self.assertEqual(op0.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op1.getName(), "r0")
        self.assertEqual(op1.getSize(), CPUSIZE.DWORD)
        self.assertEqual(op2.getValue(), 0x4)
        self.assertEqual(op2.getSize(), CPUSIZE.DWORD)

class TestX64Disass(unittest.TestCase):

    """Testing the X64 Architecture diassembly."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

    def test_inst1(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
            b"\x48\x89\xc8",                             # mov rax, rcx
            b"\xc9",                                     # leave
            b"\xc3",                                     # ret
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        insts = self.ctx.disassembly(0x1000, 5)
        self.assertEqual(str(insts), '[0x1000: movabs rcx, 0x1122334455667788, '
                                      '0x100a: inc rcx, '
                                      '0x100d: mov rax, rcx, '
                                      '0x1010: leave, '
                                      '0x1011: ret]')

    def test_inst2(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        insts = self.ctx.disassembly(0x1000, 5)
        self.assertEqual(str(insts), '[0x1000: movabs rcx, 0x1122334455667788, '
                                      '0x100a: inc rcx]')

    def test_inst3(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
            b"\x48\x89\xc8",                             # mov rax, rcx
            b"\xc9",                                     # leave
            b"\xc3",                                     # ret
            b"\x48\xff\xc1",                             # inc rcx
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        block = self.ctx.disassembly(0x1000)
        self.assertEqual(str(block.getInstructions()), '[0x1000: movabs rcx, 0x1122334455667788, '
                                                       '0x100a: inc rcx, '
                                                       '0x100d: mov rax, rcx, '
                                                       '0x1010: leave, '
                                                       '0x1011: ret]')

    def test_inst4(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
            b"\x48\x89\xc8",                             # mov rax, rcx
            b"\xc9",                                     # leave
            b"\xff\xe0",                                 # jmp rax
            b"\x48\xff\xc1",                             # inc rcx
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        block = self.ctx.disassembly(0x1000)
        self.assertEqual(str(block.getInstructions()), '[0x1000: movabs rcx, 0x1122334455667788, '
                                                       '0x100a: inc rcx, '
                                                       '0x100d: mov rax, rcx, '
                                                       '0x1010: leave, '
                                                       '0x1011: jmp rax]')

    def test_inst5(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
            b"\x48\x89\xc8",                             # mov rax, rcx
            b"\xc9",                                     # leave
            b"\xff\xff\xff\xff",
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        self.assertRaises(Exception, self.ctx.disassembly, 0x1000, 5)

    def test_inst6(self):
        code = [
            b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11", # mov rcx, 0x1122334455667788
            b"\x48\xff\xc1",                             # inc rcx
            b"\x48\x89\xc8",                             # mov rax, rcx
            b"\xc9",                                     # leave
            b"\xff\xff\xff\xff",
        ]
        raw = b"".join(code)
        self.ctx.setConcreteMemoryAreaValue(0x1000, raw)
        self.assertRaises(Exception, self.ctx.disassembly, 0x1000)

    def test_inst7(self):
        block = BasicBlock([
            Instruction(b"\x48\xb9\x88\x77\x66\x55\x44\x33\x22\x11"), # mov rcx, 0x1122334455667788
            Instruction(b"\x48\xff\xc1"),                             # inc rcx
            Instruction(b"\x48\x89\xc8"),                             # mov rax, rcx
            Instruction(b"\xc9"),                                     # leave
            Instruction(b"\xc3"),                                     # ret
        ])
        self.ctx.disassembly(block)
        self.assertEqual(block.getInstructions()[0].getAddress(), 0x0)

        self.ctx.disassembly(block, 0x1000)
        self.assertEqual(block.getInstructions()[0].getAddress(), 0x1000)

        self.ctx.disassembly(block)
        self.assertEqual(block.getInstructions()[0].getAddress(), 0x0)

        self.ctx.processing(block)
        self.assertEqual(block.getInstructions()[0].getAddress(), 0x0)

        self.ctx.processing(block, 0x112233)
        self.assertEqual(block.getInstructions()[0].getAddress(), 0x112233)


class TestAArch64VAS(unittest.TestCase):
    """Test aarch64 VAS type"""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.AARCH64)

    def test_1(self):
        inst = Instruction(b"\x20\x1c\x22\x2e")  # eor v0.8b, v1.8b, v2.8b
        self.ctx.disassembly(inst)
        op0 = inst.getOperands()[0]
        op1 = inst.getOperands()[1]
        op2 = inst.getOperands()[2]
        self.assertEqual(op0.getName(), "v0.8B")
        self.assertEqual(op1.getName(), "v1.8B")
        self.assertEqual(op2.getName(), "v2.8B")
        self.assertEqual(op0.getVASType(), VAS.ARM.v8B)
        self.assertEqual(op1.getVASType(), VAS.ARM.v8B)
        self.assertEqual(op2.getVASType(), VAS.ARM.v8B)
