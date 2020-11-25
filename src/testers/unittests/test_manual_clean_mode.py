#!/usr/bin/env python
# coding: utf-8
"""Test ONLY_ON_SYMBOLIZED."""

import unittest

from triton import ARCH, MODE, CPUSIZE, TritonContext, Instruction, MemoryAccess


def checkAstIntegrity(instruction):
    """
    This function check if all ASTs under an Instruction class are still
    available.
    """
    try:
        for se in instruction.getSymbolicExpressions():
            str(se.getAst())

        for x, y in instruction.getLoadAccess():
            str(y)

        for x, y in instruction.getStoreAccess():
            str(y)

        for x, y in instruction.getReadRegisters():
            str(y)

        for x, y in instruction.getWrittenRegisters():
            str(y)

        for x, y in instruction.getReadImmediates():
            str(y)

        return True

    except:
        return False


class TestOnlySymbolizedMode(unittest.TestCase):

    """Testing the MANUAL_CLEAN_INSTRUCTION mode."""

    def test_1(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, False)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)

        inst = Instruction(b"\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_2(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.symbolizeRegister(ctx.registers.rax)

        inst = Instruction(b"\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))

        ctx.manualClearInstruction(inst)

        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_3(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))

        ctx.manualClearInstruction(inst)

        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_4(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.symbolizeRegister(ctx.registers.rax)

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_5(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.symbolizeMemory(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_6(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.symbolizeRegister(ctx.registers.rax)
        ctx.symbolizeMemory(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))

        ctx.manualClearInstruction(inst)

        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_7(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.setConcreteRegisterValue(ctx.registers.rax, 0x1337)

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x1337)
        self.assertIsNotNone(inst.getOperands()[1].getLeaAst())
        self.assertTrue(inst.isMemoryRead())

        ctx.manualClearInstruction(inst)
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x1337)
        self.assertIsNone(inst.getOperands()[1].getLeaAst())

    def test_8(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        ctx.setConcreteRegisterValue(ctx.registers.rax, 0x1337)
        ctx.symbolizeRegister(ctx.registers.rax)
        ctx.symbolizeMemory(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction(b"\x48\x8b\x18") # mov rbx, qword ptr [rax]
        self.assertTrue(ctx.processing(inst))

        ctx.manualClearInstruction(inst)
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x1337)
        self.assertIsNotNone(inst.getOperands()[1].getLeaAst())

    def test_9(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.setMode(MODE.ONLY_ON_TAINTED, False)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        self.assertEqual(ctx.isModeEnabled(MODE.ONLY_ON_TAINTED), False)
        self.assertEqual(ctx.isModeEnabled(MODE.MANUAL_CLEAN_INSTRUCTION), True)

        inst = Instruction(b"\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.manualClearInstruction(inst)
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.assertEqual(ctx.isModeEnabled(MODE.ONLY_ON_TAINTED), True)

        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getSymbolicExpressions()), 0)
        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getReadImmediates()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_10(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)

        self.assertEqual(ctx.isModeEnabled(MODE.ONLY_ON_TAINTED), False)
        ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.assertEqual(ctx.isModeEnabled(MODE.ONLY_ON_TAINTED), True)

        self.assertEqual(ctx.isModeEnabled(MODE.MANUAL_CLEAN_INSTRUCTION), False)
        ctx.setMode(MODE.MANUAL_CLEAN_INSTRUCTION, True)
        self.assertEqual(ctx.isModeEnabled(MODE.MANUAL_CLEAN_INSTRUCTION), True)

        ctx.taintRegister(ctx.registers.rax)

        inst = Instruction(b"\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        ctx.manualClearInstruction(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)
