#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest

from triton import ARCH, REG, MODE, CPUSIZE, TritonContext, Instruction, MemoryAccess



class TestOnlySymbolizedMode(unittest.TestCase):

    """Testing the ONLY_SYMBOLIZED mode."""

    def test_1(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, False)

        inst = Instruction("\x48\x89\xc3") # mov rbx, rax
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        try:
            str(inst.getReadRegisters()[0][1])
            str(inst.getWrittenRegisters()[0][1])
            str(inst.getWrittenRegisters()[1][1])
        except:
            self.fail("test_1() raised unexpectedly!")

        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_2(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.convertRegisterToSymbolicVariable(ctx.Register(REG.X86_64.RAX))

        inst = Instruction("\x48\x89\xc3") # mov rbx, rax
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        try:
            str(inst.getReadRegisters()[0][1])
            str(inst.getWrittenRegisters()[0][1])
        except:
            self.fail("test_2() raised unexpectedly!")

    def test_3(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        try:
            str(inst.getReadRegisters()[0][1])
            str(inst.getWrittenRegisters()[0][1])
            str(inst.getWrittenRegisters()[1][1])
            str(inst.getLoadAccess()[0][1])
        except:
            self.fail("test_3() raised unexpectedly!")

    def test_4(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.convertRegisterToSymbolicVariable(ctx.Register(REG.X86_64.RAX))

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        try:
            str(inst.getReadRegisters()[0][1])
        except:
            self.fail("test_4() raised unexpectedly!")

    def test_5(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.convertMemoryToSymbolicVariable(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        try:
            str(inst.getWrittenRegisters()[0][1])
            str(inst.getLoadAccess()[0][1])
        except:
            self.fail("test_5() raised unexpectedly!")

    def test_6(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.convertRegisterToSymbolicVariable(ctx.Register(REG.X86_64.RAX))
        ctx.convertMemoryToSymbolicVariable(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 1)
        self.assertEqual(len(inst.getLoadAccess()), 1)
        self.assertEqual(len(inst.getStoreAccess()), 0)

        try:
            str(inst.getReadRegisters()[0][1])
            str(inst.getWrittenRegisters()[0][1])
            str(inst.getLoadAccess()[0][1])
        except:
            self.fail("test_6() raised unexpectedly!")

    def test_7(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setConcreteRegisterValue(ctx.Register(REG.X86_64.RAX, 0x1337))

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x1337)
        self.assertIsNone(inst.getOperands()[1].getLeaAst())

    def test_8(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)
        ctx.setConcreteRegisterValue(ctx.Register(REG.X86_64.RAX, 0x1337))
        ctx.convertRegisterToSymbolicVariable(ctx.Register(REG.X86_64.RAX))
        ctx.convertMemoryToSymbolicVariable(MemoryAccess(0, CPUSIZE.QWORD))

        inst = Instruction("\x48\x8b\x18") # mov rbx, qword ptr [rax]
        ctx.processing(inst)

        self.assertEqual(inst.getOperands()[1].getAddress(), 0x1337)
        self.assertIsNotNone(inst.getOperands()[1].getLeaAst())

        try:
            str(inst.getOperands()[1].getLeaAst())
        except:
            self.fail("test_8() raised unexpectedly!")

