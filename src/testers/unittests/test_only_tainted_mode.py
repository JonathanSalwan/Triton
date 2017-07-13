#!/usr/bin/env python2
# coding: utf-8
"""Test ONLY_ON_TAINTED mode."""

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


class TestOnlyTaintedMode(unittest.TestCase):

    """Testing the ONLY_ON_TAINTED mode."""

    def test_1(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_TAINTED, False)

        inst = Instruction("\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)

        ctx.enableMode(MODE.ONLY_ON_TAINTED, True)

        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getSymbolicExpressions()), 0)
        self.assertEqual(len(inst.getReadRegisters()), 0)
        self.assertEqual(len(inst.getReadImmediates()), 0)
        self.assertEqual(len(inst.getWrittenRegisters()), 0)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

    def test_2(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ONLY_ON_TAINTED, True)
        ctx.taintRegister(ctx.registers.rax)

        inst = Instruction("\x48\x89\xc3") # mov rbx, rax
        self.assertTrue(ctx.processing(inst))
        self.assertTrue(checkAstIntegrity(inst))

        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)
        self.assertEqual(len(inst.getLoadAccess()), 0)
        self.assertEqual(len(inst.getStoreAccess()), 0)

