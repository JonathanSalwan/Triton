#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic."""

import unittest

from triton import (setArchitecture, ARCH, processing, REG, Instruction,
                    getSymbolicRegisterValue, enableSymbolicEngine,
                    getConcreteRegisterValue, resetEngines, MemoryAccess,
                    newSymbolicExpression, ast, CPUSIZE,
                    getSymbolicExpressionFromId, getSymbolicMemoryId,
                    getSymbolicMemoryValue, assignSymbolicExpressionToMemory,
                    assignSymbolicExpressionToRegister, buildSymbolicImmediate,
                    buildSymbolicRegister, Immediate)


class TestSymbolic(unittest.TestCase):

    """Testing the symbolic engine."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

    def test_backup(self):
        """
        Check Symbolics value are saved when engine is disable.

        * Also check reseting a disable symbolic engines doesn't crash.
        """
        inst = Instruction()
        # update RAX
        inst.setOpcodes("\x48\xFF\xC0")
        processing(inst)

        self.assertEqual(getSymbolicRegisterValue(REG.RAX), 1)

        # This call triton::api.backupSymbolicEngine()
        enableSymbolicEngine(False)

        inst = Instruction()
        # update RAX again
        inst.setOpcodes("\x48\xFF\xC0")
        processing(inst)

        self.assertEqual(getConcreteRegisterValue(REG.RAX), 2, "concrete value is updated")
        self.assertEqual(getSymbolicRegisterValue(REG.RAX), 1, "Symbolic value is not update")

        # Try to reset engine after a backup to test if the bug #385 is fixed.
        resetEngines()

    def test_bind_expr_to_memory(self):
        """Check symbolic expression binded to memory can be retrieve."""
        # Bind expr1 to 0x100
        expr1 = newSymbolicExpression(ast.bv(0x11, 8))
        mem = MemoryAccess(0x100, CPUSIZE.BYTE)
        assignSymbolicExpressionToMemory(expr1, mem)

        # Get expr from memory
        expr2 = getSymbolicExpressionFromId(getSymbolicMemoryId(0x100))

        self.assertEqual(expr1.getAst().evaluate(), expr2.getAst().evaluate())

    def test_bind_expr_to_multi_memory(self):
        """Check symbolic expression binded to multiple memory location."""
        # Bind expr to multi memory location (0x100, 0x101, 0x102, 0x103)
        expr1 = newSymbolicExpression(ast.bv(0x11223344, 32))
        mem = MemoryAccess(0x100, CPUSIZE.DWORD)
        assignSymbolicExpressionToMemory(expr1, mem)

        # Check we can get back the same values
        expr2 = getSymbolicExpressionFromId(getSymbolicMemoryId(0x100))
        expr3 = getSymbolicExpressionFromId(getSymbolicMemoryId(0x101))
        expr4 = getSymbolicExpressionFromId(getSymbolicMemoryId(0x102))
        expr5 = getSymbolicExpressionFromId(getSymbolicMemoryId(0x103))

        self.assertEqual(expr2.getAst().evaluate(), 0x44)
        self.assertEqual(expr3.getAst().evaluate(), 0x33)
        self.assertEqual(expr4.getAst().evaluate(), 0x22)
        self.assertEqual(expr5.getAst().evaluate(), 0x11)

        self.assertEqual(getSymbolicMemoryValue(mem), 0x11223344)

    def test_bind_expr_to_register(self):
        """Check symbolic expression binded to register."""
        expr1 = newSymbolicExpression(ast.bv(0x11223344, 64))
        assignSymbolicExpressionToRegister(expr1, REG.RAX)

        self.assertEqual(getSymbolicRegisterValue(REG.RAX), 0x11223344)

        expr1 = newSymbolicExpression(ast.bv(0x11223344, 32))
        with self.assertRaises(Exception):
            # Incorrect size
            assignSymbolicExpressionToRegister(expr1, REG.RAX)


class TestSymbolicBuilding(unittest.TestCase):

    """Testing symbolic building."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)

    def test_build_immediate(self):
        """Check symbolic immediate has correct size and evaluation."""
        node = buildSymbolicImmediate(Immediate(0x10, CPUSIZE.BYTE))
        self.assertEqual(node.evaluate(), 0x10)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.BYTE_BIT)

    def test_build_register(self):
        """Check symbolic register has correct size and location."""
        expr1 = newSymbolicExpression(ast.bv(0x1122334455667788, CPUSIZE.QWORD_BIT))
        assignSymbolicExpressionToRegister(expr1, REG.RAX)

        node = buildSymbolicRegister(REG.RAX)
        self.assertEqual(node.evaluate(), 0x1122334455667788)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.QWORD_BIT)

        node = buildSymbolicRegister(REG.EAX)
        self.assertEqual(node.evaluate(), 0x55667788)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.DWORD_BIT)

        node = buildSymbolicRegister(REG.AX)
        self.assertEqual(node.evaluate(), 0x7788)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.WORD_BIT)

        node = buildSymbolicRegister(REG.AH)
        self.assertEqual(node.evaluate(), 0x77)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.BYTE_BIT)

        node = buildSymbolicRegister(REG.AL)
        self.assertEqual(node.evaluate(), 0x88)
        self.assertEqual(node.getBitvectorSize(), CPUSIZE.BYTE_BIT)
