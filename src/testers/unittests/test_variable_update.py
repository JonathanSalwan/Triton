#!/usr/bin/env python3
# coding: utf-8
"""Test the evaluation of ASTs after a symbolic variable update."""

import unittest
from triton import *

MASK = (1 << 64) - 1
CHAIN = 20000


class TestVariableUpdate(unittest.TestCase):

    """Testing evaluation after setConcreteVariableValue."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

    def emulate(self, codes, count):
        for index in range(count):
            self.ctx.processing(Instruction(codes[index % len(codes)]))

    def chain(self, start, x, y, count):
        for _ in range(count):
            start = ((start + x) * y) & MASK
        return start

    def test_deep_reference_chain(self):
        """rax references the previous rax expression CHAIN times."""
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, 1)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rcx, 5)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdx, 3)
        x = self.ctx.symbolizeRegister(self.ctx.registers.rcx, 'x')
        y = self.ctx.symbolizeRegister(self.ctx.registers.rdx, 'y')

        # add rax, rcx; imul rax, rdx
        self.emulate([b"\x48\x01\xc8", b"\x48\x0f\xaf\xc2"], 20)
        inner = self.ctx.getSymbolicRegister(self.ctx.registers.rax).getAst()
        self.emulate([b"\x48\x01\xc8", b"\x48\x0f\xaf\xc2"], 2 * CHAIN - 20)
        root = self.ctx.getSymbolicRegister(self.ctx.registers.rax).getAst()
        self.assertEqual(root.evaluate(), self.chain(1, 5, 3, CHAIN))

        # The root first, then a node it contains
        self.ctx.setConcreteVariableValue(x, 7)
        self.assertEqual(root.evaluate(), self.chain(1, 7, 3, CHAIN))
        self.assertEqual(inner.evaluate(), self.chain(1, 7, 3, 10))

        # A contained node first, then the root
        self.ctx.setConcreteVariableValue(y, 9)
        self.assertEqual(inner.evaluate(), self.chain(1, 7, 9, 10))
        self.assertEqual(root.evaluate(), self.chain(1, 7, 9, CHAIN))

        # Several updates without evaluating in between
        for value in range(100):
            self.ctx.setConcreteVariableValue(x, value)
            self.ctx.setConcreteVariableValue(y, value + 1)
        self.assertEqual(root.evaluate(), self.chain(1, 99, 100, CHAIN))
        self.assertEqual(inner.evaluate(), self.chain(1, 99, 100, 10))

    def test_new_nodes_after_update(self):
        """Nodes built after an update over older nodes use the new value."""
        x = self.ast.variable(self.ctx.newSymbolicVariable(64, 'x'))
        older = self.ast.bvadd(x, self.ast.bv(1, 64))
        self.ctx.setConcreteVariableValue(x.getSymbolicVariable(), 10)
        newer = self.ast.bvmul(older, self.ast.bv(2, 64))
        self.assertEqual(newer.evaluate(), 22)
        self.assertEqual(older.evaluate(), 11)

    def test_unsymbolized_node(self):
        node = self.ast.bvadd(self.ast.bv(1, 64), self.ast.bv(2, 64))
        x = self.ast.variable(self.ctx.newSymbolicVariable(64, 'x'))
        self.ctx.setConcreteVariableValue(x.getSymbolicVariable(), 10)
        self.assertEqual(node.evaluate(), 3)

    def test_is_signed(self):
        x = self.ast.variable(self.ctx.newSymbolicVariable(8, 'x'))
        node = self.ast.bvadd(x, self.ast.bv(0, 8))
        self.assertFalse(node.isSigned())
        self.ctx.setConcreteVariableValue(x.getSymbolicVariable(), 0x80)
        self.assertTrue(node.isSigned())

    def test_memory_array(self):
        """A load through a store at a symbolic address follows the address variable."""
        self.ctx.setMode(MODE.MEMORY_ARRAY, True)
        self.ctx.setMode(MODE.SYMBOLIZE_STORE, True)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x2000)
        rsi = self.ctx.symbolizeRegister(self.ctx.registers.rsi, 'rsi')

        # mov byte ptr [rsi], 0x41; mov al, byte ptr [0x1000]
        self.emulate([b"\xc6\x06\x41", b"\x8a\x04\x25\x00\x10\x00\x00"], 2)
        al = self.ast.extract(7, 0, self.ctx.getSymbolicRegister(self.ctx.registers.rax).getAst())
        self.assertEqual(al.evaluate(), 0)

        self.ctx.setConcreteVariableValue(rsi, 0x1000)
        self.assertEqual(al.evaluate(), 0x41)
        self.ctx.setConcreteVariableValue(rsi, 0x2000)
        self.assertEqual(al.evaluate(), 0)


if __name__ == '__main__':
    unittest.main()
