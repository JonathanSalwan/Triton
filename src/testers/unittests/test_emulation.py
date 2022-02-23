#!/usr/bin/env python3
# coding: utf-8
"""Test synthesizing."""

import unittest
import os

from triton import *


class TestEmulation(unittest.TestCase):
    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "md5", "md5-x64")
        self.binary = self.loadBinary(binary_file)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x7fffffff)

        self.ctx.symbolizeMemory(MemoryAccess(0x2049, CPUSIZE.BYTE))
        self.ctx.symbolizeMemory(MemoryAccess(0x204a, CPUSIZE.BYTE))
        self.ctx.symbolizeMemory(MemoryAccess(0x204b, CPUSIZE.BYTE))
        self.ctx.symbolizeMemory(MemoryAccess(0x204c, CPUSIZE.BYTE))
        self.ctx.symbolizeMemory(MemoryAccess(0x204d, CPUSIZE.BYTE))
        self.ctx.symbolizeMemory(MemoryAccess(0x204e, CPUSIZE.BYTE))

        self.ctx.taintMemory(MemoryAccess(0x2049, CPUSIZE.BYTE))
        self.ctx.taintMemory(MemoryAccess(0x204a, CPUSIZE.BYTE))
        self.ctx.taintMemory(MemoryAccess(0x204b, CPUSIZE.BYTE))
        self.ctx.taintMemory(MemoryAccess(0x204c, CPUSIZE.BYTE))
        self.ctx.taintMemory(MemoryAccess(0x204d, CPUSIZE.BYTE))
        self.ctx.taintMemory(MemoryAccess(0x204e, CPUSIZE.BYTE))

    def emulate(self, pc):
        while pc:
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
        return

    def loadBinary(self, path):
        import lief
        # Map the binary into the memory
        binary = lief.parse(path)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            self.ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)
        return binary

    def start(self):
        self.emulate(0x1743)

        s0 = self.ctx.getMemoryAst(MemoryAccess(0x41A0, CPUSIZE.DWORD))
        s1 = self.ctx.getMemoryAst(MemoryAccess(0x41A0 + 4, CPUSIZE.DWORD))
        s2 = self.ctx.getMemoryAst(MemoryAccess(0x41A0 + 8, CPUSIZE.DWORD))
        s3 = self.ctx.getMemoryAst(MemoryAccess(0x41A0 + 12, CPUSIZE.DWORD))

        self.assertEqual(s0.evaluate(), 0xa1ff6be2)
        self.assertEqual(s1.evaluate(), 0xc8985752)
        self.assertEqual(s2.evaluate(), 0xd2a8dce1)
        self.assertEqual(s3.evaluate(), 0xa899a435)

    def test_1(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.start()

    def test_2(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.start()

    def test_3(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.start()

    def test_3(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.start()

    def test_4(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.start()

    def test_5(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.CONCRETIZE_UNDEFINED_REGISTERS, True)
        self.start()

    def test_6(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.start()

    def test_7(self):
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        self.start()

    def test_8(self):
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        self.start()

    def test_9(self):
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        self.start()

    def test_10(self):
        self.ctx.setMode(MODE.ONLY_ON_TAINTED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        self.start()

    def test_11(self):
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        self.start()
