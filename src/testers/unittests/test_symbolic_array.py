#!/usr/bin/env python3
# coding: utf-8
"""Test Symbolic Array."""

import unittest
from triton import *


class TestSymbolicArray(unittest.TestCase):

    """Testing symbolic array."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setMode(MODE.MEMORY_ARRAY, True)
        self.ctx.setMode(MODE.SYMBOLIZE_LOAD, True)
        self.ctx.setMode(MODE.SYMBOLIZE_STORE, True)

    def test_1(self):
        code = [
            b"\x48\xc7\xc0\x00\x10\x00\x00", # mov rax, 0x1000
            b"\x48\xc7\xc3\x32\x00\x00\x00", # mov rbx, 0x32
            b"\xc7\x04\x18\xad\xde\x00\x00", # mov dword ptr [rax + rbx], 0xdead
            b"\x48\x81\xf6\xef\xbe\x00\x00", # xor rsi, 0xbeef
            b"\x48\x8b\x0e", # mov rcx, [rsi]
            b"\x48\x81\xf9\xad\xde\x00\x00", # cmp rcx, 0xdead
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for op in code:
            i = Instruction(op)
            self.ctx.processing(i)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.getModel(zf == 1)
        self.assertEqual(m[0].getValue(), 0xaedd)

    def test_2(self):
        code = [
            (1, b"\x48\xc7\xc0\x00\x10\x00\x00"), # mov rax, 0x1000
            (2, b"\x48\xc7\xc3\x32\x00\x00\x00"), # mov rbx, 0x32
            (3, b"\xc7\x04\x18\xad\xde\x00\x00"), # mov dword ptr [rax + rbx], 0xdead
            (4, b"\x48\x8b\x0e"), # mov rcx, [rsi]
            (5, b"\x48\x81\xf9\xad\xde\x00\x00"), # cmp rcx, 0xdead
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for _, op in code:
            i = Instruction(op)
            self.ctx.processing(i)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.getModel(zf == 1)
        self.assertEqual(m[0].getValue(), 0x1032)

    def test_3(self):
        code = [
            (1, b"\x48\xc7\xc0\x00\x10\x00\x00"), # mov rax, 0x1000
            (2, b"\x48\xc7\xc3\x32\x00\x00\x00"), # mov rbx, 0x32
            (3, b"\x89\x34\x18"), # mov dword ptr [rax + rbx], esi
            (4, b"\x8b\x0c\x18"), # mov ecx, dword ptr [rax + rbx]
            (5, b"\x48\x81\xf9\xad\xde\x00\x00"), # cmp rcx, 0xdead
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for i, op in code:
            inst = Instruction(op)
            self.ctx.processing(inst)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.getModel(zf == 1)
        self.assertEqual(m[0].getValue(), 0xdead)

    def test_4(self):
        code = [
            (1, b"\x48\xc7\xc0\x00\x10\x00\x00"), # mov rax, 0x1000
            (2, b"\x48\xc7\xc3\x32\x00\x00\x00"), # mov rbx, 0x32
            (3, b"\x89\x34\x18"), # mov dword ptr [rax + rbx], esi
            (4, b"\x8b\x0c\x18"), # mov ecx, dword ptr [rax + rbx]
            (5, b"\x48\x81\xf9\xad\xde\x00\x00"), # cmp rcx, 0xdead
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for i, op in code:
            if i == 4:
                self.ctx.concretizeMemory(0x1032)
            inst = Instruction(op)
            self.ctx.processing(inst)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.isSat(zf == 1)
        self.assertEqual(m, False)

    def test_5(self):
        code = [
            (1, b"\x48\xc7\xc0\x00\x10\x00\x00"), # mov rax, 0x1000
            (2, b"\x48\xc7\xc3\x32\x00\x00\x00"), # mov rbx, 0x32
            (3, b"\x89\x34\x18"), # mov dword ptr [rax + rbx], esi
            (4, b"\x8b\x0c\x18"), # mov ecx, dword ptr [rax + rbx]
            (5, b"\x48\x81\xf9\xad\xde\x00\x00"), # cmp rcx, 0xdead
        ]

        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0xdeae)
        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')

        for i, op in code:
            if i == 4:
                self.ctx.concretizeMemory(0x1033)
            inst = Instruction(op)
            self.ctx.processing(inst)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.isSat(zf == 1)
        self.assertEqual(m, True)

    def test_6(self):
        code = [
            b"\x48\x8b\x3e", # mov rdi, [rsi]
            b"\x81\xff\x44\x33\x22\x11", # cmp edi, 0x11223344
        ]

        self.ctx.symbolizeRegister(self.ctx.registers.rsi, 's_rsi')
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x99\x88\x77\x66\x55\x44\x33\x22\x11\x00\xaa\xbb\xcc")

        for op in code:
            inst = Instruction(op)
            self.ctx.processing(inst)

        zf = self.ctx.getRegisterAst(self.ctx.registers.zf)
        m = self.ctx.getModel(zf == 1)
        self.assertEqual(m[0].getValue(), 0x1005)

    def test_7(self):
        code = [
            b"\x8b\x3e", # mov edi, dword ptr [rsi]
        ]

        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x1005)
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x99\x88\x77\x66\x55\x44\x33\x22\x11\x00\xaa\xbb\xcc")

        for op in code:
            inst = Instruction(op)
            self.ctx.processing(inst)

        edi = self.ctx.getRegisterAst(self.ctx.registers.edi)
        self.assertEqual(edi.evaluate(), 0x11223344)

    def test_8(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"\x99\x88\x77\x66\x55\x44\x33\x22\x11\x00\xaa\xbb\xcc")

        value = self.ctx.getSymbolicMemoryValue(0x1000)
        self.assertEqual(value, 0x99)

        value = self.ctx.getSymbolicMemoryValue(MemoryAccess(0x1000, 4))
        self.assertEqual(value, 0x66778899)

    def test_9(self):
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)

        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.symbolizeRegister(self.ctx.registers.rsi)
        inst = Instruction(b"\x48\x89\x37") # mov [rdi], rsi
        self.ctx.processing(inst)

        e = self.ctx.getSymbolicMemory(0x1000)
        self.assertEqual(str(e), "(define-fun ref!9 () (Array (_ BitVec 64) (_ BitVec 8)) (store ref!8 (_ bv4096 64) ((_ extract 7 0) ref!0))) ; Byte reference - MOV operation")

        e = self.ctx.getMemoryAst(MemoryAccess(0x1000, 1))
        self.assertEqual(str(e), "(select ref!9 (_ bv4096 64))")

        es = self.ctx.getSymbolicMemory()
        self.assertEqual(len(es), 8) # 8 bytes

        sym = self.ctx.isMemorySymbolized(0x1000)
        self.assertTrue(sym)

        sym = self.ctx.isMemorySymbolized(0x1008)
        self.assertFalse(sym)
