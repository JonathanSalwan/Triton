#!/usr/bin/env python3
# coding: utf-8
"""Test Stubs."""

import unittest

from triton import *


class TestStubsx8664(unittest.TestCase):
    """Testing stubs."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setConcreteMemoryAreaValue(0x66600000, STUBS.X8664.SYSTEMV.LIBC.code)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x7ffffff0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7ffffff0)

    def emulate(self, pc):
        while pc:
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
        return

    def test_strlen(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strlen"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 12)

    def test_strcmp(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x2000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strcmp"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0)

    def test_strtoul1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"123456")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdx, 10)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strtoul"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 123456)

    def test_strtoul2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"0xdeadbeef")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdx, 16)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strtoul"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0xdeadbeef)

    def test_atoi1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"12345")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["atoi"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 12345)

    def test_atoi2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"-1")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["atoi"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0xffffffffffffffff)

    def test_a64l1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"zz1")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["a64l"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0x3fff)

    def test_a64l2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"FT")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["a64l"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 2001)

    def test_strncasecmp(self):
        # Equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton StuBS")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn stUbS")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x2000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdx, 12)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strncasecmp"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertEqual(rax, 0)

        # Not equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton St..S")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn stUbS")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, 0x2000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdx, 12)
        self.emulate(0x66600000 + STUBS.X8664.SYSTEMV.LIBC.symbols["strncasecmp"])
        rax = self.ctx.getConcreteRegisterValue(self.ctx.registers.rax)
        self.assertNotEqual(rax, 0)


class TestStubsi386(unittest.TestCase):
    """Testing stubs."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.X86)
        self.ctx.setConcreteMemoryAreaValue(0x66600000, STUBS.I386.SYSTEMV.LIBC.code)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.esp, 0x7ffffff0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.ebp, 0x7ffffff0)

    def emulate(self, pc):
        while pc != 0:
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
        return

    def push_stack(self, value):
        esp = self.ctx.getConcreteRegisterValue(self.ctx.registers.esp)
        self.ctx.setConcreteMemoryValue(MemoryAccess(esp, CPUSIZE.DWORD), value)
        esp -= CPUSIZE.DWORD
        self.ctx.setConcreteRegisterValue(self.ctx.registers.esp, esp)
        return

    def test_strlen(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.push_stack(0x1000) # arg1
        self.emulate(0x66600000 + STUBS.I386.SYSTEMV.LIBC.symbols["strlen"])
        eax = self.ctx.getConcreteRegisterValue(self.ctx.registers.eax)
        self.assertEqual(eax, 12)

    def test_strncasecmp(self):
        # Equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton StuBS")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn stUbS")
        self.push_stack(12) # arg3
        self.push_stack(0x2000) # arg2
        self.push_stack(0x1000) # arg1
        self.emulate(0x66600000 + STUBS.I386.SYSTEMV.LIBC.symbols["strncasecmp"])
        eax = self.ctx.getConcreteRegisterValue(self.ctx.registers.eax)
        self.assertEqual(eax, 0)

        # Not Equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton StuBS")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn st..S")
        self.push_stack(12) # arg3
        self.push_stack(0x2000) # arg2
        self.push_stack(0x1000) # arg1
        self.emulate(0x66600000 + STUBS.I386.SYSTEMV.LIBC.symbols["strncasecmp"])
        eax = self.ctx.getConcreteRegisterValue(self.ctx.registers.eax)
        self.assertNotEqual(eax, 0)

    def test_strtoull(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"0x1122334455667788")
        self.push_stack(0x1000) # arg1
        self.emulate(0x66600000 + STUBS.I386.SYSTEMV.LIBC.symbols["strtoull"])
        eax = self.ctx.getConcreteRegisterValue(self.ctx.registers.eax)
        edx = self.ctx.getConcreteRegisterValue(self.ctx.registers.edx)
        self.assertEqual(eax, 0x55667788)
        self.assertEqual(edx, 0x11223344)


class TestStubsAArch64(unittest.TestCase):
    """Testing stubs."""

    def setUp(self):
        self.ctx = TritonContext(ARCH.AARCH64)
        self.ctx.setConcreteMemoryAreaValue(0x66600000, STUBS.AARCH64.LIBC.code)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.sp, 0x7ffffff0)

    def emulate(self, pc):
        while pc:
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 4)
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.pc)
        return

    def test_strlen(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strlen"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 12)

    def test_strcmp(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"triton stubs")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"triton stubs")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0x2000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strcmp"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 0)

    def test_strtoul1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"123456")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x2, 10)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strtoul"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 123456)

    def test_strtoul2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"0xdeadbeef")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x2, 16)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strtoul"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 0xdeadbeef)

    def test_atoi1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"12345")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["atoi"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 12345)

    def test_atoi2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"-1")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["atoi"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 0xffffffffffffffff)

    def test_a64l1(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"zz1")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["a64l"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 0x3fff)

    def test_a64l2(self):
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"FT")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["a64l"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 2001)

    def test_strncasecmp(self):
        # Equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton StuBS")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn stUbS")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0x2000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x2, 12)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strncasecmp"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertEqual(x0, 0)

        # Not equal
        self.ctx.setConcreteMemoryAreaValue(0x1000, b"trIton St..S")
        self.ctx.setConcreteMemoryAreaValue(0x2000, b"TritOn stUbS")
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x0, 0x1000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x1, 0x2000)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.x2, 12)
        self.emulate(0x66600000 + STUBS.AARCH64.LIBC.symbols["strncasecmp"])
        x0 = self.ctx.getConcreteRegisterValue(self.ctx.registers.x0)
        self.assertNotEqual(x0, 0)
