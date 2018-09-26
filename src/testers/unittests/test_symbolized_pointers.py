#!/usr/bin/env python2
# coding: utf-8
"""Test SYMBOLIZED_POINTERS mode."""

import os
import unittest

from triton import *


class TestSymbolizedPointers(unittest.TestCase):
    """Test SYMBOLIZED_POINTERS mode"""

    def test_array(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EAX))
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EBX))
        eax = ctx.getRegisterAst(ctx.getRegister(REG.X86.EAX))
        bl = ctx.getRegisterAst(ctx.getRegister(REG.X86.BL))
        ast = ctx.getAstContext()
        a = ast.array(32)
        val = ast.select(ast.store(a, eax, bl), eax)
        self.assertFalse(ctx.isSat(val != bl))

    def test_array_concat(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EAX))
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EBX))
        eax = ctx.getRegisterAst(ctx.getRegister(REG.X86.EAX))
        ebx = ctx.getRegisterAst(ctx.getRegister(REG.X86.EBX))
        ast = ctx.getAstContext()
        a = ast.array(32)
        for i in range(4):
            a = ast.store(a, eax + i, ast.extract(8 * i + 7, 8 * i, ebx))
        val = ast.concat([ast.select(a, eax + 3 - i) for i in range(4)])
        self.assertFalse(ctx.isSat(val != ebx))

    def test_symbolic_pointers(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EAX), "eax")
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EBX), "ebx")
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.ECX), "ecx")
        eax = ctx.getRegisterAst(ctx.getRegister(REG.X86.EAX))
        ebx = ctx.getRegisterAst(ctx.getRegister(REG.X86.EBX))
        ecx = ctx.getRegisterAst(ctx.getRegister(REG.X86.ECX))
        insn = Instruction()
        insn.setOpcode("\x89\x18")
        ctx.processing(insn)
        mem = ctx.getMemoryAst(ecx, 0, 4)
        self.assertTrue(ctx.isSat(mem != ebx))
        mem = ctx.getMemoryAst(eax, 0, 4)
        self.assertFalse(ctx.isSat(mem != ebx))

    def test_symbolic_pointers_ret(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        insn = Instruction()
        insn.setOpcode("\xc3")
        self.assertTrue(ctx.processing(insn))

    def test_push_esp(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.ESP))
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.EIP))
        esp = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        code = [
            (0xdeadbeaf, "\x54"),  # push esp
            (0xdeadbeb0, "\xc3"),  # ret
        ]
        for addr, opcode in code:
            insn = Instruction()
            insn.setOpcode(opcode)
            insn.setAddress(addr)
            ctx.processing(insn)
        eip = ctx.getRegisterAst(ctx.getRegister(REG.X86.EIP))
        self.assertFalse(ctx.isSat(eip != esp))

    def test_popal(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.ESP))
        esp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        insn = Instruction()
        insn.setOpcode("\x61")  # popal
        ctx.processing(insn)
        esp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        self.assertFalse(ctx.isSat(esp_new != esp_old + 32))

    def test_popf_x86(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86.ESP))
        esp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        insn = Instruction()
        insn.setOpcode("\x66\x9d")  # popf
        ctx.processing(insn)
        esp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        self.assertFalse(ctx.isSat(esp_new != esp_old + 4))

    def test_popf_x86_64(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.SYMBOLIZED_POINTERS, True)
        ctx.convertRegisterToSymbolicVariable(ctx.getRegister(REG.X86_64.RSP))
        rsp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86_64.RSP))
        insn = Instruction()
        insn.setOpcode("\x66\x9d")  # popf
        ctx.processing(insn)
        rsp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86_64.RSP))
        self.assertFalse(ctx.isSat(rsp_new != rsp_old + 8))
