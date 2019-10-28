#!/usr/bin/env python2
# coding: utf-8
"""Test the undefined register behavior."""

import unittest
from triton import *


class TestUndefinedRegisters(unittest.TestCase):

    """Testing the undefined register behavior."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)


    def test_undefined_on(self):
        self.ctx.setMode(MODE.CONCRETIZE_UNDEFINED_REGISTERS, True)

        trace = [
            b"\x48\xc7\xc0\x10\x00\x00\x00", # mov rax, 0x10
            b"\x48\xc7\xc3\x20\x00\x00\x00", # mov rbx, 0x20
            b"\x48\xff\xc0",                 # inc rax
            b"\x48\x31\xd8",                 # xor rax, rbx
            b"\x48\xf7\xe3",                 # mul rbx
        ]

        for op in trace:
            inst = Instruction(op)
            self.ctx.processing(inst)
            if inst.getType() == OPCODE.X86.XOR:
                self.assertEqual(len(inst.getUndefinedRegisters()), 1)
            if inst.getType() == OPCODE.X86.MUL:
                self.assertEqual(len(inst.getUndefinedRegisters()), 4)

        self.assertEqual(REG.X86_64.SF in self.ctx.getSymbolicRegisters(), False)
        self.assertEqual(REG.X86_64.ZF in self.ctx.getSymbolicRegisters(), False)
        self.assertEqual(REG.X86_64.AF in self.ctx.getSymbolicRegisters(), False)
        self.assertEqual(REG.X86_64.PF in self.ctx.getSymbolicRegisters(), False)


    def test_undefined_off(self):
        self.ctx.setMode(MODE.CONCRETIZE_UNDEFINED_REGISTERS, False)

        trace = [
            b"\x48\xc7\xc0\x10\x00\x00\x00", # mov rax, 0x10
            b"\x48\xc7\xc3\x20\x00\x00\x00", # mov rbx, 0x20
            b"\x48\xff\xc0",                 # inc rax
            b"\x48\x31\xd8",                 # xor rax, rbx
            b"\x48\xf7\xe3",                 # mul rbx
        ]

        for op in trace:
            inst = Instruction(op)
            self.ctx.processing(inst)
            if inst.getType() == OPCODE.X86.XOR:
                self.assertEqual(len(inst.getUndefinedRegisters()), 1)
            if inst.getType() == OPCODE.X86.MUL:
                self.assertEqual(len(inst.getUndefinedRegisters()), 4)

        self.assertEqual(REG.X86_64.SF in self.ctx.getSymbolicRegisters(), True)
        self.assertEqual(REG.X86_64.ZF in self.ctx.getSymbolicRegisters(), True)
        self.assertEqual(REG.X86_64.AF in self.ctx.getSymbolicRegisters(), True)
        self.assertEqual(REG.X86_64.PF in self.ctx.getSymbolicRegisters(), True)
