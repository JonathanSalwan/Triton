#!/usr/bin/env python2
# coding: utf-8
"""Test architectures."""

import unittest
from triton import *


class TestASTUndefined(unittest.TestCase):

    """Testing the undefined node."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.enableMode(MODE.CONCRETIZE_UNDEFINED_NODE, True)


    def test_undefined(self):
        trace = [
            "\x48\xc7\xc0\x10\x00\x00\x00", # mov rax, 0x10
            "\x48\xc7\xc3\x20\x00\x00\x00", # mov rbx, 0x20
            "\x48\xff\xc0",                 # inc rax
            "\x48\x31\xd8",                 # xor rax, rbx
            "\x48\xf7\xe3",                 # mul rbx
        ]

        for op in trace:
            inst = Instruction(op)
            self.ctx.processing(inst)

            if inst.getType() == OPCODE.X86.XOR:
                self.assertEqual(len(inst.getUndefinedRegisters()), 1)

            if inst.getType() == OPCODE.X86.MUL:
                self.assertEqual(len(inst.getUndefinedRegisters()), 4)
