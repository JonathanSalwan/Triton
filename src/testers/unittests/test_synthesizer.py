#!/usr/bin/env python3
# coding: utf-8
"""Test synthesizing."""

import unittest
import random

from triton import *


class TestSynth_1(unittest.TestCase):
    def setUp(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

        self.ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

        x = self.ast.variable(self.ctx.newSymbolicVariable(8, 'x'))
        y = self.ast.variable(self.ctx.newSymbolicVariable(8, 'y'))
        z = self.ast.variable(self.ctx.newSymbolicVariable(32, 'z'))

        # Some obfuscated expressions
        self.obf_exprs = [
            ('(~(x) & 0xff)',        (((0xff - x) & 0xff) + (1 * (1 - 1)))),
            ('((x + 0x1) & 0xff)',   -~x & 0xff),
            ('((x + y) & 0xff)',     (x | y) + y - (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(x ^ y)',              (x | y) - y + (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(x ^ y)',              (x & ~y) | (~x & y)),                                # from ?
            ('(x | y)',              (x ^ y) + y - (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(y & x)',               -(x | y) + y + x),                                  # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(z & 0xffff00)',       ((z << 8) >> 16) << 8),                              # from https://blog.regehr.org/archives/1636
            ('((x + y) & 0xff)',     (((x ^ y) + 2 * (x & y)) * 39 + 23) * 151 + 111),    # from Ninon Eyrolle's thesis
        ]


    def test_1(self):
        for org, obfu in self.obf_exprs:
            self.assertEqual(str(self.ctx.synthesize(obfu)), org)


class TestSynth_2(unittest.TestCase):
    def setUp(self):
        self.CODE  = b"\x55\x48\x89\xE5\x89\x7D\xEC\x89\x75\xE8\x8B\x45\xE8\x23\x45\xEC"
        self.CODE += b"\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD1\x0F\xAF\xC8\x8B\x45\xEC"
        self.CODE += b"\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7\xD0\x23\x45\xEC\x0F"
        self.CODE += b"\xAF\xC2\x01\xC8\x23\x45\xE8\x89\xC2\x8B\x45\xE8\x23\x45\xEC\x89"
        self.CODE += b"\xC1\x8B\x45\xE8\x0B\x45\xEC\x89\xCE\x0F\xAF\xF0\x8B\x45\xEC\xF7"
        self.CODE += b"\xD0\x23\x45\xE8\x89\xC1\x8B\x45\xE8\xF7\xD0\x23\x45\xEC\x0F\xAF"
        self.CODE += b"\xC1\x01\xF0\x0B\x45\xE8\x89\xD6\x0F\xAF\xF0\x8B\x45\xE8\x23\x45"
        self.CODE += b"\xEC\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD1\x0F\xAF\xC8\x8B\x45"
        self.CODE += b"\xEC\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7\xD0\x23\x45\xEC"
        self.CODE += b"\x0F\xAF\xC2\x8D\x14\x01\x8B\x45\xE8\xF7\xD0\x89\xD1\x21\xC1\x8B"
        self.CODE += b"\x45\xE8\x23\x45\xEC\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD7\x0F"
        self.CODE += b"\xAF\xF8\x8B\x45\xEC\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7"
        self.CODE += b"\xD0\x23\x45\xEC\x0F\xAF\xC2\x01\xF8\xF7\xD0\x23\x45\xE8\x0F\xAF"
        self.CODE += b"\xC1\x8D\x14\x06\x8B\x45\xEC\x01\xD0\x83\xC0\x01\x89\x45\xFC\x8B"
        self.CODE += b"\x45\xFC\x5D\xC3"

    def emulate(self, ctx, pc):
        while pc:
            opcode = ctx.getConcreteMemoryAreaValue(pc, 16)
            instruction = Instruction(pc, opcode)
            ctx.processing(instruction)
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
        return

    def cb(self, ctx, node):
        synth = ctx.synthesize(node, constant=False, subexpr=False)
        if synth:
            return synth
        return node

    def init(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setMode(MODE.CONSTANT_FOLDING, True)
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

        self.ctx.symbolizeRegister(self.ctx.registers.edi, "a")
        self.ctx.symbolizeRegister(self.ctx.registers.esi, "b")
        self.ctx.setConcreteMemoryAreaValue(0x1000, self.CODE)

    def test_2(self):
        # First test using on the fly synthesis
        self.init()
        self.ctx.addCallback(CALLBACK.SYMBOLIC_SIMPLIFICATION, self.cb)
        self.emulate(self.ctx, 0x1000)
        eax  = self.ctx.getRegisterAst(self.ctx.registers.eax)
        ast  = self.ctx.getAstContext()
        res1 = str(ast.unroll(eax))

        # Second test using subexpr
        self.init()
        self.emulate(self.ctx, 0x1000)
        eax  = self.ctx.getRegisterAst(self.ctx.registers.eax)
        ast  = self.ctx.getAstContext()
        res2 = str(ast.unroll(self.ctx.synthesize(eax, constant=False, subexpr=True)))

        # Both results must be equal
        self.assertLessEqual(res1, res2)
