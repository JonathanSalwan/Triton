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

        c = self.ast.variable(self.ctx.newSymbolicVariable(8, 'c'))
        x = self.ast.variable(self.ctx.newSymbolicVariable(8, 'x'))
        y = self.ast.variable(self.ctx.newSymbolicVariable(8, 'y'))
        z = self.ast.variable(self.ctx.newSymbolicVariable(32, 'z'))

        # Some obfuscated expressions
        self.obf_exprs = [
            ('(~(x) & 0xff)',                                               (((0xff - x) & 0xff) + (1 * (1 - 1)))),
            ('((x + 0x1) & 0xff)',                                          -~x & 0xff),
            ('((x + y) & 0xff)',                                            (x | y) + y - (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(x ^ y)',                                                     (x | y) - y + (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(x ^ y)',                                                     (x & ~y) | (~x & y)),                                # from ?
            ('(x | y)',                                                     (x ^ y) + y - (~x & y)),                             # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(y & x)',                                                      -(x | y) + y + x),                                  # from http://archive.bar/pdfs/bar2020-preprint9.pdf
            ('(z & 0xffff00)',                                              ((z << 8) >> 16) << 8),                              # from https://blog.regehr.org/archives/1636
            ('((x + y) & 0xff)',                                            (((x ^ y) + 2 * (x & y)) * 39 + 23) * 151 + 111),    # from Ninon Eyrolle's thesis
            ('(x ^ 0x5c)',                                                  self.x_xor_92_obfuscated(x)),                        # from imassage
            ('((0x2 * (c ^ 0x1)) & 0xff)',                                  self.opaque_constant(x, y, c)),                      # from ?
            ('(((bswap(z, 32) ^ 0x23746fbe) + 0xfffffffd) & 0xffffffff)',   self.bswap32_xor_const(z)),                          # from UnityPlayer.dll
        ]

    def bswap32_xor_const(self, x):
        a = ((~((((((x & 0xff)) << 8 | ((x >> 8) & 0xff)) << 8 | ((x >> 16) & 0xff)) << 8 | ((x >> 24) & 0xff)))) & 0xd7848ce1)
        b = ((((((x & 0xff)) << 8 | ((x >> 8) & 0xff)) << 8 | ((x >> 16) & 0xff)) << 8 | ((x >> 24) & 0xff)) & 0x287b731e)
        return ((( a | b ) ^ 0xf4f0e35f) + 0xfffffffd)

    def x_xor_92_obfuscated(self, x):
        a = 229 * x + 247
        b = 237 * a + 214 + ((38 * a + 85) & 254)
        c = (b + ((-(2 * b) + 255) & 254)) * 3 + 77
        d = ((86 * c + 36) & 70) * 75 + 231 * c + 118
        e = ((58 * d + 175) & 244) + 99 * d + 46
        f = (e & 148)
        g = (f - (e & 255) + f) * 103 + 13
        R = (237 * (45 * g + (174 * g | 34) * 229 + 194 - 247) & 255)
        return R

    def opaque_constant(self, a, b, c):
        op1 = (2 * (b & ~a) + ( -1 * (~ a | b) + ( -1 * ~( a & b) + (2 * ~( a | b) + 1 * a )))) # 0 (opaque constant)
        op2 = (a | b) - (a + b) + (a & b)                                                       # 0 (opaque constant)
        n = op1 + (1 << op2)                                                                    # 0 + 1
        n = (op1 + 2) * (c ^ n)                                                                 # (0 + 2) * (c ^ 1)
        return n

    def test_1(self):
        for org, obfu in self.obf_exprs:
            self.assertEqual(str(self.ctx.synthesize(obfu, constant=True, subexpr=True, opaque=True)), org)


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

    def init(self):
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

        self.ctx.symbolizeRegister(self.ctx.registers.edi, "a")
        self.ctx.symbolizeRegister(self.ctx.registers.esi, "b")
        self.ctx.setConcreteMemoryAreaValue(0x1000, self.CODE)

    def test_2(self):
        self.init()
        self.emulate(self.ctx, 0x1000)
        eax = self.ctx.getRegisterAst(self.ctx.registers.eax)
        ast = self.ctx.getAstContext()
        res = str(ast.unroll(self.ctx.synthesize(eax, constant=False, subexpr=True)))
        self.assertLessEqual(res, "(bvadd (bvadd a (bvmul (bvmul a b) b)) (_ bv1 32))")
