#!/usr/bin/env python3
# coding: utf-8
"""Test x86 VINSERTF128, VINSERTI128, VZEROUPPER and VZEROALL against the Intel SDM pseudocode."""

import random
import unittest

from triton import ARCH, EXCEPTION, Instruction, MemoryAccess, TritonContext


LOW128 = (1 << 128) - 1
MEM = 0x1000

def pattern(seed, bits):
    return random.Random(seed).getrandbits(bits)


class TestX86AvxLanes(unittest.TestCase):

    def process(self, ctx, code):
        inst = Instruction(0x400000, code)
        self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT, inst)
        return inst

    def test_vinsert128(self):
        # (arch, code, dst, src1, src2 register or None for [MEM], imm8)
        forms = []
        for arch in (ARCH.X86, ARCH.X86_64):
            for opcode in (0x18, 0x38):  # vinsertf128, vinserti128
                for imm in (0, 1, 0xfe, 0xff):
                    forms.append((arch, bytes((0xc4, 0xe3, 0x75, opcode, 0xc2, imm)), "ymm0", "ymm1", "xmm2", imm))
                    forms.append((arch, bytes((0xc4, 0xe3, 0x75, opcode, 0x00, imm)), "ymm0", "ymm1", None, imm))
                    if arch == ARCH.X86_64:
                        forms.append((arch, bytes((0xc4, 0x43, 0x35, opcode, 0xc2, imm)), "ymm8", "ymm9", "xmm10", imm))

        for arch, code, dst, src1, src2, imm in forms:
            with self.subTest(arch=arch, code=code.hex()):
                ctx = TritonContext(arch)
                a = pattern(1, 256)
                b = pattern(2, 128)
                ctx.setConcreteRegisterValue(getattr(ctx.registers, src1), a)
                if src2 is None:
                    ctx.setConcreteRegisterValue(ctx.registers.eax if arch == ARCH.X86 else ctx.registers.rax, MEM)
                    ctx.setConcreteMemoryValue(MemoryAccess(MEM, 16), b)
                else:
                    ctx.setConcreteRegisterValue(getattr(ctx.registers, src2), b)
                self.process(ctx, code)
                expected = (a & LOW128) | b << 128 if imm & 1 else (a & ~LOW128) | b
                self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, dst)), expected)

    def test_vinsert128_symbolic(self):
        ctx = TritonContext(ARCH.X86_64)
        ctx.setConcreteRegisterValue(ctx.registers.ymm1, pattern(1, 256))
        var = ctx.symbolizeRegister(ctx.registers.xmm2, "x")
        self.process(ctx, b"\xc4\xe3\x75\x18\xc2\x01")  # vinsertf128 ymm0, ymm1, xmm2, 1
        ast = ctx.getAstContext()
        ymm0 = ctx.getRegisterAst(ctx.registers.ymm0)
        self.assertFalse(ctx.isSat(ast.extract(255, 128, ymm0) != ast.variable(var)))
        self.assertFalse(ctx.isSat(ast.extract(127, 0, ymm0) != ast.bv(pattern(1, 256) & LOW128, 128)))

    def test_vinsert128_taint(self):
        # vinsertf128 ymm0, ymm1, xmm2, imm8: ymm0 is tainted when either source is.
        for tainted in (None, "ymm1", "xmm2"):
            for imm in (0, 1):
                with self.subTest(tainted=tainted, imm=imm):
                    ctx = TritonContext(ARCH.X86_64)
                    ctx.taintRegister(ctx.registers.ymm0)
                    if tainted:
                        ctx.taintRegister(getattr(ctx.registers, tainted))
                    self.process(ctx, bytes((0xc4, 0xe3, 0x75, 0x18, 0xc2, imm)))
                    self.assertEqual(ctx.isRegisterTainted(ctx.registers.ymm0), tainted is not None)

    def check_vzero(self, arch, code, upper_only):
        ctx = TritonContext(arch)
        if arch == ARCH.X86_64:
            cleared = ["zmm%d" % i for i in range(16)]
            kept = ["zmm%d" % i for i in range(16, 32)]
            bits = 512
        else:
            cleared = ["ymm%d" % i for i in range(8)]
            kept = []
            bits = 256
        for i, reg in enumerate(cleared + kept):
            ctx.setConcreteRegisterValue(getattr(ctx.registers, reg), pattern(i, bits))
        ctx.taintRegister(getattr(ctx.registers, cleared[3]))
        self.process(ctx, code)
        for i, reg in enumerate(cleared):
            expected = pattern(i, bits) & LOW128 if upper_only else 0
            self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, reg)), expected, reg)
        for i, reg in enumerate(kept, len(cleared)):
            self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, reg)), pattern(i, bits), reg)
        self.assertEqual(ctx.isRegisterTainted(getattr(ctx.registers, cleared[3])), upper_only)

    def test_vzeroupper(self):
        for arch in (ARCH.X86, ARCH.X86_64):
            with self.subTest(arch=arch):
                self.check_vzero(arch, b"\xc5\xf8\x77", True)

    def test_vzeroall(self):
        for arch in (ARCH.X86, ARCH.X86_64):
            with self.subTest(arch=arch):
                self.check_vzero(arch, b"\xc5\xfc\x77", False)


if __name__ == "__main__":
    unittest.main()
