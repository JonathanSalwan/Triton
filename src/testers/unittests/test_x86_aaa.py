#!/usr/bin/env python3
# coding: utf-8
"""验证 AAA 的整 AX 进位、符号关系和 AF 污点。"""

import unittest

from triton import ARCH, EXCEPTION, Instruction, TritonContext


def expected(ax, af):
    adjust = (ax & 0xf) > 9 or af == 1
    return ((ax + (0x106 if adjust else 0)) & 0xff0f), int(adjust)


class TestX86AAA(unittest.TestCase):

    def test_concrete(self):
        for ax, af in ((0x0ffa, 1), (0xfffa, 0), (0xff04, 1),
                       (0x0000, 0), (0x1239, 0), (0x12f9, 0),
                       (0x1204, 1), (0x12f9, 1), (0x12fa, 0)):
            with self.subTest(ax=hex(ax), af=af):
                ctx = TritonContext(ARCH.X86)
                ctx.setConcreteRegisterValue(ctx.registers.eax, 0xa5a50000 | ax)
                ctx.setConcreteRegisterValue(ctx.registers.af, af)
                self.assertEqual(ctx.processing(Instruction(0x1000, b"\x37")), EXCEPTION.NO_FAULT)
                result, carry = expected(ax, af)
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.eax), 0xa5a50000 | result)
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.af), carry)
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.cf), carry)

    def test_symbolic(self):
        ctx = TritonContext(ARCH.X86)
        ax = ctx.symbolizeRegister(ctx.registers.ax, "ax")
        af = ctx.symbolizeRegister(ctx.registers.af, "af")
        ctx.processing(Instruction(0x1000, b"\x37"))
        result = ctx.getRegisterAst(ctx.registers.ax)
        for value, flag in ((0x0ffa, 0), (0xfffa, 1), (0x1204, 0), (0x1204, 1)):
            with self.subTest(ax=hex(value), af=flag):
                ctx.setConcreteVariableValue(ax, value)
                ctx.setConcreteVariableValue(af, flag)
                self.assertEqual(result.evaluate(), expected(value, flag)[0])

    def test_taint(self):
        for ax_taint, af_taint in ((False, False), (True, False), (False, True), (True, True)):
            with self.subTest(ax=ax_taint, af=af_taint):
                ctx = TritonContext(ARCH.X86)
                ctx.setConcreteRegisterValue(ctx.registers.ax, 0x1204)
                if ax_taint:
                    ctx.taintRegister(ctx.registers.ax)
                if af_taint:
                    ctx.taintRegister(ctx.registers.af)
                inst = Instruction(0x1000, b"\x37")
                ctx.processing(inst)
                self.assertEqual(ctx.isRegisterTainted(ctx.registers.ax), ax_taint or af_taint)
                self.assertEqual(inst.getSymbolicExpressions()[0].isTainted(), ax_taint or af_taint)


if __name__ == "__main__":
    unittest.main()
