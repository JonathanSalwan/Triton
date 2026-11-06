#!/usr/bin/env python3
# coding: utf-8
"""Test x86 LOOPE and LOOPNE."""

import unittest

from triton import ARCH, Instruction, TritonContext


class TestX86LoopCondition(unittest.TestCase):
    """Check that LOOPE and LOOPNE decrement the counter and branch on it and ZF."""

    def test_concrete(self):
        cases = (
            # opcode, counter, zf, taken
            (b"\xe1\x10", 5, 1, True),    # loope
            (b"\xe1\x10", 5, 0, False),
            (b"\xe1\x10", 1, 1, False),
            (b"\xe0\x10", 5, 0, True),    # loopne
            (b"\xe0\x10", 5, 1, False),
            (b"\xe0\x10", 1, 0, False),
        )
        for arch, counter, pc in ((ARCH.X86, "ecx", "eip"), (ARCH.X86_64, "rcx", "rip")):
            for opcode, count, zf, taken in cases:
                with self.subTest(arch=arch, opcode=opcode, count=count, zf=zf):
                    ctx = TritonContext(arch)
                    ctx.setConcreteRegisterValue(getattr(ctx.registers, counter), count)
                    ctx.setConcreteRegisterValue(ctx.registers.zf, zf)
                    inst = Instruction(0x1000, opcode)
                    ctx.processing(inst)
                    self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, counter)), count - 1)
                    self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, pc)), 0x1012 if taken else 0x1002)
                    self.assertEqual(inst.isConditionTaken(), taken)

    def test_symbolic(self):
        for opcode, zf in ((b"\xe1\x10", 1), (b"\xe0\x10", 0)):
            with self.subTest(opcode=opcode):
                ctx = TritonContext(ARCH.X86_64)
                ctx.setConcreteRegisterValue(ctx.registers.rcx, 5)
                ctx.symbolizeRegister(ctx.registers.zf, "zf")
                ctx.processing(Instruction(0x1000, opcode))
                constraint = ctx.getPathConstraints()[0]
                self.assertTrue(constraint.isMultipleBranches())
                ast = ctx.getAstContext()
                for target, value in ((0x1012, zf), (0x1002, 1 - zf)):
                    branch = next(b for b in constraint.getBranchConstraints() if b["dstAddr"] == target)
                    model = ctx.getModel(branch["constraint"])
                    self.assertEqual(list(model.values())[0].getValue(), value)


if __name__ == '__main__':
    unittest.main()
