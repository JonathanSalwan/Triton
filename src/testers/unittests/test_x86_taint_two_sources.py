#!/usr/bin/env python3
# coding: utf-8
"""Test that x86 instructions with two register sources taint the destination from either source."""

import unittest

from triton import ARCH, OPERAND, Instruction, TritonContext


FORMS = [
    # BMI1/BMI2, 32- and 64-bit
    "c4e270f2c2", "c4e2f0f2c2",  # andn
    "c4e270f7c2", "c4e2f0f7c2",  # bextr
    "c4e270f5c2", "c4e2f0f5c2",  # bzhi
    "c4e273f5c2", "c4e2f3f5c2",  # pdep
    "c4e272f5c2", "c4e2f2f5c2",  # pext
    # VEX, xmm0/ymm0 <- xmm1/ymm1, xmm2/ymm2
    "c5f310c2",                  # vmovsd xmm0, xmm1, xmm2
    "c5f16bc2", "c5f56bc2",      # vpackssdw
    "c5f163c2", "c5f563c2",      # vpacksswb
    "c5f167c2", "c5f567c2",      # vpackuswb
    "c5f1fcc2", "c5f5fcc2",      # vpaddb
    "c5f1fec2", "c5f5fec2",      # vpaddd
    "c5f1fdc2", "c5f5fdc2",      # vpaddw
    "c5f1dbc2", "c5f5dbc2",      # vpand
    "c5f1dfc2", "c5f5dfc2",      # vpandn
    "c5f174c2", "c5f574c2",      # vpcmpeqb
    "c5f176c2", "c5f576c2",      # vpcmpeqd
    "c4e27129c2", "c4e27529c2",  # vpcmpeqq
    "c5f175c2", "c5f575c2",      # vpcmpeqw
    "c5f164c2", "c5f564c2",      # vpcmpgtb
    "c5f166c2", "c5f566c2",      # vpcmpgtd
    "c5f165c2", "c5f565c2",      # vpcmpgtw
    "c4e37546c221",              # vperm2i128 ymm0, ymm1, ymm2, 0x21
    "c5f1f5c2", "c5f5f5c2",      # vpmaddwd
    "c5f1dac2", "c5f5dac2",      # vpminub
    "c5f1e5c2", "c5f5e5c2",      # vpmulhw
    "c5f1d5c2", "c5f5d5c2",      # vpmullw
    "c5f1ebc2", "c5f5ebc2",      # vpor
    "c5f1f1c2", "c5f5f1c2",      # vpsllw
    "c5f1e2c2", "c5f5e2c2",      # vpsrad
    "c5f1e1c2", "c5f5e1c2",      # vpsraw
    "c5f1d1c2", "c5f5d1c2",      # vpsrlw
    "c5f1f8c2", "c5f5f8c2",      # vpsubb
    "c5f1fac2", "c5f5fac2",      # vpsubd
    "c5f1fbc2", "c5f5fbc2",      # vpsubq
    "c5f1f9c2", "c5f5f9c2",      # vpsubw
    "c5f168c2", "c5f568c2",      # vpunpckhbw
    "c5f16ac2", "c5f56ac2",      # vpunpckhdq
    "c5f16dc2", "c5f56dc2",      # vpunpckhqdq
    "c5f169c2", "c5f569c2",      # vpunpckhwd
    "c5f160c2", "c5f560c2",      # vpunpcklbw
    "c5f162c2", "c5f562c2",      # vpunpckldq
    "c5f16cc2", "c5f56cc2",      # vpunpcklqdq
    "c5f161c2", "c5f561c2",      # vpunpcklwd
    "c5f1efc2", "c5f5efc2",      # vpxor
    "c5f057c2", "c5f457c2",      # vxorps
    # VEX shift by immediate: xmm1/ymm1 <- xmm2/ymm2, 3
    "c5f173fa03", "c5f573fa03",  # vpslldq
    "c5f171f203", "c5f571f203",  # vpsllw
    "c5f172e203", "c5f572e203",  # vpsrad
    "c5f171e203", "c5f571e203",  # vpsraw
    "c5f173da03", "c5f573da03",  # vpsrldq
    "c5f171d203", "c5f571d203",  # vpsrlw
]


class TestX86TaintTwoSources(unittest.TestCase):
    """The destination starts tainted; afterwards it is tainted exactly when a source register is."""

    def test_destination_taint(self):
        for code in map(bytes.fromhex, FORMS):
            probe = Instruction(0x400000, code)
            TritonContext(ARCH.X86_64).disassembly(probe)
            dst, *srcs = probe.getOperands()
            regs = [op for op in srcs if op.getType() == OPERAND.REG]
            for tainted in [None] + regs:
                with self.subTest(inst=probe.getDisassembly(), tainted=tainted and tainted.getName()):
                    ctx = TritonContext(ARCH.X86_64)
                    ctx.taintRegister(dst)
                    if tainted:
                        ctx.taintRegister(tainted)
                    inst = Instruction(0x400000, code)
                    ctx.processing(inst)
                    self.assertEqual(ctx.isRegisterTainted(dst), tainted is not None)
                    self.assertEqual(inst.isTainted(), tainted is not None)


if __name__ == "__main__":
    unittest.main()
