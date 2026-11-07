#!/usr/bin/env python3
# coding: utf-8
"""Test MODE.INTEL_UNDEFINED_FLAGS: the values Intel processors write to flags the manual leaves undefined."""

import unittest

from triton import ARCH, MODE, Instruction, TritonContext


# (code, result register, result width, {flag: rule}); rules: "0", "parity" (low byte of the result), "msb"
FORMS = [
    ("21d1",       "ecx", 32, {"af": "0"}),                                   # and ecx, edx
    ("4809d1",     "rcx", 64, {"af": "0"}),                                   # or rcx, rdx
    ("30d1",       "cl",   8, {"af": "0"}),                                   # xor cl, dl
    ("6685d1",     "cx",  16, {"af": "0"}),                                   # test cx, dx
    ("c1e105",     "ecx", 32, {"af": "0"}),                                   # shl ecx, 5
    ("c1e905",     "ecx", 32, {"af": "0"}),                                   # shr ecx, 5
    ("c1f905",     "ecx", 32, {"af": "0", "of": "0"}),                        # sar ecx, 5
    ("0fa4d105",   "ecx", 32, {"af": "0"}),                                   # shld ecx, edx, 5
    ("0facd105",   "ecx", 32, {"af": "0"}),                                   # shrd ecx, edx, 5
    ("f6e2",       "al",   8, {"af": "0", "pf": "parity", "sf": "msb"}),      # mul dl
    ("f7e2",       "eax", 32, {"af": "0", "pf": "parity", "sf": "msb"}),      # mul edx
    ("48f7e2",     "rax", 64, {"af": "0", "pf": "parity", "sf": "msb"}),      # mul rdx
    ("f7ea",       "eax", 32, {"af": "0", "pf": "parity", "sf": "msb"}),      # imul edx
    ("660fafca",   "cx",  16, {"af": "0", "pf": "parity", "sf": "msb"}),      # imul cx, dx
    ("6bca07",     "ecx", 32, {"af": "0", "pf": "parity", "sf": "msb"}),      # imul ecx, edx, 7
    ("0fbcca",     "ecx", 32, {"af": "0", "cf": "0", "of": "0", "sf": "0"}),  # bsf ecx, edx
    ("0fbdca",     "ecx", 32, {"af": "0", "cf": "0", "of": "0", "sf": "0"}),  # bsr ecx, edx
    ("f30fbdca",   "ecx", 32, {"af": "0", "of": "0", "sf": "0", "pf": "0"}),  # lzcnt ecx, edx
    ("f30fbcca",   "ecx", 32, {"af": "0", "of": "0", "sf": "0", "pf": "0"}),  # tzcnt ecx, edx
    ("c4e270f2ca", "ecx", 32, {"af": "0", "pf": "0"}),                        # andn ecx, ecx, edx
    ("c4e270f7ca", "ecx", 32, {"af": "0", "pf": "0", "sf": "0"}),             # bextr ecx, edx, ecx
    ("c4e270f3da", "ecx", 32, {"af": "0", "pf": "0"}),                        # blsi ecx, edx
    ("c4e270f3d2", "ecx", 32, {"af": "0", "pf": "0"}),                        # blsmsk ecx, edx
    ("c4e270f3ca", "ecx", 32, {"af": "0", "pf": "0"}),                        # blsr ecx, edx
    ("c4e270f5ca", "ecx", 32, {"af": "0", "pf": "0"}),                        # bzhi ecx, edx, ecx
]

VALUES = [(0x1234567890abcdef, 0x0fedcba987654321), (0x80, 0x81), (0xffffffffffffffff, 0x10), (0x7f0, 0x8000000000000003)]
FLAGS = ("cf", "pf", "af", "zf", "sf", "of")


class TestX86IntelUndefinedFlags(unittest.TestCase):

    def run_form(self, code, rax_rcx, rdx, mode):
        ctx = TritonContext(ARCH.X86_64)
        ctx.setMode(MODE.INTEL_UNDEFINED_FLAGS, mode)
        ctx.setConcreteRegisterValue(ctx.registers.rax, rax_rcx)
        ctx.setConcreteRegisterValue(ctx.registers.rcx, rax_rcx)
        ctx.setConcreteRegisterValue(ctx.registers.rdx, rdx)
        for flag in FLAGS:
            ctx.setConcreteRegisterValue(getattr(ctx.registers, flag), 1)
        inst = Instruction(0x1000, bytes.fromhex(code))
        ctx.processing(inst)
        return ctx, inst

    def test_mode(self):
        for code, reg, width, rules in FORMS:
            for a, b in VALUES:
                with self.subTest(code=code, a=hex(a), b=hex(b)):
                    ctx, inst = self.run_form(code, a, b, True)
                    result = ctx.getConcreteRegisterValue(getattr(ctx.registers, reg))
                    undefined = {r.getName() for r in inst.getUndefinedRegisters()}
                    for flag, rule in rules.items():
                        expected = {"0": 0, "parity": int(bin(result & 0xff).count("1") % 2 == 0),
                                    "msb": result >> (width - 1) & 1}[rule]
                        self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, flag)), expected, flag)
                        self.assertNotIn(flag, undefined)

    def test_default_unchanged(self):
        # Without the mode the flags keep their previous value (1 here); those Triton tagged undefined stay tagged.
        for code, reg, width, rules in FORMS:
            with self.subTest(code=code):
                ctx, inst = self.run_form(code, 0x80, 0x81, False)
                for flag in rules:
                    self.assertEqual(ctx.getConcreteRegisterValue(getattr(ctx.registers, flag)), 1, flag)


if __name__ == "__main__":
    unittest.main()
