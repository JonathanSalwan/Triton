#!/usr/bin/env python3
# coding: utf-8
"""Test x86 ADOX, BZHI, PDEP and PEXT against the Intel SDM pseudocode."""

import unittest

from triton import ARCH, EXCEPTION, Instruction, TritonContext


VALUES = (0, 1, 0x7f, 0x80, 0xffff, 0x80000000, 0xffffffff, 0x100000000, 0x5555555555555555,
          0x8000000000000001, 0x123456789abcdef0, 0xffffffffffffffff)


def ref_pdep(src, mask, size):
    result, k = 0, 0
    for i in range(size):
        if mask >> i & 1:
            result |= (src >> k & 1) << i
            k += 1
    return result


def ref_pext(src, mask, size):
    result, k = 0, 0
    for i in range(size):
        if mask >> i & 1:
            result |= (src >> i & 1) << k
            k += 1
    return result


class TestX86Bmi2Adx(unittest.TestCase):
    """Run each instruction on concrete values and compare with the SDM pseudocode."""

    def run_inst(self, code, regs, flags=None):
        ctx = TritonContext(ARCH.X86_64)
        for reg, value in regs.items():
            ctx.setConcreteRegisterValue(getattr(ctx.registers, reg), value)
        for flag, value in (flags or {}).items():
            ctx.setConcreteRegisterValue(getattr(ctx.registers, flag), value)
        self.assertEqual(ctx.processing(Instruction(0x400000, code)), EXCEPTION.NO_FAULT)
        return ctx

    def test_adox(self):
        for code, size in ((b"\xf3\x0f\x38\xf6\xc3", 32), (b"\xf3\x48\x0f\x38\xf6\xc3", 64)):
            mask = (1 << size) - 1
            for a in VALUES:
                for b in VALUES:
                    for of in (0, 1):
                        with self.subTest(size=size, a=hex(a), b=hex(b), of=of):
                            ctx = self.run_inst(code, {"rax": a, "rbx": b}, {"of": of, "cf": 1})
                            total = (a & mask) + (b & mask) + of
                            self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.rax), total & mask)
                            self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.of), total >> size)
                            self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.cf), 1)

    def test_bzhi(self):
        for code, size in ((b"\xc4\xe2\x70\xf5\xc3", 32), (b"\xc4\xe2\xf0\xf5\xc3", 64)):
            mask = (1 << size) - 1
            for a in VALUES:
                for index in (0, 1, 8, 31, 32, 33, 63, 64, 255, 0x1f01, 0xff20):
                    with self.subTest(size=size, a=hex(a), index=hex(index)):
                        ctx = self.run_inst(code, {"rax": 0x5a5a5a5a5a5a5a5a, "rbx": a, "rcx": index})
                        n = index & 0xff
                        expected = a & mask if n >= size else a & ((1 << n) - 1)
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.rax), expected)
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.cf), int(n > size - 1))
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.zf), int(expected == 0))
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.sf), expected >> (size - 1) & 1)
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.of), 0)

    def test_pdep_pext(self):
        forms = ((b"\xc4\xe2\x63\xf5\xc1", 32, ref_pdep), (b"\xc4\xe2\xe3\xf5\xc1", 64, ref_pdep),
                 (b"\xc4\xe2\x62\xf5\xc1", 32, ref_pext), (b"\xc4\xe2\xe2\xf5\xc1", 64, ref_pext))
        for code, size, ref in forms:
            mask = (1 << size) - 1
            for src in VALUES:
                for sel in VALUES + (0xffffffff00000304,):
                    with self.subTest(op=ref.__name__, size=size, src=hex(src), mask=hex(sel)):
                        ctx = self.run_inst(code, {"rax": 0x5a5a5a5a5a5a5a5a, "rbx": src, "rcx": sel})
                        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.rax),
                                         ref(src & mask, sel & mask, size))


if __name__ == "__main__":
    unittest.main()
