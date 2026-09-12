#!/usr/bin/env python3
# coding: utf-8
"""Test x86 PUSH operand sizes and stack writes."""

import unittest

from triton import ARCH, EXCEPTION, Instruction, TritonContext


class TestX86Push(unittest.TestCase):
    """Check immediate, register and memory PUSH forms."""

    def test_operand_sizes(self):
        cases = (
            ("imm8 positive", "6a 7f", False, 0x7f),
            ("imm8 negative", "6a ff", False, -1),
            ("imm32 positive", "68 7f 00 00 00", False, 0x7f),
            ("imm32 negative", "68 00 ff ff ff", False, -256),
            ("imm8 positive override", "66 6a 7f", True, 0x7f),
            ("imm8 negative override", "66 6a ff", True, -1),
            ("imm16 positive", "66 68 7f 00", True, 0x7f),
            ("imm16 issue1450", "66 68 00 ff", True, 0xff00),
            ("register", "50", False, 0x12345678),
            ("register override", "66 50", True, 0x5678),
            ("memory", "ff 33", False, 0x12345678),
            ("memory override", "66 ff 33", True, 0x5678),
        )

        for arch, default_size in ((ARCH.X86, 4), (ARCH.X86_64, 8)):
            for name, encoding, operand16, value in cases:
                with self.subTest(arch=arch, case=name):
                    ctx = TritonContext(arch)
                    if arch == ARCH.X86:
                        sp = ctx.registers.esp
                        accumulator = ctx.registers.eax
                        base = ctx.registers.ebx
                        initial_sp = 0x11000
                    else:
                        sp = ctx.registers.rsp
                        accumulator = ctx.registers.rax
                        base = ctx.registers.rbx
                        initial_sp = 0x100001000

                    size = 2 if operand16 else default_size
                    expected_sp = initial_sp - size
                    expected_value = value & ((1 << (size * 8)) - 1)
                    expected_bytes = expected_value.to_bytes(size, "little")

                    ctx.setConcreteRegisterValue(sp, initial_sp)
                    ctx.setConcreteRegisterValue(accumulator, 0x12345678)
                    ctx.setConcreteRegisterValue(base, 0x2000)
                    ctx.setConcreteMemoryAreaValue(
                        0x2000, (0x12345678).to_bytes(default_size, "little")
                    )
                    ctx.setConcreteMemoryAreaValue(
                        initial_sp - 16, b"\xa5" * 32
                    )

                    inst = Instruction(0x400000, bytes.fromhex(encoding))
                    self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                    self.assertEqual(
                        ctx.getConcreteRegisterValue(sp), expected_sp
                    )

                    stores = inst.getStoreAccess()
                    self.assertEqual(len(stores), 1)
                    memory, expression = stores[0]
                    self.assertEqual(memory.getAddress(), expected_sp)
                    self.assertEqual(memory.getSize(), size)
                    self.assertEqual(expression.getBitvectorSize(), size * 8)
                    self.assertEqual(expression.evaluate(), expected_value)

                    expected_memory = (
                        b"\xa5" * (16 - size)
                        + expected_bytes
                        + b"\xa5" * 16
                    )
                    self.assertEqual(
                        ctx.getConcreteMemoryAreaValue(initial_sp - 16, 32),
                        expected_memory,
                    )


if __name__ == "__main__":
    unittest.main()
