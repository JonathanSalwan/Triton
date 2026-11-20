#!/usr/bin/env python3
"""Regressions for AArch64 extended operands and partial vector writes."""

import unittest

from triton import ARCH, EXCEPTION, Instruction, TritonContext


class TestAArch64ExtendedOperands(unittest.TestCase):
    """Check that register extension precedes the optional left shift."""

    def test_add_uxtb_reported_case(self):
        """Keep bits shifted beyond the source byte in the reported ADD."""
        ctx = TritonContext(ARCH.AARCH64)
        ctx.setConcreteRegisterValue(ctx.registers.x22, 0x71210cd220)
        ctx.setConcreteRegisterValue(ctx.registers.x0, 0x25)
        inst = Instruction(0x1000, bytes.fromhex('c80e208b'))
        self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.x8),
                         0x71210cd348)

    def test_add_extended_shift_overflow(self):
        """Preserve shifted bits for unsigned and signed 32/64-bit additions."""
        for width, suffix in ((32, '0b'), (64, '8b')):
            for option, bits, signed in (
                    ('0e', 8, False), ('2e', 16, False), ('4e', 32, False),
                    ('8e', 8, True), ('ae', 16, True), ('ce', 32, True)):
                opcode = bytes.fromhex('c8' + option + '20' + suffix)
                for symbolic in (False, True):
                    with self.subTest(opcode=opcode.hex(), symbolic=symbolic):
                        ctx = TritonContext(ARCH.AARCH64)
                        base = 0x71210cd220
                        ctx.setConcreteRegisterValue(ctx.registers.x22, base)
                        variable = None
                        if symbolic:
                            variable = ctx.symbolizeRegister(ctx.registers.x0)
                        for value in (0, 0x25, 1 << (bits - 1), (1 << bits) - 1,
                                      0x1122334400000025):
                            if symbolic:
                                ctx.setConcreteVariableValue(variable, value)
                            else:
                                ctx.setConcreteRegisterValue(ctx.registers.x0, value)
                            inst = Instruction(0x1000, opcode)
                            self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                            extended = value & ((1 << bits) - 1)
                            if signed and extended & (1 << (bits - 1)):
                                extended -= 1 << bits
                            expected = (base + (extended << 3)) & ((1 << width) - 1)
                            self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.x8),
                                             expected)
                            node = ctx.getRegisterAst(ctx.registers.x8)
                            self.assertEqual(node.evaluate(), expected)
                            self.assertEqual(node.isSymbolized(), symbolic)


class TestAArch64MovLanes(unittest.TestCase):
    """Check that MOV replaces only the selected vector element."""

    # Opcode, element width, destination index, source index.
    CASES = (
        ('017c016e', 8, 0, 15),
        ('01041f6e', 8, 15, 0),
        ('0174026e', 16, 0, 7),
        ('01141e6e', 16, 7, 1),
        ('0124046e', 32, 0, 1),
        ('01240c6e', 32, 1, 1),
        ('0124146e', 32, 2, 1),
        ('01641c6e', 32, 3, 3),
        ('0144086e', 64, 0, 1),
        ('0124186e', 64, 1, 0),
    )
    SOURCE = 0x112233445566778899aabbccddeeff00
    DESTINATION = 0xfedcba98765432100123456789abcdef

    def test_reported_case(self):
        """Write the high source word to the high destination word only."""
        ctx = TritonContext(ARCH.AARCH64)
        ctx.setConcreteRegisterValue(ctx.registers.q0, self.SOURCE)
        ctx.setConcreteRegisterValue(ctx.registers.q1, (1 << 128) - 1)
        inst = Instruction(0x1000, bytes.fromhex('01641c6e'))
        self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.q1),
                         0x11223344ffffffffffffffffffffffff)

    def test_concrete_lanes(self):
        """Preserve every unselected byte with distinct source/destination data."""
        for opcode, bits, dst_index, src_index in self.CASES:
            with self.subTest(opcode=opcode):
                ctx = TritonContext(ARCH.AARCH64)
                ctx.setConcreteRegisterValue(ctx.registers.q0, self.SOURCE)
                ctx.setConcreteRegisterValue(ctx.registers.q1, self.DESTINATION)
                inst = Instruction(0x1000, bytes.fromhex(opcode))
                self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                mask = (1 << bits) - 1
                element = (self.SOURCE >> (bits * src_index)) & mask
                expected = ((self.DESTINATION & ~(mask << (bits * dst_index))) |
                            (element << (bits * dst_index)))
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.q1), expected)
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.q0), self.SOURCE)
                self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.pc), 0x1004)

    def test_symbolic_lanes(self):
        """Keep dependencies on the source lane and the untouched destination lanes."""
        for opcode, bits, dst_index, src_index in self.CASES:
            with self.subTest(opcode=opcode):
                ctx = TritonContext(ARCH.AARCH64)
                source = ctx.symbolizeRegister(ctx.registers.q0)
                destination = ctx.symbolizeRegister(ctx.registers.q1)
                previous = ctx.getRegisterAst(ctx.registers.q1)
                inst = Instruction(0x1000, bytes.fromhex(opcode))
                self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                node = ctx.getRegisterAst(ctx.registers.q1)
                self.assertEqual(node.getBitvectorSize(), 128)
                self.assertTrue(node.isSymbolized())
                mask = (1 << bits) - 1
                for src_value, dst_value in ((self.SOURCE, self.DESTINATION),
                                             (self.DESTINATION, self.SOURCE),
                                             (0, (1 << 128) - 1)):
                    ctx.setConcreteVariableValue(source, src_value)
                    ctx.setConcreteVariableValue(destination, dst_value)
                    self.assertEqual(previous.evaluate(), dst_value)
                    element = (src_value >> (bits * src_index)) & mask
                    expected = ((dst_value & ~(mask << (bits * dst_index))) |
                                (element << (bits * dst_index)))
                    self.assertEqual(node.evaluate(), expected)

    def test_overlapping_register(self):
        """Read both elements before updating a vector used as its own source."""
        ctx = TritonContext(ARCH.AARCH64)
        ctx.setConcreteRegisterValue(ctx.registers.q0, self.SOURCE)
        inst = Instruction(0x1000, bytes.fromhex('0024146e'))
        self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.q0),
                         0x1122334499aabbcc99aabbccddeeff00)

    def test_general_register_and_whole_vector_moves(self):
        """Support lane insertion from W registers and existing MOV forms."""
        for opcode, destination, expected in (
                ('011c0c4e', 'q1', 0xfedcba98765432107654321089abcdef),
                ('013c1c0e', 'x1', 0x11223344),
                ('011ca04e', 'q1', self.SOURCE)):
            with self.subTest(opcode=opcode):
                ctx = TritonContext(ARCH.AARCH64)
                ctx.setConcreteRegisterValue(ctx.registers.q0, self.SOURCE)
                ctx.setConcreteRegisterValue(ctx.registers.q1, self.DESTINATION)
                ctx.setConcreteRegisterValue(ctx.registers.x0, 0xfedcba9876543210)
                ctx.setConcreteRegisterValue(ctx.registers.x1, (1 << 64) - 1)
                inst = Instruction(0x1000, bytes.fromhex(opcode))
                self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                self.assertEqual(ctx.getConcreteRegisterValue(
                    getattr(ctx.registers, destination)), expected)

    def test_taint(self):
        """Retain destination taint because a lane write preserves other elements."""
        for src_taint, dst_taint in ((False, False), (False, True),
                                     (True, False), (True, True)):
            with self.subTest(source=src_taint, destination=dst_taint):
                ctx = TritonContext(ARCH.AARCH64)
                if src_taint:
                    ctx.taintRegister(ctx.registers.q0)
                if dst_taint:
                    ctx.taintRegister(ctx.registers.q1)
                inst = Instruction(0x1000, bytes.fromhex('01641c6e'))
                self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT)
                self.assertEqual(ctx.isRegisterTainted(ctx.registers.q1),
                                 src_taint or dst_taint)


if __name__ == '__main__':
    unittest.main()
