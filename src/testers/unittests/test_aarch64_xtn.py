#!/usr/bin/env python3
import unittest

from triton import ARCH, EXCEPTION, Instruction, TritonContext


CASES = (
    (bytes.fromhex('0028210e'), 2, 0),
    (bytes.fromhex('0028610e'), 4, 0),
    (bytes.fromhex('0028a10e'), 8, 0),
    (bytes.fromhex('2028210e'), 2, 1),
    (bytes.fromhex('2028610e'), 4, 1),
    (bytes.fromhex('2028a10e'), 8, 1),
)
SOURCE = 0x112233445566778899aabbccddeeff00
MASK128 = (1 << 128) - 1


def narrow(value, element_bytes):
    raw = value.to_bytes(16, 'little')
    result = b''.join(raw[i:i + element_bytes // 2]
                      for i in range(0, 16, element_bytes))
    return int.from_bytes(result, 'little')


class TestAArch64Xtn(unittest.TestCase):
    def context(self, source_index, value=SOURCE):
        ctx = TritonContext(ARCH.AARCH64)
        ctx.setConcreteRegisterValue(ctx.registers.v0, MASK128)
        ctx.setConcreteRegisterValue(ctx.registers.pc, 0x1000)
        src = getattr(ctx.registers, 'v%d' % source_index)
        ctx.setConcreteRegisterValue(src, value)
        return ctx, src

    def process(self, ctx, opcode):
        inst = Instruction(opcode)
        inst.setAddress(0x1000)
        self.assertEqual(ctx.processing(inst), EXCEPTION.NO_FAULT,
                         inst.getDisassembly())
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.pc), 0x1004)
        return inst

    def test_issue_1435(self):
        ctx, _ = self.context(0)
        self.process(ctx, bytes.fromhex('0028a10e'))
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.v0),
                         0x000000000000000055667788ddeeff00)

    def test_concrete(self):
        for opcode, element_bytes, source_index in CASES:
            for value in (0, MASK128, SOURCE):
                with self.subTest(opcode=opcode.hex(), value=hex(value)):
                    ctx, src = self.context(source_index, value)
                    for name, flag in zip(('n', 'z', 'c', 'v'), (1, 0, 1, 1)):
                        ctx.setConcreteRegisterValue(getattr(ctx.registers, name), flag)
                    self.process(ctx, opcode)
                    self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.v0),
                                     narrow(value, element_bytes))
                    if source_index != 0:
                        self.assertEqual(ctx.getConcreteRegisterValue(src), value)
                    for name, flag in zip(('n', 'z', 'c', 'v'), (1, 0, 1, 1)):
                        self.assertEqual(ctx.getConcreteRegisterValue(
                            getattr(ctx.registers, name)), flag)

    def test_symbolic(self):
        for opcode, element_bytes, source_index in CASES:
            with self.subTest(opcode=opcode.hex()):
                ctx, src = self.context(source_index)
                old_dst = None
                if source_index != 0:
                    old_dst = ctx.symbolizeRegister(ctx.registers.v0, 'old_dst')
                    previous = ctx.getRegisterAst(ctx.registers.v0)
                variable = ctx.symbolizeRegister(src, 'source')
                self.process(ctx, opcode)
                node = ctx.getRegisterAst(ctx.registers.v0)
                self.assertTrue(node.isSymbolized())
                self.assertEqual(node.getBitvectorSize(), 128)
                self.assertEqual(node.evaluate(), narrow(SOURCE, element_bytes))
                for bit in range(128):
                    value = SOURCE ^ (1 << bit)
                    ctx.setConcreteVariableValue(variable, value)
                    self.assertEqual(node.evaluate(), narrow(value, element_bytes),
                                     'source bit %d' % bit)
                if old_dst is not None:
                    expected = node.evaluate()
                    ctx.setConcreteVariableValue(old_dst, 0)
                    self.assertEqual(previous.evaluate(), 0)
                    self.assertEqual(node.evaluate(), expected)

    def test_taint(self):
        for opcode, _, source_index in CASES:
            states = ((False, False), (True, True)) if source_index == 0 else (
                (False, False), (False, True), (True, False), (True, True))
            for source_taint, destination_taint in states:
                with self.subTest(opcode=opcode.hex(), source=source_taint,
                                  destination=destination_taint):
                    ctx, src = self.context(source_index)
                    if source_taint:
                        ctx.taintRegister(src)
                    if destination_taint:
                        ctx.taintRegister(ctx.registers.v0)
                    self.process(ctx, opcode)
                    self.assertEqual(ctx.isRegisterTainted(ctx.registers.v0),
                                     source_taint)


if __name__ == '__main__':
    unittest.main(verbosity=2)
