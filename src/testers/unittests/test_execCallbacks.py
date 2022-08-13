#!/usr/bin/env python3
# coding: utf-8
"""Test execCallbacks."""

import unittest

from triton import *

class TestExecCallbacks(unittest.TestCase):
    """Testing execCallbacks."""

    def setUp(self):
        self.log_trace = False

        self.function = {
            0x401000: b"\x55",                 #  push   ebp
            0x401001: b"\x8b\xec",             #  mov    ebp,             esp
            0x401003: b"\x6b\x45\x08\x06",     #  imul   eax,             DWORD PTR [ebp+0x8], 0x6
            0x401007: b"\x8b\x4d\x0c",         #  mov    ecx,             DWORD PTR [ebp+0xc]
            0x40100a: b"\x89\x01",             #  mov    DWORD PTR [ecx], eax
            0x40100c: b"\xb8\x01\x00\x00\x00", #  mov    eax,             0x1
            0x401011: b"\x5d",                 #  pop    ebp
            0x401012: b"\xc3",                 #  ret
        }

        self.expect = [
            # (trace type, R/W, target, data)
            ('REG', 'R', 'ebp', 0x7ffff0),
            ('REG', 'R', 'esp', 0x7ffff0),
            ('REG', 'W', 'esp', 0x7fffec),
            ('MEM', 'W', MemoryAccess(0x7fffec, 4), 0x7ffff0),
            ('REG', 'W', 'eip', 0x401001),
            ('REG', 'R', 'esp', 0x7fffec),
            ('REG', 'W', 'ebp', 0x7fffec),
            ('REG', 'W', 'eip', 0x401003),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('MEM', 'R', MemoryAccess(0x7ffff4, 4), 0x4),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('REG', 'W', 'eax', 0x18),
            ('REG', 'W', 'cf', 0x0),
            ('REG', 'W', 'of', 0x0),
            ('REG', 'W', 'eip', 0x401007),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('MEM', 'R', MemoryAccess(0x7ffff8, 4), 0x5fffa0),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('REG', 'R', 'ebp', 0x7fffec),
            ('REG', 'W', 'ecx', 0x5fffa0),
            ('REG', 'W', 'eip', 0x40100a),
            ('REG', 'R', 'ecx', 0x5fffa0),
            ('REG', 'R', 'eax', 0x18),
            ('REG', 'R', 'ecx', 0x5fffa0),
            ('MEM', 'W', MemoryAccess(0x5fffa0, 4), 0x18),
            ('REG', 'W', 'eip', 0x40100c),
            ('REG', 'W', 'eax', 0x1),
            ('REG', 'W', 'eip', 0x401011),
            ('REG', 'R', 'esp', 0x7fffec),
            ('MEM', 'R', MemoryAccess(0x7fffec, 4), 0x7ffff0),
            ('REG', 'W', 'ebp', 0x7ffff0),
            ('REG', 'R', 'esp', 0x7fffec),
            ('REG', 'W', 'esp', 0x7ffff0),
            ('REG', 'W', 'eip', 0x401012),
            ('REG', 'R', 'esp', 0x7ffff0),
            ('MEM', 'R', MemoryAccess(0x7ffff0, 4), 0x400400),
            ('REG', 'W', 'eip', 0x400400),
            ('REG', 'R', 'esp', 0x7ffff0),
            ('REG', 'W', 'esp', 0x7ffff4),
        ]

        self.actual = list()
        self.trace = iter(self.expect)

        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86)
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

        if self.log_trace:
            self.ctx.setConcreteRegisterValue(self.ctx.registers.ebp, 0x7FFFF0)
            self.ctx.setConcreteRegisterValue(self.ctx.registers.esp, 0x7FFFF0)
            self.ctx.setConcreteRegisterValue(self.ctx.registers.esp, 0x7FFFF0)
            self.ctx.setConcreteMemoryValue(MemoryAccess(0x7FFFF0, 4), 0x400400)
            self.ctx.setConcreteMemoryValue(MemoryAccess(0x7FFFF4, 4), 4)
            self.ctx.setConcreteMemoryValue(MemoryAccess(0x7FFFF8, 4), 0x5FFFA0)

        self.ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.mem_read_cb)
        self.ctx.addCallback(CALLBACK.SET_CONCRETE_MEMORY_VALUE, self.mem_write_cb)
        self.ctx.addCallback(CALLBACK.GET_CONCRETE_REGISTER_VALUE, self.reg_read_cb)
        self.ctx.addCallback(CALLBACK.SET_CONCRETE_REGISTER_VALUE, self.reg_write_cb)

    def mem_read_cb(self, ctx, mem):
        if self.log_trace:
            print('(\'MEM\', \'R\', MemoryAccess({}, {}), {}),'.format(
                hex(mem.getAddress()),
                mem.getSize(),
                hex(ctx.getConcreteMemoryValue(mem, callbacks=False)),
            ))
            return
        event = next(self.trace, None)
        self.assertIsNotNone(event)
        (eType, eAction, eTarget, eValue) = event
        self.assertEqual(eType, 'MEM')
        self.assertEqual(eAction, 'R')
        self.assertEqual(eTarget.getSize(), mem.getSize())
        self.assertEqual(eTarget.getAddress(), mem.getAddress())
        if ctx.isConcreteMemoryValueDefined(mem):
            self.assertEqual(eValue, ctx.getConcreteMemoryValue(mem, callbacks=False))
        else:
            ctx.setConcreteMemoryValue(mem, eValue, callbacks=False)
        self.actual.append(event)

    def mem_write_cb(self, ctx, mem, value):
        if self.log_trace:
            print('(\'MEM\', \'W\', MemoryAccess({}, {}), {}),'.format(
                hex(mem.getAddress()),
                mem.getSize(),
                hex(value),
            ))
            return
        event = next(self.trace, None)
        self.assertIsNotNone(event)
        (eType, eAction, eTarget, eValue) = event
        self.assertEqual(eType, 'MEM')
        self.assertEqual(eAction, 'W')
        self.assertEqual(eTarget.getSize(), mem.getSize())
        self.assertEqual(eTarget.getAddress(), mem.getAddress())
        self.assertEqual(eValue, value)
        self.actual.append(event)

    def reg_read_cb(self, ctx, reg):
        if self.log_trace:
            print('(\'REG\', \'R\', \'{}\', {}),'.format(
                reg.getName(),
                hex(ctx.getConcreteRegisterValue(reg, callbacks=False)),
            ))
            return
        event = next(self.trace, None)
        self.assertIsNotNone(event)
        (eType, eAction, eTarget, eValue) = event
        self.assertEqual(eType, 'REG')
        self.assertEqual(eAction, 'R')
        self.assertEqual(eTarget, reg.getName())
        tValue = ctx.getConcreteRegisterValue(reg, callbacks=False)
        if tValue != eValue:
            self.assertEqual(tValue, 0)
            ctx.setConcreteRegisterValue(reg, eValue, callbacks=False)
        self.actual.append(event)

    def reg_write_cb(self, ctx, reg, value):
        if self.log_trace:
            print('(\'REG\', \'W\', \'{}\', {}),'.format(
                reg.getName(),
                hex(value),
            ))
            return
        event = next(self.trace, None)
        self.assertIsNotNone(event)
        (eType, eAction, eTarget, eValue) = event
        self.assertEqual(eType, 'REG')
        self.assertEqual(eAction, 'W')
        self.assertEqual(eTarget, reg.getName())
        self.assertEqual(eValue, value)
        self.actual.append(event)

    def test_execCallbacks(self):
        pc = 0x401000
        while pc in self.function:
            inst = Instruction(pc, self.function[pc])
            self.ctx.processing(inst)
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip, callbacks=False)
        self.assertEqual(self.expect, self.actual)
