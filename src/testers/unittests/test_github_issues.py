#!/usr/bin/env python2
# coding: utf-8
"""Issue from Github."""

import unittest

from triton import *



class TestIssue656(unittest.TestCase):

    """Testing #656."""

    @staticmethod
    def sym_exec_gadget(gadget):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        ctx.enableMode(MODE.ALIGNED_MEMORY, True)

        r = ctx.registers
        gprs = (
            r.rax, r.rbx, r.rcx, r.rdx,
            r.rsi, r.rdi, r.esp, r.ebp,
            r.r8, r.r9, r.r10, r.r11,
            r.r12, r.r13, r.r14
        )

        for gpr in gprs:
            ctx.convertRegisterToSymbolicVariable(gpr)

        for assembly in gadget:
            i = Instruction()
            i.setOpcode(assembly)
            ctx.processing(i)

        srax = ctx.getSymbolicRegister(ctx.registers.rax)

        return srax


    def test_issue(self):
        e = self.sym_exec_gadget((b'\x89\xd8', b'\xc2\x04\x00'))
        self.assertEqual(str(e), '(define-fun ref!15 () (_ BitVec 64) ((_ zero_extend 32) ((_ extract 31 0) ref!1))) ; MOV operation')
        a = e.getAst()
        self.assertEqual(str(a + 1), '(bvadd ((_ zero_extend 32) ((_ extract 31 0) ref!1)) (_ bv1 64))')
        self.assertEqual(str(1 + a), '(bvadd (_ bv1 64) ((_ zero_extend 32) ((_ extract 31 0) ref!1)))')



class TestIssue673(unittest.TestCase):

    """Testing #673."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)


    def test_issue1(self):
        inst = Instruction(b"\xc0\xc0\x00") # rol al, 0
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getUndefinedRegisters()), 0)
        self.assertEqual(len(inst.getReadRegisters()), 1)
        self.assertEqual(len(inst.getWrittenRegisters()), 2)


    def test_issue2(self):
        inst = Instruction(b"\xc0\xc0\x01") # rol al, 1
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getUndefinedRegisters()), 0)
        self.assertEqual(len(inst.getReadRegisters()), 2)
        self.assertEqual(len(inst.getWrittenRegisters()), 4)


    def test_issue3(self):
        inst = Instruction(b"\xc0\xc0\x07") # rol al, 7
        self.ctx.processing(inst)
        self.assertEqual(len(inst.getUndefinedRegisters()), 1)
        self.assertEqual(len(inst.getReadRegisters()), 2)
        self.assertEqual(len(inst.getWrittenRegisters()), 4)
