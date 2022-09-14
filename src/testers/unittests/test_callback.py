#!/usr/bin/env python3
# coding: utf-8
"""Test callback."""

import unittest

from triton import (TritonContext, ARCH, CALLBACK, Instruction, MemoryAccess)


class TestCallback(unittest.TestCase):

    """Testing callbacks."""

    def test_get_concrete_memory_value(self):
        global flag
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

        flag = False
        self.Triton.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.cb_flag)
        # movabs rax, qword ptr [0x1000]
        self.Triton.processing(Instruction(b"\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00"))
        self.assertTrue(flag)

        flag = False
        self.Triton.removeCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.cb_flag)
        # movabs rax, qword ptr [0x1000]
        self.Triton.processing(Instruction(b"\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00"))
        self.assertFalse(flag)

    def test_get_concrete_register_value(self):
        global flag
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)

        flag = False
        self.Triton.addCallback(CALLBACK.GET_CONCRETE_REGISTER_VALUE, self.cb_flag)
        self.Triton.processing(Instruction(b"\x48\x89\xd8"))  # mov rax, rbx
        self.assertTrue(flag)

        flag = False
        self.Triton.removeCallback(CALLBACK.GET_CONCRETE_REGISTER_VALUE, self.cb_flag)
        self.Triton.processing(Instruction(b"\x48\x89\xd8"))  # mov rax, rbx
        self.assertFalse(flag)

        # Remove all callbacks
        flag = False
        self.Triton.addCallback(CALLBACK.GET_CONCRETE_REGISTER_VALUE, self.cb_flag)
        self.Triton.processing(Instruction(b"\x48\x89\xd8"))  # mov rax, rbx
        self.assertTrue(flag)

        flag = False
        self.Triton.clearCallbacks()
        self.Triton.processing(Instruction(b"\x48\x89\xd8"))  # mov rax, rbx
        self.assertFalse(flag)

    @staticmethod
    def cb_flag(api, x):
        global flag
        flag = True

    def method_callback(self, api, _):
        pass

    def test_method_callback_removal(self):
        # regression test for #809
        import sys
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        cb = self.method_callback.__func__
        cb_initial_refcnt = sys.getrefcount(cb)
        self.Triton.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        self.Triton.removeCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        self.assertTrue(cb_initial_refcnt == sys.getrefcount(cb))

        cb = self.method_callback
        cb_initial_refcnt = tuple(sys.getrefcount(x) for x in (cb, cb.__self__, cb.__func__))
        self.Triton.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        self.Triton.removeCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        cb_new_refcnt = tuple(sys.getrefcount(x) for x in (cb, cb.__self__, cb.__func__))
        self.assertTrue(cb_initial_refcnt == cb_new_refcnt)

        self.Triton.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        self.Triton.getConcreteMemoryAreaValue(0x1000, 1)
        self.Triton.removeCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, self.method_callback)
        cb_new_refcnt = tuple(sys.getrefcount(x) for x in (cb, cb.__self__, cb.__func__))
        self.assertTrue(cb_initial_refcnt == cb_new_refcnt)

    def test_call_rsp_issue(self):
        def test_call(add_callback):
            def get_concrete_memory_value_hook(ctx, mem):
                pass

            ctx = TritonContext(ARCH.X86_64)

            rsp = 0xeffffd80

            ctx.setConcreteMemoryValue(MemoryAccess(rsp + 0x48, 8), 0x41c8e0)
            ctx.setConcreteMemoryValue(MemoryAccess(rsp + 0x50, 8), 0x41c910)

            ctx.setConcreteRegisterValue(ctx.registers.rsp, rsp)

            if add_callback:
                ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, get_concrete_memory_value_hook)

            ctx.processing(Instruction(0x41C690, b"\xff\x54\x24\x50"))  # call qword ptr [rsp + 0x50]

            self.assertTrue(ctx.getConcreteRegisterValue(ctx.registers.rip) == 0x41c910)

        test_call(False)
        test_call(True)
