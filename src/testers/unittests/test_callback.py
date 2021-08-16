#!/usr/bin/env python3
# coding: utf-8
"""Test callback."""

import unittest

from triton import (TritonContext, ARCH, CALLBACK, Instruction)


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
