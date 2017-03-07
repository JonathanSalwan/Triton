#!/usr/bin/env python2
# coding: utf-8
"""Test callback."""

import unittest

from triton import *


class TestCallback(unittest.TestCase):

    """Testing callbacks."""

    def test_get_concrete_memory_value(self):
        global flag
        setArchitecture(ARCH.X86_64)

        flag = False
        addCallback(self.cb_flag, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
        processing(Instruction("\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00")) # movabs rax, qword ptr [0x1000]
        self.assertTrue(flag)

        flag = False
        removeCallback(self.cb_flag, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
        processing(Instruction("\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00")) # movabs rax, qword ptr [0x1000]
        self.assertFalse(flag)

    def test_get_concrete_register_value(self):
        global flag
        setArchitecture(ARCH.X86_64)

        flag = False
        addCallback(self.cb_flag, CALLBACK.GET_CONCRETE_REGISTER_VALUE)
        processing(Instruction("\x48\x89\xd8")) # mov rax, rbx
        self.assertTrue(flag)

        flag = False
        removeCallback(self.cb_flag, CALLBACK.GET_CONCRETE_REGISTER_VALUE)
        processing(Instruction("\x48\x89\xd8")) # mov rax, rbx
        self.assertFalse(flag)

    @staticmethod
    def cb_flag(x):
        global flag
        flag = True

