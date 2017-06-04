#!/usr/bin/env python2
# coding: utf-8
"""Test instance method callback."""

import unittest

from triton import *


class TestCallback(unittest.TestCase):

    """Testing callbacks."""

    def test_get_concrete_memory_value(self):
        setArchitecture(ARCH.X86_64)

        self.flag = False
        addCallback(self.cb_flag, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
        processing(Instruction("\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00")) # movabs rax, qword ptr [0x1000]
        self.assertTrue(self.flag)

        self.flag = False
        removeCallback(self.cb_flag, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
        processing(Instruction("\x48\xa1\x00\x10\x00\x00\x00\x00\x00\x00")) # movabs rax, qword ptr [0x1000]
        self.assertFalse(self.flag)

    def test_get_concrete_register_value(self):
        global flag
        setArchitecture(ARCH.X86_64)

        self.flag = False
        addCallback(self.cb_flag, CALLBACK.GET_CONCRETE_REGISTER_VALUE)
        processing(Instruction("\x48\x89\xd8")) # mov rax, rbx
        self.assertTrue(self.flag)

        self.flag = False
        removeCallback(self.cb_flag, CALLBACK.GET_CONCRETE_REGISTER_VALUE)
        processing(Instruction("\x48\x89\xd8")) # mov rax, rbx
        self.assertFalse(self.flag)

    def cb_flag(self, x):
        self.flag = True

