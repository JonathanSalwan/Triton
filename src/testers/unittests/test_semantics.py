#!/usr/bin/env python2
# coding: utf-8
"""Test Semantics."""

import unittest
import os

from triton import (getConcreteMemoryAreaValue, getConcreteRegisterValue,
                    Instruction, setArchitecture, ARCH, processing, REG,
                    setConcreteMemoryAreaValue, Register, Elf,
                    setConcreteRegisterValue)


class TestIR(unittest.TestCase):
    """Test IR."""

    def emulate(self, pc):
        """
        Emulate every opcodes from pc.

        * Process instruction until the end and search for constraint
        resolution on cmp eax, 1 then set the new correct value and keep going.
        """
        while pc:
            # Fetch opcodes
            opcodes = getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcodes(opcodes)
            instruction.setAddress(pc)

            # Process
            self.assertTrue(processing(instruction))

            # Next
            pc = getConcreteRegisterValue(REG.RIP)

        return

    def load_binary(self, filename):
        """Load in memory every opcode from an elf program."""
        binary = Elf(filename)
        raw = binary.getRaw()
        phdrs = binary.getProgramHeaders()
        for phdr in phdrs:
            offset = phdr.getOffset()
            size = phdr.getFilesz()
            vaddr = phdr.getVaddr()
            setConcreteMemoryAreaValue(vaddr, raw[offset:offset+size])

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        # Set arch
        setArchitecture(ARCH.X86_64)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))
        setConcreteRegisterValue(Register(REG.RSP, 0x6fffffff))

        self.emulate(0x40065c)
        return

