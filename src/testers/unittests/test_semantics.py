#!/usr/bin/env python2
# coding: utf-8
"""Test Semantics."""

import os
import string
import sys
import unittest

from triton import *



class TestIR(unittest.TestCase):
    """Test IR."""

    def emulate(self, pc):
        """
        Emulate every opcodes from pc.
        Process instruction until the end
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


class TestIRQemu(unittest.TestCase):
    """Test IR based on the qemu test suite."""

    def setUp(self):
        self.BASE_PLT  = 0x10000000
        self.BASE_ARGV = 0x20000000
        self.RELO = [
            ['__libc_start_main',  self.__libc_start_main,  None],
            ['printf',             self.__printf,           None],
        ]

    # Simulate the __libc_start_main routine
    def __libc_start_main(self):
        # Get arguments
        main = getConcreteRegisterValue(REG.RDI)

        # Push the return value to jump into the main() function
        concretizeRegister(REG.RSP)
        setConcreteRegisterValue(Register(REG.RSP, getConcreteRegisterValue(REG.RSP)-CPUSIZE.QWORD))

        ret2main = MemoryAccess(getConcreteRegisterValue(REG.RSP), CPUSIZE.QWORD, main)
        concretizeMemory(ret2main)
        setConcreteMemoryValue(ret2main)

        # Setup argc / argv
        concretizeRegister(REG.RDI)
        concretizeRegister(REG.RSI)

        # Setup target argvs
        argvs = list()

        # Define argc / argv
        base  = self.BASE_ARGV
        addrs = list()

        index = 0
        for argv in argvs:
            addrs.append(base)
            setConcreteMemoryAreaValue(base, argv+'\x00')

            # Tainting argvs
            for i in range(len(argv)):
                taintMemory(base + i)

            base += len(argv)+1
            index += 1

        argc = len(argvs)
        argv = base
        for addr in addrs:
            setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD, addr))
            base += CPUSIZE.QWORD

        setConcreteRegisterValue(Register(REG.RDI, argc))
        setConcreteRegisterValue(Register(REG.RSI, argv))

        return 0

    # Simulate the printf() function
    def __printf(self):
        return 0

    def emulate(self, pc):
        """
        Emulate every opcodes from pc.
        Process instruction until the end
        """
        while pc:
            # Fetch opcodes
            opcodes = getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcodes(opcodes)
            instruction.setAddress(pc)

            # Process
            ret = processing(instruction)

            if instruction.getType() == OPCODE.HLT:
                break

            self.assertTrue(ret)

            # Simulate routines
            self.hooking_handler()

            # Next
            pc = getConcreteRegisterValue(REG.RIP)

        return

    def hooking_handler(self):
        pc = getConcreteRegisterValue(REG.RIP)
        for rel in self.RELO:
            if rel[2] == pc:
                # Emulate the routine and the return value
                ret_value = rel[1]()
                concretizeRegister(REG.RAX)
                setConcreteRegisterValue(Register(REG.RAX, ret_value))

                # Get the return address
                ret_addr = getConcreteMemoryValue(MemoryAccess(getConcreteRegisterValue(REG.RSP), CPUSIZE.QWORD))

                # Hijack RIP to skip the call
                concretizeRegister(REG.RIP)
                setConcreteRegisterValue(Register(REG.RIP, ret_addr))

                # Restore RSP (simulate the ret)
                concretizeRegister(REG.RSP)
                setConcreteRegisterValue(Register(REG.RSP, getConcreteRegisterValue(REG.RSP)+CPUSIZE.QWORD))
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
        return binary

    def make_relocation(self, binary):
        # Setup plt
        for pltIndex in range(len(self.RELO)):
            self.RELO[pltIndex][2] = self.BASE_PLT + pltIndex

        # Perform our own relocations
        symbols = binary.getSymbolsTable()
        relocations = binary.getRelocationTable()
        for rel in relocations:
            symbolName = symbols[rel.getSymidx()].getName()
            symbolRelo = rel.getOffset()
            for crel in self.RELO:
                if symbolName == crel[0]:
                    setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD, crel[2]))
                    break
        return

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        # Set arch
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))
        setConcreteRegisterValue(Register(REG.RSP, 0x6fffffff))

        self.emulate(binary.getHeader().getEntry())
        return

