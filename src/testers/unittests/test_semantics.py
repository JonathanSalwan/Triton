#!/usr/bin/env python2
# coding: utf-8
"""Test Semantics."""

import os
import unittest

from triton import (TritonContext, ARCH, Instruction, OPCODE, CPUSIZE,
                    MemoryAccess, MODE)


def checkAstIntegrity(instruction):
    """
    This function check if all ASTs under an Instruction class are still
    available.
    """
    try:
        for se in instruction.getSymbolicExpressions():
            str(se.getAst())

        for x, y in instruction.getLoadAccess():
            str(y)

        for x, y in instruction.getStoreAccess():
            str(y)

        for x, y in instruction.getReadRegisters():
            str(y)

        for x, y in instruction.getWrittenRegisters():
            str(y)

        for x, y in instruction.getReadImmediates():
            str(y)

        return True

    except:
        return False


class TestIR(unittest.TestCase):

    """Test IR."""

    def emulate(self, pc):
        """
        Emulate every opcode from pc.

        Process instruction until the end
        """
        while pc:
            # Fetch opcode
            opcode = self.Triton.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            self.assertTrue(self.Triton.processing(instruction))

            # Next
            pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)

        return

    def load_binary(self, filename):
        """Load in memory every opcode from an elf program."""
        import lief
        binary = lief.parse(filename)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            self.Triton.setConcreteMemoryAreaValue(vaddr, phdr.content)

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

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
        main = self.Triton.getConcreteRegisterValue(self.Triton.registers.rdi)

        # Push the return value to jump into the main() function
        self.Triton.concretizeRegister(self.Triton.registers.rsp)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, self.Triton.getConcreteRegisterValue(self.Triton.registers.rsp)-CPUSIZE.QWORD)

        ret2main = MemoryAccess(self.Triton.getConcreteRegisterValue(self.Triton.registers.rsp), CPUSIZE.QWORD)
        self.Triton.concretizeMemory(ret2main)
        self.Triton.setConcreteMemoryValue(ret2main, main)

        # Setup argc / argv
        self.Triton.concretizeRegister(self.Triton.registers.rdi)
        self.Triton.concretizeRegister(self.Triton.registers.rsi)

        # Setup target argvs
        argvs = list()

        # Define argc / argv
        base  = self.BASE_ARGV
        addrs = list()

        index = 0
        for argv in argvs:
            addrs.append(base)
            self.Triton.setConcreteMemoryAreaValue(base, argv+'\x00')

            # Tainting argvs
            for i in range(len(argv)):
                self.Triton.taintMemory(base + i)

            base += len(argv)+1
            index += 1

        argc = len(argvs)
        argv = base
        for addr in addrs:
            self.Triton.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
            base += CPUSIZE.QWORD

        self.Triton.setConcreteRegisterValue(self.Triton.registers.rdi, argc)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsi, argv)

        return 0

    # Simulate the printf() function
    def __printf(self):
        return 0

    def emulate(self, pc):
        """
        Emulate every opcode from pc.
        Process instruction until the end
        """
        while pc:
            # Fetch opcode
            opcode = self.Triton.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            ret = self.Triton.processing(instruction)

            if instruction.getType() == OPCODE.HLT:
                break

            self.assertTrue(ret)
            self.assertTrue(checkAstIntegrity(instruction))

            # Simulate routines
            self.hooking_handler()

            # Next
            pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)

        return

    def hooking_handler(self):
        pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)
        for rel in self.RELO:
            if rel[2] == pc:
                # Emulate the routine and the return value
                ret_value = rel[1]()
                self.Triton.concretizeRegister(self.Triton.registers.rax)
                self.Triton.setConcreteRegisterValue(self.Triton.registers.rax, ret_value)

                # Get the return address
                ret_addr = self.Triton.getConcreteMemoryValue(MemoryAccess(self.Triton.getConcreteRegisterValue(self.Triton.registers.rsp), CPUSIZE.QWORD))

                # Hijack RIP to skip the call
                self.Triton.concretizeRegister(self.Triton.registers.rip)
                self.Triton.setConcreteRegisterValue(self.Triton.registers.rip, ret_addr)

                # Restore RSP (simulate the ret)
                self.Triton.concretizeRegister(self.Triton.registers.rsp)
                self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, self.Triton.getConcreteRegisterValue(self.Triton.registers.rsp)+CPUSIZE.QWORD)
        return

    def load_binary(self, filename):
        """Load in memory every opcode from an elf program."""
        import lief
        binary = lief.parse(filename)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            self.Triton.setConcreteMemoryAreaValue(vaddr, phdr.content)
        return binary

    def make_relocation(self, binary):
        # Setup plt
        for pltIndex in range(len(self.RELO)):
            self.RELO[pltIndex][2] = self.BASE_PLT + pltIndex

        # Perform our own relocations
        for rel in binary.pltgot_relocations:
            symbolName = rel.symbol.name
            symbolRelo = rel.address
            for crel in self.RELO:
                if symbolName == crel[0]:
                    self.Triton.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                    break
        return

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return

