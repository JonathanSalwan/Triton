#!/usr/bin/env python
# coding: utf-8
"""Test Optimizations."""

import os
import unittest

from triton import *



class TestOptimizations(unittest.TestCase):
    """Test optimizations on the qemu test suite."""

    def setUp(self):
        self.ctx1 = TritonContext(ARCH.X86_64)
        self.ctx2 = TritonContext(ARCH.X86_64)

        self.ctx1.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx2.setMode(MODE.AST_OPTIMIZATIONS, True)

        self.BASE_PLT  = 0x10000000
        self.BASE_ARGV = 0x20000000
        self.RELO = [
            ['__libc_start_main', self.__libc_start_main,  None],
            ['printf',            self.__printf,           None],
        ]

    # Simulate the __libc_start_main routine
    def __libc_start_main(self):
        # Get arguments
        main1 = self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rdi)
        main2 = self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rdi)

        # Push the return value to jump into the main() function
        self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rsp, self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rsp)-CPUSIZE.QWORD)
        self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rsp, self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rsp)-CPUSIZE.QWORD)

        ret2main1 = MemoryAccess(self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rsp), CPUSIZE.QWORD)
        self.ctx1.setConcreteMemoryValue(ret2main1, main1)

        ret2main2 = MemoryAccess(self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rsp), CPUSIZE.QWORD)
        self.ctx2.setConcreteMemoryValue(ret2main2, main2)

        # Setup target argvs
        argvs = list()

        # Define argc / argv
        base  = self.BASE_ARGV
        addrs = list()

        index = 0
        for argv in argvs:
            addrs.append(base)
            self.ctx1.setConcreteMemoryAreaValue(base, argv+'\x00')
            self.ctx2.setConcreteMemoryAreaValue(base, argv+'\x00')

            # Tainting argvs
            for i in range(len(argv)):
                self.ctx1.taintMemory(base + i)
                self.ctx2.taintMemory(base + i)

            base += len(argv)+1
            index += 1

        argc = len(argvs)
        argv = base
        for addr in addrs:
            self.ctx1.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
            self.ctx2.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
            base += CPUSIZE.QWORD

        self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rdi, argc)
        self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rsi, argv)

        self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rdi, argc)
        self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rsi, argv)

        return 0

    # Simulate the printf() function
    def __printf(self):
        return 0

    def check_ast(self, instruction1, instruction2):
        for i in range(len(instruction1.getSymbolicExpressions())):
            exprs1 = instruction1.getSymbolicExpressions()
            exprs2 = instruction2.getSymbolicExpressions()
            self.assertEqual(exprs1[i].getAst().evaluate(), exprs2[i].getAst().evaluate())
        return

    def emulate(self, pc1):
        """
        Emulate every opcode from pc.
        Process instruction until the end
        """
        pc2 = pc1
        while pc1:
            # Fetch opcode
            opcode1 = self.ctx1.getConcreteMemoryAreaValue(pc1, 16)
            opcode2 = self.ctx2.getConcreteMemoryAreaValue(pc2, 16)

            # Create the Triton instruction
            instruction1 = Instruction(pc1, opcode1)
            instruction2 = Instruction(pc2, opcode2)

            # Process
            self.ctx1.processing(instruction1)
            self.ctx2.processing(instruction2)

            if instruction1.getType() == OPCODE.X86.HLT:
                break

            self.check_ast(instruction1, instruction2)

            # Simulate routines
            self.hooking_handler()

            # Next
            pc1 = self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rip)
            pc2 = self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rip)
            self.assertEqual(pc1, pc2)

        return

    def hooking_handler(self):
        pc = self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rip)
        for rel in self.RELO:
            if rel[2] == pc:
                # Emulate the routine and the return value
                ret_value = rel[1]()
                self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rax, ret_value)
                self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rax, ret_value)

                # Get the return address
                ret_addr1 = self.ctx1.getConcreteMemoryValue(MemoryAccess(self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rsp), CPUSIZE.QWORD))
                ret_addr2 = self.ctx2.getConcreteMemoryValue(MemoryAccess(self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rsp), CPUSIZE.QWORD))

                # Hijack RIP to skip the call
                self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rip, ret_addr1)
                self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rip, ret_addr2)

                # Restore RSP (simulate the ret)
                self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rsp, self.ctx1.getConcreteRegisterValue(self.ctx1.registers.rsp)+CPUSIZE.QWORD)
                self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rsp, self.ctx2.getConcreteRegisterValue(self.ctx2.registers.rsp)+CPUSIZE.QWORD)
        return

    def load_binary(self, filename):
        """Load in memory every opcode from an elf program."""
        import lief
        binary = lief.parse(filename)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            self.ctx1.setConcreteMemoryAreaValue(vaddr, phdr.content)
            self.ctx2.setConcreteMemoryAreaValue(vaddr, phdr.content)
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
                    self.ctx1.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                    self.ctx2.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                    break
        return

    def test(self):
        """Load binary, setup environment and emulate the ir test suite."""
        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu-light.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rbp, 0x7fffffff)
        self.ctx1.setConcreteRegisterValue(self.ctx1.registers.rsp, 0x6fffffff)

        self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rbp, 0x7fffffff)
        self.ctx2.setConcreteRegisterValue(self.ctx2.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return
