#!/usr/bin/env python2
# coding: utf-8
"""Test Semantics."""

import os
import unittest

from triton import *



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
        #lief.Logger.disable()
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

    def test_ir_with_opti1(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        self.emulate(0x40065c)
        return

    def test_ir_with_opti2(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.Triton.setMode(MODE.AST_OPTIMIZATIONS, True)

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

            if instruction.getType() == OPCODE.X86.HLT:
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
        #lief.Logger.disable()
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
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return

    def test_ir_with_opti1(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return

    def test_ir_with_opti2(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.Triton = TritonContext()
        # Set arch
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.Triton.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.Triton.setMode(MODE.AST_OPTIMIZATIONS, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return


class TestCustomIR(unittest.TestCase):
    """Test custom IR"""

    def test_push_esp(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        esp = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        code = [
            (0xdeadbeaf, b"\x54"),  # push esp
            (0xdeadbeb0, b"\xc3"),  # ret
        ]
        for addr, opcode in code:
            insn = Instruction()
            insn.setOpcode(opcode)
            insn.setAddress(addr)
            ctx.processing(insn)
        eip = ctx.getRegisterAst(ctx.getRegister(REG.X86.EIP))
        self.assertTrue(ctx.isSat(eip == esp))

    def test_popal(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        esp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        insn = Instruction()
        insn.setOpcode(b"\x61")  # popal
        ctx.processing(insn)
        esp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        self.assertTrue(ctx.isSat(esp_new == esp_old + 32))

    def test_popf_x86(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86)
        esp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        insn = Instruction()
        insn.setOpcode(b"\x66\x9d")  # popf
        ctx.processing(insn)
        esp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86.ESP))
        self.assertTrue(ctx.isSat(esp_new == esp_old + 4))

    def test_popf_x86_64(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        rsp_old = ctx.getRegisterAst(ctx.getRegister(REG.X86_64.RSP))
        insn = Instruction()
        insn.setOpcode(b"\x66\x9d")  # popf
        ctx.processing(insn)
        rsp_new = ctx.getRegisterAst(ctx.getRegister(REG.X86_64.RSP))
        self.assertTrue(ctx.isSat(rsp_new == rsp_old + 8))

    def test_ldr1_aarch64(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.AARCH64)

        inst = Instruction(b"\x27\x44\x40\xf8") # ldr x7, [x1], #4
        ctx.processing(inst)

        found = False
        for r, _ in inst.getReadRegisters():
            if r.getName() == 'x1':
                found = True
        self.assertTrue(found)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'x1':
                found = True
        self.assertTrue(found)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'x7':
                found = True
        self.assertTrue(found)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'pc':
                found = True
        self.assertTrue(found)

        found = False
        for m, _ in inst.getLoadAccess():
            if m.getBaseRegister().getName() == 'x1':
                found = True
        self.assertTrue(found)

    def test_ldr2_aarch64(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.AARCH64)

        inst = Instruction(b"\x27\x00\x40\xf9") # ldr x7, [x1]
        ctx.processing(inst)

        found = False
        for r, _ in inst.getReadRegisters():
            if r.getName() == 'x1':
                found = True
        self.assertTrue(found)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'x1':
                found = True
        self.assertTrue(found == False)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'x7':
                found = True
        self.assertTrue(found)

        found = False
        for r, _ in inst.getWrittenRegisters():
            if r.getName() == 'pc':
                found = True
        self.assertTrue(found)

        found = False
        for m, _ in inst.getLoadAccess():
            if m.getBaseRegister().getName() == 'x1':
                found = True
        self.assertTrue(found)
