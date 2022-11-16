#!/usr/bin/env python3
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
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            self.assertTrue(self.ctx.processing(instruction) == EXCEPTION.NO_FAULT)

            # Next
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)

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
            self.ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

        self.emulate(0x40065c)
        return

    def test_ir_with_opti1(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

        self.emulate(0x40065c)
        return

    def test_ir_with_opti2(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "ir-test-suite.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

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
        main = self.ctx.getConcreteRegisterValue(self.ctx.registers.rdi)

        # Push the return value to jump into the main() function
        self.ctx.concretizeRegister(self.ctx.registers.rsp)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp)-CPUSIZE.QWORD)

        ret2main = MemoryAccess(self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp), CPUSIZE.QWORD)
        self.ctx.concretizeMemory(ret2main)
        self.ctx.setConcreteMemoryValue(ret2main, main)

        # Setup argc / argv
        self.ctx.concretizeRegister(self.ctx.registers.rdi)
        self.ctx.concretizeRegister(self.ctx.registers.rsi)

        # Setup target argvs
        argvs = list()

        # Define argc / argv
        base  = self.BASE_ARGV
        addrs = list()

        index = 0
        for argv in argvs:
            addrs.append(base)
            self.ctx.setConcreteMemoryAreaValue(base, argv+'\x00')

            # Tainting argvs
            for i in range(len(argv)):
                self.ctx.taintMemory(base + i)

            base += len(argv)+1
            index += 1

        argc = len(argvs)
        argv = base
        for addr in addrs:
            self.ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
            base += CPUSIZE.QWORD

        self.ctx.setConcreteRegisterValue(self.ctx.registers.rdi, argc)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsi, argv)

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
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            ret = self.ctx.processing(instruction)

            if instruction.getType() == OPCODE.X86.HLT:
                break

            self.assertTrue(ret == EXCEPTION.NO_FAULT)
            self.assertTrue(checkAstIntegrity(instruction))

            # Simulate routines
            self.hooking_handler()

            # Next
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)

        return

    def hooking_handler(self):
        pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
        for rel in self.RELO:
            if rel[2] == pc:
                # Emulate the routine and the return value
                ret_value = rel[1]()
                self.ctx.concretizeRegister(self.ctx.registers.rax)
                self.ctx.setConcreteRegisterValue(self.ctx.registers.rax, ret_value)

                # Get the return address
                ret_addr = self.ctx.getConcreteMemoryValue(MemoryAccess(self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp), CPUSIZE.QWORD))

                # Hijack RIP to skip the call
                self.ctx.concretizeRegister(self.ctx.registers.rip)
                self.ctx.setConcreteRegisterValue(self.ctx.registers.rip, ret_addr)

                # Restore RSP (simulate the ret)
                self.ctx.concretizeRegister(self.ctx.registers.rsp)
                self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp)+CPUSIZE.QWORD)
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
            self.ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content))
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
                    self.ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                    break
        return

    def test_ir(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return

    def test_ir_with_opti1(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

        self.emulate(binary.entrypoint)
        return

    def test_ir_with_opti2(self):
        """Load binary, setup environment and emulate the ir test suite."""
        self.ctx = TritonContext()
        self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.ctx.setMode(MODE.SYMBOLIZE_INDEX_ROTATION, True)
        self.ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "qemu", "ir-test-suite-qemu.bin")
        binary = self.load_binary(binary_file)

        self.make_relocation(binary)

        # Define a fake stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, 0x7fffffff)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, 0x6fffffff)

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

    def test_blr1_aarch64(self):
        ctx = TritonContext(ARCH.AARCH64)
        ctx.setConcreteRegisterValue(ctx.registers.pc, 0x1000)
        ctx.setConcreteRegisterValue(ctx.registers.x1, 0xaaaa)
        ctx.processing(Instruction(b"\x20\x00\x3f\xd6")) # blr x1p
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.pc), 0xaaaa)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.x30), 0x1004)

    def test_brk1_aarch64(self):
        ctx = TritonContext(ARCH.AARCH64)
        ret = ctx.processing(Instruction(b"\x20\x00\x20\xd4")) # brk 1
        self.assertEqual(ret, EXCEPTION.FAULT_BP)

    def test_movn_aarch64(self):
        ctx = TritonContext(ARCH.AARCH64)
        ctx.processing(Instruction(b"\x41\x01\x80\x92")) # movn x1, #10
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.x1), 0xfffffffffffffff5)

    def test_movz_aarch64(self):
        ctx = TritonContext(ARCH.AARCH64)
        ctx.processing(Instruction(b"\x41\x01\x80\xd2")) # movz x1, #10
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.x1), 0xa)

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

    def test_fpu_x86(self):
        ctx = TritonContext()
        ctx.setArchitecture(ARCH.X86_64)
        code1 = [
            (b"\x48\xB8\x11\x11\x11\x11\x11\x11\x11\x11",   "mov rax, 0x1111111111111111"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x04\x24",                           "movq mm0, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x22\x22\x22\x22\x22\x22\x22\x22",   "mov rax, 0x2222222222222222"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x0C\x24",                           "movq mm1, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x33\x33\x33\x33\x33\x33\x33\x33",   "mov rax, 0x3333333333333333"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x14\x24",                           "movq mm2, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x44\x44\x44\x44\x44\x44\x44\x44",   "mov rax, 0x4444444444444444"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x1C\x24",                           "movq mm3, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x55\x55\x55\x55\x55\x55\x55\x55",   "mov rax, 0x5555555555555555"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x24\x24",                           "movq mm4, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x66\x66\x66\x66\x66\x66\x66\x66",   "mov rax, 0x6666666666666666"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x2C\x24",                           "movq mm5, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x77\x77\x77\x77\x77\x77\x77\x77",   "mov rax, 0x7777777777777777"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x34\x24",                           "movq mm6, qword ptr ss:[rsp]"),
            (b"\x48\xB8\x88\x88\x88\x88\x88\x88\x88\x88",   "mov rax, 0x8888888888888888"),
            (b"\x48\x89\x04\x24",                           "mov qword ptr ss:[rsp], rax"),
            (b"\x0F\x6F\x3C\x24",                           "movq mm7, qword ptr ss:[rsp]"),
        ]

        for op, asm in code1:
            ctx.processing(Instruction(op))

        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm0), 0x1111111111111111)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm1), 0x2222222222222222)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm2), 0x3333333333333333)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm3), 0x4444444444444444)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm4), 0x5555555555555555)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm5), 0x6666666666666666)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm6), 0x7777777777777777)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.mm7), 0x8888888888888888)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st0), 0x1111111111111111)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st1), 0x2222222222222222)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st2), 0x3333333333333333)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st3), 0x4444444444444444)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st4), 0x5555555555555555)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st5), 0x6666666666666666)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st6), 0x7777777777777777)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st7), 0x8888888888888888)

        # Save and trash registers
        ctx.processing(Instruction(b"\x0F\xAE\x04\x24")) # fxsave ss:[rsp]
        ctx.setConcreteRegisterValue(ctx.registers.st0, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st1, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st2, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st3, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st4, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st5, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st6, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st7, 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st0), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st1), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st2), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st3), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st4), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st5), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st6), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st7), 0)

        # Restor and check registers
        ctx.processing(Instruction(b"\x0F\xAE\x0C\x24")) # fxrstor ss:[rsp]
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st0), 0x1111111111111111)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st1), 0x2222222222222222)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st2), 0x3333333333333333)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st3), 0x4444444444444444)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st4), 0x5555555555555555)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st5), 0x6666666666666666)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st6), 0x7777777777777777)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st7), 0x8888888888888888)

        # Save and trash registers
        ctx.processing(Instruction(b"\x48\x0f\xae\x04\x24")) # fxsave64 ss:[rsp]
        ctx.setConcreteRegisterValue(ctx.registers.st0, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st1, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st2, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st3, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st4, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st5, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st6, 0)
        ctx.setConcreteRegisterValue(ctx.registers.st7, 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st0), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st1), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st2), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st3), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st4), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st5), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st6), 0)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st7), 0)

        # Restor and check registers
        ctx.processing(Instruction(b"\x48\x0f\xae\x0c\x24")) # fxrstor64 ss:[rsp]
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st0), 0x1111111111111111)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st1), 0x2222222222222222)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st2), 0x3333333333333333)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st3), 0x4444444444444444)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st4), 0x5555555555555555)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st5), 0x6666666666666666)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st6), 0x7777777777777777)
        self.assertEqual(ctx.getConcreteRegisterValue(ctx.registers.st7), 0x8888888888888888)
