#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Engine."""

import unittest
import os

from triton import (Instruction, ARCH, CPUSIZE, MemoryAccess, MODE,
                    TritonContext, REG)


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


class DefCamp2015(object):

    """Test for DefCamp2015 challenge."""

    def emulate(self, pc):
        """
        Emulate every opcode from pc.

        * Process instruction until the end and search for constraint
        resolution on cmp eax, 1 then self.Triton.set the new correct value and keep going.
        """
        astCtxt = self.Triton.getAstContext()
        while pc:
            # Fetch opcode
            opcode = self.Triton.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            self.Triton.processing(instruction)
            self.assertTrue(checkAstIntegrity(instruction))

            # 40078B: cmp eax, 1
            # eax must be equal to 1 at each round.
            if instruction.getAddress() == 0x40078B:
                # Slice expressions
                rax = self.Triton.getSymbolicRegister(self.Triton.registers.rax)
                eax = astCtxt.extract(31, 0, rax.getAst())

                # Define constraint
                cstr = astCtxt.land([self.Triton.getPathPredicate(), astCtxt.equal(eax, astCtxt.bv(1, 32))])

                model = self.Triton.getModel(cstr)
                solution = str()
                for k, v in list(model.items()):
                    value = v.getValue()
                    solution += chr(value)
                    self.Triton.setConcreteVariableValue(self.Triton.getSymbolicVariable(k), value)

            # Next
            pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)
        return solution

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

    def test_defcamp_2015(self):
        """Load binary, self.Triton.setup environment and solve challenge with sym eval."""
        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "defcamp-2015-r100.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

        # Define an user input
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rdi, 0x10000000)

        # Symbolize user inputs (30 bytes)
        for index in range(30):
            self.Triton.symbolizeMemory(MemoryAccess(0x10000000+index, CPUSIZE.BYTE))

        # Emulate from the verification function
        solution = self.emulate(0x4006FD)
        self.assertEqual(solution, 'Code_Talkers')


class SeedCoverage(object):

    """Test for seed coverage."""

    def init_ctxt(self):
        """Setup memory and register values."""
        # Define the address of the serial pointer. The address of the serial
        # pointer must be the same that the one hardcoded into the tarself.Triton.geted
        # function. However, the serial pointer (here 0x900000) is arbitrary.
        self.Triton.setConcreteMemoryValue(0x601040, 0x00)
        self.Triton.setConcreteMemoryValue(0x601041, 0x00)
        self.Triton.setConcreteMemoryValue(0x601042, 0x90)

        # Define the serial context. We store the serial content located on our
        # arbitrary # serial pointer (0x900000).
        self.Triton.setConcreteMemoryValue(0x900000, 0x31)
        self.Triton.setConcreteMemoryValue(0x900001, 0x3e)
        self.Triton.setConcreteMemoryValue(0x900002, 0x3d)
        self.Triton.setConcreteMemoryValue(0x900003, 0x26)
        self.Triton.setConcreteMemoryValue(0x900004, 0x31)

        # Point RDI on our buffer. The address of our buffer is arbitrary. We
        # just need to point the RDI register on it as first argument of our
        # tarself.Triton.geted function.
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rdi, 0x1000)

        # Setup stack on an abitrary address.
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x7fffffff)
        self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)

    def symbolize_inputs(self, seed):
        """Add symboles in memory for seed."""
        self.Triton.concretizeAllRegister()
        self.Triton.concretizeAllMemory()
        for address, value in list(seed.items()):
            self.Triton.setConcreteMemoryValue(address, value)
            self.Triton.symbolizeMemory(MemoryAccess(address, CPUSIZE.BYTE))
            self.Triton.symbolizeMemory(MemoryAccess(address+1, CPUSIZE.BYTE))

    def seed_emulate(self, ip):
        """Emulate one run of the function with already self.Triton.setup memory."""
        function = {
            #   <serial> function
            #   push    rbp
            0x40056d: b"\x55",
            #   mov     rbp,rsp
            0x40056e: b"\x48\x89\xe5",
            #   mov     QWORD PTR [rbp-0x18],rdi
            0x400571: b"\x48\x89\x7d\xe8",
            #   mov     DWORD PTR [rbp-0x4],0x0
            0x400575: b"\xc7\x45\xfc\x00\x00\x00\x00",
            #   jmp     4005bd <check+0x50>
            0x40057c: b"\xeb\x3f",
            #   mov     eax,DWORD PTR [rbp-0x4]
            0x40057e: b"\x8b\x45\xfc",
            #   movsxd  rdx,eax
            0x400581: b"\x48\x63\xd0",
            #   mov     rax,QWORD PTR [rbp-0x18]
            0x400584: b"\x48\x8b\x45\xe8",
            #   add     rax,rdx
            0x400588: b"\x48\x01\xd0",
            #   movzx   eax,BYTE PTR [rax]
            0x40058b: b"\x0f\xb6\x00",
            #   movsx   eax,al
            0x40058e: b"\x0f\xbe\xc0",
            #   sub     eax,0x1
            0x400591: b"\x83\xe8\x01",
            #   xor     eax,0x55
            0x400594: b"\x83\xf0\x55",
            #   mov     ecx,eax
            0x400597: b"\x89\xc1",
            #   mov     rdx,QWORD PTR [rip+0x200aa0]        # 601040 <serial>
            0x400599: b"\x48\x8b\x15\xa0\x0a\x20\x00",
            #   mov     eax,DWORD PTR [rbp-0x4]
            0x4005a0: b"\x8b\x45\xfc",
            #   cdqe
            0x4005a3: b"\x48\x98",
            #   add     rax,rdx
            0x4005a5: b"\x48\x01\xd0",
            #   movzx   eax,BYTE PTR [rax]
            0x4005a8: b"\x0f\xb6\x00",
            #   movsx   eax,al
            0x4005ab: b"\x0f\xbe\xc0",
            #   cmp     ecx,eax
            0x4005ae: b"\x39\xc1",
            #   je      4005b9 <check+0x4c>
            0x4005b0: b"\x74\x07",
            #   mov     eax,0x1
            0x4005b2: b"\xb8\x01\x00\x00\x00",
            #   jmp     4005c8 <check+0x5b>
            0x4005b7: b"\xeb\x0f",
            #   add     DWORD PTR [rbp-0x4],0x1
            0x4005b9: b"\x83\x45\xfc\x01",
            #   cmp     DWORD PTR [rbp-0x4],0x4
            0x4005bd: b"\x83\x7d\xfc\x04",
            #   jle     40057e <check+0x11>
            0x4005c1: b"\x7e\xbb",
            #   mov     eax,0x0
            0x4005c3: b"\xb8\x00\x00\x00\x00",
            #   pop     rbp
            0x4005c8: b"\x5d",
            #   ret
            0x4005c9: b"\xc3",
        }
        while ip in function:
            # Build an instruction
            inst = Instruction()

            # Setup opcode
            inst.setOpcode(function[ip])

            # Setup Address
            inst.setAddress(ip)

            # Process everything
            self.Triton.processing(inst)
            self.assertTrue(checkAstIntegrity(inst))

            # Next instruction
            ip = self.Triton.getRegisterAst(self.Triton.registers.rip).evaluate()

    def new_inputs(self):
        """Look for another branching using current constraints found."""
        astCtxt = self.Triton.getAstContext()

        # Set of new inputs
        inputs = list()

        # Get path constraints from the last execution
        pco = self.Triton.getPathConstraints()

        # We start with any input. T (Top)
        previousConstraints = astCtxt.equal(astCtxt.bvtrue(), astCtxt.bvtrue())

        # Go through the path constraints
        for pc in pco:
            # If there is a condition
            if pc.isMultipleBranches():
                # Get all branches
                branches = pc.getBranchConstraints()
                for branch in branches:
                    # Get the constraint of the branch which has been not taken
                    if branch['isTaken'] == False:
                        # Ask for a model
                        models = self.Triton.getModel(astCtxt.land([previousConstraints, branch['constraint']]))
                        seed = dict()
                        for k, v in list(models.items()):
                            # Get the symbolic variable assigned to the model
                            symVar = self.Triton.getSymbolicVariable(k)
                            # Save the new input as seed.
                            seed.update({symVar.getOrigin(): v.getValue()})
                        if seed:
                            inputs.append(seed)

            # Update the previous constraints with true branch to keep a good
            # path.
            previousConstraints = astCtxt.land([previousConstraints, pc.getTakenPredicate()])

        # Clear the path constraints to be clean at the next execution.
        self.Triton.clearPathConstraints()

        return inputs

    def test_seed_coverage(self):
        """Found every seed so that every opcode will be use at least once."""
        # Define entry point
        ENTRY = 0x40056d

        # We start the execution with a random value located at 0x1000.
        lastInput = list()
        worklist = list([{0x1000: 1}])

        while worklist:
            # Take the first seed
            seed = worklist[0]

            # Symbolize inputs
            self.symbolize_inputs(seed)

            # Init context memory
            self.init_ctxt()

            # Emulate
            self.seed_emulate(ENTRY)

            lastInput += [dict(seed)]
            del worklist[0]

            newInputs = self.new_inputs()
            for inputs in newInputs:
                if inputs not in lastInput and inputs not in worklist:
                    worklist += [dict(inputs)]

        self.assertIn({4096: 101,
                       4097: 108,
                       4098: 105,
                       4099: 116,
                       4100: 101}, lastInput)


class Emu1(object):

    """Test for emu_1.dump."""

    def test_emulate(self, concretize=False):
        """Run a dumped simulation and check output registers."""
        # Get dumped data
        dump = os.path.join(os.path.dirname(__file__), "misc", "emu_1.dump")
        with open(dump) as f:
            regs, mems = eval(f.read())

        # Load memory
        for mem in mems:
            start = mem['start']
            if mem['memory'] is not None:
                self.Triton.setConcreteMemoryAreaValue(start, bytearray(mem['memory']))

        # self.Triton.setup registers
        for reg_name in ("rax", "rbx", "rcx", "rdx", "rdi", "rsi", "rbp",
                         "rsp", "rip", "r8", "r9", "r10", "r11", "r12", "r13",
                         "r14", "eflags", "xmm0", "xmm1", "xmm2", "xmm3",
                         "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9",
                         "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15"):
            self.Triton.setConcreteRegisterValue(self.Triton.getRegister(getattr(REG.X86_64, reg_name.upper())), regs[reg_name])

        # run the code
        pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)
        while pc != 0x409A18:
            opcode = self.Triton.getConcreteMemoryAreaValue(pc, 20)

            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Check if triton doesn't supports this instruction
            self.assertTrue(self.Triton.processing(instruction))
            self.assertTrue(checkAstIntegrity(instruction))

            pc = self.Triton.getConcreteRegisterValue(self.Triton.registers.rip)

            if concretize:
                self.Triton.concretizeAllMemory()
                self.Triton.concretizeAllRegister()

        rax = self.Triton.getConcreteRegisterValue(self.Triton.registers.rax)
        rbx = self.Triton.getConcreteRegisterValue(self.Triton.registers.rbx)
        rcx = self.Triton.getConcreteRegisterValue(self.Triton.registers.rcx)
        rdx = self.Triton.getConcreteRegisterValue(self.Triton.registers.rdx)
        rsi = self.Triton.getConcreteRegisterValue(self.Triton.registers.rsi)

        self.assertEqual(rax, 0)
        self.assertEqual(rbx, 0)
        self.assertEqual(rcx, 0)
        self.assertEqual(rdx, 0x4d2)
        self.assertEqual(rsi, 0x3669000000000000)


class BaseTestSimulation(DefCamp2015, SeedCoverage, Emu1):

    """BaseClass to test the simulation."""


class TestSymbolicEngineNoOptim(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine without optimization."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        super(TestSymbolicEngineNoOptim, self).setUp()


class TestSymbolicEngineGC(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with iterative GC."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ITERATIVE_GC, True)
        super(TestSymbolicEngineGC, self).setUp()


class TestSymbolicEngineAligned(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ALIGNED_MEMORY, True)
        super(TestSymbolicEngineAligned, self).setUp()


class TestSymbolicEngineAlignedAndTaintPtr(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ALIGNED_MEMORY, True)
        self.Triton.setMode(MODE.TAINT_THROUGH_POINTERS, True)
        super(TestSymbolicEngineAlignedAndTaintPtr, self).setUp()


class TestSymbolicEngineOnlySymbolized(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ONLY_ON_SYMBOLIZED."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        super(TestSymbolicEngineOnlySymbolized, self).setUp()


class TestSymbolicEngineAlignedOnlySymbolized(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY and ONLY_ON_SYMBOLIZED."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ALIGNED_MEMORY, True)
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        super(TestSymbolicEngineAlignedOnlySymbolized, self).setUp()


class TestSymbolicEngineDisable(BaseTestSimulation, unittest.TestCase):

    """Testing the emulation with the symbolic engine disabled."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.enableSymbolicEngine(False)
        super(TestSymbolicEngineDisable, self).setUp()

    @unittest.skip("Not possible")
    def test_seed_coverage(self):
        pass

    @unittest.skip("Not possible")
    def test_defcamp_2015(self):
        pass


class TestSymbolicEngineSymOpti(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine without optimization."""

    def setUp(self):
        """Define the arch."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.AST_OPTIMIZATIONS, True)
        super(TestSymbolicEngineSymOpti, self).setUp()


class TestSymbolicEngineAlignedSymOpti(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ALIGNED_MEMORY, True)
        self.Triton.setMode(MODE.AST_OPTIMIZATIONS, True)
        super(TestSymbolicEngineAlignedSymOpti, self).setUp()


class TestSymbolicEngineAlignedOnlySymbolizedSymOpti(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY, ONLY_ON_SYMBOLIZED and AST_OPTIMIZATIONS."""

    def setUp(self):
        """Define the arch and modes."""
        self.Triton = TritonContext()
        self.Triton.setArchitecture(ARCH.X86_64)
        self.Triton.setMode(MODE.ALIGNED_MEMORY, True)
        self.Triton.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
        self.Triton.setMode(MODE.AST_OPTIMIZATIONS, True)
        super(TestSymbolicEngineAlignedOnlySymbolizedSymOpti, self).setUp()
