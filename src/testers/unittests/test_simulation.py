#!/usr/bin/env python2
# coding: utf-8
"""Test Symbolic Engine."""

import unittest
import os

from triton import (ast, getConcreteMemoryAreaValue, getConcreteRegisterValue,
                    Instruction, getSymbolicExpressionFromId, setArchitecture,
                    getSymbolicRegisterId, getSymbolicVariableFromId, ARCH,
                    processing, REG, getPathConstraintsAst, getPathConstraints,
                    CPUSIZE, setConcreteMemoryAreaValue, concretizeAllRegister,
                    convertMemoryToSymbolicVariable, MemoryAccess, Register,
                    setConcreteRegisterValue, setConcreteMemoryValue, getModel,
                    Elf, concretizeAllMemory, buildSymbolicRegister, MODE,
                    clearPathConstraints, enableMode, enableSymbolicEngine)


class DefCamp2015(object):

    """Test for DefCamp2015 challenge."""

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
            processing(instruction)

            # 40078B: cmp eax, 1
            # eax must be equal to 1 at each round.
            if instruction.getAddress() == 0x40078B:
                # Slice expressions
                rax = getSymbolicExpressionFromId(getSymbolicRegisterId(REG.RAX))
                eax = ast.extract(31, 0, rax.getAst())

                # Define constraint
                cstr = ast.assert_(ast.land(getPathConstraintsAst(), ast.equal(eax, ast.bv(1, 32))))

                model = getModel(cstr)
                solution = str()
                for k, v in model.items():
                    value = v.getValue()
                    solution += chr(value)
                    getSymbolicVariableFromId(k).setConcreteValue(value)

            # Next
            pc = getConcreteRegisterValue(REG.RIP)
        return solution

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

    def test_defcamp_2015(self):
        """Load binary, setup environment and solve challenge with sym eval."""
        # Load the binary
        binary_file = os.path.join(os.path.dirname(__file__), "misc", "defcamp-2015-r100.bin")
        self.load_binary(binary_file)

        # Define a fake stack
        setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))
        setConcreteRegisterValue(Register(REG.RSP, 0x6fffffff))

        # Define an user input
        setConcreteRegisterValue(Register(REG.RDI, 0x10000000))

        # Symbolize user inputs (30 bytes)
        for index in range(30):
            convertMemoryToSymbolicVariable(MemoryAccess(0x10000000+index, CPUSIZE.BYTE))

        # Emulate from the verification function
        solution = self.emulate(0x4006FD)
        self.assertEqual(solution, 'Code_Talkers')


class SeedCoverage(object):

    """Test for seed coverage."""

    def init_ctxt(self):
        """Setup memory and register values."""
        # Define the address of the serial pointer. The address of the serial
        # pointer must be the same that the one hardcoded into the targeted
        # function. However, the serial pointer (here 0x900000) is arbitrary.
        setConcreteMemoryValue(0x601040, 0x00)
        setConcreteMemoryValue(0x601041, 0x00)
        setConcreteMemoryValue(0x601042, 0x90)

        # Define the serial context. We store the serial content located on our
        # arbitrary # serial pointer (0x900000).
        setConcreteMemoryValue(0x900000, 0x31)
        setConcreteMemoryValue(0x900001, 0x3e)
        setConcreteMemoryValue(0x900002, 0x3d)
        setConcreteMemoryValue(0x900003, 0x26)
        setConcreteMemoryValue(0x900004, 0x31)

        # Point RDI on our buffer. The address of our buffer is arbitrary. We
        # just need to point the RDI register on it as first argument of our
        # targeted function.
        setConcreteRegisterValue(Register(REG.RDI, 0x1000))

        # Setup stack on an abitrary address.
        setConcreteRegisterValue(Register(REG.RSP, 0x7fffffff))
        setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))

    def symbolize_inputs(self, seed):
        """Add symboles in memory for seed."""
        concretizeAllRegister()
        concretizeAllMemory()
        for address, value in seed.items():
            convertMemoryToSymbolicVariable(MemoryAccess(address, CPUSIZE.BYTE, value))
            convertMemoryToSymbolicVariable(MemoryAccess(address+1, CPUSIZE.BYTE))

    def seed_emulate(self, ip):
        """Emulate one run of the function with already setup memory."""
        function = {
            #   <serial> function
            #   push    rbp
            0x40056d: "\x55",
            #   mov     rbp,rsp
            0x40056e: "\x48\x89\xe5",
            #   mov     QWORD PTR [rbp-0x18],rdi
            0x400571: "\x48\x89\x7d\xe8",
            #   mov     DWORD PTR [rbp-0x4],0x0
            0x400575: "\xc7\x45\xfc\x00\x00\x00\x00",
            #   jmp     4005bd <check+0x50>
            0x40057c: "\xeb\x3f",
            #   mov     eax,DWORD PTR [rbp-0x4]
            0x40057e: "\x8b\x45\xfc",
            #   movsxd  rdx,eax
            0x400581: "\x48\x63\xd0",
            #   mov     rax,QWORD PTR [rbp-0x18]
            0x400584: "\x48\x8b\x45\xe8",
            #   add     rax,rdx
            0x400588: "\x48\x01\xd0",
            #   movzx   eax,BYTE PTR [rax]
            0x40058b: "\x0f\xb6\x00",
            #   movsx   eax,al
            0x40058e: "\x0f\xbe\xc0",
            #   sub     eax,0x1
            0x400591: "\x83\xe8\x01",
            #   xor     eax,0x55
            0x400594: "\x83\xf0\x55",
            #   mov     ecx,eax
            0x400597: "\x89\xc1",
            #   mov     rdx,QWORD PTR [rip+0x200aa0]        # 601040 <serial>
            0x400599: "\x48\x8b\x15\xa0\x0a\x20\x00",
            #   mov     eax,DWORD PTR [rbp-0x4]
            0x4005a0: "\x8b\x45\xfc",
            #   cdqe
            0x4005a3: "\x48\x98",
            #   add     rax,rdx
            0x4005a5: "\x48\x01\xd0",
            #   movzx   eax,BYTE PTR [rax]
            0x4005a8: "\x0f\xb6\x00",
            #   movsx   eax,al
            0x4005ab: "\x0f\xbe\xc0",
            #   cmp     ecx,eax
            0x4005ae: "\x39\xc1",
            #   je      4005b9 <check+0x4c>
            0x4005b0: "\x74\x07",
            #   mov     eax,0x1
            0x4005b2: "\xb8\x01\x00\x00\x00",
            #   jmp     4005c8 <check+0x5b>
            0x4005b7: "\xeb\x0f",
            #   add     DWORD PTR [rbp-0x4],0x1
            0x4005b9: "\x83\x45\xfc\x01",
            #   cmp     DWORD PTR [rbp-0x4],0x4
            0x4005bd: "\x83\x7d\xfc\x04",
            #   jle     40057e <check+0x11>
            0x4005c1: "\x7e\xbb",
            #   mov     eax,0x0
            0x4005c3: "\xb8\x00\x00\x00\x00",
            #   pop     rbp
            0x4005c8: "\x5d",
            #   ret
            0x4005c9: "\xc3",
        }
        while ip in function:
            # Build an instruction
            inst = Instruction()

            # Setup opcodes
            inst.setOpcodes(function[ip])

            # Setup Address
            inst.setAddress(ip)

            # Process everything
            processing(inst)

            # Next instruction
            ip = buildSymbolicRegister(REG.RIP).evaluate()

    def new_inputs(self):
        """Look for another branching using current constraints found."""
        # Set of new inputs
        inputs = list()

        # Get path constraints from the last execution
        pco = getPathConstraints()

        # We start with any input. T (Top)
        previousConstraints = ast.equal(ast.bvtrue(), ast.bvtrue())

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
                        models = getModel(ast.assert_(ast.land(previousConstraints, branch['constraint'])))
                        seed = dict()
                        for k, v in models.items():
                            # Get the symbolic variable assigned to the model
                            symVar = getSymbolicVariableFromId(k)
                            # Save the new input as seed.
                            seed.update({symVar.getKindValue(): v.getValue()})
                        if seed:
                            inputs.append(seed)

            # Update the previous constraints with true branch to keep a good
            # path.
            previousConstraints = ast.land(previousConstraints, pc.getTakenPathConstraintAst())

        # Clear the path constraints to be clean at the next execution.
        clearPathConstraints()

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

        self.assertIn({4096L: 101L,
                       4097L: 108L,
                       4098L: 105L,
                       4099L: 116L,
                       4100L: 101L}, lastInput)


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
                setConcreteMemoryAreaValue(start, bytearray(mem['memory']))

        # setup registers
        for reg_name in ("rax", "rbx", "rcx", "rdx", "rdi", "rsi", "rbp",
                         "rsp", "rip", "r8", "r9", "r10", "r11", "r12", "r13",
                         "r14", "eflags", "xmm0", "xmm1", "xmm2", "xmm3",
                         "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9",
                         "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15"):
            setConcreteRegisterValue(Register(getattr(REG, reg_name.upper()), regs[reg_name]))

        # run the code
        pc = getConcreteRegisterValue(REG.RIP)
        while pc != 0x409A18:
            opcodes = getConcreteMemoryAreaValue(pc, 20)

            instruction = Instruction()
            instruction.setOpcodes(opcodes)
            instruction.setAddress(pc)

            # Check if triton doesn't supports this instruction
            self.assertTrue(processing(instruction))

            pc = getConcreteRegisterValue(REG.RIP)

            if concretize:
                concretizeAllMemory()
                concretizeAllRegister()

        rax = getConcreteRegisterValue(REG.RAX)
        rbx = getConcreteRegisterValue(REG.RBX)
        rcx = getConcreteRegisterValue(REG.RCX)
        rdx = getConcreteRegisterValue(REG.RDX)
        rsi = getConcreteRegisterValue(REG.RSI)

        self.assertEqual(rax, 0)
        self.assertEqual(rbx, 0)
        self.assertEqual(rcx, 0)
        self.assertEqual(rdx, 0x4d2)
        self.assertEqual(rsi, 0x3669000000000000)


class BaseTestSimulation(DefCamp2015, SeedCoverage, Emu1):

    """BaseClass to test the simulation."""


class TestSymboliqueEngineNoOptim(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine without optimization."""

    def setUp(self):
        """Define the arch."""
        setArchitecture(ARCH.X86_64)
        super(TestSymboliqueEngineNoOptim, self).setUp()


class TestSymboliqueEngineAligned(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic emulation engine with ALIGNED_MEMORY."""

    def setUp(self):
        """Define the arch and modes."""
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.ALIGNED_MEMORY, True)
        super(TestSymboliqueEngineAligned, self).setUp()


class TestSymboliqueEngineAlignedAst(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic engine with ALIGNED_MEMORY and AST Dict."""

    def setUp(self):
        """Define the arch and modes."""
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.ALIGNED_MEMORY, True)
        enableMode(MODE.AST_DICTIONARIES, True)
        super(TestSymboliqueEngineAlignedAst, self).setUp()

    @unittest.skip("segfault")
    def test_defcamp_2015(self):
        pass


class TestSymboliqueEngineAst(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic engine with AST Dictionnary."""

    def setUp(self):
        """Define the arch and modes."""
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.AST_DICTIONARIES, True)
        super(TestSymboliqueEngineAst, self).setUp()

    @unittest.skip("segfault")
    def test_defcamp_2015(self):
        pass


class TestSymboliqueEngineConcreteAst(BaseTestSimulation, unittest.TestCase):

    """Testing the symbolic engine with AST Dictionnary and concretization."""

    def setUp(self):
        """Define the arch and modes."""
        setArchitecture(ARCH.X86_64)
        enableMode(MODE.AST_DICTIONARIES, True)
        super(TestSymboliqueEngineConcreteAst, self).setUp()

    def test_emulate(self):
        super(TestSymboliqueEngineConcreteAst, self).test_emulate(False)

    @unittest.skip("No seed coverage with concretization.")
    def test_seed_coverage(self):
        pass

    @unittest.skip("No defcamp with concretization")
    def test_defcamp_2015(self):
        pass

