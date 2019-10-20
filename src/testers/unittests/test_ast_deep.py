import unittest
from triton import *

DEPTH = 10000


class TestDeep(unittest.TestCase):

    def setUp(self):
        """Define the arch."""
        self.triton = TritonContext()
        self.triton.setArchitecture(ARCH.X86_64)
        self.ctx = self.triton.getAstContext()

        sym_var = self.ctx.variable(self.triton.convertRegisterToSymbolicVariable(self.triton.registers.rax))

        add_inst = Instruction()
        add_inst.setAddress(0x100)
        add_inst.setOpcode("\x48\x01\xc0")      # add   rax, rax

        sub_inst = Instruction()
        sub_inst.setOpcode("\x48\x29\xC0")      # sub   rax, rax

        for _ in range(DEPTH):
            self.triton.processing(add_inst)
            sub_inst.setAddress(add_inst.getAddress() + add_inst.getSize())
            self.triton.processing(sub_inst)
            add_inst.setAddress(sub_inst.getAddress() + sub_inst.getSize())

        self.complex_ast_tree = self.triton.getSymbolicRegister(self.triton.registers.rax).getAst()

    def test_z3_conversion(self):
        result = self.triton.simplify(self.complex_ast_tree, True)
        answer = self.ctx.bv(0, 64)
        self.assertEqual(str(result), str(answer))

    def test_duplication(self):
        s = self.ctx.duplicate(self.complex_ast_tree)
