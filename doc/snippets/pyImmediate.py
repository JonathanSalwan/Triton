>>> from triton import TritonContext, ARCH, Instruction, Immediate, CPUSIZE

>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> inst = Instruction()
>>> inst.setOpcodes("\xB8\x14\x00\x00\x00")

# [Process instruction]
>>> ctxt.processing(inst)
True
>>> print inst
0x0: mov eax, 0x14

>>> op1 = inst.getOperands()[1]
>>> print op1
0x14:32 bv[31..0]

>>> print hex(op1.getValue())
0x14L

>>> print op1.getBitSize()
32

# [Process instruction]

# [Constructor]
>>> imm = Immediate(0x1234, CPUSIZE.WORD)
>>> print imm
0x1234:16 bv[15..0]
>>> imm.getValue()
4660L
>>> imm.getSize()
2L
>>> imm.getBitSize()
16L

# [Constructor]
