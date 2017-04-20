>>> from triton import ARCH, TritonContext, Instruction, REG
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> inst = Instruction("\x8A\xA4\x4A\x00\x01\x00\x00")
>>> inst.setAddress(0x40000)

# [Example]
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov ah, byte ptr [rdx + rcx*2 + 0x100]

>>> op0 = inst.getOperands()[0]
>>> print op0
ah:8 bv[15..8]

>>> op0.getName()
'ah'

>>> op0.getSize()
1L

>>> op0.getBitSize()
8L

>>> ctxt.getParentRegister(op0).getName()
'rax'

# [Example]

# [Constructor]
>>> ah = ctxt.Register(REG.AH, 0x18)
>>> print ah
ah:8 bv[15..8]

>>> print ah.getBitSize()
8

>>> print hex(ah.getConcreteValue())
0x18L

>>> print ctxt.Register(REG.RAX)
rax:64 bv[63..0]

# [Constructor]
