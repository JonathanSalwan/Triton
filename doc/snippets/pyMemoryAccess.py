>>> from triton import TritonContext, ARCH, Instruction, MemoryAccess
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> inst = Instruction("\x8A\xA4\x4A\x00\x01\x00\x00")
>>> inst.setAddress(0x40000)

# [Example]
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov ah, byte ptr [rdx + rcx*2 + 0x100]

>>> op1 = inst.getOperands()[1]
>>> print op1
[@0x100]:8 bv[7..0]

>>> print op1.getBaseRegister()
rdx:64 bv[63..0]

>>> print op1.getIndexRegister()
rcx:64 bv[63..0]

>>> print op1.getScale()
0x2:64 bv[63..0]

>>> print op1.getDisplacement()
0x100:64 bv[63..0]

>>> print op1.getLeaAst()
(bvadd (_ bv0 64) (bvadd (bvmul (_ bv0 64) (_ bv2 64)) (_ bv256 64)))

>>> print hex(op1.getLeaAst().evaluate())
0x100L

>>> print hex(op1.getAddress())
0x100L

>>> print op1.getSize()
1

# [Example]

# [Constructor]
>>> mem = MemoryAccess(0x400f4d3, 8, 0x6162636465666768)
>>> print mem
[@0x400f4d3]:64 bv[63..0]

>>> hex(mem.getAddress())
'0x400f4d3L'

>>> mem.getSize()
8L

>>> hex(mem.getConcreteValue())
'0x6162636465666768L'

# [Constructor]
