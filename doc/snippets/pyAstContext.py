>>> from triton import REG, TritonContext, ARCH, Instruction, AST_REPRESENTATION
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> opcodes = "\x48\x31\xD0"
>>> inst = Instruction()

>>> inst.setOpcodes(opcodes)
>>> inst.setAddress(0x400000)
>>> inst.updateContext(ctxt.Register(REG.RAX, 12345))
>>> inst.updateContext(ctxt.Register(REG.RDX, 67890))

>>> ctxt.processing(inst)
True
>>> print inst
0x400000: xor rax, rdx

# [Reference]
>>> zfId = ctxt.getSymbolicRegisterId(ctxt.Register(REG.ZF))
>>> partialTree = ctxt.getSymbolicExpressionFromId(zfId).getAst()
>>> print partialTree
(ite (= ((_ extract 63 0) ref!0) (_ bv0 64)) (_ bv1 1) (_ bv0 1))

>>> fullTree = ctxt.getFullAst(partialTree)
>>> print fullTree
(ite (= ((_ extract 63 0) ((_ zero_extend 0) (bvxor (_ bv12345 64) (_ bv67890 64)))) (_ bv0 64)) (_ bv1 1) (_ bv0 1))

# [Reference]

# [SMT]
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)
>>> ctxt.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
>>> inst = Instruction()
>>> inst.setOpcodes("\x48\x01\xd8") # add rax, rbx
>>> inst.setAddress(0x400000)
>>> inst.updateContext(ctxt.Register(REG.RAX, 0x1122334455667788))
>>> inst.updateContext(ctxt.Register(REG.RBX, 0x8877665544332211))
>>> ctxt.processing(inst)
True
>>> print inst
0x400000: add rax, rbx

>>> for expr in inst.getSymbolicExpressions():
...     print expr
...
ref_0 = ((0x1122334455667788 + 0x8877665544332211) & 0xFFFFFFFFFFFFFFFF) # ADD operation
ref_1 = (0x1 if (0x10 == (0x10 & ((ref_0 & 0xFFFFFFFFFFFFFFFF) ^ (0x1122334455667788 ^ 0x8877665544332211)))) else 0x0) # Adjust flag
ref_2 = ((((0x1122334455667788 & 0x8877665544332211) ^ (((0x1122334455667788 ^ 0x8877665544332211) ^ (ref_0 & 0xFFFFFFFFFFFFFFFF)) & (0x1122334455667788 ^ 0x8877665544332211))) >> 63) & 0x1) # Carry flag
ref_3 = ((((0x1122334455667788 ^ (~(0x8877665544332211) & 0xFFFFFFFFFFFFFFFF)) & (0x1122334455667788 ^ (ref_0 & 0xFFFFFFFFFFFFFFFF))) >> 63) & 0x1) # Overflow flag
ref_4 = ((((((((0x1 ^ (((ref_0 & 0xFF) >> 0x0) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x1) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x2) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x3) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x4) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x5) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x6) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x7) & 0x1)) # Parity flag
ref_5 = ((ref_0 >> 63) & 0x1) # Sign flag
ref_6 = (0x1 if ((ref_0 & 0xFFFFFFFFFFFFFFFF) == 0x0) else 0x0) # Zero flag
ref_7 = 0x400003 # Program Counter

# [SMT]

# TODO : astRepresentation should not be a global value.
>>> ctxt.setAstRepresentationMode(AST_REPRESENTATION.SMT)

# [example 1]
>>> # Get the symbolic expression of the ZF flag
>>> zfId    = ctxt.getSymbolicRegisterId(ctxt.Register(REG.ZF))
>>> zfExpr  = ctxt.getFullAst(ctxt.getSymbolicExpressionFromId(zfId).getAst())

>>> astCtxt = ctxt.getAstContext()

>>> # (assert (= zf True))
>>> newExpr = astCtxt.assert_(
...            astCtxt.equal(
...                zfExpr,
...                astCtxt.bvtrue()
...            )
...          )

>>> # Get a model
>>> models  = ctxt.getModel(newExpr)
>>> # [example 1]

# [example 2]
# Node information

>>> node = astCtxt.bvadd(astCtxt.bv(1, 8), astCtxt.bvxor(astCtxt.bv(10, 8), astCtxt.bv(20, 8)))
>>> print type(node)
<type 'AstNode'>

>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> subchild = node.getChilds()[1].getChilds()[0]
>>> print subchild
(_ bv10 8)

>>> print subchild.getChilds()[0].getValue()
10
>>> print subchild.getChilds()[1].getValue()
8

# Node modification

>>> node = astCtxt.bvadd(astCtxt.bv(1, 8), astCtxt.bvxor(astCtxt.bv(10, 8), astCtxt.bv(20, 8)))
>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> node.setChild(0, astCtxt.bv(123, 8))
True
>>> print node
(bvadd (_ bv123 8) (bvxor (_ bv10 8) (_ bv20 8)))

# [example 2]
# [example 3]
>>> a = astCtxt.bv(1, 8)
>>> b = astCtxt.bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print c
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))

# [example 3]
