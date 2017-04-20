>>> from triton import TritonContext, ARCH, Instruction, REG

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

>>> for expr in inst.getSymbolicExpressions():
...     print expr
...
ref!0 = ((_ zero_extend 0) (bvxor (_ bv12345 64) (_ bv67890 64))) ; XOR operation
ref!1 = (_ bv0 1) ; Clears carry flag
ref!2 = (_ bv0 1) ; Clears overflow flag
ref!3 = (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv7 8)))) ; Parity flag
ref!4 = ((_ extract 63 63) ref!0) ; Sign flag
ref!5 = (ite (= ((_ extract 63 0) ref!0) (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
ref!6 = ((_ zero_extend 0) (_ bv4194307 64)) ; Program Counter

>>> expr_1 = inst.getSymbolicExpressions()[0]
>>> expr_1 # doctest: +ELLIPSIS
<SymbolicExpression object at 0x...>
>>> print expr_1
ref!0 = ((_ zero_extend 0) (bvxor (_ bv12345 64) (_ bv67890 64))) ; XOR operation

>>> print expr_1.getId()
0

>>> ast = expr_1.getAst()
>>> ast # doctest: +ELLIPSIS
<AstNode object at 0x...>
>>> print ast
((_ zero_extend 0) (bvxor (_ bv12345 64) (_ bv67890 64)))


>>> expr_1.isMemory()
False

>>> expr_1.isRegister()
True

>>> print expr_1.getOriginRegister()
rax:64 bv[63..0]

