>>> from triton import TritonContext, ARCH, Instruction, REG

>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)
>>> inst = Instruction()
>>> inst.setOpcodes("\x48\x35\x44\x33\x22\x11") # xor rax, 0x11223344

>>> symvar = ctxt.convertRegisterToSymbolicVariable(ctxt.Register(REG.X86_64.RAX))
>>> print symvar
SymVar_0:64

>>> ctxt.processing(inst)
True
>>> print inst
0x0: xor rax, 0x11223344

>>> raxAst = ctxt.getFullAstFromId(ctxt.getSymbolicRegisterId(ctxt.Register(REG.X86_64.RAX)))
>>> print raxAst
((_ zero_extend 0) (bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64)))

>>> astCtxt = ctxt.getAstContext()
>>> constraint = astCtxt.assert_(astCtxt.equal(raxAst, astCtxt.bv(0, raxAst.getBitvectorSize())))
>>> print constraint
(assert (= ((_ zero_extend 0) (bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64))) (_ bv0 64)))

>>> model = ctxt.getModel(constraint)
>>> print model #doctest: +ELLIPSIS
{0L: <SolverModel object at 0x...>}

>>> symvarModel =  model[symvar.getId()] # Model from the symvar's id
>>> print symvarModel
SymVar_0 = 0x11223344
>>> hex(symvarModel.getValue())
'0x11223344L'
