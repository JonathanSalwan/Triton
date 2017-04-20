>>> from triton import TritonContext, REG, ARCH
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

# [Description]
>>> symvar = ctxt.convertRegisterToSymbolicVariable(ctxt.Register(REG.X86_64.RAX))
>>> print symvar
SymVar_0:64

# [Description]
