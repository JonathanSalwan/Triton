>>> from triton import ARCH, TritonContext, REG
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

# [Description]
>>> ah = ctxt.Register(REG.AH)
>>> bitvector = ah.getBitvector()
>>> bitvector.getHigh()
15L
>>> bitvector.getLow()
8L
>>> bitvector.getVectorSize()
8L

# [Description]
