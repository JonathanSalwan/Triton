from __future__ import print_function
# import triton

from triton_autocomplete import *

ctx = TritonContext()
ctx.setArchitecture(ARCH.X86_64)
ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

# ctx = triton_import.TritonContext()
# ctx.setConcreteMemoryValue()

print('Done')
