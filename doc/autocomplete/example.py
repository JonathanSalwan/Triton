from __future__ import print_function
# triton_autocomplete will raise an import error.
# IDEs should still provide autocomplete based on
# the triton_autocomplete module
from triton import *
try:
    from triton_autocomplete import *
except ImportError:
    pass


ctx = TritonContext()
# Set the arch
ctx.setArchitecture(ARCH.X86)

inst = Instruction()
inst.setAddress(0x40000)
inst.setOpcode(b"\x89\xd0")    # mov eax, edx
ctx.processing(inst)
print(inst)
