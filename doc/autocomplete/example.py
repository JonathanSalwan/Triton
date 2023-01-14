from __future__ import print_function
# The triton_autocomplete module has been replaced with a .pyi stub file
# which is automatically installed when using a precompiled Triton package
# IDEs should detect it and provide autocomplete without any extra imports
from triton import *


ctx = TritonContext()
# Set the arch
ctx.setArchitecture(ARCH.X86)

inst = Instruction()
inst.setAddress(0x40000)
inst.setOpcode(b"\x89\xd0")    # mov eax, edx
ctx.processing(inst)
print(inst)
