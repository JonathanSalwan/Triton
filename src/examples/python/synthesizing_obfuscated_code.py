#!/usr/bin/env python
## -*- coding: utf-8 -*-

import sys
from triton import *

# int f(unsigned a, unsigned b) {
#   unsigned n = (a & ~(-((((b & a) * (b | a) + (b & ~a) * (~b & a)) & b) *                     \
#                (((b&a)*(b|a) + (b& ~a)*(~b&a))|b) + (((b&a)*(b| a) + (b & ~a) *               \
#                (~b & a)) & ~b) * (~((b & a) * (b | a) + (b & ~a) * (~b & a)) & b)) - 1)) -    \
#                (~a & (-((((b & a) * (b | a) + (b & ~a) * (~b & a)) & b) * (((b & a) *         \
#                (b | a) + (b & ~a) * (~b & a)) | b) + (((b & a) * (b | a) + (b & ~a) *         \
#                (~b & a)) & ~b) * (~((b & a) * (b | a) + (b & ~a) * (~b & a)) & b)) - 1));     \
#   return n;
# }
#
# The above function returns: a - (~((b * a) * b))
# Below its binary code.
#
CODE  = b"\x55\x48\x89\xE5\x89\x7D\xEC\x89\x75\xE8\x8B\x45\xE8\x23\x45\xEC"
CODE += b"\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD1\x0F\xAF\xC8\x8B\x45\xEC"
CODE += b"\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7\xD0\x23\x45\xEC\x0F"
CODE += b"\xAF\xC2\x01\xC8\x23\x45\xE8\x89\xC2\x8B\x45\xE8\x23\x45\xEC\x89"
CODE += b"\xC1\x8B\x45\xE8\x0B\x45\xEC\x89\xCE\x0F\xAF\xF0\x8B\x45\xEC\xF7"
CODE += b"\xD0\x23\x45\xE8\x89\xC1\x8B\x45\xE8\xF7\xD0\x23\x45\xEC\x0F\xAF"
CODE += b"\xC1\x01\xF0\x0B\x45\xE8\x89\xD6\x0F\xAF\xF0\x8B\x45\xE8\x23\x45"
CODE += b"\xEC\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD1\x0F\xAF\xC8\x8B\x45"
CODE += b"\xEC\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7\xD0\x23\x45\xEC"
CODE += b"\x0F\xAF\xC2\x8D\x14\x01\x8B\x45\xE8\xF7\xD0\x89\xD1\x21\xC1\x8B"
CODE += b"\x45\xE8\x23\x45\xEC\x89\xC2\x8B\x45\xE8\x0B\x45\xEC\x89\xD7\x0F"
CODE += b"\xAF\xF8\x8B\x45\xEC\xF7\xD0\x23\x45\xE8\x89\xC2\x8B\x45\xE8\xF7"
CODE += b"\xD0\x23\x45\xEC\x0F\xAF\xC2\x01\xF8\xF7\xD0\x23\x45\xE8\x0F\xAF"
CODE += b"\xC1\x8D\x14\x06\x8B\x45\xEC\x01\xD0\x83\xC0\x01\x89\x45\xFC\x8B"
CODE += b"\x45\xFC\x5D\xC3"

def emulate(ctx, pc):
    while pc:
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)
        instruction = Instruction(pc, opcode)
        ctx.processing(instruction)
        print(instruction)
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    return

def main():
    ctx = TritonContext(ARCH.X86_64)
    ast = ctx.getAstContext()

    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    a = ast.variable(ctx.symbolizeRegister(ctx.registers.edi, "a"))
    b = ast.variable(ctx.symbolizeRegister(ctx.registers.esi, "b"))

    ctx.setConcreteMemoryAreaValue(0x1000, CODE)
    print('Emulate the code')
    emulate(ctx, 0x1000)

    eax = ctx.getRegisterAst(ctx.registers.eax)
    print()
    print('Synthesis IN:', ast.unroll(eax))
    print()
    eax = ctx.synthesize(eax, constant=False, subexpr=True)
    print('Synthesis OUT:', ast.unroll(eax))
    return 0

if __name__ == '__main__':
    sys.exit(main())
