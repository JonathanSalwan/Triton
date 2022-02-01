#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
## Example of synthesizing obfuscated expressions.
##
## $ time python3 ./synthesizing_obfuscated_expressions.py
## In: (((((SymVar_0 | SymVar_1) + SymVar_1) & 0xff) - ((~(SymVar_0) & 0xff) & SymVar_1)) & 0xff)
## Out: ((SymVar_0 + SymVar_1) & 0xff)
##
## In: (((((SymVar_0 | SymVar_1) - SymVar_1) & 0xff) + ((~(SymVar_0) & 0xff) & SymVar_1)) & 0xff)
## Out: (SymVar_0 ^ SymVar_1)
##
## In: ((SymVar_0 & (~(SymVar_1) & 0xff)) | ((~(SymVar_0) & 0xff) & SymVar_1))
## Out: (SymVar_0 ^ SymVar_1)
##
## In: (((((SymVar_0 ^ SymVar_1) + SymVar_1) & 0xff) - ((~(SymVar_0) & 0xff) & SymVar_1)) & 0xff)
## Out: (SymVar_0 | SymVar_1)
##
## In: ((((-(SymVar_0 | SymVar_1) + SymVar_1) & 0xff) + SymVar_0) & 0xff)
## Out: (SymVar_1 & SymVar_0)
##
## In: (((((SymVar_2 << 0x8) & 0xffffffff) >> 0x10) << 0x8) & 0xffffffff)
## Out: (SymVar_2 & 0xffff00)
##
## In: (((((((((((SymVar_0 ^ SymVar_1) + ((0x2 * (SymVar_0 & SymVar_1)) & 0xff)) & 0xff) * 0x27) & 0xff) +  ...
## Out: ((SymVar_0 + SymVar_1) & 0xff)
##
## In: (((0xed * ((((((((0x2d * ((((((((((((((((((0x3a * (((((((((((0x56 * ((((((((((((0xed * ((((0xe5 * Sy ...
## Out: (SymVar_0 ^ 0x5c)
##
## python3 ./synthesizing_obfuscated_expressions.py  0.12s user 0.01s system 99% cpu 0.125 total
##

import sys
import ctypes

from triton import *


# The following function returns an MBA-obfuscated expression found by
# Mougey et al. while analyzing an obfuscated program. I took this
# representation from the Ninon Eyrolle's thesis. The MBA performs
# the following operation: (x ^ 92).
def x_xor_92_obfuscated(x):
    a = 229 * x + 247
    b = 237 * a + 214 + ((38 * a + 85) & 254)
    c = (b + ((-(2 * b) + 255) & 254)) * 3 + 77
    d = ((86 * c + 36) & 70) * 75 + 231 * c + 118
    e = ((58 * d + 175) & 244) + 99 * d + 46
    f = (e & 148)
    g = (f - (e & 255) + f) * 103 + 13
    R = (237 * (45 * g + (174 * g | 34) * 229 + 194 - 247) & 255)
    return R


def main():
    if VERSION.Z3_INTERFACE is False:
        # NOTE: The FORALL node is not supported currently in Bitwuzla.
        print("This script requires Z3 as the solver engine. Compile Triton with Z3 support and re-run.")
        # Return 0 so the test don't fail.
        sys.exit(0)

    ctx = TritonContext(ARCH.X86_64)
    ctx.setSolver(SOLVER.Z3)

    ast = ctx.getAstContext()

    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    x = ast.variable(ctx.newSymbolicVariable(8, 'x'))
    y = ast.variable(ctx.newSymbolicVariable(8, 'y'))
    z = ast.variable(ctx.newSymbolicVariable(32, 'z'))

    # Some obfuscated expressions
    obf_exprs = [
        (x | y) + y - (~x & y),                             # x + y         (from http://archive.bar/pdfs/bar2020-preprint9.pdf)
        (x | y) - y + (~x & y),                             # x ^ y         (from http://archive.bar/pdfs/bar2020-preprint9.pdf)
        (x & ~y) | (~x & y),                                # x ^ y         (from ?)
        (x ^ y) + y - (~x & y),                             # x | y         (from http://archive.bar/pdfs/bar2020-preprint9.pdf)
        -(x | y) + y + x,                                   # x & y         (from http://archive.bar/pdfs/bar2020-preprint9.pdf)
        ((z << 8) >> 16) << 8,                              # z & 0xffff00  (from https://blog.regehr.org/archives/1636)
        (((x ^ y) + 2 * (x & y)) * 39 + 23) * 151 + 111,    # x + y         (from Ninon Eyrolle's thesis)
        x_xor_92_obfuscated(x),                             # x ^ 92        (from Ninon Eyrolle's thesis)
    ]

    for expr in obf_exprs:
        (print('In: %s' %(expr)) if len(str(expr)) < 100 else print('In: %s ...' %(str(expr)[0:100])))
        expr = ctx.synthesize(expr, constant=True)
        print('Out: %s' %(expr))
        print()

    return 0


if __name__ == '__main__':
    sys.exit(main())
