#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## Example of synthetizing obfuscated expressions.
##
## $ time python ./synthetizing_obfuscated_expressions.py
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
## python ./synthetizing_obfuscated_expressions.py  0.12s user 0.01s system 99% cpu 0.125 total
##

from __future__ import print_function

import sys
import ctypes

from triton import *


# Oracles table, each entry is structured as follow (x value, y value, result).
# More entries there are, more precise is the result for example checkout
# this table [0] or generate your own table with [1].
#
# [0] http://shell-storm.org/repo/Notepad/synthesis_tables.py
# [1] http://shell-storm.org/repo/Notepad/gen_synthesis_tables.py

oracles_table = [
    {
        'oracles'   : [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 2)],
        'synthesis' : 'x + y'
    },
    {
        'oracles'   : [(0, 0, 0), (0, 1, -1), (1, 0, 1), (1, 1, 0)],
        'synthesis' : 'x - y'
    },
    {
        'oracles'   : [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)],
        'synthesis' : 'x ^ y'
    },
    {
        'oracles'   : [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 1)],
        'synthesis' : 'x | y'
    },
    {
        'oracles'   : [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 1)],
        'synthesis' : 'x & y'
    },
]


sizes_table = {
    8:  ctypes.c_uint8,
    16: ctypes.c_uint16,
    32: ctypes.c_uint32,
    64: ctypes.c_uint64,
}


# Two vars synthetizing
def two_vars_synthetizing(ctx, expr, x, y):
    for entry in oracles_table:
        valid = True

        for oracle in entry['oracles']:
            ctx.setConcreteVariableValue(x.getSymbolicVariable(), sizes_table[x.getBitvectorSize()](oracle[0]).value)
            ctx.setConcreteVariableValue(y.getSymbolicVariable(), sizes_table[y.getBitvectorSize()](oracle[1]).value)
            if expr.evaluate() != sizes_table[y.getBitvectorSize()](oracle[2]).value:
                valid = False
                break

        if valid is True:
            return eval(entry['synthesis'])

    return expr


# Constant synthetizing
def constant_synthetizing(ctx, expr, x):
    ast = ctx.getAstContext()
    c   = ast.variable(ctx.newSymbolicVariable(x.getBitvectorSize()))

    synth = [
        (x & c, 'x & c'),
        (x * c, 'x * c'),
        (x ^ c, 'x ^ c'),
        (x + c, 'x + c'),
        (x - c, 'x - c'),
        (c - x, 'c - x'),
    ]

    for op, s in synth:
        m = ctx.getModel(ast.forall([x], expr == op))
        if m:
            c = m[c.getSymbolicVariable().getId()].getValue()
            return eval(s)

    return expr


def synthetize(ctx, expr):
    ast       = ctx.getAstContext()
    variables = ast.search(expr, AST_NODE.VARIABLE)

    # There is no variable in the expression
    if len(variables) == 0:
        return expr

    elif len(variables) == 1:
        x = variables[0]
        return constant_synthetizing(ctx, expr, x)

    elif len(variables) == 2:
        x = variables[0]
        y = variables[1]
        return two_vars_synthetizing(ctx, expr, x, y)

    return expr


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
    ctx = TritonContext(ARCH.X86_64)
    ast = ctx.getAstContext()

    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    x = ast.variable(ctx.newSymbolicVariable(8))
    y = ast.variable(ctx.newSymbolicVariable(8))
    z = ast.variable(ctx.newSymbolicVariable(32))

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
        expr = synthetize(ctx, expr)
        print('Out: %s' %(expr))
        print()

    return 0


if __name__ == '__main__':
    sys.exit(main())
