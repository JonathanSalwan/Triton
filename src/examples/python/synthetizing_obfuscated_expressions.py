#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## Example of synthetizing obfuscated expressions.
##
## $ python synthetizing_obfuscated_expressions.py
## In: (bvsub (bvadd (bvor SymVar_0 SymVar_1) SymVar_1) (bvand (bvnot SymVar_0) SymVar_1))
## Out: (bvadd SymVar_0 SymVar_1)
##
## In: (bvadd (bvsub (bvor SymVar_0 SymVar_1) SymVar_1) (bvand (bvnot SymVar_0) SymVar_1))
## Out: (bvxor SymVar_0 SymVar_1)
##
## In: (bvor (bvand SymVar_0 (bvnot SymVar_1)) (bvand (bvnot SymVar_0) SymVar_1))
## Out: (bvxor SymVar_0 SymVar_1)
##
## In: (bvsub (bvadd (bvxor SymVar_0 SymVar_1) SymVar_1) (bvand (bvnot SymVar_0) SymVar_1))
## Out: (bvor SymVar_0 SymVar_1)
##
## In: (bvadd (bvadd (bvneg (bvor SymVar_0 SymVar_1)) SymVar_1) SymVar_0)
## Out: (bvand SymVar_1 SymVar_0)
##
## In: (bvshl (bvlshr (bvshl SymVar_2 (_ bv8 32)) (_ bv16 32)) (_ bv8 32))
## Out: (bvand SymVar_2 (_ bv16776960 32))
##

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


def main():
    ctx = TritonContext(ARCH.X86_64)
    ast = ctx.getAstContext()

    x = ast.variable(ctx.newSymbolicVariable(8))
    y = ast.variable(ctx.newSymbolicVariable(8))
    z = ast.variable(ctx.newSymbolicVariable(32))

    # Some obfuscated expressions
    obf_exprs = [
        (x | y) + y - (~x & y), # x + y
        (x | y) - y + (~x & y), # x ^ y
        (x & ~y) | (~x & y),    # x ^ y
        (x ^ y) + y - (~x & y), # x | y
        -(x | y) + y + x,       # x & y
        ((z << 8) >> 16) << 8,  # z & 0xffff00
    ]

    for expr in obf_exprs:
        print('In: %s' %(expr))
        expr = synthetize(ctx, expr)
        print('Out: %s' %(expr))
        print()

    return 0


if __name__ == '__main__':
    sys.exit(main())
