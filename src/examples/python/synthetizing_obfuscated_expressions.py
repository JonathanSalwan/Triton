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

import sys
import ctypes

from triton import *


# Oracles table, each entry is structured as follow (x, y, result).
# More entries there are, more precise is the result.
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


def synthetize(ctx, expr):
    ast       = ctx.getAstContext()
    variables = ast.search(expr, AST_NODE.VARIABLE)

    x = variables[0]
    y = variables[1]
    s = {
        8:  ctypes.c_uint8,
        16: ctypes.c_uint16,
        32: ctypes.c_uint32,
        64: ctypes.c_uint64,
    }

    for entry in oracles_table:
        OK = False
        for oracle in entry['oracles']:
            ctx.setConcreteVariableValue(x.getSymbolicVariable(), s[x.getBitvectorSize()](oracle[0]).value)
            ctx.setConcreteVariableValue(y.getSymbolicVariable(), s[y.getBitvectorSize()](oracle[1]).value)
            if expr.evaluate() != s[y.getBitvectorSize()](oracle[2]).value:
                OK = False
                break
            else:
                OK = True
                continue
        if OK is True:
            return eval(entry['synthesis'])

    return expr


def main():
    ctx = TritonContext(ARCH.X86_64)
    ast = ctx.getAstContext()

    x = ast.variable(ctx.newSymbolicVariable(8))
    y = ast.variable(ctx.newSymbolicVariable(8))

    # Some obfuscated expressions
    obf_exprs = [
        (x | y) + y - (~x & y), # x + y
        (x | y) - y + (~x & y), # x ^ y
        (x & ~y) | (~x & y),    # x ^ y
        (x ^ y) + y - (~x & y), # x | y
        -(x | y) + y + x,       # x & y
    ]

    for expr in obf_exprs:
        print('In: %s' %(expr))
        expr = synthetize(ctx, expr)
        print('Out: %s' %(expr))
        print()

    return 0


if __name__ == '__main__':
    sys.exit(main())
