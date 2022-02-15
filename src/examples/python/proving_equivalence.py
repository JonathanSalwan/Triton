#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## $ python ./proving equivalence.py
## True
## True
## True
## True
## True
## True
## True
## True
## True
## True
## True
## True
## True
## True
##

import sys
from triton import *


def prove(ctx, n):
    ast = ctx.getAstContext()
    if ctx.isSat(ast.lnot(n)) == True:
        return False
    return True

if __name__ == '__main__':
    ctx = TritonContext(ARCH.X86_64)
    ast = ctx.getAstContext()

    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    x = ast.variable(ctx.newSymbolicVariable(8, 'x'))
    y = ast.variable(ctx.newSymbolicVariable(8, 'y'))

    # MBA coming from VMProtect https://whereisr0da.github.io/blog/posts/2021-02-16-vmp-3/
    # To detect their equivalence you can synthesize them (see synthesizing_obfuscated_expressions.py)
    # Then you can confirm the synthesized output with this example
    print(prove(ctx, x ^ y          == (~(~(x) & ~(y)) & ~(~(~(x)) & ~(~(y))))))
    print(prove(ctx, x + y          == ((~(~(x)) & ~(~(y))) + (~(~(x)) | ~(~(y))))))
    print(prove(ctx, x + y          == ((~(~(y)) | ~(~(x))) + ~(~(x)) - (~(~(x)) & ~(~(~(y)))))))
    print(prove(ctx, x + y          == ((~(~(x)) | ~(~(y))) + (~(~(~(x))) | ~(~(y))) - (~(~(~(x)))))))
    print(prove(ctx, x + y          == ((~(~(x)) | ~(~(y))) + ~(~(y)) - (~(~(~(x))) & ~(~(y))))))
    print(prove(ctx, x + y          == (~(~(y)) + (~(~(x)) & ~(~(~(y)))) + (~(~(x)) & ~(~(y))))))
    print(prove(ctx, x - y          == (~(~(x) + y))))
    print(prove(ctx, ~((x | y) - x) == (~(((~(~(x)) | y) - (~(~(x))))))))
    print(prove(ctx, x - y          == (~((~(x) & ~(x)) + y) & ~((~(x) & ~(x)) + y))))
    print(prove(ctx, x & y          == ((~(~(x)) | y) - (~(~(~(x))) & y) - (~(~(x)) & ~y))))
    print(prove(ctx, x & y          == ((~(~(~(x))) | y) - (~(~(~(x)))))))
    print(prove(ctx, x | y          == ((~(~(x)) & ~(y)) + y)))
    print(prove(ctx, x | y          == (((~(~(x)) & ~(y)) & y) + ((~(~(x)) & ~(y)) | y))))
    print(prove(ctx, x + y          == ((~(~(x)) & ~(~(y))) + (~(~(x)) | ~(~(y))))))

    sys.exit(0)
