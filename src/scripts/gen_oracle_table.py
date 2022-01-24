#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## Copyright (C) - Triton
## This program is under the terms of the Apache License 2.0.
##
## Generate the oracle table for obfuscated expressions synthesis
## Output: src/libtriton/engines/synthesis/oracleTable.cpp
##

import sys
import operator

from triton import *
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64
from random import randrange

HOW_BIG_IS_THE_TABLE = 10

ctx = TritonContext(ARCH.X86_64) # does not matter of the architecture, we just need an AstContext
ast = ctx.getAstContext()


binary_operators = [
    [ast.bvadd,     'bvadd',  'triton::ast::BVADD_NODE'],
    [ast.bvand,     'bvand',  'triton::ast::BVAND_NODE'],
    [ast.bvmul,     'bvmul',  'triton::ast::BVMUL_NODE'],
    [ast.bvnand,    'bvnand', 'triton::ast::BVNAND_NODE'],
    [ast.bvnor,     'bvnor',  'triton::ast::BVNOR_NODE'],
    [ast.bvor,      'bvor',   'triton::ast::BVOR_NODE'],
    [ast.bvrol,     'bvrol',  'triton::ast::BVROL_NODE'],
    [ast.bvror,     'bvror',  'triton::ast::BVROR_NODE'],
    [ast.bvsdiv,    'bvsdiv', 'triton::ast::BVSDIV_NODE'],
    [ast.bvsmod,    'bvsmod', 'triton::ast::BVSMOD_NODE'],
    [ast.bvsrem,    'bvsrem', 'triton::ast::BVSREM_NODE'],
    [ast.bvsub,     'bvsub',  'triton::ast::BVSUB_NODE'],
    [ast.bvudiv,    'bvudiv', 'triton::ast::BVUDIV_NODE'],
    [ast.bvurem,    'bvurem', 'triton::ast::BVUREM_NODE'],
    [ast.bvxnor,    'bvxnor', 'triton::ast::BVXNOR_NODE'],
    [ast.bvxor,     'bvxor',  'triton::ast::BVXOR_NODE'],
]


def gen_binary_operator(binary_op):
    op, name, enum = binary_op
    print('        /* %s synthesis */' %(name))
    print('        {')
    print('          %s, {' %(enum))
    for i in range(HOW_BIG_IS_THE_TABLE):
        stop = False
        while not stop:
            s1 = ast.bv(randrange(1, 0x100), 8)
            s2 = ast.bv(randrange(1, 0x100), 8)

            # Special case for div, we need small number
            if name in ['bvsdiv', 'bvudiv']:
                s2 = ast.bv(1 << i % 7, 8)

            r1 = op(s1, s2)
            if r1.evaluate() != 0:
                stop = True

        stop = False
        while not stop:
            s3 = ast.bv(randrange(0x100, 0x10000), 16)
            s4 = ast.bv(randrange(0x100, 0x10000), 16)

            # Special case for div, we need small number
            if name in ['bvsdiv', 'bvudiv']:
                s4 = ast.bv(1 << i, 16)

            r2 = op(s3, s4)
            if r2.evaluate() != 0:
                stop = True

        stop = False
        while not stop:
            s5 = ast.bv(randrange(0x10000, 0x100000000), 32)
            s6 = ast.bv(randrange(0x10000, 0x100000000), 32)

            # Special case for div, we need small number
            if name in ['bvsdiv', 'bvudiv']:
                s6 = ast.bv(1 << i, 32)

            r3 = op(s5, s6)
            if r3.evaluate() != 0:
                stop = True

        stop = False
        while not stop:
            s7 = ast.bv(randrange(0x100000000, 0x10000000000000000), 64)
            s8 = ast.bv(randrange(0x100000000, 0x10000000000000000), 64)

            # Special case for div, we need small number
            if name in ['bvsdiv', 'bvudiv']:
                s8 = ast.bv(1 << i, 64)

            r4 = op(s7, s8)
            if r4.evaluate() != 0:
                stop = True

        print('            OracleEntry(8, 0x%02x, 0x%02x, 0x%02x), OracleEntry(16, 0x%04x, 0x%04x, 0x%04x), OracleEntry(32, 0x%08x, 0x%08x, 0x%08x), OracleEntry(64, 0x%016x, 0x%016x, 0x%016x),'
            % (s1.evaluate(), s2.evaluate(), r1.evaluate(), s3.evaluate(), s4.evaluate(), r2.evaluate(), s5.evaluate(), s6.evaluate(), r3.evaluate(), s7.evaluate(), s8.evaluate(), r4.evaluate())
        )
    print('          }')
    print('        },')
    return


def main():
    print('//! \\file')
    print('/*')
    print('**  Copyright (C) - Triton')
    print('**')
    print('**  This program is under the terms of the Apache License 2.0.')
    print('*/')
    print('')
    print('#include <array>')
    print('#include <deque>')
    print('#include <map>')
    print('')
    print('#include <triton/astEnums.hpp>')
    print('#include <triton/oracleEntry.hpp>')
    print('')
    print('')
    print('')
    print('namespace triton {')
    print('  namespace engines {')
    print('    namespace synthesis {')
    print('')
    print('      //! The oracle table. Each entry is an OracleEntry object.')
    print('      /*! \\brief Entry: <bits> <x value> <y value> <result> <operator> */')
    print('      std::map<triton::ast::ast_e, std::array<OracleEntry, 40>> oracleTable = {')
    for op in binary_operators:
        gen_binary_operator(op)
    print('      };\n')
    print('    }; /* synthesis namespace */')
    print('  }; /* engines namespace */')
    print('}; /* triton namespace */')
    return 0


if __name__ == '__main__':
    sys.exit(main())
