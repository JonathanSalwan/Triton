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
from random import randrange

HOW_BIG_IS_THE_TABLE = 10

ctx = TritonContext(ARCH.X86_64) # does not matter of the architecture, we just need an AstContext
ast = ctx.getAstContext()


unary_operators = [
    [ast.bvneg,     'bvneg',  'triton::ast::BVNEG_NODE'],
    [ast.bvnot,     'bvnot',  'triton::ast::BVNOT_NODE'],
    [ast.bswap,     'bswap',  'triton::ast::BSWAP_NODE'],
]


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


def gen_unary_operator():
    for op, name, enum in unary_operators:
        print('          /* %s synthesis */' %(name))
        print('          {')
        print('            %s, {' %(enum))
        for i in range(HOW_BIG_IS_THE_TABLE):
            stop = False
            while not stop:
                s1 = ast.bv(randrange(1, 0x100), 8)
                r1 = op(s1)
                if r1.evaluate() != 0:
                    stop = True

            stop = False
            while not stop:
                s2 = ast.bv(randrange(0x100, 0x10000), 16)
                r2 = op(s2)
                if r2.evaluate() != 0:
                    stop = True

            stop = False
            while not stop:
                s3 = ast.bv(randrange(0x10000, 0x100000000), 32)
                r3 = op(s3)
                if r3.evaluate() != 0:
                    stop = True

            stop = False
            while not stop:
                s4 = ast.bv(randrange(0x100000000, 0x10000000000000000), 64)
                r4 = op(s4)
                if r4.evaluate() != 0:
                    stop = True

            print('              UnaryEntry(8, 0x%02x, 0x%02x), UnaryEntry(16, 0x%04x, 0x%04x), UnaryEntry(32, 0x%08x, 0x%08x), UnaryEntry(64, 0x%016x, 0x%016x),'
                % (s1.evaluate(), r1.evaluate(), s2.evaluate(), r2.evaluate(), s3.evaluate(), r3.evaluate(), s4.evaluate(), r4.evaluate())
            )
        print('            }')
        print('          },')
    return


def gen_binary_operator():
    for op, name, enum in binary_operators:
        print('          /* %s synthesis */' %(name))
        print('          {')
        print('            %s, {' %(enum))
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

            print('              BinaryEntry(8, 0x%02x, 0x%02x, 0x%02x), BinaryEntry(16, 0x%04x, 0x%04x, 0x%04x), BinaryEntry(32, 0x%08x, 0x%08x, 0x%08x), BinaryEntry(64, 0x%016x, 0x%016x, 0x%016x),'
                % (s1.evaluate(), s2.evaluate(), r1.evaluate(), s3.evaluate(), s4.evaluate(), r2.evaluate(), s5.evaluate(), s6.evaluate(), r3.evaluate(), s7.evaluate(), s8.evaluate(), r4.evaluate())
            )
        print('            }')
        print('          },')
    return


def gen_trinary_operator():
    vk = {0: 'x', 1: 'y'}
    for op1, name1, enum1 in binary_operators:
        for op2, name2, enum2 in binary_operators:
            for s1 in [0, 1]:
                for s2 in [0, 1]:
                    for s3 in [0, 1]:

                        # Skip expressions that contain only one variable
                        if s1 == s2 == s3:
                            continue

                        # Skip those expressions
                        subset = ['bvsdiv', 'bvsmod', 'bvsrem', 'bvudiv', 'bvurem']
                        if name1 in subset or name2 in subset:
                            continue

                        pp = '%s(%s(%c, %c), %c)' % (name1, name2, vk[s1], vk[s2], vk[s3])
                        print('          /* %s synthesis */' %(pp))
                        print('          {')
                        print('            OpEncoding<2>({%s, %s}, {%d, %d, %d}), {' % (enum1, enum2, s1, s2, s3))
                        for i in range(HOW_BIG_IS_THE_TABLE):
                            v1 = {}
                            v2 = {}
                            v3 = {}
                            v4 = {}
                            try_hard = 0
                            stop = False
                            while not stop:
                                v1[0] = ast.bv(randrange(1, 0x100), 8)
                                v1[1] = ast.bv(randrange(1, 0x100), 8)
                                r1 = op1(op2(v1[s1], v1[s2]), v1[s3])
                                if r1.evaluate() != 0 or try_hard == 1000:
                                    stop = True
                                try_hard += 1

                            try_hard = 0
                            stop = False
                            while not stop:
                                v2[0] = ast.bv(randrange(0x100, 0x10000), 16)
                                v2[1] = ast.bv(randrange(0x100, 0x10000), 16)
                                r2 = op1(op2(v2[s1], v2[s2]), v2[s3])
                                if r2.evaluate() != 0 or try_hard == 1000:
                                    stop = True
                                try_hard += 1

                            try_hard = 0
                            stop = False
                            while not stop:
                                v3[0] = ast.bv(randrange(0x10000, 0x100000000), 32)
                                v3[1] = ast.bv(randrange(0x10000, 0x100000000), 32)
                                r3 = op1(op2(v3[s1], v3[s2]), v3[s3])
                                if r3.evaluate() != 0 or try_hard == 1000:
                                    stop = True
                                try_hard += 1

                            try_hard = 0
                            stop = False
                            while not stop:
                                v4[0] = ast.bv(randrange(0x100000000, 0x10000000000000000), 64)
                                v4[1] = ast.bv(randrange(0x100000000, 0x10000000000000000), 64)
                                r4 = op1(op2(v4[s1], v4[s2]), v4[s3])
                                if r4.evaluate() != 0 or try_hard == 1000:
                                    stop = True
                                try_hard += 1

                            print('              BinaryEntry(8, 0x%02x, 0x%02x, 0x%02x), BinaryEntry(16, 0x%04x, 0x%04x, 0x%04x), BinaryEntry(32, 0x%08x, 0x%08x, 0x%08x), BinaryEntry(64, 0x%016x, 0x%016x, 0x%016x),'
                                % (v1[0].evaluate(), v1[1].evaluate(), r1.evaluate(), v2[0].evaluate(), v2[1].evaluate(), r2.evaluate(), v3[0].evaluate(), v3[1].evaluate(), r3.evaluate(), v4[0].evaluate(), v4[1].evaluate(), r4.evaluate())
                            )
                        print('            }')
                        print('          },')
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
    print('      namespace oracles {')
    print('')
    print('        //! The oracle table for unary operators. Each entry is a UnaryEntry object.')
    print('        /*! \\brief Entry: <bits> <x value> <result> <operator> */')
    print('        std::map<triton::ast::ast_e, std::array<UnaryEntry, 40>> unopTable = {')
    gen_unary_operator()
    print('        };')
    print('')
    print('')
    print('        //! The oracle table for binary operators. Each entry is a BinaryEntry object.')
    print('        /*! \\brief Entry: <bits> <x value> <y value> <result> <operator> */')
    print('        std::map<triton::ast::ast_e, std::array<BinaryEntry, 40>> binopTable = {')
    gen_binary_operator()
    print('        };')
    print('')
    #print('')
    #print('        //! The oracle table for trinary operators. Each entry is a BinaryEntry object.')
    #print('        /*! \\brief Entry: <bits> <x value> <y value> <result> <operator> */')
    #print('        std::map<OpEncoding<2>, std::array<BinaryEntry, 40>> triopTable = {')
    #gen_trinary_operator()
    #print('        };')
    #print('')
    print('      }; /* oracles namespace */')
    print('    }; /* synthesis namespace */')
    print('  }; /* engines namespace */')
    print('}; /* triton namespace */')
    return 0


if __name__ == '__main__':
    sys.exit(main())
