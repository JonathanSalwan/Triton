#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
##  This program is under the terms of the BSD License.
##  Jonathan Salwan - 2020-03-18
##
##  Generate the oracle table for obfuscated expressions synthesis
##
##  Output: src/libtriton/engines/synthesis/oracleTable.cpp
##

import sys
import operator

from ctypes import c_uint8, c_uint16, c_uint32, c_uint64
from random import randrange

HOW_BIG_IS_THE_TABLE = 10


binary_operators = [
    [operator.__add__, 'bvadd', 'triton::ast::BVADD_NODE'],
    [operator.__sub__, 'bvsub', 'triton::ast::BVSUB_NODE'],
    [operator.__xor__, 'bvxor', 'triton::ast::BVXOR_NODE'],
    [operator.__or__,  'bvor',  'triton::ast::BVOR_NODE'],
    [operator.__and__, 'bvand', 'triton::ast::BVAND_NODE'],
    [operator.__mul__, 'bvmul', 'triton::ast::BVMUL_NODE'],
]


def gen_binary_operator(binary_op):
    op, name, enum = binary_op
    print('        /* %s synthesis */' %(name))
    print('        {')
    print('          %s, {' %(enum))
    for i in range(HOW_BIG_IS_THE_TABLE):
        s1 = c_uint8(randrange(1, 0x100))
        s2 = c_uint8(randrange(1, 0x100))
        r1 = c_uint8(op(s1.value, s2.value))

        s3 = c_uint16(randrange(0x100, 0x10000))
        s4 = c_uint16(randrange(0x100, 0x10000))
        r2 = c_uint16(op(s3.value, s4.value))

        s5 = c_uint32(randrange(0x10000, 0x100000000))
        s6 = c_uint32(randrange(0x10000, 0x100000000))
        r3 = c_uint32(op(s5.value, s6.value))

        s7 = c_uint64(randrange(0x100000000, 0x10000000000000000))
        s8 = c_uint64(randrange(0x100000000, 0x10000000000000000))
        r4 = c_uint64(op(s7.value, s8.value))

        print('            OracleEntry(8, 0x%02x, 0x%02x, 0x%02x), OracleEntry(16, 0x%04x, 0x%04x, 0x%04x), OracleEntry(32, 0x%08x, 0x%08x, 0x%08x), OracleEntry(64, 0x%016x, 0x%016x, 0x%016x),'
            % (s1.value, s2.value, r1.value, s3.value, s4.value, r2.value, s5.value, s6.value, r3.value, s7.value, s8.value, r4.value)
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
