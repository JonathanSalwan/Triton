#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys
from triton import *


# Constraint using AST form
def test1():
    setArchitecture(ARCH.X86)

    x = newSymbolicVariable(32)
    c = ast.assert_(
            ast.equal(
                ast.bvsub(
                    ast.bvxor(
                        ast.variable(x),
                        ast.bv(0x40, 32)
                    ),
                    ast.bv(1, 32)
                ),
                ast.bv(0x10, 32)
            )
        )
    print 'Test 1:', getModel(c)[0]

    return

# Constraint using AST operator overloading
def test2():
    setArchitecture(ARCH.X86)

    x = newSymbolicVariable(32)
    c = ast.assert_(
            (ast.variable(x) ^ 0x40) - 1 == 0x10
        )
    print 'Test 2:', getModel(c)[0]

    return

# Logical conjunction constraints using AST operator overloading
def test3():
    setArchitecture(ARCH.X86)

    x = newSymbolicVariable(8)
    c = ast.assert_(
            ast.land(
                ast.variable(x) * ast.variable(x) - 1 == 0x20,
                ast.variable(x) != 0x11
            )
        )
    print 'Test 3:', getModel(c)[0]

    return

# Several models
def test4():
    setArchitecture(ARCH.X86)

    x = newSymbolicVariable(8)
    c = ast.assert_(
            ast.variable(x) * ast.variable(x) - 1 == 0x20,
        )
    print 'Test 4:', getModels(c, 10)

    return

# From instruction
def test5():
    setArchitecture(ARCH.X86)

    # rax is now symbolic
    convertRegisterToSymbolicVariable(REG.EAX)

    # process instruction
    processing(Instruction("\x83\xc0\x07")) # add eax, 0x7

    # get rax ast
    eaxAst = getAstFromId(getSymbolicRegisterId(REG.EAX))

    # constraint
    c = ast.assert_(
            eaxAst ^ 0x11223344 == 0xdeadbeaf
        )

    print 'Test 5:', getModel(c)[0]

    return

if __name__ == '__main__':
    test1()
    test2()
    test3()
    test4()
    test5()
