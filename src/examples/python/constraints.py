#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from triton import TritonContext, ARCH, Instruction


# Constraint using AST form
def test1():
    Triton = TritonContext()
    Triton.setArchitecture(ARCH.X86)
    astCtxt = Triton.getAstContext()

    x = Triton.newSymbolicVariable(32)
    c = astCtxt.equal(
            astCtxt.bvsub(
                astCtxt.bvxor(
                    astCtxt.variable(x),
                    astCtxt.bv(0x40, 32)
                ),
                astCtxt.bv(1, 32)
            ),
            astCtxt.bv(0x10, 32)
        )
    print 'Test 1:', Triton.getModel(c)[0]

    return

# Constraint using AST operator overloading
def test2():
    Triton = TritonContext()
    Triton.setArchitecture(ARCH.X86)
    astCtxt = Triton.getAstContext()

    x = Triton.newSymbolicVariable(32)
    c = ((astCtxt.variable(x) ^ 0x40) - 1 == 0x10)
    print 'Test 2:', Triton.getModel(c)[0]

    return

# Logical conjunction constraints using AST operator overloading
def test3():
    Triton = TritonContext()
    Triton.setArchitecture(ARCH.X86)
    astCtxt = Triton.getAstContext()

    x = Triton.newSymbolicVariable(8)
    c = astCtxt.land([
            astCtxt.variable(x) * astCtxt.variable(x) - 1 == 0x20,
            astCtxt.variable(x) != 0x11
        ])
    print 'Test 3:', Triton.getModel(c)[0]

    return

# Several models
def test4():
    Triton = TritonContext()
    Triton.setArchitecture(ARCH.X86)
    astCtxt = Triton.getAstContext()

    x = Triton.newSymbolicVariable(8)
    c = astCtxt.variable(x) * astCtxt.variable(x) - 1 == 0x20
    print 'Test 4:', Triton.getModels(c, 10)

    return

# From instruction
def test5():
    Triton = TritonContext()
    Triton.setArchitecture(ARCH.X86)
    astCtxt = Triton.getAstContext()

    # rax is now symbolic
    Triton.convertRegisterToSymbolicVariable(Triton.registers.eax)

    # process instruction
    Triton.processing(Instruction("\x83\xc0\x07")) # add eax, 0x7

    # get rax ast
    eaxAst = Triton.getAstFromId(Triton.getSymbolicRegisterId(Triton.registers.eax))

    # constraint
    c = eaxAst ^ 0x11223344 == 0xdeadbeaf

    print 'Test 5:', Triton.getModel(c)[0]

    return

if __name__ == '__main__':
    test1()
    test2()
    test3()
    test4()
    test5()
