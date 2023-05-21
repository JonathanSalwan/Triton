#!/usr/bin/env python3
# coding: utf-8
"""Test AST representation."""

import unittest

from triton import TritonContext, ARCH, AST_REPRESENTATION, VERSION


smtlifting = """(define-fun bswap8 ((value (_ BitVec 8))) (_ BitVec 8)
    value
)

(define-fun bswap16 ((value (_ BitVec 16))) (_ BitVec 16)
  (bvor
    (bvshl
      (bvand value (_ bv255 16))
      (_ bv8 16)
    )
    (bvand (bvlshr value (_ bv8 16)) (_ bv255 16))
  )
)

(define-fun bswap32 ((value (_ BitVec 32))) (_ BitVec 32)
  (bvor
    (bvshl
      (bvor
        (bvshl
          (bvor
            (bvshl
              (bvand value (_ bv255 32))
              (_ bv8 32)
            )
            (bvand (bvlshr value (_ bv8 32)) (_ bv255 32))
          )
          (_ bv8 32)
        )
        (bvand (bvlshr value (_ bv16 32)) (_ bv255 32))
      )
      (_ bv8 32)
    )
    (bvand (bvlshr value (_ bv24 32)) (_ bv255 32))
  )
)

(define-fun bswap64 ((value (_ BitVec 64))) (_ BitVec 64)
  (bvor
    (bvshl
      (bvor
        (bvshl
          (bvor
            (bvshl
              (bvor
                (bvshl
                  (bvor
                    (bvshl
                      (bvor
                        (bvshl
                          (bvor
                            (bvshl
                              (bvand value (_ bv255 64))
                              (_ bv8 64)
                            )
                            (bvand (bvlshr value (_ bv8 64)) (_ bv255 64))
                          )
                          (_ bv8 64)
                        )
                        (bvand (bvlshr value (_ bv16 64)) (_ bv255 64))
                      )
                      (_ bv8 64)
                    )
                    (bvand (bvlshr value (_ bv24 64)) (_ bv255 64))
                  )
                  (_ bv8 64)
                )
                (bvand (bvlshr value (_ bv32 64)) (_ bv255 64))
              )
              (_ bv8 64)
            )
            (bvand (bvlshr value (_ bv40 64)) (_ bv255 64))
          )
          (_ bv8 64)
        )
        (bvand (bvlshr value (_ bv48 64)) (_ bv255 64))
      )
      (_ bv8 64)
    )
    (bvand (bvlshr value (_ bv56 64)) (_ bv255 64))
  )
)

(declare-fun SymVar_0 () (_ BitVec 8))
(declare-fun SymVar_1 () (_ BitVec 8))
(define-fun ref!0 () (_ BitVec 8) (bvadd SymVar_0 SymVar_1)) ; ref test
"""

pythonlifting = """def select(mem, index):
    return mem[index]

def store(mem, index, value):
    mem[index] = value
    return mem

def sx(bits, value):
    sign_bit = 1 << (bits - 1)
    return (value & (sign_bit - 1)) - (value & sign_bit)

def rol(value, rot, bits):
    return ((value << rot) | (value >> (bits - rot))) & ((0b1 << bits) - 1)

def ror(value, rot, bits):
    return ((value >> rot) | (value << (bits - rot))) & ((0b1 << bits) - 1)

def forall(variables, expr):
    return True

def bswap(value, size):
    v = value & 0xff
    for index in range(8, size, 8):
        v <<= 8
        v |= (value >> index) & 0xff
    return v

SymVar_0 = int(input())
SymVar_1 = int(input())
ref_0 = ((SymVar_0 + SymVar_1) & 0xff) # ref test
"""


class TestAstRepresentation(unittest.TestCase):

    """Testing the AST Representation."""

    def setUp(self):
        """Define the arch."""
        self.ctx = TritonContext(ARCH.X86_64)
        self.ast = self.ctx.getAstContext()

        self.v1  = self.ast.variable(self.ctx.newSymbolicVariable(8))
        self.v2  = self.ast.variable(self.ctx.newSymbolicVariable(8))
        self.ref = self.ctx.newSymbolicExpression(self.v1 + self.v2, "ref test")

        # Default
        self.assertEqual(self.ctx.getAstRepresentationMode(), AST_REPRESENTATION.SMT)

        self.node = [
            # Overloaded operators                           # SMT                                                           # Python
            ((self.v1 & self.v2),                            "(bvand SymVar_0 SymVar_1)",                                    "(SymVar_0 & SymVar_1)"),
            ((self.v1 + self.v2),                            "(bvadd SymVar_0 SymVar_1)",                                    "((SymVar_0 + SymVar_1) & 0xFF)"),
            ((self.v1 - self.v2),                            "(bvsub SymVar_0 SymVar_1)",                                    "((SymVar_0 - SymVar_1) & 0xFF)"),
            ((self.v1 ^ self.v2),                            "(bvxor SymVar_0 SymVar_1)",                                    "(SymVar_0 ^ SymVar_1)"),
            ((self.v1 | self.v2),                            "(bvor SymVar_0 SymVar_1)",                                     "(SymVar_0 | SymVar_1)"),
            ((self.v1 * self.v2),                            "(bvmul SymVar_0 SymVar_1)",                                    "((SymVar_0 * SymVar_1) & 0xFF)"),
            ((self.v1 / self.v2),                            "(bvudiv SymVar_0 SymVar_1)",                                   "(SymVar_0 / SymVar_1)"),
            ((self.v1 % self.v2),                            "(bvurem SymVar_0 SymVar_1)",                                   "(SymVar_0 % SymVar_1)"),
            ((self.v1 << self.v2),                           "(bvshl SymVar_0 SymVar_1)",                                    "((SymVar_0 << SymVar_1) & 0xFF)"),
            ((self.v1 >> self.v2),                           "(bvlshr SymVar_0 SymVar_1)",                                   "(SymVar_0 >> SymVar_1)"),
            ((~self.v1),                                     "(bvnot SymVar_0)",                                             "(~(SymVar_0) & 0xFF)"),
            ((-self.v1),                                     "(bvneg SymVar_0)",                                             "(-(symvar_0) & 0xff)"),
            ((self.v1 == self.v2),                           "(= SymVar_0 SymVar_1)",                                        "(SymVar_0 == SymVar_1)"),
            ((self.v1 != self.v2),                           "(not (= SymVar_0 SymVar_1))",                                  "not (SymVar_0 == SymVar_1)"),
            ((self.v1 <= self.v2),                           "(bvule SymVar_0 SymVar_1)",                                    "(SymVar_0 <= SymVar_1)"),
            ((self.v1 >= self.v2),                           "(bvuge SymVar_0 SymVar_1)",                                    "(SymVar_0 >= SymVar_1)"),
            ((self.v1 < self.v2),                            "(bvult SymVar_0 SymVar_1)",                                    "(SymVar_0 < SymVar_1)"),
            ((self.v1 > self.v2),                            "(bvugt SymVar_0 SymVar_1)",                                    "(SymVar_0 > SymVar_1)"),

            # AST api                                        # SMT                                                           # Python
            (self.ast.assert_(self.v1 == 0),                 "(assert (= SymVar_0 (_ bv0 8)))",                              "assert((SymVar_0 == 0x0))"),
            (self.ast.bswap(self.v1),                        "(bswap8 SymVar_0)",                                            "bswap(SymVar_0, 8)"),
            (self.ast.bv(2, 8),                              "(_ bv2 8)",                                                    "0x2"),
            (self.ast.bvashr(self.v1, self.v2),              "(bvashr SymVar_0 SymVar_1)",                                   "(SymVar_0 >> SymVar_1)"),
            (self.ast.bvfalse(),                             "(_ bv0 1)",                                                    "0x0"),
            (self.ast.bvnand(self.v1, self.v2),              "(bvnand SymVar_0 SymVar_1)",                                   "(~(SymVar_0 & SymVar_1) & 0xFF)"),
            (self.ast.bvnor(self.v1, self.v2),               "(bvnor SymVar_0 SymVar_1)",                                    "(~(SymVar_0 | SymVar_1) & 0xFF)"),
            (self.ast.bvrol(self.v1, self.ast.bv(3, 8)),     "((_ rotate_left 3) SymVar_0)",                                 "rol(SymVar_0, 0x3, 8)"),
            (self.ast.bvror(self.v2, self.ast.bv(2, 8)),     "((_ rotate_right 2) SymVar_1)",                                "ror(SymVar_1, 0x2, 8)"),
            (self.ast.bvsdiv(self.v1, self.v2),              "(bvsdiv SymVar_0 SymVar_1)",                                   "(SymVar_0 / SymVar_1)"),
            (self.ast.bvsge(self.v1, self.v2),               "(bvsge SymVar_0 SymVar_1)",                                    "(SymVar_0 >= SymVar_1)"),
            (self.ast.bvsgt(self.v1, self.v2),               "(bvsgt SymVar_0 SymVar_1)",                                    "(SymVar_0 > SymVar_1)"),
            (self.ast.bvsle(self.v1, self.v2),               "(bvsle SymVar_0 SymVar_1)",                                    "(SymVar_0 <= SymVar_1)"),
            (self.ast.bvslt(self.v1, self.v2),               "(bvslt SymVar_0 SymVar_1)",                                    "(SymVar_0 < SymVar_1)"),
            (self.ast.bvsmod(self.v1, self.v2),              "(bvsmod SymVar_0 SymVar_1)",                                   "(SymVar_0 % SymVar_1)"),
            (self.ast.bvsrem(self.v1, self.v2),              "(bvsrem SymVar_0 SymVar_1)",                                   "(SymVar_0 % SymVar_1)"),
            (self.ast.bvtrue(),                              "(_ bv1 1)",                                                    "0x1"),
            (self.ast.bvurem(self.v1, self.v2),              "(bvurem SymVar_0 SymVar_1)",                                   "(SymVar_0 % SymVar_1)"),
            (self.ast.bvxnor(self.v1, self.v2),              "(bvxnor SymVar_0 SymVar_1)",                                   "(~(SymVar_0 ^ SymVar_1) & 0xFF)"),
            (self.ast.compound([self.v1, self.v2]),          "SymVar_0\nSymVar_1",                                           "SymVar_0\nSymVar_1"),
            (self.ast.concat([self.v1, self.v2]),            "(concat SymVar_0 SymVar_1)",                                   "((SymVar_0) << 8 | SymVar_1)"),
            (self.ast.declare(self.v1),                      "(declare-fun SymVar_0 () (_ BitVec 8))",                       "SymVar_0 = int(input())"),
            (self.ast.distinct(self.v1, self.v2),            "(distinct SymVar_0 SymVar_1)",                                 "(SymVar_0 != SymVar_1)"),
            (self.ast.equal(self.v1, self.v2),               "(= SymVar_0 SymVar_1)",                                        "(SymVar_0 == SymVar_1)"),
            (self.ast.extract(4, 2, self.v1),                "((_ extract 4 2) SymVar_0)",                                   "((SymVar_0 >> 2) & 0x7)"),
            (self.ast.extract(6, 0, self.v1),                "((_ extract 6 0) SymVar_0)",                                   "(SymVar_0 & 0x7F)"),
            (self.ast.extract(7, 0, self.v1),                "SymVar_0",                                                     "SymVar_0"),
            (self.ast.iff(self.v1 == 1, self.v2 == 2),       "(iff (= SymVar_0 (_ bv1 8)) (= SymVar_1 (_ bv2 8)))",          "((SymVar_0 == 0x1) and (SymVar_1 == 0x2)) or (not (SymVar_0 == 0x1) and not (SymVar_1 == 0x2))"),
            (self.ast.ite(self.v1 == 1, self.v1, self.v2),   "(ite (= SymVar_0 (_ bv1 8)) SymVar_0 SymVar_1)",               "(SymVar_0 if (SymVar_0 == 0x1) else SymVar_1)"),
            (self.ast.land([self.v1 == 1, self.v2 == 2]),    "(and (= SymVar_0 (_ bv1 8)) (= SymVar_1 (_ bv2 8)))",          "((SymVar_0 == 0x1) and (SymVar_1 == 0x2))"),
            (self.ast.let("alias", self.v1, self.v2),        "(let ((alias SymVar_0)) SymVar_1)",                            "SymVar_1"),
            (self.ast.lnot(self.v1 == 0),                    "(not (= SymVar_0 (_ bv0 8)))",                                 "not (SymVar_0 == 0x0)"),
            (self.ast.lor([self.v1 >= 0, self.v2 <= 10]),    "(or (bvuge SymVar_0 (_ bv0 8)) (bvule SymVar_1 (_ bv10 8)))",  "((SymVar_0 >= 0x0) or (SymVar_1 <= 0xA))"),
            (self.ast.lxor([self.v1 >= 0, self.v2 <= 10]),   "(xor (bvuge SymVar_0 (_ bv0 8)) (bvule SymVar_1 (_ bv10 8)))", "(bool((SymVar_0 >= 0x0)) != bool((SymVar_1 <= 0xA)))"),
            (self.ast.reference(self.ref),                   "ref!0",                                                        "ref_0"),
            (self.ast.string("test"),                        "test",                                                         "test"),
            (self.ast.sx(8, self.v1),                        "((_ sign_extend 8) SymVar_0)",                                 "sx(0x8, SymVar_0)"),
            (self.ast.zx(8, self.v1),                        "((_ zero_extend 8) SymVar_0)",                                 "SymVar_0"),
            (self.ast.forall([self.v1], 1 == self.v1),       "(forall ((SymVar_0 (_ BitVec 8))) (= SymVar_0 (_ bv1 8)))",    "forall([symvar_0], (symvar_0 == 0x1))"),
        ]

    def test_smt_representation(self):
        self.ctx.setAstRepresentationMode(AST_REPRESENTATION.SMT)
        self.assertEqual(self.ctx.getAstRepresentationMode(), AST_REPRESENTATION.SMT)
        for n in self.node:
            self.assertEqual(str(n[0]), n[1])

    def test_python_representation(self):
        self.ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
        self.assertEqual(self.ctx.getAstRepresentationMode(), AST_REPRESENTATION.PYTHON)
        for n in self.node:
            # Note: lower() in order to handle boost-1.55 (from travis) and boost-1.71 (from an up-to-date machine)
            self.assertEqual(str(n[0]).lower(), n[2].lower())

    def test_lifting(self):
        self.assertEqual(self.ctx.liftToSMT(self.ref), smtlifting)
        self.assertEqual(self.ctx.liftToPython(self.ref), pythonlifting)

        nodes = [
            (self.v1 & self.v2),
            (self.v1 + self.v2),
            (self.v1 - self.v2),
            (self.v1 ^ self.v2),
            (self.v1 | self.v2),
            (self.v1 * self.v2),
            (self.v1 / self.v2),
            (self.v1 % self.v2),
            (self.v1 << self.v2),
            (self.v1 >> self.v2),
            (~self.v1),
            (-self.v1),
            (self.v1 == self.v2),
            (self.v1 != self.v2),
            (self.v1 <= self.v2),
            (self.v1 >= self.v2),
            (self.v1 < self.v2),
            (self.v1 > self.v2),
            self.ast.bswap(self.ast.bv(0x1122, 16)),
            self.ast.bv(2, 8),
            self.ast.bvashr(self.v1, self.v2),
            self.ast.bvnand(self.v1, self.v2),
            self.ast.bvnor(self.v1, self.v2),
            self.ast.bvrol(self.v1, self.ast.bv(3, 8)),
            self.ast.bvror(self.v2, self.ast.bv(2, 8)),
            self.ast.bvsdiv(self.v1, self.v2),
            self.ast.bvsge(self.v1, self.v2),
            self.ast.bvsgt(self.v1, self.v2),
            self.ast.bvsle(self.v1, self.v2),
            self.ast.bvslt(self.v1, self.v2),
            self.ast.bvsmod(self.v1, self.v2),
            self.ast.bvsrem(self.v1, self.v2),
            self.ast.bvurem(self.v1, self.v2),
            self.ast.bvxnor(self.v1, self.v2),
            self.ast.concat([self.v1, self.v2]),
            self.ast.distinct(self.v1, self.v2),
            self.ast.equal(self.v1, self.v2),
            self.ast.extract(4, 2, self.v1),
            self.ast.extract(6, 0, self.v1),
            self.ast.extract(7, 0, self.v1),
            self.ast.ite(self.v1 == 1, self.v1, self.v2),
            self.ast.land([self.v1 == 1, self.v2 == 2]),
            self.ast.lnot(self.v1 == 0),
            self.ast.lor([self.v1 >= 0, self.v2 <= 10]),
            self.ast.lxor([self.v1 >= 0, self.v2 <= 10]),
            self.ast.reference(self.ref),
            self.ast.sx(8, self.v1),
            self.ast.zx(8, self.v1),
        ]

        for n in nodes:
            # LLVM
            if VERSION.LLVM_INTERFACE is True:
                self.assertNotEqual(len(self.ctx.liftToLLVM(n, fname="test", optimize=True)), 0)
            # Dot
            self.assertNotEqual(len(self.ctx.liftToDot(n)), 0)
