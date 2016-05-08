#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys

from triton import *
from ast    import *

def test_1():
    setArchitecture(ARCH.X86_64)
    tests = [
        bvsub(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvsub(bv(0x12345678, 32), bv(0, 32)),
        bvsub(bv(0x12345678, 32), bv(1, 32)),
        bvsub(bv(0x12345678, 32), bv(2, 32)),
        bvsub(bv(0x12345678, 32), bv(3, 32)),
        bvsub(bv(0x12345678, 32), bv(32, 32)),
        bvsub(bv(0x12345678, 32), bv(64, 32)),
        bvsub(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvsub(bv(0xf2345678, 32), bv(0, 32)),
        bvsub(bv(0xf2345678, 32), bv(1, 32)),
        bvsub(bv(0xf2345678, 32), bv(2, 32)),
        bvsub(bv(0xf2345678, 32), bv(3, 32)),
        bvsub(bv(0xf2345678, 32), bv(32, 32)),
        bvsub(bv(0xf2345678, 32), bv(64, 32)),
        bvsub(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvadd(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvadd(bv(0x12345678, 32), bv(0, 32)),
        bvadd(bv(0x12345678, 32), bv(1, 32)),
        bvadd(bv(0x12345678, 32), bv(2, 32)),
        bvadd(bv(0x12345678, 32), bv(3, 32)),
        bvadd(bv(0x12345678, 32), bv(32, 32)),
        bvadd(bv(0x12345678, 32), bv(64, 32)),
        bvadd(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvadd(bv(0xf2345678, 32), bv(0, 32)),
        bvadd(bv(0xf2345678, 32), bv(1, 32)),
        bvadd(bv(0xf2345678, 32), bv(2, 32)),
        bvadd(bv(0xf2345678, 32), bv(3, 32)),
        bvadd(bv(0xf2345678, 32), bv(32, 32)),
        bvadd(bv(0xf2345678, 32), bv(64, 32)),
        bvadd(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvxor(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvxor(bv(0x12345678, 32), bv(0, 32)),
        bvxor(bv(0x12345678, 32), bv(1, 32)),
        bvxor(bv(0x12345678, 32), bv(2, 32)),
        bvxor(bv(0x12345678, 32), bv(3, 32)),
        bvxor(bv(0x12345678, 32), bv(32, 32)),
        bvxor(bv(0x12345678, 32), bv(64, 32)),
        bvxor(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvxor(bv(0xf2345678, 32), bv(0, 32)),
        bvxor(bv(0xf2345678, 32), bv(1, 32)),
        bvxor(bv(0xf2345678, 32), bv(2, 32)),
        bvxor(bv(0xf2345678, 32), bv(3, 32)),
        bvxor(bv(0xf2345678, 32), bv(32, 32)),
        bvxor(bv(0xf2345678, 32), bv(64, 32)),
        bvxor(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvor(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvor(bv(0x12345678, 32), bv(0, 32)),
        bvor(bv(0x12345678, 32), bv(1, 32)),
        bvor(bv(0x12345678, 32), bv(2, 32)),
        bvor(bv(0x12345678, 32), bv(3, 32)),
        bvor(bv(0x12345678, 32), bv(32, 32)),
        bvor(bv(0x12345678, 32), bv(64, 32)),
        bvor(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvor(bv(0xf2345678, 32), bv(0, 32)),
        bvor(bv(0xf2345678, 32), bv(1, 32)),
        bvor(bv(0xf2345678, 32), bv(2, 32)),
        bvor(bv(0xf2345678, 32), bv(3, 32)),
        bvor(bv(0xf2345678, 32), bv(32, 32)),
        bvor(bv(0xf2345678, 32), bv(64, 32)),
        bvor(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvand(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvand(bv(0x12345678, 32), bv(0, 32)),
        bvand(bv(0x12345678, 32), bv(1, 32)),
        bvand(bv(0x12345678, 32), bv(2, 32)),
        bvand(bv(0x12345678, 32), bv(3, 32)),
        bvand(bv(0x12345678, 32), bv(32, 32)),
        bvand(bv(0x12345678, 32), bv(64, 32)),
        bvand(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvand(bv(0xf2345678, 32), bv(0, 32)),
        bvand(bv(0xf2345678, 32), bv(1, 32)),
        bvand(bv(0xf2345678, 32), bv(2, 32)),
        bvand(bv(0xf2345678, 32), bv(3, 32)),
        bvand(bv(0xf2345678, 32), bv(32, 32)),
        bvand(bv(0xf2345678, 32), bv(64, 32)),
        bvand(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvnand(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvnand(bv(0x12345678, 32), bv(0, 32)),
        bvnand(bv(0x12345678, 32), bv(1, 32)),
        bvnand(bv(0x12345678, 32), bv(2, 32)),
        bvnand(bv(0x12345678, 32), bv(3, 32)),
        bvnand(bv(0x12345678, 32), bv(32, 32)),
        bvnand(bv(0x12345678, 32), bv(64, 32)),
        bvnand(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvnand(bv(0xf2345678, 32), bv(0, 32)),
        bvnand(bv(0xf2345678, 32), bv(1, 32)),
        bvnand(bv(0xf2345678, 32), bv(2, 32)),
        bvnand(bv(0xf2345678, 32), bv(3, 32)),
        bvnand(bv(0xf2345678, 32), bv(32, 32)),
        bvnand(bv(0xf2345678, 32), bv(64, 32)),
        bvnand(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvnor(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvnor(bv(0x12345678, 32), bv(0, 32)),
        bvnor(bv(0x12345678, 32), bv(1, 32)),
        bvnor(bv(0x12345678, 32), bv(2, 32)),
        bvnor(bv(0x12345678, 32), bv(3, 32)),
        bvnor(bv(0x12345678, 32), bv(32, 32)),
        bvnor(bv(0x12345678, 32), bv(64, 32)),
        bvnor(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvnor(bv(0xf2345678, 32), bv(0, 32)),
        bvnor(bv(0xf2345678, 32), bv(1, 32)),
        bvnor(bv(0xf2345678, 32), bv(2, 32)),
        bvnor(bv(0xf2345678, 32), bv(3, 32)),
        bvnor(bv(0xf2345678, 32), bv(32, 32)),
        bvnor(bv(0xf2345678, 32), bv(64, 32)),
        bvnor(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvxnor(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvxnor(bv(0x12345678, 32), bv(0, 32)),
        bvxnor(bv(0x12345678, 32), bv(1, 32)),
        bvxnor(bv(0x12345678, 32), bv(2, 32)),
        bvxnor(bv(0x12345678, 32), bv(3, 32)),
        bvxnor(bv(0x12345678, 32), bv(32, 32)),
        bvxnor(bv(0x12345678, 32), bv(64, 32)),
        bvxnor(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvxnor(bv(0xf2345678, 32), bv(0, 32)),
        bvxnor(bv(0xf2345678, 32), bv(1, 32)),
        bvxnor(bv(0xf2345678, 32), bv(2, 32)),
        bvxnor(bv(0xf2345678, 32), bv(3, 32)),
        bvxnor(bv(0xf2345678, 32), bv(32, 32)),
        bvxnor(bv(0xf2345678, 32), bv(64, 32)),
        bvxnor(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvmul(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvmul(bv(0x12345678, 32), bv(0, 32)),
        bvmul(bv(0x12345678, 32), bv(1, 32)),
        bvmul(bv(0x12345678, 32), bv(2, 32)),
        bvmul(bv(0x12345678, 32), bv(3, 32)),
        bvmul(bv(0x12345678, 32), bv(32, 32)),
        bvmul(bv(0x12345678, 32), bv(64, 32)),
        bvmul(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvmul(bv(0xf2345678, 32), bv(0, 32)),
        bvmul(bv(0xf2345678, 32), bv(1, 32)),
        bvmul(bv(0xf2345678, 32), bv(2, 32)),
        bvmul(bv(0xf2345678, 32), bv(3, 32)),
        bvmul(bv(0xf2345678, 32), bv(32, 32)),
        bvmul(bv(0xf2345678, 32), bv(64, 32)),
        bvmul(bv(0xf2345678, 32), bv(0x12345678, 32)),

        bvneg(bv(0x88888888, 32)),
        bvneg(bv(0x12345678, 32)),
        bvneg(bv(0x22345678, 32)),
        bvneg(bv(0x32345678, 32)),
        bvneg(bv(0x42345678, 32)),
        bvneg(bv(0x52345678, 32)),
        bvneg(bv(0x62345678, 32)),
        bvneg(bv(0x72345678, 32)),
        bvneg(bv(0x82345678, 32)),
        bvneg(bv(0x92345678, 32)),
        bvneg(bv(0xa2345678, 32)),
        bvneg(bv(0xb2345678, 32)),
        bvneg(bv(0xc2345678, 32)),
        bvneg(bv(0xd345678, 32)),
        bvneg(bv(0xe2345678, 32)),
        bvneg(bv(0xf2345678, 32)),
        bvneg(bv(0x1, 32)),
        bvneg(bv(0x2, 32)),
        bvneg(bv(0x3, 32)),
        bvneg(bv(0x4, 32)),
        bvneg(bv(0x5, 32)),
        bvneg(bv(0x6, 32)),
        bvneg(bv(0xa, 32)),
        bvneg(bv(0xe, 32)),
        bvneg(bv(0xf, 32)),
        bvneg(bv(0x1f, 32)),
        bvneg(bv(0x2f, 32)),
        bvneg(bv(0x3e, 32)),
        bvneg(bv(0xffff, 32)),

        bvnot(bv(0x88888888, 32)),
        bvnot(bv(0x12345678, 32)),
        bvnot(bv(0x22345678, 32)),
        bvnot(bv(0x32345678, 32)),
        bvnot(bv(0x42345678, 32)),
        bvnot(bv(0x52345678, 32)),
        bvnot(bv(0x62345678, 32)),
        bvnot(bv(0x72345678, 32)),
        bvnot(bv(0x82345678, 32)),
        bvnot(bv(0x92345678, 32)),
        bvnot(bv(0xa2345678, 32)),
        bvnot(bv(0xb2345678, 32)),
        bvnot(bv(0xc2345678, 32)),
        bvnot(bv(0xd345678, 32)),
        bvnot(bv(0xe2345678, 32)),
        bvnot(bv(0xf2345678, 32)),
        bvnot(bv(0x1, 32)),
        bvnot(bv(0x2, 32)),
        bvnot(bv(0x3, 32)),
        bvnot(bv(0x4, 32)),
        bvnot(bv(0x5, 32)),
        bvnot(bv(0x6, 32)),
        bvnot(bv(0xa, 32)),
        bvnot(bv(0xe, 32)),
        bvnot(bv(0xf, 32)),
        bvnot(bv(0x1f, 32)),
        bvnot(bv(0x2f, 32)),
        bvnot(bv(0x3e, 32)),
        bvnot(bv(0xffff, 32)),

        bvsdiv(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvsdiv(bv(0x12345678, 32), bv(0, 32)),
        bvsdiv(bv(0x12345678, 32), bv(1, 32)),
        bvsdiv(bv(0x12345678, 32), bv(2, 32)),
        bvsdiv(bv(0x12345678, 32), bv(3, 32)),
        bvsdiv(bv(0x12345678, 32), bv(32, 32)),
        bvsdiv(bv(0x12345678, 32), bv(64, 32)),
        bvsdiv(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(0, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(1, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(2, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(3, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(32, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(64, 32)),
        bvsdiv(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvsdiv(bv(0b10000000, 8), bv(0, 8)),
        bvsdiv(bv(0b10000000, 8), bv(1, 8)),
        bvsdiv(bv(0b10000000, 8), bv(2, 8)),
        bvsdiv(bv(0b10000000, 8), bv(3, 8)),
        bvsdiv(bv(0b10000000, 8), bv(4, 8)),
        bvsdiv(bv(0b10000000, 8), bv(5, 8)),
        bvsdiv(bv(0b10000000, 8), bv(6, 8)),
        bvsdiv(bv(0b10000000, 8), bv(7, 8)),
        bvsdiv(bv(0b10000000, 8), bv(8, 8)),
        bvsdiv(bv(0b10000000, 8), bv(9, 8)),
        bvsdiv(bv(0b10000000, 8), bv(123, 8)),
        bvsdiv(bv(0b10001000, 8), bv(0, 8)),
        bvsdiv(bv(0b10001000, 8), bv(1, 8)),
        bvsdiv(bv(0b10001000, 8), bv(2, 8)),
        bvsdiv(bv(0b10001000, 8), bv(3, 8)),
        bvsdiv(bv(0b10001000, 8), bv(4, 8)),
        bvsdiv(bv(0b10001000, 8), bv(5, 8)),
        bvsdiv(bv(0b10001000, 8), bv(6, 8)),
        bvsdiv(bv(0b10001000, 8), bv(7, 8)),
        bvsdiv(bv(0b10001000, 8), bv(8, 8)),
        bvsdiv(bv(0b10001000, 8), bv(9, 8)),
        bvsdiv(bv(0b10001000, 8), bv(123, 8)),
        bvsdiv(bv(0b00010001, 8), bv(0b00000001, 8)),
        bvsdiv(bv(0b00010010, 8), bv(0b00000010, 8)),
        bvsdiv(bv(0b00010100, 8), bv(0b00000100, 8)),
        bvsdiv(bv(0b00001000, 8), bv(0b00001000, 8)),
        bvsdiv(bv(0b00010000, 8), bv(0b00010000, 8)),
        bvsdiv(bv(0b00100000, 8), bv(0b00100000, 8)),
        bvsdiv(bv(0b01000000, 8), bv(0b01000001, 8)),
        bvsdiv(bv(0b10000000, 8), bv(0b10000010, 8)),
        bvsdiv(bv(0b01000000, 8), bv(0b00000011, 8)),
        bvsdiv(bv(0b00100000, 8), bv(0b00000101, 8)),
        bvsdiv(bv(0b00010000, 8), bv(0b00000110, 8)),
        bvsdiv(bv(0b0010001, 7), bv(0b0000001, 7)),
        bvsdiv(bv(0b0010010, 7), bv(0b0000010, 7)),
        bvsdiv(bv(0b0010100, 7), bv(0b0000100, 7)),
        bvsdiv(bv(0b0001000, 7), bv(0b0001000, 7)),
        bvsdiv(bv(0b0010000, 7), bv(0b0010000, 7)),
        bvsdiv(bv(0b0100000, 7), bv(0b0100000, 7)),
        bvsdiv(bv(0b0000000, 7), bv(0b0000001, 7)),
        bvsdiv(bv(0b1000000, 7), bv(0b1000010, 7)),
        bvsdiv(bv(0b0000000, 7), bv(0b0000100, 7)),
        bvsdiv(bv(0b0100000, 7), bv(0b0000110, 7)),
        bvsdiv(bv(0b0010000, 7), bv(0b0000111, 7)),

        bvudiv(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvudiv(bv(0x12345678, 32), bv(0, 32)),
        bvudiv(bv(0x12345678, 32), bv(1, 32)),
        bvudiv(bv(0x12345678, 32), bv(2, 32)),
        bvudiv(bv(0x12345678, 32), bv(3, 32)),
        bvudiv(bv(0x12345678, 32), bv(32, 32)),
        bvudiv(bv(0x12345678, 32), bv(64, 32)),
        bvudiv(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvudiv(bv(0xf2345678, 32), bv(0, 32)),
        bvudiv(bv(0xf2345678, 32), bv(1, 32)),
        bvudiv(bv(0xf2345678, 32), bv(2, 32)),
        bvudiv(bv(0xf2345678, 32), bv(3, 32)),
        bvudiv(bv(0xf2345678, 32), bv(32, 32)),
        bvudiv(bv(0xf2345678, 32), bv(64, 32)),
        bvudiv(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvudiv(bv(0b10000000, 8), bv(0, 8)),
        bvudiv(bv(0b10000000, 8), bv(1, 8)),
        bvudiv(bv(0b10000000, 8), bv(2, 8)),
        bvudiv(bv(0b10000000, 8), bv(3, 8)),
        bvudiv(bv(0b10000000, 8), bv(4, 8)),
        bvudiv(bv(0b10000000, 8), bv(5, 8)),
        bvudiv(bv(0b10000000, 8), bv(6, 8)),
        bvudiv(bv(0b10000000, 8), bv(7, 8)),
        bvudiv(bv(0b10000000, 8), bv(8, 8)),
        bvudiv(bv(0b10000000, 8), bv(9, 8)),
        bvudiv(bv(0b10000000, 8), bv(123, 8)),
        bvudiv(bv(0b10001000, 8), bv(0, 8)),
        bvudiv(bv(0b10001000, 8), bv(1, 8)),
        bvudiv(bv(0b10001000, 8), bv(2, 8)),
        bvudiv(bv(0b10001000, 8), bv(3, 8)),
        bvudiv(bv(0b10001000, 8), bv(4, 8)),
        bvudiv(bv(0b10001000, 8), bv(5, 8)),
        bvudiv(bv(0b10001000, 8), bv(6, 8)),
        bvudiv(bv(0b10001000, 8), bv(7, 8)),
        bvudiv(bv(0b10001000, 8), bv(8, 8)),
        bvudiv(bv(0b10001000, 8), bv(9, 8)),
        bvudiv(bv(0b10001000, 8), bv(123, 8)),
        bvudiv(bv(0b00010001, 8), bv(0b00000001, 8)),
        bvudiv(bv(0b00010010, 8), bv(0b00000010, 8)),
        bvudiv(bv(0b00010100, 8), bv(0b00000100, 8)),
        bvudiv(bv(0b00001000, 8), bv(0b00001000, 8)),
        bvudiv(bv(0b00010000, 8), bv(0b00010000, 8)),
        bvudiv(bv(0b00100000, 8), bv(0b00100000, 8)),
        bvudiv(bv(0b01000000, 8), bv(0b01000001, 8)),
        bvudiv(bv(0b10000000, 8), bv(0b10000010, 8)),
        bvudiv(bv(0b01000000, 8), bv(0b00000011, 8)),
        bvudiv(bv(0b00100000, 8), bv(0b00000101, 8)),
        bvudiv(bv(0b00010000, 8), bv(0b00000110, 8)),
        bvudiv(bv(0b0010001, 7), bv(0b0000001, 7)),
        bvudiv(bv(0b0010010, 7), bv(0b0000010, 7)),
        bvudiv(bv(0b0010100, 7), bv(0b0000100, 7)),
        bvudiv(bv(0b0001000, 7), bv(0b0001000, 7)),
        bvudiv(bv(0b0010000, 7), bv(0b0010000, 7)),
        bvudiv(bv(0b0100000, 7), bv(0b0100000, 7)),
        bvudiv(bv(0b0000000, 7), bv(0b0000001, 7)),
        bvudiv(bv(0b1000000, 7), bv(0b1000010, 7)),
        bvudiv(bv(0b0000000, 7), bv(0b0000100, 7)),
        bvudiv(bv(0b0100000, 7), bv(0b0000110, 7)),
        bvudiv(bv(0b0010000, 7), bv(0b0000111, 7)),

        bvashr(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvashr(bv(0x12345678, 32), bv(0, 32)),
        bvashr(bv(0x12345678, 32), bv(1, 32)),
        bvashr(bv(0x12345678, 32), bv(2, 32)),
        bvashr(bv(0x12345678, 32), bv(3, 32)),
        bvashr(bv(0x12345678, 32), bv(32, 32)),
        bvashr(bv(0x12345678, 32), bv(64, 32)),
        bvashr(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvashr(bv(0xf2345678, 32), bv(0, 32)),
        bvashr(bv(0xf2345678, 32), bv(1, 32)),
        bvashr(bv(0xf2345678, 32), bv(2, 32)),
        bvashr(bv(0xf2345678, 32), bv(3, 32)),
        bvashr(bv(0xf2345678, 32), bv(32, 32)),
        bvashr(bv(0xf2345678, 32), bv(64, 32)),
        bvashr(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvashr(bv(0b10000000, 8), bv(0, 8)),
        bvashr(bv(0b10000000, 8), bv(1, 8)),
        bvashr(bv(0b10000000, 8), bv(2, 8)),
        bvashr(bv(0b10000000, 8), bv(3, 8)),
        bvashr(bv(0b10000000, 8), bv(4, 8)),
        bvashr(bv(0b10000000, 8), bv(5, 8)),
        bvashr(bv(0b10000000, 8), bv(6, 8)),
        bvashr(bv(0b10000000, 8), bv(7, 8)),
        bvashr(bv(0b10000000, 8), bv(8, 8)),
        bvashr(bv(0b10000000, 8), bv(9, 8)),
        bvashr(bv(0b10000000, 8), bv(123, 8)),
        bvashr(bv(0b10001000, 8), bv(0, 8)),
        bvashr(bv(0b10001000, 8), bv(1, 8)),
        bvashr(bv(0b10001000, 8), bv(2, 8)),
        bvashr(bv(0b10001000, 8), bv(3, 8)),
        bvashr(bv(0b10001000, 8), bv(4, 8)),
        bvashr(bv(0b10001000, 8), bv(5, 8)),
        bvashr(bv(0b10001000, 8), bv(6, 8)),
        bvashr(bv(0b10001000, 8), bv(7, 8)),
        bvashr(bv(0b10001000, 8), bv(8, 8)),
        bvashr(bv(0b10001000, 8), bv(9, 8)),
        bvashr(bv(0b10001000, 8), bv(123, 8)),
        bvashr(bv(0b00010001, 8), bv(0b00000001, 8)),
        bvashr(bv(0b00010010, 8), bv(0b00000010, 8)),
        bvashr(bv(0b00010100, 8), bv(0b00000100, 8)),
        bvashr(bv(0b00001000, 8), bv(0b00001000, 8)),
        bvashr(bv(0b00010000, 8), bv(0b00010000, 8)),
        bvashr(bv(0b00100000, 8), bv(0b00100000, 8)),
        bvashr(bv(0b01000000, 8), bv(0b01000001, 8)),
        bvashr(bv(0b10000000, 8), bv(0b10000010, 8)),
        bvashr(bv(0b01000000, 8), bv(0b00000011, 8)),
        bvashr(bv(0b00100000, 8), bv(0b00000101, 8)),
        bvashr(bv(0b00010000, 8), bv(0b00000110, 8)),
        bvashr(bv(0b0010001, 7), bv(0b0000001, 7)),
        bvashr(bv(0b0010010, 7), bv(0b0000010, 7)),
        bvashr(bv(0b0010100, 7), bv(0b0000100, 7)),
        bvashr(bv(0b0001000, 7), bv(0b0001000, 7)),
        bvashr(bv(0b0010000, 7), bv(0b0010000, 7)),
        bvashr(bv(0b0100000, 7), bv(0b0100000, 7)),
        bvashr(bv(0b0000000, 7), bv(0b0000001, 7)),
        bvashr(bv(0b1000000, 7), bv(0b1000010, 7)),
        bvashr(bv(0b0000000, 7), bv(0b0000100, 7)),
        bvashr(bv(0b0100000, 7), bv(0b0000110, 7)),
        bvashr(bv(0b0010000, 7), bv(0b0000111, 7)),
        bvashr(bv(0xfe00000000000000, 64), bv(8, 64)),

        bvlshr(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvlshr(bv(0x12345678, 32), bv(0, 32)),
        bvlshr(bv(0x12345678, 32), bv(1, 32)),
        bvlshr(bv(0x12345678, 32), bv(2, 32)),
        bvlshr(bv(0x12345678, 32), bv(3, 32)),
        bvlshr(bv(0x12345678, 32), bv(32, 32)),
        bvlshr(bv(0x12345678, 32), bv(64, 32)),
        bvlshr(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvlshr(bv(0xf2345678, 32), bv(0, 32)),
        bvlshr(bv(0xf2345678, 32), bv(1, 32)),
        bvlshr(bv(0xf2345678, 32), bv(2, 32)),
        bvlshr(bv(0xf2345678, 32), bv(3, 32)),
        bvlshr(bv(0xf2345678, 32), bv(4, 32)),
        bvlshr(bv(0xf2345678, 32), bv(5, 32)),
        bvlshr(bv(0xf2345678, 32), bv(6, 32)),
        bvlshr(bv(0xf2345678, 32), bv(32, 32)),
        bvlshr(bv(0xf2345678, 32), bv(64, 32)),
        bvlshr(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvlshr(bv(0b10000000, 8), bv(0, 8)),
        bvlshr(bv(0b10000000, 8), bv(1, 8)),
        bvlshr(bv(0b10000000, 8), bv(2, 8)),
        bvlshr(bv(0b10000000, 8), bv(3, 8)),
        bvlshr(bv(0b10000000, 8), bv(4, 8)),
        bvlshr(bv(0b10000000, 8), bv(5, 8)),
        bvlshr(bv(0b10000000, 8), bv(6, 8)),
        bvlshr(bv(0b10000000, 8), bv(7, 8)),
        bvlshr(bv(0b10000000, 8), bv(8, 8)),
        bvlshr(bv(0b10000000, 8), bv(9, 8)),
        bvlshr(bv(0b10000000, 8), bv(123, 8)),
        bvlshr(bv(0b10001000, 8), bv(0, 8)),
        bvlshr(bv(0b10001000, 8), bv(1, 8)),
        bvlshr(bv(0b10001000, 8), bv(2, 8)),
        bvlshr(bv(0b10001000, 8), bv(3, 8)),
        bvlshr(bv(0b10001000, 8), bv(4, 8)),
        bvlshr(bv(0b10001000, 8), bv(5, 8)),
        bvlshr(bv(0b10001000, 8), bv(6, 8)),
        bvlshr(bv(0b10001000, 8), bv(7, 8)),
        bvlshr(bv(0b10001000, 8), bv(8, 8)),
        bvlshr(bv(0b10001000, 8), bv(9, 8)),
        bvlshr(bv(0b10001000, 8), bv(123, 8)),

        bvshl(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvshl(bv(0x12345678, 32), bv(0, 32)),
        bvshl(bv(0x12345678, 32), bv(1, 32)),
        bvshl(bv(0x12345678, 32), bv(2, 32)),
        bvshl(bv(0x12345678, 32), bv(3, 32)),
        bvshl(bv(0x12345678, 32), bv(32, 32)),
        bvshl(bv(0x12345678, 32), bv(64, 32)),
        bvshl(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvshl(bv(0xf2345678, 32), bv(0, 32)),
        bvshl(bv(0xf2345678, 32), bv(1, 32)),
        bvshl(bv(0xf2345678, 32), bv(2, 32)),
        bvshl(bv(0xf2345678, 32), bv(3, 32)),
        bvshl(bv(0xf2345678, 32), bv(32, 32)),
        bvshl(bv(0xf2345678, 32), bv(64, 32)),
        bvshl(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvshl(bv(0b00000001, 8), bv(0, 8)),
        bvshl(bv(0b00000001, 8), bv(1, 8)),
        bvshl(bv(0b00000001, 8), bv(2, 8)),
        bvshl(bv(0b00000001, 8), bv(3, 8)),
        bvshl(bv(0b00000001, 8), bv(4, 8)),
        bvshl(bv(0b00000001, 8), bv(5, 8)),
        bvshl(bv(0b00000001, 8), bv(6, 8)),
        bvshl(bv(0b00000001, 8), bv(7, 8)),
        bvshl(bv(0b00000001, 8), bv(8, 8)),
        bvshl(bv(0b00000001, 8), bv(9, 8)),
        bvshl(bv(0b00000001, 8), bv(123, 8)),
        bvshl(bv(0b00000001, 8), bv(0, 8)),
        bvshl(bv(0b00000011, 8), bv(1, 8)),
        bvshl(bv(0b00000101, 8), bv(2, 8)),
        bvshl(bv(0b00001001, 8), bv(3, 8)),
        bvshl(bv(0b00010001, 8), bv(4, 8)),
        bvshl(bv(0b00100001, 8), bv(5, 8)),
        bvshl(bv(0b01000001, 8), bv(6, 8)),
        bvshl(bv(0b10000011, 8), bv(7, 8)),
        bvshl(bv(0b01000101, 8), bv(8, 8)),
        bvshl(bv(0b00101001, 8), bv(9, 8)),
        bvshl(bv(0b00010001, 8), bv(123, 8)),

        bvrol(0x88888888, bv(0x99999999, 32)),
        bvrol(0x12345678, bv(0, 32)),
        bvrol(0x12345678, bv(1, 32)),
        bvrol(0x12345678, bv(2, 32)),
        bvrol(0x12345678, bv(3, 32)),
        bvrol(0x12345678, bv(32, 32)),
        bvrol(0x12345678, bv(64, 32)),
        bvrol(0x12345678, bv(0x12345678, 32)),
        bvrol(0xf2345678, bv(0, 32)),
        bvrol(0xf2345678, bv(1, 32)),
        bvrol(0xf2345678, bv(2, 32)),
        bvrol(0xf2345678, bv(3, 32)),
        bvrol(0xf2345678, bv(32, 32)),
        bvrol(0xf2345678, bv(64, 32)),
        bvrol(0xf2345678, bv(0x12345678, 32)),

        bvrol(0x99999999, bv(0x88888888, 32)),
        bvrol(0, bv(0x12345678, 32)),
        bvrol(1, bv(0x12345678, 32)),
        bvrol(2, bv(0x12345678, 32)),
        bvrol(3, bv(0x12345678, 32)),
        bvrol(32, bv(0x12345678, 32)),
        bvrol(64, bv(0x12345678, 32)),
        bvrol(0x12345678, bv(0x12345678, 32)),
        bvrol(0, bv(0xf2345678, 32)),
        bvrol(1, bv(0xf2345678, 32)),
        bvrol(2, bv(0xf2345678, 32)),
        bvrol(3, bv(0xf2345678, 32)),
        bvrol(32, bv(0xf2345678, 32)),
        bvrol(64, bv(0xf2345678, 32)),
        bvrol(0x12345678, bv(0xf2345678, 32)),

        bvror(0x88888888, bv(0x99999999, 32)),
        bvror(0x12345678, bv(0, 32)),
        bvror(0x12345678, bv(1, 32)),
        bvror(0x12345678, bv(2, 32)),
        bvror(0x12345678, bv(3, 32)),
        bvror(0x12345678, bv(32, 32)),
        bvror(0x12345678, bv(64, 32)),
        bvror(0x12345678, bv(0x12345678, 32)),
        bvror(0xf2345678, bv(0, 32)),
        bvror(0xf2345678, bv(1, 32)),
        bvror(0xf2345678, bv(2, 32)),
        bvror(0xf2345678, bv(3, 32)),
        bvror(0xf2345678, bv(32, 32)),
        bvror(0xf2345678, bv(64, 32)),
        bvror(0xf2345678, bv(0x12345678, 32)),

        bvror(0x99999999, bv(0x88888888, 32)),
        bvror(0, bv(0x12345678, 32)),
        bvror(1, bv(0x12345678, 32)),
        bvror(2, bv(0x12345678, 32)),
        bvror(3, bv(0x12345678, 32)),
        bvror(32, bv(0x12345678, 32)),
        bvror(64, bv(0x12345678, 32)),
        bvror(0x12345678, bv(0x12345678, 32)),
        bvror(0, bv(0xf2345678, 32)),
        bvror(1, bv(0xf2345678, 32)),
        bvror(2, bv(0xf2345678, 32)),
        bvror(3, bv(0xf2345678, 32)),
        bvror(32, bv(0xf2345678, 32)),
        bvror(64, bv(0xf2345678, 32)),
        bvror(0x12345678, bv(0xf2345678, 32)),

        bvsmod(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvsmod(bv(0x12345678, 32), bv(0, 32)),
        bvsmod(bv(0x12345678, 32), bv(1, 32)),
        bvsmod(bv(0x12345678, 32), bv(2, 32)),
        bvsmod(bv(0x12345678, 32), bv(3, 32)),
        bvsmod(bv(0x12345678, 32), bv(32, 32)),
        bvsmod(bv(0x12345678, 32), bv(64, 32)),
        bvsmod(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvsmod(bv(0xf2345678, 32), bv(0, 32)),
        bvsmod(bv(0xf2345678, 32), bv(1, 32)),
        bvsmod(bv(0xf2345678, 32), bv(2, 32)),
        bvsmod(bv(0xf2345678, 32), bv(3, 32)),
        bvsmod(bv(0xf2345678, 32), bv(32, 32)),
        bvsmod(bv(0xf2345678, 32), bv(64, 32)),
        bvsmod(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvsmod(bv(0b10000000, 8), bv(0, 8)),
        bvsmod(bv(0b10000000, 8), bv(1, 8)),
        bvsmod(bv(0b10000000, 8), bv(2, 8)),
        bvsmod(bv(0b10000000, 8), bv(3, 8)),
        bvsmod(bv(0b10000000, 8), bv(4, 8)),
        bvsmod(bv(0b10000000, 8), bv(5, 8)),
        bvsmod(bv(0b10000000, 8), bv(6, 8)),
        bvsmod(bv(0b10000000, 8), bv(7, 8)),
        bvsmod(bv(0b10000000, 8), bv(8, 8)),
        bvsmod(bv(0b10000000, 8), bv(9, 8)),
        bvsmod(bv(0b10000000, 8), bv(123, 8)),
        bvsmod(bv(0b10001000, 8), bv(0, 8)),
        bvsmod(bv(0b10001000, 8), bv(1, 8)),
        bvsmod(bv(0b10001000, 8), bv(2, 8)),
        bvsmod(bv(0b10001000, 8), bv(3, 8)),
        bvsmod(bv(0b10001000, 8), bv(4, 8)),
        bvsmod(bv(0b10001000, 8), bv(5, 8)),
        bvsmod(bv(0b10001000, 8), bv(6, 8)),
        bvsmod(bv(0b10001000, 8), bv(7, 8)),
        bvsmod(bv(0b10001000, 8), bv(8, 8)),
        bvsmod(bv(0b10001000, 8), bv(9, 8)),
        bvsmod(bv(0b10001000, 8), bv(123, 8)),
        bvsmod(bv(0b00010001, 8), bv(0b00000001, 8)),
        bvsmod(bv(0b00010010, 8), bv(0b00000010, 8)),
        bvsmod(bv(0b00010100, 8), bv(0b00000100, 8)),
        bvsmod(bv(0b00001000, 8), bv(0b00001000, 8)),
        bvsmod(bv(0b00010000, 8), bv(0b00010000, 8)),
        bvsmod(bv(0b00100000, 8), bv(0b00100000, 8)),
        bvsmod(bv(0b01000000, 8), bv(0b01000001, 8)),
        bvsmod(bv(0b10000000, 8), bv(0b10000010, 8)),
        bvsmod(bv(0b01000000, 8), bv(0b00000011, 8)),
        bvsmod(bv(0b00100000, 8), bv(0b00000101, 8)),
        bvsmod(bv(0b00010000, 8), bv(0b00000110, 8)),
        bvsmod(bv(0b0010001, 7), bv(0b0000001, 7)),
        bvsmod(bv(0b0010010, 7), bv(0b0000010, 7)),
        bvsmod(bv(0b0010100, 7), bv(0b0000100, 7)),
        bvsmod(bv(0b0001000, 7), bv(0b0001000, 7)),
        bvsmod(bv(0b0010000, 7), bv(0b0010000, 7)),
        bvsmod(bv(0b0100000, 7), bv(0b0100000, 7)),
        bvsmod(bv(0b0000000, 7), bv(0b0000001, 7)),
        bvsmod(bv(0b1000000, 7), bv(0b1000010, 7)),
        bvsmod(bv(0b0000000, 7), bv(0b0000100, 7)),
        bvsmod(bv(0b0100000, 7), bv(0b0000110, 7)),
        bvsmod(bv(0b0010000, 7), bv(0b0000111, 7)),

        bvsrem(bv(0x88888888, 32), bv(0x99999999, 32)),
        bvsrem(bv(0x12345678, 32), bv(0, 32)),
        bvsrem(bv(0x12345678, 32), bv(1, 32)),
        bvsrem(bv(0x12345678, 32), bv(2, 32)),
        bvsrem(bv(0x12345678, 32), bv(3, 32)),
        bvsrem(bv(0x12345678, 32), bv(32, 32)),
        bvsrem(bv(0x12345678, 32), bv(64, 32)),
        bvsrem(bv(0x12345678, 32), bv(0x12345678, 32)),
        bvsrem(bv(0xf2345678, 32), bv(0, 32)),
        bvsrem(bv(0xf2345678, 32), bv(1, 32)),
        bvsrem(bv(0xf2345678, 32), bv(2, 32)),
        bvsrem(bv(0xf2345678, 32), bv(3, 32)),
        bvsrem(bv(0xf2345678, 32), bv(32, 32)),
        bvsrem(bv(0xf2345678, 32), bv(64, 32)),
        bvsrem(bv(0xf2345678, 32), bv(0x12345678, 32)),
        bvsrem(bv(0b10000000, 8), bv(0, 8)),
        bvsrem(bv(0b10000000, 8), bv(1, 8)),
        bvsrem(bv(0b10000000, 8), bv(2, 8)),
        bvsrem(bv(0b10000000, 8), bv(3, 8)),
        bvsrem(bv(0b10000000, 8), bv(4, 8)),
        bvsrem(bv(0b10000000, 8), bv(5, 8)),
        bvsrem(bv(0b10000000, 8), bv(6, 8)),
        bvsrem(bv(0b10000000, 8), bv(7, 8)),
        bvsrem(bv(0b10000000, 8), bv(8, 8)),
        bvsrem(bv(0b10000000, 8), bv(9, 8)),
        bvsrem(bv(0b10000000, 8), bv(123, 8)),
        bvsrem(bv(0b10001000, 8), bv(0, 8)),
        bvsrem(bv(0b10001000, 8), bv(1, 8)),
        bvsrem(bv(0b10001000, 8), bv(2, 8)),
        bvsrem(bv(0b10001000, 8), bv(3, 8)),
        bvsrem(bv(0b10001000, 8), bv(4, 8)),
        bvsrem(bv(0b10001000, 8), bv(5, 8)),
        bvsrem(bv(0b10001000, 8), bv(6, 8)),
        bvsrem(bv(0b10001000, 8), bv(7, 8)),
        bvsrem(bv(0b10001000, 8), bv(8, 8)),
        bvsrem(bv(0b10001000, 8), bv(9, 8)),
        bvsrem(bv(0b10001000, 8), bv(123, 8)),
        bvsrem(bv(0b00010001, 8), bv(0b00000001, 8)),
        bvsrem(bv(0b00010010, 8), bv(0b00000010, 8)),
        bvsrem(bv(0b00010100, 8), bv(0b00000100, 8)),
        bvsrem(bv(0b00001000, 8), bv(0b00001000, 8)),
        bvsrem(bv(0b00010000, 8), bv(0b00010000, 8)),
        bvsrem(bv(0b00100000, 8), bv(0b00100000, 8)),
        bvsrem(bv(0b01000000, 8), bv(0b01000001, 8)),
        bvsrem(bv(0b10000000, 8), bv(0b10000010, 8)),
        bvsrem(bv(0b01000000, 8), bv(0b00000011, 8)),
        bvsrem(bv(0b00100000, 8), bv(0b00000101, 8)),
        bvsrem(bv(0b00010000, 8), bv(0b00000110, 8)),
        bvsrem(bv(0b0010001, 7), bv(0b0000001, 7)),
        bvsrem(bv(0b0010010, 7), bv(0b0000010, 7)),
        bvsrem(bv(0b0010100, 7), bv(0b0000100, 7)),
        bvsrem(bv(0b0001000, 7), bv(0b0001000, 7)),
        bvsrem(bv(0b0010000, 7), bv(0b0010000, 7)),
        bvsrem(bv(0b0100000, 7), bv(0b0100000, 7)),
        bvsrem(bv(0b0000000, 7), bv(0b0000001, 7)),
        bvsrem(bv(0b1000000, 7), bv(0b1000010, 7)),
        bvsrem(bv(0b0000000, 7), bv(0b0000100, 7)),
        bvsrem(bv(0b0100000, 7), bv(0b0000110, 7)),
        bvsrem(bv(0b0010000, 7), bv(0b0000111, 7)),
    ]
    count = 0
    for test in tests:
        trv = test.evaluate()
        z3v = evaluateAstViaZ3(test)
        if not trv == z3v:
            print '[KO] %s', test
            print '\tTriton value : %x' %(trv)
            print '\tZ3 value     : %x' %(z3v)
            return -1
        else:
            count += 1
    return count


def test_2():
    count = 0
    setArchitecture(ARCH.X86_64)

    reg      = REG.RAX
    name     = reg.getName()
    size     = reg.getSize()
    sizeBit  = reg.getBitSize()
    cv       = reg.getConcreteValue()
    parent   = reg.getParent()
    t        = reg.getType()
    valid    = reg.isValid()
    flag     = reg.isFlag()
    register = reg.isRegister()

    if name == 'rax':
        count += 1
    else:
        print '[KO] REG.RAX.getName()'
        print '\tOutput   : %s' %(name)
        print '\tExpected : rax'
        return -1

    if size == 8:
        count += 1
    else:
        print '[KO] REG.RAX.getSize()'
        print '\tOutput   : %d' %(size)
        print '\tExpected : 8'
        return -1

    if sizeBit == 64:
        count += 1
    else:
        print '[KO] REG.RAX.getSize()'
        print '\tOutput   : %d' %(sizeBit)
        print '\tExpected : 64'
        return -1

    if cv == 0:
        count += 1
    else:
        print '[KO] REG.RAX.getConcreteValue()'
        print '\tOutput   : 0x%x' %(cv)
        print '\tExpected : 0x0'
        return -1

    cv = reg.setConcreteValue(0x1122334455667788)
    cv = reg.getConcreteValue()
    if cv == 0x1122334455667788:
        count += 1
    else:
        print '[KO] REG.RAX.getConcreteValue()'
        print '\tOutput   : 0x%x' %(cv)
        print '\tExpected : 0x1122334455667788'
        return -1

    if parent.getName() == 'rax':
        count += 1
    else:
        print '[KO] REG.RAX.getParent().getName()'
        print '\tOutput   : %s' %(parent.getName())
        print '\tExpected : rax'
        return -1

    if t == OPERAND.REG:
        count += 1
    else:
        print '[KO] REG.RAX.getType()'
        print '\tOutput   : %d' %(t)
        print '\tExpected : OPERAND.REG'
        return -1

    if valid:
        count += 1
    else:
        print '[KO] REG.RAX.isValid()'
        print '\tOutput   : false'
        print '\tExpected : true'
        return -1

    if not flag:
        count += 1
    else:
        print '[KO] REG.RAX.isFlag()'
        print '\tOutput   : true'
        print '\tExpected : false'
        return -1

    if register:
        count += 1
    else:
        print '[KO] REG.RAX.isRegister()'
        print '\tOutput   : false'
        print '\tExpected : true'
        return -1

    if REG.AH.getSize() == 1:
        count += 1
    else:
        print '[KO] REG.AH.getSize()'
        print '\tOutput   : %d' %(REG.AH.getSize())
        print '\tExpected : 1'
        return -1

    if REG.AH.getBitvector().getHigh() == 15:
        count += 1
    else:
        print '[KO] REG.AH.getBitvector().getHigh()'
        print '\tOutput   : %d' %(REG.AH.getBitvector().getHigh())
        print '\tExpected : 15'
        return -1

    if REG.AH.getBitvector().getLow() == 8:
        count += 1
    else:
        print '[KO] REG.AH.getBitvector().getLow()'
        print '\tOutput   : %d' %(REG.AH.getBitvector().getLow())
        print '\tExpected : 8'
        return -1

    if REG.AH.getBitvector().getVectorSize() == 8:
        count += 1
    else:
        print '[KO] REG.AH.getBitvector().getVectorSize()'
        print '\tOutput   : %d' %(REG.AH.getBitvector().getVectorSize())
        print '\tExpected : 8'
        return -1

    if REG.AH.getParent().getName() == 'rax':
        count += 1
    else:
        print '[KO] REG.AH.getParent().getName()'
        print '\tOutput   : %s' %(REG.AH.getParent().getName())
        print '\tExpected : rax'
        return -1

    setArchitecture(ARCH.X86)
    if REG.AH.getParent().getName() == 'eax':
        count += 1
    else:
        print '[KO] REG.AH.getParent().getName()'
        print '\tOutput   : %s' %(REG.AH.getParent().getName())
        print '\tExpected : rax'
        return -1

    if REG.AH.getParent().getBitSize() == 32:
        count += 1
    else:
        print '[KO] REG.AH.getParent().getBitSize()'
        print '\tOutput   : %d' %(REG.AH.getParent().getBitSize())
        print '\tExpected : 32'
        return -1

    xmm = Register(REG.XMM1, 0x112233445566778899aabbccddeeff00)
    if xmm.getBitSize() == 128:
        count += 1
    else:
        print '[KO] xmm.getBitSize()'
        print '\tOutput   : %d' %(xmm.getBitSize())
        print '\tExpected : 128'
        return -1

    if xmm.getConcreteValue() == 0x112233445566778899aabbccddeeff00:
        count += 1
    else:
        print '[KO] xmm.getConcreteValue()'
        print '\tOutput   : 0x%x' %(xmm.getConcreteValue())
        print '\tExpected : 0x112233445566778899aabbccddeeff00'
        return -1

    setArchitecture(ARCH.X86_64)
    ymm = Register(REG.YMM1, 0x112233445566778899aabbccddeeff00)
    if ymm.getBitSize() == 256:
        count += 1
    else:
        print '[KO] ymm.getBitSize()'
        print '\tOutput   : %d' %(ymm.getBitSize())
        print '\tExpected : 256'
        return -1

    if ymm.getConcreteValue() == 0x112233445566778899aabbccddeeff00:
        count += 1
    else:
        print '[KO] ymm.getConcreteValue()'
        print '\tOutput   : 0x%x' %(ymm.getConcreteValue())
        print '\tExpected : 0x112233445566778899aabbccddeeff00'
        return -1

    ymm.setConcreteValue(0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
    if ymm.getConcreteValue() == 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:
        count += 1
    else:
        print '[KO] ymm.getConcreteValue()'
        print '\tOutput   : 0x%x' %(ymm.getConcreteValue())
        print '\tExpected : 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00'
        return -1

    zmm = Register(REG.ZMM2, 0)
    if zmm.getBitSize() == 512:
        count += 1
    else:
        print '[KO] zmm.getBitSize()'
        print '\tOutput   : %d' %(zmm.getBitSize())
        print '\tExpected : 512'
        return -1

    zmm.setConcreteValue(0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
    if zmm.getConcreteValue() == 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:
        count += 1
    else:
        print '[KO] zmm.getConcreteValue()'
        print '\tOutput   : 0x%x' %(zmm.getConcreteValue())
        print '\tExpected : 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00'
        return -1

    try:
        Register(REG.AL, 0xff)
        count += 1
    except:
        print '[KO] Register(REG.AL, 0xff)'
        print '\tOutput   : <exception>'
        print '\tExpected : OK'
        return -1

    try:
        Register(REG.AL, 0xff + 1)
        print '[KO] Register(REG.AL, 0xff + 1)'
        print '\tOutput   : OK'
        print '\tExpected : <exception>'
        return -1
    except:
        count += 1

    try:
        Register(REG.AH, 0xff)
        count += 1
    except:
        print '[KO] Register(REG.AH, 0xff)'
        print '\tOutput   : <exception>'
        print '\tExpected : OK'
        return -1

    try:
        Register(REG.AH, 0xff + 1)
        print '[KO] Register(REG.AH, 0xff + 1)'
        print '\tOutput   : OK'
        print '\tExpected : <exception>'
        return -1
    except:
        count += 1

    try:
        Register(REG.ZF, 1)
        count += 1
    except:
        print '[KO] Register(REG.ZF, 1)'
        print '\tOutput   : <exception>'
        print '\tExpected : OK'
        return -1

    try:
        Register(REG.ZF, 2)
        print '[KO] Register(REG.ZF, 2)'
        print '\tOutput   : OK'
        print '\tExpected : <exception>'
        return -1
    except:
        count += 1

    try:
        al = Register(REG.AL)
        al.setConcreteValue(0xff)
        count += 1
    except:
        print '[KO] al.setConcreteValue(0xff)'
        print '\tOutput   : <exception>'
        print '\tExpected : OK'
        return -1

    try:
        al = Register(REG.AL)
        al.setConcreteValue(0x100)
        print '[KO] al.setConcreteValue(0x100)'
        print '\tOutput   : OK'
        print '\tExpected : <exception>'
        return -1
    except:
        count += 1

    return count


def test_3():
    count = 0
    setArchitecture(ARCH.X86_64)

    mem = Memory(0x400f4d3, 8, 0x6162636465666768)

    if mem.getAddress() == 0x400f4d3:
        count += 1
    else:
        print '[KO] mem.getAddress()'
        print '\tOutput   : 0x%x' %(mem.getAddress())
        print '\tExpected : 0x400f4d3'
        return -1

    if mem.getBitSize() == 64:
        count += 1
    else:
        print '[KO] mem.getBitSize()'
        print '\tOutput   : %d' %(mem.getBitSize())
        print '\tExpected : 64'
        return -1

    if mem.getSize() == 8:
        count += 1
    else:
        print '[KO] mem.getSize()'
        print '\tOutput   : %d' %(mem.getSize())
        print '\tExpected : 8'
        return -1

    if mem.getConcreteValue() == 0x6162636465666768:
        count += 1
    else:
        print '[KO] mem.getConcreteValue()'
        print '\tOutput   : 0x%x' %(mem.getConcreteValue())
        print '\tExpected : 0x6162636465666768'
        return -1

    if mem.getType() == OPERAND.MEM:
        count += 1
    else:
        print '[KO] mem.getType()'
        print '\tOutput   : %d' %(mem.getType())
        print '\tExpected : OPERAND.MEM'
        return -1

    mem.setConcreteValue(0x1000)
    if mem.getConcreteValue() == 0x1000:
        count += 1
    else:
        print '[KO] mem.getConcreteValue()'
        print '\tOutput   : 0x%x' %(mem.getConcreteValue())
        print '\tExpected : 0x1000'
        return -1

    if mem.getSize() == 8:
        count += 1
    else:
        print '[KO] mem.getSize()'
        print '\tOutput   : %d' %(mem.getSize())
        print '\tExpected : 8'
        return -1

    if not mem.getBaseRegister().isValid():
        count += 1
    else:
        print '[KO] mem.getBaseRegister()'
        print '\tOutput   : %s' %(mem.getBaseRegister())
        print '\tExpected : unknown:1 bv[0..0]'
        return -1

    if not mem.getIndexRegister().isValid():
        count += 1
    else:
        print '[KO] mem.getIndexRegister()'
        print '\tOutput   : %s' %(mem.getIndexRegister())
        print '\tExpected : unknown:1 bv[0..0]'
        return -1

    if not mem.getSegmentRegister().isValid():
        count += 1
    else:
        print '[KO] mem.getSegmentRegister()'
        print '\tOutput   : %s' %(mem.getSegmentRegister())
        print '\tExpected : unknown:1 bv[0..0]'
        return -1

    if mem.getScale().getValue() == 0:
        count += 1
    else:
        print '[KO] mem.getScale().getValue()'
        print '\tOutput   : 0x%x' %(mem.getScale().getValue())
        print '\tExpected : 0x0'
        return -1

    if mem.getScale().getBitSize() == 1:
        count += 1
    else:
        print '[KO] mem.getScale().getBitSize()'
        print '\tOutput   : %d' %(mem.getScale().getBitSize())
        print '\tExpected : 1'
        return -1

    if mem.getDisplacement().getValue() == 0:
        count += 1
    else:
        print '[KO] mem.getDisplacement().getValue()'
        print '\tOutput   : 0x%x' %(mem.getDisplacement().getValue())
        print '\tExpected : 0x0'
        return -1

    if mem.getLeaAst() is None:
        count += 1
    else:
        print '[KO] mem.getLeaAst()'
        print '\tOutput   : %s' %(mem.getLeaAst())
        print '\tExpected : None'
        return -1

    mem.setBaseRegister(REG.RAX)
    if mem.getBaseRegister().getName() == REG.RAX.getName():
        count += 1
    else:
        print '[KO] mem.setBaseRegister() and mem.getBaseRegister()'
        print '\tOutput   : %s' %(mem.getBaseRegister())
        print '\tExpected : True'
        return -1

    if mem.getBaseRegister().getName() != REG.RBX.getName():
        count += 1
    else:
        print '[KO] mem.setBaseRegister() and mem.getBaseRegister()'
        print '\tOutput   : %s' %(mem.getBaseRegister())
        print '\tExpected : False'
        return -1

    mem.setIndexRegister(REG.RCX)
    if mem.getIndexRegister().getName() == REG.RCX.getName():
        count += 1
    else:
        print '[KO] mem.setIndexRegister() and mem.getIndexRegister()'
        print '\tOutput   : %s' %(mem.getIndexRegister())
        print '\tExpected : True'
        return -1

    if mem.getIndexRegister().getName() != REG.RAX.getName():
        count += 1
    else:
        print '[KO] mem.setIndexRegister() and mem.getIndexRegister()'
        print '\tOutput   : %s' %(mem.getIndexRegister())
        print '\tExpected : False'
        return -1

    mem.setSegmentRegister(REG.FS)
    if mem.getSegmentRegister().getName() == REG.FS.getName():
        count += 1
    else:
        print '[KO] mem.setSegmentRegister() and mem.getSegmentRegister()'
        print '\tOutput   : %s' %(mem.getSegmentRegister())
        print '\tExpected : True'
        return -1

    if mem.getSegmentRegister().getName() != REG.GS.getName():
        count += 1
    else:
        print '[KO] mem.setSegmentRegister() and mem.getSegmentRegister()'
        print '\tOutput   : %s' %(mem.getSegmentRegister())
        print '\tExpected : False'
        return -1

    return count


def test_4():
    count = 0
    setArchitecture(ARCH.X86_64)

    imm = Immediate(0x1234, CPUSIZE.WORD)

    if imm.getBitSize() == 16:
        count += 1
    else:
        print '[KO] imm.getBitSize()'
        print '\tOutput   : %d' %(imm.getBitSize())
        print '\tExpected : 16'
        return -1

    if imm.getSize() == 2:
        count += 1
    else:
        print '[KO] imm.getSize()'
        print '\tOutput   : %d' %(imm.getSize())
        print '\tExpected : 2'
        return -1

    if imm.getBitSize() != 32:
        count += 1
    else:
        print '[KO] imm.getBitSize()'
        print '\tOutput   : %d' %(imm.getBitSize())
        print '\tExpected : 16'
        return -1

    if imm.getSize() != 1:
        count += 1
    else:
        print '[KO] imm.getSize()'
        print '\tOutput   : %d' %(imm.getSize())
        print '\tExpected : 2'
        return -1

    if imm.getValue() == 0x1234:
        count += 1
    else:
        print '[KO] imm.getValue()'
        print '\tOutput   : 0x%x' %(imm.getValue())
        print '\tExpected : 0x1234'
        return -1

    if imm.getValue() != 0x0234:
        count += 1
    else:
        print '[KO] imm.getValue()'
        print '\tOutput   : 0x%x' %(imm.getValue())
        print '\tExpected : 0x1234'
        return -1

    if imm.getType() == OPERAND.IMM:
        count += 1
    else:
        print '[KO] imm.getType()'
        print '\tOutput   : %d' %(imm.getType())
        print '\tExpected : OPERAND.IMM'
        return -1

    return count


def test_5():
    count = 0

    setArchitecture(ARCH.X86_64)
    inst = Instruction()
    inst.setOpcodes("\x48\x01\xd8") # add rax, rbx
    inst.setAddress(0x400000)
    inst.updateContext(Register(REG.RAX, 0x1122334455667788))
    inst.updateContext(Register(REG.RBX, 0x8877665544332211))
    processing(inst)

    if inst.getAddress() == 0x400000:
        count += 1
    else:
        print '[KO] inst.getAddress()'
        print '\tOutput   : %d' %(inst.getAddress())
        print '\tExpected : 0x400000'
        return -1

    if not len(inst.getLoadAccess()):
        count += 1
    else:
        print '[KO] inst.getLoadAccess()'
        print '\tOutput   : %s' %(inst.getLoadAccess())
        print '\tExpected : []'
        return -1

    if not len(inst.getStoreAccess()):
        count += 1
    else:
        print '[KO] inst.getStoreAccess()'
        print '\tOutput   : %s' %(inst.getStoreAccess())
        print '\tExpected : []'
        return -1

    if len(inst.getReadRegisters()) == 2:
        count += 1
    else:
        print '[KO] inst.getReadRegisters()'
        print '\tOutput   : %s' %(inst.getReadRegisters())
        print '\tExpected : [RAX, RBX]'
        return -1

    if len(inst.getWrittenRegisters()) == 8:
        count += 1
    else:
        print '[KO] inst.getReadRegisters()'
        print '\tOutput   : %s' %(inst.getWrittenRegisters())
        print '\tExpected : [RAX, RIP, AF, CF, OF, PF, SF, ZF]'
        return -1

    if not inst.isTainted():
        count += 1
    else:
        print '[KO] inst.isTainted()'
        print '\tOutput   : %d' %(inst.isTainted())
        print '\tExpected : false'
        return -1

    if not inst.isPrefixed():
        count += 1
    else:
        print '[KO] inst.isPrefixed()'
        print '\tOutput   : %d' %(inst.isPrefixed())
        print '\tExpected : false'
        return -1

    if not inst.isMemoryWrite():
        count += 1
    else:
        print '[KO] inst.isMemoryWrite()'
        print '\tOutput   : %d' %(inst.isMemoryWrite())
        print '\tExpected : false'
        return -1

    if not inst.isMemoryRead():
        count += 1
    else:
        print '[KO] inst.isMemoryRead()'
        print '\tOutput   : %d' %(inst.isMemoryRead())
        print '\tExpected : false'
        return -1

    if not inst.isControlFlow():
        count += 1
    else:
        print '[KO] inst.isControlFlow()'
        print '\tOutput   : %d' %(inst.isControlFlow())
        print '\tExpected : false'
        return -1

    if not inst.isConditionTaken():
        count += 1
    else:
        print '[KO] inst.isConditionTaken()'
        print '\tOutput   : %d' %(inst.isConditionTaken())
        print '\tExpected : false'
        return -1

    if not inst.isBranch():
        count += 1
    else:
        print '[KO] inst.isBranch()'
        print '\tOutput   : %d' %(inst.isBranch())
        print '\tExpected : false'

    if inst.getType() == OPCODE.ADD:
        count += 1
    else:
        print '[KO] inst.getType()'
        print '\tOutput   : %d' %(inst.getType())
        print '\tExpected : OPCODE.ADD'
        return -1

    if inst.getThreadId() == 0:
        count += 1
    else:
        print '[KO] inst.getThreadId()'
        print '\tOutput   : %d' %(inst.getThreadId())
        print '\tExpected : 0'
        return -1

    try:
        inst.getThirdOperand()
        print '[KO] inst.getThirdOperand()'
        print '\tOutput   : %s' %(inst.getThirdOperand())
        print '\tExpected : <exception>'
        return -1
    except:
        count += 1

    if len(inst.getSymbolicExpressions()) == 8:
        count += 1
    else:
        print '[KO] inst.getSymbolicExpressions()'
        print '\tOutput   : %d' %(inst.getSymbolicExpressions())
        print '\tExpected : 8 expressions'
        return -1

    if inst.getSize() == 3:
        count += 1
    else:
        print '[KO] inst.getSize()'
        print '\tOutput   : %d' %(inst.getSize())
        print '\tExpected : 3'
        return -1

    if inst.getFirstOperand().getName() == 'rax':
        count += 1
    else:
        print '[KO] inst.getFirstOperand().getName()'
        print '\tOutput   : %s' %(inst.getFirstOperand().getName())
        print '\tExpected : rax'
        return -1

    if inst.getSecondOperand().getName() == 'rbx':
        count += 1
    else:
        print '[KO] inst.getSecondOperand().getName()'
        print '\tOutput   : %s' %(inst.getSecondOperand().getName())
        print '\tExpected : rbx'
        return -1

    if inst.getDisassembly() == 'add rax, rbx':
        count += 1
    else:
        print '[KO] inst.getDisassembly()'
        print '\tOutput   : %s' %(inst.getDisassembly())
        print '\tExpected : add rax, rbx'
        return -1

    if inst.getNextAddress() == 0x400003:
        count += 1
    else:
        print '[KO] inst.getNextAddress()'
        print '\tOutput   : 0x%x' %(inst.getNextAddress())
        print '\tExpected : 0x400003'
        return -1

    if inst.getOpcodes() == "\x48\x01\xd8":
        count += 1
    else:
        print '[KO] inst.getOpcodes()'
        print '\tOutput   : %s' %(repr(inst.getOpcodes()))
        print '\tExpected : \\x48\\x01\\xd8'
        return -1

    if len(inst.getOperands()) == 2:
        count += 1
    else:
        print '[KO] len(inst.getOperands())'
        print '\tOutput   : %s' %(len(inst.getOperands()))
        print '\tExpected : 2'
        return -1

    if inst.getPrefix() == PREFIX.INVALID:
        count += 1
    else:
        print '[KO] inst.getPrefix()'
        print '\tOutput   : %d' %(inst.getPrefix())
        print '\tExpected : PREFIX.INVALID'
        return -1

    return count


def test_6():
    count = 0
    try:
        setArchitecture(ARCH.X86_64)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86_64)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86_64)
        setArchitecture(ARCH.X86_64)
        setArchitecture(ARCH.X86_64)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86)
        setArchitecture(ARCH.X86_64)
        count += 1
    except:
        print '[KO] Chaining multiple setArchitecture()'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1

    setArchitecture(ARCH.X86_64)
    try:
        tmp = REG.RAX
        count += 1
    except:
        print '[KO] REG.RAX not found (64-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1

    try:
        tmp = REG.ZMM1
        count += 1
    except:
        print '[KO] REG.ZMM1 not found (64-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1

    try:
        tmp = REG.XMM15
        count += 1
    except:
        print '[KO] REG.XMM15 not found (64-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1

    setArchitecture(ARCH.X86)
    try:
        tmp = REG.RAX
        print '[KO] REG.RAX found (32-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1
    except:
        count += 1

    try:
        tmp = REG.ZMM1
        print '[KO] REG.ZMM1 found (32-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1
    except:
        count += 1

    try:
        tmp = REG.XMM8
        print '[KO] REG.XMM8 found (32-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1
    except:
        count += 1

    try:
        tmp = REG.XMM15
        print '[KO] REG.XMM15 found (32-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1
    except:
        count += 1

    try:
        tmp = REG.XMM7
        count += 1
    except:
        print '[KO] REG.XMM7 not found (32-bits)'
        print '\tOutput   : <exception>'
        print '\tExpected : <nothing>'
        return -1

    return count



units_testing = [
    ("Testing the arithmetic and logic AST interpreter", test_1),
    ("Testing the RegisterOperand class", test_2),
    ("Testing the MemoryOperand class", test_3),
    ("Testing the ImmediateOperand class", test_4),
    ("Testing the Instruction class", test_5),
    ("Testing the architectures", test_6),
]


if __name__ == '__main__':
    count = 0
    for n, f in units_testing:
        ret = f()
        if ret < 0:
            print '[KO]\t%s' %(n)
            sys.exit(-1)
        else:
            count += ret
            print '[OK]\t%s' %(n)
    print '[GOOD]\t%d tests were been executed successfully :-)' %(count)
    sys.exit(0)

