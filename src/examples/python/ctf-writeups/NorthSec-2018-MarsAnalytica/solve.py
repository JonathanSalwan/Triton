#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2022-05-29
##
##  Solving the NorthSec 2018 MarsAnalytica (Virtual Machine) challenge.
##
##  Output:
##
##  $ time python solve.py
##  [+] Define registers
##  [+] Define memory areas
##  [+] Define memory 400000-e5e000
##  [+] Define memory e5e000-105d000
##  [+] Define memory 105d000-105e000
##  [+] Define memory 105e000-1080000
##  [+] Define memory 7ffff7da8000-7ffff7daa000
##  [+] Define memory 7ffff7daa000-7ffff7dd2000
##  [+] Define memory 7ffff7dd2000-7ffff7f3d000
##  [+] Define memory 7ffff7f3d000-7ffff7f94000
##  [+] Define memory 7ffff7f94000-7ffff7f95000
##  [+] Define memory 7ffff7f95000-7ffff7f99000
##  [+] Define memory 7ffff7f99000-7ffff7f9b000
##  [+] Define memory 7ffff7f9b000-7ffff7fa5000
##  [+] Define memory 7ffff7fc5000-7ffff7fc6000
##  [+] Define memory 7ffff7fc6000-7ffff7feb000
##  [+] Define memory 7ffff7feb000-7ffff7ff5000
##  [+] Define memory 7ffff7ff5000-7ffff7ff7000
##  [+] Define memory 7ffff7ff7000-7ffff7ff9000
##  [+] Define memory 7ffff7ff9000-7ffff7ffd000
##  [+] Define memory 7ffff7ffd000-7ffff7fff000
##  [+] Define memory 7ffffff42000-7ffffffff000
##  [+] Define memory ffffffffff600000-ffffffffff601000
##  [+] Hijack .plt @0x105E018 -> __free
##  [+] Hijack .plt @0x105E020 -> __putchar
##  [+] Hijack .plt @0x105E040 -> __getchar
##  [+] Hijack .plt @0x105E058 -> __malloc
##  [+] Hijack .plt @0x105E060 -> __fflush
##  [+] Hijack .plt @0x105E029 -> __puts
##  [+] Starting emulation
##  [+] 100,000 instructions executed
##  [+] 200,000 instructions executed
##  [+] 300,000 instructions executed
##  [+] 400,000 instructions executed
##  [+] 500,000 instructions executed
##  [+] 600,000 instructions executed
##  [+] 700,000 instructions executed
##  [+] Serial in construction: ",000007000$0P/c00@0"
##  [+] Serial in construction: "0@`xP@-@``DAp'!``@3"
##  [+] 800,000 instructions executed
##  [+] 900,000 instructions executed
##  [+] 1,000,000 instructions executed
##  [+] Serial in construction: "`:@``A7P`B0``9!yE+@"
##  [+] Serial in construction: "hP`MP(7!@c(BX3co[AM"
##  [+] Serial in construction: "A)<;7A-`pa@0m&!zZ@`"
##  [+] 1,100,000 instructions executed
##  [+] 1,200,000 instructions executed
##  [+] 1,300,000 instructions executed
##  [+] Serial in construction: "b(S;$@yAtA00n=-`?%d"
##  [+] Serial in construction: "e17~,C-^`C@sz1!|T:|"
##  [+] 1,400,000 instructions executed
##  [+] Serial in construction: "`0A{"`!W`##ppD7rqWx"
##  [+] Serial in construction: "a=Bd"^yMg$-Y`0-kjPp"
##  [+] Serial in construction: "o7Pz$d!>w(*oX'7]bH{"
##  [+] Serial in construction: "o=:H5Tc_l83=zB!ylRt"
##  [+] 1,500,000 instructions executed
##  [+] Serial in construction: "{?@X+cc>h55MyA!s^DY"
##  [+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
##  [+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
##  [+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
##  [+] 1,600,000 instructions executed
##  [+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
##  [+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
##  [+] End point reached
##  [+] Final serial found: q4Eo-eyMq-1dd0-leKx
##  [+] Emulation done
##  [+] Going further than just solving the challenge
##  [+] Lifting the path predicate to LLVM
##
##  ; ModuleID = 'tritonModule'
##  source_filename = "tritonModule"
##
##  ; Function Attrs: mustprogress nofree norecurse nosync nounwind readnone willreturn
##  define i1 @mars_analytica(i8 %SymVar_0, i8 %SymVar_1, i8 %SymVar_4, i8 %SymVar_3, i8 %SymVar_2, i8 %SymVar_7, i8 %SymVar_6, i8 %SymVar_5, i8 %SymVar_11, i8 %SymVar_8, i8 %SymVar_9, i8 %SymVar_10, i8 %SymVar_14, i8 %SymVar_12, i8 %SymVar_13, i8 %SymVar_15, i8 %SymVar_16, i8 %SymVar_18, i8 %SymVar_17) local_unnamed_addr #0 {
##  entry:
##    %0 = zext i8 %SymVar_13 to i32
##    %1 = zext i8 %SymVar_5 to i32
##    %2 = add nuw nsw i32 %0, %1
##    %3 = zext i8 %SymVar_16 to i32
##    %4 = mul nuw nsw i32 %2, %3
##    %.not = icmp eq i32 %4, 15049
##    %5 = zext i8 %SymVar_15 to i32
##    %6 = zext i8 %SymVar_3 to i32
##    %7 = mul nuw nsw i32 %5, %6
##    %8 = zext i8 %SymVar_2 to i32
##    %9 = zext i8 %SymVar_11 to i32
##    %10 = mul nuw nsw i32 %9, %8
##    %narrow = add nuw nsw i32 %7, %10
##    %.not1 = icmp eq i32 %narrow, 18888
##    %11 = zext i8 %SymVar_4 to i32
##    %12 = zext i8 %SymVar_18 to i32
##    %13 = mul nuw nsw i32 %12, %11
##    %14 = zext i8 %SymVar_12 to i32
##    %15 = sub nsw i32 %5, %14
##    %.neg = add nsw i32 %15, %13
##    %.not2 = icmp eq i32 %.neg, 5408
##    %16 = zext i8 %SymVar_6 to i32
##    %17 = mul nuw nsw i32 %9, %16
##    %18 = zext i8 %SymVar_1 to i32
##    %19 = mul nuw nsw i32 %6, %18
##    %narrow3 = add nuw nsw i32 %17, %19
##    %.not4 = icmp eq i32 %narrow3, 17872
##    %20 = xor i8 %SymVar_14, %SymVar_7
##    %21 = zext i8 %20 to i32
##    %22 = zext i8 %SymVar_17 to i32
##    %23 = mul nuw nsw i32 %22, %21
##    %.not5 = icmp eq i32 %23, 7200
##    %24 = zext i8 %SymVar_0 to i32
##    %25 = add nuw nsw i32 %8, %24
##    %26 = sub nsw i32 %25, %1
##    %.neg6 = add nsw i32 %26, %3
##    %.not7 = icmp eq i32 %.neg6, 182
##    %27 = zext i8 %SymVar_9 to i32
##    %28 = zext i8 %SymVar_10 to i32
##    %29 = zext i8 %SymVar_8 to i32
##    %30 = mul nuw nsw i32 %28, %29
##    %31 = add nuw nsw i32 %30, %27
##    %narrow8 = add nuw nsw i32 %31, %0
##    %.not9 = icmp eq i32 %narrow8, 5630
##    %32 = add nuw nsw i32 %6, %14
##    %.neg10 = sub nsw i32 %1, %32
##    %.not11 = icmp eq i32 %.neg10, -110
##    %33 = zext i8 %SymVar_7 to i32
##    %34 = zext i8 %SymVar_14 to i32
##    %35 = mul nuw nsw i32 %0, %34
##    %.neg12 = sub nsw i32 %33, %35
##    %.not13 = icmp eq i32 %.neg12, -2083
##    %36 = mul nuw nsw i32 %3, %8
##    %37 = xor i8 %SymVar_17, %SymVar_0
##    %38 = zext i8 %37 to i32
##    %39 = mul nuw nsw i32 %38, %18
##    %narrow14 = add nuw nsw i32 %39, %36
##    %.not15 = icmp eq i32 %narrow14, 9985
##    %40 = xor i8 %SymVar_10, %SymVar_9
##    %41 = zext i8 %40 to i32
##    %42 = add nuw nsw i32 %9, %12
##    %43 = sub nsw i32 %41, %42
##    %44 = xor i32 %43, %16
##    %.not16 = icmp eq i32 %44, -199
##    %45 = sub nsw i32 %29, %11
##    %46 = add nsw i32 %45, %5
##    %.not19 = icmp eq i32 %46, 176
##    %47 = add nuw nsw i32 %8, %11
##    %48 = xor i32 %47, %29
##    %.not20 = icmp eq i32 %48, 3
##    %.neg21 = sub nsw i32 %9, %6
##    %.not22 = icmp eq i32 %.neg21, -11
##    %.neg23 = sub nsw i32 %3, %22
##    %49 = add nuw nsw i32 %27, %1
##    %50 = xor i32 %49, %24
##    %.neg24 = mul nsw i32 %.neg23, %50
##    %.not25 = icmp eq i32 %.neg24, 5902
##    %51 = sub nsw i32 %5, %33
##    %52 = xor i8 %SymVar_18, %SymVar_1
##    %53 = zext i8 %52 to i32
##    %54 = xor i32 %51, %53
##    %.not26 = icmp eq i32 %54, 83
##    %55 = mul nuw nsw i32 %34, %16
##    %56 = sub nsw i32 %14, %28
##    %57 = xor i32 %56, %0
##    %58 = mul nsw i32 %55, %57
##    %.not27 = icmp eq i32 %58, 16335
##    %SymVar_18.off = add i8 %SymVar_18, -33
##    %59 = icmp ult i8 %SymVar_18.off, 94
##    %SymVar_17.off = add i8 %SymVar_17, -33
##    %60 = icmp ult i8 %SymVar_17.off, 94
##    %SymVar_16.off = add i8 %SymVar_16, -33
##    %61 = icmp ult i8 %SymVar_16.off, 94
##    %SymVar_15.off = add i8 %SymVar_15, -33
##    %62 = icmp ult i8 %SymVar_15.off, 94
##    %SymVar_14.off = add i8 %SymVar_14, -33
##    %63 = icmp ult i8 %SymVar_14.off, 94
##    %SymVar_13.off = add i8 %SymVar_13, -33
##    %64 = icmp ult i8 %SymVar_13.off, 94
##    %SymVar_12.off = add i8 %SymVar_12, -33
##    %65 = icmp ult i8 %SymVar_12.off, 94
##    %SymVar_11.off = add i8 %SymVar_11, -33
##    %66 = icmp ult i8 %SymVar_11.off, 94
##    %SymVar_10.off = add i8 %SymVar_10, -33
##    %67 = icmp ult i8 %SymVar_10.off, 94
##    %SymVar_9.off = add i8 %SymVar_9, -33
##    %68 = icmp ult i8 %SymVar_9.off, 94
##    %SymVar_8.off = add i8 %SymVar_8, -33
##    %69 = icmp ult i8 %SymVar_8.off, 94
##    %SymVar_7.off = add i8 %SymVar_7, -33
##    %70 = icmp ult i8 %SymVar_7.off, 94
##    %SymVar_6.off = add i8 %SymVar_6, -33
##    %71 = icmp ult i8 %SymVar_6.off, 94
##    %SymVar_5.off = add i8 %SymVar_5, -33
##    %72 = icmp ult i8 %SymVar_5.off, 94
##    %SymVar_4.off = add i8 %SymVar_4, -33
##    %73 = icmp ult i8 %SymVar_4.off, 94
##    %SymVar_3.off = add i8 %SymVar_3, -33
##    %74 = icmp ult i8 %SymVar_3.off, 94
##    %SymVar_2.off = add i8 %SymVar_2, -33
##    %75 = icmp ult i8 %SymVar_2.off, 94
##    %SymVar_1.off = add i8 %SymVar_1, -33
##    %76 = icmp ult i8 %SymVar_1.off, 94
##    %SymVar_0.off = add i8 %SymVar_0, -33
##    %77 = icmp ult i8 %SymVar_0.off, 94
##    %78 = and i1 %77, %76
##    %79 = and i1 %78, %75
##    %80 = and i1 %74, %79
##    %81 = and i1 %73, %80
##    %82 = and i1 %81, %72
##    %83 = and i1 %71, %82
##    %84 = and i1 %70, %83
##    %85 = and i1 %69, %84
##    %86 = and i1 %68, %85
##    %87 = and i1 %67, %86
##    %88 = and i1 %66, %87
##    %89 = and i1 %65, %88
##    %90 = and i1 %64, %89
##    %91 = and i1 %63, %90
##    %92 = and i1 %62, %91
##    %93 = and i1 %61, %92
##    %94 = and i1 %60, %93
##    %95 = and i1 %59, %94
##    %96 = and i1 %77, %95
##    %97 = and i1 %76, %96
##    %98 = and i1 %75, %97
##    %99 = and i1 %74, %98
##    %100 = and i1 %73, %99
##    %101 = and i1 %72, %100
##    %102 = and i1 %71, %101
##    %103 = and i1 %70, %102
##    %104 = and i1 %69, %103
##    %105 = and i1 %68, %104
##    %106 = and i1 %67, %105
##    %107 = and i1 %66, %106
##    %108 = and i1 %65, %107
##    %109 = and i1 %64, %108
##    %110 = and i1 %63, %109
##    %111 = and i1 %62, %110
##    %112 = and i1 %61, %111
##    %113 = and i1 %60, %112
##    %114 = and i1 %59, %113
##    %115 = and i1 %.not27, %114
##    %116 = and i1 %.not26, %115
##    %117 = and i1 %.not25, %116
##    %118 = and i1 %.not22, %117
##    %119 = and i1 %.not20, %118
##    %120 = and i1 %.not19, %119
##    %121 = and i1 %.not16, %120
##    %122 = and i1 %.not15, %121
##    %123 = and i1 %.not13, %122
##    %124 = and i1 %.not11, %123
##    %125 = and i1 %.not9, %124
##    %126 = and i1 %.not7, %125
##    %127 = and i1 %.not5, %126
##    %128 = and i1 %.not4, %127
##    %129 = and i1 %.not2, %128
##    %130 = and i1 %.not1, %129
##    %131 = and i1 %.not, %130
##    ret i1 %131
##  }
##
##  attributes #0 = { mustprogress nofree norecurse nosync nounwind readnone willreturn }
##
##  python solve.py  136.84s user 0.56s system 99% cpu 2:17.53 total
##

from __future__ import print_function
from triton     import *

import string
import sys
import lief
import os

DEBUG = False
def debug(s):
    if DEBUG: print(s)

# Memory mapping
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9fffffff

# Global settings
SYMBOLIC = True
CONCRETE = not SYMBOLIC
CHAR_CNT = 0

# Allocation information used by malloc()
mallocCurrentAllocation = 0
mallocMaxAllocation     = 2048
mallocBase              = BASE_ALLOC
mallocChunkSize         = 0x00010000


def __free(ctx):
    debug('[+] __free hooked')
    # Do not care about free :)
    return (CONCRETE, None)


def __putchar(ctx):
    debug('[+] __putchar hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1))

    return (CONCRETE, 1)


def __getchar(ctx):
    global CHAR_CNT
    debug('[+] __getchar hooked, returning a symbolic variable')
    # The target uses getchar several times to read each character
    # of the serial input. So we will symbolize the return of this
    # function. We also return as a concrete value the character
    # 'A' 19 times and then '\n'. This is basically the size of
    # serial.
    ret = (0x0a if CHAR_CNT == 19 else 0x41)
    CHAR_CNT +=1
    return (SYMBOLIC, ret)


# Minimalist alloc implementation.
def __malloc(ctx):
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    debug('[+] __malloc hooked')

    # Get arguments
    size = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    if size > mallocChunkSize:
        debug('[-] malloc failed: size too big')
        sys.exit(-1)

    if mallocCurrentAllocation >= mallocMaxAllocation:
        debug('[-] malloc failed: too many allocations done')
        sys.exit(-1)

    area = mallocBase + (mallocCurrentAllocation * mallocChunkSize)
    mallocCurrentAllocation += 1

    # Return value
    return (CONCRETE, area)


def __fflush(ctx):
    debug('[+] __fflush hooked')
    # Assuming it's stdout :)
    sys.stdout.flush()
    return (CONCRETE, None)


def getMemoryString(ctx, addr):
    s = str()
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def __puts(ctx):
    debug('[+] __puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return (CONCRETE, len(arg1) + 1)


# Routine to emulate
customRelocation = [
    ['__free',      __free,     BASE_PLT + 1],
    ['__putchar',   __putchar,  BASE_PLT + 2],
    ['__getchar',   __getchar,  BASE_PLT + 3],
    ['__malloc',    __malloc,   BASE_PLT + 4],
    ['__fflush',    __fflush,   BASE_PLT + 5],
    ['__puts',      __puts,     BASE_PLT + 6],
]


def routineHandler(ctx):
    pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            state, ret_value = rel[1](ctx)
            if ret_value is not None:
                ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)
                if state is SYMBOLIC:
                    ast = ctx.getAstContext()
                    var = ctx.symbolizeRegister(ctx.registers.al)
                    ctx.pushPathConstraint(ast.land([ast.variable(var) > 0x20, ast.variable(var) < 0x7f]))
            # Get the return address
            ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))
            # Hijack RIP to skip the call
            ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)
            # Restore RSP (simulate the ret)
            ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
    return


def symbolicBranch(ctx):
    serial = bytearray(19)
    ast    = ctx.getAstContext()
    pred   = ctx.getPathPredicate()
    zf     = ctx.getRegisterAst(ctx.registers.zf)

    model, status, _ = ctx.getModel(ast.land([pred, zf == 1]), status=True)
    if status == SOLVER_STATE.SAT:
        for k, v in sorted(model.items()):
            serial[k] = v.getValue()
            ctx.setConcreteVariableValue(v.getVariable(), v.getValue())
        print(f'[+] Serial in construction: "{serial.decode()}"')

    return serial


# Emulate the binary code.
def emulate(ctx, pc):
    count = 0
    serial = None
    while pc:
        # Fetch opcodes
        opcodes = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction(pc, opcodes)
        ctx.processing(instruction)

        count += 1
        if count % 100000 == 0:
            print(f'[+] {count:,} instructions executed')

        if instruction.isSymbolized() and instruction.getType() == OPCODE.X86.CMP:
            serial = symbolicBranch(ctx)

        elif instruction.getType() == OPCODE.X86.HLT or instruction.getAddress() == 0xc4d42a:
            print(f'[+] End point reached')
            print(f'[+] Final serial found: {serial.decode()}')
            break

        # Simulate routines
        routineHandler(ctx)

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    return serial


# As we dumped the memory, the plt has already been linked to libc.
# We patch the PLT to hijack control flow to our own routines.
def patchPLT(ctx):
    print('[+] Hijack .plt @0x105E018 -> __free')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E018, CPUSIZE.QWORD), BASE_PLT + 1)

    print('[+] Hijack .plt @0x105E020 -> __putchar')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E020, CPUSIZE.QWORD), BASE_PLT + 2)

    print('[+] Hijack .plt @0x105E040 -> __getchar')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E040, CPUSIZE.QWORD), BASE_PLT + 3)

    print('[+] Hijack .plt @0x105E058 -> __malloc')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E058, CPUSIZE.QWORD), BASE_PLT + 4)

    print('[+] Hijack .plt @0x105E060 -> __fflush')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E060, CPUSIZE.QWORD), BASE_PLT + 5)

    print('[+] Hijack .plt @0x105E029 -> __puts')
    ctx.setConcreteMemoryValue(MemoryAccess(0x105E028, CPUSIZE.QWORD), BASE_PLT + 6)
    return


def run(ctx):
    print('[+] Starting emulation')
    serial = emulate(ctx, ctx.getConcreteRegisterValue(ctx.registers.rip))
    print('[+] Emulation done')
    return serial


def loadDump(ctx, path):
    # Open the dump
    fd = open(path)
    data = eval(fd.read())
    fd.close()

    # Extract registers and memory
    regs = data[0]
    mems = data[1]

    # Load registers and memory into the libctx
    print('[+] Define registers')
    ctx.setConcreteRegisterValue(ctx.registers.rax,    regs['rax'])
    ctx.setConcreteRegisterValue(ctx.registers.rbx,    regs['rbx'])
    ctx.setConcreteRegisterValue(ctx.registers.rcx,    regs['rcx'])
    ctx.setConcreteRegisterValue(ctx.registers.rdx,    regs['rdx'])
    ctx.setConcreteRegisterValue(ctx.registers.rdi,    regs['rdi'])
    ctx.setConcreteRegisterValue(ctx.registers.rsi,    regs['rsi'])
    ctx.setConcreteRegisterValue(ctx.registers.rbp,    regs['rbp'])
    ctx.setConcreteRegisterValue(ctx.registers.rsp,    regs['rsp'])
    ctx.setConcreteRegisterValue(ctx.registers.rip,    regs['rip'])
    ctx.setConcreteRegisterValue(ctx.registers.r8,     regs['r8'])
    ctx.setConcreteRegisterValue(ctx.registers.r9,     regs['r9'])
    ctx.setConcreteRegisterValue(ctx.registers.r10,    regs['r10'])
    ctx.setConcreteRegisterValue(ctx.registers.r11,    regs['r11'])
    ctx.setConcreteRegisterValue(ctx.registers.r12,    regs['r12'])
    ctx.setConcreteRegisterValue(ctx.registers.r13,    regs['r13'])
    ctx.setConcreteRegisterValue(ctx.registers.r14,    regs['r14'])
    ctx.setConcreteRegisterValue(ctx.registers.eflags, regs['eflags'])

    print('[+] Define memory areas')
    for mem in mems:
        start = mem['start']
        end   = mem['end']
        print('[+] Define memory %x-%x' %(start, end))
        if mem['memory']:
            ctx.setConcreteMemoryAreaValue(start, mem['memory'])

    return


def lifting2llvm(ctx):
    predicate = ctx.getPathPredicate()
    M = ctx.liftToLLVM(predicate, fname="mars_analytica", optimize=True)
    print('[+] Going further than just solving the challenge')
    print('[+] Lifting the path predicate to LLVM')
    print()
    print(M)
    return


def main():
    # Get a Triton context
    ctx = TritonContext(ARCH.X86_64)

    # Set optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx.setMode(MODE.CONSTANT_FOLDING, True)
    ctx.setMode(MODE.ONLY_ON_SYMBOLIZED, True)
    ctx.setMode(MODE.AST_OPTIMIZATIONS, True)

    # Load the meory dump
    loadDump(ctx, os.path.join(os.path.dirname(__file__), "fulldump.dump"))

    # Perform our own relocations
    patchPLT(ctx)

    # Init and emulate
    serial = run(ctx)

    # Going further than just solving the challenge
    # Lifting the path predicate to LLVM
    if VERSION.LLVM_INTERFACE is True:
        lifting2llvm(ctx)

    # Used as unittest
    return not serial == b'q4Eo-eyMq-1dd0-leKx'


if __name__ == '__main__':
    retValue = main()
    sys.exit(retValue)
