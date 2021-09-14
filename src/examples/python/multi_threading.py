#!/usr/bin/env python
## -*- coding: utf-8 -*-

from triton import *


class ThreadContext(object):
    def __init__(self, tid):
        self.cregs  = dict() # context of concrete registers
        self.sregs  = dict() # context of symbolic registers
        self.tid    = tid    # The thread id

    def save(self, ctx):
        # Save symbolic registers
        self.sregs = ctx.getSymbolicRegisters()
        # Save concrete registers
        for r in ctx.getParentRegisters():
            self.cregs.update({r.getId(): ctx.getConcreteRegisterValue(r)})


    def restore(self, ctx):
        # Restore concrete registers
        for rid, v in self.cregs.items():
            ctx.setConcreteRegisterValue(ctx.getRegister(rid), v)
        # Restore symbolic registers
        for rid, e in self.sregs.items():
            ctx.assignSymbolicExpressionToRegister(e, ctx.getRegister(rid))


if __name__ == "__main__":
    thread0 = [
        b"\xb8\x03\x00\x00\x00",    # mov eax, 3
        b"\x89\xc3",                # mov ebx, eax
    ]
    thread1 = [
        b"\xb8\x04\x00\x00\x00",    # mov eax, 4
    ]

    # The Triton context
    ctx = TritonContext(ARCH.X86)
    th0 = ThreadContext(0)
    th1 = ThreadContext(1)

    th0.save(ctx) # save the initial state of the thread 0
    th1.save(ctx) # save the initial state of the thread 1

    # Execute instructions of the thread 0
    for inst in thread0:
        ctx.processing(Instruction(inst))

    # Save the state of the thread 0 and restore the state of thread 1
    th0.save(ctx)
    th1.restore(ctx)

    # Execute instructions of the thread 1
    for inst in thread1:
        ctx.processing(Instruction(inst))

    # Save the state of the thread 1 and restore the state of the thread 0
    th1.save(ctx)
    th0.restore(ctx)

    print(f"Thread {th0.tid}: eax = {th0.cregs[REG.X86.EAX]}")
    print(f"Thread {th0.tid}: ebx = {th0.cregs[REG.X86.EBX]}")
    print(f"Thread {th1.tid}: eax = {th1.cregs[REG.X86.EAX]}")
    print(f"Thread {th1.tid}: ebx = {th1.cregs[REG.X86.EBX]}")
