#!/usr/bin/python2.7
# -*- coding: utf-8 -*-

# $ triton $PIN_ROOT/source/tools/Triton/examples/code_coverage.py $PIN_ROOT/source/tools/Triton/samples/others/code_coverage a
# TODO : convertToSymVar, retturn the symvar
from triton import *
import smt2lib

sidVar = []
todo = []
done = []
def csym(instruction):
    if instruction.address == 0x400575:

        addr = getRegValue(IDREF.REG.RBP) - 0x18 # point on passwd input
        pointeur = getMemValue(addr, IDREF.CPUSIZE.QWORD)

        for i in range(8):
            print "We set %x to symvar"%(pointeur + i)
            sid = convertMemToSymVar(pointeur + i, IDREF.CPUSIZE.BYTE, "addr_%d"%i)
            sidVar.append(sid)

        if len(todo) != 0:
            addr,value = todo.pop()
            print "We inject %d in %x"%(value,addr)
            setMemValue(addr, IDREF.CPUSIZE.QWORD, value)
            done.append((addr,value))








    return

def cafter(instruction):
    if instruction.address == 0x40058B:


        addr = getRegValue(IDREF.REG.RBP) - 0x18 # point on passwd input
        pointeur = getMemValue(addr, IDREF.CPUSIZE.QWORD)
        s = getSymVar(sidVar[0])
        #print getBacktrackedSymExpr(s.id)
        rax = getRegValue(IDREF.REG.RAX)
        print "RAX = %x"%rax


        #print map(hex,sidVar)
        rax = getRegValue(IDREF.REG.RAX)
        #raxId   = getRegSymbolicID(IDREF.REG.RAX)
        raxId = sidVar[0]
        print getSymVar(raxId).comment
        raxExpr = getBacktrackedSymExpr(raxId)
        #print raxExpr
        expr    = smt2lib.smtAssert(smt2lib.equal(raxExpr, smt2lib.bv(8, 8))) # (assert (= zf True))
        models  = getModel(expr)
        #print "hello"
        for k, v in models.items():
            s = getSymVar(k)
            print "\t",s.comment,v
                    #restoreSnapshot(

    return


def cbefore(instruction):
    if instruction.address == 0x4005BD:
        addr = getRegValue(IDREF.REG.RBP) - 0x18 # point on passwd input
        pointeur = getMemValue(addr, IDREF.CPUSIZE.QWORD)
        s = getSymVar(sidVar[0])
        print getBacktrackedSymExpr(s.id)
        #rax = getRegValue(IDREF.REG.RAX)
        #print "RAX = %x"%rax
    if instruction.isBranch:
        print instruction.assembly
        for operand in instruction.operands:
            next_addr_1 = operand.value
        next_addr_2 = getRegValue(IDREF.REG.RIP) + 2
        print "Two ways :"
        print "\t RIP = 0x%x"%next_addr_2
        print "\t RIP = 0x%x"%next_addr_1
        ripId   = getRegSymbolicID(IDREF.REG.RIP)
        ripExpr = getBacktrackedSymExpr(ripId)
        expr    = smt2lib.smtAssert(smt2lib.equal(ripExpr, smt2lib.bv(next_addr_1, 64))) # (assert (= zf True))
        models  = getModel(expr)
        #print "hello"
        for k, v in models.items():
            s = getSymVar(k)
            if s.kind == IDREF.SYMVAR.MEM:
                if (s.kindValue, v) not in done:
                    print "To take the first branch:"
                    todo.append((s.kindValue, v))
                    s = getSymVar(k)
                    print "\t",s.comment,v
                    #restoreSnapshot()

        ripExpr = getBacktrackedSymExpr(ripId)
        expr    = smt2lib.smtAssert(smt2lib.equal(ripExpr, smt2lib.bv(next_addr_2, 64))) # (assert (= zf True))
        models  = getModel(expr)
        #print "hello"

        for k, v in models.items():
            if s.kind == IDREF.SYMVAR.MEM:
                if (s.kindValue, v) not in done:
                    print "To take the 2nd branch:"
                    todo.append((s.kindValue, v))
                    s = getSymVar(k)
                    print "\t",s.comment,v
                    #restoreSnapshot()


    if instruction.address == 0x4005B2:
        print "BB1"
        return
    if instruction.address == 0x4005C3:
        print "BB2"
        return

    if instruction.address == 0x4005B9:
        print "BB3"
        return






    if instruction.address == 0x40056D and not isSnapshotEnable():
        takeSnapshot()
        return



    if instruction.address == 0x4005C8:
        #restoreSnapshot()
        return
        #restoreSnapshot()

    return



def fini():
    #print addrCmp
    print '[+] Done !'


if __name__=='__main__':

    # Start the symbolic analysis from the entry point
    startAnalysisFromSymbol('check')

    addCallback(cafter,         IDREF.CALLBACK.AFTER)
    addCallback(cbefore,        IDREF.CALLBACK.BEFORE)
    addCallback(csym,           IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(fini,           IDREF.CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()


