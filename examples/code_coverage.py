#!/usr/bin/python2.7
# -*- coding: utf-8 -*-

# $ triton $PIN_ROOT/source/tools/Triton/examples/code_coverage.py $PIN_ROOT/source/tools/Triton/samples/others/code_coverage a
# TODO : convertToSymVar, retturn the symvar
from triton import *
import smt2lib

class Node:
    def __init__(self, instruction):
        #self.num = 0
        self.instruction = instruction
        self.if_true = None
        self.if_false = None
        self.true_v = False
        self.false_v = False
        self.expr = None
        self.symVars = dict()


cond = dict()
addrCmp = dict()
addrDone = []
workList = []
def csym(instruction):
    global addrCmp
    global workList

    if instruction.opcode == IDREF.OPCODE.CMP and instruction.address not in addrCmp: # we are one a cmp
        print "[+] New cmp instr"
        for op in instruction.operands:
            if op.type == IDREF.OPERAND.MEM_R:
                addr = op.value
                sid = convertMemToSymVar(addr, IDREF.CPUSIZE.QWORD, "addr")
                n = Node(instruction)
                addrCmp[instruction.address] = n
        print instruction.assembly
        print "[+] Add node to the work list"
        workList.append(n)


    return

def cafter(instruction):

    global addrCmp
    global workList

    if instruction.opcode == IDREF.OPCODE.CMP:
        zfValue = getFlagValue(IDREF.FLAG.ZF)
        node = addrCmp[instruction.address]

        node.true_v = True if zfValue == 1 else False
        node.true_f = True if zfValue == 0 else False

        if node.if_true is None:
            zfId    = getRegSymbolicID(IDREF.FLAG.ZF)
            zfExpr  = getBacktrackedSymExpr(zfId)
            node.expr = zfExpr if node.expr is None else None
            expr    = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvtrue())) # (assert (= zf True))
            models  = getModel(expr)
            node.if_true = dict()
            for k, v in models.items():
                sm = getSymVar(k)
                addr = sm.kindValue
                node.if_true[addr] = v


        if node.if_false is None:
            zfId    = getRegSymbolicID(IDREF.FLAG.ZF)
            zfExpr  = getBacktrackedSymExpr(zfId)
            node.expr = zfExpr if node.expr is None else None
            expr    = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvfalse())) # (assert (= zf False))
            models  = getModel(expr)
            node.if_false = dict()
            for k, v in models.items():
                sm = getSymVar(k)
                addr = sm.kindValue
                node.if_false[addr] = v

        return


    return


def cbefore(instruction):

    if instruction.address == 0x400513:
        print "BB1"
        return
    if instruction.address == 0x400522:
        print "BB2"
        return

    if instruction.address == 0x400532:
        print "BB3"
        return



    if instruction.address == 0x400506 and not isSnapshotEnable():
        takeSnapshot()
        print "[+] Take a snapshot at the prologue of the function"
        return

    if instruction.address == 0x40053B and len(workList) == 0:
        print '[+] We coveraged all graph'
        disableSnapshot()
        return


    if instruction.address == 0x40053B:
        #print workList
        n = workList.pop()

        #print "[+] We set %x to %d"%(addr, v)
        #setMemValue(addr, IDREF.CPUSIZE.QWORD, v)
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


