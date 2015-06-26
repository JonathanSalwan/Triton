#!/usr/bin/python2.7
# -*- coding: utf-8 -*-

# $ triton $PIN_ROOT/source/tools/Triton/examples/code_coverage.py $PIN_ROOT/source/tools/Triton/samples/others/code_coverage a

from triton import *
import smt2lib

class Node:
    def __init__(self, instruction):
        #self.num = 0
        self.instruction = instruction
        self.if_true = None
        self.if_false = None
        self.expr = None


cond = dict()
t = dict()
f = dict()
addrCmp = dict()
addrDone = []
workList = []
def csym(instruction):
    global addrCmp

    if instruction.opcode == IDREF.OPCODE.CMP and instruction.address not in addrCmp: # we are one a cmp
        print "[+] New cmp instr"
        for op in instruction.operands:
            if op.type == IDREF.OPERAND.MEM_R:
                addr = op.value
                sid = convertMemToSymVar(addr, IDREF.CPUSIZE.QWORD, "addr")
                addrCmp[instruction.address] = {'true': None, 'false': None}

        print instruction.assembly


    return

def cafter(instruction):

    global addrCmp
    global workList

    if instruction.opcode == IDREF.OPCODE.CMP:
        if addrCmp[instruction.address]['true'] is None:
            addrDone.append(instruction.address)
            addrCmp[instruction.address]['true'] = dict()
            zfId    = getRegSymbolicID(IDREF.FLAG.ZF)
            zfExpr  = getBacktrackedSymExpr(zfId)
            expr    = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvtrue())) # (assert (= zf True))
            models  = getModel(expr)
            for k, v in models.items():
                sm = getSymVar(k)
                if sm.kind == IDREF.SYMVAR.MEM:
                    addr = sm.kindValue
                    workList.append((addr,v))
                addrCmp[instruction.address]['true'][k] = v


        if addrCmp[instruction.address]['false'] is None:
            addrDone.append(instruction.address)
            addrCmp[instruction.address]['false'] = dict()
            expr    = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvfalse())) # (assert (= zf False))
            models  = getModel(expr)
            for k, v in models.items():
                sm = getSymVar(k)
                if sm.kind == IDREF.SYMVAR.MEM:
                    addr = sm.kindValue
                    workList.append((addr,v))
                addrCmp[instruction.address]['false'][k] = v


                #password.update({symVarMem: v})
                #print k,v

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
        print '[+] We can coverage all graph'
        disableSnapshot()
        return


    if instruction.address == 0x40053B:
        #print workList
        addr,v = workList.pop()
        print "[+] We set %x to %d"%(addr, v)
        setMemValue(addr, IDREF.CPUSIZE.QWORD, v)
        restoreSnapshot()
        return
        #restoreSnapshot()

    return



def fini():
    for add in addrCmp:
        print hex(add), addrCmp[add]
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


