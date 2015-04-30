
from    triton import *
import  smt2lib

password = dict()
tmp      = None

# $ ../../../pin -t ./triton.so -script ./examples/get_model.py -- ./samples/crackmes/crackme_xor elite
# {'SymVar_0': "0x65, 'e'"}
# {'SymVar_1': "0x6c, 'l'"}
# {'SymVar_2': "0x69, 'i'"}
# {'SymVar_3': "0x74, 't'"}
# {'SymVar_4': "0x65, 'e'"}
# Win
# $

# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed, 
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):
    if instruction.address == 0x40058b:
        rax = getRegValue(IDREF.REG.RAX)
        taintMem(rax)

        global tmp
        tmp = rax

        global password
        if rax in password:
            setMemValue(rax, 1, password[rax])
            print '[+] Inject the character \'%c\' in memory' %(chr(password[rax]))
    return


# 0x4005ae: cmp ecx, eax
def cafter(instruction):
    if instruction.address == 0x4005ae:
        zfId    = getRegSymbolicID(IDREF.FLAG.ZF)
        zfExpr  = getBacktrackedSymExpr(zfId)
        expr    = smt2lib.smtAssert(smt2lib.equal(zfExpr, smt2lib.bvtrue())) # (assert (= zf True))
        models  = getModel(expr)
        global password
        for k, v in models.items():
            password.update({tmp: v})
    return


def cbefore(instruction):
    # Prologue of the function
    global snapshot
    if instruction.address == 0x40056d and isSnapshotEnable() == False:
        takeSnapshot()
        print '[+] Take a snapshot at the prologue of the function'
        return

    # Epilogue of the function
    if instruction.address == 0x4005c8:
        rax = getRegValue(IDREF.REG.RAX)
        # The function returns 0 if the password is valid
        # So, we restore the snapshot until this function
        # returns something else than 0.
        if rax != 0:
            print '[+] Still not the good password. Restore snapshot.'
            restoreSnapshot()
        else:
            print '[+] Good password found!'
            disableSnapshot()
        return
    return


def fini():
    print '[+] Analysis done!'


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    addCallback(cbeforeSymProc, IDREF.CALLBACK.BEFORE_SYMPROC)
    addCallback(cafter,         IDREF.CALLBACK.AFTER)
    addCallback(cbefore,        IDREF.CALLBACK.BEFORE)
    addCallback(fini,           IDREF.CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()

