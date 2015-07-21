
# Output
# $ ~/tools/pin/pin-2.14-71313-gcc.4.4.7-linux/pin -t ./triton.so -script ./examples/callback_after.py -- ./samples/crackmes/crackme_xor a
# $ ../../../pin -t ./triton.so -script ./examples/callback_after.py -- ./samples/crackmes/crackme_xor a

from triton import *


# A callback must be a function with one argument. This argument is
# always the Instruction class and contains all information

strOperandType = {0:"IMM", 1:"REG", 2:"MEM_R", 3:"MEM_W", 4:"LEA"}
def getTypefromEnum(enum):
    return strOperandType[enum] 

strRegName = {0:"ID_INVALID",
        1:"ID_RAX",
        2:"ID_RBX",     
        3:"ID_RCX",     
        4:"ID_RDX",     
        5:"ID_RDI",     
        6:"ID_RSI",     
        7:"ID_RBP",     
        8:"ID_RSP",     
        9:"ID_RIP",     
        10:"ID_R8",     
        11:"ID_R9",     
        12:"ID_R10",    
        13:"ID_R11",    
        14:"ID_R12",    
        15:"ID_R13",    
        16:"ID_R14",    
        17:"ID_R15",    
        18:"ID_XMM0",   
        19:"ID_XMM1",   
        20:"ID_XMM2",   
        21:"ID_XMM3",   
        22:"ID_XMM4",   
        23:"ID_XMM5",   
        24:"ID_XMM6",   
        25:"ID_XMM7",   
        26:"ID_XMM8",   
        27:"ID_XMM9",   
        28:"ID_XMM10",  
        29:"ID_XMM11",  
        30:"ID_XMM12",  
        31:"ID_XMM13",  
        32:"ID_XMM14",  
        33:"ID_XMM15",  
        34:"ID_RFLAGS", 
        35:"ID_AF",     
        36:"ID_CF",     
        37:"ID_DF",     
        38:"ID_IF",     
        39:"ID_OF",     
        40:"ID_PF",     
        41:"ID_SF",     
        42:"ID_TF",     
        43:"ID_ZF",
        44:"ID_LAST_ITEM"}
def getRegfromEnum(enum):
    return strRegName[enum]

def getAllRegValue():
    AllReg = IDREF.REG()

    AllReg.RAX = getRegValue(IDREF.REG.RAX)
    AllReg.RBX = getRegValue(IDREF.REG.RBX)
    AllReg.RCX = getRegValue(IDREF.REG.RCX)
    AllReg.RDX = getRegValue(IDREF.REG.RDX)
    AllReg.RBP = getRegValue(IDREF.REG.RBP)
    AllReg.RSP = getRegValue(IDREF.REG.RSP)
    AllReg.RSI = getRegValue(IDREF.REG.RSI)
    AllReg.RDI = getRegValue(IDREF.REG.RDI)
    AllReg.RIP = getRegValue(IDREF.REG.RIP)
    AllReg.R8  = getRegValue(IDREF.REG.R8)
    AllReg.R9  = getRegValue(IDREF.REG.R9)
    AllReg.R10 = getRegValue(IDREF.REG.R10)
    AllReg.R11 = getRegValue(IDREF.REG.R11)
    AllReg.R12 = getRegValue(IDREF.REG.R12)
    AllReg.R13 = getRegValue(IDREF.REG.R13)
    AllReg.R14 = getRegValue(IDREF.REG.R14)
    AllReg.R15 = getRegValue(IDREF.REG.R15)
    
    return AllReg

def IDREF2DICT(AllReg, DICT):
    DICT['RAX'] = AllReg.RAX
    DICT['RBX'] = AllReg.RBX
    DICT['RCX'] = AllReg.RCX
    DICT['RDX'] = AllReg.RDX
    DICT['RBP'] = AllReg.RBP
    DICT['RSP'] = AllReg.RSP
    DICT['RSI'] = AllReg.RSI
    DICT['RDI'] = AllReg.RDI
    DICT['RIP'] = AllReg.RIP
    DICT['R8'] = AllReg.R8
    DICT['R9'] = AllReg.R9
    DICT['R10'] = AllReg.R10
    DICT['R11'] = AllReg.R11
    DICT['R12'] = AllReg.R12
    DICT['R13'] = AllReg.R13
    DICT['R14'] = AllReg.R14
    DICT['R15'] = AllReg.R15

    return 


# 
def printReg(AllReg):
    strReg = ""
    for i, Element in enumerate(AllReg):
        strReg += Element + ": %X || "%AllReg[Element]
    print strReg
    return

def getRegChanged(Old, New):
    strReg = "\t"
    for i, Element in enumerate(Old):
        if Element == 'RIP': continue
        if Old[Element] != New[Element]:
            strReg += Element+" : "
            strReg += "["+("%X"%Old[Element])+"->"+("%X"%New[Element])+"] "
        # when u want print changed reg only
        """
        else:
            strReg += Element+ " : "
            strReg += ("%X "%Old[Element])
        """
    if strReg == "\t": strReg = ""
    return strReg
    
def printMemChanged(Old, New):
    strReg = ""
    

dictOldReg = {}#dictkey#idref.reg()
dictNewReg = {}#dictkey
strOldMem = ""
strNewMem = ""

def dumpOnWrite(dumpWhen, instruction, operand):
    global strOldMem
    global strNewMem
    opAccess         = 'Write'
    memoryAccess     = operand.value
    memoryAccessSize = operand.size

    a = str()
    #d = '[%c:%d] 0x%016x: %s' %(opAccess, memoryAccessSize, instruction.address, instruction.assembly)

    if checkReadAccess(memoryAccess):
        a = '%s:0x%016x:' %(opAccess, memoryAccess)
        for i in range(memoryAccessSize):
            a += ' %02x' %(getMemValue(memoryAccess+i, 1))

    strResult = '%s (%#x)' %(a, getMemValue(memoryAccess, memoryAccessSize))
    if dumpWhen == 'before':
        strOldMem = strResult
    else:
        strNewMem = strResult

    return


def dump(opType, instruction, operand):
    opAccess         = 'Read' if opType == IDREF.OPERAND.MEM_R else 'W'
    memoryAccess     = operand.value
    memoryAccessSize = operand.size

    a = str()
    d = '[%s:%d] 0x%016x: %s' %(opAccess, memoryAccessSize, instruction.address, instruction.assembly)

    if checkReadAccess(memoryAccess):
        a = '%s:0x%016x:' %(opAccess, memoryAccess)
        for i in range(memoryAccessSize):
            a += ' %02x' %(getMemValue(memoryAccess+i, 1))

    print '\t%s%s%s (%#x)' %(d, ' '*(70-len(d)), a, getMemValue(memoryAccess, memoryAccessSize))
    return

def my_callback_before(instruction):
    #print "=== callback before ==="
    print '%#x: %s' %(instruction.address, instruction.assembly)
    AllReg = getAllRegValue()
    IDREF2DICT(AllReg, dictOldReg)
   
    #print "--- operand analyze"
    for operand in instruction.operands:

        if (((operand.type == IDREF.OPERAND.MEM_R) or (operand.type == IDREF.OPERAND.MEM_W)) and operand.value == 0x0):
            continue
        if operand.type == IDREF.OPERAND.MEM_W:
            dumpOnWrite('before', instruction, operand)
    return
 

def my_callback_after(instruction):
    #print "=== callback after ==="
    #print '%#x: %s' %(instruction.address, instruction.assembly)
    
    AllReg = getAllRegValue()
    IDREF2DICT(AllReg, dictNewReg)
    #print "--- changed reg analyze"
    strRegChanged =  getRegChanged(dictOldReg, dictNewReg)
    if strRegChanged != "":
        print strRegChanged

    AllReg = getAllRegValue()
    IDREF2DICT(AllReg, dictNewReg)

    #print "--- operand analyze"
    for operand in instruction.operands:
        if (((operand.type == IDREF.OPERAND.MEM_R) or (operand.type == IDREF.OPERAND.MEM_W)) and operand.value == 0x0):
            continue

        if (operand.type == IDREF.OPERAND.MEM_R):
            dump(operand.type, instruction, operand)

        elif (operand.type == IDREF.OPERAND.MEM_W):
            dumpOnWrite('after', instruction, operand)
            print '\t  %s\n\t->%s'%(strOldMem, strNewMem)
    IDREF2DICT(AllReg, dictOldReg)

    #print "--- code analyze done\n"
    return

def my_callback_fin(instruction):
    #print "=== callback fin ==="
    #print '%#x: %s' %(instruction.address, instruction.assembly)
    
    AllReg = getAllRegValue()
    IDREF2DICT(AllReg, dictNewReg)

    #print "--- operand analyze"
    for operand in instruction.operands:
        print "value : %X / size : %d / displacement : %d / baseReg : %d / indexReg : %d / memoryScale : %d"%(operand.value, operand.size, operand.displacement, operand.baseReg, operand.indexReg, operand.memoryScale)


    IDREF2DICT(AllReg, dictOldReg)
    print "--- code analyze done "



if __name__ == '__main__':
    startAnalysisFromSymbol('check')

    addCallback(my_callback_before, IDREF.CALLBACK.BEFORE)
    addCallback(my_callback_after, IDREF.CALLBACK.AFTER)
    addCallback(my_callback_fin, IDREF.CALLBACK.FINI)
    # Run the instrumentation - Never returns
    runProgram()

