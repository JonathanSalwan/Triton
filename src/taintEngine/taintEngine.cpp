
#include "TaintEngine.h"
#include "Registers.h"



TaintEngine::TaintEngine()
{
  /* Init all registers to not tainted */
  this->taintedReg[ID_RAX]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RBX]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RCX]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RDX]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RDI]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RSI]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RBP]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RSP]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_RIP]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R8]    = (uint64_t)!TAINTED;
  this->taintedReg[ID_R9]    = (uint64_t)!TAINTED;
  this->taintedReg[ID_R10]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R11]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R12]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R13]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R14]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_R15]   = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM0]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM1]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM2]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM3]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM4]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM5]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM6]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM7]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM8]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM9]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM10] = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM11] = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM12] = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM13] = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM14] = (uint64_t)!TAINTED;
  this->taintedReg[ID_XMM15] = (uint64_t)!TAINTED;
}


void TaintEngine::init(const TaintEngine &other)
{
  this->taintedReg[ID_RAX]   = other.taintedReg[ID_RAX];
  this->taintedReg[ID_RBX]   = other.taintedReg[ID_RBX];
  this->taintedReg[ID_RCX]   = other.taintedReg[ID_RCX];
  this->taintedReg[ID_RDX]   = other.taintedReg[ID_RDX];
  this->taintedReg[ID_RDI]   = other.taintedReg[ID_RDI];
  this->taintedReg[ID_RSI]   = other.taintedReg[ID_RSI];
  this->taintedReg[ID_RBP]   = other.taintedReg[ID_RBP];
  this->taintedReg[ID_RSP]   = other.taintedReg[ID_RSP];
  this->taintedReg[ID_RIP]   = other.taintedReg[ID_RIP];
  this->taintedReg[ID_R8]    = other.taintedReg[ID_R8];
  this->taintedReg[ID_R9]    = other.taintedReg[ID_R9];
  this->taintedReg[ID_R10]   = other.taintedReg[ID_R10];
  this->taintedReg[ID_R11]   = other.taintedReg[ID_R11];
  this->taintedReg[ID_R12]   = other.taintedReg[ID_R12];
  this->taintedReg[ID_R13]   = other.taintedReg[ID_R13];
  this->taintedReg[ID_R14]   = other.taintedReg[ID_R14];
  this->taintedReg[ID_R15]   = other.taintedReg[ID_R15];
  this->taintedReg[ID_XMM0]  = other.taintedReg[ID_XMM0];
  this->taintedReg[ID_XMM1]  = other.taintedReg[ID_XMM1];
  this->taintedReg[ID_XMM2]  = other.taintedReg[ID_XMM2];
  this->taintedReg[ID_XMM3]  = other.taintedReg[ID_XMM3];
  this->taintedReg[ID_XMM4]  = other.taintedReg[ID_XMM4];
  this->taintedReg[ID_XMM5]  = other.taintedReg[ID_XMM5];
  this->taintedReg[ID_XMM6]  = other.taintedReg[ID_XMM6];
  this->taintedReg[ID_XMM7]  = other.taintedReg[ID_XMM7];
  this->taintedReg[ID_XMM8]  = other.taintedReg[ID_XMM8];
  this->taintedReg[ID_XMM9]  = other.taintedReg[ID_XMM9];
  this->taintedReg[ID_XMM10] = other.taintedReg[ID_XMM10];
  this->taintedReg[ID_XMM11] = other.taintedReg[ID_XMM11];
  this->taintedReg[ID_XMM12] = other.taintedReg[ID_XMM12];
  this->taintedReg[ID_XMM13] = other.taintedReg[ID_XMM13];
  this->taintedReg[ID_XMM14] = other.taintedReg[ID_XMM14];
  this->taintedReg[ID_XMM15] = other.taintedReg[ID_XMM15];

  this->taintedAddresses = other.taintedAddresses;
}


TaintEngine::TaintEngine(const TaintEngine &copy)
{
  init(copy);
}


TaintEngine::~TaintEngine()
{
}


void TaintEngine::operator=(const TaintEngine &other)
{
  init(other);
}


/* Returns true of false if the memory address is currently tainted */
bool TaintEngine::isMemTainted(uint64_t addr)
{
  std::list<uint64_t>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return TAINTED;
  }
  return !TAINTED;
}

/* Returns true of false if the register is currently tainted */
bool TaintEngine::isRegTainted(uint64_t regID)
{
  if (regID >= (sizeof(this->taintedReg) / sizeof(this->taintedReg[0])))
    return !TAINTED;
  return this->taintedReg[regID];
}


/* Taint the register */
void TaintEngine::taintReg(uint64_t regID)
{
  if (regID >= (sizeof(this->taintedReg) / sizeof(this->taintedReg[0])))
    return ;
  this->taintedReg[regID] = TAINTED;
}


/* Untaint the register */
void TaintEngine::untaintReg(uint64_t regID)
{
  if (regID >= (sizeof(this->taintedReg) / sizeof(this->taintedReg[0])))
    return ;
  this->taintedReg[regID] = !TAINTED;
}


/* Taint the address */
void TaintEngine::taintMem(uint64_t addr)
{
  if (!this->isMemTainted(addr))
    this->taintedAddresses.push_front(addr);
}


/* Untaint the address */
void TaintEngine::untaintMem(uint64_t addr)
{
  this->taintedAddresses.remove(addr);
}


/*
 * Spread the taint in regDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegReg(uint64_t regDst, uint64_t regSrc)
{
  if (this->isRegTainted(regSrc)){
    this->taintReg(regDst);
    return TAINTED;
  }
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Untaint the regDst.
 * Returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegImm(uint64_t regDst)
{
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in regDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegMem(uint64_t regDst, uint64_t memSrc, uint32_t readSize)
{
  for (uint64_t offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintReg(regDst);
      return TAINTED;
    }
  }
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemMem(uint64_t memDst, uint64_t memSrc, uint32_t readSize)
{
  bool isTainted = !TAINTED;
  for (uint64_t offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintMem(memDst+offset);
      isTainted = TAINTED;
    }
  }
  return isTainted;
}

/*
 * Untaint the memDst.
 * Returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemImm(uint64_t memDst, uint32_t writeSize)
{
  for (uint64_t offset = 0; offset != writeSize; offset++)
    this->untaintMem(memDst+offset);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemReg(uint64_t memDst, uint64_t regSrc, uint32_t writeSize)
{
  if (this->isRegTainted(regSrc)){
    for (uint64_t offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }
  this->untaintMem(memDst);
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::aluSpreadTaintRegImm(uint64_t regDst)
{
  return this->isRegTainted(regDst);
}


/*
 * If the RegSrc is tainted we taint the regDst, otherwise 
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegReg(uint64_t regDst, uint64_t regSrc)
{
  if (this->isRegTainted(regSrc)){
    this->taintReg(regDst);
    return TAINTED;
  }
  return this->isRegTainted(regDst);
}


/*
 * If the Mem is tainted we taint the regDst, otherwise 
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegMem(uint64_t regDst, uint64_t memSrc, uint32_t readSize)
{
  for (uint64_t offset = 0; offset < readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintReg(regDst);
      return TAINTED;
    }
  }
  return this->isRegTainted(regDst);
}


bool TaintEngine::aluSpreadTaintMemImm(uint64_t memDst, uint32_t writeSize)
{
  for (uint64_t offset = 0; offset < writeSize; offset++){
    if (this->isMemTainted(memDst+offset)){
      return TAINTED;
    }
  }
  return !TAINTED;
}


bool TaintEngine::aluSpreadTaintMemReg(uint64_t memDst, uint64_t regSrc, uint32_t writeSize)
{
  uint64_t offset;

  if (this->isRegTainted(regSrc)){
    for (offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }

  for (offset = 0; offset != writeSize; offset++){
    if (this->isMemTainted(memDst+offset))
      return TAINTED;
  }

  return !TAINTED;
}

