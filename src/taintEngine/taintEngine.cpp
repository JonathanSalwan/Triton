
#include <stdexcept>

#include "TaintEngine.h"
#include "Registers.h"



TaintEngine::TaintEngine()
{
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++){
    this->taintedReg[i] = !TAINTED;
  }
}


void TaintEngine::init(const TaintEngine &other)
{
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++){
    this->taintedReg[i] = other.taintedReg[i];
  }
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
  if (regID >= ID_LAST_ITEM)
    return !TAINTED;
  return this->taintedReg[regID];
}


/* Taint the register */
void TaintEngine::taintReg(uint64_t regID)
{
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = TAINTED;
}


/* Set the taint on memory */
void TaintEngine::setTaintMem(uint64_t mem, uint64_t flag)
{
  if (flag == TAINTED)
    this->taintMem(mem);
  else if (flag == !TAINTED)
    this->untaintMem(mem);
  else
    throw std::runtime_error("Error: Invalid flag in setTainMem()");
}


/* Set the taint on register */
void TaintEngine::setTaintReg(uint64_t regID, uint64_t flag)
{
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = flag;
}


/* Untaint the register */
void TaintEngine::untaintReg(uint64_t regID)
{
  if (regID >= ID_LAST_ITEM)
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
 * If the MemSrc is tainted we taint the memDst, otherwise 
 * we check if memDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintMemMem(uint64_t memDst, uint64_t memSrc)
{
  if (this->isMemTainted(memSrc)){
    this->taintMem(memDst);
    return TAINTED;
  }
  return this->isMemTainted(memDst);
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

