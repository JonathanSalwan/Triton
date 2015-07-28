/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <stdexcept>

#include <TaintEngine.h>
#include <Registers.h>



TaintEngine::TaintEngine()
{
  for (uint64 i = 0; i < ID_LAST_ITEM; i++){
    this->taintedReg[i] = !TAINTED;
  }
}


void TaintEngine::init(const TaintEngine &other)
{
  for (uint64 i = 0; i < ID_LAST_ITEM; i++){
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
bool TaintEngine::isMemTainted(uint64 addr)
{
  std::list<uint64>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return TAINTED;
  }
  return !TAINTED;
}


/* Returns true of false if the register is currently tainted */
bool TaintEngine::isRegTainted(uint64 regID)
{
  if (regID >= ID_LAST_ITEM)
    return !TAINTED;
  return this->taintedReg[regID];
}


/* Taint the register */
void TaintEngine::taintReg(uint64 regID)
{
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = TAINTED;
}


/* Set the taint on memory */
void TaintEngine::setTaintMem(uint64 mem, uint64 flag)
{
  if (flag == TAINTED)
    this->taintMem(mem);
  else if (flag == !TAINTED)
    this->untaintMem(mem);
  else
    throw std::runtime_error("Error: Invalid flag in setTainMem()");
}


/* Set the taint on register */
void TaintEngine::setTaintReg(uint64 regID, uint64 flag)
{
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = flag;
}


/* Untaint the register */
void TaintEngine::untaintReg(uint64 regID)
{
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = !TAINTED;
}


/* Taint the address */
void TaintEngine::taintMem(uint64 addr)
{
  if (!this->isMemTainted(addr))
    this->taintedAddresses.push_front(addr);
}


/* Untaint the address */
void TaintEngine::untaintMem(uint64 addr)
{
  this->taintedAddresses.remove(addr);
}


/*
 * Spread the taint in regDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegReg(uint64 regDst, uint64 regSrc)
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
bool TaintEngine::assignmentSpreadTaintRegImm(uint64 regDst)
{
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in regDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegMem(uint64 regDst, uint64 memSrc, uint32 readSize)
{
  for (uint64 offset = 0; offset != readSize; offset++){
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
bool TaintEngine::assignmentSpreadTaintMemMem(uint64 memDst, uint64 memSrc, uint32 readSize)
{
  bool isTainted = !TAINTED;
  for (uint64 offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintMem(memDst+offset);
      isTainted = TAINTED;
    }
  }
  return isTainted;
}


/*
 * Returns True if the memory is tainted.
 */
bool TaintEngine::assignmentSpreadTaintExprMem(uint64 memSrc, uint32 readSize)
{
  for (uint64 offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      return TAINTED;
    }
  }
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprReg(uint64 regSrc)
{
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or mem are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegMem(uint64 regSrc, uint64 memSrc, uint32 readSize)
{
  for (uint64 offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      return TAINTED;
    }
  }
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or reg2 are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegReg(uint64 regSrc1, uint64 regSrc2)
{
  return this->isRegTainted(regSrc1) | this->isRegTainted(regSrc2);
}


/*
 * Untaint the memDst.
 * Returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemImm(uint64 memDst, uint32 writeSize)
{
  for (uint64 offset = 0; offset != writeSize; offset++)
    this->untaintMem(memDst+offset);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemReg(uint64 memDst, uint64 regSrc, uint32 writeSize)
{
  if (this->isRegTainted(regSrc)){
    for (uint64 offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }
  this->untaintMem(memDst);
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::aluSpreadTaintRegImm(uint64 regDst)
{
  return this->isRegTainted(regDst);
}


/*
 * If the RegSrc is tainted we taint the regDst, otherwise
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegReg(uint64 regDst, uint64 regSrc)
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
bool TaintEngine::aluSpreadTaintMemMem(uint64 memDst, uint64 memSrc, uint32 writeSize)
{
  bool tainted = !TAINTED;

  for (uint64 offset = 0; offset < writeSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintMem(memDst+offset);
      tainted = TAINTED;
    }
  }
  return tainted;
}


/*
 * If the Mem is tainted we taint the regDst, otherwise
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegMem(uint64 regDst, uint64 memSrc, uint32 readSize)
{
  for (uint64 offset = 0; offset < readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintReg(regDst);
      return TAINTED;
    }
  }
  return this->isRegTainted(regDst);
}


bool TaintEngine::aluSpreadTaintMemImm(uint64 memDst, uint32 writeSize)
{
  for (uint64 offset = 0; offset < writeSize; offset++){
    if (this->isMemTainted(memDst+offset)){
      return TAINTED;
    }
  }
  return !TAINTED;
}


bool TaintEngine::aluSpreadTaintMemReg(uint64 memDst, uint64 regSrc, uint32 writeSize)
{
  uint64 offset;

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

