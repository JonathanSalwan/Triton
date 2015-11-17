/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <stdexcept>

#include <TaintEngine.h>
#include <Registers.h>



TaintEngine::TaintEngine() {
  for (reg_size i = 0; i < ID_LAST_ITEM; i++){
    this->taintedReg[i] = !TAINTED;
  }
}


void TaintEngine::init(const TaintEngine &other) {
  for (reg_size i = 0; i < ID_LAST_ITEM; i++){
    this->taintedReg[i] = other.taintedReg[i];
  }
  this->taintedAddresses = other.taintedAddresses;
}


TaintEngine::TaintEngine(const TaintEngine &copy) {
  init(copy);
}


TaintEngine::~TaintEngine() {
}


void TaintEngine::operator=(const TaintEngine &other) {
  init(other);
}


/* Returns true of false if the memory address is currently tainted */
bool TaintEngine::isMemTainted(reg_size addr) {
  std::list<reg_size>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return TAINTED;
  }
  return !TAINTED;
}


/* Returns true of false if the register is currently tainted */
bool TaintEngine::isRegTainted(reg_size regID) {
  if (regID >= ID_LAST_ITEM)
    return !TAINTED;
  return this->taintedReg[regID];
}


/* Taint the register */
void TaintEngine::taintReg(reg_size regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = TAINTED;
}


/* Set the taint on memory */
void TaintEngine::setTaintMem(reg_size mem, reg_size flag) {
  if (flag == TAINTED)
    this->taintMem(mem);
  else if (flag == !TAINTED)
    this->untaintMem(mem);
  else
    throw std::runtime_error("Error: Invalid flag in setTainMem()");
}


/* Set the taint on register */
void TaintEngine::setTaintReg(reg_size regID, reg_size flag) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = flag;
}


/* Untaint the register */
void TaintEngine::untaintReg(reg_size regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = !TAINTED;
}


/* Taint the address */
void TaintEngine::taintMem(reg_size addr) {
  if (!this->isMemTainted(addr))
    this->taintedAddresses.push_front(addr);
}


/* Untaint the address */
void TaintEngine::untaintMem(reg_size addr) {
  this->taintedAddresses.remove(addr);
}


/*
 * Spread the taint in regDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegReg(reg_size regDst, reg_size regSrc) {
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
bool TaintEngine::assignmentSpreadTaintRegImm(reg_size regDst) {
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in regDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegMem(reg_size regDst, reg_size memSrc, uint32 readSize) {
  for (reg_size offset = 0; offset != readSize; offset++){
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
bool TaintEngine::assignmentSpreadTaintMemMem(reg_size memDst, reg_size memSrc, uint32 readSize) {
  bool isTainted = !TAINTED;
  for (reg_size offset = 0; offset != readSize; offset++){
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
bool TaintEngine::assignmentSpreadTaintExprMem(reg_size memSrc, uint32 readSize) {
  for (reg_size offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      return TAINTED;
    }
  }
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprReg(reg_size regSrc) {
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or mem are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegMem(reg_size regSrc, reg_size memSrc, uint32 readSize) {
  for (reg_size offset = 0; offset != readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      return TAINTED;
    }
  }
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or reg2 are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegReg(reg_size regSrc1, reg_size regSrc2) {
  return this->isRegTainted(regSrc1) | this->isRegTainted(regSrc2);
}


/*
 * Untaint the memDst.
 * Returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemImm(reg_size memDst, uint32 writeSize) {
  for (reg_size offset = 0; offset != writeSize; offset++)
    this->untaintMem(memDst+offset);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemReg(reg_size memDst, reg_size regSrc, uint32 writeSize) {
  if (this->isRegTainted(regSrc)){
    for (reg_size offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }
  this->untaintMem(memDst);
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::aluSpreadTaintRegImm(reg_size regDst) {
  return this->isRegTainted(regDst);
}


/*
 * If the RegSrc is tainted we taint the regDst, otherwise
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegReg(reg_size regDst, reg_size regSrc) {
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
bool TaintEngine::aluSpreadTaintMemMem(reg_size memDst, reg_size memSrc, uint32 writeSize) {
  bool tainted = !TAINTED;

  for (reg_size offset = 0; offset < writeSize; offset++){
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
bool TaintEngine::aluSpreadTaintRegMem(reg_size regDst, reg_size memSrc, uint32 readSize) {
  for (reg_size offset = 0; offset < readSize; offset++){
    if (this->isMemTainted(memSrc+offset)){
      this->taintReg(regDst);
      return TAINTED;
    }
  }
  return this->isRegTainted(regDst);
}


bool TaintEngine::aluSpreadTaintMemImm(reg_size memDst, uint32 writeSize) {
  for (reg_size offset = 0; offset < writeSize; offset++){
    if (this->isMemTainted(memDst+offset)){
      return TAINTED;
    }
  }
  return !TAINTED;
}


bool TaintEngine::aluSpreadTaintMemReg(reg_size memDst, reg_size regSrc, uint32 writeSize) {
  reg_size offset;

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

#endif /* LIGHT_VERSION */

