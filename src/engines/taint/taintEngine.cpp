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
  for (__uint i = 0; i < ID_LAST_ITEM; i++) {
    this->taintedReg[i] = !TAINTED;
  }
}


void TaintEngine::init(const TaintEngine &other) {
  for (__uint i = 0; i < ID_LAST_ITEM; i++) {
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
bool TaintEngine::isMemTainted(__uint addr, uint32 size) {
  for (uint32 index = 0; index != size; index++) {
    if (this->taintedAddresses.find(addr+index) != this->taintedAddresses.end())
        return TAINTED;
  }
  return !TAINTED;
}


/* Returns true of false if the register is currently tainted */
bool TaintEngine::isRegTainted(__uint regID) {
  if (regID >= ID_LAST_ITEM)
    return !TAINTED;
  return this->taintedReg[regID];
}


/* Taint the register */
void TaintEngine::taintReg(__uint regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = TAINTED;
}


/* Set the taint on memory */
void TaintEngine::setTaintMem(__uint mem, __uint flag) {
  if (flag == TAINTED)
    this->taintMem(mem);
  else if (flag == !TAINTED)
    this->untaintMem(mem);
  else
    throw std::runtime_error("Error: Invalid flag in setTainMem()");
}


/* Set the taint on register */
void TaintEngine::setTaintReg(__uint regID, __uint flag) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = flag;
}


/* Untaint the register */
void TaintEngine::untaintReg(__uint regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->taintedReg[regID] = !TAINTED;
}


/* Taint the address */
void TaintEngine::taintMem(__uint addr) {
  this->taintedAddresses[addr] = true;
}


/* Untaint the address */
void TaintEngine::untaintMem(__uint addr) {
  this->taintedAddresses.erase(addr);
}


/*
 * Spread the taint in regDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegReg(__uint regDst, __uint regSrc) {
  if (this->isRegTainted(regSrc)) {
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
bool TaintEngine::assignmentSpreadTaintRegImm(__uint regDst) {
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in regDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintRegMem(__uint regDst, __uint memSrc, uint32 readSize) {
  if (this->isMemTainted(memSrc, readSize)) {
    this->taintReg(regDst);
    return TAINTED;
  }
  this->untaintReg(regDst);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if memSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemMem(__uint memDst, __uint memSrc, uint32 readSize) {
  bool isTainted = !TAINTED;
  for (__uint offset = 0; offset != readSize; offset++) {
    if (this->isMemTainted(memSrc+offset)) {
      this->taintMem(memDst+offset);
      isTainted = TAINTED;
    }
  }
  return isTainted;
}


/*
 * Returns True if the memory is tainted.
 */
bool TaintEngine::assignmentSpreadTaintExprMem(__uint memSrc, uint32 readSize) {
  if (this->isMemTainted(memSrc, readSize)) {
    return TAINTED;
  }
  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprReg(__uint regSrc) {
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or mem are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegMem(__uint regSrc, __uint memSrc, uint32 readSize) {
  if (this->isMemTainted(memSrc, readSize)) {
    return TAINTED;
  }
  return this->isRegTainted(regSrc);
}


/*
 * If the reg1 or reg2 are tainted, we returns true to taint the SE.
 */
bool TaintEngine::assignmentSpreadTaintExprRegReg(__uint regSrc1, __uint regSrc2) {
  return this->isRegTainted(regSrc1) | this->isRegTainted(regSrc2);
}


/*
 * Untaint the memDst.
 * Returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemImm(__uint memDst, uint32 writeSize) {
  for (__uint offset = 0; offset != writeSize; offset++)
    this->untaintMem(memDst+offset);
  return !TAINTED;
}


/*
 * Spread the taint in memDst if regSrc is tainted.
 * Returns true if a spreading occurs otherwise returns false.
 */
bool TaintEngine::assignmentSpreadTaintMemReg(__uint memDst, __uint regSrc, uint32 writeSize) {

  /* Check source */
  if (this->isRegTainted(regSrc)) {
    for (__uint offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }

  /* Spread destination */
  for (__uint offset = 0; offset != writeSize; offset++)
    this->untaintMem(memDst+offset);

  return !TAINTED;
}


/*
 * If the reg is tainted, we returns true to taint the SE.
 */
bool TaintEngine::aluSpreadTaintRegImm(__uint regDst) {
  return this->isRegTainted(regDst);
}


/*
 * If the RegSrc is tainted we taint the regDst, otherwise
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegReg(__uint regDst, __uint regSrc) {
  if (this->isRegTainted(regSrc)) {
    this->taintReg(regDst);
    return TAINTED;
  }
  return this->isRegTainted(regDst);
}


/*
 * If the MemSrc is tainted we taint the memDst, otherwise
 * we check if memDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintMemMem(__uint memDst, __uint memSrc, uint32 writeSize) {
  bool tainted = !TAINTED;

  /* Check source */
  for (__uint offset = 0; offset != writeSize; offset++) {
    if (this->isMemTainted(memSrc+offset)) {
      this->taintMem(memDst+offset);
      tainted = TAINTED;
    }
  }

  /* Check destination */
  if (this->isMemTainted(memDst, writeSize)) {
    return TAINTED;
  }

  return tainted;
}


/*
 * If the Mem is tainted we taint the regDst, otherwise
 * we check if regDst is tainted and returns the status.
 */
bool TaintEngine::aluSpreadTaintRegMem(__uint regDst, __uint memSrc, uint32 readSize) {
  if (this->isMemTainted(memSrc, readSize)) {
    this->taintReg(regDst);
    return TAINTED;
  }
  return this->isRegTainted(regDst);
}


bool TaintEngine::aluSpreadTaintMemImm(__uint memDst, uint32 writeSize) {
  if (this->isMemTainted(memDst, writeSize)) {
    return TAINTED;
  }
  return !TAINTED;
}


bool TaintEngine::aluSpreadTaintMemReg(__uint memDst, __uint regSrc, uint32 writeSize) {
  __uint offset;

  if (this->isRegTainted(regSrc)) {
    for (offset = 0; offset != writeSize; offset++)
      this->taintMem(memDst+offset);
    return TAINTED;
  }

  if (this->isMemTainted(memDst, writeSize))
    return TAINTED;

  return !TAINTED;
}

#endif /* LIGHT_VERSION */

