/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <SnapshotEngine.h>



SnapshotEngine::SnapshotEngine() {
  this->locked              = LOCKED;
  this->snapshotTaintEngine = nullptr;
  this->snapshotSymEngine   = nullptr;
  this->mustBeRestore       = false;
}


SnapshotEngine::~SnapshotEngine() {
}


/* Add the modification byte. */
void SnapshotEngine::addModification(__uint mem, char byte) {
  if (this->locked == UNLOCKED)
    this->memory.push_front(make_pair(mem, byte));
}


/* Enable the snapshot engine. */
void SnapshotEngine::takeSnapshot(const SymbolicEngine &currentSymEngine, const TaintEngine &currentTaintEngine, CONTEXT *ctx) {
  /* 1 - Unlock the engine */
  this->locked = UNLOCKED;

  /* 2 - Save current symbolic engine state */
  this->snapshotSymEngine = new SymbolicEngine(currentSymEngine);

  /* 3 - Save current taint engine state */
  this->snapshotTaintEngine = new TaintEngine(currentTaintEngine);

  /* 4 - Save current taint engine state */
  this->nodesList = smt2lib::nodesList;

  /* 5 - Save Pin registers context */
  PIN_SaveContext(ctx, &this->pinCtx);
}


/* Restore the snapshot. */
void SnapshotEngine::restoreSnapshot(SymbolicEngine *currentSymEngine, TaintEngine *currentTaintEngine, CONTEXT *ctx) {

  if (this->mustBeRestore == false)
    return;

  /* 1 - Restore all memory modification. */
  list< std::pair<__uint, char> >::iterator i;
  for(i = this->memory.begin(); i != this->memory.end(); ++i){
    *(reinterpret_cast<char*>(i->first)) = i->second;
  }
  this->memory.clear();

  /* 2.1 - Delete unused expressions */
  std::vector<SymbolicExpression *> currentExpressions = currentSymEngine->getExpressions();

  __uint currentSize  = currentExpressions.size();
  __uint snapshotSize = this->snapshotSymEngine->getExpressions().size();
  for (__uint index = snapshotSize; index < currentSize; index++) {
    delete currentExpressions[index];
  }

  /* 2.2 - Delete unused variables */
  std::vector<SymbolicVariable *> currentSymbolicVars = currentSymEngine->getSymVars();

  currentSize  = currentSymbolicVars.size();
  snapshotSize = this->snapshotSymEngine->getSymVars().size();
  for (__uint index = snapshotSize; index < currentSize; index++) {
    delete currentSymbolicVars[index];
  }

  /* 2.3 - Restore current symbolic engine state */
  *currentSymEngine = *this->snapshotSymEngine;

  /* 3 - Restore current taint engine state */
  *currentTaintEngine = *this->snapshotTaintEngine;

  /* 4 - Delete unused AST nodes */
  smt2lib::freeUnusedNodes(this->nodesList);

  /* 5 - Restore Pin registers context */
  PIN_SaveContext(&this->pinCtx, ctx);

  this->mustBeRestore = false;
  PIN_UnlockClient();
  PIN_ExecuteAt(ctx);
}


/* Disable the snapshot engine. */
void SnapshotEngine::disableSnapshot(void) {
  this->locked = LOCKED;
}


/* Reset the snapshot engine.
 * Clear all backups for a new snapshot. */
void SnapshotEngine::resetEngine(void) {
  this->memory.clear();

  delete this->snapshotSymEngine;
  this->snapshotSymEngine = nullptr;

  delete this->snapshotTaintEngine;
  this->snapshotTaintEngine = nullptr;
}


/* Check if the snapshot engine is locked. */
bool SnapshotEngine::isLocked(void) {
  return this->locked;
}


CONTEXT *SnapshotEngine::getCtx(void) {
  return &this->pinCtx;
}


/* Check if we must restore the snapshot */
bool SnapshotEngine::isMustBeRestored(void) {
  return this->mustBeRestore;
}


/* Check if we must restore the snapshot */
void SnapshotEngine::setRestore(bool flag) {
  this->mustBeRestore = flag;
}

#endif /* LIGHT_VERSION */

