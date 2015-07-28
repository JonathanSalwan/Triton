/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <iostream>

#include <SnapshotEngine.h>



SnapshotEngine::SnapshotEngine()
{
  this->locked              = LOCKED;
  this->snapshotTaintEngine = nullptr;
  this->snapshotSymEngine   = nullptr;
}


SnapshotEngine::~SnapshotEngine()
{
}


/* Add the modification byte. */
void SnapshotEngine::addModification(uint64 mem, char byte)
{
  if (this->locked == UNLOCKED)
    this->memory.push_front(make_pair(mem, byte));
}


/* Enable the snapshot engine. */
void SnapshotEngine::takeSnapshot(const SymbolicEngine &currentSymEngine, const TaintEngine &currentTaintEngine, CONTEXT *ctx)
{
  /* 1 - Unlock the engine */
  this->locked = UNLOCKED;

  /* 2 - Save current symbolic engine state */
  this->snapshotSymEngine = new SymbolicEngine(currentSymEngine);

  /* 3 - Save current taint engine state */
  this->snapshotTaintEngine = new TaintEngine(currentTaintEngine);

  /* 4 - Save Pin registers context */
  PIN_SaveContext(ctx, &this->pinCtx);
}


/* Restore the snapshot. */
void SnapshotEngine::restoreSnapshot(SymbolicEngine *currentSymEngine, TaintEngine *currentTaintEngine, CONTEXT *ctx)
{
  /* 1 - Restore all memory modification. */
  list< std::pair<uint64, char> >::iterator i;
  for(i = this->memory.begin(); i != this->memory.end(); ++i){
    *(reinterpret_cast<char*>(i->first)) = i->second;
  }
  this->memory.clear();

  /* 2 - Restore current symbolic engine state */
  *currentSymEngine = *this->snapshotSymEngine;

  /* 3 - Restore current taint engine state */
  *currentTaintEngine = *this->snapshotTaintEngine;

  /* 4 - Restore Pin registers context */
  PIN_SaveContext(&this->pinCtx, ctx);

  PIN_UnlockClient();
  PIN_ExecuteAt(ctx);
}


/* Disable the snapshot engine. */
void SnapshotEngine::disableSnapshot()
{
  this->locked = LOCKED;
}


/* Reset the snapshot engine.
 * Clear all backups for a new snapshot. */
void SnapshotEngine::resetEngine()
{
  this->memory.clear();

  delete this->snapshotSymEngine;
  this->snapshotSymEngine = nullptr;

  delete this->snapshotTaintEngine;
  this->snapshotTaintEngine = nullptr;
}


/* Check if the snapshot engine is locked. */
BOOL SnapshotEngine::isLocked()
{
  return this->locked;
}


CONTEXT *SnapshotEngine::getCtx(void)
{
  return &this->pinCtx;
}

