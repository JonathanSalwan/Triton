
#include <iostream>

#include "pin.H"
#include "SnapshotEngine.h"
#include "Registers.h"



SnapshotEngine::SnapshotEngine()
{
  this->locked = LOCKED;
}


SnapshotEngine::~SnapshotEngine()
{
}


/* Add the modification byte. */
VOID SnapshotEngine::addModification(UINT64 mem, UINT8 byte)
{
  this->memory.push_back(make_pair(mem, byte));
}


/* Enable the snapshot engine. */
VOID SnapshotEngine::takeSnapshot(const SymbolicEngine &currentSymEngine, const TaintEngine &currentTaintEngine, CONTEXT *ctx)
{
  /* 1 - Unlock the engine */
  this->locked = UNLOCKED;

  /* 2 - Save current symbolic engine state */
  this->snapshotSymEngine = new SymbolicEngine(currentSymEngine);

  /* 3 - Save current taint engine state */
  this->snapshotTaintEngine = new TaintEngine(currentTaintEngine);

  /* 4 - Save Pin registers context */
  PIN_SaveContext(ctx, &this->pinCtx);

  std::cout << "[snapshot]" << std::endl;
}


/* Restore the snapshot. */
VOID SnapshotEngine::restoreSnapshot(SymbolicEngine *currentSymEngine, TaintEngine *currentTaintEngine, CONTEXT *ctx)
{
  /* 1 - Restore all memory modification. */
  list< std::pair<UINT64, UINT8> >::iterator i;
  for(i = this->memory.begin(); i != this->memory.end(); ++i){
    *(reinterpret_cast<ADDRINT*>(i->first)) = i->second;
  }
  this->memory.clear();

  /* 2 - Restore current symbolic engine state */
  *currentSymEngine = *this->snapshotSymEngine;

  /* 3 - Restore current taint engine state */
  *currentTaintEngine = *this->snapshotTaintEngine;

  /* 4 - Restore Pin registers context */
  PIN_SaveContext(&this->pinCtx, ctx);

  std::cout << "[restore snapshot]" << std::endl;

  PIN_ExecuteAt(ctx);
}


/* Disable the snapshot engine. */
VOID SnapshotEngine::disableSnapshot()
{
  this->locked = LOCKED;
}


/* Reset the snapshot engine.
 * Clear all backups for a new snapshot. */
VOID SnapshotEngine::resetEngine()
{
  this->memory.clear();
  delete this->snapshotSymEngine;
  this->snapshotSymEngine = NULL;
}


/* Check if the snapshot engine is locked. */
BOOL SnapshotEngine::isLocked()
{
  return this->locked;
}


