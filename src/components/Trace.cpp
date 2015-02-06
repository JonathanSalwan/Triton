#include "Trace.h"


Trace::Trace()
{
  /* Snapshot Engine */
  this->snapshotEngine = new SnapshotEngine;

  /* Taint Engine */
  this->taintEngine = new TaintEngine;

  /* Symbolic Engine */
  this->symbolicEngine = new SymbolicEngine;
}


Trace::~Trace()
{
  delete this->snapshotEngine;
  delete this->taintEngine;
  delete this->symbolicEngine;
}


void Trace::addInstruction(Tritinst *instruction)
{
  this->instructions.push_back(instruction);
}

