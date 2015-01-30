#include "BasicBlock.h"


BasicBlock::BasicBlock(const SnapshotEngine &ss, const SymbolicEngine &se, const TaintEngine &te):
      snapshot(ss),
      symEngine(se),
      taintEngine(te)
{
}

BasicBlock::~BasicBlock()
{
}


void BasicBlock::addInstruction(Instruction ins)
{
  // TODO
}


//std::string BasicBlock::getPathCondition()
//{
//  // TODO
//}


void BasicBlock::restoreSnapshot()
{
  // TODO
}

