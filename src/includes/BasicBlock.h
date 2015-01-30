#ifndef _BASICBLOCK_H_
#define _BASICBLOCK_H_

#include <list>

#include "Instruction.h"
#include "SnapshotEngine.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"


/* Basic Block */
class BasicBlock {
  private:
    SnapshotEngine snapshot;
    SymbolicEngine symEngine;
    TaintEngine taintEngine;
    std::list<Instruction> instructions;

  public:
    BasicBlock(const SnapshotEngine &ss, const SymbolicEngine &se, const TaintEngine &te):
      snapshot(ss),
      symEngine(se),
      taintEngine(te),
      instructions() { }

    ~BasicBlock();

    void addInstruction(Instruction ins);
    std::string &getPathCondition();
    void restoreSnapshot();
};

#endif /* !_BASIC_BLOCK_H_ */
