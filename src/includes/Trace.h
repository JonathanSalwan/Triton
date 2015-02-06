#ifndef _TRACE_H_
#define _TRACE_H_

#include <stdint.h>

#include <list>

#include "Instruction.h"
#include "SnapshotEngine.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"

/* Trace of a run */
class Trace {

  private:
    std::list<Instruction>  instructions;

  public:

    /* Snapshot Engine */
    SnapshotEngine *snapshotEngine;

    /* Taint Engine */
    TaintEngine *taintEngine;

    /* Symbolic Engine */
    SymbolicEngine *symbolicEngine;

    Trace();
    ~Trace();
};

#endif /* !_TRACE_H_ */

