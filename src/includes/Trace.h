#ifndef _TRACE_H_
#define _TRACE_H_

#include <stdint.h>

#include <list>

#include "SnapshotEngine.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "Tritinst.h"

/* Trace of a run */
class Trace {

  private:
    std::list<Tritinst *> instructions;

  public:

    /* Snapshot Engine */
    SnapshotEngine *snapshotEngine;

    /* Taint Engine */
    TaintEngine *taintEngine;

    /* Symbolic Engine */
    SymbolicEngine *symbolicEngine;

    Trace();
    ~Trace();

    void addInstruction(Tritinst *instruction);
};

#endif /* !_TRACE_H_ */

