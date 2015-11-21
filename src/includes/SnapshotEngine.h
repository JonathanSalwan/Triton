/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SNAPSHOTENGINE_H
#define SNAPSHOTENGINE_H

#include <list>
#include <map>

#include "pin.H"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "SMT2Lib.h"

#define LOCKED    1
#define UNLOCKED  !LOCKED



class SnapshotEngine{

  private:
    /* I/O memory monitoring for snapshot */
    /* item1: memory address              */
    /* item2: byte                        */
    std::list< std::pair<__uint, char> > memory;

    /* Status of the snapshot engine */
    bool locked;

    /* Flag which defines if we must restore the snapshot */
    bool mustBeRestore;

    /* AST node state */
    std::map<smt2lib::smtAstAbstractNode *, bool> nodesList;

    /* Engines context */
    SymbolicEngine  *snapshotSymEngine;
    TaintEngine     *snapshotTaintEngine;
    CONTEXT         pinCtx;


  public:
    SnapshotEngine();
    ~SnapshotEngine();

    CONTEXT   *getCtx(void);
    bool      isLocked(void);
    bool      isMustBeRestored(void);
    void      addModification(__uint address, char byte);
    void      disableSnapshot(void);
    void      resetEngine(void);
    void      restoreSnapshot(SymbolicEngine *currentSymEngine, TaintEngine *currentTaintEngine, CONTEXT *ctx);
    void      setRestore(bool flag);
    void      takeSnapshot(const SymbolicEngine &currentSymEngine, const TaintEngine &currentTaintEngine, CONTEXT *ctx);

};

#endif /* !__SNAPSHOTENGINE_H__ */
#endif /* LIGHT_VERSION */

