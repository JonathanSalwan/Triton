/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SNAPSHOTENGINE_H
#define SNAPSHOTENGINE_H

#include <list>

#include "pin.H"
#include "SymbolicEngine.h"
#include "TaintEngine.h"

#define LOCKED    1
#define UNLOCKED  !LOCKED



class SnapshotEngine{

  private:
    /* I/O memory monitoring for snapshot */
    /* item1: memory address              */
    /* item2: byte                        */
    std::list< std::pair<reg_size, char> > memory;

    /* Status of the snapshot engine */
    bool locked;

    SymbolicEngine  *snapshotSymEngine;
    TaintEngine     *snapshotTaintEngine;
    CONTEXT         pinCtx;


  public:
    SnapshotEngine();
    ~SnapshotEngine();

    CONTEXT   *getCtx(void);
    bool      isLocked();
    void      addModification(reg_size address, char byte);
    void      disableSnapshot();
    void      resetEngine();
    void      restoreSnapshot(SymbolicEngine *currentSymEngine, TaintEngine *currentTaintEngine, CONTEXT *ctx);
    void      takeSnapshot(const SymbolicEngine &currentSymEngine, const TaintEngine &currentTaintEngine, CONTEXT *ctx);

};

#endif /* !__SNAPSHOTENGINE_H__ */
#endif /* LIGHT_VERSION */

