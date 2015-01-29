
#ifndef   __SNAPSHOTENGINE_H__
#define   __SNAPSHOTENGINE_H__

#include <list>

#include "pin.H"
#include "SymbolicEngine.h"

#define LOCKED    1
#define UNLOCKED  !LOCKED



class SnapshotEngine{

  private:
    /* I/O memory monitoring for snapshot */
    /* item1: memory address              */
    /* item2: byte                        */
    std::list< std::pair<UINT64, UINT8> > memory;

    /* Status of the snapshot engine */
    BOOL locked;

    SymbolicEngine *snapshotSymEngine;
    CONTEXT        pinCtx;


  public:
    SnapshotEngine();
    ~SnapshotEngine();

    BOOL isLocked();
    VOID addModification(UINT64 address, UINT8 byte);
    VOID disableSnapshot();
    VOID resetEngine();
    VOID restoreSnapshot(SymbolicEngine currentSymEngine, CONTEXT *ctx);
    VOID takeSnapshot(const SymbolicEngine &currentSymEngine, CONTEXT *ctx);

};

/* decl */
VOID memoryWrite(std::string insDis, ADDRINT insAddr, UINT64 mem, UINT32 writeSize);

#endif     /* !__SNAPSHOTENGINE_H__ */

