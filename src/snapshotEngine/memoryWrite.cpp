
#include "pin.H"
#include "Triton.h"


/* Snapshot callback for all STORE instructions.
 * Used to save the memory modification on-the-fly */
VOID memoryWrite(std::string insDis, ADDRINT insAddr, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED)
    return;
 
  /* If the snapshot is not enable we don't save the memory */
  if (trace->snapshotEngine->isLocked())
    return;

  UINT32 i = 0;
  for (; i < writeSize ; i++)
    trace->snapshotEngine->addModification(mem+i, *(reinterpret_cast<UINT8*>(mem+i)));

  return;
}


