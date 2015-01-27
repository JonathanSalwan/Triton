
#ifndef __UTILS_H__
#define __UTILS_H__

#include <iostream>

#include "pin.H"

#include "TaintEngine.h"

#define LOCKED        1
#define UNLOCKED      !LOCKED


UINT64 translatePinRegToID(REG reg);
REG getHighReg(REG reg);
VOID unlockAnalysis(UINT32 *analysisStatus);
VOID lockAnalysis(UINT32 *analysisStatus);
VOID taintParams(CONTEXT *ctx, TaintEngine *taintEngine);
UINT64 derefMem(UINT64 mem, UINT64 readSize);

#endif /* !__UTILS_H__ */
