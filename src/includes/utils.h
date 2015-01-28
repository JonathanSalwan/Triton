
#ifndef __UTILS_H__
#define __UTILS_H__

#include <iostream>

#include "pin.H"

#include "SymbolicEngine.h"
#include "TaintEngine.h"

#define LOCKED        1
#define UNLOCKED      !LOCKED


REG     getHighReg(REG reg);
UINT64  derefMem(UINT64 mem, UINT64 readSize);
UINT64  translatePinRegToID(REG reg);
VOID    displayTrace(ADDRINT addr, const std::string &insDis, const std::string &expr, UINT64 isTainted);
VOID    displayTrace(ADDRINT addr, const std::string &insDis, symbolicElement *symElement);
VOID    displayBug(const std::string &str);
VOID    lockAnalysis(UINT32 *analysisStatus);
VOID    taintParams(CONTEXT *ctx, TaintEngine *taintEngine);
VOID    unlockAnalysis(UINT32 *analysisStatus);

#endif /* !__UTILS_H__ */
