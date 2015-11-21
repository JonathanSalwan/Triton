/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef CONTEXTHANDLER_H
#define CONTEXTHANDLER_H

#include "TritonTypes.h"


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual bool    isMustBeExecuted(void) const = 0;
    virtual uint128 getMemValue(__uint mem, uint32 readSize) const = 0;
    virtual uint128 getSSERegisterValue(__uint regID) const = 0;
    virtual uint32  getThreadID(void) const = 0;
    virtual __uint  getFlagValue(__uint TritFlagID) const = 0;
    virtual __uint  getRegisterValue(__uint regID) const = 0;
    virtual void    *getCtx(void) const = 0;
    virtual void    executeContext(void) = 0;
    virtual void    setExecutedFlag(bool flag) = 0;
    virtual void    setMemValue(__uint mem, uint32 readSize, uint128 value) const = 0;
    virtual void    setRegisterValue(__uint regID, __uint value) = 0;
    virtual void    setSSERegisterValue(__uint regID, uint128 value) = 0;
};

#endif // CONTEXTHANDLER_H
