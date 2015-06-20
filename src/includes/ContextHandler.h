#ifndef CONTEXTHANDLER_H
#define CONTEXTHANDLER_H

#include "TritonTypes.h"


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual uint128 getMemValue(uint64 mem, uint32 readSize) const = 0;
    virtual uint128 getSSERegisterValue(uint64 regID) const = 0;
    virtual uint32  getThreadID(void) const = 0;
    virtual uint64  getFlagValue(uint64 TritFlagID) const = 0;
    virtual uint64  getRegisterValue(uint64 regID) const = 0;
    virtual void    *getCtx(void) const = 0;
    virtual void    setMemValue(uint64 mem, uint32 readSize, uint128 value) const = 0;
    virtual void    setRegisterValue(uint64 regID, uint64 value) const = 0;
    virtual void    setSSERegisterValue(uint64 regID, uint128 value) const = 0;
};

#endif // CONTEXTHANDLER_H
