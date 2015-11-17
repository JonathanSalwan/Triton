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

    virtual uint128 getMemValue(reg_size mem, uint32 readSize) const = 0;
    virtual uint128 getSSERegisterValue(reg_size regID) const = 0;
    virtual uint32  getThreadID(void) const = 0;
    virtual reg_size  getFlagValue(reg_size TritFlagID) const = 0;
    virtual reg_size  getRegisterValue(reg_size regID) const = 0;
    virtual void    *getCtx(void) const = 0;
    virtual void    setMemValue(reg_size mem, uint32 readSize, uint128 value) const = 0;
    virtual void    setRegisterValue(reg_size regID, reg_size value) const = 0;
    virtual void    setSSERegisterValue(reg_size regID, uint128 value) const = 0;
};

#endif // CONTEXTHANDLER_H
