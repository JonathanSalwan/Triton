/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef PINCONTEXTHANDLER_H
#define PINCONTEXTHANDLER_H

#include "pin.H"

#include "ContextHandler.h"
#include "Registers.h"
#include "TritonTypes.h"


class PINContextHandler: public ContextHandler {
  public:
    PINContextHandler(CONTEXT *ctx, THREADID threadId);

    uint128   getMemValue(reg_size mem, uint32 readSize) const;
    uint128   getSSERegisterValue(reg_size regID) const;
    uint32    getThreadID(void) const;
    reg_size    getFlagValue(reg_size TritFlagID) const;
    reg_size    getRegisterValue(reg_size regID) const;
    void      *getCtx(void) const;
    void      setMemValue(reg_size mem, uint32 readSize, uint128 value) const;
    void      setRegisterValue(reg_size TritRegID, reg_size value) const;
    void      setSSERegisterValue(reg_size TritRegID, uint128 value) const;

  private:
    CONTEXT   *_ctx;
    THREADID  _threadId;
};

#endif // PINCONTEXTHANDLER_H
