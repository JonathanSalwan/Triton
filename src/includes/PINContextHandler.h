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

    bool      isMustBeExecuted(void) const;
    uint128   getMemValue(__uint mem, uint32 readSize) const;
    uint128   getSSERegisterValue(__uint regID) const;
    uint32    getThreadID(void) const;
    __uint    getFlagValue(__uint TritFlagID) const;
    __uint    getRegisterValue(__uint regID) const;
    void      *getCtx(void) const;
    void      executeContext(void);
    void      setExecutedFlag(bool flag);
    void      setMemValue(__uint mem, uint32 readSize, uint128 value) const;
    void      setRegisterValue(__uint TritRegID, __uint value);
    void      setSSERegisterValue(__uint TritRegID, uint128 value);

  private:
    CONTEXT   *_ctx;
    THREADID  _threadId;
    bool      mustBeExecuted;
};

#endif // PINCONTEXTHANDLER_H

