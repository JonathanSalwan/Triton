#ifndef _PINCONTEXTHANDLER_H_
#define _PINCONTEXTHANDLER_H_

#include <cstdint>

#include "pin.H"

#include "ContextHandler.h"
#include "Registers.h"


class PINContextHandler: public ContextHandler {
  public:
    PINContextHandler(CONTEXT *ctx, THREADID threadId);

    THREADID  getThreadID(void) const;
    uint64_t  convertTritonReg2PinReg(uint64_t regID) const;
    uint64_t  getMemValue(uint64_t mem, uint32_t readSize) const;
    uint64_t  getRegisterSize(uint64_t regID) const;
    uint64_t  getRegisterValue(uint64_t regID) const;
    uint64_t  convertPinReg2TritonReg(uint64_t regID) const;

  private:
    CONTEXT   *_ctx;
    THREADID  _threadId;
};

#endif // _PINCONTEXTHANDLER_H_
