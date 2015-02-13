#ifndef _PINCONTEXTHANDLER_H_
#define _PINCONTEXTHANDLER_H_

#include <cstdint>

#include "pin.H"

#include "ContextHandler.h"
#include "Registers.h"


class PINContextHandler: public ContextHandler {
  public:
    PINContextHandler(CONTEXT *ctx);

    uint64_t getRegisterValue(uint64_t regID) const;
    uint64_t getRegisterSize(uint64_t regID) const;
    uint64_t translateRegID(uint64_t regID) const;
    uint64_t getMemoryValue(uint64_t mem, uint32_t readSize) const;

  private:
    CONTEXT *_ctx;
};

#endif // _PINCONTEXTHANDLER_H_
