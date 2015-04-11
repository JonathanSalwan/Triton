#ifndef _CONTEXTHANDLER_H_
#define _CONTEXTHANDLER_H_

#include <cstdint>


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual uint64_t getRegisterValue(uint64_t regID) const = 0;

    // Returns the size in bytes of the register.
    virtual uint64_t getRegisterSize(uint64_t regID) const = 0;

    // Translates the register ID from instrumentation to the inner ID.
    virtual uint64_t convertPinReg2TritonReg(uint64_t regID) const = 0;

    // Returns the memory value with a safety dereference
    virtual uint64_t getMemValue(uint64_t mem, uint32_t readSize) const = 0;

    // Returns the thread ID
    virtual uint32_t getThreadID(void) const = 0;
};

#endif // _CONTEXTHANDLER_H_
