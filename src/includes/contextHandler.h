#ifndef _CONTEXTHANDLER_H_
#define _CONTEXTHANDLER_H_

#include <cstdint>


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual uint64_t getRegisterValue(uint64_t regID) const = 0;

    // Return the size in bytes of the register.
    virtual uint64_t getRegisterSize(uint64_t regID) const = 0;

    // Translate the register ID from instrumentation to the inner ID.
    virtual uint64_t translateRegID(uint64_t regID) const = 0;
};

#endif // _CONTEXTHANDLER_H_
