#ifndef _CONTEXTHANDLER_H_
#define _CONTEXTHANDLER_H_

#include <cstdint>


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual uint64_t getRegisterValue(uint64_t regID) const = 0;

    // Returns the memory value with a safety dereference
    virtual uint64_t getMemValue(uint64_t mem, uint32_t readSize) const = 0;

    // Returns the thread ID
    virtual uint32_t getThreadID(void) const = 0;
};

#endif // _CONTEXTHANDLER_H_
