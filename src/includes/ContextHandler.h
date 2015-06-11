#ifndef CONTEXTHANDLER_H
#define CONTEXTHANDLER_H

#include <cstdint>


class ContextHandler {
  public:
    virtual ~ContextHandler() { }

    virtual __uint128_t getMemValue(uint64_t mem, uint32_t readSize) const = 0;
    virtual __uint128_t getSSERegisterValue(uint64_t regID) const = 0;
    virtual uint32_t    getThreadID(void) const = 0;
    virtual uint64_t    getFlagValue(uint64_t TritFlagID) const = 0;
    virtual uint64_t    getRegisterValue(uint64_t regID) const = 0;
    virtual void        *getCtx(void) const = 0;
    virtual void        setMemValue(uint64_t mem, uint32_t readSize, __uint128_t value) const = 0;
    virtual void        setRegisterValue(uint64_t regID, uint64_t value) const = 0;
    virtual void        setSSERegisterValue(uint64_t regID, __uint128_t value) const = 0;
};

#endif // CONTEXTHANDLER_H
