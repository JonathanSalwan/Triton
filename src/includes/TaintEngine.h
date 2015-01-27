
#ifndef   __TAINTENGINE_H__
#define   __TAINTENGINE_H__

#include <list>
#include <sstream>
#include <stdint.h>


#define TAINTED       1


class TaintEngine {

  private:

    /* Tainted addresses */
    std::list<uint64_t> taintedAddresses;

    /* Tainted registers */
    uint64_t taintedReg[16];


  public:
    TaintEngine();
    ~TaintEngine();

    bool       isMemoryTainted(uint64_t addr);
    bool       isRegTainted(uint64_t regID);
    uint64_t   getRegStatus(uint64_t regID);
    void       addAddress(uint64_t addr);
    void       removeAddress(uint64_t addr);
    void       taintReg(uint64_t regID);
    void       untaintReg(uint64_t regID);

};

#endif     /* !__TAINTENGINE_H__ */

