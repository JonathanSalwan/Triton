
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

    /* Initialization of an object */
    void init(const TaintEngine &other);


  public:
    bool        isMemoryTainted(uint64_t addr);
    bool        isRegTainted(uint64_t regID);
    uint64_t    getRegStatus(uint64_t regID);
    void        taintMem(uint64_t addr);
    void        untaintMem(uint64_t addr);
    void        taintReg(uint64_t regID);
    void        untaintReg(uint64_t regID);

    void        operator=(const TaintEngine &other);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif     /* !__TAINTENGINE_H__ */

