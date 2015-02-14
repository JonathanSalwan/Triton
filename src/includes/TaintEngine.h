
#ifndef   __TAINTENGINE_H__
#define   __TAINTENGINE_H__

#include <list>
#include <sstream>
#include <stdint.h>

#define TAINTED     1
#define UNTAINTED   !TAINTED

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
    void        taintAddress(uint64_t addr);
    void        untaintAddress(uint64_t addr);
    void        taintReg(uint64_t regID);
    void        untaintReg(uint64_t regID);

    void        operator=(const TaintEngine &other);

    bool        spreadTaintRegReg(uint64_t regDst, uint64_t regSrc);
    bool        spreadTaintRegImm(uint64_t regDst);
    bool        spreadTaintRegMem(uint64_t regDst, uint64_t memSrc);
    bool        spreadTaintMemImm(uint64_t memDst);
    bool        spreadTaintMemReg(uint64_t memDst, uint64_t regSrc);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif     /* !__TAINTENGINE_H__ */

