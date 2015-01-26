
#ifndef   __TAINTENGINE_H__
#define   __TAINTENGINE_H__

#include "pin.H"
#include "triton.h"


class TaintEngine {

  private:

    /* Tainted addresses */
    std::list<UINT64> taintedAddresses;

    /* Tainted registers */
    UINT64 taintedReg[16]; 


  public:
    TaintEngine();
    ~TaintEngine();

    UINT64    getRegStatus(UINT64 regID);
    VOID      addAddress(UINT64 addr);
    VOID      removeAddress(UINT64 addr);
    VOID      taintReg(UINT64 regID);
    VOID      untaintReg(UINT64 regID);
    bool      isMemoryTainted(UINT64 addr);
    bool      isRegTainted(UINT64 regID);

};

#endif     /* !__TAINTENGINE_H__ */

