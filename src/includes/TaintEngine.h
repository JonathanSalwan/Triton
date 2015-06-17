
#ifndef   TAINTENGINE_H
#define   TAINTENGINE_H

#include <list>
#include <sstream>
#include <stdint.h>

#include "Registers.h"

#define TAINTED     1
#define UNTAINTED   !TAINTED


class TaintEngine {

  private:

    /* Tainted addresses */
    std::list<uint64_t> taintedAddresses;

    /*
     *Tainted registers.
     * Currently this is an over approximation of the taint.
     * sizeof(taintedReg) = enum REG
     */
    uint64_t taintedReg[ID_LAST_ITEM];

    /* Initialization of an object */
    void init(const TaintEngine &other);


  public:
    bool        isMemTainted(uint64_t addr);
    bool        isRegTainted(uint64_t regID);
    void        setTaintMem(uint64_t mem, uint64_t flag);
    void        setTaintReg(uint64_t regID, uint64_t flag);
    void        taintMem(uint64_t addr);
    void        taintReg(uint64_t regID);
    void        untaintMem(uint64_t addr);
    void        untaintReg(uint64_t regID);

    void        operator=(const TaintEngine &other);

    /* ALU Spreading */
    bool        aluSpreadTaintMemImm(uint64_t memDst, uint32_t writeSize);
    bool        aluSpreadTaintMemReg(uint64_t memDst, uint64_t regSrc, uint32_t writeSize);
    bool        aluSpreadTaintRegImm(uint64_t regDst);
    bool        aluSpreadTaintRegMem(uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    bool        aluSpreadTaintRegReg(uint64_t regDst, uint64_t regSrc);
    bool        aluSpreadTaintMemMem(uint64_t memDst, uint64_t memSrc, uint32_t writeSize);

    /* Assignment Spreading */
    bool        assignmentSpreadTaintMemImm(uint64_t memDst, uint32_t writeSize);
    bool        assignmentSpreadTaintMemReg(uint64_t memDst, uint64_t regSrc, uint32_t writeSize);
    bool        assignmentSpreadTaintRegImm(uint64_t regDst);
    bool        assignmentSpreadTaintRegMem(uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    bool        assignmentSpreadTaintMemMem(uint64_t memDst, uint64_t memSrc, uint32_t readSize);
    bool        assignmentSpreadTaintRegReg(uint64_t regDst, uint64_t regSrc);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif     /* !__TAINTENGINE_H__ */

