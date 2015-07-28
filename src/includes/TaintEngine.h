/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   TAINTENGINE_H
#define   TAINTENGINE_H

#include <list>
#include <sstream>
#include <stdint.h>

#include "Registers.h"
#include "TritonTypes.h"

#define TAINTED     1
#define UNTAINTED   !TAINTED


class TaintEngine {

  private:

    /* Tainted addresses */
    std::list<uint64> taintedAddresses;

    /*
     *Tainted registers.
     * Currently this is an over approximation of the taint.
     * sizeof(taintedReg) = enum REG
     */
    uint64 taintedReg[ID_LAST_ITEM];

    /* Initialization of an object */
    void init(const TaintEngine &other);


  public:
    bool        isMemTainted(uint64 addr);
    bool        isRegTainted(uint64 regID);
    void        setTaintMem(uint64 mem, uint64 flag);
    void        setTaintReg(uint64 regID, uint64 flag);
    void        taintMem(uint64 addr);
    void        taintReg(uint64 regID);
    void        untaintMem(uint64 addr);
    void        untaintReg(uint64 regID);

    void        operator=(const TaintEngine &other);

    /* ALU Spreading */
    bool        aluSpreadTaintMemImm(uint64 memDst, uint32 writeSize);
    bool        aluSpreadTaintMemReg(uint64 memDst, uint64 regSrc, uint32 writeSize);
    bool        aluSpreadTaintRegImm(uint64 regDst);
    bool        aluSpreadTaintRegMem(uint64 regDst, uint64 memSrc, uint32 readSize);
    bool        aluSpreadTaintRegReg(uint64 regDst, uint64 regSrc);
    bool        aluSpreadTaintMemMem(uint64 memDst, uint64 memSrc, uint32 writeSize);

    /* Assignment Spreading */
    bool        assignmentSpreadTaintExprMem(uint64 memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprReg(uint64 regSrc);
    bool        assignmentSpreadTaintExprRegMem(uint64 regSrc, uint64 memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprRegReg(uint64 regSrc1, uint64 regSrc2);
    bool        assignmentSpreadTaintMemImm(uint64 memDst, uint32 writeSize);
    bool        assignmentSpreadTaintMemMem(uint64 memDst, uint64 memSrc, uint32 readSize);
    bool        assignmentSpreadTaintMemReg(uint64 memDst, uint64 regSrc, uint32 writeSize);
    bool        assignmentSpreadTaintRegImm(uint64 regDst);
    bool        assignmentSpreadTaintRegMem(uint64 regDst, uint64 memSrc, uint32 readSize);
    bool        assignmentSpreadTaintRegReg(uint64 regDst, uint64 regSrc);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif     /* !__TAINTENGINE_H__ */

