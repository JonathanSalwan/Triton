/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef TAINTENGINE_H
#define TAINTENGINE_H

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
    std::list<reg_size> taintedAddresses;

    /*
     *Tainted registers.
     * Currently this is an over approximation of the taint.
     * sizeof(taintedReg) = enum REG
     */
    reg_size taintedReg[ID_LAST_ITEM];

    /* Initialization of an object */
    void init(const TaintEngine &other);


  public:
    bool        isMemTainted(reg_size addr);
    bool        isRegTainted(reg_size regID);
    void        setTaintMem(reg_size mem, reg_size flag);
    void        setTaintReg(reg_size regID, reg_size flag);
    void        taintMem(reg_size addr);
    void        taintReg(reg_size regID);
    void        untaintMem(reg_size addr);
    void        untaintReg(reg_size regID);

    void        operator=(const TaintEngine &other);

    /* ALU Spreading */
    bool        aluSpreadTaintMemImm(reg_size memDst, uint32 writeSize);
    bool        aluSpreadTaintMemReg(reg_size memDst, reg_size regSrc, uint32 writeSize);
    bool        aluSpreadTaintRegImm(reg_size regDst);
    bool        aluSpreadTaintRegMem(reg_size regDst, reg_size memSrc, uint32 readSize);
    bool        aluSpreadTaintRegReg(reg_size regDst, reg_size regSrc);
    bool        aluSpreadTaintMemMem(reg_size memDst, reg_size memSrc, uint32 writeSize);

    /* Assignment Spreading */
    bool        assignmentSpreadTaintExprMem(reg_size memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprReg(reg_size regSrc);
    bool        assignmentSpreadTaintExprRegMem(reg_size regSrc, reg_size memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprRegReg(reg_size regSrc1, reg_size regSrc2);
    bool        assignmentSpreadTaintMemImm(reg_size memDst, uint32 writeSize);
    bool        assignmentSpreadTaintMemMem(reg_size memDst, reg_size memSrc, uint32 readSize);
    bool        assignmentSpreadTaintMemReg(reg_size memDst, reg_size regSrc, uint32 writeSize);
    bool        assignmentSpreadTaintRegImm(reg_size regDst);
    bool        assignmentSpreadTaintRegMem(reg_size regDst, reg_size memSrc, uint32 readSize);
    bool        assignmentSpreadTaintRegReg(reg_size regDst, reg_size regSrc);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif /* !__TAINTENGINE_H__ */
#endif /* LIGHT_VERSION */

