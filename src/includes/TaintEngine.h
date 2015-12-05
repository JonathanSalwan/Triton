/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef TAINTENGINE_H
#define TAINTENGINE_H

#include <map>
#include <sstream>
#include <stdint.h>

#include "Registers.h"
#include "TritonTypes.h"

#define TAINTED     1
#define UNTAINTED   !TAINTED


class TaintEngine {

  private:

    /* Tainted addresses */
    std::map<__uint, bool> taintedAddresses;

    /*
     *Tainted registers.
     * Currently this is an over approximation of the taint.
     * sizeof(taintedReg) = enum REG
     */
    __uint taintedReg[ID_LAST_ITEM];

    /* Initialization of an object */
    void init(const TaintEngine &other);


  public:
    bool        isMemTainted(__uint addr, uint32 size=1);
    bool        isRegTainted(__uint regID);
    void        setTaintMem(__uint mem, __uint flag);
    void        setTaintReg(__uint regID, __uint flag);
    void        taintMem(__uint addr);
    void        taintReg(__uint regID);
    void        untaintMem(__uint addr);
    void        untaintReg(__uint regID);

    void        operator=(const TaintEngine &other);

    /* ALU Spreading */
    bool        aluSpreadTaintMemImm(__uint memDst, uint32 writeSize);
    bool        aluSpreadTaintMemReg(__uint memDst, __uint regSrc, uint32 writeSize);
    bool        aluSpreadTaintRegImm(__uint regDst);
    bool        aluSpreadTaintRegMem(__uint regDst, __uint memSrc, uint32 readSize);
    bool        aluSpreadTaintRegReg(__uint regDst, __uint regSrc);
    bool        aluSpreadTaintMemMem(__uint memDst, __uint memSrc, uint32 writeSize);

    /* Assignment Spreading */
    bool        assignmentSpreadTaintExprMem(__uint memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprReg(__uint regSrc);
    bool        assignmentSpreadTaintExprRegMem(__uint regSrc, __uint memSrc, uint32 readSize);
    bool        assignmentSpreadTaintExprRegReg(__uint regSrc1, __uint regSrc2);
    bool        assignmentSpreadTaintMemImm(__uint memDst, uint32 writeSize);
    bool        assignmentSpreadTaintMemMem(__uint memDst, __uint memSrc, uint32 readSize);
    bool        assignmentSpreadTaintMemReg(__uint memDst, __uint regSrc, uint32 writeSize);
    bool        assignmentSpreadTaintRegImm(__uint regDst);
    bool        assignmentSpreadTaintRegMem(__uint regDst, __uint memSrc, uint32 readSize);
    bool        assignmentSpreadTaintRegReg(__uint regDst, __uint regSrc);

    TaintEngine();
    TaintEngine(const TaintEngine &copy);
    ~TaintEngine();
};

#endif /* !__TAINTENGINE_H__ */
#endif /* LIGHT_VERSION */

