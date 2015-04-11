#ifndef _ANALYSISPROCESSOR_H_
#define _ANALYSISPROCESSOR_H_

#include "PINContextHandler.h"
#include "SolverEngine.h"
#include "Stats.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"


class AnalysisProcessor {
  public:
    AnalysisProcessor();

    /* 
     * The this->currentCtxH attribute must be updated at each instruction processing.
     * This is a dirty hack which allows Python Bindings to access to the current CPU
     * context.
     */
    void updateCurrentCtxH(CONTEXT *ctx, THREADID threadId);
    PINContextHandler *getCurrentCtxH(void);

    // Context Handler Facade  
    // ----------------------

    // Returns the thread Id.
    THREADID getThreadId(void);

    // Returns the value of the register.
    uint64_t getRegisterValue(uint64_t regID);

    // Returns the size of the register.
    uint64_t getRegisterSize(uint64_t regID);

    // Returns the value of the memory.
    uint64_t getMemoryValue(uint64_t mem, uint32_t readSize);

    // Translates a Pin REG into a Triton REG.
    uint64_t translateRegID(uint64_t regID);

    // Symbolic Engine Facade
    // ----------------------

    // Returns a symbolic element for the register (regID).
    SymbolicElement *createRegSE(std::stringstream &expr, uint64_t regID);

    // Returns a symbolic element for the memory address.
    SymbolicElement *createMemSE(std::stringstream &expr, uint64_t address);

    // Returns the ID of the symbolic element currently present in the
    // symbolic register. If there is no symbolic element, it returns UNSET.
    uint64_t getRegSymbolicID(uint64_t regID);

    // Returns the ID of the symbolic element currently present in the
    // symbolic memory. If there is no symbolic element, it returns UNSET.
    uint64_t getMemSymbolicID(uint64_t address);

    // Returns the symbolic engine reference
    SymbolicEngine &getSymbolicEngine();

    // Taint Engine Facade
    // -------------------

    // Returns the taint engine reference
    TaintEngine &getTaintEngine();

    // Taint interface.
    // Taint the symbolic element if the taint occurs.
    bool isMemTainted(uint64_t addr);
    bool isRegTainted(uint64_t reg);
    void taintReg(uint64_t reg);
    void untaintReg(uint64_t reg);
    void taintMem(uint64_t addr);
    void untaintMem(uint64_t addr);

    /* ALU Spreading */
    void aluSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint32_t writeSize);
    void aluSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint32_t writeSize);
    void aluSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst);
    void aluSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    void aluSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc);

    /* Assignment Spreading */
    void assignmentSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint64_t writeSize);
    void assignmentSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint64_t writeSize);
    void assignmentSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst);
    void assignmentSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc);

    // SolverEngine Facade

    // Returns a reference to the solver engine.
    SolverEngine &getSolverEngine();

    // Statistics Facade

    // Returns a reference to the Stats object.
    Stats     &getStats();
    void      displayStats(void);
    void      incNumberOfExpressions(uint64_t val);
    void      incNumberOfExpressions(void);
    void      incNumberOfUnknownInstruction(void);


  private:
    SymbolicEngine    symEngine;
    SolverEngine      solverEngine;
    TaintEngine       taintEngine;
    Stats             stats;
    PINContextHandler *currentCtxH;
};

#endif //_ANALYSISPROCESSOR_H_
