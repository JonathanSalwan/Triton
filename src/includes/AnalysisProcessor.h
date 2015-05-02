#ifndef _ANALYSISPROCESSOR_H_
#define _ANALYSISPROCESSOR_H_

#include "ContextHandler.h"
#include "SnapshotEngine.h"
#include "SolverEngine.h"
#include "Stats.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "Trace.h"


class AnalysisProcessor {
  public:
    AnalysisProcessor();

    /*
     * The this->currentCtxH attribute must be updated at each instruction processing.
     * This is a dirty hack which allows Python Bindings to access to the current CPU
     * context.
     */
    void updateCurrentCtxH(ContextHandler *ctxtHandler);
    ContextHandler *getCurrentCtxH(void);

    // Context Handler Facade
    // ----------------------

    // Returns the thread Id.
    uint32_t getThreadID(void);

    // Returns the value of the register.
    uint64_t getRegisterValue(uint64_t regID);
    uint64_t getCFValue(void);

    // Set the value into the register.
    void setRegisterValue(uint64_t regID, uint64_t value);

    // Returns the value of the memory.
    uint64_t getMemValue(uint64_t mem, uint32_t readSize);

    // Symbolic Engine Facade
    // ----------------------

    // Returns a symbolic element for the register (regID).
    SymbolicElement *createRegSE(std::stringstream &expr, uint64_t regID);

    // Returns a symbolic element for the memory address.
    SymbolicElement *createMemSE(std::stringstream &expr, uint64_t address);

    // Returns a symbolic element. This methods is mainly used for temporary expression.
    SymbolicElement *createSE(std::stringstream &expr);

    // Returns the ID of the symbolic element currently present in the
    // symbolic register. If there is no symbolic element, it returns UNSET.
    uint64_t getRegSymbolicID(uint64_t regID);

    // Returns the ID of the symbolic element currently present in the
    // symbolic memory. If there is no symbolic element, it returns UNSET.
    uint64_t getMemSymbolicID(uint64_t address);

    // Returns the symbolic element from its id.
    SymbolicElement *getElementFromId(uint64_t id);

    // Returns the backtracked symbolic expression from an id.
    std::string getBacktrackedExpressionFromId(uint64_t id);

    // Returns the symbolic engine reference
    SymbolicEngine &getSymbolicEngine(void);

    // Converts an expression to a symbolic variable
    bool convertExprToSymVar(uint64_t exprId, uint64_t symVarSize);

    // Assigns a symbolic variable to an expression
    bool assignExprToSymVar(uint64_t exprId, uint64_t symVarId);

    uint64_t memoryFromSymVar(uint64_t symVar);
    uint64_t symVarFromMemory(uint64_t address);


    // Taint Engine Facade
    // -------------------

    // Returns the taint engine reference
    TaintEngine &getTaintEngine(void);

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
    void aluSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc);

    /* Assignment Spreading */
    void assignmentSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint64_t writeSize);
    void assignmentSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint64_t writeSize);
    void assignmentSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst);
    void assignmentSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc);

    // SolverEngine Facade
    // -------------------

    // Returns a reference to the solver engine.
    SolverEngine                                            &getSolverEngine();
    std::list< std::pair<std::string, unsigned long long> > getModel(std::string expr);

    // Statistics Facade
    // -----------------

    // Returns a reference to the Stats object.
    Stats     &getStats(void);
    void      incNumberOfBranchesTaken(void);
    void      incNumberOfBranchesTaken(bool isBranch);
    void      incNumberOfExpressions(uint64_t val);
    void      incNumberOfExpressions(void);
    void      incNumberOfUnknownInstruction(void);
    uint64_t  getNumberOfBranchesTaken(void);
    uint64_t  getNumberOfExpressions(void);
    uint64_t  getTimeOfExecution(void);
    uint64_t  getNumberOfUnknownInstruction(void);

    // Trace Facade
    // ------------

    Inst      *getLastInstruction(void);
    Trace     &getTrace(void);
    void      addInstructionToTrace(Inst *instruction);
    void      saveTrace(std::stringstream &file);

    // Snapshot Facade
    // ---------------

    SnapshotEngine  &getSnapshotEngine(void);
    bool            isSnapshotLocked(void);
    void            addSnapshotModification(uint64_t addr, char byte);
    void            takeSnapshot(void);
    void            restoreSnapshot(void);
    void            disableSnapshot(void);
    bool            isSnapshotEnable(void);


  private:
    SymbolicEngine    symEngine;
    SolverEngine      solverEngine;
    TaintEngine       taintEngine;
    SnapshotEngine    snapshotEngine;
    Stats             stats;
    Trace             trace;
    ContextHandler    *currentCtxH;
};

#endif //_ANALYSISPROCESSOR_H_
