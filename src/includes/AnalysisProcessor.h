#ifndef ANALYSISPROCESSOR_H
#define ANALYSISPROCESSOR_H

#include "ContextHandler.h"
#include "Inst.h"
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
    void            updateCurrentCtxH(ContextHandler *ctxtHandler);
    ContextHandler *getCurrentCtxH(void);

    /*
     * Context Handler Facade
     * ----------------------
     */

    /* Returns the thread Id */
    uint32_t      getThreadID(void);

    /* Returns the value of the register */
    uint64_t      getRegisterValue(uint64_t regID);
    uint64_t      getFlagValue(uint64_t flagID);
    __uint128_t   getSSERegisterValue(uint64_t regID);

    /* Set the value into the register */
    void          setRegisterValue(uint64_t regID, uint64_t value);
    void          setSSERegisterValue(uint64_t regID, __uint128_t value);

    /* Returns the value of the memory */
    __uint128_t   getMemValue(uint64_t mem, uint32_t readSize);
    void          setMemValue(uint64_t mem, uint32_t writeSize, __uint128_t value);

    /*
     * Symbolic Engine Facade
     * ----------------------
     */

    /* Returns a symbolic element for the register (regID) */
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, std::string comment);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, uint64_t regSize);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, uint64_t regSize, std::string comment);

    /* Returns a symbolic element for the memory address */
    SymbolicElement *createMemSE(Inst &inst, std::stringstream &expr, uint64_t address, uint64_t writeSize);
    SymbolicElement *createMemSE(Inst &inst, std::stringstream &expr, uint64_t address, uint64_t writeSize, std::string comment);

    /* Returns a symbolic element. This methods is mainly used for temporary expression */
    SymbolicElement *createSE(Inst &inst, std::stringstream &expr);
    SymbolicElement *createSE(Inst &inst, std::stringstream &expr, std::string comment);

    /*
     * Returns the ID of the symbolic element currently present in the
     * symbolic register. If there is no symbolic element, it returns UNSET
     */
    uint64_t getRegSymbolicID(uint64_t regID);

    /*
     * Returns the ID of the symbolic element currently present in the
     * symbolic memory. If there is no symbolic element, it returns UNSET
     */
    uint64_t getMemSymbolicID(uint64_t address);

    /* Returns the symbolic element from its id */
    SymbolicElement *getElementFromId(uint64_t id);

    /* Returns the backtracked symbolic expression from an id */
    std::string getBacktrackedExpressionFromId(uint64_t id);

    /* Returns the symbolic engine reference */
    SymbolicEngine &getSymbolicEngine(void);

    /* Converts an expression, register or memory to a symbolic variable */
    uint64_t convertExprToSymVar(uint64_t exprId, uint64_t symVarSize);
    uint64_t convertMemToSymVar(uint64_t memAddr, uint64_t symVarSize);
    uint64_t convertRegToSymVar(uint64_t regId, uint64_t symVarSize);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(uint64_t symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(uint64_t exprId);
    std::list<uint64_t> getPathConstraints(void);

    /* Build a symbolic register operand */
    std::string buildSymbolicRegOperand(uint64_t regID, uint64_t regSize);
    std::string buildSymbolicRegOperand(uint64_t regID, uint64_t regSize, uint64_t highExtract, uint64_t lowExtract);
    std::string buildSymbolicMemOperand(uint64_t mem, uint64_t memSize);
    std::string buildSymbolicFlagOperand(uint64_t flagID, uint64_t size);
    std::string buildSymbolicFlagOperand(uint64_t flagID);

    /* Concretize register and memory */
    void concretizeReg(uint64_t regID);
    void concretizeMem(uint64_t mem);


    /*
     * Taint Engine Facade
     * -------------------
     */

    /* Returns the taint engine reference */
    TaintEngine &getTaintEngine(void);

    /*
     * Taint interface.
     * Taint the symbolic element if the taint occurs.
     */
    bool isMemTainted(uint64_t addr);
    bool isRegTainted(uint64_t reg);
    void setTaintMem(SymbolicElement *se, uint64_t mem, uint64_t flag);
    void setTaintReg(SymbolicElement *se, uint64_t reg, uint64_t flag);
    void taintMem(uint64_t addr);
    void taintReg(uint64_t reg);
    void untaintMem(uint64_t addr);
    void untaintReg(uint64_t reg);

    /* ALU Spreading */
    void aluSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint32_t writeSize);
    void aluSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint32_t writeSize);
    void aluSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst);
    void aluSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    void aluSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc);
    void aluSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t writeSize);

    /* Assignment Spreading */
    void assignmentSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint64_t writeSize);
    void assignmentSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint64_t writeSize);
    void assignmentSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst);
    void assignmentSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t readSize);
    void assignmentSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc);


    /*
     * Solver Engine Facade
     * --------------------
     */

    /* Returns a reference to the solver engine. */
    SolverEngine &getSolverEngine();
    std::list< std::pair<std::string, unsigned long long> > getModel(std::string expr);


    /*
     * Statistics Facade
     * -----------------
     */

    /* Returns a reference to the Stats object. */
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


    /*
     * Trace Facade
     * ------------
     */

    Inst      *getLastInstruction(void);
    Trace     &getTrace(void);
    void      addInstructionToTrace(Inst *instruction);
    void      saveTrace(std::stringstream &file);


    /*
     * Snapshot Facade
     * ---------------
     */

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
