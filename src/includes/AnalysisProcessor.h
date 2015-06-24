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
#include "TritonTypes.h"



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
    uint32      getThreadID(void);

    /* Returns the value of the register */
    uint64      getRegisterValue(uint64 regID);
    uint64      getFlagValue(uint64 flagID);
    uint128     getSSERegisterValue(uint64 regID);

    /* Set the value into the register */
    void        setRegisterValue(uint64 regID, uint64 value);
    void        setSSERegisterValue(uint64 regID, uint128 value);

    /* Returns the value of the memory */
    uint128     getMemValue(uint64 mem, uint32 readSize);
    void        setMemValue(uint64 mem, uint32 writeSize, uint128 value);

    /*
     * Symbolic Engine Facade
     * ----------------------
     */

    /* Returns a symbolic element for the register (regID) */
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64 regID);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, std::string comment);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, uint64 regSize);
    SymbolicElement *createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, uint64 regSize, std::string comment);

    /* Returns a symbolic element for the memory address */
    SymbolicElement *createMemSE(Inst &inst, std::stringstream &expr, uint64 address, uint64 writeSize);
    SymbolicElement *createMemSE(Inst &inst, std::stringstream &expr, uint64 address, uint64 writeSize, std::string comment);

    /* Returns a symbolic element. This methods is mainly used for temporary expression */
    SymbolicElement *createSE(Inst &inst, std::stringstream &expr);
    SymbolicElement *createSE(Inst &inst, std::stringstream &expr, std::string comment);

    /*
     * Returns the ID of the symbolic element currently present in the
     * symbolic register. If there is no symbolic element, it returns UNSET
     */
    uint64 getRegSymbolicID(uint64 regID);

    /*
     * Returns the ID of the symbolic element currently present in the
     * symbolic memory. If there is no symbolic element, it returns UNSET
     */
    uint64 getMemSymbolicID(uint64 address);

    /* Returns the symbolic element from its id */
    SymbolicElement *getElementFromId(uint64 id);

    /* Returns the backtracked symbolic expression from an id */
    std::string getBacktrackedExpressionFromId(uint64 id);

    /* Returns the symbolic engine reference */
    SymbolicEngine &getSymbolicEngine(void);

    /* Converts an expression, register or memory to a symbolic variable */
    uint64 convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment);
    uint64 convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment);
    uint64 convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(uint64 symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(uint64 exprId);
    std::list<uint64> getPathConstraints(void);

    /* Build a symbolic register operand */
    std::string buildSymbolicRegOperand(uint64 regID, uint64 regSize);
    std::string buildSymbolicRegOperand(uint64 regID, uint64 regSize, uint64 highExtract, uint64 lowExtract);
    std::string buildSymbolicMemOperand(uint64 mem, uint64 memSize);
    std::string buildSymbolicFlagOperand(uint64 flagID, uint64 size);
    std::string buildSymbolicFlagOperand(uint64 flagID);

    /* Concretize register and memory */
    void concretizeReg(uint64 regID);
    void concretizeMem(uint64 mem);


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
    bool isMemTainted(uint64 addr);
    bool isRegTainted(uint64 reg);
    void setTaintMem(SymbolicElement *se, uint64 mem, uint64 flag);
    void setTaintReg(SymbolicElement *se, uint64 reg, uint64 flag);
    void taintMem(uint64 addr);
    void taintReg(uint64 reg);
    void untaintMem(uint64 addr);
    void untaintReg(uint64 reg);

    /* ALU Spreading */
    void aluSpreadTaintMemImm(SymbolicElement *se, uint64 memDst, uint32 writeSize);
    void aluSpreadTaintMemReg(SymbolicElement *se, uint64 memDst, uint64 regSrc, uint32 writeSize);
    void aluSpreadTaintRegImm(SymbolicElement *se, uint64 regDst);
    void aluSpreadTaintRegMem(SymbolicElement *se, uint64 regDst, uint64 memSrc, uint32 readSize);
    void aluSpreadTaintRegReg(SymbolicElement *se, uint64 regDst, uint64 regSrc);
    void aluSpreadTaintMemMem(SymbolicElement *se, uint64 memDst, uint64 memSrc, uint32 writeSize);

    /* Assignment Spreading */
    void assignmentSpreadTaintExprMem(SymbolicElement *se, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintExprReg(SymbolicElement *se, uint64 regSrc);
    void assignmentSpreadTaintExprRegMem(SymbolicElement *se, uint64 regSrc, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintExprRegReg(SymbolicElement *se, uint64 regSrc1, uint64 regSrc2);
    void assignmentSpreadTaintMemImm(SymbolicElement *se, uint64 memDst, uint64 writeSize);
    void assignmentSpreadTaintMemMem(SymbolicElement *se, uint64 memDst, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintMemReg(SymbolicElement *se, uint64 memDst, uint64 regSrc, uint64 writeSize);
    void assignmentSpreadTaintRegImm(SymbolicElement *se, uint64 regDst);
    void assignmentSpreadTaintRegMem(SymbolicElement *se, uint64 regDst, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintRegReg(SymbolicElement *se, uint64 regDst, uint64 regSrc);


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
    Stats   &getStats(void);
    void    incNumberOfBranchesTaken(void);
    void    incNumberOfBranchesTaken(bool isBranch);
    void    incNumberOfExpressions(uint64 val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);
    uint64  getNumberOfBranchesTaken(void);
    uint64  getNumberOfExpressions(void);
    uint64  getTimeOfExecution(void);
    uint64  getNumberOfUnknownInstruction(void);


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
    void            addSnapshotModification(uint64 addr, char byte);
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
