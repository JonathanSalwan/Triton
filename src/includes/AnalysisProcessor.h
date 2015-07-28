/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef ANALYSISPROCESSOR_H
#define ANALYSISPROCESSOR_H

#include "ContextHandler.h"
#include "Inst.h"
#include "SMT2Lib.h"
#include "SnapshotEngine.h"
#include "SolverEngine.h"
#include "Stats.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "Trace.h"
#include "TritonTypes.h"
#include "Z3ast.h"



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

    /* Mutex */
    void            lock(void);
    void            unlock(void);

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

    /* Returns a symbolic expression for the register (regID) */
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID);
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, std::string comment);
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, uint64 regSize);
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, uint64 regSize, std::string comment);

    /* Returns a symbolic expression for the memory address */
    SymbolicExpression *createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 address, uint64 writeSize);
    SymbolicExpression *createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 address, uint64 writeSize, std::string comment);

    /* Returns a symbolic expression. This methods is mainly used for temporary expression */
    SymbolicExpression *createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr);
    SymbolicExpression *createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic register. If there is no symbolic expression, it returns UNSET
     */
    uint64 getRegSymbolicID(uint64 regID);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic memory. If there is no symbolic expression, it returns UNSET
     */
    uint64 getMemSymbolicID(uint64 address);

    /* Returns the symbolic expression from its id */
    SymbolicExpression *getExpressionFromId(uint64 id);

    /* Returns all symbolic expressions */
    std::vector<SymbolicExpression *> getExpressions(void);

    /* Returns a list which contains all tainted expressions */
    std::list<SymbolicExpression *> getTaintedExpressions(void);

    /* Returns the full symbolic expression backtracked */
    smt2lib::smtAstAbstractNode *getFullExpression(smt2lib::smtAstAbstractNode *node);

    /* Returns the symbolic engine reference */
    SymbolicEngine &getSymbolicEngine(void);

    /* Converts an expression, register or memory to a symbolic variable */
    SymbolicVariable *convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable *convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable *convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(uint64 symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(uint64 exprId);
    std::list<uint64> getPathConstraints(void);

    /* Build a symbolic register operand */
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(uint64 regID, uint64 regSize);
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(uint64 regID, uint64 regSize, uint64 highExtract, uint64 lowExtract);
    smt2lib::smtAstAbstractNode *buildSymbolicMemOperand(uint64 mem, uint64 memSize);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(uint64 flagID, uint64 size);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(uint64 flagID);

    /* Concretize register and memory */
    void concretizeAllReg(void);
    void concretizeAllMem(void);
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
     * Taint the symbolic expression if the taint occurs.
     */
    bool isMemTainted(uint64 addr);
    bool isRegTainted(uint64 reg);
    void setTaintMem(SymbolicExpression *se, uint64 mem, uint64 flag);
    void setTaintReg(SymbolicExpression *se, uint64 reg, uint64 flag);
    void taintMem(uint64 addr);
    void taintReg(uint64 reg);
    void untaintMem(uint64 addr);
    void untaintReg(uint64 reg);

    /* ALU Spreading */
    void aluSpreadTaintMemImm(SymbolicExpression *se, uint64 memDst, uint32 writeSize);
    void aluSpreadTaintMemReg(SymbolicExpression *se, uint64 memDst, uint64 regSrc, uint32 writeSize);
    void aluSpreadTaintRegImm(SymbolicExpression *se, uint64 regDst);
    void aluSpreadTaintRegMem(SymbolicExpression *se, uint64 regDst, uint64 memSrc, uint32 readSize);
    void aluSpreadTaintRegReg(SymbolicExpression *se, uint64 regDst, uint64 regSrc);
    void aluSpreadTaintMemMem(SymbolicExpression *se, uint64 memDst, uint64 memSrc, uint32 writeSize);

    /* Assignment Spreading */
    void assignmentSpreadTaintExprMem(SymbolicExpression *se, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintExprReg(SymbolicExpression *se, uint64 regSrc);
    void assignmentSpreadTaintExprRegMem(SymbolicExpression *se, uint64 regSrc, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintExprRegReg(SymbolicExpression *se, uint64 regSrc1, uint64 regSrc2);
    void assignmentSpreadTaintMemImm(SymbolicExpression *se, uint64 memDst, uint64 writeSize);
    void assignmentSpreadTaintMemMem(SymbolicExpression *se, uint64 memDst, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintMemReg(SymbolicExpression *se, uint64 memDst, uint64 regSrc, uint64 writeSize);
    void assignmentSpreadTaintRegImm(SymbolicExpression *se, uint64 regDst);
    void assignmentSpreadTaintRegMem(SymbolicExpression *se, uint64 regDst, uint64 memSrc, uint32 readSize);
    void assignmentSpreadTaintRegReg(SymbolicExpression *se, uint64 regDst, uint64 regSrc);


    /*
     * Solver Engine Facade
     * --------------------
     */

    /* Returns a reference to the solver engine. */
    SolverEngine                    &getSolverEngine();
    /* Returns models */
    std::list<Smodel>               getModel(smt2lib::smtAstAbstractNode *node);
    std::vector<std::list<Smodel>>  getModels(smt2lib::smtAstAbstractNode *node, uint64 limit);


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
    bool            isSnapshotEnabled(void);

   /*
    * Convert the SMT AST to a Z3 ast and evaluate it
    * ------------------------------------------------
    */
    uint512 evaluateAST(smt2lib::smtAstAbstractNode *node);


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
