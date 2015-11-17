/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef ANALYSISPROCESSOR_H
#define ANALYSISPROCESSOR_H

#include "ContextHandler.h"
#include "ImmediateOperand.h"
#include "Inst.h"
#include "MemoryOperand.h"
#include "RegisterOperand.h"
#include "Trace.h"
#include "TritonTypes.h"

#ifndef LIGHT_VERSION
  #include "SMT2Lib.h"
  #include "SnapshotEngine.h"
  #include "SolverEngine.h"
  #include "Stats.h"
  #include "SymbolicEngine.h"
  #include "TaintEngine.h"
  #include "Z3ast.h"
#endif



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
    reg_size      getRegisterValue(RegisterOperand &reg);
    reg_size      getFlagValue(RegisterOperand &flag);
    uint128     getSSERegisterValue(RegisterOperand &reg);

    /* Set the value into the register */
    void        setRegisterValue(RegisterOperand &reg, reg_size value);
    void        setSSERegisterValue(RegisterOperand &reg, uint128 value);

    /* Returns the value of the memory */
    uint128     getMemValue(MemoryOperand &mem, uint32 readSize);
    uint128     getMemValue(reg_size mem, uint32 readSize);
    void        setMemValue(MemoryOperand &mem, uint32 writeSize, uint128 value);


    /*
     * Trace Facade
     * ------------
     */

    Inst      *getLastInstruction(void);
    Trace     &getTrace(void);
    void      addInstructionToTrace(Inst *instruction);
    void      clearTrace(void);


    #ifndef LIGHT_VERSION
    /*
     * Symbolic Engine Facade
     * ----------------------
     */

    /* Returns a symbolic expression for the flag register */
    SymbolicExpression *createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment="");

    /* Returns a symbolic expression for the register */
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, reg_size regSize, std::string comment="");

    /* Returns a symbolic expression for the memory address */
    SymbolicExpression *createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, reg_size writeSize, std::string comment="");

    /* Returns a symbolic expression. This methods is mainly used for temporary expression */
    SymbolicExpression *createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment="");

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic register. If there is no symbolic expression, it returns UNSET
     */
    reg_size getRegSymbolicID(RegisterOperand &reg);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic memory. If there is no symbolic expression, it returns UNSET
     */
    reg_size getMemSymbolicID(MemoryOperand &mem);
    reg_size getMemSymbolicID(reg_size address);

    /* Returns the symbolic expression from its id */
    SymbolicExpression *getExpressionFromId(reg_size id);

    /* Returns all symbolic expressions */
    std::vector<SymbolicExpression *> getExpressions(void);

    /* Returns a list which contains all tainted expressions */
    std::list<SymbolicExpression *> getTaintedExpressions(void);

    /* Returns the full symbolic expression backtracked */
    smt2lib::smtAstAbstractNode *getFullExpression(smt2lib::smtAstAbstractNode *node);

    /* Returns the symbolic engine reference */
    SymbolicEngine &getSymbolicEngine(void);

    /* Converts an expression, register or memory to a symbolic variable */
    SymbolicVariable *convertExprToSymVar(reg_size exprId, reg_size symVarSize, std::string symVarComment);
    SymbolicVariable *convertMemToSymVar(MemoryOperand &mem, reg_size symVarSize, std::string symVarComment);
    SymbolicVariable *convertRegToSymVar(RegisterOperand &reg, reg_size symVarSize, std::string symVarComment);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(reg_size symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(reg_size exprId);
    std::list<reg_size> getPathConstraints(void);

    /* Build a symbolic register operand */
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, reg_size regSize);
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, reg_size regSize, reg_size highExtract, reg_size lowExtract);
    smt2lib::smtAstAbstractNode *buildSymbolicMemOperand(MemoryOperand &mem, reg_size memSize);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(RegisterOperand &flag, reg_size size);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(RegisterOperand &flag);

    /* Concretize register and memory */
    void concretizeAllReg(void);
    void concretizeAllMem(void);
    void concretizeReg(RegisterOperand &reg);
    void concretizeMem(MemoryOperand &mem);


    /*
     * Taint Engine Facade
     * -------------------
     */

    /* Returns the taint engine reference */
    TaintEngine &getTaintEngine(void);

    bool isMemTainted(MemoryOperand &mem);
    bool isRegTainted(RegisterOperand &reg);
    void setTaintMem(SymbolicExpression *se, MemoryOperand &mem, reg_size flag);
    void setTaintReg(SymbolicExpression *se, RegisterOperand &reg, reg_size flag);
    void taintMem(MemoryOperand &mem);
    void taintReg(RegisterOperand &reg);
    void untaintMem(MemoryOperand &mem);
    void untaintReg(RegisterOperand &reg);

    /* ALU Spreading */
    void aluSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint32 writeSize);
    void aluSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint32 writeSize);
    void aluSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst);
    void aluSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize);
    void aluSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc);
    void aluSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 writeSize);

    /* Assignment Spreading */
    void assignmentSpreadTaintExprMem(SymbolicExpression *se, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintExprReg(SymbolicExpression *se, RegisterOperand &regSrc);
    void assignmentSpreadTaintExprRegMem(SymbolicExpression *se, RegisterOperand &regSrc, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintExprRegReg(SymbolicExpression *se, RegisterOperand &regSrc1, RegisterOperand &regSrc2);
    void assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, reg_size writeSize);
    void assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, reg_size writeSize);
    void assignmentSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst);
    void assignmentSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc);


    /*
     * Solver Engine Facade
     * --------------------
     */

    /* Returns a reference to the solver engine. */
    SolverEngine                    &getSolverEngine();
    /* Returns models */
    std::list<Smodel>               getModel(smt2lib::smtAstAbstractNode *node);
    std::vector<std::list<Smodel>>  getModels(smt2lib::smtAstAbstractNode *node, reg_size limit);


    /*
     * Statistics Facade
     * -----------------
     */

    /* Returns a reference to the Stats object. */
    Stats   &getStats(void);
    void    incNumberOfBranchesTaken(void);
    void    incNumberOfBranchesTaken(bool isBranch);
    void    incNumberOfExpressions(reg_size val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);
    reg_size  getNumberOfBranchesTaken(void);
    reg_size  getNumberOfExpressions(void);
    reg_size  getTimeOfExecution(void);
    reg_size  getNumberOfUnknownInstruction(void);


    /*
     * Snapshot Facade
     * ---------------
     */

    SnapshotEngine  &getSnapshotEngine(void);
    bool            isSnapshotLocked(void);
    void            addSnapshotModification(reg_size addr, char byte);
    void            takeSnapshot(void);
    void            restoreSnapshot(void);
    void            disableSnapshot(void);
    bool            isSnapshotEnabled(void);

   /*
    * Convert the SMT AST to a Z3 ast and evaluate it
    * ------------------------------------------------
    */
    uint512 evaluateAST(smt2lib::smtAstAbstractNode *node);

    #endif /* LIGHT_VERSION */


  private:
    #ifndef LIGHT_VERSION
    SymbolicEngine    symEngine;
    SolverEngine      solverEngine;
    TaintEngine       taintEngine;
    SnapshotEngine    snapshotEngine;
    Stats             stats;
    #endif
    Trace             trace;
    ContextHandler    *currentCtxH;
};

#endif //_ANALYSISPROCESSOR_H_

