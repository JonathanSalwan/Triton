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
    __uint      getRegisterValue(RegisterOperand &reg);
    __uint      getFlagValue(RegisterOperand &flag);
    uint128     getSSERegisterValue(RegisterOperand &reg);

    /* Set the value into the register */
    void        setRegisterValue(RegisterOperand &reg, __uint value);
    void        setSSERegisterValue(RegisterOperand &reg, uint128 value);

    /* Returns the value of the memory */
    uint128     getMemValue(MemoryOperand &mem, uint32 readSize);
    uint128     getMemValue(__uint mem, uint32 readSize);
    void        setMemValue(MemoryOperand &mem, uint32 writeSize, uint128 value);

    /* Deal with the context */
    bool        isContextMustBeExecuted(void);
    void        executeContext(void);

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

    /* Returns a symbolic expression. This methods is mainly used for temporary expression */
    SymbolicExpression *createSE(smt2lib::smtAstAbstractNode *expr, std::string comment="");
    SymbolicExpression *createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment="");

    /* Returns a symbolic expression for the flag register */
    SymbolicExpression *createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment="");

    /* Returns a symbolic expression for the register */
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, std::string comment="");
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, __uint regSize, std::string comment="");

    /* Returns a symbolic expression for the memory address */
    SymbolicExpression *createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, __uint writeSize, std::string comment="");

    /* Assign a symbolic expression to a register */
    bool assignSEToReg(SymbolicExpression *se, __uint regId);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic register. If there is no symbolic expression, it returns UNSET
     */
    __uint getRegSymbolicID(RegisterOperand &reg);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic memory. If there is no symbolic expression, it returns UNSET
     */
    __uint getMemSymbolicID(MemoryOperand &mem);
    __uint getMemSymbolicID(__uint address);

    /* Returns the symbolic expression from its id */
    SymbolicExpression *getExpressionFromId(__uint id);

    /* Returns all symbolic expressions */
    std::vector<SymbolicExpression *> getExpressions(void);

    /* Returns a list which contains all tainted expressions */
    std::list<SymbolicExpression *> getTaintedExpressions(void);

    /* Returns the full symbolic expression backtracked */
    smt2lib::smtAstAbstractNode *getFullExpression(smt2lib::smtAstAbstractNode *node);

    /* Returns the symbolic engine reference */
    SymbolicEngine &getSymbolicEngine(void);

    /* Converts an expression, register or memory to a symbolic variable */
    SymbolicVariable *convertExprToSymVar(__uint exprId, __uint symVarSize, std::string symVarComment);
    SymbolicVariable *convertMemToSymVar(MemoryOperand &mem, __uint symVarSize, std::string symVarComment);
    SymbolicVariable *convertRegToSymVar(RegisterOperand &reg, __uint symVarSize, std::string symVarComment);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(__uint symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(__uint exprId);
    std::list<__uint> getPathConstraints(void);

    /* Build a symbolic register operand */
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg);
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, __uint regSize);
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, __uint highExtract, __uint lowExtract);
    smt2lib::smtAstAbstractNode *buildSymbolicMemOperand(MemoryOperand &mem, __uint memSize);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(RegisterOperand &flag, __uint size);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(RegisterOperand &flag);

    /* Concretize register and memory */
    void concretizeAllReg(void);
    void concretizeAllMem(void);
    void concretizeReg(RegisterOperand &reg);
    void concretizeMem(MemoryOperand &mem);

    /* Lock / Unlock flag */
    bool isSymEngineEnabled(void);
    void enableSymEngine(void);
    void disableSymEngine(void);


    /*
     * Taint Engine Facade
     * -------------------
     */

    /* Returns the taint engine reference */
    TaintEngine &getTaintEngine(void);

    bool isMemTainted(MemoryOperand &mem);
    bool isRegTainted(RegisterOperand &reg);
    void setTaintMem(SymbolicExpression *se, MemoryOperand &mem, __uint flag);
    void setTaintReg(SymbolicExpression *se, RegisterOperand &reg, __uint flag);
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
    void assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, __uint writeSize);
    void assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, __uint writeSize);
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
    std::vector<std::list<Smodel>>  getModels(smt2lib::smtAstAbstractNode *node, __uint limit);


    /*
     * Statistics Facade
     * -----------------
     */

    /* Returns a reference to the Stats object. */
    Stats   &getStats(void);
    void    incNumberOfBranchesTaken(void);
    void    incNumberOfBranchesTaken(bool isBranch);
    void    incNumberOfExpressions(__uint val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);
    __uint  getNumberOfBranchesTaken(void);
    __uint  getNumberOfExpressions(void);
    __uint  getTimeOfExecution(void);
    __uint  getNumberOfUnknownInstruction(void);


    /*
     * Snapshot Facade
     * ---------------
     */

    SnapshotEngine  &getSnapshotEngine(void);
    bool            isSnapshotEnabled(void);
    bool            isSnapshotLocked(void);
    bool            isSnapshotMustBeRestored(void);
    void            addSnapshotModification(__uint addr, char byte);
    void            disableSnapshot(void);
    void            restoreSnapshot(void);
    void            setSnapshotRestoreFlag(bool flag);
    void            takeSnapshot(void);

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

