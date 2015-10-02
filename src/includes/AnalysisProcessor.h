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
    uint64      getRegisterValue(RegisterOperand &reg);
    uint64      getFlagValue(RegisterOperand &flag);
    uint128     getSSERegisterValue(RegisterOperand &reg);

    /* Set the value into the register */
    void        setRegisterValue(RegisterOperand &reg, uint64 value);
    void        setSSERegisterValue(RegisterOperand &reg, uint128 value);

    /* Returns the value of the memory */
    uint128     getMemValue(MemoryOperand &mem, uint32 readSize);
    uint128     getMemValue(uint64 mem, uint32 readSize);
    void        setMemValue(MemoryOperand &mem, uint32 writeSize, uint128 value);


    /*
     * Trace Facade
     * ------------
     */

    Inst      *getLastInstruction(void);
    Trace     &getTrace(void);
    void      addInstructionToTrace(Inst *instruction);


    #ifndef LIGHT_VERSION
    /*
     * Symbolic Engine Facade
     * ----------------------
     */

    /* Returns a symbolic expression for the flag register */
    SymbolicExpression *createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment="");

    /* Returns a symbolic expression for the register */
    SymbolicExpression *createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, uint64 regSize, std::string comment="");

    /* Returns a symbolic expression for the memory address */
    SymbolicExpression *createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, uint64 writeSize, std::string comment="");

    /* Returns a symbolic expression. This methods is mainly used for temporary expression */
    SymbolicExpression *createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment="");

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic register. If there is no symbolic expression, it returns UNSET
     */
    uint64 getRegSymbolicID(RegisterOperand &reg);

    /*
     * Returns the ID of the symbolic expression currently present in the
     * symbolic memory. If there is no symbolic expression, it returns UNSET
     */
    uint64 getMemSymbolicID(MemoryOperand &mem);
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
    SymbolicVariable *convertMemToSymVar(MemoryOperand &mem, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable *convertRegToSymVar(RegisterOperand &reg, uint64 symVarSize, std::string symVarComment);

    /* Returns the symbolic variable from ID or std::string */
    SymbolicVariable *getSymVar(uint64 symVarId);
    SymbolicVariable *getSymVar(std::string symVarName);

    /* Returns all symbolic variables */
    std::vector<SymbolicVariable *> getSymVars(void);

    /* The a path constraint in the PC list */
    void addPathConstraint(uint64 exprId);
    std::list<uint64> getPathConstraints(void);

    /* Build a symbolic register operand */
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, uint64 regSize);
    smt2lib::smtAstAbstractNode *buildSymbolicRegOperand(RegisterOperand &reg, uint64 regSize, uint64 highExtract, uint64 lowExtract);
    smt2lib::smtAstAbstractNode *buildSymbolicMemOperand(MemoryOperand &mem, uint64 memSize);
    smt2lib::smtAstAbstractNode *buildSymbolicFlagOperand(RegisterOperand &flag, uint64 size);
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
    void setTaintMem(SymbolicExpression *se, MemoryOperand &mem, uint64 flag);
    void setTaintReg(SymbolicExpression *se, RegisterOperand &reg, uint64 flag);
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
    void assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint64 writeSize);
    void assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize);
    void assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint64 writeSize);
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

