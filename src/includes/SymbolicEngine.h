/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SYMBOLICENGINE_H
#define SYMBOLICENGINE_H

#include <map>
#include <list>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <sstream>

#include "Misc.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicExpression.h"
#include "SymbolicVariable.h"
#include "TritonTypes.h"


/* Symbolic Engine */
class SymbolicEngine {

  private:

    /* Enable / Disable flag */
    bool enableFlag;

    /* Symbolic expressions ID */
    __uint uniqueID;

    /* List of symbolic variables */
    std::vector<SymbolicVariable *> symbolicVariables;

    /* List of symbolic expressions */
    std::vector<SymbolicExpression *> symbolicExpressions;

    /*
     * Addresses -> symbolic expression
     * item1: memory address
     * item2: symbolic reference ID
     */
    std::map<__uint, __uint> memoryReference;

    /*
     * List of path constaints (PC).
     * Item = symbolic reference ID.
     *
     * When a branch instruction is executed,
     * it must add the PC in this list.
     */
    std::list<__uint> pathConstaints;


  public:

    /* Symbolic trace */
    /* sizeof(symbolicReg) = enum REG */
    __uint                            symbolicReg[ID_LAST_ITEM];

    /* public methods */
    SymbolicExpression                *getExpressionFromId(__uint id);
    SymbolicExpression                *newSymbolicExpression(smt2lib::smtAstAbstractNode *node, enum SymExpr::kind kind, std::string comment="");
    SymbolicVariable                  *addSymbolicVariable(SymVar::kind kind, __uint kindValue, __uint size, std::string comment);
    SymbolicVariable                  *convertExprToSymVar(__uint exprId, __uint symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertMemToSymVar(__uint memAddr, __uint symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertRegToSymVar(__uint regId, __uint symVarSize, std::string symVarComment);
    SymbolicVariable                  *getSymVar(__uint symVarId);
    SymbolicVariable                  *getSymVar(std::string symVarName);
    __uint                            getMemSymbolicID(__uint addr);
    __uint                            getRegSymbolicID(__uint regID);
    __uint                            getUniqueID();
    bool                              isEnabled(void);
    smt2lib::smtAstAbstractNode       *getFullExpression(smt2lib::smtAstAbstractNode *node);
    std::list<SymbolicExpression *>   getTaintedExpressions(void);
    std::list<__uint>                 getPathConstraints(void);
    std::string                       getVariablesDeclaration(void);
    std::vector<SymbolicExpression *> getExpressions(void);
    std::vector<SymbolicVariable *>   getSymVars(void);
    void                              addMemoryReference(__uint mem, __uint id);
    void                              addPathConstraint(__uint exprId);
    void                              concretizeAllMem(void);
    void                              concretizeAllReg(void);
    void                              concretizeMem(__uint mem);
    void                              concretizeReg(__uint regID);
    void                              disable(void);
    void                              enable(void);
    void                              init(const SymbolicEngine &other);
    void                              operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif /* !__SYMBOLICENGINE_H__ */
#endif /* LIGHT_VERSION */

