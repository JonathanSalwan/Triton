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

    /* Symbolic expressions ID */
    reg_size uniqueID;

    /* List of symbolic variables */
    std::vector<SymbolicVariable *> symbolicVariables;

    /* List of symbolic expressions */
    std::vector<SymbolicExpression *> symbolicExpressions;

    /*
     * Addresses -> symbolic expression
     * item1: memory address
     * item2: symbolic reference ID
     */
    std::map<reg_size, reg_size> memoryReference;

    /*
     * List of path constaints (PC).
     * Item = symbolic reference ID.
     *
     * When a branch instruction is executed,
     * it must add the PC in this list.
     */
    std::list<reg_size> pathConstaints;


  public:

    /* Symbolic trace */
    /* sizeof(symbolicReg) = enum REG */
    reg_size                            symbolicReg[ID_LAST_ITEM];

    /* public methods */
    SymbolicExpression                *getExpressionFromId(reg_size id);
    SymbolicExpression                *newSymbolicExpression(smt2lib::smtAstAbstractNode *node, enum SymExpr::kind kind, std::string comment="");
    SymbolicVariable                  *addSymbolicVariable(SymVar::kind kind, reg_size kindValue, reg_size size, std::string comment);
    SymbolicVariable                  *convertExprToSymVar(reg_size exprId, reg_size symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertMemToSymVar(reg_size memAddr, reg_size symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertRegToSymVar(reg_size regId, reg_size symVarSize, std::string symVarComment);
    SymbolicVariable                  *getSymVar(std::string symVarName);
    SymbolicVariable                  *getSymVar(reg_size symVarId);
    smt2lib::smtAstAbstractNode       *getFullExpression(smt2lib::smtAstAbstractNode *node);
    std::list<SymbolicExpression *>   getTaintedExpressions(void);
    std::list<reg_size>                 getPathConstraints(void);
    std::string                       getVariablesDeclaration(void);
    std::vector<SymbolicExpression *> getExpressions(void);
    std::vector<SymbolicVariable *>   getSymVars(void);
    reg_size                            getMemSymbolicID(reg_size addr);
    reg_size                            getRegSymbolicID(reg_size regID);
    reg_size                            getUniqueID();
    void                              addMemoryReference(reg_size mem, reg_size id);
    void                              addPathConstraint(reg_size exprId);
    void                              concretizeAllMem(void);
    void                              concretizeAllReg(void);
    void                              concretizeMem(reg_size mem);
    void                              concretizeReg(reg_size regID);
    void                              init(const SymbolicEngine &other);
    void                              operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif /* !__SYMBOLICENGINE_H__ */
#endif /* LIGHT_VERSION */

