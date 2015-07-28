/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   SYMBOLICENGINE_H
#define   SYMBOLICENGINE_H

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
    uint64 uniqueID;

    /* List of symbolic variables */
    std::vector<SymbolicVariable *> symbolicVariables;

    /* List of symbolic expressions */
    std::vector<SymbolicExpression *> symbolicExpressions;

    /*
     * Addresses -> symbolic expression
     * item1: memory address
     * item2: symbolic reference ID
     */
    std::map<uint64, uint64> memoryReference;

    /*
     * List of path constaints (PC).
     * Item = symbolic reference ID.
     *
     * When a branch instruction is executed,
     * it must add the PC in this list.
     */
    std::list<uint64> pathConstaints;


  public:

    /* Symbolic trace */
    /* sizeof(symbolicReg) = enum REG */
    uint64                            symbolicReg[ID_LAST_ITEM];

    /* public methods */
    SymbolicExpression                *getExpressionFromId(uint64 id);
    SymbolicExpression                *newSymbolicExpression(smt2lib::smtAstAbstractNode *node);
    SymbolicExpression                *newSymbolicExpression(smt2lib::smtAstAbstractNode *node, std::string comment);
    SymbolicVariable                  *addSymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 size, std::string comment);
    SymbolicVariable                  *convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable                  *convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment);
    SymbolicVariable                  *getSymVar(std::string symVarName);
    SymbolicVariable                  *getSymVar(uint64 symVarId);
    smt2lib::smtAstAbstractNode       *getFullExpression(smt2lib::smtAstAbstractNode *node);
    std::list<SymbolicExpression *>   getTaintedExpressions(void);
    std::list<uint64>                 getPathConstraints(void);
    std::string                       getVariablesDeclaration(void);
    std::vector<SymbolicExpression *> getExpressions(void);
    std::vector<SymbolicVariable *>   getSymVars(void);
    uint64                            getMemSymbolicID(uint64 addr);
    uint64                            getRegSymbolicID(uint64 regID);
    uint64                            getUniqueID();
    void                              addMemoryReference(uint64 mem, uint64 id);
    void                              addPathConstraint(uint64 exprId);
    void                              concretizeAllMem(void);
    void                              concretizeAllReg(void);
    void                              concretizeMem(uint64 mem);
    void                              concretizeReg(uint64 regID);
    void                              init(const SymbolicEngine &other);
    void                              operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif     /* !__SYMBOLICENGINE_H__ */

