
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
#include "SymbolicElement.h"
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
    std::vector<SymbolicElement *> symbolicExpressions;

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

    /* Private classes used by getBacktrackedExpressionFromId() */
    std::string deepReplace(std::stringstream &formula);
    std::string replaceEq(std::string str, const std::string from, const std::string to);


  public:

    /* Symbolic trace */
    /* sizeof(symbolicReg) = enum REG */
    uint64                          symbolicReg[ID_LAST_ITEM];

    /* public methods */
    SymbolicElement                 *getElementFromId(uint64 id);
    SymbolicElement                 *newSymbolicElement(std::stringstream &src);
    SymbolicElement                 *newSymbolicElement(std::stringstream &src, std::string comment);
    SymbolicVariable                *addSymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 size, std::string comment);
    SymbolicVariable                *getSymVar(uint64 symVarId);
    SymbolicVariable                *getSymVar(std::string symVarName);
    std::list<uint64>               getPathConstraints(void);
    std::string                     getBacktrackedExpressionFromId(uint64 id);
    std::string                     getVariablesDeclaration(void);
    std::vector<SymbolicVariable *> getSymVars(void);
    uint64                          convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment);
    uint64                          convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment);
    uint64                          convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment);
    uint64                          getMemSymbolicID(uint64 addr);
    uint64                          getRegSymbolicID(uint64 regID);
    uint64                          getUniqueID();
    void                            addMemoryReference(uint64 mem, uint64 id);
    void                            addPathConstraint(uint64 exprId);
    void                            concretizeMem(uint64 mem);
    void                            concretizeReg(uint64 regID);
    void                            init(const SymbolicEngine &other);
    void                            operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif     /* !__SYMBOLICENGINE_H__ */

