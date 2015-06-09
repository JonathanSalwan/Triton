
#ifndef   SYMBOLICENGINE_H
#define   SYMBOLICENGINE_H

#include <cstdint>

#include <map>
#include <list>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <sstream>

#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"
#include "SymbolicVariable.h"

const uint64_t UNSET = -1;


/* Symbolic Engine */
class SymbolicEngine {

  private:

    /* Symbolic expressions ID */
    uint64_t uniqueID;

    /* List of symbolic variables */
    std::vector<SymbolicVariable *> symbolicVariables;

    /* List of symbolic expressions */
    std::vector<SymbolicElement *> symbolicExpressions;

    /*
     * Addresses -> symbolic expression
     * item1: memory address
     * item2: symbolic reference ID
     */
    std::map<uint64_t, uint64_t> memoryReference;

    /*
     * List of path constaints (PC).
     * Item = symbolic reference ID.
     *
     * When a branch instruction is executed,
     * it must add the PC in this list.
     */
    std::list<uint64_t> pathConstaints;

    /* Private classes used by getBacktrackedExpressionFromId() */
    std::string deepReplace(std::stringstream &formula);
    std::string replaceEq(std::string str, const std::string from, const std::string to);


  public:

    /* Symbolic trace */
    /* sizeof(symbolicReg) = enum REG */
    uint64_t                        symbolicReg[ID_LAST_ITEM];

    /* public methods */
    SymbolicElement                 *getElementFromId(uint64_t id);
    SymbolicElement                 *newSymbolicElement(std::stringstream &src);
    SymbolicElement                 *newSymbolicElement(std::stringstream &src, std::string comment);
    SymbolicVariable                *addSymbolicVariable(SymVar::kind kind, uint64_t kindValue, uint64_t concreteValue, uint64_t size);
    SymbolicVariable                *getSymVar(uint64_t symVarId);
    SymbolicVariable                *getSymVar(std::string symVarName);
    std::list<uint64_t>             getPathConstraints(void);
    std::string                     getBacktrackedExpressionFromId(uint64_t id);
    std::string                     getVariablesDeclaration(void);
    std::vector<SymbolicVariable *> getSymVars(void);
    uint64_t                        convertExprToSymVar(uint64_t exprId, uint64_t symVarSize);
    uint64_t                        getMemSymbolicID(uint64_t addr);
    uint64_t                        getRegSymbolicID(uint64_t regID);
    uint64_t                        getUniqueID();
    void                            addMemoryReference(uint64_t mem, uint64_t id);
    void                            addPathConstraint(uint64_t exprId);
    void                            concretizeMem(uint64_t mem);
    void                            concretizeReg(uint64_t regID);
    void                            init(const SymbolicEngine &other);
    void                            operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif     /* !__SYMBOLICENGINE_H__ */

