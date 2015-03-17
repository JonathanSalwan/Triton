
#ifndef   __SYMBOLICENGINE_H__
#define   __SYMBOLICENGINE_H__

#include <cstdint>

#include <map>
#include <list>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "SymbolicElement.h"
#include "SMT2Lib.h"


const uint64_t UNSET = -1;


/* Symbolic Engine */
class SymbolicEngine {

  private:

    /* symbolic expression ID */
    uint64_t uniqueID;

    /* Number of symbolic variables used */
    uint64_t numberOfSymVar;

    /*
     * Addresses -> symbolic expression
     * item1: memory address
     * item2: reference ID
     */
    std::map<uint64_t, uint64_t> memoryReference;

    /*
     * Z3 Symbolic Addresse -> variable
     * item1: memory address
     * item2: symbolic variable ID
     */
    std::map<uint64_t, uint64_t> symVarMemoryReference;

    /* List of variables decl in smt2lib */
    std::list<std::string> smt2libVarDeclList;

    /* List of symbolic elements ID */
    std::vector<SymbolicElement *> symbolicVector;


  public:

    /* Symbolic trace */
    uint64_t              symbolicReg[42];

    /* public methods */
    SymbolicElement       *getElementFromId(uint64_t id);
    SymbolicElement       *newSymbolicElement(std::stringstream &src);
    std::string           getSmt2LibVarsDecl();
    uint64_t              getRegSymbolicID(uint64_t regID);
    uint64_t              getUniqueID();
    uint64_t              getUniqueSymVarID();
    uint64_t              isMemoryReference(uint64_t addr);
    uint64_t              isSymVarMemory(uint64_t mem);
    void                  addMemoryReference(uint64_t mem, uint64_t id);
    void                  addSmt2LibVarDecl(uint64_t symVarID, uint64_t readSize);
    void                  addSymVarMemoryReference(uint64_t mem, uint64_t symVarID);
    void                  init(const SymbolicEngine &other);
    void                  operator=(const SymbolicEngine &other);

    SymbolicEngine();
    SymbolicEngine(const SymbolicEngine &copy);
    ~SymbolicEngine();

};

#endif     /* !__SYMBOLICENGINE_H__ */

