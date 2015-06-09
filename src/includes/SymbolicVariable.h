
#ifndef   SYMBOLICVARIABLE_H
#define   SYMBOLICVARIABLE_H

#include <cstdint>
#include <string>

/* The name of the symbolic variables */
#define SYMVAR_NAME       "SymVar_"
#define SYMVAR_NAME_SIZE  (sizeof(SYMVAR_NAME) - 1)


/* Symbolic Variable */
class SymbolicVariable {

  private:
    std::string   symVarName;
    uint64_t      symVarID;
    uint64_t      symVarSize;

  public:
    SymbolicVariable(uint64_t symVarID, uint64_t symVarSize);
    SymbolicVariable(const SymbolicVariable &copy);
    ~SymbolicVariable();

    std::string   getSymVarName(void);
    uint64_t      getSymVarId(void);
    uint64_t      getSymVarSize(void);

};

#endif

