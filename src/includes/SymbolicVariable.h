
#ifndef   SYMBOLICVARIABLE_H
#define   SYMBOLICVARIABLE_H

#include <cstdint>
#include <string>

/* The name of the symbolic variables */
#define SYMVAR_NAME       "SymVar_"
#define SYMVAR_NAME_SIZE  (sizeof(SYMVAR_NAME) - 1)


namespace SymVar
{
  /* Defines the kind of the symbolic variable */
  enum kind {
    UNDEF = 0,
    REG,
    MEM
  };
};


/* Symbolic Variable */
class SymbolicVariable {

  private:
    SymVar::kind  symVarKind;
    std::string   symVarName;
    uint64_t      symVarId;
    uint64_t      symVarKindValue;
    uint64_t      symVarSize;

  public:

    SymbolicVariable(SymVar::kind kind, uint64_t kindValue, uint64_t id, uint64_t size);
    SymbolicVariable(const SymbolicVariable &copy);
    ~SymbolicVariable();

    SymVar::kind  getSymVarKind(void);
    std::string   getSymVarName(void);
    uint64_t      getSymVarId(void);
    uint64_t      getSymVarKindValue(void);
    uint64_t      getSymVarSize(void);

};

#endif

