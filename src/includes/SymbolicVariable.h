
#ifndef   SYMBOLICVARIABLE_H
#define   SYMBOLICVARIABLE_H

#include <string>
#include "TritonTypes.h"

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
    uint64        symVarId;
    uint64        symVarKindValue;
    uint64        symVarSize;
    std::string   symVarComment;

  public:

    SymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 id, uint64 size, std::string comment);
    SymbolicVariable(const SymbolicVariable &copy);
    ~SymbolicVariable();

    SymVar::kind  getSymVarKind(void);
    std::string   getSymVarName(void);
    uint64        getSymVarId(void);
    uint64        getSymVarKindValue(void);
    uint64        getSymVarSize(void);
    std::string   getSymVarComment(void);

};

#endif

