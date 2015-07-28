/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


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
    std::string   symVarComment;
    std::string   symVarName;
    uint64        symVarId;
    uint64        symVarKindValue;
    uint64        symVarSize;
    uint128       symVarConcreteValue;
    bool          symVarHasConcreteValue;

  public:

    SymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 id, uint64 size, std::string comment, uint128 concreteValue);
    SymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 id, uint64 size, std::string comment);
    SymbolicVariable(const SymbolicVariable &copy);
    ~SymbolicVariable();

    SymVar::kind  getSymVarKind(void);
    std::string   getSymVarComment(void);
    std::string   getSymVarName(void);
    uint64        getSymVarId(void);
    uint64        getSymVarKindValue(void);
    uint64        getSymVarSize(void);
    uint128       getConcreteValue(void);
    bool          hasConcreteValue(void);
    void          setSymVarConcreteValue(uint128 value);


};

#endif

