
#include <SymbolicVariable.h>


SymbolicVariable::SymbolicVariable(SymVar::kind kind,
                                   uint64_t kindValue,
                                   uint64_t id,
                                   uint64_t size)
{
  this->symVarId        = id;
  this->symVarKind      = kind;
  this->symVarKindValue = kindValue;
  this->symVarName      = SYMVAR_NAME + std::to_string(id);
  this->symVarSize      = size;
}


SymbolicVariable::SymbolicVariable(const SymbolicVariable &copy)
{
  this->symVarId        = copy.symVarId;
  this->symVarKind      = copy.symVarKind;
  this->symVarKindValue = copy.symVarKindValue;
  this->symVarName      = copy.symVarName;
  this->symVarSize      = copy.symVarSize;
}


SymbolicVariable::~SymbolicVariable()
{
}


SymVar::kind SymbolicVariable::getSymVarKind(void)
{
  return this->symVarKind;
}


std::string SymbolicVariable::getSymVarName(void)
{
  return this->symVarName;
}


uint64_t SymbolicVariable::getSymVarId(void)
{
  return this->symVarId;
}


uint64_t SymbolicVariable::getSymVarKindValue(void)
{
  return this->symVarKindValue;
}


uint64_t SymbolicVariable::getSymVarSize(void)
{
  return this->symVarSize;
}


