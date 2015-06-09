
#include <SymbolicVariable.h>


SymbolicVariable::SymbolicVariable(uint64_t symVarID, uint64_t symVarSize)
{
  this->symVarID = symVarID;
  this->symVarSize = symVarSize;
  this->symVarName = SYMVAR_NAME + std::to_string(symVarID);
}


SymbolicVariable::SymbolicVariable(const SymbolicVariable &copy)
{
  this->symVarID            = copy.symVarID;
  this->symVarName          = copy.symVarName;
  this->symVarSize          = copy.symVarSize;
}


SymbolicVariable::~SymbolicVariable()
{
}


std::string SymbolicVariable::getSymVarName(void)
{
  return this->symVarName;
}


uint64_t SymbolicVariable::getSymVarId(void)
{
  return this->symVarID;
}


uint64_t SymbolicVariable::getSymVarSize(void)
{
  return this->symVarSize;
}


