/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <SymbolicVariable.h>



SymbolicVariable::SymbolicVariable(SymVar::kind kind,
                                   uint64 kindValue,
                                   uint64 id,
                                   uint64 size,
                                   std::string comment,
                                   uint128 concreteValue) {
  this->symVarComment          = comment;
  this->symVarId               = id;
  this->symVarKind             = kind;
  this->symVarKindValue        = kindValue;
  this->symVarName             = SYMVAR_NAME + std::to_string(id);
  this->symVarSize             = size;
  this->symVarConcreteValue    = concreteValue;
  this->symVarHasConcreteValue = true;
}


SymbolicVariable::SymbolicVariable(SymVar::kind kind,
                                   uint64 kindValue,
                                   uint64 id,
                                   uint64 size,
                                   std::string comment
                                   ) : SymbolicVariable(kind, kindValue, id, size, comment, 0) {
  this->symVarHasConcreteValue = false;
}


SymbolicVariable::SymbolicVariable(const SymbolicVariable &copy) {
  this->symVarComment          = copy.symVarComment;
  this->symVarId               = copy.symVarId;
  this->symVarKind             = copy.symVarKind;
  this->symVarKindValue        = copy.symVarKindValue;
  this->symVarName             = copy.symVarName;
  this->symVarSize             = copy.symVarSize;
  this->symVarConcreteValue    = copy.symVarConcreteValue;
  this->symVarHasConcreteValue = copy.symVarHasConcreteValue;
}


SymbolicVariable::~SymbolicVariable() {
}


SymVar::kind SymbolicVariable::getSymVarKind(void) {
  return this->symVarKind;
}


std::string SymbolicVariable::getSymVarName(void) {
  return this->symVarName;
}


uint64 SymbolicVariable::getSymVarId(void) {
  return this->symVarId;
}


uint64 SymbolicVariable::getSymVarKindValue(void) {
  return this->symVarKindValue;
}


uint64 SymbolicVariable::getSymVarSize(void) {
  return this->symVarSize;
}


std::string SymbolicVariable::getSymVarComment(void) {
  return this->symVarComment;
}


uint128 SymbolicVariable::getConcreteValue(void) {
  if (this->symVarHasConcreteValue)
    return this->symVarConcreteValue;
  else
    throw std::runtime_error("SymbolicVariable: The symbolic variable has not a concrete value");
}


bool SymbolicVariable::hasConcreteValue(void) {
  return this->symVarHasConcreteValue;
}


void SymbolicVariable::setSymVarConcreteValue(uint128 value) {
  this->symVarConcreteValue    = value;
  this->symVarHasConcreteValue = true;
}

#endif /* LIGHT_VERSION */

