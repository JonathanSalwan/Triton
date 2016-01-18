//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <symbolicVariable.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicVariable::SymbolicVariable(symkind_e kind,
                                         triton::__uint kindValue,
                                         triton::__uint id,
                                         triton::uint32 size,
                                         std::string comment,
                                         triton::uint128 concreteValue) {
        this->symVarComment          = comment;
        this->symVarId               = id;
        this->symVarKind             = kind;
        this->symVarKindValue        = kindValue;
        this->symVarName             = SYMVAR_NAME + std::to_string(id);
        this->symVarSize             = size;
        this->symVarConcreteValue    = concreteValue;
        this->symVarHasConcreteValue = true;
      }


      SymbolicVariable::SymbolicVariable(symkind_e kind,
                                         triton::__uint kindValue,
                                         triton::__uint id,
                                         triton::uint32 size,
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


      symkind_e SymbolicVariable::getSymVarKind(void) {
        return this->symVarKind;
      }


      std::string SymbolicVariable::getSymVarName(void) {
        return this->symVarName;
      }


      triton::__uint SymbolicVariable::getSymVarId(void) {
        return this->symVarId;
      }


      triton::__uint SymbolicVariable::getSymVarKindValue(void) {
        return this->symVarKindValue;
      }


      triton::uint32 SymbolicVariable::getSymVarSize(void) {
        return this->symVarSize;
      }


      std::string SymbolicVariable::getSymVarComment(void) {
        return this->symVarComment;
      }


      triton::uint128 SymbolicVariable::getConcreteValue(void) {
        if (this->symVarHasConcreteValue)
          return this->symVarConcreteValue;
        else
          throw std::runtime_error("SymbolicVariable::SymbolicVariable(): The symbolic variable has not a concrete value");
      }


      bool SymbolicVariable::hasConcreteValue(void) {
        return this->symVarHasConcreteValue;
      }


      void SymbolicVariable::setSymVarConcreteValue(triton::uint128 value) {
        this->symVarConcreteValue    = value;
        this->symVarHasConcreteValue = true;
      }


      std::ostream &operator<<(std::ostream &stream, SymbolicVariable symVar) {
        stream << symVar.getSymVarName() << ":" << symVar.getSymVarSize();
        return stream;
      }


      std::ostream &operator<<(std::ostream &stream, SymbolicVariable* symVar) {
        stream << symVar->getSymVarName() << ":" << symVar->getSymVarSize();
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

