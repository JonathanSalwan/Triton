//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <ast.hpp>
#include <cpuSize.hpp>
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
        this->symVarName             = TRITON_SYMVAR_NAME + std::to_string(id);
        this->symVarSize             = size;
        this->symVarConcreteValue    = concreteValue;

        if (this->symVarSize > MAX_BITS_SUPPORTED)
          throw std::runtime_error("SymbolicVariable::SymbolicVariable(): Size connot be greater than MAX_BITS_SUPPORTED.");
      }


      SymbolicVariable::SymbolicVariable(const SymbolicVariable &copy) {
        this->symVarComment          = copy.symVarComment;
        this->symVarId               = copy.symVarId;
        this->symVarKind             = copy.symVarKind;
        this->symVarKindValue        = copy.symVarKindValue;
        this->symVarName             = copy.symVarName;
        this->symVarSize             = copy.symVarSize;
        this->symVarConcreteValue    = copy.symVarConcreteValue;
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
        return this->symVarConcreteValue;
      }


      void SymbolicVariable::setSymVarConcreteValue(triton::uint128 value) {
        this->symVarConcreteValue = value;
        if (triton::ast::variableNodes.find(this->getSymVarName()) != triton::ast::variableNodes.end())
          triton::ast::variableNodes[this->getSymVarName()]->init();
      }


      std::ostream& operator<<(std::ostream& stream, SymbolicVariable symVar) {
        stream << symVar.getSymVarName() << ":" << symVar.getSymVarSize();
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, SymbolicVariable* symVar) {
        stream << *symVar;
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

