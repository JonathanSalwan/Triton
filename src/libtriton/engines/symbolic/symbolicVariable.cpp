//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/cpuSize.hpp>
#include <triton/symbolicVariable.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicVariable::SymbolicVariable(symkind_e kind,
                                         triton::uint64 kindValue,
                                         triton::usize id,
                                         triton::uint32 size,
                                         const std::string& comment) {
        this->comment         = comment;
        this->id              = id;
        this->kind            = kind;
        this->kindValue       = kindValue;
        this->name            = TRITON_SYMVAR_NAME + std::to_string(id);
        this->size            = size;

        if (this->size > MAX_BITS_SUPPORTED)
          throw triton::exceptions::SymbolicVariable("SymbolicVariable::SymbolicVariable(): Size connot be greater than MAX_BITS_SUPPORTED.");
      }


      SymbolicVariable::SymbolicVariable(const SymbolicVariable& other) {
        this->comment         = other.comment;
        this->id              = other.id;
        this->kind            = other.kind;
        this->kindValue       = other.kindValue;
        this->name            = other.name;
        this->size            = other.size;
      }


      SymbolicVariable& SymbolicVariable::operator=(const SymbolicVariable& other) {
        this->comment         = other.comment;
        this->id              = other.id;
        this->kind            = other.kind;
        this->kindValue       = other.kindValue;
        this->name            = other.name;
        this->size            = other.size;
        return *this;
      }


      symkind_e SymbolicVariable::getKind(void) const {
        return this->kind;
      }


      const std::string& SymbolicVariable::getName(void) const {
        return this->name;
      }


      triton::usize SymbolicVariable::getId(void) const {
        return this->id;
      }


      triton::uint64 SymbolicVariable::getKindValue(void) const {
        return this->kindValue;
      }


      triton::uint32 SymbolicVariable::getSize(void) const {
        return this->size;
      }


      const std::string& SymbolicVariable::getComment(void) const {
        return this->comment;
      }


      void SymbolicVariable::setComment(const std::string& comment) {
        this->comment = comment;
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable& symVar) {
        stream << symVar.getName() << ":" << symVar.getSize();
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable* symVar) {
        stream << *symVar;
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

