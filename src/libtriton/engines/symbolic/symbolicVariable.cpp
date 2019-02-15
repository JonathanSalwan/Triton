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

      SymbolicVariable::SymbolicVariable(triton::engines::symbolic::variable_e type,
                                         triton::uint64 origin,
                                         triton::usize id,
                                         triton::uint32 size,
                                         const std::string& comment) {
        this->alias   = "";
        this->comment = comment;
        this->id      = id;
        this->name    = TRITON_SYMVAR_NAME + std::to_string(id);
        this->origin  = origin;
        this->size    = size;
        this->type    = type;

        if (this->size > MAX_BITS_SUPPORTED)
          throw triton::exceptions::SymbolicVariable("SymbolicVariable::SymbolicVariable(): Size connot be greater than MAX_BITS_SUPPORTED.");
      }


      SymbolicVariable::SymbolicVariable(const SymbolicVariable& other) {
        this->alias   = other.alias;
        this->comment = other.comment;
        this->id      = other.id;
        this->name    = other.name;
        this->origin  = other.origin;
        this->size    = other.size;
        this->type    = other.type;
      }


      SymbolicVariable& SymbolicVariable::operator=(const SymbolicVariable& other) {
        this->alias   = other.alias;
        this->comment = other.comment;
        this->id      = other.id;
        this->name    = other.name;
        this->origin  = other.origin;
        this->size    = other.size;
        this->type    = other.type;
        return *this;
      }


      triton::engines::symbolic::variable_e SymbolicVariable::getType(void) const {
        return this->type;
      }


      const std::string& SymbolicVariable::getAlias(void) const {
        return this->alias;
      }


      const std::string& SymbolicVariable::getComment(void) const {
        return this->comment;
      }


      const std::string& SymbolicVariable::getName(void) const {
        return this->name;
      }


      triton::usize SymbolicVariable::getId(void) const {
        return this->id;
      }


      triton::uint64 SymbolicVariable::getOrigin(void) const {
        return this->origin;
      }


      triton::uint32 SymbolicVariable::getSize(void) const {
        return this->size;
      }


      void SymbolicVariable::setAlias(const std::string& alias) {
        this->alias = alias;
      }


      void SymbolicVariable::setComment(const std::string& comment) {
        this->comment = comment;
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable& symVar) {
        if (symVar.getAlias().empty())
          stream << symVar.getName() << ":" << symVar.getSize();
        else
          stream << symVar.getAlias() << ":" << symVar.getSize();
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable* symVar) {
        stream << *symVar;
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
