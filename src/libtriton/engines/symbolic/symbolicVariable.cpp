//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
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
                                         const std::string& alias) {
        this->alias   = alias;
        this->comment = "";
        this->id      = id;
        this->name    = TRITON_SYMVAR_NAME + std::to_string(id);
        this->origin  = origin;
        this->size    = size;
        this->type    = type;

        if (this->size > triton::bitsize::max_supported)
          throw triton::exceptions::SymbolicVariable("SymbolicVariable::SymbolicVariable(): Size cannot be greater than triton::bitsize::max_supported.");

        if (this->size == 0)
          throw triton::exceptions::SymbolicVariable("SymbolicVariable::SymbolicVariable(): Size cannot be zero.");
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


      bool operator<(const SymbolicVariable& symvar1, const SymbolicVariable& symvar2) {
        return symvar1.getId() < symvar2.getId();
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
