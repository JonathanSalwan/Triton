//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/registerSpecification.hpp>



namespace triton {
  namespace arch {

    RegisterSpecification::RegisterSpecification() {
      this->name     = "unknown";
      this->high     = 0;
      this->low      = 0;
      this->parentId = 0;
    }


    RegisterSpecification::RegisterSpecification(std::string& name, triton::uint32 high, triton::uint32 low, triton::uint32 parentId) {
      this->name     = name;
      this->high     = high;
      this->low      = low;
      this->parentId = parentId;
    }


    RegisterSpecification::RegisterSpecification(const RegisterSpecification& other) {
      this->name     = other.name;
      this->high     = other.high;
      this->low      = other.low;
      this->parentId = other.parentId;
    }


    RegisterSpecification::~RegisterSpecification() {
    }


    void RegisterSpecification::operator=(const RegisterSpecification& other) {
      this->name     = other.name;
      this->high     = other.high;
      this->low      = other.low;
      this->parentId = other.parentId;
    }


    std::string RegisterSpecification::getName(void) const {
      return this->name;
    }


    triton::uint32 RegisterSpecification::getHigh(void) const {
      return this->high;
    }


    triton::uint32 RegisterSpecification::getLow(void) const {
      return this->low;
    }


    triton::uint32 RegisterSpecification::getParentId(void) const {
      return this->parentId;
    }


    void RegisterSpecification::setName(const std::string& name) {
      this->name = name;
    }


    void RegisterSpecification::setHigh(triton::uint32 high) {
      this->high = high;
    }


    void RegisterSpecification::setLow(triton::uint32 low) {
      this->low = low;
    }


    void RegisterSpecification::setParentId(triton::uint32 parentId) {
      this->parentId = parentId;
    }

  }; /* arch namespace */
}; /* triton namespace */
