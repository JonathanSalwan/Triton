//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/exceptions.hpp>
#include <triton/register.hpp>
#include <triton/registerSpecification.hpp>



namespace triton {
  namespace arch {

    Register::Register() {
      this->clear();
    }


    Register::Register(triton::uint32 regId) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }

      this->setup(regId);
      this->immutable            = false;
      this->concreteValueDefined = false;
    }


    Register::Register(triton::uint32 regId, triton::uint512 concreteValue)
      : Register(regId, concreteValue, false) {
    }


    Register::Register(triton::uint32 regId, triton::uint512 concreteValue, bool immutable) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }

      this->setup(regId);
      this->immutable = false;
      this->setConcreteValue(concreteValue);
      this->immutable = immutable;
    }


    Register::Register(const Register& other) : BitsVector(other) {
      this->copy(other);
    }


    Register::~Register() {
    }


    void Register::operator=(const Register& other) {
      BitsVector::operator=(other);
      this->copy(other);
    }


    void Register::clear(void) {
      this->concreteValue        = 0;
      this->concreteValueDefined = false;
      this->id                   = triton::arch::INVALID_REGISTER_ID;
      this->immutable            = false;
      this->name                 = "unknown";
      this->parent               = triton::arch::INVALID_REGISTER_ID;
    }


    void Register::setup(triton::uint32 regId) {
      triton::arch::RegisterSpecification regInfo;

      this->id = regId;
      if (!triton::api.isRegisterValid(regId))
        this->id = triton::arch::INVALID_REGISTER_ID;

      regInfo      = triton::api.getRegisterSpecification(this->id);
      this->name   = regInfo.getName();
      this->parent = regInfo.getParentId();

      this->setHigh(regInfo.getHigh());
      this->setLow(regInfo.getLow());
    }


    void Register::copy(const Register& other) {
      this->concreteValue        = other.concreteValue;
      this->concreteValueDefined = other.concreteValueDefined;
      this->id                   = other.id;
      this->immutable            = false;
      this->name                 = other.name;
      this->parent               = other.parent;
    }


    triton::uint32 Register::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 Register::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::uint32 Register::getId(void) const {
      return this->id;
    }


    Register Register::getParent(void) const {
      return Register(this->parent);
    }


    triton::uint32 Register::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint32 Register::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    std::string Register::getName(void) const {
      return this->name;
    }


    triton::uint32 Register::getType(void) const {
      return triton::arch::OP_REG;
    }


    triton::uint512 Register::getConcreteValue(void) const {
      return this->concreteValue;
    }


    void Register::setName(const std::string& name) {
      this->name = name;
    }


    void Register::setId(triton::uint32 regId) {
      this->id = regId;
    }


    void Register::setParent(triton::uint32 regId) {
      this->parent = regId;
    }


    void Register::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw triton::exceptions::Register("Register::setConcreteValue(): You cannot set this concrete value (too big) to this register.");

      if (this->immutable)
        return;

      this->concreteValue        = concreteValue;
      this->concreteValueDefined = true;
    }


    bool Register::isImmutable(void) const {
      return this->immutable;
    }


    bool Register::isOverlapWith(const Register& other) const {
      if (this->getParent().getId() == other.getParent().getId()) {
        if (this->getLow() <= other.getLow() && other.getLow() <= this->getHigh()) return true;
        if (other.getLow() <= this->getLow() && this->getLow() <= other.getHigh()) return true;
      }
      return false;
    }


    bool Register::hasConcreteValue(void) const {
      return this->concreteValueDefined;
    }


    std::ostream& operator<<(std::ostream& stream, const Register& reg) {
      stream << reg.getName()
             << ":"
             << std::dec << reg.getBitSize()
             << " bv["
             << reg.getHigh()
             << ".."
             << reg.getLow()
             << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const Register* reg) {
      stream << *reg;
      return stream;
    }


    bool operator==(const Register& reg1, const Register& reg2) {
      if (reg1.getId() != reg2.getId())
        return false;
      if (reg1.getConcreteValue() != reg2.getConcreteValue())
        return false;
      return true;
    }


    bool operator!=(const Register& reg1, const Register& reg2) {
      return !(reg1 == reg2);
    }


    bool operator<(const Register& reg1, const Register& reg2) {
      return (reg1.getId() < reg2.getId());
    }

  }; /* arch namespace */
}; /* triton namespace */
